/**@file
*****************************************************************************
Range proofs for fixed ranges in the provable setting
 One can also modify this for arbitrary ranges
 This file is part of "A Succinct and Efficient Range Proof with More Functionalities based on Interactive Oracle Proof"
*****************************************************************************
* @author   Weihan Li
*****************************************************************************/

#include <algorithm>
#include <cstdint>
#include <iostream>

#include <libff/algebra/fields/prime_base/fields_64.hpp>
#include "range_proof/algebra/fft.hpp"
#include "range_proof/iop/iop.hpp"
#include "range_proof/protocols/ldt/fri/fri_ldt.hpp"
#include <sys/time.h>


using namespace range_proof;

int main(){

    typedef libff::Fields_64 FieldT;

    const std::size_t repeat_num = 100;

    // common parameters
    // N
    const std::size_t range_dim = 6;
    const std::size_t range = 1ull << range_dim;
    // for implemention we set the base as 2
    const std::size_t base = 2;
    const std::size_t instance = 180;
    // rho
    const std::size_t RS_extra_dimension = 3;
    // eta
    std::vector<std::size_t> localization_parameter_array({1,2});
    // lambda
    const std::size_t security_parameter = 128;
    // |F|
    const std::size_t field_size_bits = (long double)(libff::soundness_log_of_field_size_helper<FieldT>(FieldT::zero()));

    libff::enter_block("Configure parameters and generate witness");

    /** Compute other parameters
     * the query repetition parameter according to the conjecture; l
     * the max poly degree when invoking sumcheck instance; k
     * random challenges of verifier;
     * the interactive repetition parameter;
     * the hash output size; |H|
     * achieved soundness bits  **/

    // l - query repetition parameter
    // \sqrt(rho) * (1 + 1/2j), where j is a positive parameter
    // j is related to the interactive soundness error, and this soundness error is related to kmax, it's a circulation
    // we first set a temporary value for \sqrt(rho), then check if this is valied
    double rate_sqrt = sqrt(1/double(1ull << RS_extra_dimension));
    std::cout << "rate_sqrt is " << rate_sqrt << std::endl;
    std::cout << "log2(rate_sqrt) is " << log2(rate_sqrt) << std::endl;
    std::cout << "-1 * security_parameter / log2(rate_sqrt) is " << -1 * double(security_parameter) / (log2(rate_sqrt)) << std::endl;


    std::size_t query_repetition_parameter = -1 * double(security_parameter) / (log2(rate_sqrt))  + 1;

    std::cout << "query_repetition_parameter is " << query_repetition_parameter << std::endl;

    /** the max poly degree
     * Two kinds constraints, one is binary constraint, one is location constraint
     * For binary constraint in zk, deg(secret poly) = 2*(n + l) - 1. deg (sumcheck poly) = (3n + 2l) -2
     * For location constraint in zk, deg(secret poly) = n + l , deg (sumcheck poly ) = (2n + l) - 1
     * So k = (3n + 2l) -2
     * Note that we should padding k to 2^? for FRI **/
    const std::size_t sum_degree_bound = base * ( range + query_repetition_parameter ) +  range - base;
    std::size_t FRI_degree_bound = libff::round_to_next_power_of_2(sum_degree_bound);

    // random challenges of verifier
    /** # random challengs are related to security parameter
     * Note that all these polynomials are with the same secret polys, and could be invoked in one IPA**/
    const std::size_t challenge_vector_number = ceil(double(security_parameter) / field_size_bits);

    /** determine the polynomials and domains **/
    field_subset<FieldT> summation_domain(range);
    field_subset<FieldT> codeword_domain(FRI_degree_bound << RS_extra_dimension , FieldT(FRI_degree_bound<< RS_extra_dimension));
    // every instance will have two pairs of polynomials,
    std::size_t poly_number = instance * 2 * challenge_vector_number;
    std::size_t codeword_domain_size = codeword_domain.num_elements();
    std::cout << "codeword_domain_size is " << codeword_domain_size << std::endl;

    // interactive repetition parameter
    /** the interactive repetition parameter of FRI
     *  \epsilon = fenzi / (|F|^e), here we suppose e = 3, this is the same as conjecture setting
     *  fenzi_1 = (instance - 1/2) * pow(1/2 + j , 7) * (1/2) * pow(RS_extra_dimension, 2/3) * pow(codeword_domain_size, 2)
     *  fenzi_2 =
     *  **/
    std::size_t target_inter_security_bits = security_parameter + 1;
    std::size_t sum_eta = 0;
    double fenmu = pow((1ull << field_size_bits) , 3);
    std::cout << "fenmu is " << fenmu << std::endl;
    for (std::size_t i = 0; i < localization_parameter_array.size() ; i++)
    {
        sum_eta += (1ull << localization_parameter_array[i]);
    }
    std::size_t john_bound = 3;
    bool flag = 1;
    while (flag)
    {
        john_bound+=1;
        double fenzi_1 = double(instance - 1/2) * pow(john_bound + 0.5 , 7) * 0.5 * pow( (1ull<<RS_extra_dimension), 3/2) * pow(codeword_domain_size, 2);
        //std::cout << "fenzi_1 is " << fenzi_1 << std::endl;
        double fenzi_2 = (2*john_bound +1 ) * (codeword_domain_size + 1) * (sum_eta);
        //std::cout << "fenzi_2 is " << fenzi_2 << std::endl;
        if ((double(fenzi_1 / fenmu)) > (double(1/(pow(2,target_inter_security_bits)))) )
        {
            //std::cout << "fdouble (fenzi_1 / fenmu) is " << double (fenzi_1 / fenmu) << std::endl;
            john_bound -= 1;
            flag = 0;
        }
        if ((double(fenzi_2 / fenmu)) > (double(1/(pow(2,target_inter_security_bits)))) ) {
            //std::cout << "fdouble (fenzi_2 / fenmu) is " << double(fenzi_2 / fenmu) << std::endl;
            john_bound -= 1;
            flag = 0;
        }
    }

    const std::size_t inter_repetition_parameter = 3;

    // correct the query parameter
    query_repetition_parameter = -1 * double(security_parameter) / (log2(rate_sqrt * (1+ 1/(2*john_bound))))  + 1;
    std::cout << "query_repetition_parameter is " << query_repetition_parameter << std::endl;

    // hash function parameter
    const std::size_t hash_ouput_size = 256;

    /** compute achieved soundness parameter **/
    std::size_t hadamard_to_inner_error = challenge_vector_number * field_size_bits;

    double fenzi_1 = double(instance - 1/2) * pow(john_bound + 0.5 , 7) * 0.5 * pow( (1ull<<RS_extra_dimension), 3/2) * pow(codeword_domain_size, 2);
    //std::cout << "fenzi_1 is " << fenzi_1 << std::endl;
    double fenzi_2 = (2*john_bound +1 ) * (codeword_domain_size + 1) * (sum_eta);
    std::size_t FRI_interactive_error = - log2(double ((fenzi_1 + fenzi_2)/(fenmu)));

    double FRI_query_error = - log2(pow(rate_sqrt * (1 + john_bound/(2*john_bound)),query_repetition_parameter));
    assert(FRI_query_error >= double(security_parameter));

    std::size_t achieved_soundness = std::min<std::size_t>({hadamard_to_inner_error,FRI_interactive_error, std::size_t(FRI_query_error)}) ;


     printf("\nRange proof parameters\n");
    libff::print_indent(); printf("* target security parameter = %zu\n", security_parameter);
    libff::print_indent(); printf("* achieved security parameter = %zu\n", achieved_soundness);
    libff::print_indent(); printf("* range dim = %zu\n", range_dim);
    libff::print_indent(); printf("* poly degree bound = %zu\n", range_dim);
    libff::print_indent(); printf("* RS extra dimensions = %zu\n", RS_extra_dimension);
    libff::print_indent(); printf("* field size bits = %zu\n", field_size_bits);
    libff::print_indent(); printf("* the whole protocol interactions = challenge_vector_number  = %zu\n", challenge_vector_number);
    libff::print_indent(); printf("* FRI interactive repetitions = %zu\n", inter_repetition_parameter);
    libff::print_indent(); printf("* john_bound = %zu\n", john_bound);
    libff::print_indent(); printf("* FRI query repetitions = %zu\n", query_repetition_parameter);
    libff::print_indent(); printf("* summation degree bound = %zu\n", sum_degree_bound);
    libff::print_indent(); printf("* FRI degree bound = %zu\n", FRI_degree_bound);

    /** Generate random secret vectors **/
    std::vector<std::vector<FieldT>> secret_vectors;
    secret_vectors.resize(instance);
    for (std::size_t i = 0; i < instance; i++)
    {
        secret_vectors[i].resize(range);
        for (std::size_t j = 0; j < range; j ++)
        {
            std:size_t random_element = std::rand() % 2;
            secret_vectors[i][j] = FieldT(random_element);
        }
    }

    libff::leave_block("Configure parameters and generate witness");

    std::size_t repeat;
    struct timeval prover_start,prover_end;
    float prover_time = 0;
    struct timeval verifier_start,verifier_end;
    float verifier_time = 0;
    struct timeval pubpoly_start,pubpoly_end;
    float pubpoly_time = 0;

    double total_proof_size_field = 0;
    double total_proof_size_hash = 0;

    for (repeat = 0; repeat < repeat_num; repeat ++) {
        /** Generate random secret vectors **/
        std::vector<std::vector<FieldT>> secret_vectors;
        secret_vectors.resize(instance);
        for (std::size_t i = 0; i < instance; i++) {
            secret_vectors[i].resize(range);
            for (std::size_t j = 0; j < range; j++) {
                std::size_t random_element = std::rand() % 2;
                secret_vectors[i][j] = FieldT(random_element);
            }
        }

    /** Range Proof Prover **/

    libff::enter_block("Range proof prover");
    gettimeofday(&prover_start, nullptr);

    libff::enter_block("Initial polynomials and target sum");

    libff::enter_block("Initial secret polynomials and compute evaluations");

    /** There are total poly_number = instance * 2 * challenge_vector_number
     * here we take challenge_vector_number = 2 as an example
     * we arrange according to the following order:
     * binary_poly_1 - challenge_vector_1_poly_1
     * location_poly_1 - challenge_vector_1_poly_2
     * binary_poly_1 - challenge_vector_2_poly_1
     * location_poly_1 - challenge_vector_2_poly_2
     * binary_poly_2 - challenge_vector_1_poly_1
     * location_poly_2 - challenge_vector_1_poly_2
     * binary_poly_2 - challenge_vector_2_poly_1
     * location_poly_2 - challenge_vector_2_poly_2
     * ... **/

    // constant polynomial
    vanishing_polynomial<FieldT> vanishing_polynomial(summation_domain);

    std::vector<polynomial<FieldT>> IPA_sec_polys;
    IPA_sec_polys.resize(poly_number);

    std::vector<std::vector<FieldT>> IPA_sec_evaluations;
    IPA_sec_evaluations.resize(poly_number);

    // only secret 0/1 vectors
    std::vector<std::vector<FieldT>> secret_vector_only_evaluations;
    secret_vector_only_evaluations.resize(instance);

    for (std::size_t i = 0; i < 2 * instance * challenge_vector_number ; i += (2 * challenge_vector_number))
    {
        for (std::size_t j = 0; j < 2 * challenge_vector_number; j += 2)
        {
            if (j==0){
                polynomial<FieldT> secret_poly = polynomial<FieldT> (IFFT_over_field_subset(secret_vectors[i/(2*challenge_vector_number)],summation_domain));
                std::vector<FieldT> constant_vec(1,FieldT::one());
                polynomial<FieldT> secret_poly_1 = secret_poly - polynomial<FieldT> (std::move(constant_vec));

                secret_vector_only_evaluations[i/(2*challenge_vector_number)] = FFT_over_field_subset(secret_poly.coefficients(),codeword_domain);

                // random masking polynomial
                polynomial<FieldT> random_poly = polynomial<FieldT>::random_polynomial(query_repetition_parameter);
                polynomial<FieldT> binary_poly = secret_poly.multiply(secret_poly_1) + vanishing_polynomial*random_poly;
                polynomial<FieldT> location_poly = secret_poly + vanishing_polynomial*random_poly;

                IPA_sec_polys[i + j] = binary_poly;
                IPA_sec_evaluations[i+j] = FFT_over_field_subset(IPA_sec_polys[i+j].coefficients(),codeword_domain);
                IPA_sec_polys[i+j+1] = location_poly;
                IPA_sec_evaluations[i+j+1] = FFT_over_field_subset(IPA_sec_polys[i+j+1].coefficients(),codeword_domain);
            }
            else{
                IPA_sec_polys[i + j] = IPA_sec_polys[i];
                IPA_sec_evaluations[i+j] = IPA_sec_evaluations[i];
                IPA_sec_polys[i+j+1] = IPA_sec_polys[i+1];
                IPA_sec_evaluations[i+j+1] = IPA_sec_evaluations[i+1];
            }
        }
    }

    libff::leave_block("Initial secret polynomials and compute evaluations");

    libff::enter_block("Initial public polynomials and compute evaluations");
    /**This block time should be added to the verifier time too**/
    /** There are total poly_number = instance * 2 * challenge_vector_number
     * here we take challenge_vector_number = 2 as an example
     * we arrange according to the following order:
     * binary_poly_1 - challenge_vector_1_poly_1
     * location_poly_1 - challenge_vector_1_poly_2
     * binary_poly_1 - challenge_vector_2_poly_1
     * location_poly_1 - challenge_vector_2_poly_2
     * binary_poly_2 - challenge_vector_1_poly_1
     * location_poly_2 - challenge_vector_1_poly_2
     * binary_poly_2 - challenge_vector_2_poly_1
     * location_poly_2 - challenge_vector_2_poly_2
     * ...
     *
     * For public polys, there are also two kinds,
     * one is binary_pub_poly, r^{m}
     * one is location_pub_poly, if assuming m = n, this poly is indeed unnecessary, r^{m-n}||0^{n}
     * **/

    gettimeofday(&pubpoly_start, nullptr);

    std::vector<std::vector<FieldT>> public_vectors;
    public_vectors.resize(challenge_vector_number);

    for (std::size_t i = 0; i < challenge_vector_number; i++)
    {
        public_vectors[i].resize(range);
        for (std::size_t j = 0; j < range; j ++)
        {
            std::size_t random_element = std::rand();
            public_vectors[i][j] = FieldT(random_element);
        }
    }

    std::vector<polynomial<FieldT>> public_polys;
    public_polys.resize(challenge_vector_number);

    //TODO
    std::vector<std::vector<FieldT>> public_poly_evaluations;
    public_poly_evaluations.resize(challenge_vector_number);

    for (std::size_t i = 0; i < challenge_vector_number; i ++)
    {
        public_polys[i] = polynomial<FieldT> (IFFT_over_field_subset(public_vectors[i], summation_domain));
        public_poly_evaluations[i] = FFT_over_field_subset(public_polys[i].coefficients(), codeword_domain);
    }

    std::vector<polynomial<FieldT>> IPA_pub_polys;
    IPA_pub_polys.resize(poly_number);

    std::vector<std::vector<FieldT>> IPA_pub_evaluations;
    IPA_pub_evaluations.resize(poly_number);

    std::vector<FieldT> constant_vec_pub(1,FieldT::zero());
    polynomial<FieldT> constant_vec_poly = polynomial<FieldT> (std::move(constant_vec_pub));
    std::vector<FieldT> constant_vec_poly_eva = FFT_over_field_subset(constant_vec_poly.coefficients(), codeword_domain);

    for (std::size_t i = 0; i < (poly_number ); i += 2)
    {
        IPA_pub_polys[i] = public_polys[(i/2)%challenge_vector_number];
        IPA_pub_evaluations[i] = public_poly_evaluations[(i/2)%challenge_vector_number];

        std::vector<FieldT> constant_vec_pub(1,FieldT::zero());
        IPA_pub_polys[i+1] = constant_vec_poly;
        IPA_pub_evaluations[i + 1] = constant_vec_poly_eva;
    }

    /** generate \gamma(x), it equals to add a secret poly \gamma(x) and a public poly 1 **/
    polynomial<FieldT> gamma = polynomial<FieldT>::random_polynomial(sum_degree_bound);
    std::vector<FieldT> gamma_eva = FFT_over_field_subset(gamma.coefficients(), codeword_domain);

    std::vector<FieldT> constant_vec(1, FieldT::one());
    polynomial<FieldT> constant_poly = polynomial<FieldT> (std::move(constant_vec));
    std::vector<FieldT> constant_poly_eva = FFT_over_field_subset(constant_poly.coefficients(), codeword_domain);

    IPA_sec_polys.resize(instance+1);
    IPA_sec_polys[instance] = gamma;
    IPA_pub_polys.resize(instance+1);
    IPA_pub_polys[instance] = constant_poly;

    IPA_sec_evaluations.resize(instance+1);
    IPA_sec_evaluations[instance] = gamma_eva;
    IPA_pub_evaluations.resize(instance+1);
    IPA_pub_evaluations[instance] = constant_poly_eva;

    // compute Gamma
    FieldT Gamma = FieldT::zero();
    std::cout << "IPA_sec_polys.size() is " << IPA_sec_polys.size() << std::endl;

    for (auto i: summation_domain.all_elements())
    {
        Gamma += gamma.evaluation_at_point(i) * constant_poly.evaluation_at_point(i);
    }
    //std::cout << "Gamma is " << Gamma << std::endl;

    FieldT target_sum = Gamma;

    // check the inner product argument
//    /**Note here must be next to power of 2**/
//    std::size_t extended_summation_domain_size = libff::round_to_next_power_of_2(sum_degree_bound);
//    field_subset<FieldT> extended_summation_domain(extended_summation_domain_size);
//    FieldT val1 = FieldT::zero();
//    for (std::size_t i = 0 ; i < (IPA_sec_polys.size()); i++){
//        std::vector<FieldT> secret_eval = FFT_over_field_subset(IPA_sec_polys[i].coefficients(), extended_summation_domain);
//        std::vector<FieldT> public_eval = FFT_over_field_subset(IPA_pub_polys[i].coefficients(), summation_domain);
//         //here must be public_eval.size()
//        for(std::size_t j = 0 ; j < summation_domain.num_elements() ; j++){
//            std::size_t idx = extended_summation_domain.reindex_by_subset(summation_domain.dimension(), j);
//            val1+=secret_eval[idx]*public_eval[j];
//        }
//        // another straightforward way
////        for (auto j: summation_domain.all_elements())
////        {
////            val1 += (IPA_sec_polys[i].evaluation_at_point(j) * IPA_pub_polys[i].evaluation_at_point(j));
////        }
//    }
//    assert(val1 == target_sum);

    gettimeofday(&pubpoly_end, nullptr);
    pubpoly_time += (pubpoly_end.tv_usec-pubpoly_start.tv_usec)/1000000.0 + pubpoly_end.tv_sec-pubpoly_start.tv_sec;
    libff::leave_block("Initial public polynomials and compute evaluations");
    libff::leave_block("Initial polynomials and target sum");

    libff::enter_block("Generating Merkle tree roots");

    std::vector<std::size_t> IPA_query_set;
    IPA_query_set.clear();
    for (std::size_t i = 0; i < query_repetition_parameter; ++i)
    {
        bool is_repeat = true;
        std::size_t val;
        while(is_repeat){
            val = std::rand() % (codeword_domain.num_elements()>> localization_parameter_array[0]);
            std::vector<std::size_t>::iterator it;
            it = find(IPA_query_set.begin(),IPA_query_set.end(),val);
            if(it == IPA_query_set.end()){
                is_repeat = false;
            }
        }
        IPA_query_set.emplace_back(val);
    }

    for (auto &i: IPA_query_set) {
        i %= (codeword_domain.num_elements() >> localization_parameter_array[0]);
    }
    std::vector<std::size_t> tmp;
    std::sort(IPA_query_set.begin(), IPA_query_set.end());
    tmp.push_back(IPA_query_set[0]);
    for (std::size_t i = 1; i < IPA_query_set.size(); i++) {
        if (IPA_query_set[i] != IPA_query_set[i - 1]) {
            tmp.push_back(IPA_query_set[i]);
        }
    }
    IPA_query_set = tmp;

    for (auto & i : IPA_query_set)
    {
        i += ((codeword_domain.num_elements() >> localization_parameter_array[0]) - 1);
    }

    /** It only needs to commit every secret evaluations once as the verifier can construct virtual oracles
     * There is an optimization that every evaluation can be spilt and aggregated together,
     * this is related to the localization array**/

    std::vector<std::vector<FieldT>> commit_matrix;
    commit_matrix.resize( (1ull << localization_parameter_array[0]) * (instance + 1) );
    for (std::size_t i = 0; i < instance; i++)
    {
        for (std::size_t j = 0; j < (1ull << localization_parameter_array[0]); j ++){
            for (std::size_t k = 0; k < (codeword_domain.num_elements() >> localization_parameter_array[0]); k ++){
                commit_matrix[(i*(1ull<<localization_parameter_array[0]))+j].push_back
                        (secret_vector_only_evaluations[i][k+j*(codeword_domain.num_elements() >> localization_parameter_array[0])]);
            }
        }
    }

    for (std::size_t j = 0; j < (1ull << localization_parameter_array[0]); j ++){
        for (std::size_t k = 0; k < (codeword_domain.num_elements() >> localization_parameter_array[0]); k ++){
            commit_matrix[(instance*(1ull<<localization_parameter_array[0]))+j].push_back
                    (gamma_eva[k+j*(codeword_domain.num_elements() >> localization_parameter_array[0])]);
        }
    }

    // true is every column put in one leaf
    std::shared_ptr<range_proof::merkle<FieldT>> secret_vector_tree;
    secret_vector_tree.reset(new merkle<FieldT>(
            codeword_domain.num_elements() >> localization_parameter_array[0],
            IPA_query_set,
            true
    ));

    range_proof::merkleTreeParameter par_for_secret_vector;
    par_for_secret_vector = secret_vector_tree->create_merklePar_of_matrix(commit_matrix);

    libff::leave_block("Generating Merkle tree roots");

    libff::enter_block("Setting parameters");

    // min padding degree
    std::size_t padding_degree = FRI_degree_bound - sum_degree_bound;

    libff::leave_block("Setting parameters");

    libff::enter_block("Setting inner product verifier");

    std::shared_ptr<Inner_product_verifier<FieldT>> IPA_verifier_;
    std::shared_ptr<Inner_product_prover<FieldT>> IPA_prover_;
    std::vector<polynomial<FieldT>> IPA_pub_polys_2 = IPA_pub_polys;

    IPA_verifier_.reset(new Inner_product_verifier<FieldT>(std::move(IPA_pub_polys), summation_domain, std::move(IPA_sec_evaluations),
                                                                 std::move(IPA_pub_evaluations), padding_degree, FRI_degree_bound,
                                                                 localization_parameter_array, codeword_domain, target_sum, inter_repetition_parameter));

    libff::leave_block("Setting inner product verifier");

    libff::enter_block("Inner Product Prover");
    libff::enter_block("Setting Inner Product Prover and compute the first round");
    IPA_prover_.reset(new Inner_product_prover<FieldT>(std::move(IPA_pub_polys_2), std::move(IPA_sec_polys), IPA_query_set,
                                                             localization_parameter_array, FRI_degree_bound, *(IPA_verifier_), codeword_domain,
                                                             inter_repetition_parameter));
    libff::leave_block("Setting Inner Product Prover and compute the first round");

    libff::enter_block("Proving all the remained rounds for FRI");
    IPA_prover_->prove(IPA_query_set);
    libff::leave_block("Proving all the remained rounds for FRI");

    libff::leave_block("Inner Product Prover");

    gettimeofday(&prover_end, nullptr);
    prover_time += (prover_end.tv_usec-prover_start.tv_usec)/1000000.0 + prover_end.tv_sec-prover_start.tv_sec;
    libff::leave_block("Range proof prover");


    /** Range Proof Verifier **/

    libff::enter_block("Inner Product Verifier");
    gettimeofday(&verifier_start, nullptr);
    bool result1 = IPA_verifier_->verify(IPA_query_set, &(*IPA_prover_));

    bool result2 = secret_vector_tree->verify_merkle_commit(par_for_secret_vector);

    gettimeofday(&verifier_end, nullptr);
    verifier_time += (verifier_end.tv_usec-verifier_start.tv_usec)/1000000.0 + verifier_end.tv_sec-verifier_start.tv_sec;
    libff::leave_block("Inner Product Verifier");


    if (!(result1 && result2)){
        libff::print_indent(); printf("error occurs! \n");
    }
    else{
        libff::print_indent(); printf("protocol runs successfully! \n");
    }

    /** Compute the proof size **/

    std::size_t secret_vector_tree_hashes = par_for_secret_vector.path_lenth;
    std::size_t h_tree_hashes = IPA_prover_->h_tree_lenth;
    std::size_t FRI_trees_hashes = IPA_prover_->FRI_tree_lenth ;
    std::size_t proof_size_path_hash_number = secret_vector_tree_hashes + h_tree_hashes + FRI_trees_hashes;
    std::size_t proof_size_roots_hash_number = 1 + 1 + (localization_parameter_array.size() * inter_repetition_parameter);
    std::size_t proof_size_hash_number = proof_size_roots_hash_number + proof_size_path_hash_number;
    double proof_size_hash = double((proof_size_hash_number * hash_ouput_size)/1024.0/8.0);
    total_proof_size_hash += proof_size_hash;

    //std::cout << "proof_size_hash_number is " << proof_size_hash_number << std::endl;
    //std::cout << "secret_vector_tree_hashes is " << secret_vector_tree_hashes*hash_ouput_size/1024/8 << std::endl;
    //std::cout << "h_tree_hashes is " << h_tree_hashes*hash_ouput_size/1024/8 << std::endl;
    //std::cout << "FRI_tree_hashes is " << FRI_trees_hashes*hash_ouput_size/1024/8 << std::endl;
    //std::cout << "proof_size_hash is " << proof_size_hash << std::endl;

    std::size_t proof_size_field_number = 0;
    std::size_t poly_degree_bound_last_round = FRI_degree_bound;
    // Note that it is necessary to query (query number) times in all rounds instead of each round
    for (std::size_t i = 0 ; i < localization_parameter_array.size() ; i++)
    {
        if (i==0)
        {
            // v field number
            proof_size_field_number +=  (instance+1) * query_repetition_parameter * ( 1 << localization_parameter_array[i]);
            // h field number
            proof_size_field_number += query_repetition_parameter * ( 1 << localization_parameter_array[i]);
            poly_degree_bound_last_round /= ( 1ull << localization_parameter_array[i]);
        }
        else{
            proof_size_field_number +=  query_repetition_parameter * ( 1 << localization_parameter_array[i]) * inter_repetition_parameter;
            poly_degree_bound_last_round /= ( 1ull << localization_parameter_array[i]);
        }
    }

    // The final_poly proof size
    std::size_t FRI_field_number_last_round = inter_repetition_parameter * (poly_degree_bound_last_round + 1) ;
    proof_size_field_number +=  FRI_field_number_last_round;
    double proof_size_field = double ((proof_size_field_number * field_size_bits)/1024.0/8.0);
    total_proof_size_field += proof_size_field;
    //std::cout << "proof_size_field_number is " << proof_size_field_number << std::endl;
    //std::cout << "proof_size_field is " << proof_size_field << std::endl;

    double total_proof_size = proof_size_field + proof_size_hash;
    //libff::print_indent(); printf("* total proof size = %f\n", total_proof_size);

    }

    std::cout<<"protocol run correctly!"<<std::endl;
    std::cout<<"prover time is "<<std::endl;
    std::cout<<prover_time/repeat_num<<" s"<<std::endl;
    std::cout<<"verifier time is "<<std::endl;
    std::cout<<(verifier_time+pubpoly_time)/repeat_num<<" s"<<std::endl;
    std::cout<<"pubpoly time is "<<std::endl;
    std::cout<<pubpoly_time/repeat_num<<" s"<<std::endl;
    std::cout << "proof size hahs is " <<std::endl;
    std::cout << total_proof_size_hash/repeat_num << std::endl;
    std::cout << "proof size field is " <<std::endl;
    std::cout << total_proof_size_field/repeat_num << std::endl;
    std::cout << "total proof size is " << std::endl;
    std::cout << (total_proof_size_hash+ total_proof_size_field)/repeat_num << std::endl;
}


