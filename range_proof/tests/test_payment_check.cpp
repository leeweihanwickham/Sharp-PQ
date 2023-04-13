//
// Created by leeweihan on 23-4-5.
//


/**@file
*****************************************************************************
Range proofs for when using in a payment system

*****************************************************************************
* @author   Weihan Li
*****************************************************************************/

/**Given commitments to A,B, we first prove A + B = C by an inner product argument, this is transaction balance check
 * Then use the range proof to prove C is in valid range
 * Note that every commitment to C are separate,
 * but the FRI and inner product argument can still batch**/


#include <algorithm>
#include <cstdint>
#include <iostream>

#include <libff/algebra/fields/prime_base/fields_64.hpp>
#include <libff/algebra/field_utils/field_utils.hpp>
#include "range_proof/algebra/fft.hpp"
#include "range_proof/algebra/field_subset/subgroup.hpp"
#include <libff/common/utils.hpp>
#include "range_proof/iop/iop.hpp"
#include "range_proof/protocols/ldt/fri/fri_ldt.hpp"
#include "range_proof/algebra/polynomials/polynomial.hpp"
#include <sys/time.h>

using namespace range_proof;

typedef libff::Fields_64 FieldT;

// a function from a size_t to the vector in field
std::vector<FieldT> decToBin(std::size_t n, std::size_t range)
{
    std::size_t i = 0;
    std::size_t j = 0;
    std::vector<std::size_t> str(range,0);
    std::vector<FieldT> result(range, FieldT::zero());
    if (n == 0)
    {
        return result;
    }
    else
    {
        while (n != 0)
        {
            str[i] = n % 2;
            n /= 2;
            i++;
        }
        for (i = range -1; i != (-1); i--) {
            //printf("%d", str[i]);
            result[j] = FieldT(str[i]);
            j++;
        }
//        for (i = 0; i <result.size(); i ++)
//        {
//            std::cout << result[i];
//        }
        //printf("\n");
        return result;
    }
}

int main(){

    typedef libff::Fields_64 FieldT;

    const std::size_t repeat_num = 100;

    // common parameters
    // N
    const std::size_t range_dim = 6;
    const std::size_t range = 1ull << range_dim;
    // for implemention we set the base as 2
    const std::size_t base = 2;
    const std::size_t instance = 1024;
    // rho
    const std::size_t RS_extra_dimension = 4;
    // eta
    std::vector<std::size_t> localization_parameter_array({1,2});
    // lambda
    const std::size_t security_parameter = 120;
    // |F|
    const std::size_t field_size_bits = (long double)(libff::soundness_log_of_field_size_helper<FieldT>(FieldT::zero()));

    libff::enter_block("Configure parameters and generate witness");

    /** Compute other parameters
     * the query repetition parameter according to the conjecture; l
     * the max poly degree when invoking sumcheck instance; k
     * random challenges of verifier;
     * the interactive repetition parameter;
     * the hash output size; |H| TODO: how to set?
     * achieved soundness bits  **/

    // l - query repetition parameter
    const std::size_t query_repetition_parameter = ceil( double(security_parameter) / RS_extra_dimension );
    /** the max poly degree
     * Two kinds constraints, one is binary constraint, one is location constraint
     * For binary constraint in zk, deg(secret poly) = 2*(n + l) - 1. deg (sumcheck poly) = (3n + 2l) -2
     * For location constraint in zk, deg(secret poly) = n + l , deg (sumcheck poly ) = (2n + l) - 1
     * So k = (3n + 2l) -2
     * Note that we should padding k to 2^? for FRI **/
    //const std::size_t sum_degree_bound = base * ( range + query_repetition_parameter ) +  range - base;
    const std::size_t sum_degree_bound = 3 * range + query_repetition_parameter * 2 * ( 1<<localization_parameter_array[0] ) - 2;
    std::size_t FRI_degree_bound = libff::round_to_next_power_of_2(sum_degree_bound);

    // random challenges of verifier
    /** # random challengs are related to security parameter
     * Note that all these polynomials are with the same secret polys, and could be invoked in one IPA**/
    const std::size_t challenge_vector_number = ceil(double(security_parameter) / field_size_bits);

    // interactive repetition parameter
    /** the interactive repetition parameter of FRI
     *  [2^{(field_size_bits)} ^ {-e}] * poly_degree_bound = 2^{- security_parameter}
     * [2^{(field_size_bits)} ^ {-e}]   = 2^{- security_parameter} / poly_degree_bound
     * -e * [(field_size_bits)    = {- security_parameter} -  log_2(poly_degree_bound)
     * e      = ({security_parameter} +  log_2(poly_degree_bound))/ (field_size_bits)**/
    std::size_t inter_repetition = ceil(double( security_parameter + libff::log2(FRI_degree_bound) ) / field_size_bits);
    const std::size_t inter_repetition_parameter = std::max<size_t> (1, inter_repetition);

    // hash function parameter
    const std::size_t hash_ouput_size = 256;

    /** compute achieved soundness parameter **/
    std::size_t hadamard_to_inner_error = challenge_vector_number * field_size_bits;
    std::size_t FRI_interactive_error = (inter_repetition_parameter * field_size_bits) - ceil(libff::log2(FRI_degree_bound));
    std::size_t FRI_query_error = query_repetition_parameter * RS_extra_dimension;
    std::size_t achieved_soundness = std::min<std::size_t>({hadamard_to_inner_error,FRI_interactive_error,FRI_query_error}) ;

    /** determine the polynomials and domains **/
    field_subset<FieldT> summation_domain(range);
    field_subset<FieldT> codeword_domain(FRI_degree_bound << RS_extra_dimension , FieldT(FRI_degree_bound<< RS_extra_dimension));
    // every instance will have two pairs of polynomials,

    printf("\nRange proof parameters\n");
    libff::print_indent(); printf("* target security parameter = %zu\n", security_parameter);
    libff::print_indent(); printf("* achieved security parameter = %zu\n", achieved_soundness);
    libff::print_indent(); printf("* range dim = %zu\n", range_dim);
    libff::print_indent(); printf("* poly degree bound = %zu\n", range_dim);
    libff::print_indent(); printf("* RS extra dimensions = %zu\n", RS_extra_dimension);
    libff::print_indent(); printf("* field size bits = %zu\n", field_size_bits);
    libff::print_indent(); printf("* the whole protocol interactions = challenge_vector_number  = %zu\n", challenge_vector_number);
    libff::print_indent(); printf("* FRI interactive repetitions = %zu\n", inter_repetition_parameter);
    libff::print_indent(); printf("* FRI query repetitions = %zu\n", query_repetition_parameter);
    libff::print_indent(); printf("* summation degree bound = %zu\n", sum_degree_bound);
    libff::print_indent(); printf("* FRI degree bound = %zu\n", FRI_degree_bound);

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

        /**Generate random secret element and random range **/

        std::vector<std::vector<FieldT>> a_vec;
        a_vec.resize(instance);
        std::vector<std::vector<FieldT>> b_vec;
        b_vec.resize(instance);
        std::vector<std::vector<FieldT>> v_vec;
        v_vec.resize(instance);

        for (std::size_t i = 0; i < instance; i ++) {

            std::size_t A = 0;
            std::size_t B = 0;

            B = std::rand() % (range / 2);

            A = std::rand() % (range / 2);

            std::size_t V = A + B;

            assert( A >= 0 && A < range);
            assert( B >= 0 && B < range);
            assert( V >= 0 && V < range);

            std::vector<FieldT> v = decToBin(V,range);
            v_vec[i] = v;
            std::vector<FieldT> a = decToBin(A,range);
            a_vec[i] = a;
            std::vector<FieldT> b = decToBin(B,range);
            b_vec[i] = b;
        }

        /**
        * binary constraint v need
        * equation constraint v - a - b= 0 need **/

        /** Generate random secret vectors **/

        std::size_t poly_number = instance * 1 * challenge_vector_number + 1 * instance;

        libff::enter_block("Generate old commitments for A and B");

        vanishing_polynomial<FieldT> vanishing_polynomial(summation_domain);

        std::vector<FieldT> zero_vec(1, FieldT::zero());

        /** Initial a secret polynomials
        * **/

        std::vector<polynomial<FieldT>> a_polys;
        a_polys.resize(instance);

        // it is only used for commitments
        std::vector<std::vector<FieldT>> a_polys_loc_evas;
        a_polys_loc_evas.resize(instance);

        for (std::size_t i = 0; i < a_polys.size(); i ++)
        {
            polynomial<FieldT> random_poly = polynomial<FieldT>::random_polynomial(query_repetition_parameter);
            a_polys[i] = polynomial<FieldT> (IFFT_over_field_subset(a_vec[i],summation_domain)) + vanishing_polynomial *  random_poly;
            a_polys_loc_evas[i] = FFT_over_field_subset(a_polys[i].coefficients(),codeword_domain);
            std::vector<FieldT> one_vec(1, FieldT::one());
            polynomial<FieldT> a_polys_i_minus_one = a_polys[i] - polynomial<FieldT>(std::move(one_vec));
            a_polys[i] = a_polys[i].multiply(a_polys_i_minus_one);
        }

        std::vector<std::vector<FieldT>> a_polys_evas;
        a_polys_evas.resize(instance);

        for (std::size_t i = 0; i < a_polys_evas.size(); i ++)
        {
            a_polys_evas[i] = FFT_over_field_subset(a_polys[i].coefficients(),codeword_domain);
        }

        /** Initial b secret polynomials
         **/

        std::vector<polynomial<FieldT>> b_polys;
        b_polys.resize(instance);

        // it is only used for commitments
        std::vector<std::vector<FieldT>> b_polys_loc_evas;
        b_polys_loc_evas.resize(instance);

        for (std::size_t i = 0; i < b_polys.size(); i ++)
        {
            polynomial<FieldT> random_poly = polynomial<FieldT>::random_polynomial(query_repetition_parameter);
            b_polys[i] = polynomial<FieldT> (IFFT_over_field_subset(b_vec[i],summation_domain)) + vanishing_polynomial *  random_poly;
            b_polys_loc_evas[i] = FFT_over_field_subset(b_polys[i].coefficients(),codeword_domain);
            std::vector<FieldT> one_vec(1, FieldT::one());
            polynomial<FieldT> b_polys_i_minus_one = b_polys[i] - polynomial<FieldT>(std::move(one_vec));
            a_polys[i] = b_polys[i].multiply(b_polys_i_minus_one);
        }

        std::vector<std::vector<FieldT>> b_polys_evas;
        b_polys_evas.resize(instance);

        for (std::size_t i = 0; i < b_polys_evas.size(); i ++)
        {
            b_polys_evas[i] = FFT_over_field_subset(a_polys[i].coefficients(),codeword_domain);
        }

        libff::enter_block("Generating Merkle tree roots for A and B");

        std::vector<std::size_t> IPA_query_set;
        IPA_query_set.clear();
        for (std::size_t i = 0; i < query_repetition_parameter; ++i) {
            bool is_repeat = true;
            std::size_t val;
            while (is_repeat) {
                val = std::rand() % (codeword_domain.num_elements() >> localization_parameter_array[0]);
                std::vector<std::size_t>::iterator it;
                it = find(IPA_query_set.begin(), IPA_query_set.end(), val);
                if (it == IPA_query_set.end()) {
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

        for (auto &i: IPA_query_set) {
            i += ((codeword_domain.num_elements() >> localization_parameter_array[0]) - 1);
        }


        std::vector<std::vector<FieldT>> secret_vectors_A;
        secret_vectors_A.insert(secret_vectors_A.end(),a_vec.begin(),a_vec.end());

        std::vector<std::vector<FieldT>> secret_vectors_B;
        secret_vectors_B.insert(secret_vectors_B.end(),b_vec.begin(),b_vec.end());

        std::vector<std::vector<FieldT>> secret_vectors_evas_A;
        secret_vectors_evas_A.insert(secret_vectors_evas_A.end(),a_polys_loc_evas.begin(),a_polys_loc_evas.end());

        std::vector<std::vector<FieldT>> secret_vectors_evas_B;
        secret_vectors_evas_B.insert(secret_vectors_evas_B.end(),b_polys_loc_evas.begin(),b_polys_loc_evas.end());

        std::vector<std::vector<std::vector<FieldT>>> commit_matrixs_A;
        commit_matrixs_A.resize(instance);

        std::vector<std::shared_ptr<range_proof::merkle<FieldT>>> secret_vector_trees_A;
        secret_vector_trees_A.resize(instance);

        std::vector<range_proof::merkleTreeParameter> pars_for_secret_vector_A;
        pars_for_secret_vector_A.resize(instance);

        /** Different from batch range proof, in a payment system merkle trees can not be batched
         * but the FRI can still be batched **/

        for (std::size_t l = 0; l < instance; l ++)
        {
            commit_matrixs_A[l].resize((1ull << localization_parameter_array[0]) * (1 * 1));
            for (std::size_t i = 0; i < (1 * 1); i++) {
                for (std::size_t j = 0; j < (1ull << localization_parameter_array[0]); j++) {
                    for (std::size_t k = 0; k < (codeword_domain.num_elements() >> localization_parameter_array[0]); k++) {
                        commit_matrixs_A[l][(i * (1ull << localization_parameter_array[0])) + j].push_back
                                (secret_vectors_evas_A[l][k + j * (codeword_domain.num_elements()
                                        >> localization_parameter_array[0])]);
                    }
                }
            }

            // true is every column put in one leaf
            secret_vector_trees_A[l].reset(new merkle<FieldT>(
                    codeword_domain.num_elements() >> localization_parameter_array[0],
                    IPA_query_set,
                    true
            ));

            pars_for_secret_vector_A[l] = secret_vector_trees_A[l]->create_merklePar_of_matrix(commit_matrixs_A[l]);
        }

        std::vector<std::vector<std::vector<FieldT>>> commit_matrixs_B;
        commit_matrixs_B.resize(instance);

        std::vector<std::shared_ptr<range_proof::merkle<FieldT>>> secret_vector_trees_B;
        secret_vector_trees_B.resize(instance);

        std::vector<range_proof::merkleTreeParameter> pars_for_secret_vector_B;
        pars_for_secret_vector_B.resize(instance);

        for (std::size_t l = 0; l < instance; l ++)
        {
            commit_matrixs_B[l].resize((1ull << localization_parameter_array[0]) * (1 * 1));
            for (std::size_t i = 0; i < (1 * 1); i++) {
                for (std::size_t j = 0; j < (1ull << localization_parameter_array[0]); j++) {
                    for (std::size_t k = 0; k < (codeword_domain.num_elements() >> localization_parameter_array[0]); k++) {
                        commit_matrixs_B[l][(i * (1ull << localization_parameter_array[0])) + j].push_back
                                (secret_vectors_evas_B[l][k + j * (codeword_domain.num_elements()
                                        >> localization_parameter_array[0])]);
                    }
                }
            }

            // true is every column put in one leaf
            secret_vector_trees_B[l].reset(new merkle<FieldT>(
                    codeword_domain.num_elements() >> localization_parameter_array[0],
                    IPA_query_set,
                    true
            ));

            pars_for_secret_vector_B[l] = secret_vector_trees_B[l]->create_merklePar_of_matrix(commit_matrixs_B[l]);
        }

        libff::leave_block("Generating Merkle tree roots for A and B");

        libff::leave_block("Generate old commitments for A and B");

        /** Range Proof Prover **/

        libff::enter_block("Range proof prover");

        libff::enter_block("Initial polynomials and target sum");

        libff::enter_block("Initial secret polynomials and compute evaluations");

        gettimeofday(&prover_start, nullptr);

        std::vector<polynomial<FieldT>> IPA_sec_polys;
        //IPA_sec_polys.resize(poly_number);

        std::vector<std::vector<FieldT>> IPA_sec_evaluations;
        //IPA_sec_evaluations.resize(poly_number);

        /** Initial v secret polynomials
         * v1(v1-1)-challenge_vector_1
         * v2(v2-1)-challenge_vector_1
         * v1(v1-1)-challenge_vector_2
         * v2(v2-1)-challenge_vector_2**/

        std::vector<polynomial<FieldT>> v_polys;
        v_polys.resize(instance);

        // it is only used for commitments
        std::vector<std::vector<FieldT>> v_polys_loc_evas;
        v_polys_loc_evas.resize(instance);

        for (std::size_t i = 0; i < v_polys.size(); i ++)
        {
            polynomial<FieldT> random_poly = polynomial<FieldT>::random_polynomial(query_repetition_parameter);
            v_polys[i] = polynomial<FieldT> (IFFT_over_field_subset(v_vec[i],summation_domain)) + vanishing_polynomial *  random_poly;
            v_polys_loc_evas[i] = FFT_over_field_subset(v_polys[i].coefficients(),codeword_domain);
            std::vector<FieldT> one_vec(1, FieldT::one());
            polynomial<FieldT> v_polys_i_minus_one = v_polys[i] - polynomial<FieldT>(std::move(one_vec));
            v_polys[i] = v_polys[i].multiply(v_polys_i_minus_one);
        }

        std::vector<std::vector<FieldT>> v_polys_evas;
        v_polys_evas.resize(instance);

        for (std::size_t i = 0; i < v_polys_evas.size(); i ++)
        {
            v_polys_evas[i] = FFT_over_field_subset(v_polys[i].coefficients(),codeword_domain);
        }

        for (std::size_t i = 0; i < challenge_vector_number; i ++)
        {
            IPA_sec_polys.insert(IPA_sec_polys.end(),v_polys.begin(),v_polys.end());
            IPA_sec_evaluations.insert(IPA_sec_evaluations.end(),v_polys_evas.begin(),v_polys_evas.end());
        }

        /** Initial 0 secret polynomials
         * v1 - a1 - b1 - challenge_vector
         * v2 - a2 - b2 - challenge_vector
         * They are all zero!! **/

        polynomial<FieldT> zero_poly = polynomial<FieldT>(std::move(zero_vec));
        std::vector<FieldT> zero_poly_eva(codeword_domain.num_elements(),FieldT::zero());

        IPA_sec_polys.insert(IPA_sec_polys.end(),instance,zero_poly);
        IPA_sec_evaluations.insert(IPA_sec_evaluations.end(),instance,zero_poly_eva);

        libff::leave_block("Initial secret polynomials and compute evaluations");

        libff::enter_block("Initial public polynomials and compute evaluations");
        /**This block time should be added to the verifier time too**/

        /** Initial v secret polynomials
         * v1(v1-1)-challenge_vector_1
         * v2(v2-1)-challenge_vector_1
         * v1(v1-1)-challenge_vector_2
         * v2(v2-1)-challenge_vector_2**/
        /** Initial 0 secret polynomials
        * v1 - a1 - b1 - challenge_vector
        * v2 - a2 - b2 - challenge_vector
        * They are all zero!! **/

        gettimeofday(&pubpoly_start, nullptr);

        std::vector<polynomial<FieldT>> IPA_pub_polys;
        //IPA_pub_polys.resize(poly_number);

        std::vector<std::vector<FieldT>> IPA_pub_evaluations;
        //IPA_pub_evaluations.resize(poly_number);

        /** Generage challenge_vectors **/
        std::vector<std::vector<FieldT>> public_vectors;
        public_vectors.resize(challenge_vector_number);

        for (std::size_t i = 0; i < challenge_vector_number; i++) {
            public_vectors[i].resize(range);
            for (std::size_t j = 0; j < range; j++) {
                std::size_t random_element = std::rand();
                public_vectors[i][j] = FieldT(random_element);
            }
        }

        std::vector<polynomial<FieldT>> public_polys;
        public_polys.resize(challenge_vector_number);

        std::vector<std::vector<FieldT>> public_poly_evaluations;
        public_poly_evaluations.resize(challenge_vector_number);

        for (std::size_t i = 0; i < challenge_vector_number; i++) {
            public_polys[i] = polynomial<FieldT>(IFFT_over_field_subset(public_vectors[i], summation_domain));
            public_poly_evaluations[i] = FFT_over_field_subset(public_polys[i].coefficients(), codeword_domain);
        }

        // (2^N-1, 2^N-2 , ..., 1 )
        std::vector<FieldT> bin_rep_vec;
        bin_rep_vec.resize(range);
        for (std::size_t i = 0; i < range; i ++)
        {
            bin_rep_vec[i] = (1<<i);
        }
        polynomial<FieldT> bin_rep_poly = polynomial<FieldT>(IFFT_over_field_subset(bin_rep_vec,summation_domain));
        std::vector<FieldT> bin_rep_eva = FFT_over_field_subset(bin_rep_poly.coefficients(),codeword_domain);

        for (std::size_t j = 0; j < challenge_vector_number; j ++)
        {
            IPA_pub_polys.insert(IPA_pub_polys.end(),instance,public_polys[j]);
        }

        IPA_pub_polys.insert(IPA_pub_polys.end(),instance,bin_rep_poly);

        for (std::size_t j = 0; j < challenge_vector_number; j ++)
        {
            IPA_pub_evaluations.insert(IPA_pub_evaluations.end(),instance,public_poly_evaluations[j]);
        }

        IPA_pub_evaluations.insert(IPA_pub_evaluations.end(),instance,bin_rep_eva);

        assert(IPA_pub_polys.size() == poly_number);
        assert(IPA_pub_evaluations.size() == poly_number);
        assert(IPA_pub_polys.size() == IPA_sec_polys.size());
        assert(IPA_pub_polys.size() == IPA_pub_evaluations.size());
        assert(IPA_sec_polys.size() == IPA_sec_evaluations.size());

        /** generate \gamma(x), it equals to add a secret poly \gamma(x) and a public poly 1 **/
        polynomial<FieldT> gamma = polynomial<FieldT>::random_polynomial(sum_degree_bound);
        std::vector<FieldT> gamma_eva = FFT_over_field_subset(gamma.coefficients(), codeword_domain);

        std::vector<FieldT> constant_vec(1, FieldT::one());
        polynomial<FieldT> constant_poly = polynomial<FieldT>(std::move(constant_vec));
        std::vector<FieldT> constant_poly_eva = std::vector<FieldT> (codeword_domain.num_elements(),FieldT::one());

        IPA_sec_polys.resize(poly_number + 1);
        IPA_sec_polys[poly_number] = gamma;
        IPA_pub_polys.resize(poly_number + 1);
        IPA_pub_polys[poly_number] = constant_poly;

        IPA_sec_evaluations.resize(poly_number + 1);
        IPA_sec_evaluations[poly_number] = gamma_eva;
        IPA_pub_evaluations.resize(poly_number + 1);
        IPA_pub_evaluations[poly_number] = constant_poly_eva;

        // compute Gamma
        FieldT Gamma = FieldT::zero();

//        for (auto i: summation_domain.all_elements()) {
//            Gamma += gamma.evaluation_at_point(i) * constant_poly.evaluation_at_point(i);
//        }

        std::size_t extended_summation_domain_size = libff::round_to_next_power_of_2(sum_degree_bound);
        field_subset<FieldT> extended_summation_domain(extended_summation_domain_size);
        std::vector<FieldT> gamma_eva_on_summation = FFT_over_field_subset(gamma.coefficients(),extended_summation_domain);
        for(std::size_t j = 0 ; j < summation_domain.num_elements() ; j++){
            std::size_t idx = extended_summation_domain.reindex_by_subset(summation_domain.dimension(), j);
            Gamma+=gamma_eva_on_summation[idx]*FieldT::one();
        }

        FieldT target_sum = Gamma;

        // check the inner product argument
        /**Note here must be next to power of 2**/
        //std::size_t extended_summation_domain_size = libff::round_to_next_power_of_2(sum_degree_bound);
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
//    std::cout << "change poly number" <<std::endl;
//    std::cout << "sum is right" << std::endl;

        gettimeofday(&pubpoly_end, nullptr);
        pubpoly_time += (pubpoly_end.tv_usec-pubpoly_start.tv_usec)/1000000.0 + pubpoly_end.tv_sec-pubpoly_start.tv_sec;
        libff::leave_block("Initial public polynomials and compute evaluations");
        libff::leave_block("Initial polynomials and target sum");

        libff::enter_block("Generating Merkle tree roots");

        std::vector<std::vector<FieldT>> secret_vectors;
        secret_vectors.insert(secret_vectors.end(),v_vec.begin(),v_vec.end());

        std::vector<std::vector<FieldT>> secret_vectors_evas;
        secret_vectors_evas.insert(secret_vectors_evas.end(),v_polys_loc_evas.begin(),v_polys_loc_evas.end());

        std::vector<std::vector<std::vector<FieldT>>> commit_matrixs;
        commit_matrixs.resize(instance);

        std::vector<std::shared_ptr<range_proof::merkle<FieldT>>> secret_vector_trees;
        secret_vector_trees.resize(instance);

        std::vector<range_proof::merkleTreeParameter> pars_for_secret_vector;
        pars_for_secret_vector.resize(instance);

        /** Different from batch range proof, in a payment system merkle trees can not be batched
         * but the FRI can still be batched **/

        for (std::size_t l = 0; l < instance; l ++) {

            commit_matrixs[l].resize((1ull << localization_parameter_array[0]) * (1 * 1 + 1));
            for (std::size_t i = 0; i < (1 * 1); i++) {
                for (std::size_t j = 0; j < (1ull << localization_parameter_array[0]); j++) {
                    for (std::size_t k = 0;
                         k < (codeword_domain.num_elements() >> localization_parameter_array[0]); k++) {
                        commit_matrixs[l][(i * (1ull << localization_parameter_array[0])) + j].push_back
                                (secret_vectors_evas[l][k + j * (codeword_domain.num_elements()
                                        >> localization_parameter_array[0])]);
                    }
                }
            }

            for (std::size_t j = 0; j < (1ull << localization_parameter_array[0]); j++) {
                for (std::size_t k = 0; k < (codeword_domain.num_elements() >> localization_parameter_array[0]); k++) {
                    commit_matrixs[l][(1 * 1 * (1ull << localization_parameter_array[0])) + j].push_back
                            (gamma_eva[k + j * (codeword_domain.num_elements() >> localization_parameter_array[0])]);
                }
            }

            // true is every column put in one leaf

            secret_vector_trees[l].reset(new merkle<FieldT>(
                    codeword_domain.num_elements() >> localization_parameter_array[0],
                    IPA_query_set,
                    true
            ));

            pars_for_secret_vector[l] = secret_vector_trees[l]->create_merklePar_of_matrix(commit_matrixs[l]);

        }

        libff::leave_block("Generating Merkle tree roots");

        libff::enter_block("Setting parameters");

        // min padding degree
        std::size_t padding_degree = FRI_degree_bound - sum_degree_bound;

        libff::leave_block("Setting parameters");


        libff::enter_block("Setting inner product verifier");

        std::shared_ptr<Inner_product_verifier<FieldT>> IPA_verifier_;
        std::shared_ptr<Inner_product_prover<FieldT>> IPA_prover_;
        std::vector<polynomial<FieldT>> IPA_pub_polys_2 = IPA_pub_polys;

        IPA_verifier_.reset(new Inner_product_verifier<FieldT>(std::move(IPA_pub_polys), summation_domain,
                                                               std::move(IPA_sec_evaluations),
                                                               std::move(IPA_pub_evaluations), padding_degree,
                                                               FRI_degree_bound,
                                                               localization_parameter_array, codeword_domain,
                                                               target_sum, inter_repetition_parameter));

        libff::leave_block("Setting inner product verifier");

        libff::enter_block("Inner Product Prover");
        libff::enter_block("Setting Inner Product Prover and compute the first round");
        IPA_prover_.reset(
                new Inner_product_prover<FieldT>(std::move(IPA_pub_polys_2), std::move(IPA_sec_polys), IPA_query_set,
                                                 localization_parameter_array, FRI_degree_bound, *(IPA_verifier_),
                                                 codeword_domain,
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

        libff::enter_block("Range proof Verifier");
        gettimeofday(&verifier_start, nullptr);

        libff::enter_block("Inner product Verifier");
        bool result1 = IPA_verifier_->verify(IPA_query_set, &(*IPA_prover_));
        libff::leave_block("Inner product Verifier");

        libff::enter_block("Merkle tree Verifier");
        bool result = 1;
        bool result2 = 1;
        bool result3 = 1;
        for ( std::size_t l = 0; l < instance ; l ++) {
            result = secret_vector_trees[l]->verify_merkle_commit(pars_for_secret_vector[l]);
            result2 = secret_vector_trees_A[l]->verify_merkle_commit(pars_for_secret_vector_A[l]);
            result3 = secret_vector_trees_B[l]->verify_merkle_commit(pars_for_secret_vector_B[l]);
            if (!(result && result2 && result3 )){
                libff::print_indent();
                printf("error occurs! \n");
            }
        }
        libff::leave_block("Merkle tree Verifier");

        gettimeofday(&verifier_end, nullptr);
        verifier_time += (verifier_end.tv_usec-verifier_start.tv_usec)/1000000.0 + verifier_end.tv_sec-verifier_start.tv_sec;
        libff::leave_block("Range proof Verifier");

        if (!(result1  )) {
            libff::print_indent();
            printf("error occurs! \n");
        } else {
            libff::print_indent();
            printf("protocol runs successfully! \n");
        }

        /** Compute the proof size **/

        std::size_t secret_vector_tree_hashes = (pars_for_secret_vector[0].path_lenth + pars_for_secret_vector_A[0].path_lenth + pars_for_secret_vector_B[0].path_lenth) * instance ;
        std::size_t h_tree_hashes = IPA_prover_->h_tree_lenth;
        std::size_t FRI_trees_hashes = IPA_prover_->FRI_tree_lenth;
        std::size_t proof_size_path_hash_number = secret_vector_tree_hashes + h_tree_hashes + FRI_trees_hashes;
        std::size_t proof_size_roots_hash_number =
                3 + 1 + (localization_parameter_array.size() * inter_repetition_parameter);
        std::size_t proof_size_hash_number = proof_size_roots_hash_number + proof_size_path_hash_number;
        double proof_size_hash = double((proof_size_hash_number * hash_ouput_size) / 1024.0 / 8.0);
        total_proof_size_hash += proof_size_hash;

        //std::cout << "proof_size_hash_number is " << proof_size_hash_number << std::endl;
        //std::cout << "secret_vector_tree_hashes is " << secret_vector_tree_hashes*hash_ouput_size/1024/8 << std::endl;
        //std::cout << "h_tree_hashes is " << h_tree_hashes*hash_ouput_size/1024/8 << std::endl;
        //std::cout << "FRI_tree_hashes is " << FRI_trees_hashes*hash_ouput_size/1024/8 << std::endl;
        //std::cout << "proof_size_hash is " << proof_size_hash << std::endl;

        std::size_t proof_size_field_number = 0;
        std::size_t poly_degree_bound_last_round = FRI_degree_bound;
        // Note that it is necessary to query (query number) times in all rounds instead of each round
        for (std::size_t i = 0; i < localization_parameter_array.size(); i++) {
            if (i == 0) {
                // v field number
                proof_size_field_number +=
                        (3 * instance + 1) * query_repetition_parameter * (1 << localization_parameter_array[i]);
                // h field number
                proof_size_field_number += query_repetition_parameter * (1 << localization_parameter_array[i]);
                poly_degree_bound_last_round /= (1ull << localization_parameter_array[i]);
            } else {
                proof_size_field_number += query_repetition_parameter * (1 << localization_parameter_array[i]) *
                                           inter_repetition_parameter;
                poly_degree_bound_last_round /= (1ull << localization_parameter_array[i]);
            }
        }

        // The final_poly proof size
        std::size_t FRI_field_number_last_round = inter_repetition_parameter * (poly_degree_bound_last_round + 1);
        proof_size_field_number += FRI_field_number_last_round;
        double proof_size_field = double((proof_size_field_number * field_size_bits) / 1024.0 / 8.0);
        total_proof_size_field += proof_size_field;
        //std::cout << "proof_size_field_number is " << proof_size_field_number << std::endl;
        //std::cout << "proof_size_field is " << proof_size_field << std::endl;

        //double total_proof_size = proof_size_field + proof_size_hash;
        //libff::print_indent();
        //printf("* total proof size = %f\n", total_proof_size);
    }

    std::cout<<"protocol run correctly!"<<std::endl;
    std::cout<<"prover time, pubpoly time, verifier time, proof size field, proof size hash is "<<std::endl;
    std::cout<< prover_time/repeat_num<< '\t' << pubpoly_time/repeat_num << '\t' << (verifier_time+pubpoly_time)/repeat_num << '\t'
             << total_proof_size_field/repeat_num << '\t' << total_proof_size_hash/repeat_num << '\t' << (total_proof_size_hash+ total_proof_size_field)/repeat_num << std::endl;
//    std::cout<<"prover time is "<<std::endl;
//    std::cout<<prover_time/repeat_num<<" s"<<std::endl;
//    std::cout<<"verifier time is "<<std::endl;
//    std::cout<<(verifier_time+pubpoly_time)/repeat_num<<" s"<<std::endl;
//    std::cout<<"pubpoly time is "<<std::endl;
//    std::cout<<pubpoly_time/repeat_num<<" s"<<std::endl;
//    std::cout << "proof size hahs is " <<std::endl;
//    std::cout << total_proof_size_hash/repeat_num << std::endl;
//    std::cout << "proof size field is " <<std::endl;
//    std::cout << total_proof_size_field/repeat_num << std::endl;
//    std::cout << "total proof size is " << std::endl;
//    std::cout << (total_proof_size_hash+ total_proof_size_field)/repeat_num << std::endl;
}




