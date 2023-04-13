/**@file
*****************************************************************************
Range proofs for arbitrary ranges in the conjecture setting
 This file is part of "A Succinct and Efficient Range Proof with More Functionalities based on Interactive Oracle Proof"
*****************************************************************************
* @author   Weihan Li
*****************************************************************************/

// This is a range proof for v \in [A,B] for arbitrary A and B with u^(l-1) < B < u^(l)
/** Its equal to prove that V-A \in [0,u^n -1] \land V- B + u^n \in [0, u^n -1]
 * binary constraint v
 * binary constraint c
 * binary constraint d
 * location constraint c
 * location constraint d
 * equation constraint v - a = c
 * equation constraint v - b + u^n = d **/

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
    const std::size_t range_dim = 5;
    const std::size_t range = 1ull << range_dim;
    // for implemention we set the base as 2
    const std::size_t base = 2;
    const std::size_t instance = 1;
    // rho
    const std::size_t RS_extra_dimension = 3;
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

        std::vector<std::vector<FieldT>> c_vec;
        c_vec.resize(instance);
        std::vector<std::vector<FieldT>> d_vec;
        d_vec.resize(instance);
        std::vector<std::vector<FieldT>> v_vec;
        v_vec.resize(instance);

        for (std::size_t i = 0; i < instance; i ++) {

            std::size_t A;
            std::size_t B = 0;


            B = std::rand() % (range - 5) + 3;

            A = std::rand() % (B - 2);

            std::size_t V = 0;
            while (V <= A) {
                V = std::rand() % (B - A - 1);
                V += A;
            }

//            std::cout << "A is " << A << std::endl;
//            std::cout << "B is " << B << std::endl;
//            std::cout << "V is " << V << std::endl;

            std::size_t C = V - A;
            std::size_t D = V - B + range;
            assert( C >= 0 && C< range);
            assert( D >= 0 && D< range);
            assert( V >= A && V< B);

//            std::cout << "C is " << C << std::endl;
//            std::cout << "D is " << D << std::endl;

            std::vector<FieldT> v = decToBin(V,range);
            v_vec[i] = v;
            std::vector<FieldT> c = decToBin(C,range);
            c_vec[i] = c;
            std::vector<FieldT> d = decToBin(D,range);
            d_vec[i] = d;
        }

//        /** Generate random secret vectors **/
//        std::vector<std::vector<FieldT>> secret_vectors;
//        secret_vectors.resize(instance);
//        for (std::size_t i = 0; i < instance; i++) {
//            secret_vectors[i].resize(range);
//            for (std::size_t j = 0; j < range; j++) {
//                std:
//                size_t random_element = std::rand() % 2;
//                secret_vectors[i][j] = FieldT(random_element);
//            }
//        }


        /** Its equal to prove that V-A \in [0,u^n -1] \land V- B + u^n \in [0, u^n -1]
        * binary constraint v
        * binary constraint c
        * binary constraint d
        * location constraint c; no need now
        * location constraint d; no need now
        * equation constraint v - a -c = 0
        * equation constraint v - b + 2^n - d = 0  **/

        /** Generate random secret vectors **/

        std::size_t poly_number = instance * 3 * challenge_vector_number + 2 * instance;

        /** Range Proof Prover **/

        libff::enter_block("Range proof prover");
        gettimeofday(&prover_start, nullptr);

        libff::enter_block("Initial polynomials and target sum");

        libff::enter_block("Initial secret polynomials and compute evaluations");

        vanishing_polynomial<FieldT> vanishing_polynomial(summation_domain);

        std::vector<FieldT> zero_vec(1, FieldT::zero());

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
        //std::cout<< "IPA_sec_polys.size() is " << IPA_sec_polys.size() << std::endl;

        /** Initial c secret polynomials
         * c1(c1-1)-challenge_vector_1
         * c2(c2-1)-challenge_vector_1
         * c1(c1-1)-challenge_vector_2
         * c2(c2-1)-challenge_vector_2
         * c1 - 0
         * c2 - 0
         * c1 - 0
         * c2 - 0**/

        std::vector<polynomial<FieldT>> c_polys_bin;
        c_polys_bin.resize(instance);
        std::vector<polynomial<FieldT>> c_polys_loc;
        c_polys_loc.resize(instance);

        for (std::size_t i = 0; i < c_polys_bin.size(); i ++)
        {
            std::vector<FieldT> one_vec(1, FieldT::one());
            polynomial<FieldT> random_poly = polynomial<FieldT>::random_polynomial(query_repetition_parameter/2);
            c_polys_loc[i] = polynomial<FieldT> (IFFT_over_field_subset(c_vec[i],summation_domain)) + vanishing_polynomial * random_poly;
            polynomial<FieldT> c_polys_i_minus_one = c_polys_loc[i] - polynomial<FieldT>(std::move(one_vec));
            c_polys_bin[i] = c_polys_loc[i].multiply(c_polys_i_minus_one);
        }

        std::vector<std::vector<FieldT>> c_polys_bin_evas;
        c_polys_bin_evas.resize(instance);

        std::vector<std::vector<FieldT>> c_polys_loc_evas;
        c_polys_loc_evas.resize(instance);

        for (std::size_t i = 0; i < c_polys_bin_evas.size(); i ++)
        {
            c_polys_bin_evas[i] = FFT_over_field_subset(c_polys_bin[i].coefficients(),codeword_domain);
            c_polys_loc_evas[i] = FFT_over_field_subset(c_polys_loc[i].coefficients(),codeword_domain);
        }

        for (std::size_t i = 0; i < challenge_vector_number; i ++)
        {
            IPA_sec_polys.insert(IPA_sec_polys.end(),c_polys_bin.begin(),c_polys_bin.end());
            IPA_sec_evaluations.insert(IPA_sec_evaluations.end(),c_polys_bin_evas.begin(),c_polys_bin_evas.end());
        }
        //std::cout<< "IPA_sec_polys.size() is " << IPA_sec_polys.size() << std::endl;

//        for (std::size_t i = 0; i < challenge_vector_number; i ++)
//        {
//            IPA_sec_polys.insert(IPA_sec_polys.end(),c_polys_loc.begin(),c_polys_loc.end());
//            IPA_sec_evaluations.insert(IPA_sec_evaluations.end(),c_polys_loc_evas.begin(),c_polys_loc_evas.end());
//        }
        //std::cout<< "IPA_sec_polys.size() is " << IPA_sec_polys.size() << std::endl;

        /** Initial d secret polynomials
         * d1(d1-1)-challenge_vector_1
         * d2(d2-1)-challenge_vector_1
         * d1(d1-1)-challenge_vector_2
         * d2(d2-1)-challenge_vector_2
         * d1 - 0
         * d2 - 0
         * d1 - 0
         * d2 - 0**/

        std::vector<polynomial<FieldT>> d_polys_bin;
        d_polys_bin.resize(instance);
        std::vector<polynomial<FieldT>> d_polys_loc;
        d_polys_loc.resize(instance);

        for (std::size_t i = 0; i < d_polys_bin.size(); i ++)
        {
            std::vector<FieldT> one_vec(1, FieldT::one());
            polynomial<FieldT> random_poly = polynomial<FieldT>::random_polynomial(query_repetition_parameter/2);
            d_polys_loc[i] = polynomial<FieldT> (IFFT_over_field_subset(d_vec[i],summation_domain)) + vanishing_polynomial * random_poly;
            polynomial<FieldT> d_polys_i_minus_one = d_polys_loc[i] - polynomial<FieldT>(std::move(one_vec));
            d_polys_bin[i] = d_polys_loc[i].multiply(d_polys_i_minus_one);
        }

        std::vector<std::vector<FieldT>> d_polys_bin_evas;
        d_polys_bin_evas.resize(instance);

        std::vector<std::vector<FieldT>> d_polys_loc_evas;
        d_polys_loc_evas.resize(instance);

        for (std::size_t i = 0; i < d_polys_bin_evas.size(); i ++)
        {
            d_polys_bin_evas[i] = FFT_over_field_subset(d_polys_bin[i].coefficients(),codeword_domain);
            d_polys_loc_evas[i] = FFT_over_field_subset(d_polys_loc[i].coefficients(),codeword_domain);
        }

        for (std::size_t i = 0; i < challenge_vector_number; i ++)
        {
            IPA_sec_polys.insert(IPA_sec_polys.end(),d_polys_bin.begin(),d_polys_bin.end());
            IPA_sec_evaluations.insert(IPA_sec_evaluations.end(),d_polys_bin_evas.begin(),d_polys_bin_evas.end());
        }
        //std::cout<< "IPA_sec_polys.size() is " << IPA_sec_polys.size() << std::endl;

//        for (std::size_t i = 0; i < challenge_vector_number; i ++)
//        {
//            IPA_sec_polys.insert(IPA_sec_polys.end(),d_polys_loc.begin(),d_polys_loc.end());
//            IPA_sec_evaluations.insert(IPA_sec_evaluations.end(),d_polys_loc_evas.begin(),d_polys_loc_evas.end());
//        }
        //std::cout<< "IPA_sec_polys.size() is " << IPA_sec_polys.size() << std::endl;

        /** Initial 0 secret polynomials
         * v1 - a1 - c1 - challenge_vector
         * v2 - a2 - c2 - challenge_vector
         * v1 - b1 - d1 + 2^n - challenge_vector
         * v2 - b2 - d2 + 2^n - challenge_vector
         * They are all zero!! **/

        polynomial<FieldT> zero_poly = polynomial<FieldT>(std::move(zero_vec));
        std::vector<FieldT> zero_poly_eva(codeword_domain.num_elements(),FieldT::zero());

        IPA_sec_polys.insert(IPA_sec_polys.end(),2*instance,zero_poly);
        IPA_sec_evaluations.insert(IPA_sec_evaluations.end(),2*instance,zero_poly_eva);

        //std::cout<< "IPA_sec_polys.size() is " << IPA_sec_polys.size() << std::endl;

        libff::leave_block("Initial secret polynomials and compute evaluations");

        libff::enter_block("Initial public polynomials and compute evaluations");
        /**This block time should be added to the verifier time too**/
        /** There are total poly_number = instance * 2 * challenge_vector_number
         * ...
         *
         * For public polys, there are also two kinds,
         * one is binary_pub_poly, r^{m}
         * one is location_pub_poly, if assuming m = n, this poly is indeed unnecessary, r^{m-n}||0^{n}
         * but we still add it for generality
         * **/

        /** Initial v secret polynomials
         * v1(v1-1)-challenge_vector_1
         * v2(v2-1)-challenge_vector_1
         * v1(v1-1)-challenge_vector_2
         * v2(v2-1)-challenge_vector_2**/
        /** Initial c secret polynomials
            * c1(c1-1)-challenge_vector_1
            * c2(c2-1)-challenge_vector_1
            * c1(c1-1)-challenge_vector_2
            * c2(c2-1)-challenge_vector_2**/
        /** Initial d secret polynomials
         * d1(d1-1)-challenge_vector_1
         * d2(d2-1)-challenge_vector_1
         * d1(d1-1)-challenge_vector_2
         * d2(d2-1)-challenge_vector_2
         **/
        /** Initial 0 secret polynomials
        * v1 - a1 - c1 - challenge_vector
        * v2 - a2 - c2 - challenge_vector
        * v1 - b1 - d1 + 2^n - challenge_vector
        * v2 - b2 - d2 + 2^n - challenge_vector
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
        for (std::size_t j = 0; j < challenge_vector_number; j ++)
        {
            IPA_pub_polys.insert(IPA_pub_polys.end(),instance,public_polys[j]);
        }
        //IPA_pub_polys.insert(IPA_pub_polys.end(),instance*challenge_vector_number,zero_poly);
        for (std::size_t j = 0; j < challenge_vector_number; j ++)
        {
            IPA_pub_polys.insert(IPA_pub_polys.end(),instance,public_polys[j]);
        }
        //IPA_pub_polys.insert(IPA_pub_polys.end(),instance*challenge_vector_number,zero_poly);
        IPA_pub_polys.insert(IPA_pub_polys.end(),instance*2,bin_rep_poly);

        for (std::size_t j = 0; j < challenge_vector_number; j ++)
        {
            IPA_pub_evaluations.insert(IPA_pub_evaluations.end(),instance,public_poly_evaluations[j]);
        }
        for (std::size_t j = 0; j < challenge_vector_number; j ++)
        {
            IPA_pub_evaluations.insert(IPA_pub_evaluations.end(),instance,public_poly_evaluations[j]);
        }
        //IPA_pub_evaluations.insert(IPA_pub_evaluations.end(),instance*challenge_vector_number,zero_poly_eva);
        for (std::size_t j = 0; j < challenge_vector_number; j ++)
        {
            IPA_pub_evaluations.insert(IPA_pub_evaluations.end(),instance,public_poly_evaluations[j]);
        }
        //IPA_pub_evaluations.insert(IPA_pub_evaluations.end(),instance*challenge_vector_number,zero_poly_eva);
        IPA_pub_evaluations.insert(IPA_pub_evaluations.end(),instance*2,bin_rep_eva);

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
        std::cout << "IPA_sec_polys.size() is " << IPA_sec_polys.size() << std::endl;

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

        /** It only needs to commit every secret evaluations once as the verifier can construct virtual oracles
         * There is an optimization that every evaluation can be spilt and aggregated together,
         * this is related to the localization array**/

        std::vector<std::vector<FieldT>> secret_vectors;
        secret_vectors.insert(secret_vectors.end(),v_vec.begin(),v_vec.end());
        secret_vectors.insert(secret_vectors.end(),c_vec.begin(),c_vec.end());
        secret_vectors.insert(secret_vectors.end(),d_vec.begin(),d_vec.end());

        std::vector<std::vector<FieldT>> secret_vectors_evas;
        secret_vectors_evas.insert(secret_vectors_evas.end(),v_polys_loc_evas.begin(),v_polys_loc_evas.end());
        secret_vectors_evas.insert(secret_vectors_evas.end(),c_polys_loc_evas.begin(),c_polys_loc_evas.end());
        secret_vectors_evas.insert(secret_vectors_evas.end(),d_polys_loc_evas.begin(),d_polys_loc_evas.end());

        std::vector<std::vector<FieldT>> commit_matrix;
        commit_matrix.resize((1ull << localization_parameter_array[0]) * (3 * instance + 1));
        for (std::size_t i = 0; i < (3 * instance); i++) {
            for (std::size_t j = 0; j < (1ull << localization_parameter_array[0]); j++) {
                for (std::size_t k = 0; k < (codeword_domain.num_elements() >> localization_parameter_array[0]); k++) {
                    commit_matrix[(i * (1ull << localization_parameter_array[0])) + j].push_back
                            (secret_vectors_evas[i][k + j * (codeword_domain.num_elements()
                                    >> localization_parameter_array[0])]);
                }
            }
        }

        for (std::size_t j = 0; j < (1ull << localization_parameter_array[0]); j++) {
            for (std::size_t k = 0; k < (codeword_domain.num_elements() >> localization_parameter_array[0]); k++) {
                commit_matrix[(3 * instance * (1ull << localization_parameter_array[0])) + j].push_back
                        (gamma_eva[k + j * (codeword_domain.num_elements() >> localization_parameter_array[0])]);
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
        bool result2 = secret_vector_tree->verify_merkle_commit(par_for_secret_vector);
        libff::leave_block("Merkle tree Verifier");

        gettimeofday(&verifier_end, nullptr);
        verifier_time += (verifier_end.tv_usec-verifier_start.tv_usec)/1000000.0 + verifier_end.tv_sec-verifier_start.tv_sec;
        libff::leave_block("Range proof Verifier");

        if (!(result1 && result2)) {
            libff::print_indent();
            printf("error occurs! \n");
        } else {
            libff::print_indent();
            printf("protocol runs successfully! \n");
        }

        /** Compute the proof size **/

        std::size_t secret_vector_tree_hashes = par_for_secret_vector.path_lenth;
        std::size_t h_tree_hashes = IPA_prover_->h_tree_lenth;
        std::size_t FRI_trees_hashes = IPA_prover_->FRI_tree_lenth;
        std::size_t proof_size_path_hash_number = secret_vector_tree_hashes + h_tree_hashes + FRI_trees_hashes;
        std::size_t proof_size_roots_hash_number =
                1 + 1 + (localization_parameter_array.size() * inter_repetition_parameter);
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



