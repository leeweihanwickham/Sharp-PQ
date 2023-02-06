/**@file
*****************************************************************************
Test FRI
 This file is part of "A Succinct and Efficient Range Proof with More Functionalities based on Interactive Oracle Proof"
*****************************************************************************
* @author   Weihan Li
*****************************************************************************/


#include <algorithm>
#include <cstdint>
#include <iostream>

#include <gtest/gtest.h>

#include <libff/algebra/fields/binary/gf64.hpp>
#include <libff/algebra/curves/alt_bn128/alt_bn128_pp.hpp>
#include <libff/algebra/fields/prime_base/fields_64.hpp>
#include <libff/algebra/curves/edwards/edwards_pp.hpp>
#include <libff/algebra/field_utils/field_utils.hpp>
#include "range_proof/algebra/fft.hpp"
#include "range_proof/algebra/field_subset/subgroup.hpp"
#include <libff/common/utils.hpp>
#include "range_proof/iop/iop.hpp"
#include "range_proof/protocols/ldt/fri/fri_ldt.hpp"
#include "range_proof/algebra/polynomials/polynomial.hpp"

namespace range_proof {


template<typename FieldT>
bool run_test(const std::size_t codeword_domain_dim,
              const std::vector<std::size_t> localization_parameter_array,
              const std::size_t RS_extra_dimensions,
              const std::size_t poly_degree_bound,
              const std::size_t num_interactive_repetitions = 0, /* auto filled for 129 bits of security if 0 */
              const std::size_t num_query_repetitions = 0)
{

    /**NOTE: must be domain (1<<size, FieldT(1<<size))
     * do not know why now...**/
    field_subset<FieldT> domain(1 << codeword_domain_dim, FieldT(1 << codeword_domain_dim));
    std::size_t codeword_domain_size = 1 << codeword_domain_dim;
    const polynomial<FieldT> poly = polynomial<FieldT>::random_polynomial(poly_degree_bound);
    // a null value
    FRI_verifier<FieldT> *verifier = new FRI_verifier<FieldT>(poly_degree_bound, localization_parameter_array, domain);
    // 3 kinds function, compute the first inteplot
    FRI_prover<FieldT> *prover = new FRI_prover<FieldT>(poly, localization_parameter_array, verifier, domain);
    //std::vector<std::size_t> query_set = {19260817, 20221130, 238456983, 7056978, 12312, 54976};
    std::vector<std::size_t> query_set;
    for (std::size_t i = 0; i < 10; ++i)
    {
        bool is_repeat = true;
        std::size_t val;
        while(is_repeat){
            //val = std::rand() % (codeword_domain_size);
            val = std::rand() % (codeword_domain_size >> localization_parameter_array[0]);
            std::vector<std::size_t>::iterator it;
            it = find(query_set.begin(),query_set.end(),val);
            if(it == query_set.end()){
                is_repeat = false;
            }
        }
        query_set.emplace_back(val);
    }
    std::sort(query_set.begin(),query_set.end());
    for (std::size_t i = 0; i < query_set.size(); i ++)
    {
        query_set[i] += (codeword_domain_size - 1);
    }
    prover->prove(query_set);
    prover->query(query_set);
    return verifier->verify(query_set, prover, prover->final_poly_coeffs);
}

template<typename FieldT>
bool test_inner_product(const field_subset<FieldT> &compute_domain,
                        std::vector<polynomial<FieldT>> IPA_pub_polys,
                        std::vector<polynomial<FieldT>> IPA_sec_polys,
                        FieldT target_sum,
                        std::size_t security_parameter,
                        std::size_t IPA_RS_extra_dimensions,
        // for FRI, need to padding;
        // next_power_of_two(summation_degree_bound)
                        std::size_t poly_degree_bound,
        // the max degree for degree{IPA_pub_polys[i]*IPA_sec_polys[i]}_{i}
                        std::size_t summation_degree_bound,
        // a parameter for FRI
                        std::vector<std::size_t> localization_parameter_array) {

    // the summation domain, inner product domain
    const std::size_t compute_domain_dim = libff::log2(compute_domain.num_elements());
    // after encoding
    const std::size_t codeword_domain_dim = compute_domain_dim + IPA_RS_extra_dimensions;
    /** NOTE: must be codeword_domain (1<<size, FieldT(1<<size))
     * do not know why now...**/
    // vertical codeword domain
    field_subset<FieldT> ldt_domain(1 << codeword_domain_dim, FieldT(1 << codeword_domain_dim));
    const std::size_t codeword_domain_size = 1 << codeword_domain_dim;

    // compute parameters
    const long double field_size_bits = (long double)(libff::soundness_log_of_field_size_helper<FieldT>(FieldT::zero()));

    /** [2^{(field_size_bits)} ^ {-e}] * poly_degree_bound = 2^{- security_parameter+1}
     * [2^{(field_size_bits)} ^ {-e}]   = 2^{- security_parameter+1} / poly_degree_bound
     * -e * [(field_size_bits)    = {- security_parameter+1} -  log_2(poly_degree_bound)
     * e      = ({security_parameter-1} +  log_2(poly_degree_bound))/ (field_size_bits)**/
    std::size_t inter_repetition = ceil(( security_parameter - 1 + libff::log2(summation_degree_bound) ) / field_size_bits);
    const std::size_t inter_repetition_num = std::max<size_t> (1, inter_repetition);

    /** IPA_RS_extra_dimensions * query_repetition_num > security_parameter **/
    const std::size_t query_repetition_num = ceil((security_parameter/IPA_RS_extra_dimensions)) + 1;

    // generate query_Set
    std::vector<std::size_t> query_set;
    for (std::size_t i = 0; i < query_repetition_num; ++i)
    {
        bool is_repeat = true;
        std::size_t val;
        while(is_repeat){
            val = std::rand() % (codeword_domain_size);
            //val = std::rand() % (codeword_domain_size >> localization_parameter_array[0]);
            std::vector<std::size_t>::iterator it;
            it = find(query_set.begin(),query_set.end(),val);
            if(it == query_set.end()){
                is_repeat = false;
            }
        }
        query_set.emplace_back(val);
    }
//    std::sort(query_set.begin(),query_set.end());
//    for (std::size_t i = 0; i < query_set.size(); i ++)
//    {
//        query_set[i] += (codeword_domain_size - 1);
//    }

    /**Proof size compute**/
    /** NOTE: for v_trees_hashes and h_tree_hashes
     * search TODO: proof size: v_trees related
     * and TODO: proof size: h_tree related
     * and TODO: proof size: FRI_trees related **/
    std::size_t v_trees_hashes = 0;
    std::size_t h_tree_hashes = 0;
    std::size_t FRI_trees_hashes = 0 ;

    /** in range_prooflight, there will only be 1 tree for sec_polys and v_trees_hashes **/
    //TODO the root number needs to be changed as the column width
    std::size_t proof_size_hash_number = IPA_sec_polys.size() + 1 + (localization_parameter_array.size() - 2) // Merkle tree roots number
                                         + v_trees_hashes  + h_tree_hashes + FRI_trees_hashes; // Merkle authenitacation path number.

    std::size_t hash_size = 256;
    std::size_t proof_size_hash = (proof_size_hash_number * hash_size)/1024/8;

    std::size_t proof_size_field_number = 0;
    std::size_t degree_decrease = 0 ;
    for (std::size_t i = 0 ; i < localization_parameter_array.size() ; i++)
    {
        if (i==0)
        {
            proof_size_field_number +=  inter_repetition_num * IPA_sec_polys.size() * ( 1 << localization_parameter_array[i]);
            degree_decrease += ( 1 << localization_parameter_array[i]);
        }
        else{
            proof_size_field_number +=  inter_repetition_num * ( 1 << localization_parameter_array[i]);
            degree_decrease += ( 1 << localization_parameter_array[i]);
        }
    }
    // The final_poly proof size
    proof_size_field_number += inter_repetition_num * (poly_degree_bound - degree_decrease + 1) ;
    std::size_t proof_size_field = (proof_size_field_number * field_size_bits)/1024/8;

    const std::size_t proof_size = proof_size_field + proof_size_hash;
    std::cout << "proof_size_field is " << proof_size_field << std::endl;
    std::cout << "proof_size_hash is " << proof_size_hash << std::endl;

    // The FFT evluation for secret poly
    std::vector<std::vector<FieldT>> IPA_sec_polys_evluation_on_codeword_domain;
    IPA_sec_polys_evluation_on_codeword_domain.resize(IPA_sec_polys.size());
    std::vector<std::vector<FieldT>> IPA_pub_polys_evluation_on_codeword_domain;
    IPA_pub_polys_evluation_on_codeword_domain.resize(IPA_pub_polys.size());
    for (std::size_t i = 0; i < IPA_sec_polys.size() ; i++) {
        IPA_sec_polys_evluation_on_codeword_domain[i] = (FFT_over_field_subset(IPA_sec_polys[i].coefficients(), ldt_domain));
        IPA_pub_polys_evluation_on_codeword_domain[i] = (FFT_over_field_subset(IPA_pub_polys[i].coefficients(), ldt_domain));
    }

    std::size_t padding_degree = poly_degree_bound - summation_degree_bound;

    /** TODO: the input of verifier can be IPA_pub_polys_evaluation_on_codeword_domain
     * But now is poly itself
     * The actual use is evaluation_at_point
     * Need comparison**/
    libff::enter_block("Setting Inner Product Verifier");
    Inner_product_verifier<FieldT> verifier(std::move(IPA_pub_polys), compute_domain,
                                            std::move(IPA_sec_polys_evluation_on_codeword_domain),
                                            std::move(IPA_pub_polys_evluation_on_codeword_domain),
                                            padding_degree, poly_degree_bound, localization_parameter_array,
                                            ldt_domain, target_sum, inter_repetition_num);
    libff::leave_block("Setting Inner Product Verifier");

    libff::enter_block("Inner Product Prover");
    libff::enter_block("Setting Inner Product Prover and compute the first round");
    // TODO: There is no need to commit v_trees in the prover
    // TODO: The commitment for evaluation can also be split
    Inner_product_prover<FieldT> prover(std::move(IPA_pub_polys), std::move(IPA_sec_polys), query_set,
                                        localization_parameter_array, poly_degree_bound, verifier, ldt_domain,
                                        inter_repetition_num);
    libff::leave_block("Setting Inner Product Prover and compute the first round");
    libff::enter_block("Proving all the remained rounds for FRI");
    prover.prove(query_set);
    libff::leave_block("Proving all the remained rounds for FRI");
    libff::leave_block("Inner Product Prover");

    /** Note that the most time for verifier is in verify the first round
     * where Merkle hash tree accouts about half
     * construct f(q) accouts about half **/
    libff::enter_block("Inner Product Verifier");
    bool result = verifier.verify(query_set, &prover);
    if (result){
        libff::print_indent(); printf("Protocol runs successfully! \n");
    }
    else {
        libff::print_indent(); printf("error occurs! \n");
    }
    libff::leave_block("Inner Product Verifier");
    return result;
}


TEST(Rangeproof, SimpleTest){

    typedef libff::Fields_64 FieldT;

    // common parameters
    // N
    const std::size_t range_dim = 9;
    const std::size_t range = 1ull << range_dim;
    const std::size_t base = 2;
    const std::size_t instance = 1;
    // rho
    const std::size_t RS_extra_dimension = 1ull << 4;
    // eta
    const std::vector<std::size_t> localization_parameter_array(2, 2);
    // lambda
    const std::size_t security_parameter = 120;
    // |F|
    const std::size_t field_size_bits = (long double)(libff::soundness_log_of_field_size_helper<FieldT>(FieldT::zero()));
    std::cout << "field_size_bits is " << field_size_bits << std::endl;

    /** Compute other parameters
     * the query repetition parameter according to the conjecture; l
     * the max poly degree when invoking sumcheck instance; k
     * random challenges of verifier;
     * the interactive repetition parameter;
     * the hash output size; |H| TODO: how to set?
     * achieved soundness bits TODO the initial reduction brings 1/|F| soundness error **/

    // l - query repetition parameter
    const std::size_t query_repetition_parameter = ceil( double(security_parameter) / double(libff::log2(RS_extra_dimension)) );
    /** the max poly degree
     * Two kinds constraints, one is binary constraint, one is location constraint
     * For binary constraint in zk, deg(secret poly) = 2*(n + l) - 1. deg (sumcheck poly) = (3n + 2l) -2
     * For location constraint in zk, deg(secret poly) = n + l , deg (sumcheck poly ) = (2n + l) - 1
     * So k = (3n + 2l) -2
     * Note that we should padding k to 2^? for FRI **/
    const std::size_t sum_degree_bound = base * ( range + query_repetition_parameter ) +  range - base;
    const std::size_t FRI_degree_bound = libff::round_to_next_power_of_2(sum_degree_bound);

    // random challenges of verifier
    /** # random challengs are related to security parameter
     * Note that all these polynomials are with the same secret polys, and could be invoked in one IPA**/
    const std::size_t random_vector_number = security_parameter / field_size_bits;
    std::cout << "random_vector_number is " << random_vector_number << std::endl;
        EXPECT_TRUE(0);
}


TEST(FRIMultiplicativeTrueTest, SimpleTest) {
//    libff::alt_bn128_pp::init_public_params();
//
//    typedef libff::alt_bn128_Fr FieldT;

//    libff::edwards_pp::init_public_params();
//    typedef libff::edwards_Fr FieldT;

    typedef libff::Fields_64 FieldT;

    /* Common parameters */
    const std::size_t codeword_domain_dim = 12;
    const std::size_t RS_extra_dimensions = 3; /* \rho = 2^{-RS_extra_dimensions} */

    std::vector<std::size_t> localization_parameter_array(4, 2);
    localization_parameter_array.insert(localization_parameter_array.begin(), 1);

    const std::size_t poly_degree_bound = 1ull << (codeword_domain_dim - RS_extra_dimensions);

    bool result = run_test<FieldT>(codeword_domain_dim, localization_parameter_array, RS_extra_dimensions, poly_degree_bound);
    EXPECT_TRUE(result);
}

TEST(InnerProductTest, SimpleTest) {
//        libff::alt_bn128_pp::init_public_params();
//
//        typedef libff::alt_bn128_Fr FieldT;
    typedef libff::Fields_64 FieldT;

    /* Common parameters */
    const std::size_t codeword_domain_dim = 11;
    const std::size_t RS_extra_dimensions = 2; /* \rho = 2^{-RS_extra_dimensions} */

    std::vector<std::size_t> localization_parameter_array(4, 2);
    localization_parameter_array.insert(localization_parameter_array.begin(), 1);

    const std::size_t poly_degree_bound = 1ull << (codeword_domain_dim - RS_extra_dimensions);
    field_subset<FieldT> compute_domain(poly_degree_bound >> 2, FieldT::random_element());

    std::vector<polynomial<FieldT>> IPA_pub_polys;
    IPA_pub_polys.resize(100);
    for (std::size_t i = 0; i<IPA_pub_polys.size() ; i++)
    {
        IPA_pub_polys[i] = polynomial<FieldT>::random_polynomial((poly_degree_bound >> 2) );
    }

    /** this supports some subpolynomial has degree less than poly_degree_bound **/
    std::vector<polynomial<FieldT>> IPA_sec_polys;
    IPA_sec_polys.resize(100);
    for (std::size_t i = 0; i<(IPA_sec_polys.size()-1) ; i++)
    {
        IPA_sec_polys[i] = polynomial<FieldT>::random_polynomial(poly_degree_bound - IPA_pub_polys[i].degree() - (10));
    }
    for (std::size_t i = (IPA_sec_polys.size()-1); i<IPA_sec_polys.size() ; i++)
    {
        IPA_sec_polys[i] = polynomial<FieldT>::random_polynomial(poly_degree_bound - IPA_pub_polys[i].degree() - (11));
    }

    FieldT target_sum = FieldT::zero();
    // add
    for (auto &i: compute_domain.all_elements()) {
        for (std::size_t j = 0; j < IPA_pub_polys.size(); j++ )
        {
            target_sum += IPA_pub_polys[j].evaluation_at_point(i) * IPA_sec_polys[j].evaluation_at_point(i);
        }
    }

    // compute_domain : systematic domain vertical
    bool result = test_inner_product<FieldT>(compute_domain, IPA_pub_polys, IPA_sec_polys, target_sum, 100, RS_extra_dimensions,
                                             poly_degree_bound, poly_degree_bound-10, localization_parameter_array);
    EXPECT_TRUE(result);
}


}
