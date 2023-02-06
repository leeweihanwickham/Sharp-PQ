/**@file
*****************************************************************************
FRI interfaces.
 This file is part of "A Succinct and Efficient Range Proof with More Functionalities based on Interactive Oracle Proof"
*****************************************************************************
* @author   Weihan Li
*****************************************************************************/
#ifndef PROTOCOLS_LDT_FRI_FRI_LDT_HPP_
#define PROTOCOLS_LDT_FRI_FRI_LDT_HPP_

#include <algorithm>
#include <functional>

#include <libff/algebra/field_utils/field_utils.hpp>
#include "range_proof/algebra/field_subset/subgroup.hpp"
#include "range_proof/algebra/field_subset/subspace.hpp"
#include "range_proof/algebra/polynomials/vanishing_polynomial.hpp"
#include "range_proof/algebra/polynomials/polynomial.hpp"
#include "range_proof/iop/iop.hpp"
#include "range_proof/iop/utilities/batching.hpp"
#include "range_proof/iop/utilities/query_positions.hpp"
#include "range_proof/protocols/ldt/multi_ldt_base.hpp"
#include "range_proof/protocols/ldt/fri/fri_aux.hpp"
#include "range_proof/protocols/ldt/fri/localizer_polynomial.hpp"
#include "range_proof/bcs/Newmerkle.hpp"
namespace range_proof {

/** Notation key
 *   - eta     : We call this the localization_parameter.
 *               We support supplying a vector of localization parameters,
 *               indicating how much to reduce by for each round.
 *               This enables significant proof size savings.
 *   - L^(i)   : This is domains[i] in the code.
 *   - L_0^(i) : This is localizer_domains[i] in the code,
 *               except with the affine shift being the identity.
 *   - q^(i)   : This is the localizer polynomials[i] in the code.
 *               In the multiplicative case, this is X^{2^{localization param}}.
 *               In the additive case, it is the vanishing polynomial for L_0^(i), with no affine shift.
 *   - commit  : We instead call the commit phase, the interactive phase
 *   - multi_* : This implementation supports running multiple FRI instances that all use
 *               the same interactive randomness, and query positions (for proof size reasons).
 *               The prefix multi_ to a variable name means that the final index of the nested vector
 *               is the index for which LDT instance we are in.
 */


template<typename FieldT> class FRI_prover;

template<typename FieldT>
class FRI_verifier {
public:
    std::size_t poly_degree_bound;
    std::vector<FieldT> challenges;
    FRI_prover<FieldT> *prover;
    std::vector<std::size_t> localization_parameter_array;
    field_subset<FieldT> domain_;
    std::vector<std::map<std::size_t, FieldT>> res;
    std::shared_ptr<range_proof::merkle<FieldT>> merkelTree[30];
    std::vector<merkleTreeParameter> pars;
    FRI_verifier(std::size_t poly_degree_bound,
                 std::vector<std::size_t> localization_parameter_array,
                 field_subset<FieldT> &domain);

    bool setProver(FRI_prover<FieldT> *p);
    FieldT getChallenge();
    bool verify(std::vector<std::size_t> query_list, FRI_prover<FieldT> *p, const std::vector<FieldT> &final_poly_coeffs);
};

#include <range_proof/bcs/Newmerkle.hpp>
template<typename FieldT>
class FRI_prover {
public:
    std::vector<std::size_t> localization_parameter_array;
    FRI_verifier<FieldT> *verifier;
    /**why 30 here?
     * A: 30 is enough for almost all situations**/
    std::shared_ptr<std::vector<FieldT>> interpolateValues[30];
    field_subset<FieldT> domain_;
    std::shared_ptr<range_proof::merkle<FieldT>> merkelTree[30];
    std::size_t FRI_tree_lenth;
    std::vector<FieldT> final_poly_coeffs;
    std::vector<std::map<std::size_t, FieldT>> res;
    std::vector<merkleTreeParameter> pars;
    // zuo yin yong
    FRI_prover(const polynomial<FieldT> &poly,
               std::vector<std::size_t> localization_parameter_array,
               FRI_verifier<FieldT> *verifier,
               field_subset<FieldT> &domain);
    // you yin yong
    FRI_prover(polynomial<FieldT> &&poly,
               std::vector<std::size_t> localization_parameter_array,
               FRI_verifier<FieldT> *verifier,
               field_subset<FieldT> &domain);
    // zhi yu; evaluations
    FRI_prover(std::shared_ptr<std::vector<FieldT>> value,
               std::vector<std::size_t> localization_parameter_array,
               FRI_verifier<FieldT> *verifier,
               field_subset<FieldT> &domain);
    void prove(std::vector<std::size_t> query_list);
    void query(std::vector<std::size_t> query_list);
};

template<typename FieldT> class Inner_product_prover;

template<typename FieldT>
class Inner_product_verifier {
    const std::vector<polynomial<FieldT>> s;
    polynomial<FieldT> Z_H;
    std::vector<FRI_verifier<FieldT>*>fri_verifier;
    Inner_product_prover<FieldT> *prover;
    field_subset<FieldT> ldt_domain;
    std::size_t first_round_dim;
    std::size_t round;
    FieldT value;
    std::vector<FieldT> challenge;
    std::vector<std::pair<FieldT, FieldT>> random_pair;
public:
    const std::vector<std::vector<FieldT>> v_evluation_on_codeword_domain;
    const std::vector<std::vector<FieldT>> s_evluation_on_codeword_domain;
    std::vector<std::shared_ptr<range_proof::merkle<FieldT>>> v_trees;
    std::vector<merkleTreeParameter> pars_for_vtrees;
    std::shared_ptr<range_proof::merkle<FieldT>> h_tree;
    merkleTreeParameter par_for_htree;
    field_subset<FieldT> compute_domain;
    Inner_product_verifier(const std::vector<polynomial<FieldT>> &&s,
                           field_subset<FieldT> computed_domain,
                           const std::vector<std::vector<FieldT>> &&v_evluation_on_codeword_domain,
                           const std::vector<std::vector<FieldT>> &&s_evluation_on_codeword_domain,
                           std::size_t padding_degree,
                           std::size_t poly_bound,
                           std::vector<std::size_t> localization_parameter_array,
                           field_subset<FieldT> ldt_domain,
                           FieldT value,
                           std::size_t round);

    std::pair<FieldT, FieldT> getRandomPair();
    FRI_verifier<FieldT> *getFriVerifier(std::size_t idx);
    FieldT getChallenge();
    std::size_t padding_degree;

    bool verify(std::vector<std::size_t> q,Inner_product_prover<FieldT> *p);

};

template<typename FieldT>
class Inner_product_prover {
public:
    const std::vector<polynomial<FieldT>> s;
    const std::vector<polynomial<FieldT>> v;
    polynomial<FieldT> h;
    std::vector<std::shared_ptr<range_proof::merkle<FieldT>>> v_trees;
    std::shared_ptr<range_proof::merkle<FieldT>> h_tree;
    std::vector<FRI_prover<FieldT>*> fri_prover;
    Inner_product_verifier<FieldT> &verifier;
    std::size_t round;
    std::vector<merkleTreeParameter> pars_for_vtrees;
    merkleTreeParameter par_for_htree;
    std::size_t v_tree_length;
    std::size_t h_tree_lenth;
    std::size_t FRI_tree_lenth;
    Inner_product_prover(const std::vector<polynomial<FieldT>> &&s,
                         const std::vector<polynomial<FieldT>> &&v,
                         std::vector<std::size_t> query_set,
                         std::vector<std::size_t>& localization_parameter_array,
                         std::size_t poly_bound,
                         Inner_product_verifier<FieldT> &verifier,
                         field_subset<FieldT> &ldt_domain,
                         std::size_t round);
    void prove(std::vector<std::size_t> query_set);
};


} // namespace range_proof

#include "range_proof/protocols/ldt/fri/fri_ldt.tcc"

#endif // PROTOCOLS_LDT_FRI_FRI_LDT_HPP_
