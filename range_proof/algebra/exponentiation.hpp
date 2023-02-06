/**@file
 *****************************************************************************
 Implementation of exponentiation algorithms.
 *****************************************************************************
 * @author     This file is part of Aurora in libiop
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/
#ifndef range_proof_ALGEBRA_EXPONENTIATION_HPP_
#define range_proof_ALGEBRA_EXPONENTIATION_HPP_

#include "range_proof/algebra/field_subset/field_subset.hpp"
#include "range_proof/algebra/field_subset/subgroup.hpp"
#include "range_proof/algebra/field_subset/subspace.hpp"

namespace range_proof {

template<typename FieldT>
std::vector<FieldT> subset_element_powers(const field_subset<FieldT> &S,
                                          const std::size_t exponent);

template<typename FieldT>
std::vector<FieldT> subspace_element_powers(const affine_subspace<FieldT> &S,
                                            const std::size_t exponent);

template<typename FieldT>
std::vector<FieldT> coset_element_powers(const multiplicative_coset<FieldT> &S,
                                         const std::size_t exponent);

} // namespace range_proof

#include "range_proof/algebra/exponentiation.tcc"

#endif // range_proof_ALGEBRA_EXPONENTIATION_HPP_
