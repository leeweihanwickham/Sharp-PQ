/**@file
 *****************************************************************************
 Implementation of useful operations over vectors.
 *****************************************************************************
 * @author     This file is part of Aurora in libiop
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/
#ifndef range_proof_ALGEBRA_UTILS_HPP_
#define range_proof_ALGEBRA_UTILS_HPP_

#include <cstdint>
#include <vector>

namespace range_proof {

template<typename T>
void bitreverse_vector(std::vector<T> &a);

template<typename T>
std::vector<T> random_vector(const std::size_t count);

template<typename T>
std::vector<T> all_subset_sums(const std::vector<T> &basis, const T& shift = 0)
#if defined(__clang__)
    ;
#else
    __attribute__((optimize("unroll-loops")));
#endif

template<typename FieldT>
std::vector<FieldT> batch_inverse(const std::vector<FieldT> &vec, const bool has_zeroes=false);

template<typename FieldT>
std::vector<FieldT> batch_inverse_and_mul(const std::vector<FieldT> &vec, const FieldT &k, const bool has_zeroes=false);

template<typename FieldT>
void mut_batch_inverse(std::vector<FieldT> &vec);

/** un-optimized simple GCD procedure */
std::size_t gcd(const std::size_t a, const std::size_t b);

} // namespace range_proof

#include "range_proof/algebra/utils.tcc"

#endif // range_proof_ALGEBRA_UTILS_HPP_
