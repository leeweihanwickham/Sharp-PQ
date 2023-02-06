/**@file
 *****************************************************************************
 Common routines not already present in libff.
 *****************************************************************************
 * @author     This file is part of Aurora in libiop
 * @copyright  MIT license (see LICENSE file)
 *****************************************************************************/
#ifndef range_proof_COMMON_COMMON_HPP_
#define range_proof_COMMON_COMMON_HPP_

#include <cstddef>
#include <cstdio>
#include <cstdint>
#include <iostream>
#include <vector>
#include <math.h>

namespace range_proof {

long double add_soundness_error_bits(const std::size_t bits1, const std::size_t bits2);
long double add_soundness_error_bits(const long double bits1, const long double bits2);

std::ostream &operator<<(std::ostream &os, const std::vector<std::size_t> &input)
{
    for (auto const &i: input) {
        os << i << " ";
    }
    return os;
}

} // namespace range_proof

#endif // range_proof_COMMON_COMMON_HPP_
