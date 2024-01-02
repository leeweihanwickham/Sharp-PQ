/**@file
*****************************************************************************
field for p = 2^^64 - 2^^32 + 1
 This file is part of "Sharp-PQ"
*****************************************************************************/

#ifndef FIELDS_64_HPP
#define FIELDS_64_HPP

#include <libff/algebra/fields/prime_base/fp_64.hpp>
#include <libff/algebra/fields/prime_base/fp.hpp>
#include <libff/algebra/field_utils/algorithms.hpp>
#include <libff/algebra/field_utils/bigint.hpp>

namespace libff {
    typedef Fp_64 Fields_64;
    bigint<1> Fp_64::mod = bigint<1>(0xffffffff00000001ull);
    bigint<1> Fp_64::euler = bigint<1>(9223372034707292160ull);
    bigint<1> Fp_64::t = bigint<1>(4294967295ull); // with t odd
    bigint<1> Fp_64::t_minus_1_over_2 = bigint<1>(2147483647ull);
    Fp_64 Fp_64::nqr = Fp_64(11ull);
    Fp_64 Fp_64::nqr_to_t = Fp_64(2741030659394132017ull);
    Fp_64 Fp_64::multiplicative_generator = Fp_64(11ull);
    Fp_64 Fp_64::root_of_unity = Fp_64(2741030659394132017ull);
    mp_limb_t Fp_64::inv = 18446744069414584319ull;
    bigint<1> Fp_64::Rsquared = bigint<1>(18446744065119617025ull);
    bigint<1> Fp_64::Rcubed = bigint<1>(1);
}


#endif //FIELDS_64_HPP
