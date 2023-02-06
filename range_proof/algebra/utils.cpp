#include <iostream>
#include "range_proof/algebra/utils.hpp"

namespace range_proof {

size_t gcd(const size_t a, const size_t b)
{
    return b == 0 ? a : gcd(b, a % b);
}

}


