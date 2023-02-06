#include <vector>
#include "depends/libff/libff/algebra/fields/prime_base/fields_64.hpp"

void paralle_random_element(std::vector<libff::Fields_64> &result,
                            std::size_t index,
                            std::size_t limit){
    for (std::size_t i = index; i < index+limit; i++) {
        result[i]=libff::Fields_64::random_element();
    }
}
