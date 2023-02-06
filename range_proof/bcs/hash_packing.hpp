// 封装blake3
#ifndef range_proof_HASHING_PACKING_HPP_
#define range_proof_HASHING_PACKING_HPP_
namespace range_proof{
template<typename FieldT>
class blake3HASH{
public:
    std::vector<uint8_t> get_one_hash(const std::vector<FieldT> &target);
    std::vector<uint8_t> two_to_one_hash(std::vector<uint8_t> target1, std::vector<uint8_t> target2);
    std::vector<uint8_t> get_element_hash(const FieldT &target);
};
}
#include "range_proof/bcs/hash_packing.tcc"
#endif