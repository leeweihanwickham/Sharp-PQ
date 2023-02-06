#include "hash_packing.hpp"
#ifdef __cplusplus
extern "C" {
#include "BLAKE3/blake3.h"
}
#endif
namespace range_proof {


template<typename FieldT>
std::vector<uint8_t> blake3HASH<FieldT>::get_one_hash(const std::vector<FieldT> &target) {
//    输出长度256bit
    uint8_t out[BLAKE3_OUT_LEN];
    blake3_hasher hasher;
    blake3_hasher_init(&hasher);
    auto *buf=(unsigned char*)&target[0];
    std::size_t n=sizeof(FieldT) * target.size();//sizeof(std::size_t)=8 sizeof实际上是获取了数据在内存中所占用的存储空间，以字节为单位来计数
    blake3_hasher_update(&hasher, buf, n);
    blake3_hasher_finalize(&hasher, out, BLAKE3_OUT_LEN);
    std::vector<uint8_t>res(out,out+ BLAKE3_OUT_LEN );
    return res;
}

template<typename FieldT>
std::vector<uint8_t> blake3HASH<FieldT>::get_element_hash(const FieldT &target) {
    uint8_t out[BLAKE3_OUT_LEN];
    blake3_hasher hasher;
    blake3_hasher_init(&hasher);
    std::size_t n=sizeof(FieldT);
    auto *buf=(unsigned char*)&target;
    blake3_hasher_update(&hasher, buf, n);
    blake3_hasher_finalize(&hasher, out, BLAKE3_OUT_LEN);
    std::vector<uint8_t>res(out,out+ BLAKE3_OUT_LEN );
    return res;
}

template<typename FieldT>
std::vector<uint8_t> blake3HASH<FieldT>::two_to_one_hash(std::vector<uint8_t> target1, std::vector<uint8_t> target2) {
    assert(target1.size() == target2.size());
    assert(target1.size() == BLAKE3_OUT_LEN);
    target1.insert(target1.end(), target2.begin(), target2.end());
    uint8_t out[BLAKE3_OUT_LEN];
    blake3_hasher hasher;
    blake3_hasher_init(&hasher);
    uint8_t *buf = target1.data();
    std::size_t n = BLAKE3_OUT_LEN * 2;
    blake3_hasher_update(&hasher, buf, n);
    blake3_hasher_finalize(&hasher, out, BLAKE3_OUT_LEN);
    std::vector<uint8_t> res(out, out + BLAKE3_OUT_LEN);
    return res;
}


}