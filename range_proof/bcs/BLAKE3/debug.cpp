#ifdef __cplusplus
extern "C" {
    #include "blake3.h"
}
#endif

#include <cstdio>
#include <cstring>
#include <unistd.h>
#include <iostream>

int main() {

    // Initialize the hasher.
    blake3_hasher hasher;
    blake3_hasher_init(&hasher);
    std::size_t col[17]={0x21389,0x2131234};
    auto *buf=(unsigned char *)col;
// sizeof实际上是获取了数据在内存中所占用的存储空间，以字节为单位来计数
    size_t n=sizeof(col);
    blake3_hasher_update(&hasher, buf, n);

    // Finalize the hash. BLAKE3_OUT_LEN is the default output length, 64 bytes.
    uint8_t output[BLAKE3_OUT_LEN];
    blake3_hasher_finalize(&hasher, output, BLAKE3_OUT_LEN);

    // Print the hash as hexadecimal.
//    for (std::size_t i = 0; i < BLAKE3_OUT_LEN; i++) {
//        printf("%02x", output[i]);
//    }
//    printf("\n");
//    printf("%d",BLAKE3_OUT_LEN);

    return 0;
}
