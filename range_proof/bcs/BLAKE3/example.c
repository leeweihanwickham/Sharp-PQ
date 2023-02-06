#include "blake3.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int main(void) {
    // Initialize the hasher.
    blake3_hasher hasher;
    blake3_hasher_init(&hasher);

    // Read input bytes from stdin.
    unsigned char buf[65536];
//  while (1) {
    int a[10]={1,2,3,4,5,6,7,8,9,0};
    int *p=a;


    ssize_t n= read(*p,buf,sizeof(buf));

    if (n > 0) {
        blake3_hasher_update(&hasher, buf, n);
    }


    // Finalize the hash. BLAKE3_OUT_LEN is the default output length, 32 bytes.
    uint8_t output[BLAKE3_OUT_LEN];
    blake3_hasher_finalize(&hasher, output, BLAKE3_OUT_LEN);

    // Print the hash as hexadecimal.
    for (size_t i = 0; i < BLAKE3_OUT_LEN; i++) {
        printf("%02x", output[i]);
    }
    printf("\n");
    printf("%d",BLAKE3_OUT_LEN);

    return 0;
}