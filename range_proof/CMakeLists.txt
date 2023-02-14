add_library(
  range_proof

  common/common.cpp

  protocols/ldt/ldt_reducer.cpp
  iop/utilities/batching.cpp
  algebra/utils.cpp
)

list(APPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake")

find_package(sodium)

target_link_libraries(
  range_proof

  sodium

  ff
)

target_include_directories(
 range_proof

 PUBLIC
 ../depends/libfqfft
 ../depends/libff
)


add_executable(test_merkleTree tests/test_merkleTree.cpp
        bcs/BLAKE3/blake3.c
        bcs/BLAKE3/blake3_dispatch.c
        bcs/BLAKE3/blake3_portable.c
        bcs/BLAKE3/blake3_sse2_x86-64_unix.S
        bcs/BLAKE3/blake3_sse41_x86-64_unix.S
        bcs/BLAKE3/blake3_avx2_x86-64_unix.S
        bcs/BLAKE3/blake3_avx512_x86-64_unix.S)
target_link_libraries(test_merkleTree range_proof)
target_link_libraries(test_merkleTree  -lpthread -lm)

add_executable(test_fri tests/test_fri.cpp
        bcs/BLAKE3/blake3.c
        bcs/BLAKE3/blake3_dispatch.c
        bcs/BLAKE3/blake3_portable.c
        bcs/BLAKE3/blake3_sse2_x86-64_unix.S
        bcs/BLAKE3/blake3_sse41_x86-64_unix.S
        bcs/BLAKE3/blake3_avx2_x86-64_unix.S
        bcs/BLAKE3/blake3_avx512_x86-64_unix.S)
target_link_libraries(test_fri range_proof gtest_main)

add_executable(test_rangeproof tests/test_rangeproof.cpp
        bcs/BLAKE3/blake3.c
        bcs/BLAKE3/blake3_dispatch.c
        bcs/BLAKE3/blake3_portable.c
        bcs/BLAKE3/blake3_sse2_x86-64_unix.S
        bcs/BLAKE3/blake3_sse41_x86-64_unix.S
        bcs/BLAKE3/blake3_avx2_x86-64_unix.S
        bcs/BLAKE3/blake3_avx512_x86-64_unix.S)
target_link_libraries(test_rangeproof range_proof)

add_executable(test_rangeproof_proveable tests/test_rangeproof_proveable.cpp
        bcs/BLAKE3/blake3.c
        bcs/BLAKE3/blake3_dispatch.c
        bcs/BLAKE3/blake3_portable.c
        bcs/BLAKE3/blake3_sse2_x86-64_unix.S
        bcs/BLAKE3/blake3_sse41_x86-64_unix.S
        bcs/BLAKE3/blake3_avx2_x86-64_unix.S
        bcs/BLAKE3/blake3_avx512_x86-64_unix.S)
target_link_libraries(test_rangeproof_proveable range_proof)

add_executable(test_rangeproof_arbitrary tests/test_rangeproof_arbitrary.cpp
        bcs/BLAKE3/blake3.c
        bcs/BLAKE3/blake3_dispatch.c
        bcs/BLAKE3/blake3_portable.c
        bcs/BLAKE3/blake3_sse2_x86-64_unix.S
        bcs/BLAKE3/blake3_sse41_x86-64_unix.S
        bcs/BLAKE3/blake3_avx2_x86-64_unix.S
        bcs/BLAKE3/blake3_avx512_x86-64_unix.S)
target_link_libraries(test_rangeproof_arbitrary range_proof)


ENABLE_LANGUAGE(ASM)