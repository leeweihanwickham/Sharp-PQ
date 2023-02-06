cmake_minimum_required(VERSION 3.22)
project(c)

set(CMAKE_C_STANDARD 11)

include_directories(.)

add_executable(debug
        debug.cpp
        blake3.c
        blake3_dispatch.c
        blake3_portable.c
        blake3_sse2_x86-64_unix.S
        blake3_sse41_x86-64_unix.S
        blake3_avx2_x86-64_unix.S
        blake3_avx512_x86-64_unix.S)
ENABLE_LANGUAGE(ASM)
