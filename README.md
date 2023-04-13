
This is the implementation of "An Efficient and Succinct Range Proof with 
More Functionalities based on Interactive Oracle Proof".
See [the paper](https://eprint...). It has advantages as follows.

- **Succinct:** It has lograthmic communication complexity.
- **Efficient:** It is efficient and may be practical in applications.
- **More Functionalities:** It supports arbitrary range and batch processing.

This repository refers to [libff](https://https://github.com/scipr-lab/libff) for the framework
for finite fields and FFT operation on multiplicative cosets.
We also refer to  [libiop](https://github.com/scipr-lab/libiop) for 
some helpful functions to implement FRI.

The main code is Fast Reed-Solomon Interactive Oracle Proof of Proximity (FRI) in range_proof/protocols/ldt/fri/fri_ldt.hpp. We
use [BLAKE3](https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf) for the hash functions in Merkle trees. 

The range proofs are all in range_proof/tests. Run test_rangeproof for (batch) range proofs in the conjecture setting.
Run test_rangeproof_arbitrary for (batch) range proofs for arbitrary ranges in the conjecture setting.
Run test_rangeproof_proveable for (batch) range proofs for fixed ranges in the proveable setting. We currently only
support ranges where the base is 2. Other parameters such as instance number, security level, range dimension,
localization array, code rate are all adjustable.

We implement a prime field F_p where p = 2^64 -2^32 +1. This can be seen in depends/libff/libff/algebra/fields/prime_base/fields_64.hpp
 and fp_64.hpp.


