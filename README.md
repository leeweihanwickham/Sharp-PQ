
This is the implementation of Lipara, Succinct Batch Proofs for Arbitrary Ranges based on IOP.
It has the following properties:

- **Functionality.** It is a range proof supporting batch processing and arbitrary ranges.
- **Security.**  It is transparent and plausible post-quantum secure based on interactive oracle proof. 
It is provable secure in the random oracle model.
- **Performance.** It has poly-logarithmic communication complexity and verifier complexity. It only uses
  Reed-Solomon codes and hash functions without public-key cryptographic
  operations.


This repository refers to [libff](https://https://github.com/scipr-lab/libff) for the framework
for finite fields and FFT operation on multiplicative cosets.
We also refer to  [libiop](https://github.com/scipr-lab/libiop) for 
some helpful functions to implement FRI.

The main code is Fast Reed-Solomon Interactive Oracle Proof of Proximity (FRI) in range_proof/protocols/ldt/fri/fri_ldt.hpp. We
use [BLAKE3](https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf) for the hash functions in Merkle trees. 

The range proofs are all in range_proof/tests. Run test_rangeproof.cpp for (batch) range proofs for fixed ranges in the conjecture setting.
Run test_rangeproof_arbitrary.cpp for (batch) range proofs for arbitrary ranges in the conjecture setting.
Run test_rangeproof_proveable.cpp for (batch) range proofs for fixed ranges in the proveable setting. We currently only
support ranges where the base is 2. For the evaluation of payment systems, see test_payment_check.cpp.

Parameters such as instance number, security level, range dimension,
localization array, code rate are all adjustable.

We implement a prime field F_p where p = 2^64 -2^32 +1. This can be seen in depends/libff/libff/algebra/fields/prime_base/fields_64.hpp
 and fp_64.hpp. The special properties of this field would help to improve the speed of field operations.

We refer to the implementation of [Bulletproofs](https://github.com/xevisalle/zpie) in C 
and [LNS20](github.com/gregorseiler/irelzk) in C++. 

## Usage

To run the code, first install depends

```bash
sudo apt-get install build-essential cmake git libgmp3-dev libprocps4-dev libboost-all-dev libssl-dev libsodium-dev --fix-missing
git submodule init && git submodule update
```

then build
```bash
mkdir build
cd build
cmake ..
make
```

