/**@file
*****************************************************************************
field for p = 2^^64 - 2^^32 + 1
 This file is part of "A Succinct and Efficient Range Proof with More Functionalities based on Interactive Oracle Proof"
*****************************************************************************
* @author
*****************************************************************************/

#ifndef RANGEPROOF_FP_64_HPP
#define RANGEPROOF_FP_64_HPP
#include <cassert>
#include <immintrin.h>
#include <vector>
#include <memory>
#include <cstring>
#include <libff/algebra/field_utils/bigint.hpp>

namespace libff{
    /*
    This defines a field
    */
    class Fp_64
    {
    private:
    public:
        unsigned long long real;
        bigint<1> mont_repr;

        static bigint<1> mod;
        static const mp_size_t num_limbs = 1;
        static const constexpr std::size_t num_bits = 64;
        static bigint<1> euler; // (modulus-1)/2
        static const constexpr std::size_t s = 32; // modulus = 2^s * t + 1
        static bigint<1> t; // with t odd
        static bigint<1> t_minus_1_over_2 ; // (t-1)/2
        static Fp_64 nqr;     // a quadratic nonresidue
        static Fp_64 nqr_to_t; // nqr^t
        static Fp_64 multiplicative_generator ; // generator of Fp^*
        static Fp_64 root_of_unity; // generator^((modulus-1)/2^s)
        static mp_limb_t inv; // modulus^(-1) mod W, where W = 2^(word size)
        static bigint<1> Rsquared; // R^2, where R = W^k, where k = ??
        static bigint<1> Rcubed;


        inline Fp_64();
        inline Fp_64(const bigint<1> &b);
        inline Fp_64(const __int128_t x, const bool is_unsigned=false);
        inline void set_ulong(const unsigned long long x);

        inline void clear();
        inline void print() const;
        inline void randomize();

        inline std::vector<uint64_t> to_words() const;
        inline bool from_words(std::vector<uint64_t> words);

        inline bigint<1> as_bigint() const;
        inline unsigned long long as_ulong() const;

        inline bool operator == (const Fp_64 &b) const;
        inline bool operator != (const Fp_64 &b) const;
        inline bool is_zero() const;

        inline Fp_64 operator += (const Fp_64& b);
        inline Fp_64 operator -= (const Fp_64& b);
        inline Fp_64 operator *= (const Fp_64& b);
        inline Fp_64 operator ^= (unsigned long long p);
        template<mp_size_t m>
        inline Fp_64 operator ^= (const bigint<m> &p);

        inline Fp_64 operator + (const Fp_64 &b) const;
        inline Fp_64 operator - (const Fp_64 &b) const;
        inline Fp_64 operator * (const Fp_64 &b) const;
        inline Fp_64 operator ^ (unsigned long long p) const;
        template<mp_size_t m>
        inline Fp_64 operator ^ (const bigint<m> &p) const;
        inline Fp_64 operator - () const;
        inline Fp_64 operator = (const Fp_64& b);

        inline Fp_64& square();
        inline Fp_64 squared() const;
        inline Fp_64& invert();
        inline Fp_64 inverse() const;
        inline Fp_64 Frobenius_map(unsigned long power) const;
        inline Fp_64 sqrt() const;

        inline static std::size_t ceil_size_in_bits();
        inline static std::size_t floor_size_in_bits();
        inline static std::size_t extension_degree();
        inline static bigint<1> field_char();
        inline static bool modulus_is_valid();

        inline static size_t capacity() { return num_bits - 1; }

        inline static Fp_64 zero();
        inline static Fp_64 one();
        inline static Fp_64 random_element();

        inline friend std::ostream& operator<<(std::ostream &out, const Fp_64 &p);
        inline friend std::istream& operator>>(std::istream &in, Fp_64 &p);
    };
}
#include <libff/algebra/fields/prime_base/fp_64.tcc>
#endif //RANGEPROOF_FP_64_HPP
