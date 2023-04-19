/**@file
*****************************************************************************
field for p = 2^^64 - 2^^32 + 1
 This file is part of "A Succinct and Efficient Range Proof with More Functionalities based on Interactive Oracle Proof"
*****************************************************************************
* @author
*****************************************************************************/

#ifndef RANGEPROOF_FP_64_TCC
#define RANGEPROOF_FP_64_TCC


#include <cmath>
#include <climits>
#include <cstdio>
#include <ctime>
#include <chrono>
#include <immintrin.h>
static __uint128_t High = ((__uint128_t)(1) << 127) -  ((__uint128_t)(1) << 96) + ((__uint128_t)(1) << 127);
static __uint128_t Middle = ((__uint128_t)(1) << 96) - ((__uint128_t)(1) << 64);
static __uint128_t Low = ((__uint128_t)(1) << 64) - 1;
static __int128 gcdm,gcdn,gcdt;
static constexpr unsigned long long modulus = 18446744069414584321ull;
namespace libff{

    //TODO: feima xiaodingli a^{p-2} = a ^{-1}
    inline void Exgcd(unsigned long long a, unsigned long long b, __int128 &Xgcd, __int128 &Ygcd) {
        gcdm = 0, gcdn = 1;
        Xgcd=1, Ygcd=0;
        while(b){
            gcdt=gcdm, gcdm=Xgcd-a/b*gcdm, Xgcd=gcdt;
            gcdt=gcdn, gcdn=Ygcd-a/b*gcdn, Ygcd=gcdt;
            gcdt=b, b=a%b, a=gcdt;
        }
    }
    Fp_64::Fp_64() {
        this->real = 0;
        this->mont_repr.data[0] = 0;
    }

    Fp_64::Fp_64(const bigint<1> &b) {
        this->real = b.data[0];
        if(this->real >= modulus) this->real -= modulus;
        this->mont_repr.data[0] = this->real;
    }

    Fp_64::Fp_64(const __int128_t x, const bool is_unsigned){
        __int128_t a = x % modulus;
        if(is_unsigned || x>=0){
            this->real = (unsigned long long)a;
        }
        else{
            while(a < 0) a = modulus + a;
            this->real = a;
        }
        this->mont_repr.data[0] = this->real;
    }

    void Fp_64::set_ulong(const unsigned long long x) {
        this->real = x;
        if(this->real >= modulus) this->real -= modulus;
        this->mont_repr.data[0] = this->real;
    }

    bigint<1> Fp_64::as_bigint() const {
        return this->mont_repr;
    }

    unsigned long long Fp_64::as_ulong() const {
        return this->real;
    }

    Fp_64 Fp_64::operator + (const Fp_64 &b) const
    {
        Fp_64 ret;
        unsigned long long Result = this->real + b.real;
        if(Result < this->real || Result< b.real){
            Result += 1ull<<32;
            Result -= 1;
        }
        if(Result >= modulus) Result -= modulus;
        ret.real = Result;
        //printf("%llu\n",ret.real);
        ret.mont_repr.data[0] = ret.real;
        return ret;
    }

    Fp_64 Fp_64::operator * (const Fp_64 &b) const
    {
        Fp_64 ret;
        __uint128_t Result = (__uint128_t)(this->real) * (__uint128_t)(b.real);
        unsigned long long high = (Result & High) >> 96;
        unsigned long long middle = (Result & Middle) >> 64;
        unsigned long long low = (Result & Low);
        unsigned long long low2 = low - high;
        if(high > low) low2 += modulus;
        unsigned long long product = middle << 32;
        product -= product >> 32;
        unsigned long long result = low2 + product;
        if((result < product)||(result  >= modulus)) result -= modulus;
        /*unsigned long long result = Result % modulus;*/
        ret.real = result;
        ret.mont_repr.data[0] = ret.real;
        return ret;
    }

    // change on 230210
    Fp_64 Fp_64::operator - (const Fp_64 &b) const
    {
        Fp_64 ret;
        unsigned long long result = this->real - b.real;
        if(b.real > this->real) result += modulus;
        if (result >= modulus)  result -= modulus;
        ret.real = result;
        ret.mont_repr.data[0] = ret.real;
        return ret;
    }

    Fp_64 Fp_64::operator - () const
    {
        Fp_64 ret = *this;
        if(ret.real==0) return ret;
        ret.real = modulus - ret.real;
        ret.mont_repr.data[0] = ret.real;
        return ret;
    }

    Fp_64 Fp_64::operator ^ (unsigned long long p) const {
        Fp_64 ret = Fp_64(1), tmp = *this;
        while(p)
        {
            if(p & 1)
            {
                ret = ret * tmp;
            }
            tmp = tmp * tmp;
            p >>= 1;
        }
        ret.mont_repr.data[0] = ret.real;
        return ret;
    }

    template<mp_size_t m>
    Fp_64 Fp_64::operator ^ (const bigint<m> &p) const {
        Fp_64 ret = Fp_64(1), tmp = *this;
        bool found_one = false;

        for (long i = p.max_bits() - 1; i >= 0; --i)
        {
            if (found_one)
            {
                ret = ret * ret;
            }

            if (p.test_bit(i))
            {
                found_one = true;
                ret = ret * tmp;
            }
        }
        if(ret.real >= modulus) ret.real -= modulus;
        ret.mont_repr.data[0] = ret.real;
        return ret;
    }

    Fp_64 Fp_64::operator = (const Fp_64 &b) {
        this->real = b.real;
        if(this->real >= modulus) this->real -= modulus;
        this->mont_repr.data[0] = this->real;
        return *this;
    }

    Fp_64 Fp_64::operator += (const Fp_64& b){
        *this = (*this) + b;
        return (*this);
    }

    Fp_64 Fp_64::operator -= (const Fp_64& b)  {
        *this = (*this) - b;
        return (*this);
    }

    Fp_64 Fp_64::operator *= (const Fp_64& b)  {
        *this = (*this) * b;
        return (*this);
    }

    Fp_64 Fp_64::operator ^= (unsigned long long p)  {
        *this = (*this) ^ p;
        return (*this);
    }

    template<mp_size_t m>
    Fp_64 Fp_64::operator ^= (const bigint<m> &p) {
        *this = (*this) ^ p;
        return (*this);
    }

    Fp_64 Fp_64::random_element()
    {
        Fp_64 ret;
        srand(time(NULL));
        ret.real = (unsigned long long)rand()*1ll*rand();
         ret.real %= modulus;
        ret.mont_repr.data[0] = ret.real;
        return ret;
    }

    bool Fp_64::operator != (const Fp_64 &b) const//重载不等于
    {
        return this->real != b.real;
    }

    bool Fp_64::operator == (const Fp_64 &b) const//重载等号
    {
        return this->real==b.real;
    }

    Fp_64& Fp_64::invert() {
        /*(*this) = (*this)^(this->modulus - 2);*/
        __int128 Xgcd = 0, Ygcd = 0;
        Exgcd(this->real, modulus, Xgcd, Ygcd);
        this->real = (Xgcd % modulus + modulus) % modulus;
        this->mont_repr.data[0] = this->real;
        return *this;
    }

    Fp_64 Fp_64::inverse() const{
        /*Fp_64 ret = (*this)^(this->modulus - 2);*/
        __int128 Xgcd = 0, Ygcd = 0;
        Exgcd(this->real, modulus, Xgcd, Ygcd);
        Fp_64 ret;ret.real = (Xgcd % modulus + modulus) % modulus;
        ret.mont_repr.data[0] = ret.real;
        return ret;
    }

    Fp_64& Fp_64::square() {
        (*this) = (*this) * (*this);
        return *this;
    }

    Fp_64 Fp_64::squared() const {
        Fp_64 ret = (*this) * (*this);
        return ret;
    }

    Fp_64 Fp_64::zero(){
        Fp_64 ret;
        ret.real = 0;
        ret.mont_repr.data[0] = 0;
        return ret;
    }

    Fp_64 Fp_64::one() {
        Fp_64 ret;
        ret.real = 1;
        ret.mont_repr.data[0]=1;
        return ret;
    }

    Fp_64 Fp_64::Frobenius_map(unsigned long power) const {
        Fp_64 copy = *this;
        return copy;
    }

    Fp_64 Fp_64::sqrt() const{
        // A few assertions to make sure s, t, and nqr are initialized.
        if (this->real == 0)
        {
            return this->zero();
        }
        if (this->real == 1)
        {
            return this->one();
        }
        Fp_64 one;one.real = 1;
        Fp_64 value = *this;
        std::size_t v = this->s;
        Fp_64 z = this->nqr_to_t;
        Fp_64 w = value ^ t_minus_1_over_2;
        Fp_64 x = value * w;
        Fp_64 b = x * w;
        // compute square root with Tonelli--Shanks
        // (does not terminate if not a square!)
        while (b != one)
        {
            size_t m = 0;
            Fp_64 b2m = b;
            while (b2m != one) {
                /* invariant: b2m = b^(2^m) after entering this loop */
                b2m = b2m.squared();
                m += 1;//i
            }
            int j = v-m-1;
            w = z;
            while (j > 0)
            {
                w = w.squared();
                --j;
            }
            z = w.squared();
            b = b * z;
            x = x * w;
            v = m;
        }
        x.mont_repr.data[0] = x.real;
        return x;
    }

    std::vector<uint64_t> Fp_64::to_words() const
    {
        return std::vector<uint64_t>({uint64_t(this->real)});
    }

    bool Fp_64::from_words(std::vector<uint64_t> words){
        this->real = uint64_t(words.back());
        if(this->real >= modulus){
            this->real -= modulus;
            this->mont_repr.data[0] = this->real;
            return false;
        }
        this->mont_repr.data[0] = this->real;
        return true;
    }

    void Fp_64::randomize() {
        (*this) = this->random_element();
    }

    void Fp_64::clear() {
        this->real = 0;
        this->mont_repr.data[0] = 0;
    }

    bool Fp_64::is_zero() const {
        return (this->real==0);
    }

    void Fp_64::print() const {
        std::cout<<this->real<<std::endl;
    }

    std::size_t Fp_64::ceil_size_in_bits() {
        return num_bits;
    }

    std::size_t Fp_64::floor_size_in_bits() {
        return num_bits - 1;
    }

    std::size_t Fp_64::extension_degree() {
        return 1;
    }

    bigint<1> Fp_64::field_char() {
        return bigint<1>(18446744069414584321ull);
    }

    bool Fp_64::modulus_is_valid() {
        return 1;
    }

    std::ostream& operator<<(std::ostream &out, const Fp_64 &el)
    {
        out << el.real <<std::endl;
        return out;
    }

    std::istream& operator>>(std::istream &in, Fp_64 &el)
    {
        in >> el.real ;
        return in;
    }
}
#endif //RANGEPROOF_FP_64_TCC
