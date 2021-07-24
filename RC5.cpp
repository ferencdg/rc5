#include <array>
#include <algorithm>
#include <cassert>
#include <cmath>
#include <iostream>
#include <iomanip>
#include <type_traits>

using namespace std;

//////// UTILITY TEMPLATES

template <uint8_t w>
struct WordT
{
    // any RC5 cipher with w different from 16, 32, 64 will fail to compile
    using type = void;
};

template <>
struct WordT<16>
{
    using type = uint16_t;
    static constexpr type P = 0xb7e1;
    static constexpr type Q = 0x9e37;
};

template <>
struct WordT<32>
{
    using type = uint32_t;
    static constexpr type P = 0xb7e15163;
    static constexpr type Q = 0x9e3779b9;
};

template <>
struct WordT<64>
{
    using type = uint64_t;
    static constexpr type P = 0xb7e151628aed2a6b;
    static constexpr type Q = 0x9e3779b97f4a7c15;
};

//////// RC5 cipher

template <uint8_t w, uint8_t r, uint8_t b>
class RC5
{
    // there is no need to check the cipher parameters with static_assert, as
    // the template construction/data types will make sure that
    // 0 <= r <= 255 (enforced by data type)
    // 0 <= b <= 255 (enforced by data type)
    // w can only be 16, 32, 64 (enforced by WordT template)
    // K has exactly b bytes (enforced by Key data type)

private:
    // set the underlying type for word based on w
    using Word = typename WordT<w>::type;
    using Key = array<uint8_t, b>;

    // constants derived from cipher's parameters
    static constexpr uint8_t u = ceil(w / 8);
    static constexpr uint16_t t = 2 * (r + 1);

    // set magic numbers based on w
    static constexpr Word P = WordT<w>::P;
    static constexpr Word Q = WordT<w>::Q;

public:

    template <typename ByteStream>
    static constexpr ByteStream encode(const Key &K, const ByteStream &plaintext)
    {
        // checking if padding on plaintext is correct
        static_assert(plaintext.size() == u * 2);

        ByteStream ciphertext{};
        Word A = packWord(plaintext, 0);
        Word B = packWord(plaintext, u);
        encodeWords(K, A, B);
        unpackWord(ciphertext, 0, A);
        unpackWord(ciphertext, u, B);

        return ciphertext;
    }

    static constexpr void encodeWords(const Key& K, Word &A, Word &B)
    {
        const array<Word, t> S = setupS(K);

        A += S[0];
        B += S[1];

        for (uint8_t i = 1; i <= r; ++i)
        {
            A = left_shift(A ^ B, B) + S[2 * i];
            B = left_shift(B ^ A, A) + S[2 * i + 1];
        }
    }

    template <typename ByteStream>
    static constexpr ByteStream decode(const Key& K, const ByteStream &ciphertext)
    {
        // checking if padding on ciphertext is correct
        static_assert(ciphertext.size() == u * 2);

        ByteStream plaintext{};
        Word A = packWord(ciphertext, 0);
        Word B = packWord(ciphertext, u);
        decodeWords(K, A, B);
        unpackWord(plaintext, 0, A);
        unpackWord(plaintext, u, B);

        return plaintext;
    }

    static constexpr void decodeWords(const Key& K, Word &A, Word &B)
    {
        const array<Word, t> S = setupS(K);

        for (uint8_t i = r; i > 0; --i)
        {
            B = right_shift(B - S[2 * i + 1], A) ^ A;
            A = right_shift(A - S[2 * i], B) ^ B;
        }
        B -= S[1];
        A -= S[0];
    }

private:
    // setup the S array based on the cipher's parameters and key
    static constexpr array<Word, t> setupS(const Key &K)
    {
        const uint8_t c = ceil(max<double>(b, 1) / u);
        std::array<Word, c> L{};
        for (int i = b - 1; i >= 0; --i)
            L[i / u] = (L[i / u] << 8) + K[i];

        array<Word, t> S{};
        S[0] = P;
        for (int i = 1; i < t; ++i)
            S[i] = S[i - 1] + Q;

        uint16_t i = 0, j = 0;
        Word A = 0, B = 0;
        for (int k = 0; k < 3 * max<uint16_t>(t, c); ++k)
        {
            A = S[i] = left_shift(S[i] + A + B, 3);
            B = L[j] = left_shift(L[j] + A + B, A + B);
            i = (i + 1) % t;
            j = (j + 1) % c;
        }
        return S;
    }

    //////////// UTILITY FUNCTIONS

    // packs bytes from the stream into a Word and returns it
    template <typename InputStream>
    static constexpr inline Word packWord(const InputStream &input_stream, uint16_t start)
    {
        Word word{};
        for (auto i = 1; i <= u; ++i)
            word = (word << 8) + input_stream[start + u - i];
        return word;
    }

    // unpacks bytes from a Word and inserts them into the stream
    template <typename OutputStream>
    static constexpr inline void unpackWord(OutputStream &outputStream, uint16_t start, const Word &word)
    {
        for (auto i = 0; i < u; ++i)
            outputStream[start + i] = (word & (0xFFull << i * 8)) >> (i * 8);
    }

    static constexpr inline Word left_shift(const Word &x, const Word &y)
    {
        return x << (y & (w - 1)) | x >> (w - (y & (w - 1)));
    }

    static constexpr inline Word right_shift(const Word &x, const Word &y)
    {
        return x >> (y & (w - 1)) | x << (w - (y & (w - 1)));
    }
};

//////// TESTS

// constexpr comparison for containers supporting `size()` and random indexing
template <typename ContainerType>
constexpr bool constexpr_compare(const ContainerType &c1, const ContainerType &c2)
{
    if (c1.size() != c2.size())
        return false;

    for (int i = 0; i < c1.size(); ++i)
        if (c1[i] != c2[i])
            return false;

    return true;
}

void test1()
{
    constexpr std::array<uint8_t, 16> key = {0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F};
    constexpr std::array<uint8_t, 8> plaintext = {0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77};
    constexpr std::array<uint8_t, 8> ciphertext = {0x2D, 0xDC, 0x14, 0x9B, 0xCF, 0x08, 0x8B, 0x9E};

    // the following RC5 encoding is done during COMPILE time
    constexpr auto res = RC5<32, 12, 16>::encode(key, plaintext);
    static_assert(constexpr_compare(res, ciphertext));

    // the following RC5 encoding is done during RUNTIME
    assert((RC5<32, 12, 16>::encode(key, plaintext) == ciphertext));
}

void test2()
{
    constexpr std::array<uint8_t, 16> key = {0x2B, 0xD6, 0x45, 0x9F, 0x82, 0xC5, 0xB3, 0x00, 0x95, 0x2C, 0x49, 0x10, 0x48, 0x81, 0xFF, 0x48};
    constexpr std::array<uint8_t, 8> plaintext = {0xEA, 0x02, 0x47, 0x14, 0xAD, 0x5C, 0x4D, 0x84};
    constexpr std::array<uint8_t, 8> ciphertext = {0x11, 0xE4, 0x3B, 0x86, 0xD2, 0x31, 0xEA, 0x64};
    constexpr auto res = RC5<32, 12, 16>::encode(key, plaintext);
    static_assert(constexpr_compare(res, ciphertext));
}

void test3()
{
    constexpr std::array<uint8_t, 16> key = {0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F};
    constexpr std::array<uint8_t, 8> plaintext = {0x96, 0x95, 0x0D, 0xDA, 0x65, 0x4A, 0x3D, 0x62};
    constexpr std::array<uint8_t, 8> ciphertext = {0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77};
    constexpr auto res = RC5<32, 12, 16>::decode(key, ciphertext);
    static_assert(constexpr_compare(res, plaintext));
}

void test4()
{
    constexpr std::array<uint8_t, 16> key = {0x2B, 0xD6, 0x45, 0x9F, 0x82, 0xC5, 0xB3, 0x00, 0x95, 0x2C, 0x49, 0x10, 0x48, 0x81, 0xFF, 0x48};
    constexpr std::array<uint8_t, 8> plaintext = {0x63, 0x8B, 0x3A, 0x5E, 0xF7, 0x2B, 0x66, 0x3F};
    constexpr std::array<uint8_t, 8> ciphertext = {0xEA, 0x02, 0x47, 0x14, 0xAD, 0x5C, 0x4D, 0x84};
    constexpr auto res = RC5<32, 12, 16>::decode(key, ciphertext);
    static_assert(constexpr_compare(res, plaintext));
}

// cipher with w = 64
void test5()
{
    constexpr std::array<uint8_t, 24> key = {0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17};
    ;
    constexpr std::array<uint8_t, 16> plaintext = {0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F};
    constexpr std::array<uint8_t, 16> ciphertext = {0xA4, 0x67, 0x72, 0x82, 0x0E, 0xDB, 0xCE, 0x02, 0x35, 0xAB, 0xEA, 0x32, 0xAE, 0x71, 0x78, 0xDA};
    constexpr auto res = RC5<64, 24, 24>::encode(key, plaintext);
    static_assert(constexpr_compare(res, ciphertext));
}

// cipher with L = 0 (result is not compared, as I found no test vectors with L = 0)
void test6()
{
    constexpr std::array<uint8_t, 0> key = {};
    constexpr std::array<uint8_t, 16> plaintext = {0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F};
    constexpr std::array<uint8_t, 16> ciphertext = {0xA4, 0x67, 0x72, 0x82, 0x0E, 0xDB, 0xCE, 0x02, 0x35, 0xAB, 0xEA, 0x32, 0xAE, 0x71, 0x78, 0xDA};
    RC5<64, 24, 0>::encode(key, plaintext);
}

int main()
{
    test1();
    test2();
    test3();
    test4();
    test5();
    test6();

    return 0;
}
