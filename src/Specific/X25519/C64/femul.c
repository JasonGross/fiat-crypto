#include <stdint.h>
#include <stdbool.h>
#include <x86intrin.h>
#include "liblow.h"

#include "femul.h"

typedef unsigned int uint128_t __attribute__((mode(TI)));

#if (defined(__GNUC__) || defined(__GNUG__)) && !(defined(__clang__)||defined(__INTEL_COMPILER))
// https://gcc.gnu.org/bugzilla/show_bug.cgi?id=81294
#define _subborrow_u32 __builtin_ia32_sbb_u32
#define _subborrow_u64 __builtin_ia32_sbb_u64
#endif

#undef force_inline
#define force_inline __attribute__((always_inline))

void force_inline femul(uint64_t* out, uint64_t x10, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x18, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13)
{  uint128_t x20 = (((uint128_t)x5 * x18) + (((uint128_t)x7 * x19) + (((uint128_t)x9 * x17) + (((uint128_t)x11 * x15) + ((uint128_t)x10 * x13)))));
{  ℤ x21 = ((((uint128_t)x5 * x19) + (((uint128_t)x7 * x17) + (((uint128_t)x9 * x15) + ((uint128_t)x11 * x13)))) +ℤ (Const 4294968273 *ℤ (0x10 * ((uint128_t)x10 * x18))));
{  ℤ x22 = ((((uint128_t)x5 * x17) + (((uint128_t)x7 * x15) + ((uint128_t)x9 * x13))) +ℤ (Const 4294968273 *ℤ ((0x10 * ((uint128_t)x11 * x18)) + (0x10 * ((uint128_t)x10 * x19)))));
{  ℤ x23 = ((((uint128_t)x5 * x15) + ((uint128_t)x7 * x13)) +ℤ (Const 4294968273 *ℤ ((0x10 * ((uint128_t)x9 * x18)) + ((0x10 * ((uint128_t)x11 * x19)) + (0x10 * ((uint128_t)x10 * x17))))));
{  ℤ x24 = (((uint128_t)x5 * x13) +ℤ (Const 4294968273 *ℤ ((0x10 * ((uint128_t)x7 * x18)) + ((0x10 * ((uint128_t)x9 * x19)) + ((0x10 * ((uint128_t)x11 * x17)) + (0x10 * ((uint128_t)x10 * x15)))))));
{  uint128_t x25 = (x24 >> 0x34);
{  uint64_t x26 = (x24 & 0xfffffffffffff);
{  ℤ x27 = (x25 +ℤ x23);
{  uint128_t x28 = (x27 >> 0x34);
{  uint64_t x29 = (x27 & 0xfffffffffffff);
{  ℤ x30 = (x28 +ℤ x22);
{  uint128_t x31 = (x30 >> 0x34);
{  uint64_t x32 = (x30 & 0xfffffffffffff);
{  ℤ x33 = (x31 +ℤ x21);
{  uint128_t x34 = (x33 >> 0x34);
{  uint64_t x35 = (x33 & 0xfffffffffffff);
{  uint128_t x36 = (x34 + x20);
{  uint64_t x37 = (uint64_t) (x36 >> 0x30);
{  uint64_t x38 = ((uint64_t)x36 & 0xffffffffffff);
{  uint128_t x39 = (x26 + ((uint128_t)(Const 4294968273) * x37));
{  uint64_t x40 = (uint64_t) (x39 >> 0x34);
{  uint64_t x41 = ((uint64_t)x39 & 0xfffffffffffff);
{  uint64_t x42 = (x40 + x29);
{  uint64_t x43 = (x42 >> 0x34);
{  uint64_t x44 = (x42 & 0xfffffffffffff);
out[0] = x38;
out[1] = x35;
out[2] = x43 + x32;
out[3] = x44;
out[4] = x41;
}}}}}}}}}}}}}}}}}}}}}}}}}
// caller: uint64_t out[5];
