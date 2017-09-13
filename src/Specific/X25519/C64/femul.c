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

void force_inline femul(uint64_t* out, uint64_t x10, uint64_t x11, uint64_t x9, uint64_t x7, uint64_t x5, uint64_t x18, uint64_t x19, uint64_t x17, uint64_t x15, uint64_t x13) {

uint64_t x89, x79, x86, x82, x90;
uint64_t rsp;

asm (
"mov %%rsp, %[rsp]\t\n"
// Convention is low_reg:high_reg
"mov $0x13, %%rdx\t\n"
"mov %[mx11], %%r15\t\n"
"mulx %%r15, %%r15, %%rdx\t\n" // x48 = x11 * 0x13
"mov %%r15, %%rdx\t\n"
"mov %[mx17], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x55_tmp = x48 * x17
"mov %%r14, %[rx90]\t\n" // bucket: x50_low + x52_low + x54_low + x56_low
"mov %%r13, %[rx82]\t\n" // bucket: x50_high + x52_high + x54_high + x56_high
"mov $0x13, %%rdx\t\n"
"mov %[mx9], %[rx86]\t\n"
"mulx %[rx86], %[rx86], %%rdx\t\n" // x47 = x9 * 0x13
"mov %[rx86], %%rdx\t\n"
"mov %[mx19], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x53_tmp = x47 * x19
"add %%r14, %[rx90]\t\n" // bucket: x50_low + x52_low + x54_low + x56_low
"adc %%r13, %[rx82]\t\n" // bucket: x50_high + x52_high + x54_high + x56_high
"mov $0x13, %%rdx\t\n"
"mov %[mx7], %[rx79]\t\n"
"mulx %[rx79], %[rx79], %%rdx\t\n" // x46 = x7 * 0x13
"mov %[rx79], %%rdx\t\n"
"mov %[mx18], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x51_tmp = x46 * x18
"add %%r14, %[rx90]\t\n" // bucket: x50_low + x52_low + x54_low + x56_low
"adc %%r13, %[rx82]\t\n" // bucket: x50_high + x52_high + x54_high + x56_high
"mov %[mx5], %%rdx\t\n"
"mov %[mx13], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x20_tmp = x5 * x13
"add %%r14, %[rx90]\t\n" // bucket: x50_low + x52_low + x54_low + x56_low
"adc %%r13, %[rx82]\t\n" // bucket: x50_high + x52_high + x54_high + x56_high
"mov $0x13, %%rdx\t\n"
"mov %[mx10], %[rx79]\t\n"
"mulx %[rx79], %[rx79], %%rdx\t\n" // x45 = x10 * 0x13
"mov %[rx79], %%rdx\t\n"
"mov %[mx15], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x49_tmp = x45 * x15
"add %%r14, %[rx90]\t\n" // bucket: x50_low + x52_low + x54_low + x56_low
"adc %%r13, %[rx82]\t\n" // bucket: x50_high + x52_high + x54_high + x56_high
"mov $0x7ffffffffffff, %%rdx\t\n"
"and %%rdx, %[rx90]\t\n" // x70 = x56_low & 0x7ffffffffffff
"mov %%r15, %%rdx\t\n"
"mov %[mx19], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x61_tmp = x48 * x19
"mov %[rx90], %%rdx\t\n"
"mov %[rx90], %[rx82]\t\n"
"mov %%rdx, %[rx90]\t\n"
"shrd $0x33, %[rx90], %[rx82]\t\n" // x69 = x56_low:x56_high >> 0x33
"mov %[rx82], %[rx89]\t\n" // bucket: x23_low + x58_low + x60_low + x62_low + x71_low
"add %%r14, %[rx89]\t\n" // bucket: x23_low + x58_low + x60_low + x62_low + x71_low
"mov %%r13, %%rsp\t\n" // bucket: x23_high + x58_high + x60_high + x62_high + x71_high
"mov %[rx86], %%rdx\t\n"
"mov %[mx18], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x59_tmp = x47 * x18
"add %%r14, %[rx89]\t\n" // bucket: x23_low + x58_low + x60_low + x62_low + x71_low
"adc %%r13, %%rsp\t\n" // bucket: x23_high + x58_high + x60_high + x62_high + x71_high
"mov %[rx79], %%rdx\t\n"
"mov %[mx17], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x57_tmp = x45 * x17
"add %%r14, %[rx89]\t\n" // bucket: x23_low + x58_low + x60_low + x62_low + x71_low
"adc %%r13, %%rsp\t\n" // bucket: x23_high + x58_high + x60_high + x62_high + x71_high
"mov %[mx5], %%rdx\t\n"
"mov %[mx15], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x21_tmp = x5 * x15
"add %%r14, %[rx89]\t\n" // bucket: x23_low + x58_low + x60_low + x62_low + x71_low
"adc %%r13, %%rsp\t\n" // bucket: x23_high + x58_high + x60_high + x62_high + x71_high
"mov %[mx7], %%rdx\t\n"
"mov %[mx13], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x22_tmp = x7 * x13
"add %%r14, %[rx89]\t\n" // bucket: x23_low + x58_low + x60_low + x62_low + x71_low
"adc %%r13, %%rsp\t\n" // bucket: x23_high + x58_high + x60_high + x62_high + x71_high
"mov $0x7ffffffffffff, %%rdx\t\n"
"and %%rdx, %[rx89]\t\n" // x73 = x71_low & 0x7ffffffffffff
"mov %%r15, %%rdx\t\n"
"mov %[mx18], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x65_tmp = x48 * x18
"mov %[rx89], %%rdx\t\n"
"mov %[rx89], %%rsp\t\n"
"mov %%rdx, %[rx89]\t\n"
"shrd $0x33, %[rx89], %%rsp\t\n" // x72 = x71_low:x71_high >> 0x33
"mov %%rsp, %%r15\t\n" // bucket: x26_low + x28_low + x64_low + x66_low + x74_low
"add %%r14, %%r15\t\n" // bucket: x26_low + x28_low + x64_low + x66_low + x74_low
"mov %%r13, %[rx82]\t\n" // bucket: x26_high + x28_high + x64_high + x66_high + x74_high
"mov %[rx79], %%rdx\t\n"
"mov %[mx19], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x63_tmp = x45 * x19
"add %%r14, %%r15\t\n" // bucket: x26_low + x28_low + x64_low + x66_low + x74_low
"adc %%r13, %[rx82]\t\n" // bucket: x26_high + x28_high + x64_high + x66_high + x74_high
"mov %[mx7], %%rdx\t\n"
"mov %[mx15], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x27_tmp = x7 * x15
"add %%r14, %%r15\t\n" // bucket: x26_low + x28_low + x64_low + x66_low + x74_low
"adc %%r13, %[rx82]\t\n" // bucket: x26_high + x28_high + x64_high + x66_high + x74_high
"mov %[mx5], %%rdx\t\n"
"mov %[mx17], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x24_tmp = x5 * x17
"add %%r14, %%r15\t\n" // bucket: x26_low + x28_low + x64_low + x66_low + x74_low
"adc %%r13, %[rx82]\t\n" // bucket: x26_high + x28_high + x64_high + x66_high + x74_high
"mov %[mx9], %%rdx\t\n"
"mov %[mx13], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x25_tmp = x9 * x13
"add %%r14, %%r15\t\n" // bucket: x26_low + x28_low + x64_low + x66_low + x74_low
"adc %%r13, %[rx82]\t\n" // bucket: x26_high + x28_high + x64_high + x66_high + x74_high
"mov $0x7ffffffffffff, %%rdx\t\n"
"and %%rdx, %%r15\t\n" // x76 = x74_low & 0x7ffffffffffff
"mov %[rx79], %%rdx\t\n"
"mov %[mx18], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x67_tmp = x45 * x18
"mov %%r15, %%rdx\t\n"
"mov %%r15, %[rx82]\t\n"
"mov %%rdx, %%r15\t\n"
"shrd $0x33, %%r15, %[rx82]\t\n" // x75 = x74_low:x74_high >> 0x33
"mov %[rx82], %[rx79]\t\n" // bucket: x31_low + x33_low + x35_low + x68_low + x77_low
"add %%r14, %[rx79]\t\n" // bucket: x31_low + x33_low + x35_low + x68_low + x77_low
"mov %%r13, %%rsp\t\n" // bucket: x31_high + x33_high + x35_high + x68_high + x77_high
"mov %[mx9], %%rdx\t\n"
"mov %[mx15], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x34_tmp = x9 * x15
"add %%r14, %[rx79]\t\n" // bucket: x31_low + x33_low + x35_low + x68_low + x77_low
"adc %%r13, %%rsp\t\n" // bucket: x31_high + x33_high + x35_high + x68_high + x77_high
"mov %[mx7], %%rdx\t\n"
"mov %[mx17], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x32_tmp = x7 * x17
"add %%r14, %[rx79]\t\n" // bucket: x31_low + x33_low + x35_low + x68_low + x77_low
"adc %%r13, %%rsp\t\n" // bucket: x31_high + x33_high + x35_high + x68_high + x77_high
"mov %[mx5], %%rdx\t\n"
"mov %[mx19], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x29_tmp = x5 * x19
"add %%r14, %[rx79]\t\n" // bucket: x31_low + x33_low + x35_low + x68_low + x77_low
"adc %%r13, %%rsp\t\n" // bucket: x31_high + x33_high + x35_high + x68_high + x77_high
"mov %[mx11], %%rdx\t\n"
"mov %[mx13], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x30_tmp = x11 * x13
"add %%r14, %[rx79]\t\n" // bucket: x31_low + x33_low + x35_low + x68_low + x77_low
"adc %%r13, %%rsp\t\n" // bucket: x31_high + x33_high + x35_high + x68_high + x77_high
"mov $0x7ffffffffffff, %%rdx\t\n"
"and %%rdx, %[rx79]\t\n" // x79 = x77_low & 0x7ffffffffffff
"mov %[mx9], %%rdx\t\n"
"mov %[mx17], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x43_tmp = x9 * x17
"mov %[rx79], %%rdx\t\n"
"mov %[rx79], %%rsp\t\n"
"mov %%rdx, %[rx79]\t\n"
"shrd $0x33, %[rx79], %%rsp\t\n" // x78 = x77_low:x77_high >> 0x33
"mov %%rsp, %[rx82]\t\n" // bucket: x38_low + x40_low + x42_low + x44_low + x80_low
"add %%r14, %[rx82]\t\n" // bucket: x38_low + x40_low + x42_low + x44_low + x80_low
"mov %%r13, %[rx86]\t\n" // bucket: x38_high + x40_high + x42_high + x44_high + x80_high
"mov %[mx7], %%rdx\t\n"
"mov %[mx19], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x41_tmp = x7 * x19
"add %%r14, %[rx82]\t\n" // bucket: x38_low + x40_low + x42_low + x44_low + x80_low
"adc %%r13, %[rx86]\t\n" // bucket: x38_high + x40_high + x42_high + x44_high + x80_high
"mov %[mx11], %%rdx\t\n"
"mov %[mx15], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x39_tmp = x11 * x15
"add %%r14, %[rx82]\t\n" // bucket: x38_low + x40_low + x42_low + x44_low + x80_low
"adc %%r13, %[rx86]\t\n" // bucket: x38_high + x40_high + x42_high + x44_high + x80_high
"mov %[mx5], %%rdx\t\n"
"mov %[mx18], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x36_tmp = x5 * x18
"add %%r14, %[rx82]\t\n" // bucket: x38_low + x40_low + x42_low + x44_low + x80_low
"adc %%r13, %[rx86]\t\n" // bucket: x38_high + x40_high + x42_high + x44_high + x80_high
"mov %[mx10], %%rdx\t\n"
"mov %[mx13], %%r13\t\n"
"mulx %%r13, %%r14, %%r13\t\n" // x37_tmp = x10 * x13
"add %%r14, %[rx82]\t\n" // bucket: x38_low + x40_low + x42_low + x44_low + x80_low
"adc %%r13, %[rx86]\t\n" // bucket: x38_high + x40_high + x42_high + x44_high + x80_high
"mov $0x7ffffffffffff, %%rdx\t\n"
"and %%rdx, %[rx82]\t\n" // x82 = x80_low & 0x7ffffffffffff
"mov %[rx82], %%rdx\t\n"
"mov %[rx82], %[rx86]\t\n"
"mov %%rdx, %[rx82]\t\n"
"shrd $0x33, %[rx82], %[rx86]\t\n" // x81 = x80_low:x80_high >> 0x33
"mov $0x13, %%rdx\t\n"
"mulx %[rx86], %[rx86], %%rdx\t\n" // x83 = x81 * 0x13
"add %[rx86], %[rx90]\t\n" // bucket: x84 = x70 + x83
"shr $0x33, %[rx90]\t\n" // x85 = x70 >> 0x33
"mov %[rx90], %[rx86]\t\n"
"mov $0x7ffffffffffff, %%rdx\t\n"
"and %%rdx, %[rx86]\t\n" // x86 = x84 & 0x7ffffffffffff
"add %[rx89], %[rx90]\t\n" // bucket: x87 = x85 + x73
"shr $0x33, %[rx90]\t\n" // x88 = x85 >> 0x33
"mov %[rx90], %[rx89]\t\n"
"mov $0x7ffffffffffff, %%rdx\t\n"
"and %%rdx, %[rx89]\t\n" // x89 = x87 & 0x7ffffffffffff
"add %%r15, %[rx90]\t\n" // bucket: x90 = x88 + x76
"mov %[rsp], %%rsp\t\n"
: [rx89] "=&r" (x89), [rx79] "=&r" (x79), [rx86] "=&r" (x86), [rx82] "=&r" (x82), [rx90] "=&r" (x90)
: [mx9] "m" (x9), [mx7] "m" (x7), [mx5] "m" (x5), [mx10] "m" (x10), [mx11] "m" (x11), [mx13] "m" (x13), [mx15] "m" (x15), [mx17] "m" (x17), [mx18] "m" (x18), [mx19] "m" (x19), [rsp] "m" (rsp)
: "cc", "rdx", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15"
);


out[0] = x82;
out[1] = x79;
out[2] = x90;
out[3] = x89;
out[4] = x86;
}
// caller: uint64_t out[5];
