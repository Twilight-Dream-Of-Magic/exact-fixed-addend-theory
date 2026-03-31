#include <array>
#include <cassert>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <random>
#include <stdexcept>
#include <string>

namespace fixed_addend
{

static std::uint64_t mask_for_width(unsigned n)
{
    if (n == 0 || n > 20) {
        throw std::invalid_argument("this verifier is intended for 1 <= n <= 20");
    }
    return (std::uint64_t{1} << n) - 1u;
}

static unsigned bit(std::uint64_t word, unsigned i)
{
    return static_cast<unsigned>((word >> i) & 1u);
}

static unsigned majority(unsigned x, unsigned k, unsigned carry)
{
    return (x & k) ^ (x & carry) ^ (k & carry);
}

static unsigned parity(std::uint64_t x)
{
#if defined(__GNUG__) || defined(__clang__)
    return static_cast<unsigned>(__builtin_popcountll(x) & 1u);
#else
    x ^= x >> 32;
    x ^= x >> 16;
    x ^= x >> 8;
    x ^= x >> 4;
    x &= 0xfu;
    return static_cast<unsigned>((0x6996u >> x) & 1u);
#endif
}

static std::uint64_t add_constant(unsigned n, std::uint64_t x, std::uint64_t constant_key)
{
    return (x + constant_key) & mask_for_width(n);
}

// Exact DP_K numerator: # { x : F_K(x xor u) xor F_K(x) == v }.
static std::uint64_t dpk_numerator(unsigned n,
                                   std::uint64_t constant_key,
                                   std::uint64_t input_difference,
                                   std::uint64_t output_difference)
{
    std::array<std::uint64_t, 4> state_count{1, 0, 0, 0};

    for (unsigned i = 0; i < n; ++i) {
        std::array<std::uint64_t, 4> next_count{0, 0, 0, 0};
        const unsigned k_i = bit(constant_key, i);
        const unsigned u_i = bit(input_difference, i);
        const unsigned v_i = bit(output_difference, i);

        for (unsigned state = 0; state < 4; ++state) {
            const std::uint64_t count = state_count[state];
            if (count == 0) {
                continue;
            }

            const unsigned carry = (state >> 1) & 1u;
            const unsigned carry_shifted = state & 1u;

            for (unsigned x_i = 0; x_i <= 1; ++x_i) {
                // Visible differential bit: y_i xor y'_i = u_i xor c_i xor c'_i.
                const unsigned visible_difference = u_i ^ carry ^ carry_shifted;
                if (visible_difference != v_i) {
                    continue;
                }

                const unsigned next_carry = majority(x_i, k_i, carry);
                const unsigned next_carry_shifted = majority(x_i ^ u_i, k_i, carry_shifted);
                const unsigned next_state = (next_carry << 1) | next_carry_shifted;
                next_count[next_state] += count;
            }
        }

        state_count = next_count;
    }

    return state_count[0] + state_count[1] + state_count[2] + state_count[3];
}

static std::uint64_t brute_dpk_numerator(unsigned n,
                                         std::uint64_t constant_key,
                                         std::uint64_t input_difference,
                                         std::uint64_t output_difference)
{
    const std::uint64_t modulus = std::uint64_t{1} << n;
    const std::uint64_t mask = modulus - 1u;
    std::uint64_t count = 0;

    for (std::uint64_t x = 0; x < modulus; ++x) {
        const std::uint64_t y0 = add_constant(n, x, constant_key);
        const std::uint64_t y1 = add_constant(n, x ^ input_difference, constant_key);
        if (((y0 ^ y1) & mask) == output_difference) {
            ++count;
        }
    }

    return count;
}

// Exact LC_K numerator: sum_x (-1)^(alpha*x xor beta*F_K(x)).
static std::int64_t lck_numerator(unsigned n,
                                  std::uint64_t constant_key,
                                  std::uint64_t input_mask,
                                  std::uint64_t output_mask)
{
    std::array<std::int64_t, 2> signed_mass{1, 0};

    for (unsigned i = 0; i < n; ++i) {
        std::array<std::int64_t, 2> next_mass{0, 0};
        const unsigned k_i = bit(constant_key, i);
        const unsigned alpha_i = bit(input_mask, i);
        const unsigned beta_i = bit(output_mask, i);

        for (unsigned carry = 0; carry <= 1; ++carry) {
            const std::int64_t mass = signed_mass[carry];
            if (mass == 0) {
                continue;
            }

            for (unsigned x_i = 0; x_i <= 1; ++x_i) {
                const unsigned y_i = x_i ^ k_i ^ carry;
                const unsigned exponent = (alpha_i & x_i) ^ (beta_i & y_i);
                const std::int64_t sign = exponent ? -1 : 1;
                const unsigned next_carry = majority(x_i, k_i, carry);
                next_mass[next_carry] += sign * mass;
            }
        }

        signed_mass = next_mass;
    }

    return signed_mass[0] + signed_mass[1];
}

static std::int64_t brute_lck_numerator(unsigned n,
                                        std::uint64_t constant_key,
                                        std::uint64_t input_mask,
                                        std::uint64_t output_mask)
{
    const std::uint64_t modulus = std::uint64_t{1} << n;
    std::int64_t sum = 0;

    for (std::uint64_t x = 0; x < modulus; ++x) {
        const std::uint64_t y = add_constant(n, x, constant_key);
        const unsigned exponent = parity(input_mask & x) ^ parity(output_mask & y);
        sum += exponent ? -1 : 1;
    }

    return sum;
}

static void exhaustive_small_width_checks()
{
    for (unsigned n = 1; n <= 8; ++n) {
        const std::uint64_t modulus = std::uint64_t{1} << n;
        for (std::uint64_t constant_key = 0; constant_key < modulus; ++constant_key) {
            for (std::uint64_t u = 0; u < modulus; ++u) {
                for (std::uint64_t v = 0; v < modulus; ++v) {
                    const auto exact = dpk_numerator(n, constant_key, u, v);
                    const auto brute = brute_dpk_numerator(n, constant_key, u, v);
                    if (exact != brute) {
                        throw std::runtime_error("DP_K mismatch");
                    }
                }
            }
            for (std::uint64_t alpha = 0; alpha < modulus; ++alpha) {
                for (std::uint64_t beta = 0; beta < modulus; ++beta) {
                    const auto exact = lck_numerator(n, constant_key, alpha, beta);
                    const auto brute = brute_lck_numerator(n, constant_key, alpha, beta);
                    if (exact != brute) {
                        throw std::runtime_error("LC_K mismatch");
                    }
                }
            }
        }
    }
}

static void random_medium_width_checks()
{
    std::mt19937_64 rng(0x454b494b415f4450ULL);
    for (unsigned n : {12u, 16u}) {
        const std::uint64_t mask = mask_for_width(n);
        for (unsigned trial = 0; trial < 512; ++trial) {
            const std::uint64_t constant_key = rng() & mask;
            const std::uint64_t u = rng() & mask;
            const std::uint64_t v = rng() & mask;
            const std::uint64_t alpha = rng() & mask;
            const std::uint64_t beta = rng() & mask;

            const auto dp_exact = dpk_numerator(n, constant_key, u, v);
            const auto dp_brute = brute_dpk_numerator(n, constant_key, u, v);
            if (dp_exact != dp_brute) {
                throw std::runtime_error("random DP_K mismatch");
            }

            const auto lc_exact = lck_numerator(n, constant_key, alpha, beta);
            const auto lc_brute = brute_lck_numerator(n, constant_key, alpha, beta);
            if (lc_exact != lc_brute) {
                throw std::runtime_error("random LC_K mismatch");
            }
        }
    }
}

} // namespace fixed_addend

int main()
{
    using namespace fixed_addend;

    exhaustive_small_width_checks();
    random_medium_width_checks();

    constexpr unsigned n = 8;
    constexpr std::uint64_t k = 0x3cu;
    constexpr std::uint64_t u = 0x04u;
    constexpr std::uint64_t v = 0x0cu;
    constexpr std::uint64_t alpha = 0x10u;
    constexpr std::uint64_t beta = 0x10u;

    const auto dp_count = dpk_numerator(n, k, u, v);
    const auto lc_sum = lck_numerator(n, k, alpha, beta);

    std::cout << "DP_K numerator example = " << dp_count << "/" << (std::uint64_t{1} << n) << '\n';
    std::cout << "LC_K numerator example = " << lc_sum << "/" << (std::uint64_t{1} << n) << '\n';
    std::cout << "all DP_K and LC_K reference checks passed" << '\n';
}
