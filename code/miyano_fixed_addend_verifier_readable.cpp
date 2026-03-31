// ============================================================================
// Reverse-Engineering Miyano's Fixed-Addend Differential and Linear Theory
// Single-file verifier / reproducer
//
// Reading guide for this file:
//   1. Low-level arithmetic and dyadic helper
//   2. Exact fixed-addend differential core
//   3. Exact fixed-addend linear core
//   4. Search-oriented side experiment on the differential core
//   5. Part I toy diagnostics and visible phenomenology
//   6. Exhaustive verification suites and appendix-level identities
//   7. Orchestration in main()
//
// The goal is to keep the mathematics visible in the engineering layer:
// function names and state names are chosen so that a reader can map them
// directly to the paper's objects (carry-pair states, scalar live slice,
// signed carry-conditioned Walsh state, exact 4-state count propagation, etc.).
// ============================================================================

#include <array>
#include <bit>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <random>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>
#include <map>

// ============================================================================
// Section 1. Low-level arithmetic and tiny dyadic helper
// ============================================================================

struct Dyadic {
    std::int64_t num = 0; // value = num / 2^shift
    int shift = 0;

    Dyadic() = default;
    Dyadic(std::int64_t n, int s) : num(n), shift(s) { normalize(); }

    static Dyadic zero() { return Dyadic(0, 0); }
    static Dyadic one() { return Dyadic(1, 0); }
    static Dyadic half() { return Dyadic(1, 1); }
    static Dyadic bit(int b) { return Dyadic(b ? 1 : 0, 0); }

    void normalize() {
        if (num == 0) {
            shift = 0;
            return;
        }
        while (shift > 0 && (num & 1LL) == 0) {
            num >>= 1;
            --shift;
        }
    }
};

static Dyadic align_add(const Dyadic& a, const Dyadic& b, int sign_b = +1) {
    const int s = std::max(a.shift, b.shift);
    const std::int64_t na = a.num << (s - a.shift);
    const std::int64_t nb = b.num << (s - b.shift);
    return Dyadic(na + sign_b * nb, s);
}

static Dyadic operator+(const Dyadic& a, const Dyadic& b) { return align_add(a, b, +1); }
static Dyadic operator-(const Dyadic& a, const Dyadic& b) { return align_add(a, b, -1); }
static Dyadic operator*(const Dyadic& a, const Dyadic& b) { return Dyadic(a.num * b.num, a.shift + b.shift); }
static bool operator==(const Dyadic& a, const Dyadic& b) {
    const int s = std::max(a.shift, b.shift);
    return (a.num << (s - a.shift)) == (b.num << (s - b.shift));
}

static std::uint32_t add_mod_2n(std::uint32_t x, std::uint32_t a, int n) {
    const std::uint32_t mask = (n == 32) ? 0xFFFFFFFFu : ((1u << n) - 1u);
    return (x + a) & mask;
}

static std::uint32_t sub_mod_2n(std::uint32_t x, std::uint32_t y, int n) {
    const std::uint32_t mask = (n == 32) ? 0xFFFFFFFFu : ((1u << n) - 1u);
    return (x - y) & mask;
}

static std::uint32_t multiply_by_two_mod_2n(std::uint32_t x, int n) {
    const std::uint32_t mask = (n == 32) ? 0xFFFFFFFFu : ((1u << n) - 1u);
    return (x << 1) & mask;
}

static int majority_bit(int x_bit, int addend_bit, int incoming_carry_bit) {
        return (x_bit & addend_bit) ^ (x_bit & incoming_carry_bit) ^ (addend_bit & incoming_carry_bit);
}

// Direct oracle for the fixed-addend differential count
//   #{ x : f_a(x xor u) xor f_a(x) = v }.
static std::uint64_t count_differential_pairs_bruteforce(int n, std::uint32_t constant_addend,
                                                         std::uint32_t input_difference,
                                                         std::uint32_t output_difference) {
    std::uint64_t surviving_input_count = 0;
    const std::uint32_t word_limit = 1u << n;
    for (std::uint32_t x = 0; x < word_limit; ++x) {
        const std::uint32_t lhs = add_mod_2n(x ^ input_difference, constant_addend, n);
        const std::uint32_t rhs = add_mod_2n(x, constant_addend, n);
        if ((lhs ^ rhs) == output_difference) {
            ++surviving_input_count;
        }
    }
    return surviving_input_count;
}

// ============================================================================
// Section 2. Exact fixed-addend differential core
// Theory mapping:
//   - brute-force oracle              -> direct definition of DP_a(u -> v)
//   - exact 4-state count propagation -> finite-state carry-pair form
//   - scalar dyadic evaluator         -> Algorithm 1 style normalized scan
// ============================================================================

using BinaryMap = std::uint32_t (*)(std::uint32_t, std::uint32_t, int);

static std::uint32_t pht1_map(std::uint32_t x1, std::uint32_t x2, int n) {
    return add_mod_2n(multiply_by_two_mod_2n(x1, n), x2, n);
}

static std::uint32_t pht2_map(std::uint32_t x1, std::uint32_t x2, int n) {
    return add_mod_2n(x1, x2, n);
}

static std::uint32_t pht_inv1_map(std::uint32_t y1, std::uint32_t y2, int n) {
    return sub_mod_2n(y1, y2, n);
}

static std::uint32_t pht_inv2_map(std::uint32_t y2, std::uint32_t y1, int n) {
    return sub_mod_2n(multiply_by_two_mod_2n(y2, n), y1, n);
}

static std::uint64_t count_binary_map_differential_pairs_bruteforce(
    int n,
    BinaryMap f,
    std::uint32_t dx1,
    std::uint32_t dx2,
    std::uint32_t dy
) {
    std::uint64_t cnt = 0;
    const std::uint32_t limit = 1u << n;
    for (std::uint32_t x1 = 0; x1 < limit; ++x1) {
        for (std::uint32_t x2 = 0; x2 < limit; ++x2) {
            const std::uint32_t lhs = f(x1 ^ dx1, x2 ^ dx2, n);
            const std::uint32_t rhs = f(x1, x2, n);
            if ((lhs ^ rhs) == dy) {
                ++cnt;
            }
        }
    }
    return cnt;
}

static std::uint64_t count_pht_differential_pairs_bruteforce(
    int n,
    std::uint32_t dx1,
    std::uint32_t dx2,
    std::uint32_t dy1,
    std::uint32_t dy2
) {
    std::uint64_t cnt = 0;
    const std::uint32_t limit = 1u << n;
    for (std::uint32_t x1 = 0; x1 < limit; ++x1) {
        for (std::uint32_t x2 = 0; x2 < limit; ++x2) {
            const std::uint32_t y1_lhs = pht1_map(x1 ^ dx1, x2 ^ dx2, n);
            const std::uint32_t y2_lhs = pht2_map(x1 ^ dx1, x2 ^ dx2, n);
            const std::uint32_t y1_rhs = pht1_map(x1, x2, n);
            const std::uint32_t y2_rhs = pht2_map(x1, x2, n);
            if (((y1_lhs ^ y1_rhs) == dy1) && ((y2_lhs ^ y2_rhs) == dy2)) {
                ++cnt;
            }
        }
    }
    return cnt;
}

// Exact differential evaluator in carry-pair form.
// This is the finite-state count propagation underlying the 4-state theory.
static std::uint64_t count_differential_pairs_exact_4state(int n, std::uint32_t constant_addend,
                                                           std::uint32_t input_difference,
                                                           std::uint32_t output_difference) {
    static const std::array<std::pair<int, int>, 4> carry_pair_states = {{{0,0},{0,1},{1,0},{1,1}}};
    std::array<std::uint64_t, 4> carry_pair_state_counts = {1, 0, 0, 0};

    for (int bit_index = 0; bit_index < n; ++bit_index) {
        const int addend_bit = (constant_addend >> bit_index) & 1u;
        const int input_difference_bit = (input_difference >> bit_index) & 1u;
        const int output_difference_bit = (output_difference >> bit_index) & 1u;

        std::uint64_t local_transition_count_matrix[4][4] = {};
        for (int source_state_index = 0; source_state_index < 4; ++source_state_index) {
            const auto [carry_into_x, carry_into_x_xor_u] = carry_pair_states[source_state_index];
            if ((input_difference_bit ^ carry_into_x ^ carry_into_x_xor_u) != output_difference_bit) {
                continue;
            }
            for (int input_bit = 0; input_bit <= 1; ++input_bit) {
                const std::pair<int, int> target_carry_pair = {
                    majority_bit(input_bit, addend_bit, carry_into_x),
                    majority_bit(input_bit ^ input_difference_bit, addend_bit, carry_into_x_xor_u)
                };
                int target_state_index = -1;
                for (int state_index = 0; state_index < 4; ++state_index) {
                    if (carry_pair_states[state_index] == target_carry_pair) {
                        target_state_index = state_index;
                        break;
                    }
                }
                ++local_transition_count_matrix[source_state_index][target_state_index];
            }
        }

        std::array<std::uint64_t, 4> next_carry_pair_state_counts = {0, 0, 0, 0};
        for (int source_state_index = 0; source_state_index < 4; ++source_state_index) {
            for (int target_state_index = 0; target_state_index < 4; ++target_state_index) {
                next_carry_pair_state_counts[target_state_index] +=
                    carry_pair_state_counts[source_state_index] *
                    local_transition_count_matrix[source_state_index][target_state_index];
            }
        }
        carry_pair_state_counts = next_carry_pair_state_counts;
    }

    return carry_pair_state_counts[0] + carry_pair_state_counts[1] +
           carry_pair_state_counts[2] + carry_pair_state_counts[3];
}

// Expanded scalar realization of Algorithm 1.
// Returns the normalized dyadic probability rather than the raw differential count.
static Dyadic compute_differential_probability_scalar(int n, std::uint32_t constant_addend,
                                                      std::uint32_t input_difference,
                                                      std::uint32_t output_difference) {
    Dyadic normalized_prefix_mass = Dyadic::one();
    Dyadic scalar_live_slice = Dyadic::zero();

    for (int bit_index = 0; bit_index < n; ++bit_index) {
        const int previous_input_difference_bit =
            (bit_index == 0) ? 0 : ((input_difference >> (bit_index - 1)) & 1u);
        const int previous_output_difference_bit =
            (bit_index == 0) ? 0 : ((output_difference >> (bit_index - 1)) & 1u);
        const int previous_addend_bit =
            (bit_index == 0) ? 0 : ((constant_addend >> (bit_index - 1)) & 1u);
        const int current_parity_bit =
            ((input_difference >> bit_index) & 1u) ^ ((output_difference >> bit_index) & 1u);

        Dyadic local_probability_factor = Dyadic::zero();
        Dyadic next_scalar_live_slice = Dyadic::zero();

        if (previous_input_difference_bit == 0 && previous_output_difference_bit == 0 && current_parity_bit == 0) {
            local_probability_factor = Dyadic::one();
            next_scalar_live_slice = (Dyadic::bit(previous_addend_bit) + scalar_live_slice) * Dyadic::half();
        } else if (previous_input_difference_bit == 0 && previous_output_difference_bit == 0 && current_parity_bit == 1) {
            local_probability_factor = Dyadic::zero();
            next_scalar_live_slice = Dyadic::zero();
        } else if ((previous_input_difference_bit == 0 && previous_output_difference_bit == 1 && current_parity_bit == 0) ||
                   (previous_input_difference_bit == 1 && previous_output_difference_bit == 0 && current_parity_bit == 0)) {
            local_probability_factor = Dyadic::half();
            next_scalar_live_slice = Dyadic::bit(previous_addend_bit);
        } else if ((previous_input_difference_bit == 0 && previous_output_difference_bit == 1 && current_parity_bit == 1) ||
                   (previous_input_difference_bit == 1 && previous_output_difference_bit == 0 && current_parity_bit == 1)) {
            local_probability_factor = Dyadic::half();
            next_scalar_live_slice = scalar_live_slice;
        } else if (previous_input_difference_bit == 1 && previous_output_difference_bit == 1 && current_parity_bit == 0) {
            local_probability_factor = previous_addend_bit ? scalar_live_slice : (Dyadic::one() - scalar_live_slice);
            next_scalar_live_slice = Dyadic::bit(previous_addend_bit);
        } else {
            // Necessarily: (previous_input_difference_bit, previous_output_difference_bit, current_parity_bit) = (1,1,1).
            local_probability_factor = previous_addend_bit ? (Dyadic::one() - scalar_live_slice) : scalar_live_slice;
            next_scalar_live_slice = Dyadic::half();
        }

        normalized_prefix_mass = normalized_prefix_mass * local_probability_factor;
        scalar_live_slice = next_scalar_live_slice;
    }

    return normalized_prefix_mass;
}

// Carry oracle used in the Part I / Part II bridge.
// Returns the incoming carry c_i of x + a at level i, so that
//   f_a(x)_i = x_i xor a_i xor c_i
// and the differential local law can be read as
//   v_i = u_i xor c_i xor c'_i.
static int compute_carry_into_bit(int n, std::uint32_t x, std::uint32_t constant_addend, int bit_index) {
    const std::uint32_t carry_word = x ^ constant_addend ^ add_mod_2n(x, constant_addend, n);
    return static_cast<int>((carry_word >> bit_index) & 1u);
}

// ============================================================================
// Section 3. Exact fixed-addend linear core
// Theory mapping:
//   - brute-force Walsh oracle       -> direct definition of W_a(alpha,beta)
//   - two-state signed scan          -> Algorithm 2 style evaluator
//   - local one-bit transfer         -> explicit / matrix forms of the same
//                                       signed carry-conditioned update
// ============================================================================

// Build the one-bit 2x2 signed transfer kernel M^L_{a_i,mu_i,nu_i}.
static std::array<std::array<std::int64_t, 2>, 2> build_linear_local_kernel_matrix(
    int addend_bit,
    int mu_bit,
    int nu_bit
) {
    std::array<std::array<std::int64_t, 2>, 2> local_signed_transfer_kernel{};
    for (int source_carry = 0; source_carry <= 1; ++source_carry) {
        for (int input_bit = 0; input_bit <= 1; ++input_bit) {
            const int target_carry = majority_bit(input_bit, addend_bit, source_carry);
            const int linear_phase_bit = (mu_bit & input_bit) ^ (nu_bit & addend_bit) ^ (nu_bit & source_carry);
            local_signed_transfer_kernel[source_carry][target_carry] += linear_phase_bit ? -1 : 1;
        }
    }
    return local_signed_transfer_kernel;
}

// Apply the compact 2x2 local kernel to the current signed carry state.
static std::array<std::int64_t, 2> apply_linear_local_kernel_matrix(
    const std::array<std::int64_t, 2>& signed_carry_conditioned_walsh_state,
    int addend_bit,
    int mu_bit,
    int nu_bit
) {
    const auto local_signed_transfer_kernel = build_linear_local_kernel_matrix(addend_bit, mu_bit, nu_bit);
    std::array<std::int64_t, 2> next_signed_carry_conditioned_walsh_state = {0, 0};
    for (int source_carry = 0; source_carry <= 1; ++source_carry) {
        for (int target_carry = 0; target_carry <= 1; ++target_carry) {
            next_signed_carry_conditioned_walsh_state[target_carry] +=
                signed_carry_conditioned_walsh_state[source_carry] *
                local_signed_transfer_kernel[source_carry][target_carry];
        }
    }
    return next_signed_carry_conditioned_walsh_state;
}

// Apply the same one-bit linear transfer in fully expanded brace-style form.
// This keeps the explicit eight local cases visible in the engineering layer.
static std::array<std::int64_t, 2> apply_linear_local_transfer_explicit(
    const std::array<std::int64_t, 2>& signed_carry_conditioned_walsh_state,
    int addend_bit,
    int mu_bit,
    int nu_bit
) {
    const std::int64_t state_at_carry_0 = signed_carry_conditioned_walsh_state[0];
    const std::int64_t state_at_carry_1 = signed_carry_conditioned_walsh_state[1];
    const std::int64_t sign_from_nu = (nu_bit == 0) ? 1 : -1;
    if (addend_bit == 0 && mu_bit == 0) return {2 * state_at_carry_0 + sign_from_nu * state_at_carry_1, sign_from_nu * state_at_carry_1};
    if (addend_bit == 0 && mu_bit == 1) return {sign_from_nu * state_at_carry_1, -sign_from_nu * state_at_carry_1};
    if (addend_bit == 1 && mu_bit == 0) return {sign_from_nu * state_at_carry_0, sign_from_nu * state_at_carry_0 + 2 * state_at_carry_1};
    return {sign_from_nu * state_at_carry_0, -sign_from_nu * state_at_carry_0};
}

// Direct oracle for the fixed-addend Walsh sum
//   W_a(alpha,beta) = sum_x (-1)^{<alpha,x> xor <beta,f_a(x)>}.
static std::int64_t compute_linear_walsh_sum_bruteforce(int n, std::uint32_t constant_addend,
                                                        std::uint32_t input_mask,
                                                        std::uint32_t output_mask) {
    std::int64_t walsh_sum = 0;
    const std::uint32_t word_limit = 1u << n;
    for (std::uint32_t x = 0; x < word_limit; ++x) {
        const std::uint32_t y = add_mod_2n(x, constant_addend, n);
        const int linear_phase_bit = (std::popcount(input_mask & x) ^ std::popcount(output_mask & y)) & 1u;
        walsh_sum += linear_phase_bit ? -1 : 1;
    }
    return walsh_sum;
}

// Exact linear evaluator in signed carry-conditioned two-state form.
// This is the scan version of Algorithm 2 before the final normalization.
static std::int64_t compute_linear_walsh_sum_two_state_scan(int n, std::uint32_t constant_addend,
                                                            std::uint32_t input_mask,
                                                            std::uint32_t output_mask) {
    std::array<std::int64_t, 2> signed_carry_conditioned_walsh_state = {1, 0};
    for (int bit_index = 0; bit_index < n; ++bit_index) {
        const int addend_bit = (constant_addend >> bit_index) & 1u;
        const int mu_bit = ((input_mask >> bit_index) & 1u) ^ ((output_mask >> bit_index) & 1u);
        const int nu_bit = (output_mask >> bit_index) & 1u;
        signed_carry_conditioned_walsh_state =
            apply_linear_local_kernel_matrix(signed_carry_conditioned_walsh_state, addend_bit, mu_bit, nu_bit);
    }
    return signed_carry_conditioned_walsh_state[0] + signed_carry_conditioned_walsh_state[1];
}

// Direct definition of the carry-conditioned partial Walsh state
//   (L_i(0), L_i(1))
// by exhaustive enumeration of all low prefixes of length i.
// This is the oracle behind the 'tiny summary' claim on the linear side.
static std::array<std::int64_t, 2> compute_linear_prefix_state_bruteforce(int prefix_length,
                                                                           std::uint32_t constant_addend,
                                                                           std::uint32_t input_mask,
                                                                           std::uint32_t output_mask) {
    std::array<std::int64_t, 2> signed_prefix_state = {0, 0};
    const std::uint32_t word_limit = 1u << prefix_length;
    for (std::uint32_t x = 0; x < word_limit; ++x) {
        int carry = 0;
        int linear_phase_bit = 0;
        for (int bit_index = 0; bit_index < prefix_length; ++bit_index) {
            const int input_bit = static_cast<int>((x >> bit_index) & 1u);
            const int addend_bit = static_cast<int>((constant_addend >> bit_index) & 1u);
            const int mu_bit = static_cast<int>(((input_mask >> bit_index) & 1u) ^ ((output_mask >> bit_index) & 1u));
            const int nu_bit = static_cast<int>((output_mask >> bit_index) & 1u);
            linear_phase_bit ^= (mu_bit & input_bit) ^ (nu_bit & addend_bit) ^ (nu_bit & carry);
            carry = majority_bit(input_bit, addend_bit, carry);
        }
        signed_prefix_state[carry] += linear_phase_bit ? -1 : 1;
    }
    return signed_prefix_state;
}

// Same carry-conditioned partial Walsh state, but obtained by the recovered
// two-state signed scan instead of brute force.
// Equality with the brute-force version shows that the suffix really only sees
// the one-carry summary (L_i(0), L_i(1)).
static std::array<std::int64_t, 2> compute_linear_prefix_state_two_state_scan(int prefix_length,
                                                                               std::uint32_t constant_addend,
                                                                               std::uint32_t input_mask,
                                                                               std::uint32_t output_mask) {
    std::array<std::int64_t, 2> signed_carry_conditioned_walsh_state = {1, 0};
    for (int bit_index = 0; bit_index < prefix_length; ++bit_index) {
        const int addend_bit = static_cast<int>((constant_addend >> bit_index) & 1u);
        const int mu_bit = static_cast<int>(((input_mask >> bit_index) & 1u) ^ ((output_mask >> bit_index) & 1u));
        const int nu_bit = static_cast<int>((output_mask >> bit_index) & 1u);
        signed_carry_conditioned_walsh_state =
            apply_linear_local_kernel_matrix(signed_carry_conditioned_walsh_state, addend_bit, mu_bit, nu_bit);
    }
    return signed_carry_conditioned_walsh_state;
}

// ============================================================================
// Section 4. Search-oriented side experiment on the differential core
// Not needed for the core reconstruction itself.  It tests whether the exact
// carry-pair state object can also support optimum-style search automation.
// ============================================================================

struct DifferentialDPKey {
    int i;
    std::array<std::uint64_t, 4> z;
    bool operator<(const DifferentialDPKey& other) const {
        if (i != other.i) return i < other.i;
        return z < other.z;
    }
};

static std::uint64_t compute_differential_max_count_dp_rec(int n, std::uint32_t a, int i, const std::array<std::uint64_t, 4>& z,
                                                   std::map<DifferentialDPKey, std::uint64_t>& memo) {
    DifferentialDPKey key{i, z};
    auto it = memo.find(key);
    if (it != memo.end()) return it->second;
    if (i == n) {
        const std::uint64_t total = z[0] + z[1] + z[2] + z[3];
        memo.emplace(key, total);
        return total;
    }
    static const std::array<std::pair<int, int>, 4> states = {{{0,0},{0,1},{1,0},{1,1}}};
    const int ai = (a >> i) & 1u;
    std::uint64_t best = 0;
    for (int ui = 0; ui <= 1; ++ui) {
        for (int vi = 0; vi <= 1; ++vi) {
            std::array<std::uint64_t, 4> next = {0,0,0,0};
            for (int r = 0; r < 4; ++r) {
                const auto [c, cp] = states[r];
                if ((ui ^ c ^ cp) != vi) continue;
                for (int x = 0; x <= 1; ++x) {
                    const std::pair<int, int> s = {majority_bit(x, ai, c), majority_bit(x ^ ui, ai, cp)};
                    int idx = -1;
                    for (int t = 0; t < 4; ++t) {
                        if (states[t] == s) { idx = t; break; }
                    }
                    next[idx] += z[r];
                }
            }
            best = std::max(best, compute_differential_max_count_dp_rec(n, a, i + 1, next, memo));
        }
    }
    memo.emplace(key, best);
    return best;
}

static std::uint64_t compute_differential_max_count_dp(int n, std::uint32_t a) {
    std::map<DifferentialDPKey, std::uint64_t> memo;
    return compute_differential_max_count_dp_rec(n, a, 0, {1,0,0,0}, memo);
}

static std::uint64_t compute_differential_max_count_bruteforce(int n, std::uint32_t a) {
    const std::uint32_t limit = 1u << n;
    std::uint64_t best = 0;
    for (std::uint32_t u = 0; u < limit; ++u) {
        for (std::uint32_t v = 0; v < limit; ++v) {
            best = std::max(best, count_differential_pairs_bruteforce(n, a, u, v));
        }
    }
    return best;
}

static bool verify_linear_local_transfer_equivalence() {
    for (int ai = 0; ai <= 1; ++ai) {
        for (int mu = 0; mu <= 1; ++mu) {
            for (int nu = 0; nu <= 1; ++nu) {
                for (std::int64_t z0 = -3; z0 <= 3; ++z0) {
                    for (std::int64_t z1 = -3; z1 <= 3; ++z1) {
                        const std::array<std::int64_t, 2> z = {z0, z1};
                        if (apply_linear_local_kernel_matrix(z, ai, mu, nu) != apply_linear_local_transfer_explicit(z, ai, mu, nu)) {
                            std::cerr << "Linear local action mismatch at a=" << ai << " mu=" << mu << " nu=" << nu << "\n";
                            return false;
                        }
                    }
                }
            }
        }
    }
    return true;
}

static bool verify_linear_last_bit_necessary_condition(int max_n) {
    for (int n = 1; n <= max_n; ++n) {
        const std::uint32_t limit = 1u << n;
        for (std::uint32_t a = 0; a < limit; ++a) {
            for (std::uint32_t alpha = 0; alpha < limit; ++alpha) {
                for (std::uint32_t beta = 0; beta < limit; ++beta) {
                    const int mu_last = ((alpha >> (n - 1)) & 1u) ^ ((beta >> (n - 1)) & 1u);
                    if (mu_last == 1) {
                        if (compute_linear_walsh_sum_bruteforce(n, a, alpha, beta) != 0 ||
                            compute_linear_walsh_sum_two_state_scan(n, a, alpha, beta) != 0) {
                            std::cerr << "Last-bit necessary condition failed at n=" << n << "\n";
                            return false;
                        }
                    }
                }
            }
        }
    }
    return true;
}

static std::string bit_string(std::uint32_t value, int n) {
    // Print an n-bit word from most significant bit to least significant bit.
    std::string s;
    for (int i = n - 1; i >= 0; --i) {
        s.push_back(((value >> i) & 1u) ? '1' : '0');
    }
    return s;
}


static void print_chapter_banner(const std::string& chapter_label, const std::string& chapter_title) {
    std::cout << "\n[" << chapter_label << "] " << chapter_title << "\n";
    std::cout << std::string(chapter_label.size() + chapter_title.size() + 4, '-') << "\n";
}

static std::string dyadic_probability_string_from_count(std::uint64_t count, int n) {
    Dyadic value(static_cast<std::int64_t>(count), n);
    std::ostringstream oss;
    oss << count << "/2^" << n;
    if (value.shift == 0) {
        oss << " = " << value.num;
    } else {
        oss << " = " << value.num << "/2^" << value.shift;
    }
    return oss.str();
}

static std::vector<int> compute_carry_trace(std::uint32_t x, std::uint32_t constant_addend, int n) {
    std::vector<int> carry(n + 1, 0);
    for (int i = 0; i < n; ++i) {
        const int xi = static_cast<int>((x >> i) & 1u);
        const int addend_bit = static_cast<int>((constant_addend >> i) & 1u);
        carry[i + 1] = majority_bit(xi, addend_bit, carry[i]);
    }
    return carry;
}

// ============================================================================
// Section 5. Part I toy diagnostics and visible phenomenology
// These functions are explanatory printouts, not part of the exact evaluators.
// ============================================================================

static void print_toy_differential_table(int n, std::uint32_t a) {
    const std::uint32_t limit = 1u << n;
    std::cout << "[TOY] 1996-style small differential table\n";
    std::cout << "      n=" << n << ", a=" << bit_string(a, n) << "\n";
    std::cout << "      DP_a(u->v) = 2^{-n} * #{ x : f_a(x xor u) xor f_a(x) = v }\n";
    std::cout << "      f_a(x xor u) xor f_a(x) = u xor Car_a(x xor u) xor Car_a(x)\n";
    std::cout << "      local bit law: v_i = u_i xor c_i xor c'_i\n\n";

    std::cout << std::setw(8) << "u\\v";
    for (std::uint32_t v = 0; v < limit; ++v) {
        std::cout << std::setw(10) << bit_string(v, n);
    }
    std::cout << "\n";

    for (std::uint32_t u = 0; u < limit; ++u) {
        std::cout << std::setw(8) << bit_string(u, n);
        for (std::uint32_t v = 0; v < limit; ++v) {
            const std::uint64_t brute = count_differential_pairs_bruteforce(n, a, u, v);
            const std::uint64_t automaton = count_differential_pairs_exact_4state(n, a, u, v);
            const Dyadic scalar = compute_differential_probability_scalar(n, a, u, v);
            const std::uint64_t scalar_count = static_cast<std::uint64_t>(scalar.num) << (n - scalar.shift);
            if (brute != automaton || brute != scalar_count) {
                std::cerr << "Toy differential table mismatch at n=" << n << " a=" << a
                          << " u=" << u << " v=" << v << "\n";
                std::exit(1);
            }
            if (brute == 0) {
                std::cout << std::setw(10) << ".";
            } else {
                std::ostringstream cell;
                cell << brute << "/" << limit;
                std::cout << std::setw(10) << cell.str();
            }
        }
        std::cout << "\n";
    }
    std::cout << "\n";
}

static void print_addend_dependence_row_demo(int n, std::uint32_t u, std::uint32_t a0, std::uint32_t a1) {
    const std::uint32_t limit = 1u << n;
    std::cout << "[TOY] Same visible input difference, different addend row\n";
    std::cout << "      n=" << n << ", u=" << bit_string(u, n)
              << ", a0=" << bit_string(a0, n) << ", a1=" << bit_string(a1, n) << "\n";
    std::cout << "      This is the addend-dependency witness: the row changes when only a changes.\n\n";
    std::cout << std::setw(10) << "v"
              << std::setw(14) << bit_string(a0, n)
              << std::setw(14) << bit_string(a1, n) << "\n";
    for (std::uint32_t v = 0; v < limit; ++v) {
        const std::uint64_t c0 = count_differential_pairs_bruteforce(n, a0, u, v);
        const std::uint64_t c1 = count_differential_pairs_bruteforce(n, a1, u, v);
        std::ostringstream s0;
        std::ostringstream s1;
        s0 << c0 << "/" << limit;
        s1 << c1 << "/" << limit;
        std::cout << std::setw(10) << bit_string(v, n)
                  << std::setw(14) << s0.str()
                  << std::setw(14) << s1.str() << "\n";
    }
    std::cout << "\n";
}

static void print_prefix_state_slice_demo(int n, std::uint32_t a, std::uint32_t u, std::uint32_t v) {
    const std::uint32_t limit = 1u << n;
    std::vector<std::uint32_t> live_x;
    for (std::uint32_t x = 0; x < limit; ++x) {
        if ((add_mod_2n(x ^ u, a, n) ^ add_mod_2n(x, a, n)) == v) {
            live_x.push_back(x);
        }
    }

    std::cout << "[TOY] Tiny-summary slice demo for one surviving differential\n";
    std::cout << "      n=" << n << ", a=" << bit_string(a, n)
              << ", u=" << bit_string(u, n) << ", v=" << bit_string(v, n)
              << ", surviving x count=" << live_x.size()
              << " (" << dyadic_probability_string_from_count(live_x.size(), n) << ")\n";
    std::cout << "      theorem-side claim: at level i, only the carry pair (c_i, c'_i) matters.\n";
    std::cout << "      parity slice rule  : c_i xor c'_i = u_i xor v_i\n\n";

    std::cout << std::setw(8) << "level"
              << std::setw(10) << "u_i"
              << std::setw(10) << "v_i"
              << std::setw(12) << "u_i^v_i"
              << std::setw(10) << "00"
              << std::setw(10) << "01"
              << std::setw(10) << "10"
              << std::setw(10) << "11"
              << "\n";

    for (int i = 0; i < n; ++i) {
        std::array<std::uint32_t, 4> counts = {0, 0, 0, 0};
        for (const std::uint32_t x : live_x) {
            const auto c = compute_carry_trace(x, a, n);
            const auto cp = compute_carry_trace(x ^ u, a, n);
            const int state = (c[i] << 1) | cp[i];
            ++counts[state];
        }

        const int ui = static_cast<int>((u >> i) & 1u);
        const int vi = static_cast<int>((v >> i) & 1u);
        const int parity = ui ^ vi;
        std::cout << std::setw(8) << i
                  << std::setw(10) << ui
                  << std::setw(10) << vi
                  << std::setw(12) << parity
                  << std::setw(10) << counts[0]
                  << std::setw(10) << counts[1]
                  << std::setw(10) << counts[2]
                  << std::setw(10) << counts[3]
                  << "\n";

        if ((parity == 0 && (counts[1] != 0 || counts[2] != 0)) ||
            (parity == 1 && (counts[0] != 0 || counts[3] != 0))) {
            std::cerr << "Prefix slice demo violated carry-pair parity law at level i=" << i << "\n";
            std::exit(1);
        }
    }
    std::cout << "\n";
}


static void print_toy_linear_table(int n, std::uint32_t a) {
    const std::uint32_t limit = 1u << n;
    std::cout << "[TOY] 1996-style small linear Walsh table\n";
    std::cout << "      n=" << n << ", a=" << bit_string(a, n) << "\n";
    std::cout << "      W_a(alpha,beta) = sum_x (-1)^{<alpha,x> xor <beta,f_a(x)>}\n";
    std::cout << "      Corr_a(alpha->beta) = 2^{-n} * W_a(alpha,beta)\n\n";

    std::cout << std::setw(12) << "alpha\\beta";
    for (std::uint32_t beta = 0; beta < limit; ++beta) {
        std::cout << std::setw(8) << bit_string(beta, n);
    }
    std::cout << "\n";

    for (std::uint32_t alpha = 0; alpha < limit; ++alpha) {
        std::cout << std::setw(12) << bit_string(alpha, n);
        for (std::uint32_t beta = 0; beta < limit; ++beta) {
            const std::int64_t brute = compute_linear_walsh_sum_bruteforce(n, a, alpha, beta);
            const std::int64_t matrix = compute_linear_walsh_sum_two_state_scan(n, a, alpha, beta);
            if (brute != matrix) {
                std::cerr << "Toy linear table mismatch at n=" << n << " a=" << a
                          << " alpha=" << alpha << " beta=" << beta << "\n";
                std::exit(1);
            }
            if (brute == 0) {
                std::cout << std::setw(8) << ".";
            } else {
                std::cout << std::setw(8) << brute;
            }
        }
        std::cout << "\n";
    }
    std::cout << "\n";
}

static void print_linear_addend_dependence_demo(int n, std::uint32_t alpha, std::uint32_t beta,
                                                std::uint32_t a0, std::uint32_t a1) {
    std::cout << "[TOY] Same visible mask pair, different addend on the linear side\n";
    std::cout << "      n=" << n
              << ", alpha=" << bit_string(alpha, n)
              << ", beta=" << bit_string(beta, n)
              << ", a0=" << bit_string(a0, n)
              << ", a1=" << bit_string(a1, n) << "\n";
    const std::int64_t w0 = compute_linear_walsh_sum_bruteforce(n, a0, alpha, beta);
    const std::int64_t w1 = compute_linear_walsh_sum_bruteforce(n, a1, alpha, beta);
    const std::int64_t m0 = compute_linear_walsh_sum_two_state_scan(n, a0, alpha, beta);
    const std::int64_t m1 = compute_linear_walsh_sum_two_state_scan(n, a1, alpha, beta);
    if (w0 != m0 || w1 != m1) {
        std::cerr << "Linear addend-dependence witness mismatch.\n";
        std::exit(1);
    }
    std::cout << "      W_{a0}(alpha,beta) = " << w0 << "   Corr = " << w0 << "/" << (1u << n) << "\n";
    std::cout << "      W_{a1}(alpha,beta) = " << w1 << "   Corr = " << w1 << "/" << (1u << n) << "\n";
    std::cout << "      This is the signed addend-dependency witness: same visible masks, different addend, different sign/magnitude.\n\n";
}

static void print_linear_prefix_state_demo(int n, std::uint32_t a, std::uint32_t alpha, std::uint32_t beta) {
    std::cout << "[TOY] Linear tiny-summary demo via conditioned partial Walsh sums\n";
    std::cout << "      n=" << n
              << ", a=" << bit_string(a, n)
              << ", alpha=" << bit_string(alpha, n)
              << ", beta=" << bit_string(beta, n) << "\n";
    std::cout << "      L_i(r) = sum over low prefixes of length i with carry c_i=r of the signed local contribution\n";
    std::cout << "      theorem-side claim: the suffix only needs the pair (L_i(0), L_i(1)).\n\n";

    std::cout << std::setw(16) << "prefix i"
              << std::setw(10) << "a_i"
              << std::setw(10) << "mu_i"
              << std::setw(10) << "nu_i"
              << std::setw(12) << "L_i(0)"
              << std::setw(12) << "L_i(1)"
              << std::setw(14) << "L_i(0)+L_i(1)"
              << "\n";

    for (int i = 0; i <= n; ++i) {
        const auto brute = compute_linear_prefix_state_bruteforce(i, a, alpha, beta);
        const auto matrix = compute_linear_prefix_state_two_state_scan(i, a, alpha, beta);
        if (brute != matrix) {
            std::cerr << "Linear prefix-state demo mismatch at i=" << i << "\n";
            std::exit(1);
        }
        std::string ai = "--";
        std::string mu = "--";
        std::string nu = "--";
        if (i < n) {
            ai = std::to_string((a >> i) & 1u);
            mu = std::to_string(((alpha >> i) & 1u) ^ ((beta >> i) & 1u));
            nu = std::to_string((beta >> i) & 1u);
        }
        std::cout << std::setw(16) << i
                  << std::setw(10) << ai
                  << std::setw(10) << mu
                  << std::setw(10) << nu
                  << std::setw(12) << brute[0]
                  << std::setw(12) << brute[1]
                  << std::setw(14) << (brute[0] + brute[1])
                  << "\n";
    }
    const auto final = compute_linear_prefix_state_bruteforce(n, a, alpha, beta);
    const std::int64_t w = compute_linear_walsh_sum_bruteforce(n, a, alpha, beta);
    if ((final[0] + final[1]) != w) {
        std::cerr << "Linear prefix-state final sum mismatch.\n";
        std::exit(1);
    }
    std::cout << "\n";
}

struct RunCounterexample {
    bool found = false;
    int n = 0;
    std::uint32_t a = 0, u = 0, v = 0;
    int m = 0, r = 0;
};

// ============================================================================
// Section 6. Exhaustive verification suites and appendix-level identities
// ============================================================================

// Search for the first counterexample to the older over-strong block law.
// This is intentionally kept as a separate witness search: it documents a
// negative result, namely that not every all-ones run forces the addend bits
// on the whole run to stay constant.
static RunCounterexample find_old_run_law_counterexample(int max_n) {
    for (int n = 2; n <= max_n; ++n) {
        const std::uint32_t limit = 1u << n;
        for (std::uint32_t a = 0; a < limit; ++a) {
            for (std::uint32_t u = 0; u < limit; ++u) {
                for (std::uint32_t v = 0; v < limit; ++v) {
                    if (count_differential_pairs_bruteforce(n, a, u, v) == 0) continue;
                    for (int i = 0; i < n; ) {
                        if (((u >> i) & 1u) && ((v >> i) & 1u)) {
                            const int m = i;
                            while (i + 1 < n && ((u >> (i + 1)) & 1u) && ((v >> (i + 1)) & 1u)) {
                                ++i;
                            }
                            const int r = i;
                            if (r - m >= 1) {
                                bool same = true;
                                for (int j = m + 1; j <= r; ++j) {
                                    if (((a >> j) & 1u) != ((a >> m) & 1u)) {
                                        same = false;
                                        break;
                                    }
                                }
                                if (!same) {
                                    return {true, n, a, u, v, m, r};
                                }
                            }
                        }
                        ++i;
                    }
                }
            }
        }
    }
    return {};
}

// Exhaustively validate the corrected run law stated in the paper.
// Interior bits of an all-ones run are forced, while the exit bit is governed
// by the parity bit u_{r+1} xor v_{r+1}.
static bool verify_corrected_run_law(int max_n) {
    for (int n = 2; n <= max_n; ++n) {
        const std::uint32_t limit = 1u << n;
        for (std::uint32_t a = 0; a < limit; ++a) {
            for (std::uint32_t u = 0; u < limit; ++u) {
                for (std::uint32_t v = 0; v < limit; ++v) {
                    if (count_differential_pairs_bruteforce(n, a, u, v) == 0) continue;
                    for (int i = 0; i < n; ) {
                        if (((u >> i) & 1u) && ((v >> i) & 1u)) {
                            const int m = i;
                            while (i + 1 < n && ((u >> (i + 1)) & 1u) && ((v >> (i + 1)) & 1u)) {
                                ++i;
                            }
                            const int r = i;
                            if (r - m >= 1) {
                                for (int j = m + 1; j <= r - 1; ++j) {
                                    if (((a >> j) & 1u) != ((a >> m) & 1u)) {
                                        std::cerr << "Corrected run law failed (interior) at n=" << n << "\n";
                                        return false;
                                    }
                                }
                                if (r + 1 < n) {
                                    const int lhs = (a >> r) & 1u;
                                    const int rhs = ((a >> m) & 1u) ^ (((u >> (r + 1)) & 1u) ^ ((v >> (r + 1)) & 1u));
                                    if (lhs != rhs) {
                                        std::cerr << "Corrected run law failed (exit) at n=" << n << "\n";
                                        return false;
                                    }
                                }
                            }
                        }
                        ++i;
                    }
                }
            }
        }
    }
    return true;
}

// Verify the threshold characterization of the carry into level i:
// the carry appears exactly when the low i-bit prefix crosses the threshold
// 2^i - a_low.  This is the fixed-addend version of the usual carry threshold
// view of binary addition.
static bool verify_threshold_carry_formula(int max_n) {
    for (int n = 1; n <= max_n; ++n) {
        const std::uint32_t limit = 1u << n;
        for (std::uint32_t a = 0; a < limit; ++a) {
            for (std::uint32_t x = 0; x < limit; ++x) {
                for (int i = 0; i < n; ++i) {
                    const std::uint32_t lower_mask = (i == 0) ? 0u : ((1u << i) - 1u);
                    const std::uint32_t a_low = a & lower_mask;
                    int predicted = 0;
                    if (a_low != 0) {
                        predicted = ((x & lower_mask) >= ((1u << i) - a_low)) ? 1 : 0;
                    }
                    const int actual = compute_carry_into_bit(n, x, a, i);
                    if (actual != predicted) {
                        std::cerr << "Threshold carry formula failed at n=" << n
                                  << " x=" << x << " a=" << a << " i=" << i << "\n";
                        return false;
                    }
                }
            }
        }
    }
    return true;
}

// Verify the carry-free coordinate recurrence for the graph of f_a.
// This rewrites the next output bit f_{i+1}(x) using only x_i, a_i, x_{i+1},
// a_{i+1}, and the already known coordinate f_i(x).
static bool verify_carryfree_coordinate_recurrence(int max_n) {
    for (int n = 1; n <= max_n; ++n) {
        const std::uint32_t limit = 1u << n;
        for (std::uint32_t a = 0; a < limit; ++a) {
            for (std::uint32_t x = 0; x < limit; ++x) {
                const std::uint32_t y = add_mod_2n(x, a, n);
                if ((y & 1u) != ((x & 1u) ^ (a & 1u))) {
                    std::cerr << "Carry-free recurrence base case failed at n=" << n << "\n";
                    return false;
                }
                for (int i = 0; i + 1 < n; ++i) {
                    const int fi = static_cast<int>((y >> i) & 1u);
                    const int lhs = static_cast<int>((y >> (i + 1)) & 1u);
                    const int xi = static_cast<int>((x >> i) & 1u);
                    const int ai = static_cast<int>((a >> i) & 1u);
                    const int xi1 = static_cast<int>((x >> (i + 1)) & 1u);
                    const int ai1 = static_cast<int>((a >> (i + 1)) & 1u);
                    const int rhs = xi1 ^ ai1 ^ xi ^ ai ^ (xi & ai) ^ ((xi ^ ai) & fi);
                    if (lhs != rhs) {
                        std::cerr << "Carry-free recurrence failed at n=" << n
                                  << " x=" << x << " a=" << a << " i=" << i << "\n";
                        return false;
                    }
                }
            }
        }
    }
    return true;
}

static std::int64_t compute_linear_single_bit_interval_sum(int n, std::uint32_t a, std::uint32_t alpha, int i) {
    std::int64_t sum = 0;
    const std::uint32_t limit = 1u << n;
    const std::uint32_t beta = 1u << i;
    const int ai = static_cast<int>((a >> i) & 1u);
    const std::uint32_t lower_mask = (i == 0) ? 0u : ((1u << i) - 1u);
    const std::uint32_t a_low = a & lower_mask;
    const std::uint32_t tau = (i == 0) ? 0u : ((1u << i) - a_low);
    for (std::uint32_t x = 0; x < limit; ++x) {
        int c = 0;
        if (a_low != 0) {
            c = ((x & lower_mask) >= tau) ? 1 : 0;
        }
        const int phase = (std::popcount((alpha ^ beta) & x) ^ ai ^ c) & 1u;
        sum += phase ? -1 : 1;
    }
    return sum;
}

// Verify the single-output-bit interval formula on the linear side.
// This is the explicit interval-sum form of the Walsh object when beta has
// Hamming weight one.
static bool verify_single_bit_interval_formula(int max_n) {
    for (int n = 1; n <= max_n; ++n) {
        const std::uint32_t limit = 1u << n;
        for (std::uint32_t a = 0; a < limit; ++a) {
            for (std::uint32_t alpha = 0; alpha < limit; ++alpha) {
                for (int i = 0; i < n; ++i) {
                    const std::int64_t brute = compute_linear_walsh_sum_bruteforce(n, a, alpha, 1u << i);
                    const std::int64_t interval = compute_linear_single_bit_interval_sum(n, a, alpha, i);
                    if (brute != interval) {
                        std::cerr << "Single-bit interval formula failed at n=" << n
                                  << " a=" << a << " alpha=" << alpha << " i=" << i << "\n";
                        return false;
                    }
                }
            }
        }
    }
    return true;
}

// Verify the PHT possibility criterion by comparing the direct joint condition
// with the four projected fixed-addend conditions.
static bool verify_pht_possibility_criterion(int max_n, std::uint64_t& checked_instances) {
    checked_instances = 0;
    for (int n = 1; n <= max_n; ++n) {
        const std::uint32_t limit = 1u << n;
        for (std::uint32_t dx1 = 0; dx1 < limit; ++dx1) {
            for (std::uint32_t dx2 = 0; dx2 < limit; ++dx2) {
                for (std::uint32_t dy1 = 0; dy1 < limit; ++dy1) {
                    for (std::uint32_t dy2 = 0; dy2 < limit; ++dy2) {
                        const bool direct_possible =
                            count_pht_differential_pairs_bruteforce(n, dx1, dx2, dy1, dy2) != 0;
                        const bool projected_possible =
                            count_binary_map_differential_pairs_bruteforce(n, pht1_map, dx1, dx2, dy1) != 0 &&
                            count_binary_map_differential_pairs_bruteforce(n, pht2_map, dx1, dx2, dy2) != 0 &&
                            count_binary_map_differential_pairs_bruteforce(n, pht_inv1_map, dy1, dy2, dx1) != 0 &&
                            count_binary_map_differential_pairs_bruteforce(n, pht_inv2_map, dy2, dy1, dx2) != 0;
                        if (direct_possible != projected_possible) {
                            std::cerr << "PHT possibility mismatch at n=" << n
                                      << " dx1=" << bit_string(dx1, n)
                                      << " dx2=" << bit_string(dx2, n)
                                      << " dy1=" << bit_string(dy1, n)
                                      << " dy2=" << bit_string(dy2, n) << "\n";
                            return false;
                        }
                        ++checked_instances;
                    }
                }
            }
        }
    }
    return true;
}

// ============================================================================
// Section 7. Orchestration
// ============================================================================

int main() {
    std::cout << "Miyano fixed-addend core-chapter verification (v16, readable order)\n";
    std::cout << "============================================================\n\n";
    std::cout << "This execution order follows the paper rather than the historical order in\n";
    std::cout << "which the checks were originally added to the verifier.  The goal is that a\n";
    std::cout << "reader can move from Part I intuition, to Part II exact differential core,\n";
    std::cout << "to Part III exact linear core, and finally to Appendix-level audits.\n";

    // ---------------------------------------------------------------------
    // Part I. Visible phenomenology and tiny-summary diagnostics.
    // These printouts are explanatory: they show what a 1996-style desk study
    // would have seen before everything is compressed into finite-state form.
    // ---------------------------------------------------------------------
    print_chapter_banner("Part I", "Visible phenomenology and tiny-summary demos");
    print_toy_differential_table(3, 0b001u);
    print_addend_dependence_row_demo(4, 0b0100u, 0b0001u, 0b0011u);
    print_prefix_state_slice_demo(4, 0b0001u, 0b0001u, 0b0111u);
    print_toy_linear_table(3, 0b001u);
    print_linear_addend_dependence_demo(4, 0b0011u, 0b0010u, 0b0001u, 0b0011u);
    print_linear_prefix_state_demo(4, 0b0001u, 0b0100u, 0b0100u);

    // ---------------------------------------------------------------------
    // Part II. Exact fixed-addend differential core.
    // Here the theorem-side objects are checked directly:
    //   brute-force count
    // = exact 4-state carry-pair propagation
    // = Algorithm 1 scalar dyadic scan.
    // ---------------------------------------------------------------------
    print_chapter_banner("Part II", "Exact fixed-addend differential core");

    std::uint64_t differential_instance_count = 0;
    std::uint64_t differential_x_evaluation_count = 0;
    for (int n = 1; n <= 6; ++n) {
        const std::uint32_t word_limit = 1u << n;
        for (std::uint32_t constant_addend = 0; constant_addend < word_limit; ++constant_addend) {
            for (std::uint32_t input_difference = 0; input_difference < word_limit; ++input_difference) {
                for (std::uint32_t output_difference = 0; output_difference < word_limit; ++output_difference) {
                    const std::uint64_t brute_force_count =
                        count_differential_pairs_bruteforce(n, constant_addend, input_difference, output_difference);
                    const std::uint64_t exact_4state_count =
                        count_differential_pairs_exact_4state(n, constant_addend, input_difference, output_difference);
                    const Dyadic scalar_probability =
                        compute_differential_probability_scalar(n, constant_addend, input_difference, output_difference);
                    const std::int64_t scalar_probability_as_count = scalar_probability.num << (n - scalar_probability.shift);
                    if (brute_force_count != exact_4state_count ||
                        brute_force_count != static_cast<std::uint64_t>(scalar_probability_as_count)) {
                        std::cerr << "Differential mismatch at n=" << n
                                  << " a=" << constant_addend
                                  << " u=" << input_difference
                                  << " v=" << output_difference << "\n";
                        return 1;
                    }
                    ++differential_instance_count;
                    differential_x_evaluation_count += word_limit;
                }
            }
        }
    }

    std::cout << "[OK] Differential brute force = Algorithm 1 scalar recurrence = exact 4-state carry-pair count\n";
    std::cout << "     exhaustive for 1 <= n <= 6\n";
    std::cout << "     instances checked : " << differential_instance_count << "\n";
    std::cout << "     x-evaluations     : " << differential_x_evaluation_count << "\n\n";

    const RunCounterexample old_run_law_counterexample = find_old_run_law_counterexample(6);
    if (!old_run_law_counterexample.found) {
        std::cerr << "Expected old run-law counterexample was not found.\n";
        return 1;
    }

    std::cout << "[INFO] Stronger old block claim is false. First counterexample:\n";
    std::cout << "       n=" << old_run_law_counterexample.n
              << ", A=" << bit_string(old_run_law_counterexample.a, old_run_law_counterexample.n)
              << ", u=" << bit_string(old_run_law_counterexample.u, old_run_law_counterexample.n)
              << ", v=" << bit_string(old_run_law_counterexample.v, old_run_law_counterexample.n)
              << ", block=[" << old_run_law_counterexample.m << "," << old_run_law_counterexample.r << "]\n\n";

    if (!verify_corrected_run_law(6)) {
        return 1;
    }
    std::cout << "[OK] Corrected run law validated exhaustively for all nonzero differentials with 1 <= n <= 6\n\n";

    // ---------------------------------------------------------------------
    // Part III. Exact fixed-addend linear core.
    // Here the theorem-side objects are checked directly:
    //   brute-force Walsh sum
    // = Algorithm 2 signed two-state scan.
    // ---------------------------------------------------------------------
    print_chapter_banner("Part III", "Exact fixed-addend linear core");

    std::uint64_t linear_instance_count = 0;
    std::uint64_t linear_x_evaluation_count = 0;
    for (int n = 1; n <= 6; ++n) {
        const std::uint32_t word_limit = 1u << n;
        for (std::uint32_t constant_addend = 0; constant_addend < word_limit; ++constant_addend) {
            for (std::uint32_t input_mask = 0; input_mask < word_limit; ++input_mask) {
                for (std::uint32_t output_mask = 0; output_mask < word_limit; ++output_mask) {
                    const std::int64_t brute_force_walsh_sum =
                        compute_linear_walsh_sum_bruteforce(n, constant_addend, input_mask, output_mask);
                    const std::int64_t two_state_scan_walsh_sum =
                        compute_linear_walsh_sum_two_state_scan(n, constant_addend, input_mask, output_mask);
                    if (brute_force_walsh_sum != two_state_scan_walsh_sum) {
                        std::cerr << "Linear mismatch at n=" << n
                                  << " a=" << constant_addend
                                  << " alpha=" << input_mask
                                  << " beta=" << output_mask << "\n";
                        return 1;
                    }
                    ++linear_instance_count;
                    linear_x_evaluation_count += word_limit;
                }
            }
        }
    }

    std::cout << "[OK] Linear brute force Walsh sum = Algorithm 2 signed prefix transfer\n";
    std::cout << "     exhaustive for 1 <= n <= 6\n";
    std::cout << "     instances checked : " << linear_instance_count << "\n";
    std::cout << "     x-evaluations     : " << linear_x_evaluation_count << "\n\n";
    std::cout << "[OK] Small-space validation of both recovered O(n) evaluators\n";
    std::cout << "     Algorithm 1 = brute-force differential counting for every (a,u,v), 1 <= n <= 6\n";
    std::cout << "     Algorithm 2 = brute-force Walsh summation for every (a,alpha,beta), 1 <= n <= 6\n";
    std::cout << "     zero mismatches  : yes\n\n";

    if (!verify_linear_local_transfer_equivalence()) {
        return 1;
    }
    std::cout << "[OK] Explicit linear one-bit actions = local 2x2 matrix multiplication\n\n";

    // ---------------------------------------------------------------------
    // Appendix / supplementary audits.
    // These are not the core recovered evaluators themselves; they are the
    // surrounding audits, side identities, and bridge theorems that support
    // the paper's appendices and sanity checks.
    // ---------------------------------------------------------------------
    print_chapter_banner("Appendix D", "Supplementary audits and appendix-level identities");

    std::uint64_t pht_instance_count = 0;
    if (!verify_pht_possibility_criterion(4, pht_instance_count)) {
        return 1;
    }
    std::cout << "[OK] PHT direct possibility = four-projection criterion\n";
    std::cout << "     exhaustive for 1 <= n <= 4\n";
    std::cout << "     instances checked : " << pht_instance_count << "\n\n";

    if (!verify_threshold_carry_formula(8)) {
        return 1;
    }
    std::cout << "[OK] Threshold carry characterization validated exhaustively for 1 <= n <= 8\n\n";

    if (!verify_carryfree_coordinate_recurrence(8)) {
        return 1;
    }
    std::cout << "[OK] Carry-free fixed-addend coordinate recurrence validated exhaustively for 1 <= n <= 8\n\n";

    if (!verify_single_bit_interval_formula(6)) {
        return 1;
    }
    std::cout << "[OK] Single-bit interval Walsh formula validated exhaustively for 1 <= n <= 6\n\n";

    if (!verify_linear_last_bit_necessary_condition(8)) {
        return 1;
    }
    std::cout << "[OK] Last-bit necessary condition validated exhaustively for 1 <= n <= 8\n\n";

    for (int n = 1; n <= 8; ++n) {
        const std::uint32_t word_limit = 1u << n;
        for (std::uint32_t constant_addend = 0; constant_addend < word_limit; ++constant_addend) {
            const std::uint64_t brute_force_best_count = compute_differential_max_count_bruteforce(n, constant_addend);
            const std::uint64_t dynamic_programming_best_count = compute_differential_max_count_dp(n, constant_addend);
            if (brute_force_best_count != dynamic_programming_best_count) {
                std::cerr << "Differential search DP optimum mismatch at n=" << n
                          << " a=" << constant_addend << "\n";
                return 1;
            }
        }
    }
    std::cout << "[OK] Differential search optimum = backward DP over exact carry-count states (1 <= n <= 8)\n\n";

    std::mt19937_64 rng(0xC0FFEE123456789ULL);
    constexpr int random_trials = 20000;
    for (int trial_index = 0; trial_index < random_trials; ++trial_index) {
        const int n = 8;
        const std::uint32_t word_limit = 1u << n;
        const std::uint32_t constant_addend = static_cast<std::uint32_t>(rng() % word_limit);
        const std::uint32_t input_difference = static_cast<std::uint32_t>(rng() % word_limit);
        const std::uint32_t output_difference = static_cast<std::uint32_t>(rng() % word_limit);
        const std::uint64_t brute_force_differential_count =
            count_differential_pairs_bruteforce(n, constant_addend, input_difference, output_difference);
        const std::uint64_t exact_4state_differential_count =
            count_differential_pairs_exact_4state(n, constant_addend, input_difference, output_difference);
        const Dyadic scalar_differential_probability =
            compute_differential_probability_scalar(n, constant_addend, input_difference, output_difference);
        const std::int64_t scalar_probability_as_count =
            scalar_differential_probability.num << (n - scalar_differential_probability.shift);
        if (brute_force_differential_count != exact_4state_differential_count ||
            brute_force_differential_count != static_cast<std::uint64_t>(scalar_probability_as_count)) {
            std::cerr << "Random differential mismatch at n=8\n";
            return 1;
        }

        const std::uint32_t input_mask = static_cast<std::uint32_t>(rng() % word_limit);
        const std::uint32_t output_mask = static_cast<std::uint32_t>(rng() % word_limit);
        const std::int64_t brute_force_linear_walsh_sum =
            compute_linear_walsh_sum_bruteforce(n, constant_addend, input_mask, output_mask);
        const std::int64_t two_state_linear_walsh_sum =
            compute_linear_walsh_sum_two_state_scan(n, constant_addend, input_mask, output_mask);
        if (brute_force_linear_walsh_sum != two_state_linear_walsh_sum) {
            std::cerr << "Random linear mismatch at n=8\n";
            return 1;
        }
    }

    std::cout << "[OK] Additional random spot checks passed for n=8 (" << random_trials << " trials per side)\n";
    return 0;
}
