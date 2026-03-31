#include <array>
#include <cstdint>
#include <iostream>
#include <tuple>
#include <utility>

// ============================================================================
// matrix_repro_check.cpp
//
// Purpose.
//   Standalone reproduction check for the appendix-level local kernels appearing
//   in the reconstructed fixed-addend theory.
//
// File role in the paper.
//   - Appendix B: differential 4-state local kernels M^D_{a,u,v}
//   - Appendix C: linear 2-state local kernels M^L_{a,mu,nu}
//
// Reading guide.
//   This file does not implement the full n-bit evaluators.  Instead, it checks
//   the one-bit local building blocks from which those evaluators are composed.
//   The idea is simple:
//     1) enumerate the one-bit transition directly from the carry laws,
//     2) build the corresponding local kernel matrix,
//     3) compare it against the appendix matrix claimed in the paper.
//
//   So this file is an appendix-kernel audit, not a general verifier.
// ============================================================================

// ============================================================================
// Section 1. Low-level one-bit carry law
//
// The hidden memory on both the differential and linear sides is carried by the
// binary carry recurrence
//     c_{i+1} = Maj(x_i, a_i, c_i),
// where a_i is the fixed addend bit and x_i is the active variable bit.
// ============================================================================

static int majority_bit(int variable_bit, int addend_bit, int incoming_carry) {
    return (variable_bit & addend_bit)
         ^ (variable_bit & incoming_carry)
         ^ (addend_bit  & incoming_carry);
}

using DifferentialLocalKernel4State = std::array<std::array<int,4>,4>;
using LinearLocalKernel2State       = std::array<std::array<int,2>,2>;

// ============================================================================
// Section 2. Appendix B: differential local-kernel reproduction
//
// Mathematical object.
//   For fixed one-bit controls (a,u,v), the appendix differential kernel
//   M^D_{a,u,v} acts on the four carry-pair states
//       (c_i, c'_i) in {(0,0),(0,1),(1,0),(1,1)}.
//
// Reproduction principle.
//   A row survives only if the visible parity constraint
//       v = u xor c_i xor c'_i
//   is satisfied.  Then x_i in {0,1} is enumerated, the next carry pair is
//   computed explicitly, and the appropriate matrix entry is incremented.
// ============================================================================

static DifferentialLocalKernel4State build_differential_local_kernel_from_one_bit_enumeration(
    int addend_bit,
    int input_difference_bit,
    int output_difference_bit)
{
    static const std::array<std::pair<int,int>,4> carry_pair_states = {{{0,0},{0,1},{1,0},{1,1}}};

    DifferentialLocalKernel4State local_kernel{};
    for (int source_state_index = 0; source_state_index < 4; ++source_state_index) {
        auto [left_incoming_carry, right_incoming_carry] = carry_pair_states[source_state_index];

        if ((input_difference_bit ^ left_incoming_carry ^ right_incoming_carry) != output_difference_bit) {
            continue;
        }

        for (int variable_bit = 0; variable_bit <= 1; ++variable_bit) {
            std::pair<int,int> next_carry_pair = {
                majority_bit(variable_bit, addend_bit, left_incoming_carry),
                majority_bit(variable_bit ^ input_difference_bit, addend_bit, right_incoming_carry)
            };

            for (int target_state_index = 0; target_state_index < 4; ++target_state_index) {
                if (carry_pair_states[target_state_index] == next_carry_pair) {
                    ++local_kernel[source_state_index][target_state_index];
                    break;
                }
            }
        }
    }
    return local_kernel;
}

// ============================================================================
// Section 3. Appendix C: linear local-kernel reproduction
//
// Mathematical object.
//   For fixed one-bit controls (a,mu,nu), the appendix linear kernel
//   M^L_{a,mu,nu} acts on the two carry slices r in {0,1}.
//
// Reproduction principle.
//   For each current carry slice r and each variable bit x_i in {0,1}, compute
//   the next carry slice s = Maj(x_i,a_i,r) and the one-bit Walsh phase
//       phase = (mu & x_i) xor (nu & a_i) xor (nu & r).
//   The matrix entry receives +1 or -1 depending on that phase.
// ============================================================================

static LinearLocalKernel2State build_linear_local_kernel_from_one_bit_enumeration(
    int addend_bit,
    int mu_control_bit,
    int nu_control_bit)
{
    LinearLocalKernel2State local_kernel{};
    for (int source_carry_slice = 0; source_carry_slice <= 1; ++source_carry_slice) {
        for (int variable_bit = 0; variable_bit <= 1; ++variable_bit) {
            int target_carry_slice = majority_bit(variable_bit, addend_bit, source_carry_slice);
            int linear_phase_bit = (mu_control_bit & variable_bit)
                                 ^ (nu_control_bit & addend_bit)
                                 ^ (nu_control_bit & source_carry_slice);
            local_kernel[source_carry_slice][target_carry_slice] += linear_phase_bit ? -1 : 1;
        }
    }
    return local_kernel;
}

// ============================================================================
// Section 4. Small matrix utilities
// ============================================================================

static bool matrices_equal(const DifferentialLocalKernel4State& left,
                           const DifferentialLocalKernel4State& right) {
    for (int row = 0; row < 4; ++row) {
        for (int col = 0; col < 4; ++col) {
            if (left[row][col] != right[row][col]) {
                return false;
            }
        }
    }
    return true;
}

static bool matrices_equal(const LinearLocalKernel2State& left,
                           const LinearLocalKernel2State& right) {
    for (int row = 0; row < 2; ++row) {
        for (int col = 0; col < 2; ++col) {
            if (left[row][col] != right[row][col]) {
                return false;
            }
        }
    }
    return true;
}

static void print_matrix(const DifferentialLocalKernel4State& matrix) {
    for (const auto& row : matrix) {
        std::cout << "[";
        for (int col = 0; col < 4; ++col) {
            if (col) std::cout << ", ";
            std::cout << row[col];
        }
        std::cout << "]\n";
    }
}

static void print_matrix(const LinearLocalKernel2State& matrix) {
    for (const auto& row : matrix) {
        std::cout << "[";
        for (int col = 0; col < 2; ++col) {
            if (col) std::cout << ", ";
            std::cout << row[col];
        }
        std::cout << "]\n";
    }
}

// ============================================================================
// Section 5. Main appendix-kernel audit
//
// The expected matrices below are exactly the appendix claims.  The loops below
// do not derive new theory; they only confirm that the appendix kernels are the
// direct one-bit enumeration of the carry laws.
// ============================================================================

int main() {
    const std::array<DifferentialLocalKernel4State,8> expected_differential_local_kernels = {{
        {{{2,0,0,0},{0,0,0,0},{0,0,0,0},{1,0,0,1}}}, // 000
        {{{0,0,0,0},{1,1,0,0},{1,0,1,0},{0,0,0,0}}}, // 001
        {{{0,0,0,0},{1,1,0,0},{1,0,1,0},{0,0,0,0}}}, // 010
        {{{2,0,0,0},{0,0,0,0},{0,0,0,0},{0,1,1,0}}}, // 011
        {{{1,0,0,1},{0,0,0,0},{0,0,0,0},{0,0,0,2}}}, // 100
        {{{0,0,0,0},{0,1,0,1},{0,0,1,1},{0,0,0,0}}}, // 101
        {{{0,0,0,0},{0,1,0,1},{0,0,1,1},{0,0,0,0}}}, // 110
        {{{0,1,1,0},{0,0,0,0},{0,0,0,0},{0,0,0,2}}}  // 111
    }};

    const std::array<LinearLocalKernel2State,8> expected_linear_local_kernels = {{
        {{{2,0},{1,1}}},   // 000
        {{{2,0},{-1,-1}}}, // 001
        {{{0,0},{1,-1}}},  // 010
        {{{0,0},{-1,1}}},  // 011
        {{{1,1},{0,2}}},   // 100
        {{{-1,-1},{0,2}}}, // 101
        {{{1,-1},{0,0}}},  // 110
        {{{-1,1},{0,0}}}   // 111
    }};

    bool all_checks_passed = true;

    std::cout << "Appendix B audit: differential 4-state local kernels\n";
    for (int key = 0; key < 8; ++key) {
        int addend_bit            = (key >> 2) & 1;
        int input_difference_bit  = (key >> 1) & 1;
        int output_difference_bit =  key       & 1;

        DifferentialLocalKernel4State reproduced_kernel =
            build_differential_local_kernel_from_one_bit_enumeration(
                addend_bit,
                input_difference_bit,
                output_difference_bit);

        bool matches_appendix = matrices_equal(reproduced_kernel, expected_differential_local_kernels[key]);
        std::cout << "M^D_" << addend_bit << input_difference_bit << output_difference_bit
                  << (matches_appendix ? "  [OK]\n" : "  [MISMATCH]\n");
        if (!matches_appendix) {
            print_matrix(reproduced_kernel);
            all_checks_passed = false;
        }
    }

    std::cout << "\nAppendix C audit: linear 2-state local kernels\n";
    for (int key = 0; key < 8; ++key) {
        int addend_bit     = (key >> 2) & 1;
        int mu_control_bit = (key >> 1) & 1;
        int nu_control_bit =  key       & 1;

        LinearLocalKernel2State reproduced_kernel =
            build_linear_local_kernel_from_one_bit_enumeration(
                addend_bit,
                mu_control_bit,
                nu_control_bit);

        bool matches_appendix = matrices_equal(reproduced_kernel, expected_linear_local_kernels[key]);
        std::cout << "M^L_" << addend_bit << mu_control_bit << nu_control_bit
                  << (matches_appendix ? "  [OK]\n" : "  [MISMATCH]\n");
        if (!matches_appendix) {
            print_matrix(reproduced_kernel);
            all_checks_passed = false;
        }
    }

    if (!all_checks_passed) {
        return 1;
    }

    std::cout << "\nAll appendix local matrices reproduced from one-bit enumeration.\n";
    return 0;
}
