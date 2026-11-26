/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
/-
Closed-form constants for the expected number of k-holes in random planar
point sets (see the unpublished draft on the closed form).

  a m  = 2^m/(m+1) * Σ_{j ≤ m/2} (-1)^j π^{2j}/(2j)! * C(2m-2j, m)       (cap numbers)
  C k  = 2^{k-2}/k * Σ_{1 ≤ j ≤ k/2} (-1)^{j+1} (2π)^{2j-2}/(2j-1)! * C(2k-2j-1, k-1)

This file only contains the finite-sum definitions and checks that the two
descriptions of C k agree for small k (convolution of cap numbers vs. direct
formula) for k = 3, ..., 10, plus the explicit values a 0 .. a 8 and C 3 .. C 10.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Real Finset

namespace KHoles

/-- Cap numbers `a m` as polynomials in `π²`. -/
noncomputable def a (m : ℕ) : ℝ :=
  2 ^ m / (m + 1) *
    ∑ j ∈ range (m / 2 + 1), (-1 : ℝ) ^ j * π ^ (2 * j) / (2 * j).factorial * (2 * m - 2 * j).choose m

/-- The k-hole constants `C k` (direct formula). -/
noncomputable def C (k : ℕ) : ℝ :=
  2 ^ (k - 2) / k *
    ∑ j ∈ Icc 1 (k / 2),
      (-1 : ℝ) ^ (j + 1) * (2 * π) ^ (2 * j - 2) / (2 * j - 1).factorial * (2 * k - 2 * j - 1).choose (k - 1)

/-- The k-hole constants via the cap numbers: `½ Σ_m a_m a_{k-2-m}`. -/
noncomputable def Cconv (k : ℕ) : ℝ :=
  (1 / 2) * ∑ m ∈ range (k - 1), a m * a (k - 2 - m)

/-- Cap number `a 0`. -/
lemma a_zero : a 0 = 1 := by
  norm_num [a, sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]

/-- Cap number `a 1`. -/
lemma a_one : a 1 = 2 := by
  norm_num [a, sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]

/-- Cap number `a 2`. -/
lemma a_two : a 2 = 8 - 2 / 3 * π ^ 2 := by
  norm_num [a, sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- Cap number `a 3`. -/
lemma a_three : a 3 = 40 - 4 * π ^ 2 := by
  norm_num [a, sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- Cap number `a 4`. -/
lemma a_four : a 4 = 224 - 24 * π ^ 2 + 2 / 15 * π ^ 4 := by
  norm_num [a, sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- Cap number `a 5`. -/
lemma a_five : a 5 = 1344 - 448 / 3 * π ^ 2 + 4 / 3 * π ^ 4 := by
  norm_num [a, sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- Cap number `a 6`. -/
lemma a_six : a 6 = 8448 - 960 * π ^ 2 + 32 / 3 * π ^ 4 - 4 / 315 * π ^ 6 := by
  norm_num [a, sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- Cap number `a 7`. -/
lemma a_seven : a 7 = 54912 - 6336 * π ^ 2 + 80 * π ^ 4 - 8 / 45 * π ^ 6 := by
  norm_num [a, sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- Cap number `a 8`. -/
lemma a_eight : a 8 = 366080 - 128128 / 3 * π ^ 2 + 1760 / 3 * π ^ 4 - 16 / 9 * π ^ 6 + 2 / 2835 * π ^ 8 := by
  norm_num [a, sum_range_succ, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- k-hole constant `C 3`. -/
lemma C_three : C 3 = 2 := by
  norm_num [C, Finset.sum_Icc_succ_top, Nat.choose_eq_descFactorial_div_factorial]

/-- k-hole constant `C 4`. -/
lemma C_four : C 4 = 10 - 2 / 3 * π ^ 2 := by
  norm_num [C, Finset.sum_Icc_succ_top, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- k-hole constant `C 5`. -/
lemma C_five : C 5 = 56 - 16 / 3 * π ^ 2 := by
  norm_num [C, Finset.sum_Icc_succ_top, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- k-hole constant `C 6`. -/
lemma C_six : C 6 = 336 - 112 / 3 * π ^ 2 + 16 / 45 * π ^ 4 := by
  norm_num [C, Finset.sum_Icc_succ_top, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- k-hole constant `C 7`. -/
lemma C_seven : C 7 = 2112 - 256 * π ^ 2 + 64 / 15 * π ^ 4 := by
  norm_num [C, Finset.sum_Icc_succ_top, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- k-hole constant `C 8`. -/
lemma C_eight : C 8 = 13728 - 1760 * π ^ 2 + 192 / 5 * π ^ 4 - 32 / 315 * π ^ 6 := by
  norm_num [C, Finset.sum_Icc_succ_top, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- k-hole constant `C 9`. -/
lemma C_nine : C 9 = 91520 - 36608 / 3 * π ^ 2 + 2816 / 9 * π ^ 4 - 512 / 315 * π ^ 6 := by
  norm_num [C, Finset.sum_Icc_succ_top, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- k-hole constant `C 10`. -/
lemma C_ten : C 10 = 622336 - 256256 / 3 * π ^ 2 + 36608 / 15 * π ^ 4 - 5632 / 315 * π ^ 6 + 256 / 14175 * π ^ 8 := by
  norm_num [C, Finset.sum_Icc_succ_top, Nat.choose_eq_descFactorial_div_factorial]
  ring

/-- The two descriptions agree for k = 3, …, 10 (polynomial identities in π²). -/
theorem Cconv_eq_C : ∀ k ∈ Icc 3 10, Cconv k = C k := by
  intro k hk
  obtain ⟨h3, h10⟩ := mem_Icc.mp hk
  interval_cases k
  · norm_num [Cconv, sum_range_succ, a_zero, a_one, C_three]
  · norm_num [Cconv, sum_range_succ, a_zero, a_one, a_two, C_four]
    ring
  · norm_num [Cconv, sum_range_succ, a_zero, a_one, a_two, a_three, C_five]
    ring
  · norm_num [Cconv, sum_range_succ, a_zero, a_one, a_two, a_three, a_four, C_six]
    ring
  · norm_num [Cconv, sum_range_succ, a_zero, a_one, a_two, a_three, a_four, a_five, C_seven]
    ring
  · norm_num [Cconv, sum_range_succ, a_zero, a_one, a_two, a_three, a_four, a_five, a_six, C_eight]
    ring
  · norm_num [Cconv, sum_range_succ, a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, C_nine]
    ring
  · norm_num [Cconv, sum_range_succ, a_zero, a_one, a_two, a_three, a_four, a_five, a_six, a_seven, a_eight, C_ten]
    ring


end KHoles
