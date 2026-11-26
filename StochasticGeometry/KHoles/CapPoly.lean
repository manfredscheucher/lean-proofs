/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.CapDefs

/-!
# The polynomials `P_n` and the series coefficients `fc` (stage 3, §2.2)

Pure algebra about `pc n j = [s^j] P_n` (with `P_n(s) = ∏_{i<n} (s + i(i+1))`) and
`fc j n = pc n j / ((n+1)! n!)`: vanishing above the degree, the coefficient expansion of
`capPoly`, and the recursion of `fc` in `n` (`fc_succ_succ`), obtained by telescoping the
one-step identity `(N+1)(N+2) fc (j+1) (N+1) = fc j N + N(N+1) fc (j+1) N`.
-/

open Finset

namespace KHoles

/-- `P_n` has degree `n`: its coefficients above `n` vanish. -/
theorem pc_eq_zero_of_lt {n j : ℕ} (h : n < j) : pc n j = 0 := by
  induction n generalizing j with
  | zero =>
    simp [pc_zero, Nat.pos_iff_ne_zero.mp h]
  | succ n ih =>
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [pc_succ_succ, ih (by omega), ih (by omega)]
    simp

/-- The constant coefficient of `P_{n+1}` vanishes (the factor `i = 0` is `s`). -/
theorem pc_succ_zero_eq_zero (n : ℕ) : pc (n + 1) 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pc_succ_zero, ih, mul_zero]

/-- Coefficient expansion `P_n(s) = Σ_{j ≤ n} pc n j · s^j`. -/
theorem capPoly_eq_sum (n : ℕ) (s : ℝ) :
    capPoly n s = ∑ j ∈ range (n + 1), (pc n j : ℝ) * s ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : (pc n (n + 1) : ℝ) = 0 := by
      exact_mod_cast pc_eq_zero_of_lt (Nat.lt_succ_self n)
    have k1 : ∑ j ∈ range (n + 1 + 1), (pc n j : ℝ) * s ^ j
        = ∑ j ∈ range (n + 1), (pc n j : ℝ) * s ^ j := by
      rw [Finset.sum_range_succ, h0, zero_mul, add_zero]
    have k2 : ∑ j ∈ range (n + 1 + 1), (pc n j : ℝ) * s ^ j
        = ∑ j ∈ range (n + 1), (pc n (j + 1) : ℝ) * s ^ (j + 1) + pc n 0 := by
      rw [Finset.sum_range_succ', pow_zero, mul_one]
    have hs : ∑ j ∈ range (n + 1), (pc n j : ℝ) * s ^ (j + 1)
        = s * ∑ j ∈ range (n + 1), (pc n j : ℝ) * s ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hcA : ∑ j ∈ range (n + 1), ((n : ℝ) * (n + 1) * pc n (j + 1)) * s ^ (j + 1)
        = (n : ℝ) * (n + 1) * ∑ j ∈ range (n + 1), (pc n (j + 1) : ℝ) * s ^ (j + 1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [capPoly_succ, ih, Finset.sum_range_succ' _ (n + 1)]
    simp only [pc_succ_succ, pc_succ_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      add_mul, Finset.sum_add_distrib, pow_zero, mul_one]
    rw [hs, hcA]
    linear_combination ((n : ℝ) * (n + 1)) * (k1.symm.trans k2)

theorem fc_zero_left (n : ℕ) : fc 0 n = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [fc]
  | succ n => rw [fc, pc_succ_zero_eq_zero]; simp

theorem fc_succ_zero (j : ℕ) : fc (j + 1) 0 = 0 := by
  simp [fc]

theorem fc_nonneg (j n : ℕ) : 0 ≤ fc j n := by
  unfold fc
  positivity

/-- One-step identity `(N+1)(N+2) fc (j+1) (N+1) = fc j N + N(N+1) fc (j+1) N`. -/
theorem fc_succ_succ_step (j N : ℕ) :
    ((N : ℝ) + 1) * (N + 2) * fc (j + 1) (N + 1)
      = fc j N + (N : ℝ) * (N + 1) * fc (j + 1) N := by
  simp only [fc, pc_succ_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Telescoped form: `N(N+1) fc (j+1) N = Σ_{n<N} fc j n`. -/
theorem fc_succ_telescope (j N : ℕ) :
    (N : ℝ) * (N + 1) * fc (j + 1) N = ∑ n ∈ range N, fc j n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, add_comm _ (fc j N), ← fc_succ_succ_step]
    push_cast
    ring

theorem fc_succ_succ (j N : ℕ) :
    fc (j + 1) (N + 1) = (∑ n ∈ range (N + 1), fc j n) / ((N + 1) * (N + 2)) := by
  rw [← fc_succ_telescope, eq_div_iff (by positivity)]
  push_cast
  ring

end KHoles
