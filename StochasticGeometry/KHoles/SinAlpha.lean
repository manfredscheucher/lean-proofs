/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.CapDefs
import KHoles.AlphaSeries
import KHoles.CatalanPower
import KHoles.Constants
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# `sin(π α(s))` as a power series in `s` (step iv, part 2)

For `0 < s < 1/4` we expand `sin(π α) = Σ_j (-1)^j π^{2j+1} α^{2j+1} / (2j+1)!` and
`α^{2j+1} = Σ_n κ(2j+1, n) s^n` (`hasSum_kappa_pow`). The double series over `(j, n)`
converges absolutely (its absolute values sum to `sinh(π α)`), so the order of summation can
be swapped. For fixed `n` the inner sum over `j` is finite (`κ(r, n) = 0` for `n < r`), it
vanishes for `n = 0`, and for `n = m + 1` it equals `π · a m / 2^m` by the coefficient formula
`κ(2j+1, m+1) = (2j+1)/(m+1) · C(2m-2j, m)` (`coeff_X_mul_catalanSeries_pow`). Dividing by
`π s` gives `hasSum_a_div_pow`. The bound `abs_a_div_le` follows from the finite-sum
definition of `a m`, `C(2m-2j, m) ≤ 4^m` and `Σ_j π^{2j}/(2j)! ≤ e^π`.
-/

open Real Finset

namespace KHoles

/-- `κ(2j+1, m+1) = (2j+1)/(m+1) · C(2m-2j, m)` for `j ≤ m/2`. -/
theorem kappa_odd_succ {m j : ℕ} (hj : j ≤ m / 2) :
    (kappa (2 * j + 1) (m + 1) : ℝ) = (2 * j + 1) / (m + 1) * ((2 * m - 2 * j).choose m : ℝ) := by
  have h := coeff_X_mul_catalanSeries_pow (2 * j + 1) (m + 1) (by omega) (by omega)
  have e1 : 2 * (m + 1) - (2 * j + 1) - 1 = 2 * m - 2 * j := by omega
  rw [e1, Nat.add_sub_cancel, ← kappa_def] at h
  have h' : ((m + 1 : ℕ) : ℝ) * (kappa (2 * j + 1) (m + 1) : ℝ) =
      ((2 * j + 1 : ℕ) : ℝ) * ((2 * m - 2 * j).choose m : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
  linear_combination h'

/-- The finite coefficient sum: `Σ_{j ≤ m/2} (-1)^j π^{2j+1}/(2j+1)! κ(2j+1, m+1) = π a_m / 2^m`. -/
theorem sum_sin_kappa (m : ℕ) :
    ∑ j ∈ range (m / 2 + 1), (-1 : ℝ) ^ j * π ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) *
      (kappa (2 * j + 1) (m + 1) : ℝ) = π * (a m / 2 ^ m) := by
  have hrhs : π * (a m / 2 ^ m) = ∑ j ∈ range (m / 2 + 1), π / (m + 1) *
      ((-1 : ℝ) ^ j * π ^ (2 * j) / ((2 * j).factorial : ℝ) * ((2 * m - 2 * j).choose m : ℝ)) := by
    rw [← mul_sum, a]
    field_simp
  rw [hrhs]
  refine sum_congr rfl (fun j hj => ?_)
  have hj' : j ≤ m / 2 := by rw [mem_range] at hj; omega
  rw [kappa_odd_succ hj', Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- `Σ_{j<N} x^{2j}/(2j)! ≤ Σ_{k<2N} x^k/k!` for `x ≥ 0`. -/
theorem sum_even_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ∑ j ∈ range N, x ^ (2 * j) / ((2 * j).factorial : ℝ) ≤
      ∑ k ∈ range (2 * N), x ^ k / (k.factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ]
    have : 0 ≤ x ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) := by positivity
    linarith

theorem abs_a_div_le (m : ℕ) : |a m / 2 ^ m| ≤ Real.exp π * 4 ^ m := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hchoose : ∀ j : ℕ, ((2 * m - 2 * j).choose m : ℝ) ≤ 4 ^ m := by
    intro j
    have h : (2 * m - 2 * j).choose m ≤ 4 ^ m :=
      (Nat.choose_le_two_pow _ _).trans (by
        rw [show 4 ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num]
        exact Nat.pow_le_pow_right (by norm_num) (by omega))
    exact_mod_cast h
  have hterm : ∀ j : ℕ, |(-1 : ℝ) ^ j * π ^ (2 * j) / ((2 * j).factorial : ℝ) *
      ((2 * m - 2 * j).choose m : ℝ)| ≤ π ^ (2 * j) / ((2 * j).factorial : ℝ) * 4 ^ m := by
    intro j
    rw [abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ π ^ (2 * j)), Nat.abs_cast, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (hchoose j) (by positivity)
  calc |a m / 2 ^ m|
      = |∑ j ∈ range (m / 2 + 1), (-1 : ℝ) ^ j * π ^ (2 * j) / ((2 * j).factorial : ℝ) *
          ((2 * m - 2 * j).choose m : ℝ)| / (m + 1) := by
        rw [a, ← abs_of_pos hm, ← abs_div, abs_of_pos hm]
        congr 1
        field_simp
    _ ≤ |∑ j ∈ range (m / 2 + 1), (-1 : ℝ) ^ j * π ^ (2 * j) / ((2 * j).factorial : ℝ) *
          ((2 * m - 2 * j).choose m : ℝ)| := div_le_self (abs_nonneg _) (by linarith [m.cast_nonneg (α := ℝ)])
    _ ≤ ∑ j ∈ range (m / 2 + 1), |(-1 : ℝ) ^ j * π ^ (2 * j) / ((2 * j).factorial : ℝ) *
          ((2 * m - 2 * j).choose m : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (m / 2 + 1), π ^ (2 * j) / ((2 * j).factorial : ℝ) * 4 ^ m :=
        sum_le_sum (fun j _ => hterm j)
    _ = (∑ j ∈ range (m / 2 + 1), π ^ (2 * j) / ((2 * j).factorial : ℝ)) * 4 ^ m :=
        (sum_mul _ _ _).symm
    _ ≤ Real.exp π * 4 ^ m :=
        mul_le_mul_of_nonneg_right
          ((sum_even_le pi_pos.le _).trans (Real.sum_le_exp_of_nonneg pi_pos.le _))
          (by positivity)

theorem hasSum_a_div_pow {s : ℝ} (h0 : 0 < s) (h1 : s < 1 / 4) :
    HasSum (fun m => a m / 2 ^ m * s ^ m) (Real.sin (π * alphaFn s) / (π * s)) := by
  set α := alphaFn s with hα
  have hα0 : 0 ≤ α := (alphaFn_mem h0 h1).1.le
  -- the double series over `(j, n)` and its absolute values
  set f : ℕ × ℕ → ℝ := fun p => (-1 : ℝ) ^ p.1 * π ^ (2 * p.1 + 1) /
    ((2 * p.1 + 1).factorial : ℝ) * ((kappa (2 * p.1 + 1) p.2 : ℝ) * s ^ p.2) with hf
  set g : ℕ × ℕ → ℝ := fun p => π ^ (2 * p.1 + 1) /
    ((2 * p.1 + 1).factorial : ℝ) * ((kappa (2 * p.1 + 1) p.2 : ℝ) * s ^ p.2) with hg
  have hg0 : 0 ≤ g := fun p => by
    simp only [hg, Pi.zero_apply]
    have := pi_pos
    positivity
  have hfg : ∀ p, ‖f p‖ = g p := by
    intro p
    have e : f p = (-1 : ℝ) ^ p.1 * g p := by simp only [hf, hg]; ring
    rw [e, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (hg0 p)]
  have hgj : ∀ j : ℕ, HasSum (fun n => g (j, n))
      (π ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) * α ^ (2 * j + 1)) :=
    fun j => (hasSum_kappa_pow (2 * j + 1) h0.le h1).mul_left _
  have hgs : Summable g := by
    refine (summable_prod_of_nonneg hg0).mpr ⟨fun j => (hgj j).summable, ?_⟩
    refine (Real.hasSum_sinh (π * α)).summable.congr (fun j => ?_)
    rw [(hgj j).tsum_eq, mul_pow]
    ring
  have hfs : Summable f := Summable.of_norm (hgs.congr fun p => (hfg p).symm)
  -- summing over `n` first for fixed `j` gives the sine series
  have hfj : ∀ j : ℕ, HasSum (fun n => f (j, n))
      ((-1 : ℝ) ^ j * π ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) * α ^ (2 * j + 1)) :=
    fun j => (hasSum_kappa_pow (2 * j + 1) h0.le h1).mul_left _
  have hT : ∑' p, f p = Real.sin (π * α) := by
    refine (hfs.hasSum.prod_fiberwise hfj).unique ?_
    convert Real.hasSum_sin (π * α) using 1
    funext j
    rw [mul_pow]
    ring
  -- summing over `j` first for fixed `n`: a finite sum
  have hfin : ∀ n : ℕ, ∀ j ∉ range n, f (j, n) = 0 := by
    intro n j hj
    rw [mem_range, not_lt] at hj
    simp only [hf]
    rw [kappa_eq_zero_of_lt (by omega)]
    simp
  have hswap : HasSum (fun p : ℕ × ℕ => f p.swap) (Real.sin (π * α)) := by
    rw [← hT]
    exact (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hfs.hasSum
  have hG : HasSum (fun n => ∑' j, f (j, n)) (Real.sin (π * α)) :=
    hswap.prod_fiberwise (fun n => (hasSum_sum_of_ne_finset_zero (hfin n)).summable.hasSum)
  have hG0 : ∑' j, f (j, 0) = 0 := by
    rw [tsum_eq_sum (s := range 0) (hfin 0)]
    simp
  have hGs : ∀ m : ℕ, ∑' j, f (j, m + 1) = π * s * (a m / 2 ^ m * s ^ m) := by
    intro m
    have hz : ∀ j ∉ range (m / 2 + 1), f (j, m + 1) = 0 := by
      intro j hj
      rw [mem_range, not_lt] at hj
      simp only [hf]
      rw [kappa_eq_zero_of_lt (by omega)]
      simp
    rw [tsum_eq_sum hz]
    simp only [hf, ← mul_assoc]
    rw [← sum_mul, sum_sin_kappa]
    ring
  have hshift := (hasSum_nat_add_iff' 1).mpr hG
  rw [sum_range_one, hG0, sub_zero] at hshift
  simp_rw [hGs] at hshift
  have hps : π * s ≠ 0 := by have := pi_pos; positivity
  have h := hshift.div_const (π * s)
  have e : (fun m => π * s * (a m / 2 ^ m * s ^ m) / (π * s)) = fun m => a m / 2 ^ m * s ^ m := by
    funext m
    field_simp
  rwa [e] at h

end KHoles
