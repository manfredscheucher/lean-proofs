/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.CapDefs
import KHoles.CatalanPower
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Choose.Central

/-!
# The analytic Catalan function `alphaFn` (step iv, part 1)

For `0 ≤ s < 1/4` the series `alphaFn s = Σ κ(1,n) s^n` converges absolutely
(`κ(1,n) = Cat_{n-1} ≤ 4^n`), its `r`-th power is `Σ κ(r,n) s^n` (Cauchy product,
induction on `r`), and the formal identity `X c = X + (X c)^2` gives
`alphaFn s = s + alphaFn s ^ 2`, hence `alphaFn s * (1 - alphaFn s) = s` and
`0 < alphaFn s < 1` for `0 < s < 1/4`.
-/

open PowerSeries Finset

namespace KHoles

/-- `κ(r,n) = 0` for `n < r`, since `(X c)^r = X^r c^r`. -/
theorem kappa_eq_zero_of_lt {r n : ℕ} (h : n < r) : kappa r n = 0 := by
  unfold kappa
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

/-- `κ(1,0) = 0` and `κ(1,n+1) = Cat_n`. -/
theorem kappa_one_succ (n : ℕ) : kappa 1 (n + 1) = catalan n := by
  unfold kappa
  rw [pow_one, coeff_succ_X_mul, catalanSeries_coeff]

theorem kappa_one_le (n : ℕ) : (kappa 1 n : ℝ) ≤ 4 ^ n := by
  rcases n with _ | n
  · rw [kappa_eq_zero_of_lt (by omega)]; simp
  · rw [kappa_one_succ]
    have h1 : catalan n ≤ n.centralBinom := by
      rw [← succ_mul_catalan_eq_centralBinom]
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    have h2 : catalan n ≤ 4 ^ (n + 1) :=
      h1.trans ((Nat.centralBinom_le_four_pow n).trans (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_succ n)))
    exact_mod_cast h2

/-- Absolute convergence of `Σ κ(1,n) s^n` for `0 ≤ s < 1/4`. -/
theorem summable_kappa_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1 / 4) :
    Summable (fun n => (kappa 1 n : ℝ) * s ^ n) := by
  have hg : Summable (fun n : ℕ => (4 * s) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by linarith)
  refine hg.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (kappa_one_le n) (by positivity)

/-- Cauchy-product form of the coefficients: `κ(r+1,n) s^n = Σ_{k+l=n} κ(r,k) s^k κ(1,l) s^l`. -/
theorem kappa_succ_mul_pow (r n : ℕ) (s : ℝ) :
    (kappa (r + 1) n : ℝ) * s ^ n =
      ∑ kl ∈ antidiagonal n, ((kappa r kl.1 : ℝ) * s ^ kl.1) * ((kappa 1 kl.2 : ℝ) * s ^ kl.2) := by
  have h : kappa (r + 1) n = ∑ kl ∈ antidiagonal n, kappa r kl.1 * kappa 1 kl.2 := by
    unfold kappa
    rw [pow_succ, coeff_mul, pow_one]
  rw [h, Nat.cast_sum, sum_mul]
  refine sum_congr rfl (fun kl hkl => ?_)
  rw [mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  push_cast
  ring

theorem hasSum_kappa_pow (r : ℕ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1 / 4) :
    HasSum (fun n => (kappa r n : ℝ) * s ^ n) (alphaFn s ^ r) := by
  have hs1 := summable_kappa_one h0 h1
  induction r with
  | zero =>
    have e : (fun n => (kappa 0 n : ℝ) * s ^ n) = fun n => if n = 0 then 1 else 0 := by
      funext n
      unfold kappa
      rw [pow_zero, coeff_one]
      split_ifs with hn <;> simp [hn]
    rw [e, pow_zero]
    exact hasSum_ite_eq 0 1
  | succ r ih =>
    have nn : ∀ (q n : ℕ), ‖(kappa q n : ℝ) * s ^ n‖ = (kappa q n : ℝ) * s ^ n :=
      fun q n => Real.norm_of_nonneg (by positivity)
    have hf : Summable fun n => ‖(kappa r n : ℝ) * s ^ n‖ := by
      simp_rw [nn]; exact ih.summable
    have hg : Summable fun n => ‖(kappa 1 n : ℝ) * s ^ n‖ := by
      simp_rw [nn]; exact hs1
    have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm
    have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
    simp_rw [← kappa_succ_mul_pow] at hsum heq
    rw [ih.tsum_eq] at heq
    have hα : alphaFn s = ∑' n, (kappa 1 n : ℝ) * s ^ n := rfl
    rw [← hα, ← pow_succ] at heq
    rw [heq]
    exact hsum.hasSum

theorem alphaFn_eq {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1 / 4) : alphaFn s = s + alphaFn s ^ 2 := by
  have hcoeff : ∀ n, (kappa 1 n : ℝ) * s ^ n =
      (if n = 1 then s else 0) + (kappa 2 n : ℝ) * s ^ n := by
    intro n
    have h : kappa 1 n = (if n = 1 then 1 else 0) + kappa 2 n := by
      unfold kappa
      rw [pow_one]
      conv_lhs => rw [X_mul_catalanSeries_eq]
      rw [map_add, coeff_X]
    rw [h]
    split_ifs with hn <;> simp [hn, add_mul]
  have hA : HasSum (fun n => (kappa 1 n : ℝ) * s ^ n) (s + alphaFn s ^ 2) := by
    simp_rw [hcoeff]
    exact (hasSum_ite_eq 1 s).add (hasSum_kappa_pow 2 h0 h1)
  have hB := hasSum_kappa_pow 1 h0 h1
  rw [pow_one] at hB
  exact hB.unique hA

theorem alphaFn_mul {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1 / 4) : alphaFn s * (1 - alphaFn s) = s := by
  have h := alphaFn_eq h0 h1
  linear_combination h

theorem alphaFn_mem {s : ℝ} (h0 : 0 < s) (h1 : s < 1 / 4) : 0 < alphaFn s ∧ alphaFn s < 1 := by
  have h := alphaFn_eq h0.le h1
  have hpos : 0 < alphaFn s := by nlinarith [sq_nonneg (alphaFn s)]
  refine ⟨hpos, ?_⟩
  have hm := alphaFn_mul h0.le h1
  by_contra hc
  push Not at hc
  nlinarith

end KHoles
