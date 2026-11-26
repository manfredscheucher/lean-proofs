/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.CapDefs
import KHoles.CapPoly
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Series expansion of the Volterra iteration (stage 3, step ii)

For `0 ≤ y ≤ 1`: `F j y = Σ_{n ≥ 0} fc j n · y^(n+1)` (in `ℝ≥0∞`). Proof by induction on
`j`: expand `1/(1-t)` as a geometric series, integrate termwise (`lintegral_tsum`), use
`∫_0^y t^p (y-t) dt = y^(p+2)/((p+1)(p+2))`, regroup the double sum along `N = n + k`
and apply the recursion `fc_succ_succ`.
-/

open MeasureTheory Set Finset
open scoped ENNReal

namespace KHoles

/-- `∫_0^y t^p (y - t) dt = y^(p+2) / ((p+1)(p+2))` (as an interval integral). -/
theorem intervalIntegral_pow_mul_sub (p : ℕ) (y : ℝ) :
    ∫ t in (0 : ℝ)..y, t ^ p * (y - t) = y ^ (p + 2) / (((p : ℝ) + 1) * ((p : ℝ) + 2)) := by
  have hfun : (fun t : ℝ => t ^ p * (y - t)) = fun t => y * t ^ p - t ^ (p + 1) := by
    funext t; ring
  rw [hfun, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    integral_pow, integral_pow]
  · have h1 : ((p : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((p : ℝ) + 2) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · exact ((continuous_pow p).const_mul y).intervalIntegrable _ _
  · exact (continuous_pow (p + 1)).intervalIntegrable _ _

/-- `∫⁻ t in (0,y), t^p (y - t) = y^(p+2) / ((p+1)(p+2))` for `0 ≤ y`. -/
theorem lintegral_pow_mul_sub (p : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ∫⁻ t in Ioo 0 y, ENNReal.ofReal (t ^ p * (y - t))
      = ENNReal.ofReal (y ^ (p + 2) / (((p : ℝ) + 1) * ((p : ℝ) + 2))) := by
  have hcont : Continuous fun t : ℝ => t ^ p * (y - t) := by fun_prop
  have hint : IntegrableOn (fun t : ℝ => t ^ p * (y - t)) (Ioo 0 y) :=
    (hcont.continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 y)] fun t : ℝ => t ^ p * (y - t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg (pow_nonneg ht.1.le _) (sub_nonneg.2 ht.2.le)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hy, intervalIntegral_pow_mul_sub]

/-- Pointwise expansion of the Volterra integrand: for `0 < t < y ≤ 1`,
`t^(n+1) (y-t)/(t(1-t)) = Σ_k t^(n+k) (y-t)`. -/
theorem ofReal_mul_kernel_eq_tsum (c : ℝ) (hc : 0 ≤ c) (n : ℕ) {y t : ℝ} (ht0 : 0 < t)
    (hty : t < y) (hy1 : y ≤ 1) :
    ENNReal.ofReal (c * t ^ (n + 1)) * ENNReal.ofReal ((y - t) / (t * (1 - t)))
      = ∑' k, ENNReal.ofReal c * ENNReal.ofReal (t ^ (n + k) * (y - t)) := by
  have ht1 : t < 1 := lt_of_lt_of_le hty hy1
  have hgeo := summable_geometric_of_lt_one ht0.le ht1
  have hsum : Summable fun k : ℕ => c * (t ^ (n + k) * (y - t)) := by
    have := hgeo.mul_left (c * t ^ n * (y - t))
    refine this.congr fun k => ?_
    rw [pow_add]; ring
  have hreal : c * t ^ (n + 1) * ((y - t) / (t * (1 - t)))
      = ∑' k : ℕ, c * (t ^ (n + k) * (y - t)) := by
    have h1 : ∑' k : ℕ, c * (t ^ (n + k) * (y - t))
        = c * t ^ n * (y - t) * ∑' k : ℕ, t ^ k := by
      rw [← tsum_mul_left]
      congr 1; funext k; rw [pow_add]; ring
    rw [h1, tsum_geometric_of_lt_one ht0.le ht1]
    have : (1 - t) ≠ 0 := by linarith
    field_simp
    ring
  have hnn : ∀ k : ℕ, 0 ≤ c * (t ^ (n + k) * (y - t)) := fun k =>
    mul_nonneg hc (mul_nonneg (pow_nonneg ht0.le _) (sub_nonneg.2 hty.le))
  rw [← ENNReal.ofReal_mul (mul_nonneg hc (pow_nonneg ht0.le _)), hreal,
    ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  congr 1; funext k
  rw [ENNReal.ofReal_mul hc]

/-- Regrouping a double `ℝ≥0∞` series along the anti-diagonals `N = n + k`. -/
theorem tsum_tsum_add_eq (a g : ℕ → ℝ≥0∞) :
    ∑' n, ∑' k, a n * g (n + k) = ∑' N, (∑ n ∈ range (N + 1), a n) * g N := by
  classical
  have hin : ∀ n, ∑' k, a n * g (n + k)
      = ∑' N, if n ≤ N then a n * g N else 0 := by
    intro n
    have hinj : Function.Injective fun k : ℕ => n + k := fun _ _ h => by simpa using h
    rw [← hinj.tsum_eq (f := fun N => if n ≤ N then a n * g N else 0)]
    · simp
    · intro N hN
      have : n ≤ N := by
        by_contra h; exact hN (by simp [h])
      exact ⟨N - n, by simp; omega⟩
  have hout : ∀ N, (∑ n ∈ range (N + 1), a n) * g N
      = ∑' n, if n ≤ N then a n * g N else 0 := by
    intro N
    rw [Finset.sum_mul, tsum_eq_sum (s := range (N + 1))]
    · refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))]
    · intro n hn
      rw [if_neg]
      simpa [Nat.lt_succ_iff] using hn
  simp_rw [hin, hout]
  exact ENNReal.tsum_comm

/-- Series expansion `F_j(y) = Σ_n fc j n · y^(n+1)` for `0 ≤ y ≤ 1`. -/
theorem F_eq_tsum (j : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    F j y = ∑' n, ENNReal.ofReal (fc j n * y ^ (n + 1)) := by
  induction j generalizing y with
  | zero =>
    rw [F_zero, tsum_eq_single 0]
    · simp [fc_zero_left]
    · intro n hn; simp [fc_zero_left, hn]
  | succ j ih =>
    -- pointwise expansion of the integrand on `Ioo 0 y`
    have hpt : ∀ t ∈ Ioo 0 y, F j t * ENNReal.ofReal ((y - t) / (t * (1 - t)))
        = ∑' n, ∑' k, ENNReal.ofReal (fc j n) * ENNReal.ofReal (t ^ (n + k) * (y - t)) := by
      intro t ht
      rw [ih ht.1.le (ht.2.le.trans hy1), ← ENNReal.tsum_mul_right]
      congr 1; funext n
      exact ofReal_mul_kernel_eq_tsum _ (fc_nonneg j n) n ht.1 ht.2 hy1
    have hmeas : ∀ n k, Measurable fun t : ℝ =>
        ENNReal.ofReal (fc j n) * ENNReal.ofReal (t ^ (n + k) * (y - t)) := by
      intro n k; fun_prop
    have hinner : ∀ n, ∫⁻ t in Ioo 0 y, ∑' k,
        ENNReal.ofReal (fc j n) * ENNReal.ofReal (t ^ (n + k) * (y - t))
        = ∑' k, ENNReal.ofReal (fc j n) * ENNReal.ofReal
            (y ^ (n + k + 2) / ((((n + k : ℕ) : ℝ) + 1) * (((n + k : ℕ) : ℝ) + 2))) := by
      intro n
      rw [lintegral_tsum fun k => (hmeas n k).aemeasurable]
      congr 1; funext k
      rw [lintegral_const_mul _
        (by fun_prop : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (n + k) * (y - t))),
        lintegral_pow_mul_sub _ hy0]
    rw [F_succ, setLIntegral_congr_fun measurableSet_Ioo hpt,
      lintegral_tsum fun n => (Measurable.tsum fun k => hmeas n k).aemeasurable]
    simp_rw [hinner]
    rw [tsum_tsum_add_eq (fun n => ENNReal.ofReal (fc j n))
      (fun N => ENNReal.ofReal (y ^ (N + 2) / (((N : ℝ) + 1) * ((N : ℝ) + 2))))]
    conv_rhs => rw [tsum_eq_zero_add' ENNReal.summable]
    rw [fc_succ_zero, zero_mul, ENNReal.ofReal_zero, zero_add]
    congr 1; funext N
    rw [← ENNReal.ofReal_sum_of_nonneg fun n _ => fc_nonneg j n,
      ← ENNReal.ofReal_mul (Finset.sum_nonneg fun n _ => fc_nonneg j n), fc_succ_succ]
    congr 1
    have h1 : ((N : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((N : ℝ) + 2) ≠ 0 := by positivity
    field_simp

/-- `F_j(1) = Σ_n fc j n`. -/
theorem F_one_eq_tsum (j : ℕ) : F j 1 = ∑' n, ENNReal.ofReal (fc j n) := by
  simpa using F_eq_tsum j (y := 1) zero_le_one le_rfl

end KHoles
