/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
/-
The first two cap numbers as integrals (see the (unpublished) draft on the closed form):

  a_1 = 2 ∫_0^1 x(1-x) / (x(1-x)) dx = 2,
  a_2 = 4 ∫_0^1 ∫_0^y (y - x) / ((1 - x) y) dx dy = 8 - 2π²/3.

For a_2 the inner integral is `1 + (1 - y) log (1 - y) / y`, and the outer integral reduces to
`∫_0^1 log (1 - y) / y dy = -π²/6` (termwise integration of the power series of
`-log (1 - y)`, together with `ζ(2) = π²/6`) and `∫_0^1 log (1 - y) dy = -1`.
-/
import KHoles.Constants
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Real MeasureTheory Set intervalIntegral

namespace KHoles

/-- Almost every real number differs from `1`. -/
lemma ae_ne_one : ∀ᵐ y : ℝ, y ≠ 1 := by
  rw [ae_iff]; simp

/-- `∫_0^1 log (1 - y) dy = -1`. -/
theorem integral_log_one_sub : ∫ y in (0:ℝ)..1, Real.log (1 - y) = -1 := by
  rw [intervalIntegral.integral_comp_sub_left (fun y => Real.log y) (1:ℝ)]
  norm_num [integral_log_from_zero]

lemma intervalIntegrable_log_one_sub :
    IntervalIntegrable (fun y : ℝ => Real.log (1 - y)) volume 0 1 := by
  have := (intervalIntegrable_log' (a := (1:ℝ) - 1) (b := 1 - 0)).comp_sub_left 1
  simpa using this.symm

/-- The bounded part `(1 - y) log (1 - y) / y`, with `|·| ≤ 1` on `(0, 1]`. -/
lemma abs_one_sub_mul_log_div_le {y : ℝ} (hy : y ∈ Ioc (0:ℝ) 1) :
    |(1 - y) * Real.log (1 - y) / y| ≤ 1 := by
  obtain ⟨h0, h1⟩ := hy
  rcases eq_or_lt_of_le h1 with rfl | h1
  · simp
  have hu : 0 < 1 - y := by linarith
  have hlog : Real.log (1 - y) ≤ 0 := Real.log_nonpos hu.le (by linarith)
  have hlow : 1 - (1 - y)⁻¹ ≤ Real.log (1 - y) := Real.one_sub_inv_le_log_of_pos hu
  have hlow' : -y ≤ (1 - y) * Real.log (1 - y) := by
    have := mul_le_mul_of_nonneg_left hlow hu.le
    rw [mul_sub, mul_inv_cancel₀ hu.ne'] at this
    linarith
  have hup : (1 - y) * Real.log (1 - y) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu.le hlog
  rw [abs_div, abs_of_pos h0, div_le_one h0, abs_le]
  constructor <;> linarith

lemma intervalIntegrable_one_sub_mul_log_div :
    IntervalIntegrable (fun y : ℝ => (1 - y) * Real.log (1 - y) / y) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
  · exact (((measurable_const.sub measurable_id).mul
      (measurable_const.sub measurable_id).log).div measurable_id).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact abs_one_sub_mul_log_div_le hy

/-- `(1 - y) log (1 - y) / y = log (1 - y) / y - log (1 - y)` for all real `y`. -/
lemma one_sub_mul_log_div_eq (y : ℝ) :
    (1 - y) * Real.log (1 - y) / y = Real.log (1 - y) / y - Real.log (1 - y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · field_simp

lemma intervalIntegrable_log_one_sub_div :
    IntervalIntegrable (fun y : ℝ => Real.log (1 - y) / y) volume 0 1 := by
  have := intervalIntegrable_one_sub_mul_log_div.add intervalIntegrable_log_one_sub
  refine this.congr fun y _ => ?_
  simp only [one_sub_mul_log_div_eq]
  ring

/-- `∫_0^1 log (1 - y) / y dy = -π²/6` (dilogarithm at `1`). -/
theorem integral_log_one_sub_div : ∫ y in (0:ℝ)..1, Real.log (1 - y) / y = -(π ^ 2 / 6) := by
  set F : ℕ → ℝ → ℝ := fun n y => y ^ n / (n + 1) with hF
  have hint : ∀ n : ℕ, ∫ y in (0:ℝ)..1, F n y = 1 / ((n:ℝ) + 1) ^ 2 := by
    intro n
    simp only [hF, intervalIntegral.integral_div, integral_pow]
    field_simp
    norm_num
  have hIoc : ∀ n : ℕ, ∫ y in Ioc (0:ℝ) 1, F n y = 1 / ((n:ℝ) + 1) ^ 2 := by
    intro n; rw [← intervalIntegral.integral_of_le zero_le_one, hint]
  have hFint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioc (0:ℝ) 1)) := by
    intro n
    have : IntervalIntegrable (F n) volume 0 1 :=
      (continuous_pow n |>.div_const _).intervalIntegrable 0 1
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
  have hzeta : HasSum (fun n : ℕ => 1 / ((n:ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hnorm : ∀ n : ℕ, ∫ y in Ioc (0:ℝ) 1, ‖F n y‖ = 1 / ((n:ℝ) + 1) ^ 2 := by
    intro n
    rw [← hIoc n]
    refine setIntegral_congr_fun measurableSet_Ioc fun y hy => ?_
    simp only [hF, Real.norm_eq_abs]
    exact abs_of_nonneg (div_nonneg (pow_nonneg hy.1.le n) (by positivity))
  have hsum := hasSum_integral_of_summable_integral_norm hFint
    (by simp only [hnorm]; exact hzeta.summable)
  simp only [hIoc] at hsum
  have hval : ∫ y in Ioc (0:ℝ) 1, ∑' n, F n y = ∫ y in Ioc (0:ℝ) 1, -(Real.log (1 - y) / y) := by
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [ae_ne_one] with y hy1 hy
    have habs : |y| < 1 := by
      rw [abs_of_pos hy.1]; exact lt_of_le_of_ne hy.2 hy1
    have hs := (hasSum_pow_div_log_of_abs_lt_one habs).div_const y
    have : (fun n : ℕ => y ^ (n + 1) / (n + 1) / y) = fun n => F n y := by
      funext n; simp only [hF]; rw [pow_succ]; field_simp [hy.1.ne']
    rw [this] at hs
    rw [hs.tsum_eq, neg_div]
  rw [hval, MeasureTheory.integral_neg, ← intervalIntegral.integral_of_le zero_le_one] at hsum
  have := hsum.unique hzeta
  linarith

/-- Inner integral: for `0 < y < 1`, `∫_0^y (y - x)/((1 - x) y) dx = 1 + (1 - y) log (1 - y) / y`. -/
lemma inner_integral {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    ∫ x in (0:ℝ)..y, (y - x) / ((1 - x) * y) = 1 + (1 - y) * Real.log (1 - y) / y := by
  have hderiv : ∀ x ∈ uIcc (0:ℝ) y,
      HasDerivAt (fun x => (x + (1 - y) * Real.log (1 - x)) / y)
        ((y - x) / ((1 - x) * y)) x := by
    intro x hx
    rw [uIcc_of_le h0.le] at hx
    have hx1 : 1 - x ≠ 0 := by linarith [hx.2]
    have h : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub 1
    have h3 : HasDerivAt (fun x => (x + (1 - y) * Real.log (1 - x)) / y)
        ((1 + (1 - y) * (-1 / (1 - x))) / y) x :=
      ((hasDerivAt_id' x).add ((h.log hx1).const_mul (1 - y))).div_const y
    convert h3 using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun x => (y - x) / ((1 - x) * y)) (uIcc (0:ℝ) y) := by
    rw [uIcc_of_le h0.le]
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => ?_
    have : 0 < 1 - x := by linarith [hx.2]
    positivity
  rw [integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp only [zero_add, sub_zero, Real.log_one, mul_zero, zero_div]
  field_simp

/-- The double integral defining the second cap number equals `2 - π²/6`. -/
theorem capTwo_integral :
    ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..y, (y - x) / ((1 - x) * y) = 2 - π ^ 2 / 6 := by
  have hcongr : ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..y, (y - x) / ((1 - x) * y)
      = ∫ y in (0:ℝ)..1, (1 + (Real.log (1 - y) / y - Real.log (1 - y))) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_one] with y hy1 hy
    rw [uIoc_of_le zero_le_one] at hy
    rw [inner_integral hy.1 (lt_of_le_of_ne hy.2 hy1), one_sub_mul_log_div_eq]
  rw [hcongr, intervalIntegral.integral_add intervalIntegrable_const
      (intervalIntegrable_log_one_sub_div.sub intervalIntegrable_log_one_sub),
    intervalIntegral.integral_sub intervalIntegrable_log_one_sub_div intervalIntegrable_log_one_sub,
    integral_log_one_sub_div, integral_log_one_sub]
  simp
  ring

/-- `a 2 = 4 ∫_0^1 ∫_0^y (y - x)/((1 - x) y) dx dy`. -/
theorem a_two_eq_integral :
    a 2 = 4 * ∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..y, (y - x) / ((1 - x) * y) := by
  rw [capTwo_integral, a_two]; ring

/-- `a 1 = 2 ∫_0^1 x(1 - x)/(x(1 - x)) dx` (the integrand is `1` on `(0, 1)`). -/
theorem a_one_eq_integral : a 1 = 2 * ∫ x in (0:ℝ)..1, (x * (1 - x)) / (x * (1 - x)) := by
  have : ∫ x in (0:ℝ)..1, (x * (1 - x)) / (x * (1 - x)) = ∫ _ in (0:ℝ)..1, (1:ℝ) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_ne_one] with x hx1 hx
    rw [uIoc_of_le zero_le_one] at hx
    have : x * (1 - x) ≠ 0 :=
      mul_ne_zero hx.1.ne' (sub_ne_zero.mpr (Ne.symm hx1))
    exact div_self this
  rw [this, a_one]; simp

end KHoles
