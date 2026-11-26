/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.CapDefs
import KHoles.CapPoly
import KHoles.CapSeries
import KHoles.Volterra
import KHoles.EulerTelescope
import KHoles.AlphaSeries
import KHoles.SinAlpha
import KHoles.PowerSeriesUnique
import KHoles.Constants
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Closed form of the simplex integrals (stage 3, step vi: assembly)

This file completes the analytic side of Theorem 3.4 / Proposition 3.3 of the draft: the cap
numbers defined by the simplex integral

    capInt m = ∫_{0<x_1<…<x_m<1} ∏_{j=0}^{m} (x̄_{j+1} - x̄_j) / ∏_i x_i (1 - x_i) dx

satisfy `a m = 2^m · capInt m`, where `a m` is the finite-sum closed form of `Constants.lean`.
Together with `Convolution.lean` (`Cconv_eq_C_all`) the k-hole constants `C k` are therefore
the convolution of these integrals.

Proof (plan `doc/kholes/kholes.md`, §1 (vi)). By `capInt_eq_F` and `F_one_eq_tsum`,
`capInt m = Σ_n fc m n`. For `s ≥ 0`, Tonelli in `ℝ≥0∞` gives
`Σ_m capInt m · s^m = Σ_n P_n(s)/((n+1)! n!)` (`tsum_capInt_mul_pow`), and for `0 < s < 1/4`
the right-hand side is `sin(π α(s))/(π s)` (`hasSum_capPoly` with `α = alphaFn s`). At
`s = 1/8` this shows that every `capInt m` is finite. The same function is the generating
function of `a m / 2^m` (`hasSum_a_div_pow`), so uniqueness of power-series coefficients
(`coeff_unique`) gives `(capInt m).toReal = a m / 2^m`.
-/

open MeasureTheory Set Finset Real
open scoped ENNReal

namespace KHoles

/-- `P_n(s) ≥ 0` for `s ≥ 0`. -/
theorem capPoly_nonneg (n : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ capPoly n s := by
  unfold capPoly
  exact prod_nonneg fun i _ => by positivity

theorem capInt_eq_tsum (m : ℕ) : capInt m = ∑' n, ENNReal.ofReal (fc m n) := by
  rw [capInt_eq_F, F_one_eq_tsum]

/-- Tonelli: `Σ_m capInt m · s^m = Σ_n P_n(s) / ((n+1)! n!)` in `ℝ≥0∞`, for `s ≥ 0`. -/
theorem tsum_capInt_mul_pow {s : ℝ} (hs : 0 ≤ s) :
    ∑' m, capInt m * ENNReal.ofReal (s ^ m)
      = ∑' n, ENNReal.ofReal (capPoly n s / ((n + 1).factorial * n.factorial)) := by
  have hin : ∀ n : ℕ, ∑' j, ENNReal.ofReal (fc j n * s ^ j)
      = ENNReal.ofReal (capPoly n s / ((n + 1).factorial * n.factorial)) := by
    intro n
    have hz : ∀ j ∉ range (n + 1), ENNReal.ofReal (fc j n * s ^ j) = 0 := by
      intro j hj
      rw [Finset.mem_range, not_lt] at hj
      rw [fc_def, pc_eq_zero_of_lt (by omega)]
      simp
    rw [tsum_eq_sum hz, ← ENNReal.ofReal_sum_of_nonneg
      (fun j _ => mul_nonneg (fc_nonneg j n) (pow_nonneg hs j)), capPoly_eq_sum, sum_div]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [fc_def]
    ring
  calc ∑' m, capInt m * ENNReal.ofReal (s ^ m)
      = ∑' m, ∑' n, ENNReal.ofReal (fc m n * s ^ m) := by
        refine tsum_congr fun m => ?_
        rw [capInt_eq_tsum, ← ENNReal.tsum_mul_right]
        refine tsum_congr fun n => ?_
        rw [ENNReal.ofReal_mul (fc_nonneg m n)]
    _ = ∑' n, ∑' m, ENNReal.ofReal (fc m n * s ^ m) := ENNReal.tsum_comm
    _ = _ := tsum_congr hin

/-- The generating function of the simplex integrals in `ℝ≥0∞`, for `0 < s < 1/4`. -/
theorem tsum_capInt_mul_pow_eq {s : ℝ} (h0 : 0 < s) (h1 : s < 1 / 4) :
    ∑' m, capInt m * ENNReal.ofReal (s ^ m)
      = ENNReal.ofReal (Real.sin (π * alphaFn s) / (π * s)) := by
  obtain ⟨hα0, hα1⟩ := alphaFn_mem h0 h1
  have H := hasSum_capPoly hα0 hα1
  rw [alphaFn_mul h0.le h1] at H
  rw [tsum_capInt_mul_pow h0.le, ← H.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
    (fun n => div_nonneg (capPoly_nonneg n h0.le) (by positivity)) H.summable]

theorem capInt_ne_top (m : ℕ) : capInt m ≠ ⊤ := by
  have h := tsum_capInt_mul_pow_eq (s := 1 / 8) (by norm_num) (by norm_num)
  have hle : capInt m * ENNReal.ofReal ((1 / 8 : ℝ) ^ m) ≠ ⊤ :=
    ne_top_of_le_ne_top (h ▸ ENNReal.ofReal_ne_top)
      (ENNReal.le_tsum (f := fun m => capInt m * ENNReal.ofReal ((1 / 8 : ℝ) ^ m)) m)
  intro htop
  apply hle
  rw [htop, ENNReal.top_mul (ENNReal.ofReal_pos.mpr (by positivity)).ne']

/-- The generating function of `(capInt m).toReal` in `ℝ`, for `0 < s < 1/4`. -/
theorem hasSum_capInt_toReal {s : ℝ} (h0 : 0 < s) (h1 : s < 1 / 4) :
    HasSum (fun m => (capInt m).toReal * s ^ m) (Real.sin (π * alphaFn s) / (π * s)) := by
  have h := tsum_capInt_mul_pow_eq h0 h1
  have hf : ∀ m, capInt m * ENNReal.ofReal (s ^ m) ≠ ⊤ :=
    fun m => ENNReal.mul_ne_top (capInt_ne_top m) ENNReal.ofReal_ne_top
  have H := ENNReal.hasSum_toReal (h ▸ ENNReal.ofReal_ne_top)
  rw [← ENNReal.tsum_toReal_eq hf, h, ENNReal.toReal_ofReal] at H
  · convert H using 1
    funext m
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg h0.le m)]
  · obtain ⟨hα0, hα1⟩ := alphaFn_mem h0 h1
    have := pi_pos
    have : 0 ≤ Real.sin (π * alphaFn s) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
    positivity

theorem capInt_toReal (m : ℕ) : (capInt m).toReal = a m / 2 ^ m := by
  set r : NNReal := 1 / 8 with hr_def
  have hr : (r : ℝ) = 1 / 8 := by simp [hr_def]
  have hc : Summable fun n => ‖(capInt n).toReal‖ * (r : ℝ) ^ n := by
    refine (hasSum_capInt_toReal (s := 1 / 8) (by norm_num) (by norm_num)).summable.congr
      fun n => ?_
    rw [hr, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have hd : Summable fun n => ‖a n / 2 ^ n‖ * (r : ℝ) ^ n := by
    refine ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left
      (Real.exp π)).of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    rw [hr, Real.norm_eq_abs]
    calc |a n / 2 ^ n| * (1 / 8 : ℝ) ^ n ≤ Real.exp π * 4 ^ n * (1 / 8) ^ n :=
          mul_le_mul_of_nonneg_right (abs_a_div_le n) (by positivity)
      _ = Real.exp π * (1 / 2) ^ n := by
          rw [mul_assoc, ← mul_pow]
          norm_num
  have h := coeff_unique (fun n => (capInt n).toReal) (fun n => a n / 2 ^ n) r
    (by rw [hr_def]; norm_num) hc hd (fun s hs => ?_)
  · exact congrFun h m
  · rw [hr] at hs
    rw [(hasSum_capInt_toReal hs.1 (by linarith [hs.2])).tsum_eq,
      (hasSum_a_div_pow hs.1 (by linarith [hs.2])).tsum_eq]

theorem a_eq_two_pow_mul_capInt (m : ℕ) : a m = 2 ^ m * (capInt m).toReal := by
  rw [capInt_toReal]
  field_simp

/-- `x̄` is monotone on the simplex below `1`. -/
theorem xbar_le_succ {m : ℕ} {x : Fin m → ℝ} (hx : x ∈ simplex m 1) (k : ℕ) :
    xbar m 1 x k ≤ xbar m 1 x (k + 1) := by
  rcases k with _ | k
  · rw [xbar_zero]
    rcases Nat.lt_or_ge 0 m with h | h
    · rw [xbar_of_lt _ _ h]
      exact (hx.2.1 _).le
    · rw [xbar_of_ge _ _ h]
      norm_num
  · rcases Nat.lt_or_ge k m with h | h
    · rw [xbar_of_lt _ _ h]
      rcases Nat.lt_or_ge (k + 1) m with h' | h'
      · rw [xbar_of_lt _ _ h']
        exact (hx.1 (Fin.mk_lt_mk.mpr (by omega))).le
      · rw [xbar_of_ge _ _ h']
        exact (hx.2.2 _).le
    · rw [xbar_of_ge _ _ h, xbar_of_ge _ _ (by omega)]

/-- The cap density is nonnegative on the simplex below `1`. -/
theorem capDensity_nonneg {m : ℕ} {x : Fin m → ℝ} (hx : x ∈ simplex m 1) :
    0 ≤ capDensity m 1 x := by
  unfold capDensity
  refine div_nonneg (prod_nonneg fun j _ => sub_nonneg.mpr (xbar_le_succ hx j))
    (prod_nonneg fun i _ => mul_nonneg (hx.2.1 i).le (sub_nonneg.mpr (hx.2.2 i).le))

theorem a_eq_simplex_integral (m : ℕ) :
    a m = 2 ^ m * ∫ x in simplex m 1, capDensity m 1 x := by
  rw [integral_eq_lintegral_of_nonneg_ae
      (ae_restrict_of_forall_mem (measurableSet_simplex m 1) fun x hx => capDensity_nonneg hx)
      (measurable_capDensity m 1).aestronglyMeasurable,
    ← capInt_eq, a_eq_two_pow_mul_capInt]

theorem hasSum_a_gf {s : ℝ} (h0 : 0 < s) (h1 : s < 1 / 4) :
    HasSum (fun m => a m * (s / 2) ^ m) (Real.sin (π * alphaFn s) / (π * s)) := by
  convert hasSum_a_div_pow h0 h1 using 1
  funext m
  rw [div_pow]
  ring

/-! ### Regression cross-checks -/

example : (capInt 1).toReal = 1 := by rw [capInt_toReal, a_one]; norm_num

example : (capInt 2).toReal = 2 - π ^ 2 / 6 := by rw [capInt_toReal, a_two]; ring

end KHoles
