/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import Mathlib

/-!
# The cone lemma (abstract form)

For a linear map `T : ℝ^m → ℝ^m` with nonzero determinant and a function `ℓ` with
`ℓ (T l) = (∑ i, l i) / 2`, the integral of `exp (-ℓ)` over the image of the open positive
orthant under `T` equals `2 ^ m * |det T|`.

Proof: change of variables `Y = T l` turns the integral into `|det T|` times the orthant
integral of `exp (-(∑ i, l i) / 2)`, which factorises into `m` copies of
`∫ t in Ioi 0, exp (-t / 2) = 2`.
-/

open MeasureTheory Set

namespace KHoles

/-- The open positive orthant of `ℝ^m` is measurable. -/
theorem measurableSet_orthant (m : ℕ) :
    MeasurableSet {l : Fin m → ℝ | ∀ i, 0 < l i} := by
  have : {l : Fin m → ℝ | ∀ i, 0 < l i} = Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)) := by
    ext l; simp
  rw [this]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)

/-- The orthant integral: `∫_{l > 0} exp (-(∑ l_i) / 2) dl = 2 ^ m`. -/
theorem lintegral_orthant_exp (m : ℕ) :
    ∫⁻ l in {l : Fin m → ℝ | ∀ i, 0 < l i}, ENNReal.ofReal (Real.exp (-(∑ i, l i) / 2))
      = ENNReal.ofReal (2 ^ m) := by
  have hset : {l : Fin m → ℝ | ∀ i, 0 < l i} = Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)) := by
    ext l; simp
  have hfun : ∀ l : Fin m → ℝ,
      Real.exp (-(∑ i, l i) / 2) = ∏ i, Real.exp (-1 / 2 * l i) := by
    intro l
    rw [← Real.exp_sum, ← Finset.mul_sum]
    congr 1
    ring
  have h1 : ∫ t in Set.Ioi (0 : ℝ), Real.exp (-1 / 2 * t) = 2 := by
    rw [integral_exp_mul_Ioi (by norm_num)]
    norm_num
  have hint : ∀ _ : Fin m,
      Integrable (fun t : ℝ => Real.exp (-1 / 2 * t)) (volume.restrict (Set.Ioi 0)) :=
    fun _ => integrableOn_exp_mul_Ioi (by norm_num) 0
  rw [hset, volume_pi, Measure.restrict_pi_pi]
  simp_rw [hfun]
  rw [← ofReal_integral_eq_lintegral_ofReal
      (Integrable.fintype_prod (f := fun _ t => Real.exp (-1 / 2 * t)) hint)
      (ae_of_all _ fun l => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le),
    integral_fintype_prod_eq_prod (fun _ t => Real.exp (-1 / 2 * t))]
  simp [h1]

/-- The cone lemma: `∫_{T(Ω)} exp (-ℓ) = 2 ^ m * |det T|` when `ℓ ∘ T = (∑ ·) / 2`. -/
theorem lintegral_cone (m : ℕ) (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hT : LinearMap.det T ≠ 0) (ℓ : (Fin m → ℝ) → ℝ)
    (hℓ : ∀ l, ℓ (T l) = (∑ i, l i) / 2) :
    ∫⁻ Y in T '' {l | ∀ i, 0 < l i}, ENNReal.ofReal (Real.exp (-ℓ Y))
      = ENNReal.ofReal (2 ^ m * |LinearMap.det T|) := by
  have hinj : Function.Injective T := (LinearMap.equivOfDetNeZero T hT).injective
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (measurableSet_orthant m)
      (f := (T : (Fin m → ℝ) → (Fin m → ℝ)))
      (f' := fun _ => LinearMap.toContinuousLinearMap T)
      (fun x _ => (LinearMap.toContinuousLinearMap T).hasFDerivWithinAt) hinj.injOn]
  simp only [LinearMap.det_toContinuousLinearMap, hℓ]
  have h := lintegral_orthant_exp m
  simp only [neg_div] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h, ← ENNReal.ofReal_mul (abs_nonneg _), mul_comm]

/-- Matrix version of the cone lemma, with `T l = l ᵥ* W`. -/
theorem lintegral_cone_matrix {m : ℕ} (W : Matrix (Fin m) (Fin m) ℝ) (hW : W.det ≠ 0)
    (ℓ : (Fin m → ℝ) → ℝ) (hℓ : ∀ l, ℓ (Matrix.vecMul l W) = (∑ i, l i) / 2) :
    ∫⁻ Y in Matrix.vecMulLinear W '' {l | ∀ i, 0 < l i}, ENNReal.ofReal (Real.exp (-ℓ Y))
      = ENNReal.ofReal (2 ^ m * |W.det|) := by
  have hdet : LinearMap.det (Matrix.vecMulLinear W) = W.det := by
    rw [← Matrix.mulVecLin_transpose, ← Matrix.toLin'_apply', LinearMap.det_toLin',
      Matrix.det_transpose]
  rw [lintegral_cone m _ (by rwa [hdet]) ℓ (fun l => hℓ l), hdet]

end KHoles
