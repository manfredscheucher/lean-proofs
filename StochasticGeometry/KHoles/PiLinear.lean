/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear changes of variables on `(ℝ × ℝ)^m`

Step 4 of `doc/kholes/kholes.md` (used in `PairScaling`, `PairLimit`, `LimitIntegral`).

* `lintegral_comp_pi_linearMap`, `lintegral_comp_pi_affine`: applying the same invertible
  linear (affine) map of `ℝ × ℝ` to each of the `m` points multiplies the Lebesgue integral by
  `|det L|⁻¹ ^ m` (no measurability needed).
* `det_pairLin`, `det_vscaleLin`, `det_pairLin_pairEps`: determinants of the maps of Step 4.
* `sqDist_one_pos`, `sqDist_pairMap`: the squared distance under `pairMap`.
* `lintegral_comp_vscale`: vertical scaling of all points.

Convenience forms: `map_pi_linearMap`, `lintegral_comp_pairMap`,
`lintegral_comp_pairMap_pairEps` (`∫ f (pairMap ∘ z) = n^m ∫ f`), `pairMap_eq_add`,
`pairLin_injective`, `pairEps_pos`, `pairEps_mul_sqDist`, `sqDist_vscaleLin`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### Coordinatewise linear maps on `Fin m → ℝ × ℝ` -/

/-- The linear map `z ↦ (i ↦ L (z i))` on `Fin m → ℝ × ℝ`. -/
noncomputable def piLin (m : ℕ) (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) :
    (Fin m → ℝ × ℝ) →ₗ[ℝ] (Fin m → ℝ × ℝ) :=
  LinearMap.pi fun i => L.comp (LinearMap.proj i)

@[simp] lemma piLin_apply (m : ℕ) (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (z : Fin m → ℝ × ℝ) :
    piLin m L z = fun i => L (z i) := rfl

lemma det_piLin (m : ℕ) (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) :
    LinearMap.det (piLin m L) = LinearMap.det L ^ m := by
  simp [piLin, LinearMap.det_pi]

/-- Image measure form of `lintegral_comp_pi_linearMap`. -/
theorem map_pi_linearMap (m : ℕ) (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) (hL : LinearMap.det L ≠ 0) :
    Measure.map (fun z : Fin m → ℝ × ℝ => fun i => L (z i)) volume =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| ^ m • (volume : Measure (Fin m → ℝ × ℝ)) := by
  have hLp : LinearMap.det (piLin m L) ≠ 0 := by
    rw [det_piLin]; exact pow_ne_zero _ hL
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (μ := (volume : Measure (Fin m → ℝ × ℝ))) hLp
  rw [det_piLin, ← inv_pow, abs_pow, ENNReal.ofReal_pow (abs_nonneg _)] at hmap
  exact hmap

theorem lintegral_comp_pi_linearMap (m : ℕ) (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
    (hL : LinearMap.det L ≠ 0) (f : (Fin m → ℝ × ℝ) → ℝ≥0∞) :
    ∫⁻ z : Fin m → ℝ × ℝ, f (fun i => L (z i)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| ^ m * ∫⁻ z, f z := by
  have hLp : LinearMap.det (piLin m L) ≠ 0 := by
    rw [det_piLin]; exact pow_ne_zero _ hL
  let e : (Fin m → ℝ × ℝ) ≃ₗ[ℝ] (Fin m → ℝ × ℝ) := (piLin m L).equivOfDetNeZero hLp
  let E : (Fin m → ℝ × ℝ) ≃ᵐ (Fin m → ℝ × ℝ) :=
    e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hE : ∀ z, E z = fun i => L (z i) := fun z => rfl
  calc ∫⁻ z : Fin m → ℝ × ℝ, f (fun i => L (z i)) = ∫⁻ z, f (E z) := by simp only [hE]
    _ = ∫⁻ z, f z ∂(Measure.map E volume) := (lintegral_map_equiv f E).symm
    _ = _ := by
      have : (Measure.map E volume) =
          Measure.map (fun z : Fin m → ℝ × ℝ => fun i => L (z i)) volume := rfl
      rw [this, map_pi_linearMap m L hL, lintegral_smul_measure, smul_eq_mul]

theorem lintegral_comp_pi_affine (m : ℕ) (L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ))
    (hL : LinearMap.det L ≠ 0) (c : ℝ × ℝ) (f : (Fin m → ℝ × ℝ) → ℝ≥0∞) :
    ∫⁻ z : Fin m → ℝ × ℝ, f (fun i => c + L (z i)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| ^ m * ∫⁻ z, f z := by
  have h := lintegral_comp_pi_linearMap m L hL (fun w => f ((fun _ => c) + w))
  rw [lintegral_add_left_eq_self f (fun _ : Fin m => c)] at h
  exact h

/-! ### Determinants -/

theorem det_vscaleLin (s : ℝ) : LinearMap.det (vscaleLin s) = s := by
  rw [vscaleLin, LinearMap.det_prodMap]
  simp

theorem det_pairLin (p₁ p₂ : ℝ × ℝ) (ε : ℝ) :
    LinearMap.det (pairLin p₁ p₂ ε) = ε * sqDist 1 p₁ p₂ := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, pairLin_apply, perp, sqDist]
  ring

/-- A linear map of `ℝ × ℝ` with nonzero determinant is injective. -/
lemma injective_of_det_ne_zero {L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)} (hL : LinearMap.det L ≠ 0) :
    Function.Injective L :=
  (L.equivOfDetNeZero hL).injective

/-! ### Squared distances -/

lemma sqDist_one_eq_zero_iff (p₁ p₂ : ℝ × ℝ) : sqDist 1 p₁ p₂ = 0 ↔ p₁ = p₂ := by
  constructor
  · intro h
    simp only [sqDist, one_mul] at h
    have h1 : (p₁.1 - p₂.1) ^ 2 = 0 := by nlinarith [sq_nonneg (p₁.1 - p₂.1), sq_nonneg (p₁.2 - p₂.2)]
    have h2 : (p₁.2 - p₂.2) ^ 2 = 0 := by nlinarith [sq_nonneg (p₁.1 - p₂.1), sq_nonneg (p₁.2 - p₂.2)]
    have h1' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    have h2' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    exact Prod.ext (sub_eq_zero.mp h1') (sub_eq_zero.mp h2')
  · rintro rfl
    exact sqDist_self _ _

theorem sqDist_one_pos {p₁ p₂ : ℝ × ℝ} (h : p₁ ≠ p₂) : 0 < sqDist 1 p₁ p₂ :=
  lt_of_le_of_ne (sqDist_nonneg zero_le_one _ _)
    (fun h0 => h ((sqDist_one_eq_zero_iff p₁ p₂).mp h0.symm))

lemma sqDist_one_ne_zero {p₁ p₂ : ℝ × ℝ} (h : p₁ ≠ p₂) : sqDist 1 p₁ p₂ ≠ 0 :=
  (sqDist_one_pos h).ne'

theorem sqDist_pairMap (p₁ p₂ : ℝ × ℝ) (ε : ℝ) (a b : ℝ × ℝ) :
    sqDist 1 (pairMap p₁ p₂ ε a) (pairMap p₁ p₂ ε b) = sqDist 1 p₁ p₂ * sqDist (ε ^ 2) a b := by
  simp only [sqDist, pairMap, perp, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

lemma sqDist_vscaleLin (c s : ℝ) (a b : ℝ × ℝ) :
    sqDist c (vscaleLin s a) (vscaleLin s b) = sqDist (c * s ^ 2) a b := by
  simp only [vscaleLin_apply, sqDist]
  ring

lemma sqDist_vscale (c s : ℝ) {m : ℕ} (z : Fin m → ℝ × ℝ) (i j : Fin m) :
    sqDist c (vscale s z i) (vscale s z j) = sqDist (c * s ^ 2) (z i) (z j) := by
  simp only [vscale_apply, sqDist]
  ring

/-! ### `pairMap` and `pairEps` -/

lemma pairMap_eq_add (p₁ p₂ : ℝ × ℝ) (ε : ℝ) :
    pairMap p₁ p₂ ε = fun w => p₁ + pairLin p₁ p₂ ε w :=
  funext (pairMap_eq_add_pairLin p₁ p₂ ε)

lemma pairEps_pos {p₁ p₂ : ℝ × ℝ} (h : p₁ ≠ p₂) {n : ℕ} (hn : 0 < n) : 0 < pairEps p₁ p₂ n := by
  unfold pairEps
  have := sqDist_one_pos h
  positivity

lemma pairEps_mul_sqDist {p₁ p₂ : ℝ × ℝ} (h : p₁ ≠ p₂) (n : ℕ) :
    pairEps p₁ p₂ n * sqDist 1 p₁ p₂ = 1 / n := by
  unfold pairEps
  have := sqDist_one_ne_zero h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · field_simp

theorem det_pairLin_pairEps {p₁ p₂ : ℝ × ℝ} (h : p₁ ≠ p₂) {n : ℕ} (_hn : 0 < n) :
    LinearMap.det (pairLin p₁ p₂ (pairEps p₁ p₂ n)) = 1 / n := by
  rw [det_pairLin, pairEps_mul_sqDist h]

lemma det_pairLin_ne_zero {p₁ p₂ : ℝ × ℝ} (h : p₁ ≠ p₂) {ε : ℝ} (hε : ε ≠ 0) :
    LinearMap.det (pairLin p₁ p₂ ε) ≠ 0 := by
  rw [det_pairLin]
  exact mul_ne_zero hε (sqDist_one_ne_zero h)

lemma pairLin_injective {p₁ p₂ : ℝ × ℝ} (h : p₁ ≠ p₂) {ε : ℝ} (hε : ε ≠ 0) :
    Function.Injective (pairLin p₁ p₂ ε) :=
  injective_of_det_ne_zero (det_pairLin_ne_zero h hε)

/-- Change of variables `r i = pairMap p₁ p₂ ε (z i)`. -/
theorem lintegral_comp_pairMap (m : ℕ) {p₁ p₂ : ℝ × ℝ} (h : p₁ ≠ p₂) {ε : ℝ} (hε : ε ≠ 0)
    (f : (Fin m → ℝ × ℝ) → ℝ≥0∞) :
    ∫⁻ z : Fin m → ℝ × ℝ, f (fun i => pairMap p₁ p₂ ε (z i)) =
      ENNReal.ofReal |(ε * sqDist 1 p₁ p₂)⁻¹| ^ m * ∫⁻ z, f z := by
  simp only [pairMap_eq_add_pairLin]
  rw [lintegral_comp_pi_affine m _ (det_pairLin_ne_zero h hε), det_pairLin]

/-- Change of variables `r i = pairMap p₁ p₂ (pairEps p₁ p₂ n) (z i)`: the Jacobian is `n^m`. -/
theorem lintegral_comp_pairMap_pairEps (m : ℕ) {p₁ p₂ : ℝ × ℝ} (h : p₁ ≠ p₂) {n : ℕ}
    (hn : 0 < n) (f : (Fin m → ℝ × ℝ) → ℝ≥0∞) :
    ∫⁻ z : Fin m → ℝ × ℝ, f (fun i => pairMap p₁ p₂ (pairEps p₁ p₂ n) (z i)) =
      (n : ℝ≥0∞) ^ m * ∫⁻ z, f z := by
  rw [lintegral_comp_pairMap m h (pairEps_pos h hn).ne', pairEps_mul_sqDist h, one_div, inv_inv,
    abs_of_nonneg (Nat.cast_nonneg n), ENNReal.ofReal_natCast]

/-! ### Vertical scaling -/

theorem lintegral_comp_vscale (m : ℕ) {s : ℝ} (hs : s ≠ 0) (f : (Fin m → ℝ × ℝ) → ℝ≥0∞) :
    ∫⁻ z : Fin m → ℝ × ℝ, f (vscale s z) = ENNReal.ofReal |s⁻¹| ^ m * ∫⁻ z, f z := by
  simp only [vscale_eq]
  rw [lintegral_comp_pi_linearMap m _ (by rw [det_vscaleLin]; exact hs), det_vscaleLin]

end KHoles
