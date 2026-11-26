/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
/-
The cap-number integral as an iterated integral over the simplex
(Proposition 3.3 of the (unpublished) draft on the closed form).

For fixed abscissae `0 < x 0 < … < x n < 1` (`m = n + 1` points), the cone lemma
(`lintegral_cone_matrix`) together with the cone geometry (`admissible_eq_image`,
`areaUnder_vecMul`) and the determinant formulas (`det_bbCovNorm`,
`det_bbCov_eq_prod_gaps`) evaluate the inner integral over the admissible heights:

  ∫_{Admissible x} exp (-area) dY = 2^m * (∏ gaps) / ∏ i, x i (1 - x i).

Integrating this over the open simplex of abscissae gives

  a_m = 2^m ∫_{simplex} ∏ gaps / ∏ i, x i (1 - x i) dx,

which is Proposition 3.3 (the identification of the limit with these cap integrals is done in
`UpperCap.lean` and `LimitIntegral.lean`).
-/
import KHoles.Determinant
import KHoles.ConeGeometry
import KHoles.ConeIntegral

open MeasureTheory Finset

namespace KHoles

variable {n : ℕ}

/-- **Inner integral (pointwise in `x`).** For `0 < x 0 < … < x n < 1`, the integral of
`exp (-area)` over the strictly concave chains with abscissae `x` equals
`2 ^ (n+1) * (product of the n + 2 gaps) / ∏ i, x i * (1 - x i)`.
Cone lemma plus Lemma 3.2 (determinant of the normalised bridge covariance). -/
theorem lintegral_admissible (x : Fin (n + 1) → ℝ) (hx : StrictMono x) (h0 : 0 < x 0)
    (h1 : x (Fin.last n) < 1) :
    ∫⁻ Y in Admissible x, ENNReal.ofReal (Real.exp (-areaUnder x Y)) =
      ENNReal.ofReal (2 ^ (n + 1) * (x 0 * (∏ i : Fin n, (x i.succ - x i.castSucc)) *
        (1 - x (Fin.last n))) / ∏ i, (x i * (1 - x i))) := by
  rw [admissible_eq_image hx h0 h1, coneMap,
    lintegral_cone_matrix (bbCovNorm x) (det_bbCovNorm_ne_zero hx h0 h1) (areaUnder x)
      (areaUnder_vecMul hx h0 h1),
    det_bbCovNorm, det_bbCov_eq_prod_gaps x hx h0]
  have hgaps : 0 < ∏ i : Fin n, (x i.succ - x i.castSucc) :=
    prod_pos fun i _ => sub_pos.mpr (hx Fin.castSucc_lt_succ)
  have hnum : 0 < x 0 * (∏ i : Fin n, (x i.succ - x i.castSucc)) * (1 - x (Fin.last n)) :=
    mul_pos (mul_pos h0 hgaps) (sub_pos.mpr h1)
  have hden : 0 < ∏ i, (x i * (1 - x i)) := prod_pos fun i _ => bbCov_diag_pos hx h0 h1 i
  rw [abs_of_pos (div_pos hnum hden)]
  congr 1
  ring

/-- The open simplex `0 < x 0 < … < x n < 1` of `m = n + 1` abscissae (named `simplexFin` to avoid a clash with `simplex m y` of `CapDefs.lean`). -/
def simplexFin (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | StrictMono x ∧ 0 < x 0 ∧ x (Fin.last n) < 1}

/-- The cap-number integral: over the simplex of abscissae, integrate the inner integral of
`exp (-area)` over the strictly concave chains (`a_m` with `m = n + 1`, after the Poisson
reduction, see `UpperCap.lean`). -/
noncomputable def capIntegral (n : ℕ) : ENNReal :=
  ∫⁻ x in simplexFin n, ∫⁻ Y in Admissible x, ENNReal.ofReal (Real.exp (-areaUnder x Y))

/-- The integrand of Proposition 3.3:
`2 ^ (n+1) * (product of the n + 2 gaps) / ∏ i, x i * (1 - x i)`. -/
noncomputable def gapIntegrand (x : Fin (n + 1) → ℝ) : ℝ :=
  2 ^ (n + 1) * (x 0 * (∏ i : Fin n, (x i.succ - x i.castSucc)) * (1 - x (Fin.last n))) /
    ∏ i, (x i * (1 - x i))

/-- The simplex is measurable (a finite intersection of strict inequalities between
coordinates). -/
theorem measurableSet_simplexFin (n : ℕ) : MeasurableSet (simplexFin n) := by
  have h : simplexFin n = (⋂ i : Fin n, {x : Fin (n + 1) → ℝ | x i.castSucc < x i.succ}) ∩
      ({x | 0 < x 0} ∩ {x | x (Fin.last n) < 1}) := by
    ext x
    simp [simplexFin, Fin.strictMono_iff_lt_succ]
  rw [h]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)
  · exact measurableSet_lt measurable_const (measurable_pi_apply _)
  · exact measurableSet_lt (measurable_pi_apply _) measurable_const

/-- **Proposition 3.3 (integral form).** The cap-number integral equals
`∫_{simplex} 2 ^ (n+1) * ∏ gaps / ∏ i, x i * (1 - x i)`, i.e.
`a_m = 2^m ∫_{simplex} ∏ gaps / ∏ x_i (1 - x_i)` with `m = n + 1`, modulo the Poisson
reduction. -/
theorem capIntegral_eq (n : ℕ) :
    capIntegral n = ∫⁻ x in simplexFin n, ENNReal.ofReal (gapIntegrand x) := by
  refine setLIntegral_congr_fun (measurableSet_simplexFin n) fun x hx => ?_
  exact lintegral_admissible x hx.1 hx.2.1 hx.2.2
