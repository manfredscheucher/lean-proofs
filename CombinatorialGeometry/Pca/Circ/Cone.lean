/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: the cone at a triple point (`doc/pca/circ.md`, decision C-D5)

Geometric lemmas for the extremal argument of Theorem 19 (`Pca/Circ/Thm19.lean`): three planes
meeting in a point `P` outside the sphere, the "near" intersection points of the three lines
`E_i ∩ E_j` with the sphere (the corners of the triangle facing `P`), and the planar facts used
to show that this triangle is a cell.
-/
import Pca.Circ.Generic

open Equiv Finset Matrix

namespace Pca.Circ

/-- The common point of three planes with independent normals (Cramer's rule). -/
noncomputable def triplePt (ua ub uc : V) (ha hb hc : ℝ) : V :=
  (1 / det3 ua ub uc) • (ha • (ub ⨯₃ uc) + hb • (uc ⨯₃ ua) + hc • (ua ⨯₃ ub))

theorem triplePt_spec {ua ub uc : V} (ha hb hc : ℝ) (hd : det3 ua ub uc ≠ 0) :
    ua ⬝ᵥ triplePt ua ub uc ha hb hc = ha ∧ ub ⬝ᵥ triplePt ua ub uc ha hb hc = hb ∧
      uc ⬝ᵥ triplePt ua ub uc ha hb hc = hc := by
  have e1 : ua ⬝ᵥ (ub ⨯₃ uc) = det3 ua ub uc := rfl
  have e2 : ub ⬝ᵥ (uc ⨯₃ ua) = det3 ua ub uc := by rw [← det3, det3_cyc]
  have e3 : uc ⬝ᵥ (ua ⨯₃ ub) = det3 ua ub uc := by rw [← det3, det3_cyc, det3_cyc]
  unfold triplePt
  simp only [dotProduct_smul, dotProduct_add, smul_eq_mul, e1, e2, e3, dot_self_cross,
    dot_cross_self]
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- Lines through a point `P`: `orient (P, A, x) = - τ · orient (A, A', x)` for
`P = A + τ (A' - A)`. -/
theorem orient_apex (u A A' x : V) (τ : ℝ) :
    orient u (A + τ • (A' - A)) A x = - τ * orient u A A' x := by
  simp only [orient, det3_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring

theorem orient_third (u A B A' : V) (τ : ℝ) :
    orient u A B (A + τ • (A' - A)) = τ * orient u A B A' := by
  simp only [orient, det3_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring

theorem orient_third' (u A B B' : V) (τ : ℝ) :
    orient u A B (B + τ • (B' - B)) = τ * orient u A B B' := by
  simp only [orient, det3_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring

/-- **Separation.** Four points of a circle: if `z` and `A'` are on different sides of the line
`A B`, then `z` and `B` are on the same side of the line `A A'`. -/
theorem same_side_of_sep {u : V} {h : ℝ} (hu : u ≠ 0) {A B z A' : V} (hA : OnCirc u h A)
    (hB : OnCirc u h B) (hz : OnCirc u h z) (hA' : OnCirc u h A') (hAA' : A ≠ A')
    (hzB : z ≠ B) (hzA : z ≠ A) (hzA' : z ≠ A') (hBA : B ≠ A) (hBA' : B ≠ A')
    (hsep : orient u A B z * orient u A B A' < 0) :
    0 < orient u A A' z * orient u A A' B := by
  have o1 := hA.orient_ne_zero hu hA' hz hAA' hzA.symm hzA'.symm
  have o2 := hA.orient_ne_zero hu hA' hB hAA' hBA.symm hBA'.symm
  by_contra hc
  push_neg at hc
  have hneg : orient u A A' z * orient u A A' B < 0 := lt_of_le_of_ne hc (mul_ne_zero o1 o2)
  obtain ⟨t, μ, -, ht1, hμ0, -, he⟩ := chord_meet hu hz hB hA hA' hzB hAA' hneg
  -- `orient (A, B, ·)` at the meeting point, computed on both chords
  have e1 : orient u A B (z + t • (B - z)) = (1 - t) * orient u A B z := by
    rw [orient_affine]
    have : orient u A B B = 0 := by simp only [orient, det3_eq, Pi.sub_apply]; ring
    rw [this, mul_zero, add_zero]
  have e2 : orient u A B (A + μ • (A' - A)) = μ * orient u A B A' := orient_third u A B A' μ
  rw [he, e2] at e1
  have h1t : 0 < 1 - t := by linarith
  rcases lt_or_gt_of_ne (show orient u A B z ≠ 0 by
    intro h0; rw [h0, zero_mul] at hsep; exact lt_irrefl _ hsep) with h1 | h1
  · have : 0 < orient u A B A' := by
      by_contra h2; push_neg at h2; nlinarith
    nlinarith [mul_pos hμ0 this, mul_neg_of_pos_of_neg h1t h1]
  · have : orient u A B A' < 0 := by
      by_contra h2; push_neg at h2; nlinarith
    nlinarith [mul_neg_of_pos_of_neg hμ0 this, mul_pos h1t h1]

/-- Three vectors orthogonal to `u ≠ 0` are dependent. -/
theorem det3_eq_zero_of_perp {u a b c : V} (hu : u ≠ 0) (ha : u ⬝ᵥ a = 0) (hb : u ⬝ᵥ b = 0)
    (hc : u ⬝ᵥ c = 0) : det3 a b c = 0 := by
  have hx : u ⨯₃ (a ⨯₃ b) = 0 := by
    rw [dot_eq] at ha hb
    ext k; fin_cases k <;> simp
    · linear_combination (a 0) * hb - (b 0) * ha
    · linear_combination (a 1) * hb - (b 1) * ha
    · linear_combination (a 2) * hb - (b 2) * ha
  have e := eq_smul_of_cross_eq_zero hu hx
  rw [det3_cross, e, smul_dotProduct, hc, smul_zero]

/-- **Barycentric identity** for four points of a plane with normal `u`: the affine function
`g x = ⟨ul, x⟩ - hl` satisfies `D₀ g z = w_P g P + w_A g A + w_B g B` with the orientations as
weights. -/
theorem bary (u ul P A B z : V) (hl : ℝ) :
    orient u P A B * (ul ⬝ᵥ z - hl) - (orient u z A B * (ul ⬝ᵥ P - hl) +
      orient u P z B * (ul ⬝ᵥ A - hl) + orient u P A z * (ul ⬝ᵥ B - hl)) =
      det3 (A - P) (B - P) (z - P) * (ul ⬝ᵥ u) := by
  simp only [orient, det3_eq, dot_eq, Pi.sub_apply]; ring

/-- Corner identity: for `A = P - a (u_i ⨯₃ u_j)`, `B = P - b (u_i ⨯₃ u_k)`,
`orient u_i A B P = a b det3 u_i u_j u_k ⟨u_i, u_i⟩`. -/
theorem orient_corner (ui uj uk P : V) (a b : ℝ) :
    orient ui (P - a • (ui ⨯₃ uj)) (P - b • (ui ⨯₃ uk)) P =
      a * b * det3 ui uj uk * (ui ⬝ᵥ ui) := by
  simp only [orient, det3_eq, dot_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_0,
    cross_1, cross_2]; ring

end Pca.Circ
