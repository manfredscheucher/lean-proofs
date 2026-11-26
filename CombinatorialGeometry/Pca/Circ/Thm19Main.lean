/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: Theorem 19, the triangle and the final statement

See `Pca/Circ/Thm19.lean` for the proof outline (decision C-D5). Here: the darts along the sides
of the triangle facing the minimal NonKrupp triple point, the orientation computation at its three
corners (`corner_sign`), and `Pca.Circ.thm19`.
-/
import Pca.Circ.Thm19

open Equiv Finset Matrix

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

theorem orient_corner2 (ui uj uk P : V) (b c : ℝ) :
    orient uk (P - b • (ui ⨯₃ uk)) (P - c • (uj ⨯₃ uk)) P =
      b * c * det3 ui uj uk * (uk ⬝ᵥ uk) := by
  simp only [orient, det3_eq, dot_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_0,
    cross_1, cross_2]; ring

theorem orient_corner3 (ui uj uk P : V) (a c : ℝ) :
    orient uj (P - c • (uj ⨯₃ uk)) (P - a • (ui ⨯₃ uj)) P =
      -(a * c) * det3 ui uj uk * (uj ⬝ᵥ uj) := by
  simp only [orient, det3_eq, dot_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, cross_0,
    cross_1, cross_2]; ring

theorem pos_of_two_neg {s x o : ℝ} (h₁ : x * o < 0) (h₂ : s * o < 0) : 0 < s * x := by
  have h := mul_pos_of_neg_of_neg h₂ h₁
  have ho : o ≠ 0 := by intro e; rw [e, mul_zero] at h₁; exact lt_irrefl _ h₁
  have e : s * o * (x * o) = (s * x) * (o * o) := by ring
  rw [e] at h
  exact pos_of_mul_pos_left h (mul_self_nonneg o)

namespace IsCircleRep

variable {u : Fin n → V} {h : Fin n → ℝ} {pt : A.Crossing → V} {sgn : D → ℝ}
variable (R : IsCircleRep A u h pt sgn)
include R

theorem sgn_ne_zero (d : D) : sgn d ≠ 0 := by
  rcases R.sgn_pm d with e | e <;> rw [e] <;> norm_num

/-- Darts are determined by crossing, curve and direction. -/
theorem dart_unique {d d' : D} (hc : A.crossingOf d = A.crossingOf d')
    (hcu : A.curve d' = A.curve d) (hs : sgn d' = sgn d) : d' = d := by
  have hl := A.crossingOf_eq_iff.1 hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with e | e | e | e
  · exact e
  · exact absurd (e ▸ hcu) (A.isArrangement.curve_σ d)
  · rw [e, R.sgn_σσ] at hs
    exact absurd (by linarith : sgn d = 0) (R.sgn_ne_zero d)
  · rw [e, A.curve_σσσ] at hcu
    exact absurd hcu (A.isArrangement.curve_σ d)

/-- The dart at `X` heading to `Y` along the curve `a`. -/
theorem exists_heading {a : Fin n} {X Y : A.Crossing} (haX : a ∈ Arrangement.Crossing.curves A X)
    (haY : a ∈ Arrangement.Crossing.curves A Y) (hXY : X ≠ Y) {s : ℝ} (hs : s = 1 ∨ s = -1)
    (hnext : ∀ z, a ∈ Arrangement.Crossing.curves A z → z ≠ X → z ≠ Y →
      0 < s * orient (u a) (pt X) (pt Y) (pt z)) :
    ∃ d, A.crossingOf d = X ∧ A.curve d = a ∧ sgn d = s ∧ A.crossingOf (A.α d) = Y := by
  obtain ⟨d₀, hd₀X, hd₀a⟩ := exists_dart_of_mem haX
  obtain ⟨d, hdX, hda, hds⟩ : ∃ d, A.crossingOf d = X ∧ A.curve d = a ∧ sgn d = s := by
    rcases R.sgn_pm d₀ with e | e <;> rcases hs with rfl | rfl
    · exact ⟨d₀, hd₀X, hd₀a, e⟩
    · exact ⟨A.σ (A.σ d₀), by rw [A.crossingOf_σσ, hd₀X], by rw [A.curve_σσ, hd₀a],
        by rw [R.sgn_σσ, e]⟩
    · exact ⟨A.σ (A.σ d₀), by rw [A.crossingOf_σσ, hd₀X], by rw [A.curve_σσ, hd₀a],
        by rw [R.sgn_σσ, e, neg_neg]⟩
    · exact ⟨d₀, hd₀X, hd₀a, e⟩
  refine ⟨d, hdX, hda, hds, ?_⟩
  by_contra hY
  have h1 := R.next d Y (by rw [hda]; exact haY) (by rw [hdX]; exact hXY.symm) (Ne.symm hY)
  have h2 := hnext (A.crossingOf (A.α d)) (by rw [← hda]; exact A.mem_curves_end d)
    (by rw [← hdX]; exact A.crossingOf_α_ne d) hY
  rw [hda, hdX, hds, orient_swap23] at h1
  linarith

/-- The rotation at a crossing from the orientation of the tangents. -/
theorem σ_eq_of_det {e f : D} (hef : A.crossingOf f = A.crossingOf e)
    (hcur : A.curve f ≠ A.curve e)
    (hdet : 0 < sgn e * sgn f * det3 (u (A.curve e)) (u (A.curve f)) (pt (A.crossingOf e))) :
    A.σ e = f := by
  have hσc : A.curve (A.σ e) = A.curve f := by
    have h1 := A.mem_curves_crossingOf f
    rw [hef, A.curves_crossingOf, Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 hcur
    · exact h1.symm
  have hl := A.crossingOf_eq_iff.1 (show A.crossingOf f = A.crossingOf (A.σ e) by
    rw [A.crossingOf_σ, hef])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with e' | e' | e' | e'
  · exact e'
  · exact absurd (by rw [← hσc, e']) (A.isArrangement.curve_σ f)
  · exfalso
    have hr := R.rot e
    unfold tangent at hr
    rw [det3_smul_smul, det3_cross_cross, R.on_sphere, one_mul, e', R.sgn_σσ, A.curve_σσ] at hr
    nlinarith
  · exact absurd (by rw [← hσc, e', A.curve_σσσ]) (A.isArrangement.curve_σ f)

/-- Both darts along a segment `X Y` of the circle `a` (given that no crossing lies on the near
side of the chord). -/
theorem heading_pair {a : Fin n} {X Y : A.Crossing} (haX : a ∈ Arrangement.Crossing.curves A X)
    (haY : a ∈ Arrangement.Crossing.curves A Y) (hXY : X ≠ Y) {P : V}
    (ho : orient (u a) (pt X) (pt Y) P ≠ 0)
    (hC : ∀ z, a ∈ Arrangement.Crossing.curves A z → z ≠ X → z ≠ Y →
      orient (u a) (pt X) (pt Y) (pt z) * orient (u a) (pt X) (pt Y) P < 0) :
    ∃ d d' : D, A.crossingOf d = X ∧ A.curve d = a ∧
      sgn d = (if 0 < orient (u a) (pt X) (pt Y) P then -1 else 1) ∧
      A.crossingOf d' = Y ∧ A.curve d' = a ∧
      sgn d' = -(if 0 < orient (u a) (pt X) (pt Y) P then -1 else 1) ∧
      A.α d = d' ∧ A.α d' = d := by
  obtain ⟨hsn, hpm⟩ := sign_choice ho
  set s := (if 0 < orient (u a) (pt X) (pt Y) P then (-1 : ℝ) else 1)
  obtain ⟨d, hdX, hda, hds, hdY⟩ := R.exists_heading haX haY hXY hpm
    (fun z hz h1 h2 => pos_of_two_neg (hC z hz h1 h2) hsn)
  obtain ⟨d', hd'Y, hd'a, hd's, hd'X⟩ := R.exists_heading haY haX hXY.symm
    (s := -s) (by rcases hpm with e | e <;> rw [e] <;> norm_num)
    (fun z hz h1 h2 => by
      rw [orient_swap]
      have := pos_of_two_neg (hC z hz h2 h1) hsn
      linarith)
  have e1 : A.α d = d' := R.dart_unique (by rw [hd'Y, hdY]) (by rw [A.curve_α, hda, hd'a])
    (by rw [R.sgn_α, hds, hd's])
  exact ⟨d, d', hdX, hda, hds, hd'Y, hd'a, hd's, e1, by rw [← e1, A.isArrangement.α_α]⟩

end IsCircleRep

end Pca.Circ

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- The curves of a triangle cell. -/
theorem curves_triangle {d : D} (hT : A.IsTriangle (A.cellOf d)) {a b c : Fin n}
    (ha : A.curve d = a) (hb : A.curve (A.φ d) = b) (hc : A.curve (A.φ (A.φ d)) = c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Arrangement.Cell.curves A (A.cellOf d) = {a, b, c} := by
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    unfold Arrangement.Cell.curves
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_image.2 ⟨d, Orbit.mem_darts.2 rfl, ha⟩
    · exact Finset.mem_image.2 ⟨A.φ d, Orbit.mem_darts.2 (A.cellOf_φ d), hb⟩
    · exact Finset.mem_image.2 ⟨A.φ (A.φ d), Orbit.mem_darts.2 (show A.cellOf (A.φ (A.φ d)) = A.cellOf d by
        rw [A.cellOf_φ, A.cellOf_φ]),
        hc⟩
  · rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
    unfold Arrangement.Cell.curves
    rw [Arrangement.Triangle.card_curves hT]

end Pca.Circ
