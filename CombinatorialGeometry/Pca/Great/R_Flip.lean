/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: a frame survives the flip of a triangle not touching `c0` (`doc/pca/great.md` 3.4)
-/
import Pca.Great.Frame
import Pca.Great.AFlip

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- The corners of a triangle lie on its curves. -/
theorem curves_corner_sub {d : D} (hT : A.IsTriangle (A.cellOf d)) {x : A.Crossing}
    (hx : x ∈ Arrangement.Cell.corners A (A.cellOf d)) :
    Arrangement.Crossing.curves A x ⊆ Arrangement.Cell.curves A (A.cellOf d) := by
  intro C hC
  obtain ⟨w, hw, rfl⟩ := mem_image.1 hx
  have hwT : A.cellOf w = A.cellOf d := Orbit.mem_darts.1 hw
  rw [A.curves_crossingOf, mem_insert, mem_singleton] at hC
  rcases hC with rfl | rfl
  · exact mem_image.2 ⟨w, hw, rfl⟩
  · rw [Arrangement.curve_σ_tri (Arrangement.isTriangle_of hT hwT)]
    refine mem_image.2 ⟨_, ?_, rfl⟩
    rw [Orbit.mem_darts]
    show A.cellOf (A.φ (A.φ w)) = _
    rw [A.cellOf_φ, A.cellOf_φ, hwT]

/-- A side function is determined by its value on one cell. -/
theorem normSide_eq {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) {f : A.Cell}
    (hf : s f = 1) : normSide A C f = s := by
  rcases hs.eq_or_eq_add_one (isSide_normSide C f) with h | h
  · exact h
  · exfalso
    have := congrFun h f
    rw [normSide_self, hf] at this
    exact absurd this (by decide)

namespace Frame

variable (F : Frame A) {d : D} (hT : A.IsTriangle (A.cellOf d))

/-- The frame in the flipped arrangement. -/
def flipF : Frame (A.flip d hT) := ⟨F.c0, F.β0, F.curve_β0⟩

variable (hc0 : F.c0 ∉ Arrangement.Cell.curves A (A.cellOf d))
include hT hc0

theorem not_corner_of_c0 {y : D} (hy : F.c0 ∈ Arrangement.Crossing.curves A (A.crossingOf y)) :
    ¬ A.IsCorner d y := fun h => hc0 (curves_corner_sub hT h hy)

theorem flip_straight_c0 {y : D} (hy : A.curve y = F.c0) :
    (A.flip d hT).straight y = A.straight y := by
  have h1 : ¬ A.IsCorner d y := F.not_corner_of_c0 hT hc0 (hy ▸ A.mem_curves_crossingOf y)
  have h2 : ¬ A.IsCorner d (A.straight y) :=
    F.not_corner_of_c0 hT hc0 (by rw [← hy, ← A.curve_straight]; exact A.mem_curves_crossingOf _)
  show straightPerm A.σ (Arrangement.flipα hT) y = _
  rw [Arrangement.flip_straightPerm, Arrangement.flipρ_of_not_corner hT h1,
    Arrangement.flipρ_of_not_corner hT h2]

theorem flip_straight_pow_c0 (k : ℕ) :
    ((A.flip d hT).straight ^ k) F.β0 = (A.straight ^ k) F.β0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply,
      F.flip_straight_c0 hT hc0 (by rw [curve_straight_pow, F.curve_β0])]

theorem flip_p (e : Fin n) : (F.flipF hT).p e = F.p e := by
  have h : PosOf (A.flip d hT) F.β0 e = PosOf A F.β0 e := by
    funext k
    simp only [PosOf, flip_straight_pow_c0 F hT hc0]
    rfl
  show firstPos (A.flip d hT) F.β0 e = firstPos A F.β0 e
  unfold firstPos
  split_ifs with h1 h2 h2
  · have s1 := Classical.choose_spec h1
    have s2 := Classical.choose_spec h2
    have s1' : PosOf A F.β0 e (Classical.choose h1) := by rw [← h]; exact s1
    exact s1'.unique s2
  · exact absurd (h ▸ h1) h2
  · exact absurd (h.symm ▸ h2) h1
  · rfl

theorem flip_β (e : Fin n) : (F.flipF hT).β e = F.β e := by
  show A.σ (((A.flip d hT).straight ^ (F.flipF hT).p e) F.β0) = A.σ ((A.straight ^ F.p e) F.β0)
  rw [flip_p F hT hc0, flip_straight_pow_c0 F hT hc0]

theorem not_corner_β (e : Fin n) : ¬ A.IsCorner d (F.β e) := by
  apply F.not_corner_of_c0 hT hc0
  rw [β, A.crossingOf_σ, ← F.curve_β0, ← curve_straight_pow (F.p e) F.β0]
  exact A.mem_curves_crossingOf _

/-- Side functions of the frame after the flip. -/
theorem flip_sR (e : Fin n) :
    ∀ x : A.Crossing, e ∉ Arrangement.Crossing.curves A x →
      (A.flip d hT).crossSide ((F.flipF hT).sR e) x = A.crossSide (F.sR e) x +
        (if x ∈ Arrangement.Cell.corners A (A.cellOf d) ∧
          e ∈ Arrangement.Cell.curves A (A.cellOf d) then 1 else 0) := by
  obtain ⟨s', hs', hgen, hx⟩ := flip_isSide hT (F.isSide_sR e)
  have heq : (F.flipF hT).sR e = s' := by
    show normSide (A.flip d hT) e ((A.flip d hT).cellOf ((F.flipF hT).β e)) = s'
    refine normSide_eq hs' ?_
    rw [flip_β F hT hc0, hgen _ (F.not_corner_β hT hc0 e)]
    exact F.sR_β e
  rw [heq]
  exact hx

theorem flip_s0 :
    ∀ x : A.Crossing, F.c0 ∉ Arrangement.Crossing.curves A x →
      (A.flip d hT).crossSide (F.flipF hT).s0 x = A.crossSide F.s0 x := by
  obtain ⟨s', hs', hgen, hx⟩ := flip_isSide hT F.isSide_s0
  have hα : (A.flip d hT).α F.β0 = A.α F.β0 := by
    have h1 : ¬ A.IsCorner d F.β0 :=
      F.not_corner_of_c0 hT hc0 (F.curve_β0 ▸ A.mem_curves_crossingOf _)
    have h2 : ¬ A.IsCorner d (A.α F.β0) := F.not_corner_of_c0 hT hc0
      (by rw [← F.curve_β0, ← A.isArrangement.curve_α]; exact A.mem_curves_crossingOf _)
    show Arrangement.flipα hT F.β0 = _
    rw [Arrangement.flipα_apply, Arrangement.flipρ_of_not_corner hT h1,
      Arrangement.flipρ_of_not_corner hT h2]
  have heq : (F.flipF hT).s0 = s' := by
    show normSide (A.flip d hT) F.c0 ((A.flip d hT).cellOf ((A.flip d hT).α F.β0)) = s'
    refine normSide_eq hs' ?_
    rw [hα, hgen _ (F.not_corner_of_c0 hT hc0
      (by rw [← F.curve_β0, ← A.isArrangement.curve_α]; exact A.mem_curves_crossingOf _))]
    exact F.s0_left
  intro x hx'
  rw [heq, hx x hx', if_neg (fun h => hc0 h.2), add_zero]

end Frame

end Pca.Great
