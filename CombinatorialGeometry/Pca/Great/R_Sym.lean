/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: antipodal flips are reversible and invariant under isomorphism (`doc/pca/great.md` 3.4)
-/
import Pca.Great.R_Iso
import Pca.FlipGraph.FlipSymm
import Pca.FlipGraph.IsoMap

open Equiv Finset

namespace Pca.Great

universe u v

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- Two triangles with the same corners are equal. -/
theorem tri_eq_of_corners {z w : D} (hz : A.IsTriangle (A.cellOf z))
    (h : Arrangement.Cell.corners A (A.cellOf z) = Arrangement.Cell.corners A (A.cellOf w)) :
    A.cellOf z = A.cellOf w := by
  obtain ⟨n1, n2, n3⟩ := tri_curve_ne hz
  have hb : A.curve (A.σ z) = A.curve (A.φ (A.φ z)) := Arrangement.curve_σ_tri hz
  obtain ⟨sa, hsa⟩ := Arrangement.exists_isSide (A := A) (A.curve z)
  obtain ⟨sb, hsb⟩ := Arrangement.exists_isSide (A := A) (A.curve (A.σ z))
  -- a corner of `w` gives the side of the cell `w`
  have side_of : ∀ {s : A.Cell → ZMod 2} {C : Fin n}, A.IsSide C s → ∀ y,
      A.cellOf y = A.cellOf z → C ∉ Arrangement.Crossing.curves A (A.crossingOf y) →
      s (A.cellOf w) = s (A.cellOf z) := by
    intro s C hs y hy hC
    have hm : A.crossingOf y ∈ Arrangement.Cell.corners A (A.cellOf w) := by
      rw [← h]; exact mem_image.2 ⟨y, Orbit.mem_darts.2 hy, rfl⟩
    obtain ⟨u, hu, hux⟩ := mem_image.1 hm
    have hu' : A.cellOf u = A.cellOf w := Orbit.mem_darts.1 hu
    rw [← hu', ← crossSide_eq hs (hux ▸ hC), hux, crossSide_eq hs hC, hy]
  have hφφ : A.cellOf (A.φ (A.φ z)) = A.cellOf z := by rw [A.cellOf_φ, A.cellOf_φ]
  have ha_w : sa (A.cellOf w) = sa (A.cellOf z) := side_of hsa (A.φ (A.φ z)) hφφ (by
    rw [A.curves_crossingOf, A.curve_σ_φ, mem_insert, mem_singleton, not_or]
    exact ⟨n3, n1⟩)
  have hb_w : sb (A.cellOf w) = sb (A.cellOf z) := side_of hsb (A.φ z) (A.cellOf_φ z) (by
    rw [A.curves_crossingOf, A.curve_σ_φ, mem_insert, mem_singleton, not_or, hb]
    exact ⟨Ne.symm n2, fun h' => A.isArrangement.curve_σ z (by rw [hb]; exact h')⟩)
  -- the dart of `w` at the corner of `z`
  have hm : A.crossingOf z ∈ Arrangement.Cell.corners A (A.cellOf w) := by
    rw [← h]; exact mem_image.2 ⟨z, Orbit.mem_darts.2 rfl, rfl⟩
  obtain ⟨z2, hz2, hzx⟩ := mem_image.1 hm
  have hz2w : A.cellOf z2 = A.cellOf w := Orbit.mem_darts.1 hz2
  have hl := A.crossingOf_eq_iff.1 hzx.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  have hne : A.curve (A.σ z) ≠ A.curve z := A.isArrangement.curve_σ z
  have hz1 : ∀ a : ZMod 2, a + 1 ≠ a := by decide
  rcases hl with hl | hl | hl | hl
  · rw [← hz2w, hl]
  · exfalso
    have := A.side_σ hsa z
    rw [if_pos rfl, ← hl, hz2w, ha_w] at this
    exact hz1 _ this.symm
  · exfalso
    have := A.side_σσ hsa z
    rw [if_pos rfl, if_neg hne, add_zero, ← hl, hz2w, ha_w] at this
    exact hz1 _ this.symm
  · exfalso
    have h1 := A.side_σ hsb (A.σ (A.σ z))
    have h2 := A.side_σσ hsb z
    rw [A.isArrangement.curve_σσ, if_neg (Ne.symm hne)] at h1
    rw [if_neg (Ne.symm hne), if_pos rfl, add_zero] at h2
    rw [add_zero, h2, ← hl, hz2w, hb_w] at h1
    exact hz1 _ h1.symm

/-- The antipodal triangle is unique. -/
theorem isAntipodalTri_unique {T T₁ T₂ : A.Cell} (h₁ : A.IsAntipodalTri T T₁)
    (h₂ : A.IsAntipodalTri T T₂) : T₁ = T₂ := by
  obtain ⟨z, rfl⟩ := T₁.exists_mk
  obtain ⟨w, rfl⟩ := T₂.exists_mk
  exact tri_eq_of_corners h₁.2.1 (h₁.2.2.trans h₂.2.2.symm)

end Pca.Great

namespace Pca.Great

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- The flip depends only on the triangle. -/
theorem flipα_congr {a b : D} (ha : A.IsTriangle (A.cellOf a)) (hb : A.IsTriangle (A.cellOf b))
    (h : A.cellOf a = A.cellOf b) : Arrangement.flipα ha = Arrangement.flipα hb := by
  have hs : A.sideDarts a = A.sideDarts b := by
    ext y; rw [Arrangement.mem_sideDarts, Arrangement.mem_sideDarts, h]
  ext y
  simp only [Arrangement.flipα_apply, Arrangement.flipρ_apply, hs]

theorem flip_congr {a b : D} (ha : A.IsTriangle (A.cellOf a)) (hb : A.IsTriangle (A.cellOf b))
    (h : A.cellOf a = A.cellOf b) : A.flip a ha = A.flip b hb := by
  have hα := flipα_congr ha hb h
  unfold Arrangement.flip
  congr 1

/-- A flip keeps every cell whose darts avoid the corners of the triangle. -/
theorem flip_darts_far {d y : D} (hT : A.IsTriangle (A.cellOf d))
    (hfar : ∀ z, A.cellOf z = A.cellOf y → ¬ A.IsCorner d z) :
    ((A.flip d hT).cellOf y).darts = (A.cellOf y).darts := by
  have hφ : ∀ z, A.cellOf z = A.cellOf y → (A.flip d hT).φ z = A.φ z := fun z hz => by
    refine Arrangement.flipφ_generic hT (hfar z hz) ?_
    intro hα
    apply hfar (A.φ z) (by rw [A.cellOf_φ, hz])
    unfold Arrangement.IsCorner at hα ⊢; rwa [A.crossingOf_φ]
  have hpow : ∀ k : ℕ, ((A.flip d hT).φ ^ k) y = (A.φ ^ k) y := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply, hφ]
      rw [A.cellOf_eq_iff]
      exact (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)).symm
  ext z
  rw [Orbit.mem_darts, Orbit.mem_darts]
  change (A.flip d hT).cellOf z = (A.flip d hT).cellOf y ↔ A.cellOf z = A.cellOf y
  rw [(A.flip d hT).cellOf_eq_iff, A.cellOf_eq_iff]
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := hz.symm.exists_nat_pow_eq
    rw [hpow] at hk
    rw [← hk]
    exact (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)).symm
  · intro hz
    obtain ⟨k, hk⟩ := hz.symm.exists_nat_pow_eq
    rw [← hpow] at hk
    rw [← hk]
    exact (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)).symm

/-- Equal darts, equal cells. -/
theorem cellOf_eq_of_darts {y z : D} (h : (A.cellOf y).darts = (A.cellOf z).darts) :
    A.cellOf y = A.cellOf z := by
  have : y ∈ (A.cellOf z).darts := by rw [← h]; exact A.mem_darts_cellOf_self y
  exact (Orbit.mem_darts.1 this)

end Pca.Great
