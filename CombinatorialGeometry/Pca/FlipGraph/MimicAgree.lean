/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): a triangle shared by a sub-arrangement

Setting of the first case of the mimicking (FROS: "If none of the edges of `T` belongs to `C`, we
can directly apply this triangle flip also in `𝒜`"): `B` lives on a subtype of the darts of `A`,
has the same rotation, and agrees with `A` on `α` along the triangle `T` (so `T` is a triangle of
`A` with the same darts). Then the cells of `T` are the same, and the dart correspondence `flipG`
of the flip of `T` is the same in `A` and `B` (on the darts of `B`). Pure dart chasing, no
deletion.
-/
import Pca.FlipGraph.Delete

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n m : ℕ} {D : Type u} [Fintype D] [DecidableEq D] {K : D → Prop} [DecidablePred K]

section Agree

variable {A : Arrangement n D} {B : Arrangement m {d // K d}}
  (hσ : ∀ x, (B.σ x).val = A.σ x.val) {d : {d // K d}}
  (hTB : B.IsTriangle (B.cellOf d))
  (hα : ∀ b, B.cellOf b = B.cellOf d → (B.α b).val = A.α b.val)
  (hKc : ∀ y, A.cellOf y = A.cellOf d.val → K y)

include hσ hα in
theorem agree_φ {b : {d // K d}} (hb : B.cellOf b = B.cellOf d) : (B.φ b).val = A.φ b.val := by
  rw [B.φ_apply, hσ, hα b hb, A.φ_apply]

include hσ hTB hα in
theorem agree_orbit :
    orbitFinset A.φ d.val = {d.val, (B.φ d).val, (B.φ (B.φ d)).val} := by
  have e1 := agree_φ hσ hα (rfl : B.cellOf d = B.cellOf d)
  have e2 := agree_φ hσ hα (B.cellOf_φ d)
  have e3 := agree_φ hσ hα (show B.cellOf (B.φ (B.φ d)) = B.cellOf d by rw [B.cellOf_φ, B.cellOf_φ])
  have h3 : B.φ (B.φ (B.φ d)) = d := Arrangement.tri_φφφ hTB
  have hA3 : A.φ (A.φ (A.φ d.val)) = d.val := by rw [← e1, ← e2, ← e3, h3]
  rw [orbitFinset_three hA3, ← e1, ← e2]

include hσ hTB hα in
/-- The darts of `T` are the same in `A` and `B`. -/
theorem agree_cell_iff (y : {d // K d}) :
    B.cellOf y = B.cellOf d ↔ A.cellOf y.val = A.cellOf d.val := by
  have horb := agree_orbit hσ hTB hα
  have h3 : B.φ (B.φ (B.φ d)) = d := Arrangement.tri_φφφ hTB
  have hB := orbitFinset_three h3
  constructor
  · intro hy
    have : y ∈ orbitFinset B.φ d := mem_orbitFinset.2 (B.mem_darts_cellOf.1 (hy ▸ B.mem_darts_cellOf_self y))
    have h' : y.val ∈ orbitFinset A.φ d.val := by
      rw [horb]; rw [hB, mem_insert, mem_insert, mem_singleton] at this
      rcases this with rfl | rfl | rfl <;> simp
    exact (A.cellOf_eq_iff.2 (mem_orbitFinset.1 h')).symm
  · intro hy
    have : y.val ∈ orbitFinset A.φ d.val :=
      mem_orbitFinset.2 (A.mem_darts_cellOf.1 (hy ▸ A.mem_darts_cellOf_self y.val))
    rw [horb, mem_insert, mem_insert, mem_singleton] at this
    have hy' : y ∈ orbitFinset B.φ d := by
      rw [hB, mem_insert, mem_insert, mem_singleton]
      rcases this with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
    exact (B.cellOf_eq_iff.2 (mem_orbitFinset.1 hy')).symm

include hα in
/-- A dart of `B` across a side of `T`: its `α` is that of `A`. -/
theorem agree_α_across {y : {d // K d}} (hy : B.cellOf (B.α y) = B.cellOf d) :
    (B.α y).val = A.α y.val := by
  have h := hα _ hy
  rw [B.α_α] at h
  rw [h, A.α_α]

include hσ hTB hα hKc in
theorem agree_cell_α_iff (y : {d // K d}) :
    B.cellOf (B.α y) = B.cellOf d ↔ A.cellOf (A.α y.val) = A.cellOf d.val := by
  constructor
  · intro hy
    rw [← agree_α_across hα hy]
    exact (agree_cell_iff hσ hTB hα _).1 hy
  · intro hy
    set x : {d // K d} := ⟨A.α y.val, hKc _ hy⟩
    have hx : B.cellOf x = B.cellOf d := (agree_cell_iff hσ hTB hα x).2 hy
    have hxy : B.α x = y := Subtype.ext (by rw [hα x hx]; exact A.α_α _)
    rw [← hxy, B.α_α]; exact hx

include hσ hTB hα hKc in
/-- **The dart correspondence of the flip of `T` is the same in `A` and `B`.** -/
theorem agree_flipG (y : {d // K d}) :
    (Arrangement.flipG B d y).val = Arrangement.flipG A d.val y.val := by
  have c1 := agree_cell_iff hσ hTB hα
  have c2 := agree_cell_α_iff hσ hTB hα hKc
  have hσσ : ∀ x : {d // K d}, (B.σ (B.σ x)).val = A.σ (A.σ x.val) := fun x => by rw [hσ, hσ]
  unfold Arrangement.flipG
  by_cases h1 : B.cellOf y = B.cellOf d
  · rw [if_pos h1, if_pos ((c1 y).1 h1), hσσ]
  rw [if_neg h1, if_neg (fun h => h1 ((c1 y).2 h))]
  by_cases h2 : B.cellOf (B.α y) = B.cellOf d
  · rw [if_pos h2, if_pos ((c2 y).1 h2)]
    have e := agree_α_across hα h2
    rw [agree_φ hσ hα (by rw [B.cellOf_φ, h2]), agree_φ hσ hα h2, e]
  rw [if_neg h2, if_neg (fun h => h2 ((c2 y).2 h))]
  have h3 : (B.cellOf (B.α (B.σ (B.σ y))) = B.cellOf d ∨ B.cellOf (B.σ (B.σ y)) = B.cellOf d) ↔
      (A.cellOf (A.α (A.σ (A.σ y.val))) = A.cellOf d.val ∨
        A.cellOf (A.σ (A.σ y.val)) = A.cellOf d.val) := by
    rw [c2, c1, hσσ]
  by_cases h3' : B.cellOf (B.α (B.σ (B.σ y))) = B.cellOf d ∨ B.cellOf (B.σ (B.σ y)) = B.cellOf d
  · rw [if_pos h3', if_pos (h3.1 h3'), ← hσσ]
    rcases h3' with h | h
    · exact agree_α_across hα h
    · exact hα _ h
  · rw [if_neg h3', if_neg (fun h => h3' (h3.2 h))]

end Agree

end Pca.FlipGraph
