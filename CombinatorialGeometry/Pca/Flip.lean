/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Milestone 5: the triangle flip

The flip of a triangle `T` (the cell of a dart `d`) pushes each side of `T` across the opposite
corner. On every curve through a side of `T` the two crossings at the ends of that side swap
their order. In the model this is an operation on the **same** dart type `D`
(`doc/pca/model.md`, section 7):

* a dart keeps its crossing, its curve and its direction, so `σ` and `curve` are unchanged
  and every crossing is the same crossing before and after (the notes regard `v_2'` as `v_2`),
* only `α` changes: `α' = ρ ∘ α ∘ ρ`, where the involution `ρ` swaps every dart `y` of a side
  of `T` (a dart of `T` or its reverse) with `straight y`, the dart on the same curve at the
  other end of that side, pointing in the same direction.

Results (all for an arbitrary arrangement and an arbitrary triangle):

* `Arrangement.flip`: the flipped arrangement (all axioms, Euler from the cell bijection),
* `Arrangement.flipCellEquiv`: the bijection between the cells before and after,
* `Arrangement.flip_size`: `size' (Φ f) + #{sides of T across which f lies}
  = size f + #{corners of T at which f is the opposite cell}`,
* `Arrangement.flip_isTriangle`, `Arrangement.flip_curves`: `T` stays a triangle on the same
  three curves,
* `Arrangement.flip_cellOf_of_not_corner`: away from the corners of `T` a dart lies in the
  cell corresponding to its old cell.
-/
import Pca.Fan
import Pca.Jordan

open Equiv Finset

namespace Pca

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Orbit correspondences -/

omit [DecidableEq D] in
/-- A map that respects single steps of `f` (up to `f'`-orbits) respects `f`-orbits. -/
theorem sameCycle_map {f f' : Perm D} (g : D → D) (h : ∀ y, f'.SameCycle (g y) (g (f y)))
    {a b : D} (hab : f.SameCycle a b) : f'.SameCycle (g a) (g b) := by
  obtain ⟨i, rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  induction i with
  | zero => exact Perm.SameCycle.refl _ _
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans (h _)

/-- The orbits of `f` and `f'` correspond, given maps `g`, `g'` on the darts that respect steps
and are mutually inverse up to orbits. -/
def orbitEquiv {f f' : Perm D} (g g' : D → D)
    (h1 : ∀ y, f'.SameCycle (g y) (g (f y))) (h2 : ∀ y, f.SameCycle (g' y) (g' (f' y)))
    (h3 : ∀ y, f.SameCycle y (g' (g y))) (h4 : ∀ y, f'.SameCycle y (g (g' y))) :
    Orbit f ≃ Orbit f' where
  toFun := Quotient.map' g fun _ _ h => sameCycle_map g h1 h
  invFun := Quotient.map' g' fun _ _ h => sameCycle_map g' h2 h
  left_inv o := by
    obtain ⟨y, rfl⟩ := o.exists_mk
    exact Quotient.sound' (h3 y).symm
  right_inv o := by
    obtain ⟨y, rfl⟩ := o.exists_mk
    exact Quotient.sound' (h4 y).symm

section orbitEquiv

variable {f f' : Perm D} {g g' : D → D} {h1 : ∀ y, f'.SameCycle (g y) (g (f y))}
  {h2 : ∀ y, f.SameCycle (g' y) (g' (f' y))} {h3 : ∀ y, f.SameCycle y (g' (g y))}
  {h4 : ∀ y, f'.SameCycle y (g (g' y))}

omit [DecidableEq D] in
theorem orbitEquiv_mk (y : D) :
    orbitEquiv g g' h1 h2 h3 h4 (Orbit.mk f y) = Orbit.mk f' (g y) := rfl

omit [DecidableEq D] in
theorem orbitEquiv_symm_mk (y : D) :
    (orbitEquiv g g' h1 h2 h3 h4).symm (Orbit.mk f' y) = Orbit.mk f (g' y) := rfl

end orbitEquiv

omit [Fintype D] [DecidableEq D] in
/-- One step of `f` stays in the orbit. -/
theorem sameCycle_self_apply (f : Perm D) (y : D) : f.SameCycle y (f y) :=
  Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _)

omit [Fintype D] [DecidableEq D] in
/-- Two steps of `f` stay in the orbit. -/
theorem sameCycle_two (f : Perm D) (y : D) : f.SameCycle y (f (f y)) :=
  (sameCycle_self_apply f y).trans (sameCycle_self_apply f _)

/-! ## Swapping a set with its image -/

/-- `x ↦ s x` on `S`, `x ↦ s⁻¹ x` on `s S`, the identity elsewhere. -/
def swapAlong (s : Perm D) (S : Finset D) (x : D) : D :=
  if x ∈ S then s x else if s.symm x ∈ S then s.symm x else x

omit [Fintype D] in
theorem swapAlong_involutive {s : Perm D} {S : Finset D} (h : ∀ x ∈ S, s x ∉ S) :
    Function.Involutive (swapAlong s S) := by
  intro x
  unfold swapAlong
  by_cases hx : x ∈ S
  · simp [hx, h x hx]
  · by_cases hy : s.symm x ∈ S
    · simp [hx, hy]
    · simp [hx, hy]

namespace Arrangement

variable {n : ℕ} (A : Arrangement n D)

/-! ## Facts on a triangle -/

theorem straight_symm_apply (y : D) : A.straight.symm y = A.α (A.σ (A.σ y)) := by
  rw [Equiv.symm_apply_eq, straight_apply, α_α, A.σ_σ_σ_σ]

theorem straight_α (y : D) : A.straight (A.α y) = A.σ (A.σ y) := by
  rw [straight_apply, α_α]

theorem σσ_straight (y : D) : A.σ (A.σ (A.straight y)) = A.α y := by
  rw [straight_apply, A.σ_σ_σ_σ]

/-- The cell of `straight b` is the cell to the left of `φ b`. -/
theorem cellOf_straight (b : D) : A.cellOf (A.straight b) = A.cellOf (A.α (A.φ b)) := by
  rw [straight_apply, ← cellOf_σ, φ_apply]

theorem crossingOf_straight (b : D) : A.crossingOf (A.straight b) = A.crossingOf (A.α b) := by
  rw [straight_apply, crossingOf_σσ]

/-- A triangle forces `n ≥ 3` (its sides lie on three distinct curves). -/
theorem three_le_of_triangle {f : A.Cell} (hT : A.IsTriangle f) : 3 ≤ n := by
  have h := card_le_univ (f.darts.image A.curve)
  rw [Triangle.card_curves hT, Fintype.card_fin] at h
  exact h

section Triangle

variable {A} {b : D} (hT : A.IsTriangle (A.cellOf b))
include hT

theorem tri_φφφ : A.φ (A.φ (A.φ b)) = b := A.φ_φ_φ_of_triangle hT

theorem tri_σσσ : A.σ (A.σ (A.σ b)) = A.α (A.φ (A.φ b)) := (A.α_φ_φ_of_triangle hT).symm

theorem tri_σ : A.σ b = A.straight (A.φ (A.φ b)) := by
  rw [straight_apply, A.α_φ_φ_of_triangle hT, A.σ5]

theorem tri_φ : A.IsTriangle (A.cellOf (A.φ b)) := by rw [cellOf_φ]; exact hT

theorem tri_φφ : A.IsTriangle (A.cellOf (A.φ (A.φ b))) := by rw [cellOf_φ, cellOf_φ]; exact hT

/-- N1: the reverse of a side of `T` is not in `T`. -/
theorem tri_α_ne : A.cellOf (A.α b) ≠ A.cellOf b := Triangle.cellOf_α_ne hT

/-- N3: the opposite dart `σ² b` at a corner is not in `T`. -/
theorem tri_σσ_ne : A.cellOf (A.σ (A.σ b)) ≠ A.cellOf b := by
  intro h
  have := Triangle.injOn_crossingOf hT (Orbit.mem_darts.2 h) (A.mem_darts_cellOf_self b)
    (A.crossingOf_σσ b)
  exact A.σ_σ_ne b this

/-- N2: `straight b` is not in `T`. -/
theorem tri_straight_ne : A.cellOf (A.straight b) ≠ A.cellOf b := by
  intro h
  have hφ : A.φ b ∈ (A.cellOf b).darts := by rw [← cellOf_φ]; exact A.mem_darts_cellOf_self _
  have := Triangle.injOn_crossingOf hT (Orbit.mem_darts.2 h) hφ
    (by rw [crossingOf_straight, crossingOf_φ])
  have hc := A.curve_φ_ne b
  rw [← this, curve_straight] at hc
  exact hc rfl

theorem tri_curve_not_mem : A.curve b ∉ Crossing.curves A (A.crossingOf (A.φ (A.φ b))) := by
  rw [curves_crossingOf_φ, mem_insert, mem_singleton, not_or]
  refine ⟨fun h => A.curve_φ_ne b h.symm, fun h => ?_⟩
  have hb2 : A.φ (A.φ b) ∈ (A.cellOf b).darts := by
    rw [← cellOf_φ, ← cellOf_φ]; exact A.mem_darts_cellOf_self _
  have := Triangle.injOn_curve hT (A.mem_darts_cellOf_self b) hb2 h
  have h2 : A.φ b = b := by
    conv_lhs => rw [this]
    exact tri_φφφ hT
  exact A.crossingOf_φ_ne b (by rw [h2])

theorem corners_tri : Cell.corners A (A.cellOf b) =
    {A.crossingOf b, A.crossingOf (A.φ b), A.crossingOf (A.φ (A.φ b))} :=
  corners_of_triangle A hT

/-- O1: the far end of `straight b` is not a corner of `T`. -/
theorem tri_end_straight_not_corner :
    A.crossingOf (A.α (A.straight b)) ∉ Cell.corners A (A.cellOf b) := by
  have hn := A.three_le_of_triangle hT
  rw [corners_tri hT, mem_insert, mem_insert, mem_singleton, not_or, not_or]
  refine ⟨?_, ?_, ?_⟩
  · have := A.crossingOf_α_σσ_ne hn (A.α b)
    rwa [α_α] at this
  · intro h
    exact A.crossingOf_α_ne (A.straight b) (h.trans (by rw [crossingOf_φ, crossingOf_straight]))
  · intro h
    have hm := A.mem_curves_end (A.straight b)
    rw [curve_straight, h] at hm
    exact tri_curve_not_mem hT hm

/-- O2: the far end of `σ² b` is not a corner of `T`. -/
theorem tri_end_σσ_not_corner :
    A.crossingOf (A.α (A.σ (A.σ b))) ∉ Cell.corners A (A.cellOf b) := by
  have hn := A.three_le_of_triangle hT
  rw [corners_tri hT, mem_insert, mem_insert, mem_singleton, not_or, not_or]
  refine ⟨?_, ?_, ?_⟩
  · rw [← A.crossingOf_σσ b]; exact A.crossingOf_α_ne _
  · rw [crossingOf_φ]; exact A.crossingOf_α_σσ_ne hn b
  · intro h
    have hm := A.mem_curves_end (A.σ (A.σ b))
    rw [curve_σσ, h] at hm
    exact tri_curve_not_mem hT hm

end Triangle

/-! ## The flip data of the triangle of `d` -/

section Flip

variable {A} {d : D} (hT : A.IsTriangle (A.cellOf d))

/-- The corners of the triangle of `d`. -/
abbrev IsCorner (d y : D) : Prop := A.crossingOf y ∈ Cell.corners A (A.cellOf d)

include hT in
theorem isTriangle_of {b : D} (hb : A.cellOf b = A.cellOf d) : A.IsTriangle (A.cellOf b) := by
  rw [hb]; exact hT

theorem isCorner_of_mem {y : D} (hy : A.cellOf y = A.cellOf d) : A.IsCorner d y :=
  mem_image.2 ⟨y, Orbit.mem_darts.2 hy, rfl⟩

theorem isCorner_α_of_mem {y : D} (hy : A.cellOf y = A.cellOf d) : A.IsCorner d (A.α y) := by
  rw [IsCorner, ← crossingOf_φ]
  exact isCorner_of_mem (by rw [cellOf_φ, hy])

theorem not_mem_of_not_corner {y : D} (hy : ¬ A.IsCorner d y) : A.cellOf y ≠ A.cellOf d :=
  fun h => hy (isCorner_of_mem h)

include hT in
theorem not_corner_end_straight {b : D} (hb : A.cellOf b = A.cellOf d) :
    ¬ A.IsCorner d (A.α (A.straight b)) := by
  have := tri_end_straight_not_corner (isTriangle_of hT hb)
  rwa [hb] at this

include hT in
theorem not_corner_end_σσ {b : D} (hb : A.cellOf b = A.cellOf d) :
    ¬ A.IsCorner d (A.α (A.σ (A.σ b))) := by
  have := tri_end_σσ_not_corner (isTriangle_of hT hb)
  rwa [hb] at this

include hT in
/-- Every dart at a corner of `T` is `b`, `α b`, `straight b` or `σ² b` for a dart `b` of `T`. -/
theorem corner_cases {y : D} (hy : A.IsCorner d y) :
    ∃ b, A.cellOf b = A.cellOf d ∧
      (y = b ∨ y = A.α b ∨ y = A.straight b ∨ y = A.σ (A.σ b)) := by
  obtain ⟨c, hc, hcy⟩ := mem_image.1 hy
  have hc' : A.cellOf c = A.cellOf d := Orbit.mem_darts.1 hc
  have hTc := isTriangle_of hT hc'
  have hφφ : A.cellOf (A.φ (A.φ c)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ, hc']
  rw [crossingOf_eq_iff] at hcy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcy
  rcases hcy with h | h | h | h
  · exact ⟨c, hc', Or.inl h⟩
  · exact ⟨_, hφφ, Or.inr (Or.inr (Or.inl (h.trans (tri_σ hTc))))⟩
  · exact ⟨c, hc', Or.inr (Or.inr (Or.inr h))⟩
  · exact ⟨_, hφφ, Or.inr (Or.inl (h.trans (tri_σσσ hTc)))⟩

include hT in
/-- Every dart is generic (it and its reverse are not at a corner), an outer dart (the reverse
of `straight b` or of `σ² b`), or a dart at a corner. -/
theorem dart_cases (y : D) :
    (¬ A.IsCorner d y ∧ ¬ A.IsCorner d (A.α y)) ∨
    (∃ b, A.cellOf b = A.cellOf d ∧ (y = A.α (A.straight b) ∨ y = A.α (A.σ (A.σ b)))) ∨
    (∃ b, A.cellOf b = A.cellOf d ∧
      (y = b ∨ y = A.α b ∨ y = A.straight b ∨ y = A.σ (A.σ b))) := by
  by_cases hy : A.IsCorner d y
  · exact Or.inr (Or.inr (corner_cases hT hy))
  by_cases hα : A.IsCorner d (A.α y)
  · obtain ⟨b, hb, h | h | h | h⟩ := corner_cases hT hα
    · exact absurd (by rw [← A.α_α y, h]; exact isCorner_α_of_mem hb) hy
    · exact absurd (by rw [← A.α_α y, h, α_α]; exact isCorner_of_mem hb) hy
    · exact Or.inr (Or.inl ⟨b, hb, Or.inl (by rw [← h, α_α])⟩)
    · exact Or.inr (Or.inl ⟨b, hb, Or.inr (by rw [← h, α_α])⟩)
  · exact Or.inl ⟨hy, hα⟩

/-- The six darts of the sides of `T`: its darts and their reverses. -/
def sideDarts (A : Arrangement n D) (d : D) : Finset D :=
  univ.filter (fun y => A.cellOf y = A.cellOf d ∨ A.cellOf (A.α y) = A.cellOf d)

theorem mem_sideDarts {y : D} :
    y ∈ A.sideDarts d ↔ A.cellOf y = A.cellOf d ∨ A.cellOf (A.α y) = A.cellOf d := by
  simp [sideDarts]

theorem mem_sideDarts_α {y : D} : A.α y ∈ A.sideDarts d ↔ y ∈ A.sideDarts d := by
  rw [mem_sideDarts, mem_sideDarts, α_α, or_comm]

include hT in
theorem straight_not_mem_sideDarts : ∀ y ∈ A.sideDarts d, A.straight y ∉ A.sideDarts d := by
  intro y hy
  rw [mem_sideDarts] at hy ⊢
  rcases hy with hy | hy
  · have hTy := isTriangle_of hT hy
    rw [not_or, ← hy]
    refine ⟨tri_straight_ne hTy, fun h => ?_⟩
    exact not_corner_end_straight hT hy (isCorner_of_mem (h.trans hy))
  · have hTy := isTriangle_of hT hy
    rw [straight_apply, not_or, ← hy]
    refine ⟨tri_σσ_ne hTy, fun h => ?_⟩
    exact not_corner_end_σσ hT hy (isCorner_of_mem (h.trans hy))

/-- The involution `ρ`: it swaps each dart `y` of a side of `T` with `straight y`, the dart on
the same curve at the other end of the side, in the same direction. On each of the three curves
of `T` the darts at the two ends of the side exchange their positions. -/
def flipρ : Perm D :=
  Function.Involutive.toPerm _ (swapAlong_involutive (straight_not_mem_sideDarts hT))

theorem flipρ_apply (y : D) : flipρ hT y = swapAlong A.straight (A.sideDarts d) y := rfl

theorem flipρ_flipρ (y : D) : flipρ hT (flipρ hT y) = y :=
  swapAlong_involutive (straight_not_mem_sideDarts hT) y

theorem flipρ_of_mem {b : D} (hb : A.cellOf b = A.cellOf d) : flipρ hT b = A.straight b := by
  rw [flipρ_apply, swapAlong, if_pos (mem_sideDarts.2 (Or.inl hb))]

theorem flipρ_α_of_mem {b : D} (hb : A.cellOf b = A.cellOf d) :
    flipρ hT (A.α b) = A.σ (A.σ b) := by
  rw [flipρ_apply, swapAlong, if_pos (mem_sideDarts.2 (Or.inr (by rw [α_α, hb]))), straight_α]

theorem flipρ_straight_of_mem {b : D} (hb : A.cellOf b = A.cellOf d) :
    flipρ hT (A.straight b) = b := by
  have hb' : b ∈ A.sideDarts d := mem_sideDarts.2 (Or.inl hb)
  rw [flipρ_apply, swapAlong, if_neg (straight_not_mem_sideDarts hT b hb'),
    Equiv.symm_apply_apply, if_pos hb']

theorem flipρ_σσ_of_mem {b : D} (hb : A.cellOf b = A.cellOf d) :
    flipρ hT (A.σ (A.σ b)) = A.α b := by
  have hb' : A.α b ∈ A.sideDarts d := mem_sideDarts.2 (Or.inr (by rw [α_α, hb]))
  have h := straight_not_mem_sideDarts hT _ hb'
  rw [straight_α] at h
  rw [flipρ_apply, swapAlong, if_neg h, straight_symm_apply, A.σ_σ_σ_σ, if_pos hb']

theorem flipρ_of_not_corner {y : D} (hy : ¬ A.IsCorner d y) : flipρ hT y = y := by
  have h1 : y ∉ A.sideDarts d := by
    rw [mem_sideDarts, not_or]
    refine ⟨not_mem_of_not_corner hy, fun h => hy ?_⟩
    have := isCorner_α_of_mem h
    rwa [α_α] at this
  have h2 : A.straight.symm y ∉ A.sideDarts d := by
    rw [straight_symm_apply, mem_sideDarts_α, mem_sideDarts, not_or]
    refine ⟨fun h => hy ?_, fun h => hy ?_⟩
    · have := isCorner_of_mem h
      rwa [IsCorner, crossingOf_σσ] at this
    · have := isCorner_α_of_mem h
      rwa [IsCorner, α_α, crossingOf_σσ] at this
  rw [flipρ_apply, swapAlong, if_neg h1, if_neg h2]

/-- `ρ` commutes with `σ²` (reversing the direction at a crossing). -/
theorem flipρ_σσ (y : D) : flipρ hT (A.σ (A.σ y)) = A.σ (A.σ (flipρ hT y)) := by
  have hdis := straight_not_mem_sideDarts hT
  simp only [flipρ_apply, swapAlong]
  by_cases h1 : y ∈ A.sideDarts d
  · have h2 : A.σ (A.σ y) ∉ A.sideDarts d := by
      have := hdis _ (mem_sideDarts_α.2 h1)
      rwa [straight_α] at this
    rw [if_pos h1, if_neg h2, straight_symm_apply, A.σ_σ_σ_σ, if_pos (mem_sideDarts_α.2 h1),
      A.σσ_straight]
  · rw [if_neg h1]
    by_cases h3 : A.straight.symm y ∈ A.sideDarts d
    · rw [if_pos h3]
      rw [straight_symm_apply] at h3 ⊢
      rw [if_pos (mem_sideDarts_α.1 h3), straight_apply, straight_symm_apply]
    · rw [if_neg h3]
      rw [straight_symm_apply] at h3
      have h4 : A.σ (A.σ y) ∉ A.sideDarts d := fun h => h3 (mem_sideDarts_α.2 h)
      have h5 : A.straight.symm (A.σ (A.σ y)) ∉ A.sideDarts d := by
        rw [straight_symm_apply, A.σ_σ_σ_σ, mem_sideDarts_α]; exact h1
      rw [if_neg h4, if_neg h5]

theorem isCorner_σσ {y : D} : A.IsCorner d (A.σ (A.σ y)) ↔ A.IsCorner d y := by
  rw [IsCorner, IsCorner, crossingOf_σσ]

theorem isCorner_φ {y : D} : A.IsCorner d (A.φ y) ↔ A.IsCorner d (A.α y) := by
  rw [IsCorner, IsCorner, crossingOf_φ]

/-! ### Darts not in `T` -/

section NotMem

variable {b : D} (hb : A.cellOf b = A.cellOf d)
include hT hb

theorem ne_α : A.cellOf (A.α b) ≠ A.cellOf d := by
  rw [← hb]; exact tri_α_ne (isTriangle_of hT hb)

theorem ne_σσ : A.cellOf (A.σ (A.σ b)) ≠ A.cellOf d := by
  rw [← hb]; exact tri_σσ_ne (isTriangle_of hT hb)

theorem ne_straight : A.cellOf (A.straight b) ≠ A.cellOf d := by
  rw [← hb]; exact tri_straight_ne (isTriangle_of hT hb)

theorem ne_end_straight : A.cellOf (A.α (A.straight b)) ≠ A.cellOf d :=
  not_mem_of_not_corner (not_corner_end_straight hT hb)

theorem ne_end_σσ : A.cellOf (A.α (A.σ (A.σ b))) ≠ A.cellOf d :=
  not_mem_of_not_corner (not_corner_end_σσ hT hb)

end NotMem

/-! ### The flipped edge involution `α' = ρ α ρ` -/

/-- The edge involution after the flip. -/
def flipα : Perm D := flipρ hT * A.α * flipρ hT

theorem flipα_apply (y : D) : flipα hT y = flipρ hT (A.α (flipρ hT y)) := rfl

theorem curve_flipρ (y : D) : A.curve (flipρ hT y) = A.curve y := by
  rw [flipρ_apply, swapAlong]
  split_ifs
  · exact A.curve_straight y
  · rw [← A.curve_straight (A.straight.symm y), Equiv.apply_symm_apply]
  · rfl

/-! ### The flipped face permutation `φ' = σ α'` on the darts near `T` -/

section FaceValues

variable {b : D} (hb : A.cellOf b = A.cellOf d)
include hb

theorem flipφ_of_mem : (A.σ * flipα hT) b = A.φ (A.straight b) := by
  rw [Perm.mul_apply, flipα_apply, flipρ_of_mem hT hb,
    flipρ_of_not_corner hT (not_corner_end_straight hT hb), φ_apply]

theorem flipφ_α : (A.σ * flipα hT) (A.α b) = A.φ (A.σ (A.σ b)) := by
  rw [Perm.mul_apply, flipα_apply, flipρ_α_of_mem hT hb,
    flipρ_of_not_corner hT (not_corner_end_σσ hT hb), φ_apply]

theorem flipφ_straight : (A.σ * flipα hT) (A.straight b) = A.σ (A.σ (A.σ b)) := by
  rw [Perm.mul_apply, flipα_apply, flipρ_straight_of_mem hT hb, flipρ_α_of_mem hT hb]

theorem flipφ_σσ : (A.σ * flipα hT) (A.σ (A.σ b)) = A.σ (A.σ (A.φ b)) := by
  rw [Perm.mul_apply, flipα_apply, flipρ_σσ_of_mem hT hb, α_α, flipρ_of_mem hT hb,
    straight_apply, φ_apply]

theorem flipφ_end_straight : (A.σ * flipα hT) (A.α (A.straight b)) = A.σ b := by
  rw [Perm.mul_apply, flipα_apply, flipρ_of_not_corner hT (not_corner_end_straight hT hb), α_α,
    flipρ_straight_of_mem hT hb]

theorem flipφ_end_σσ : (A.σ * flipα hT) (A.α (A.σ (A.σ b))) = A.φ b := by
  rw [Perm.mul_apply, flipα_apply, flipρ_of_not_corner hT (not_corner_end_σσ hT hb), α_α,
    flipρ_σσ_of_mem hT hb, φ_apply]

end FaceValues

theorem flipφ_generic {y : D} (hy : ¬ A.IsCorner d y) (hα : ¬ A.IsCorner d (A.α y)) :
    (A.σ * flipα hT) y = A.φ y := by
  rw [Perm.mul_apply, flipα_apply, flipρ_of_not_corner hT hy, flipρ_of_not_corner hT hα, φ_apply]

/-! ### Corresponding darts -/

/-- Old dart ↦ a dart of the corresponding cell after the flip: a dart `b` of `T` goes to the
dart `σ² b` of the flipped triangle; the darts `α b` and `straight b` of the cells across the
sides go to `φ² b` and `b` (which lie in these cells after the flip); `σ² b` (in the opposite
cell) goes to `α b`; all other darts stay. -/
def flipG (A : Arrangement n D) (d y : D) : D :=
  if A.cellOf y = A.cellOf d then A.σ (A.σ y)
  else if A.cellOf (A.α y) = A.cellOf d then A.φ (A.φ (A.α y))
  else if A.cellOf (A.α (A.σ (A.σ y))) = A.cellOf d ∨ A.cellOf (A.σ (A.σ y)) = A.cellOf d then
    A.α (A.σ (A.σ y))
  else y

/-- New dart ↦ a dart of the corresponding old cell (the reverse correspondence). -/
def flipG' (A : Arrangement n D) (d y : D) : D :=
  if A.cellOf (A.σ (A.σ y)) = A.cellOf d then A.σ (A.σ y)
  else if A.cellOf y = A.cellOf d ∨ A.cellOf (A.α y) = A.cellOf d then A.σ (A.σ (A.α y))
  else if A.cellOf (A.α (A.σ (A.σ y))) = A.cellOf d then
    A.σ (A.σ (A.φ (A.φ (A.α (A.σ (A.σ y))))))
  else y

section Eval

variable {b : D} (hb : A.cellOf b = A.cellOf d)
include hb

theorem flipG_of_mem : flipG A d b = A.σ (A.σ b) := by rw [flipG, if_pos hb]

include hT

theorem flipG_α : flipG A d (A.α b) = A.φ (A.φ b) := by
  rw [flipG, if_neg (ne_α hT hb), if_pos (by rw [α_α]; exact hb), α_α]

theorem flipG_straight : flipG A d (A.straight b) = b := by
  rw [flipG, if_neg (ne_straight hT hb), if_neg (ne_end_straight hT hb),
    if_pos (Or.inl (by rw [σσ_straight, α_α]; exact hb)), σσ_straight, α_α]

theorem flipG_σσ : flipG A d (A.σ (A.σ b)) = A.α b := by
  rw [flipG, if_neg (ne_σσ hT hb), if_neg (ne_end_σσ hT hb),
    if_pos (Or.inr (by rw [A.σ_σ_σ_σ]; exact hb)), A.σ_σ_σ_σ]

omit hT in
theorem flipG'_σσ : flipG' A d (A.σ (A.σ b)) = b := by
  rw [flipG', if_pos (by rw [A.σ_σ_σ_σ]; exact hb), A.σ_σ_σ_σ]

theorem flipG'_of_mem : flipG' A d b = A.straight b := by
  rw [flipG', if_neg (ne_σσ hT hb), if_pos (Or.inl hb), straight_apply]

theorem flipG'_α : flipG' A d (A.α b) = A.σ (A.σ b) := by
  rw [flipG', if_neg (show ¬ A.cellOf (A.σ (A.σ (A.α b))) = A.cellOf d from ne_straight hT hb),
    if_pos (Or.inr (by rw [α_α]; exact hb)), α_α]

theorem flipG'_straight : flipG' A d (A.straight b) = A.σ (A.σ (A.φ (A.φ b))) := by
  rw [flipG', σσ_straight, if_neg (ne_α hT hb),
    if_neg (not_or.2 ⟨ne_straight hT hb, ne_end_straight hT hb⟩),
    if_pos (by rw [α_α]; exact hb), α_α]

end Eval

theorem flipG_of_not_corner {y : D} (hy : ¬ A.IsCorner d y) : flipG A d y = y := by
  have h1 := not_mem_of_not_corner hy
  have h2 : A.cellOf (A.α y) ≠ A.cellOf d := fun h => hy (by
    have := isCorner_α_of_mem h; rwa [α_α] at this)
  have h3 : ¬ (A.cellOf (A.α (A.σ (A.σ y))) = A.cellOf d ∨
      A.cellOf (A.σ (A.σ y)) = A.cellOf d) := by
    rintro (h | h)
    · have := isCorner_α_of_mem h; rw [α_α, isCorner_σσ] at this; exact hy this
    · have := isCorner_of_mem h; rw [isCorner_σσ] at this; exact hy this
  rw [flipG, if_neg h1, if_neg h2, if_neg h3]

theorem flipG'_of_not_corner {y : D} (hy : ¬ A.IsCorner d y) : flipG' A d y = y := by
  have h1 : A.cellOf (A.σ (A.σ y)) ≠ A.cellOf d := fun h => hy (by
    have := isCorner_of_mem h; rwa [isCorner_σσ] at this)
  have h2 : ¬ (A.cellOf y = A.cellOf d ∨ A.cellOf (A.α y) = A.cellOf d) := by
    rintro (h | h)
    · exact hy (isCorner_of_mem h)
    · have := isCorner_α_of_mem h; rw [α_α] at this; exact hy this
  have h3 : A.cellOf (A.α (A.σ (A.σ y))) ≠ A.cellOf d := fun h => hy (by
    have := isCorner_α_of_mem h; rwa [α_α, isCorner_σσ] at this)
  rw [flipG', if_neg h1, if_neg h2, if_neg h3]

/-! ### The four correspondence conditions -/

theorem flip_C1 (y : D) : (A.σ * flipα hT).SameCycle (flipG A d y) (flipG A d (A.φ y)) := by
  rcases dart_cases hT y with ⟨hy, hα⟩ | ⟨b, hb, h | h⟩ | ⟨b, hb, h | h | h | h⟩
  · rw [flipG_of_not_corner hy, flipG_of_not_corner (isCorner_φ.not.2 hα),
      ← flipφ_generic hT hy hα]
    exact sameCycle_self_apply _ _
  all_goals subst y
  all_goals
    have hTb := isTriangle_of hT hb
    have hφb : A.cellOf (A.φ b) = A.cellOf d := by rw [cellOf_φ, hb]
    have hφφb : A.cellOf (A.φ (A.φ b)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ, hb]
  · -- `y = α (straight b)`
    have e1 : A.φ (A.α (A.straight b)) = A.σ (A.σ (A.φ b)) := by
      rw [φ_apply, α_α, straight_apply, φ_apply]
    have e2 : (A.σ * flipα hT) (A.α (A.straight b)) = A.straight (A.φ (A.φ b)) := by
      rw [flipφ_end_straight hT hb, tri_σ hTb]
    have e3 : (A.σ * flipα hT) (A.straight (A.φ (A.φ b))) = A.α (A.φ b) := by
      rw [flipφ_straight hT hφφb, tri_σσσ (tri_φφ hTb), tri_φφφ (tri_φ hTb)]
    rw [flipG_of_not_corner (not_corner_end_straight hT hb), e1, flipG_σσ hT hφb]
    have := sameCycle_two (A.σ * flipα hT) (A.α (A.straight b))
    rwa [e2, e3] at this
  · -- `y = α (σ² b)`
    rw [flipG_of_not_corner (not_corner_end_σσ hT hb), φ_apply, α_α, tri_σσσ hTb,
      flipG_α hT hφφb, tri_φφφ (tri_φ hTb), ← flipφ_end_σσ hT hb]
    exact sameCycle_self_apply _ _
  · -- `y = b`
    rw [flipG_of_mem hb, flipG_of_mem hφb, ← flipφ_σσ hT hb]
    exact sameCycle_self_apply _ _
  · -- `y = α b`
    rw [flipG_α hT hb, φ_α, tri_σ hTb, flipG_straight hT hφφb]
  · -- `y = straight b`
    have hnc : ¬ A.IsCorner d (A.φ (A.straight b)) := by
      rw [isCorner_φ]; exact not_corner_end_straight hT hb
    rw [flipG_straight hT hb, flipG_of_not_corner hnc, ← flipφ_of_mem hT hb]
    exact sameCycle_self_apply _ _
  · -- `y = σ² b`
    have hnc : ¬ A.IsCorner d (A.φ (A.σ (A.σ b))) := by
      rw [isCorner_φ]; exact not_corner_end_σσ hT hb
    rw [flipG_σσ hT hb, flipG_of_not_corner hnc, ← flipφ_α hT hb]
    exact sameCycle_self_apply _ _

theorem flip_C2 (y : D) :
    A.φ.SameCycle (flipG' A d y) (flipG' A d ((A.σ * flipα hT) y)) := by
  rcases dart_cases hT y with ⟨hy, hα⟩ | ⟨b, hb, h | h⟩ | ⟨b, hb, h | h | h | h⟩
  · rw [flipφ_generic hT hy hα, flipG'_of_not_corner hy,
      flipG'_of_not_corner (isCorner_φ.not.2 hα)]
    exact sameCycle_self_apply _ _
  all_goals subst y
  all_goals
    have hTb := isTriangle_of hT hb
    have hφb : A.cellOf (A.φ b) = A.cellOf d := by rw [cellOf_φ, hb]
    have hφφb : A.cellOf (A.φ (A.φ b)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ, hb]
  · -- `y = α (straight b)`
    have e1 : A.φ (A.α (A.straight b)) = A.σ (A.σ (A.φ b)) := by
      rw [φ_apply, α_α, straight_apply, φ_apply]
    rw [flipG'_of_not_corner (not_corner_end_straight hT hb), flipφ_end_straight hT hb,
      tri_σ hTb, flipG'_straight hT hφφb, tri_φφφ (tri_φ hTb), ← e1]
    exact sameCycle_self_apply _ _
  · -- `y = α (σ² b)`
    have e1 : A.φ (A.φ (A.α (A.σ (A.σ b)))) = A.straight (A.φ b) := by
      rw [A.φ_apply (A.α _), α_α, tri_σσσ hTb, φ_α, tri_σ (tri_φφ hTb), tri_φφφ (tri_φ hTb)]
    rw [flipG'_of_not_corner (not_corner_end_σσ hT hb), flipφ_end_σσ hT hb,
      flipG'_of_mem hT hφb, ← e1]
    exact sameCycle_two _ _
  · -- `y = b`
    have hnc : ¬ A.IsCorner d (A.φ (A.straight b)) := by
      rw [isCorner_φ]; exact not_corner_end_straight hT hb
    rw [flipG'_of_mem hT hb, flipφ_of_mem hT hb, flipG'_of_not_corner hnc]
    exact sameCycle_self_apply _ _
  · -- `y = α b`
    have hnc : ¬ A.IsCorner d (A.φ (A.σ (A.σ b))) := by
      rw [isCorner_φ]; exact not_corner_end_σσ hT hb
    rw [flipG'_α hT hb, flipφ_α hT hb, flipG'_of_not_corner hnc]
    exact sameCycle_self_apply _ _
  · -- `y = straight b`
    rw [flipG'_straight hT hb, flipφ_straight hT hb, tri_σσσ hTb, flipG'_α hT hφφb]
  · -- `y = σ² b`
    rw [flipG'_σσ hb, flipφ_σσ hT hb, flipG'_σσ hφb]
    exact sameCycle_self_apply _ _

include hT in
theorem flip_C3 (y : D) : A.φ.SameCycle y (flipG' A d (flipG A d y)) := by
  by_cases hy : A.IsCorner d y
  · obtain ⟨b, hb, h | h | h | h⟩ := corner_cases hT hy
    all_goals subst y
    · rw [flipG_of_mem hb, flipG'_σσ hb]
    · have hTb := isTriangle_of hT hb
      have hφφb : A.cellOf (A.φ (A.φ b)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ, hb]
      rw [flipG_α hT hb, flipG'_of_mem hT hφφb, ← tri_σ hTb, ← φ_α]
      exact sameCycle_self_apply _ _
    · rw [flipG_straight hT hb, flipG'_of_mem hT hb]
    · rw [flipG_σσ hT hb, flipG'_α hT hb]
  · rw [flipG_of_not_corner hy, flipG'_of_not_corner hy]

theorem flip_C4 (y : D) : (A.σ * flipα hT).SameCycle y (flipG A d (flipG' A d y)) := by
  by_cases hy : A.IsCorner d y
  · obtain ⟨b, hb, h | h | h | h⟩ := corner_cases hT hy
    all_goals subst y
    · rw [flipG'_of_mem hT hb, flipG_straight hT hb]
    · rw [flipG'_α hT hb, flipG_σσ hT hb]
    · have hTb := isTriangle_of hT hb
      have hφφb : A.cellOf (A.φ (A.φ b)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ, hb]
      rw [flipG'_straight hT hb, flipG_σσ hT hφφb, ← tri_σσσ hTb, ← flipφ_straight hT hb]
      exact sameCycle_self_apply _ _
    · rw [flipG'_σσ hb, flipG_of_mem hb]
  · rw [flipG'_of_not_corner hy, flipG_of_not_corner hy]

/-- The cells before and after the flip correspond. -/
def flipCellEquivRaw : Orbit A.φ ≃ Orbit (A.σ * flipα hT) :=
  orbitEquiv (flipG A d) (flipG' A d) (flip_C1 hT) (flip_C2 hT) (flip_C3 hT) (flip_C4 hT)

/-- The segments before and after the flip correspond (via `ρ`). -/
def flipSegEquiv : Orbit A.α ≃ Orbit (flipα hT) :=
  orbitEquiv (flipρ hT) (flipρ hT)
    (fun y => by
      have h : flipα hT (flipρ hT y) = flipρ hT (A.α y) := by rw [flipα_apply, flipρ_flipρ]
      rw [← h]; exact sameCycle_self_apply _ _)
    (fun y => by
      have h : flipρ hT (flipα hT y) = A.α (flipρ hT y) := by rw [flipα_apply, flipρ_flipρ]
      rw [h]; exact sameCycle_self_apply _ _)
    (fun y => by rw [flipρ_flipρ])
    (fun y => by rw [flipρ_flipρ])

theorem flip_straightPerm (y : D) :
    straightPerm A.σ (flipα hT) y = flipρ hT (A.straight (flipρ hT y)) := by
  show A.σ (A.σ (flipα hT y)) = _
  rw [flipα_apply, ← flipρ_σσ, straight_apply]

theorem flip_isArrangement : IsArrangement n A.σ (flipα hT) A.curve where
  card_crossing := A.isArrangement.card_crossing
  α_ne y h := by
    rw [flipα_apply] at h
    have := congrArg (flipρ hT) h
    rw [flipρ_flipρ] at this
    exact A.isArrangement.α_ne _ this
  α_α y := by rw [flipα_apply, flipα_apply, flipρ_flipρ, α_α, flipρ_flipρ]
  curve_α y := by rw [flipα_apply, curve_flipρ, curve_α, curve_flipρ]
  curve_σ := A.isArrangement.curve_σ
  curve_σσ := A.isArrangement.curve_σσ
  straight y z h := by
    have hm : ∀ {a c : D}, A.straight.SameCycle (flipρ hT a) (flipρ hT c) →
        (straightPerm A.σ (flipα hT)).SameCycle a c := by
      intro a c hac
      have := sameCycle_map (f' := straightPerm A.σ (flipα hT)) (flipρ hT) (fun w => by
        have e : straightPerm A.σ (flipα hT) (flipρ hT w) = flipρ hT (A.straight w) := by
          rw [flip_straightPerm, flipρ_flipρ]
        rw [← e]; exact sameCycle_self_apply _ _) hac
      rwa [flipρ_flipρ, flipρ_flipρ] at this
    have hc : A.curve (flipρ hT y) = A.curve (flipρ hT z) := by
      rw [curve_flipρ, curve_flipρ, h]
    rcases A.isArrangement.straight _ _ hc with h1 | h1
    · exact Or.inl (hm h1)
    · rw [← flipρ_σσ] at h1
      exact Or.inr (hm h1)
  intersecting := A.isArrangement.intersecting
  euler := by
    rw [← Fintype.card_congr (flipSegEquiv hT), ← Fintype.card_congr (flipCellEquivRaw hT)]
    exact A.isArrangement.euler

end Flip

/-- **The flip of the triangle `T` = cell of `d`** (new core definition, `doc/pca/model.md`,
section 7). Same darts, same rotation `σ`, same curve labels; the edge involution becomes
`α' = ρ α ρ` (`flipα`): on each curve through a side of `T` the two crossings at the ends of
that side exchange their order along the curve. -/
def flip (d : D) (hT : A.IsTriangle (A.cellOf d)) : Arrangement n D where
  σ := A.σ
  α := flipα hT
  curve := A.curve
  isArrangement := flip_isArrangement hT

section FlipFacts

variable {A} {d : D} (hT : A.IsTriangle (A.cellOf d))

theorem flip_σ : (A.flip d hT).σ = A.σ := rfl
theorem flip_α : (A.flip d hT).α = flipα hT := rfl
theorem flip_curve : (A.flip d hT).curve = A.curve := rfl
theorem flip_φ : (A.flip d hT).φ = A.σ * flipα hT := rfl

/-- The crossings are the same before and after the flip (same type; every crossing keeps its
darts and curves). -/
theorem flip_crossingOf (y : D) : (A.flip d hT).crossingOf y = A.crossingOf y := rfl

/-- **The cells before and after the flip correspond** (`Φ`). -/
def flipCellEquiv : A.Cell ≃ (A.flip d hT).Cell := flipCellEquivRaw hT

theorem flipCellEquiv_cellOf (y : D) :
    flipCellEquiv hT (A.cellOf y) = (A.flip d hT).cellOf (flipG A d y) := rfl

theorem flipCellEquiv_symm_cellOf (y : D) :
    (flipCellEquiv hT).symm ((A.flip d hT).cellOf y) = A.cellOf (flipG' A d y) := rfl

theorem flip_cellOf (y : D) :
    (A.flip d hT).cellOf y = flipCellEquiv hT (A.cellOf (flipG' A d y)) := by
  rw [← flipCellEquiv_symm_cellOf, Equiv.apply_symm_apply]

/-- Away from the corners of `T`, a dart lies in the cell corresponding to its old cell. -/
theorem flip_cellOf_of_not_corner {y : D} (hy : ¬ A.IsCorner d y) :
    (A.flip d hT).cellOf y = flipCellEquiv hT (A.cellOf y) := by
  rw [flip_cellOf, flipG'_of_not_corner hy]

theorem darts_flipCellEquiv (f : A.Cell) :
    (flipCellEquiv hT f).darts = univ.filter (fun z => A.cellOf (flipG' A d z) = f) := by
  ext z
  simp only [mem_filter, mem_univ, true_and]
  rw [Orbit.mem_darts]
  change (A.flip d hT).cellOf z = _ ↔ _
  rw [flip_cellOf, Equiv.apply_eq_iff_eq]

end FlipFacts

/-! ## Cell sizes after the flip -/

/-- The number of darts with property `P` among the four darts at the crossing of `c`. -/
def cnt4 (P : D → Prop) [DecidablePred P] (c : D) : ℕ :=
  (if P c then 1 else 0) + (if P (A.σ c) then 1 else 0) + (if P (A.σ (A.σ c)) then 1 else 0) +
    (if P (A.σ (A.σ (A.σ c))) then 1 else 0)

theorem card_filter_crossingOf (P : D → Prop) [DecidablePred P] (c : D) :
    ((A.crossingOf c).darts.filter P).card = A.cnt4 P c := by
  rw [crossingOf, Orbit.darts_mk, orbitFinset, card_filter_toFinset (orbitList_nodup A.σ c),
    orbitList_σ, cnt4]
  by_cases h0 : P c <;> by_cases h1 : P (A.σ c) <;> by_cases h2 : P (A.σ (A.σ c)) <;>
    by_cases h3 : P (A.σ (A.σ (A.σ c))) <;> simp [h0, h1, h2, h3]

section FlipSize

variable {A} {d : D} (hT : A.IsTriangle (A.cellOf d))
include hT

theorem corners_ne : A.crossingOf d ≠ A.crossingOf (A.φ d) ∧
    A.crossingOf d ≠ A.crossingOf (A.φ (A.φ d)) ∧
    A.crossingOf (A.φ d) ≠ A.crossingOf (A.φ (A.φ d)) := by
  refine ⟨(A.crossingOf_φ_ne d).symm, fun h => ?_, (A.crossingOf_φ_ne (A.φ d)).symm⟩
  have := A.crossingOf_φ_ne (A.φ (A.φ d))
  rw [tri_φφφ hT] at this
  exact this h

/-- Counting the darts at the three corners of `T`. -/
theorem card_corner_filter (P : D → Prop) [DecidablePred P] :
    (univ.filter (fun z => P z ∧ A.IsCorner d z)).card =
      A.cnt4 P d + A.cnt4 P (A.φ d) + A.cnt4 P (A.φ (A.φ d)) := by
  rw [card_filter_eq_sum_orbits A.σ]
  have hx : ∀ x : A.Crossing, (x.darts.filter (fun z => P z ∧ A.IsCorner d z)).card =
      if x ∈ Cell.corners A (A.cellOf d) then (x.darts.filter P).card else 0 := by
    intro x
    split_ifs with hc
    · congr 1
      refine filter_congr fun z hz => ?_
      have hz' : A.crossingOf z = x := Orbit.mem_darts.1 hz
      rw [IsCorner, hz']
      simp [hc]
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro z hz ⟨-, hzc⟩
      have hz' : A.crossingOf z = x := Orbit.mem_darts.1 hz
      rw [IsCorner, hz'] at hzc
      exact hc hzc
  rw [sum_congr rfl fun x _ => hx x, sum_ite_mem, univ_inter, corners_tri hT]
  obtain ⟨h1, h2, h3⟩ := corners_ne hT
  rw [sum_insert (by simp [h1, h2]), sum_insert (by simp [h3]), sum_singleton,
    card_filter_crossingOf, card_filter_crossingOf, card_filter_crossingOf, add_assoc]

/-- The count after the flip at the corner of a dart `c` of `T`. -/
theorem cnt4_new {c : D} (hc : A.cellOf c = A.cellOf d) (f : A.Cell) :
    A.cnt4 (fun z => A.cellOf (flipG' A d z) = f) c =
      (if A.cellOf (A.α (A.φ c)) = f then 1 else 0) +
      (if A.cellOf (A.σ (A.σ (A.φ c))) = f then 1 else 0) +
      (if A.cellOf d = f then 1 else 0) +
      (if A.cellOf (A.σ (A.σ (A.φ (A.φ c)))) = f then 1 else 0) := by
  have hTc := isTriangle_of hT hc
  have hφφc : A.cellOf (A.φ (A.φ c)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ, hc]
  rw [cnt4, tri_σσσ hTc, flipG'_σσ hc, tri_σ hTc, flipG'_of_mem hT hc, flipG'_straight hT hφφc,
    flipG'_α hT hφφc, cellOf_straight, tri_φφφ (tri_φ hTc), hc]

/-- The count before the flip at the corner of a dart `c` of `T`. -/
theorem cnt4_old {c : D} (hc : A.cellOf c = A.cellOf d) (f : A.Cell) :
    A.cnt4 (fun z => A.cellOf z = f) c =
      (if A.cellOf d = f then 1 else 0) + (if A.cellOf (A.α c) = f then 1 else 0) +
      (if A.cellOf (A.σ (A.σ c)) = f then 1 else 0) +
      (if A.cellOf (A.α (A.φ (A.φ c))) = f then 1 else 0) := by
  have hTc := isTriangle_of hT hc
  rw [cnt4, tri_σσσ hTc, A.cellOf_σ c, hc]

/-- **Cell sizes after the flip.** For every cell `f`, with `Φ f` the corresponding cell after
the flip: `|Φ f| + #{sides of T across which f lies} = |f| + #{corners of T at which f is the
cell opposite to T}`. The cell across the side `b` (a dart of `T`) is `cellOf (α b)`, the cell
opposite to `T` at the corner of `b` is `cellOf (σ² b)`. Counted with multiplicity, so this
holds whether or not these cells are distinct (they are, `flip_seven_distinct`). -/
theorem flip_size (f : A.Cell) :
    (flipCellEquiv hT f).size +
      ((if A.cellOf (A.α d) = f then 1 else 0) + (if A.cellOf (A.α (A.φ d)) = f then 1 else 0) +
        (if A.cellOf (A.α (A.φ (A.φ d))) = f then 1 else 0)) =
    f.size +
      ((if A.cellOf (A.σ (A.σ d)) = f then 1 else 0) +
        (if A.cellOf (A.σ (A.σ (A.φ d))) = f then 1 else 0) +
        (if A.cellOf (A.σ (A.σ (A.φ (A.φ d)))) = f then 1 else 0)) := by
  have hsplit : ∀ (P : D → Prop) [DecidablePred P], (univ.filter P).card =
      (univ.filter (fun z => P z ∧ A.IsCorner d z)).card +
        (univ.filter (fun z => P z ∧ ¬ A.IsCorner d z)).card := by
    intro P _
    rw [← filter_filter, ← filter_filter, card_filter_add_card_filter_not]
  have h1 : (flipCellEquiv hT f).size =
      (univ.filter (fun z => A.cellOf (flipG' A d z) = f)).card := by
    rw [Orbit.size, darts_flipCellEquiv]
  have h2 : f.size = (univ.filter (fun z => A.cellOf z = f)).card := by
    rw [Orbit.size]
    congr 1
    ext z
    simp only [mem_filter, mem_univ, true_and, Orbit.mem_darts]
    rfl
  have h3 : univ.filter (fun z => A.cellOf (flipG' A d z) = f ∧ ¬ A.IsCorner d z) =
      univ.filter (fun z => A.cellOf z = f ∧ ¬ A.IsCorner d z) := by
    refine filter_congr fun z _ => ?_
    constructor <;> rintro ⟨h, hc⟩ <;> refine ⟨?_, hc⟩ <;>
      [rwa [flipG'_of_not_corner hc] at h; rwa [flipG'_of_not_corner hc]]
  have hφd : A.cellOf (A.φ d) = A.cellOf d := cellOf_φ A d
  have hφφd : A.cellOf (A.φ (A.φ d)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ]
  rw [h1, h2, hsplit, hsplit (fun z => A.cellOf z = f), h3, card_corner_filter hT,
    card_corner_filter hT, cnt4_new hT rfl, cnt4_new hT hφd, cnt4_new hT hφφd, cnt4_old hT rfl,
    cnt4_old hT hφd, cnt4_old hT hφφd]
  simp only [tri_φφφ hT]
  omega

/-- The cells of `T` and of the flipped triangle correspond. -/
theorem flip_cellOf_σσ : (A.flip d hT).cellOf (A.σ (A.σ d)) = flipCellEquiv hT (A.cellOf d) := by
  rw [flip_cellOf, flipG'_σσ rfl]

/-- **`T` stays a triangle**: the cell of `σ² d` after the flip is a triangle. -/
theorem flip_isTriangle : (A.flip d hT).IsTriangle ((A.flip d hT).cellOf (A.σ (A.σ d))) := by
  have h := flip_size hT (A.cellOf d)
  have hd : A.cellOf d = A.cellOf d := rfl
  have hφd : A.cellOf (A.φ d) = A.cellOf d := cellOf_φ A d
  have hφφd : A.cellOf (A.φ (A.φ d)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ]
  rw [if_neg (ne_α hT hd), if_neg (ne_α hT hφd), if_neg (ne_α hT hφφd), if_neg (ne_σσ hT hd),
    if_neg (ne_σσ hT hφd), if_neg (ne_σσ hT hφφd)] at h
  rw [flip_cellOf_σσ, IsTriangle, IsKCell]
  have h3 : (A.cellOf d).size = 3 := hT
  omega

/-- The darts of the flipped triangle are the darts `σ² b`, `b` a dart of `T`. -/
theorem flip_darts_triangle :
    ((A.flip d hT).cellOf (A.σ (A.σ d))).darts = (A.cellOf d).darts.image (fun b => A.σ (A.σ b)) := by
  symm
  refine eq_of_subset_of_card_le ?_ ?_
  · intro z hz
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hz
    have hb' : A.cellOf b = A.cellOf d := Orbit.mem_darts.1 hb
    rw [Orbit.mem_darts]
    change (A.flip d hT).cellOf (A.σ (A.σ b)) = _
    rw [flip_cellOf, flipG'_σσ hb', hb', flip_cellOf_σσ]
  · have h := flip_isTriangle hT
    rw [IsTriangle, IsKCell] at h
    rw [card_image_of_injective _ (fun x y hxy => by
      have := congrArg (fun z => A.σ (A.σ z)) hxy
      simpa [A.σ_σ_σ_σ] using this)]
    exact (h.trans hT.symm).le

/-- **`T` stays a triangle on the same three curves.** -/
theorem flip_curves :
    ((A.flip d hT).cellOf (A.σ (A.σ d))).darts.image A.curve = (A.cellOf d).darts.image A.curve := by
  rw [flip_darts_triangle, image_image]
  congr 1
  funext b
  exact A.curve_σσ b

end FlipSize

/-! ## The seven cells are distinct

The cells involved in the flip of `T`: `T`, the three cells `cellOf (α b)` across the sides of
`T` and the three cells `cellOf (σ² b)` opposite to `T` at its corners (`b` a dart of `T`).
Pairs at a common segment or crossing are distinct by `cellOf_α_ne'`, `cellOf_σσ_ne`; the
remaining pairs (a cell across a side vs. the cell at the opposite corner, and two opposite
cells) by the side functions of `Pca/Jordan.lean` (the notes' closed-curve argument). -/

section Seven

variable {A} {b : D} (hTb : A.IsTriangle (A.cellOf b))
include hTb

theorem tri_mem_iff {c : D} :
    A.cellOf c = A.cellOf b ↔ c = b ∨ c = A.φ b ∨ c = A.φ (A.φ b) := by
  have hp := A.period_of_size hTb
  have hl : orbitList A.φ b = [b, A.φ b, A.φ (A.φ b)] := by
    simp [orbitList, hp, List.range_succ]
  rw [eq_comm, cellOf_eq_iff, ← mem_orbitList, hl]
  simp

theorem tri_darts_ne : b ≠ A.φ b ∧ b ≠ A.φ (A.φ b) ∧ A.φ b ≠ A.φ (A.φ b) := by
  obtain ⟨h1, h2, h3⟩ := corners_ne hTb
  exact ⟨fun h => h1 (by rw [← h]), fun h => h2 (by rw [← h]), fun h => h3 (by rw [← h])⟩

theorem curve_σ_tri : A.curve (A.σ b) = A.curve (A.φ (A.φ b)) := by
  rw [tri_σ hTb, curve_straight]

omit hTb in
/-- Two cells across consecutive sides of `T` are distinct (they are opposite at a corner). -/
theorem across_ne_across : A.cellOf (A.α b) ≠ A.cellOf (A.α (A.φ b)) := fun h =>
  A.cellOf_σσ_ne (A.α b) (by rw [← straight_apply, cellOf_straight]; exact h.symm)

/-- Two cells opposite to `T` at two of its corners are distinct (side of the curve of the
side between these corners). -/
theorem opp_ne_opp : A.cellOf (A.σ (A.σ b)) ≠ A.cellOf (A.σ (A.σ (A.φ b))) := by
  obtain ⟨s, hs⟩ := A.exists_side (A.curve (A.φ b))
  intro h
  have h1 := A.side_σσ hs b
  have h2 := A.side_σσ hs (A.φ b)
  have hc := tri_curve_not_mem hTb
  rw [curves_crossingOf_φ, mem_insert, mem_singleton, not_or] at hc
  rw [if_neg (A.curve_φ_ne b).symm, curve_σ_tri hTb, if_neg (A.curve_φ_ne (A.φ b)), add_zero,
    add_zero] at h1
  rw [if_pos rfl, if_neg (A.isArrangement.curve_σ _), add_zero, cellOf_φ] at h2
  rw [h, h2] at h1
  have := congrArg (· + s (A.cellOf b)) h1
  simp only [add_right_comm _ (1 : ZMod 2), zmod2_add_self, zero_add] at this
  exact absurd this (by decide)

omit hTb in
/-- The cell across a side and the cell opposite at an end of that side are adjacent. -/
theorem across_ne_opp : A.cellOf (A.α b) ≠ A.cellOf (A.σ (A.σ b)) := by
  intro h
  have := A.cellOf_α_ne' (A.σ b)
  rw [← A.cellOf_σ (A.σ b), A.cellOf_σ b] at this
  exact this h.symm

omit hTb in
theorem across_ne_opp_φ : A.cellOf (A.α b) ≠ A.cellOf (A.σ (A.σ (A.φ b))) := by
  intro h
  have := A.cellOf_α_ne' (A.σ (A.σ (A.σ (A.α b))))
  rw [← cellOf_σ, A.σ_σ_σ_σ, h, φ_apply] at this
  exact this rfl

/-- The cell across a side of `T` and the cell opposite to `T` at the third corner are distinct:
they lie on different sides of the curve of that side (the notes' closed-curve argument). -/
theorem across_ne_opp_φφ : A.cellOf (A.α b) ≠ A.cellOf (A.σ (A.σ (A.φ (A.φ b)))) := by
  obtain ⟨s, hs⟩ := A.exists_side (A.curve b)
  intro h
  have h1 := hs b
  have h2 := A.side_σσ hs (A.φ (A.φ b))
  have hc := tri_curve_not_mem hTb
  rw [curves_crossingOf_φ, mem_insert, mem_singleton, not_or] at hc
  rw [if_pos rfl] at h1
  rw [if_neg (Ne.symm hc.2), curve_σ_tri (tri_φφ hTb), tri_φφφ (tri_φ hTb),
    if_neg (Ne.symm hc.1), add_zero, add_zero, cellOf_φ, cellOf_φ, ← h] at h2
  rw [h2, zmod2_add_self] at h1
  exact absurd h1 (by decide)

theorem across_eq_iff {c : D} (hc : A.cellOf c = A.cellOf b) :
    A.cellOf (A.α c) = A.cellOf (A.α b) ↔ c = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rcases (tri_mem_iff hTb).1 hc with rfl | rfl | rfl
  · rfl
  · exact absurd h.symm across_ne_across
  · have := across_ne_across (A := A) (b := A.φ (A.φ b))
    rw [tri_φφφ hTb] at this
    exact absurd h this

theorem opp_eq_iff {c : D} (hc : A.cellOf c = A.cellOf b) :
    A.cellOf (A.σ (A.σ c)) = A.cellOf (A.σ (A.σ b)) ↔ c = b := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  rcases (tri_mem_iff hTb).1 hc with rfl | rfl | rfl
  · rfl
  · exact absurd h.symm (opp_ne_opp hTb)
  · have := opp_ne_opp (tri_φφ hTb)
    rw [tri_φφφ hTb] at this
    exact absurd h this

theorem opp_ne_across {c : D} (hc : A.cellOf c = A.cellOf b) :
    A.cellOf (A.σ (A.σ c)) ≠ A.cellOf (A.α b) := by
  rcases (tri_mem_iff hTb).1 hc with rfl | rfl | rfl
  · exact across_ne_opp.symm
  · exact across_ne_opp_φ.symm
  · exact (across_ne_opp_φφ hTb).symm

end Seven

section SevenFlip

variable {A} {d : D} (hT : A.IsTriangle (A.cellOf d))
include hT

/-- **The seven cells of the flip are pairwise distinct**: `T`, the cells across its three
sides and the cells opposite to it at its three corners. -/
theorem flip_seven_distinct :
    [A.cellOf d, A.cellOf (A.α d), A.cellOf (A.α (A.φ d)), A.cellOf (A.α (A.φ (A.φ d))),
      A.cellOf (A.σ (A.σ d)), A.cellOf (A.σ (A.σ (A.φ d))),
      A.cellOf (A.σ (A.σ (A.φ (A.φ d))))].Nodup := by
  have hφd : A.cellOf (A.φ d) = A.cellOf d := cellOf_φ A d
  have hφφd : A.cellOf (A.φ (A.φ d)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ]
  obtain ⟨n1, n2, n3⟩ := tri_darts_ne hT
  have tA : ∀ {c}, A.cellOf c = A.cellOf d → A.cellOf d ≠ A.cellOf (A.α c) :=
    fun hc => (ne_α hT hc).symm
  have tO : ∀ {c}, A.cellOf c = A.cellOf d → A.cellOf d ≠ A.cellOf (A.σ (A.σ c)) :=
    fun hc => (ne_σσ hT hc).symm
  have aa : ∀ {c c'}, A.cellOf c = A.cellOf d → A.cellOf c' = A.cellOf d → c ≠ c' →
      A.cellOf (A.α c) ≠ A.cellOf (A.α c') := fun hc hc' hne h =>
    hne ((across_eq_iff (isTriangle_of hT hc') (hc.trans hc'.symm)).1 h)
  have oo : ∀ {c c'}, A.cellOf c = A.cellOf d → A.cellOf c' = A.cellOf d → c ≠ c' →
      A.cellOf (A.σ (A.σ c)) ≠ A.cellOf (A.σ (A.σ c')) := fun hc hc' hne h =>
    hne ((opp_eq_iff (isTriangle_of hT hc') (hc.trans hc'.symm)).1 h)
  have ao : ∀ {c c'}, A.cellOf c = A.cellOf d → A.cellOf c' = A.cellOf d →
      A.cellOf (A.α c) ≠ A.cellOf (A.σ (A.σ c')) := fun hc hc' h =>
    opp_ne_across (isTriangle_of hT hc) (hc'.trans hc.symm) h.symm
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true]
  exact ⟨⟨tA rfl, tA hφd, tA hφφd, tO rfl, tO hφd, tO hφφd⟩,
    ⟨aa rfl hφd n1, aa rfl hφφd n2, ao rfl rfl, ao rfl hφd, ao rfl hφφd⟩,
    ⟨aa hφd hφφd n3, ao hφd rfl, ao hφd hφd, ao hφd hφφd⟩,
    ⟨ao hφφd rfl, ao hφφd hφd, ao hφφd hφφd⟩,
    ⟨oo rfl hφd n1, oo rfl hφφd n2⟩, oo hφd hφφd n3⟩

theorem ind_three {c : D} (hc : A.cellOf c = A.cellOf d) :
    (if c = d then 1 else 0) + (if c = A.φ d then 1 else 0) +
      (if c = A.φ (A.φ d) then 1 else 0) = 1 := by
  obtain ⟨n1, n2, n3⟩ := tri_darts_ne hT
  rcases (tri_mem_iff hT).1 hc with rfl | rfl | rfl <;>
    simp [n1, n2, n3, Ne.symm n1, Ne.symm n2, Ne.symm n3]

/-- **A cell across a side of `T` loses one corner.** -/
theorem flip_size_across {c : D} (hc : A.cellOf c = A.cellOf d) :
    (flipCellEquiv hT (A.cellOf (A.α c))).size + 1 = (A.cellOf (A.α c)).size := by
  have h := flip_size hT (A.cellOf (A.α c))
  have hφd : A.cellOf (A.φ d) = A.cellOf d := cellOf_φ A d
  have hφφd : A.cellOf (A.φ (A.φ d)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ]
  have hTc := isTriangle_of hT hc
  simp only [across_eq_iff hTc hc.symm, across_eq_iff hTc (hφd.trans hc.symm),
    across_eq_iff hTc (hφφd.trans hc.symm)] at h
  rw [if_neg (opp_ne_across hTc hc.symm), if_neg (opp_ne_across hTc (hφd.trans hc.symm)),
    if_neg (opp_ne_across hTc (hφφd.trans hc.symm))] at h
  have h1 := ind_three hT hc
  simp only [eq_comm (a := c)] at h1
  omega

/-- **A cell opposite to `T` at a corner gains one corner.** -/
theorem flip_size_opposite {c : D} (hc : A.cellOf c = A.cellOf d) :
    (flipCellEquiv hT (A.cellOf (A.σ (A.σ c)))).size = (A.cellOf (A.σ (A.σ c))).size + 1 := by
  have h := flip_size hT (A.cellOf (A.σ (A.σ c)))
  have hφd : A.cellOf (A.φ d) = A.cellOf d := cellOf_φ A d
  have hφφd : A.cellOf (A.φ (A.φ d)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ]
  have hTc := isTriangle_of hT hc
  have ne : ∀ {c'}, A.cellOf c' = A.cellOf d → A.cellOf (A.α c') ≠ A.cellOf (A.σ (A.σ c)) :=
    fun hc' h => opp_ne_across (isTriangle_of hT hc') (hc.trans hc'.symm) h.symm
  rw [if_neg (ne rfl), if_neg (ne hφd), if_neg (ne hφφd)] at h
  simp only [opp_eq_iff hTc hc.symm, opp_eq_iff hTc (hφd.trans hc.symm),
    opp_eq_iff hTc (hφφd.trans hc.symm)] at h
  have h1 := ind_three hT hc
  simp only [eq_comm (a := c)] at h1
  omega

/-- **All other cells keep their size** (and `T` stays a triangle, `flip_isTriangle`). -/
theorem flip_size_of_ne {f : A.Cell} (hf : ∀ c, A.cellOf c = A.cellOf d →
    f ≠ A.cellOf (A.α c) ∧ f ≠ A.cellOf (A.σ (A.σ c))) :
    (flipCellEquiv hT f).size = f.size := by
  have h := flip_size hT f
  have hφd : A.cellOf (A.φ d) = A.cellOf d := cellOf_φ A d
  have hφφd : A.cellOf (A.φ (A.φ d)) = A.cellOf d := by rw [cellOf_φ, cellOf_φ]
  rw [if_neg (hf d rfl).1.symm, if_neg (hf _ hφd).1.symm, if_neg (hf _ hφφd).1.symm,
    if_neg (hf d rfl).2.symm, if_neg (hf _ hφd).2.symm, if_neg (hf _ hφφd).2.symm] at h
  omega

end SevenFlip

end Arrangement

end Pca
