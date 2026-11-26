/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): triangle facts for P1/P2 of `Delete.lean`

For a triangle `T = cellOf d` and its side darts `U = sideDarts d` (the darts of `T` and their
reverses), with the flip `straight' = ρ ∘ straight ∘ ρ`, `ρ = swapAlong straight U`:

* `straight_straight_not_mem_sideDarts`: the swapped pairs `{u, straight u}` are separated along
  the straight walks (hypothesis `hU2` of `isFirst_swap`);
* `corner_of_mem_sideDarts`, `corner_straight_of_mem_sideDarts`: both darts of a pair start at
  corners of `T`;
* `side_ends_cover`: the two ends of a side meet all three curves of `T`.
-/
import Pca.FlipGraph.FirstReturn
import Pca.FlipGraph.Lemmas

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement

variable {A : Arrangement n D} {d : D} (hT : A.IsTriangle (A.cellOf d))

theorem mem_curves_self (A : Arrangement n D) (z : D) :
    A.curve z ∈ Crossing.curves A (A.crossingOf z) := by
  rw [A.curves_crossingOf]; exact mem_insert_self _ _

theorem mem_curves_σ (A : Arrangement n D) (z : D) :
    A.curve (A.σ z) ∈ Crossing.curves A (A.crossingOf z) := by
  rw [A.curves_crossingOf]; exact mem_insert_of_mem (mem_singleton_self _)

include hT in
theorem corner_of_mem_sideDarts {z : D} (hz : z ∈ A.sideDarts d) : A.IsCorner d z := by
  rcases A.mem_sideDarts.1 hz with h | h
  · exact isCorner_of_mem h
  · have := isCorner_α_of_mem h
    rwa [A.α_α] at this

include hT in
theorem corner_straight_of_mem_sideDarts {z : D} (hz : z ∈ A.sideDarts d) :
    A.IsCorner d (A.straight z) := by
  rw [IsCorner, crossingOf_straight]
  rcases A.mem_sideDarts.1 hz with h | h
  · exact isCorner_α_of_mem h
  · exact isCorner_of_mem h

include hT in
theorem straight_straight_not_mem_sideDarts :
    ∀ u ∈ A.sideDarts d, A.straight (A.straight u) ∉ A.sideDarts d := by
  intro u hu hm
  have hc := corner_of_mem_sideDarts hT hm
  rw [IsCorner, crossingOf_straight] at hc
  rcases A.mem_sideDarts.1 hu with h | h
  · exact not_corner_end_straight hT h hc
  · rw [show u = A.α (A.α u) from (A.α_α u).symm, straight_α] at hc
    exact not_corner_end_σσ hT h hc

theorem tri_mem_three {b y : D} (hb : A.IsTriangle (A.cellOf b)) (hy : A.cellOf y = A.cellOf b) :
    y = b ∨ y = A.φ b ∨ y = A.φ (A.φ b) := by
  have hs : A.φ.SameCycle b y := A.mem_darts_cellOf.1 (by rw [← hy]; exact A.mem_darts_cellOf_self y)
  obtain ⟨i, hi⟩ := hs.exists_nat_pow_eq
  have hp : Function.IsPeriodicPt A.φ 3 b := tri_φφφ hb
  have h3 : (A.φ ^ (i % 3)) b = y := by
    rw [← hi, Perm.coe_pow, Perm.coe_pow, hp.iterate_mod_apply]
  have : i % 3 < 3 := Nat.mod_lt _ (by omega)
  interval_cases (i % 3)
  · left; rw [← h3]; rfl
  · right; left; rw [← h3]; rfl
  · right; right; rw [← h3]; rfl

include hT in
/-- The two ends of the side of `b ∈ T` meet every curve of `T`. -/
theorem tri_curve_cover {b y : D} (hb : A.cellOf b = A.cellOf d) (hy : A.cellOf y = A.cellOf d) :
    A.curve y ∈ Crossing.curves A (A.crossingOf b) ∨
      A.curve y ∈ Crossing.curves A (A.crossingOf (A.α b)) := by
  have hTb := isTriangle_of hT hb
  rcases tri_mem_three hTb (hy.trans hb.symm) with rfl | rfl | rfl
  · exact Or.inl (mem_curves_self A _)
  · right
    rw [show A.φ b = A.σ (A.α b) from rfl]
    exact mem_curves_σ A _
  · left
    rw [← A.isArrangement.curve_α, ← tri_σσσ hTb, ← A.crossingOf_σσσ b]
    exact mem_curves_self A _

include hT in
/-- The ends of a swapped pair `{u, straight u}` are the two ends of a side of `T`. -/
theorem side_ends {u : D} (hu : u ∈ A.sideDarts d) : ∃ b, A.cellOf b = A.cellOf d ∧
    ((A.crossingOf u = A.crossingOf b ∧ A.crossingOf (A.straight u) = A.crossingOf (A.α b)) ∨
      (A.crossingOf u = A.crossingOf (A.α b) ∧ A.crossingOf (A.straight u) = A.crossingOf b)) := by
  rcases A.mem_sideDarts.1 hu with h | h
  · exact ⟨u, h, Or.inl ⟨rfl, A.crossingOf_straight u⟩⟩
  · refine ⟨A.α u, h, Or.inr ⟨by rw [A.α_α], ?_⟩⟩
    rw [show u = A.α (A.α u) from (A.α_α u).symm, straight_α, A.crossingOf_σσ, A.α_α]

include hT in
/-- P1 geometry: if a curve `c` has a side on `T`, every swapped pair has an end on `c`. -/
theorem side_pair_meets {c : Fin n} (hc : ∃ y ∈ (A.cellOf d).darts, A.curve y = c) {u : D}
    (hu : u ∈ A.sideDarts d) :
    c ∈ Crossing.curves A (A.crossingOf u) ∨ c ∈ Crossing.curves A (A.crossingOf (A.straight u)) := by
  obtain ⟨y, hy, rfl⟩ := hc
  have hy' : A.cellOf y = A.cellOf d := Orbit.mem_darts.1 hy
  obtain ⟨b, hb, h⟩ := side_ends hT hu
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact tri_curve_cover hT hb hy'
  · exact (tri_curve_cover hT hb hy').symm

end Pca.FlipGraph
