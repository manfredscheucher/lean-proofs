/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# A flip of a triangle with a side on the new curve keeps the deletion (`doc/pca/great.md` 4.3)

The segment condition of `IsDeletion` says: the first return of `straight` to the old darts after
`ι d` is `ι (straight d)` (`del_hit`, `del_of_hit`). The flip conjugates `straight` by the
involution `ρ` swapping consecutive darts along the sides of the triangle; no side joins two old
crossings (the triangle has at most one corner without the new curve), so by `hit_swap` the first
returns do not change.
-/
import Pca.Great.Swp_Hit
import Pca.Great.AFlip

open Equiv Finset

namespace Pca.Great

variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] {n : ℕ}
  {A : Arrangement n D}

/-- The segment condition of a deletion for one dart. -/
def SegCond (B : Arrangement (n + 1) D') (A : Arrangement n D) (ι : D → D') (d : D) : Prop :=
  ∃ k : ℕ, (∀ i < k, Fin.last n ∈
      Arrangement.Crossing.curves B (B.crossingOf (B.α ((B.straight ^ i) (ι d))))) ∧
    ι (A.α d) = B.α ((B.straight ^ k) (ι d))

variable {B : Arrangement (n + 1) D'} {ι : D → D'}
  (hrange : ∀ y, (∃ d, ι d = y) ↔ Fin.last n ∉
    Arrangement.Crossing.curves B (B.crossingOf y))
  (hσ : ∀ d, ι (A.σ d) = B.σ (ι d))
include hrange hσ

theorem ι_σσ (d : D) : ι (A.σ (A.σ d)) = B.σ (B.σ (ι d)) := by rw [hσ, hσ]

theorem hit_of_segCond {d : D} (h : SegCond B A ι d) :
    ∃ j, Hit B.straight (fun y => ∃ e, ι e = y) (B.straight (ι d)) (ι (A.straight d)) j := by
  obtain ⟨k, hk, he⟩ := h
  refine ⟨k, ?_, ⟨_, rfl⟩, fun i hi => ?_⟩
  · rw [← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply, B.straight_apply, ← he,
      A.straight_apply, ι_σσ hrange hσ]
  · show ¬ ∃ e, ι e = (B.straight ^ i) (B.straight (ι d))
    rw [← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply, hrange,
      B.crossingOf_straight, not_not]
    exact hk i hi

theorem segCond_of_hit {d : D} {j : ℕ}
    (h : Hit B.straight (fun y => ∃ e, ι e = y) (B.straight (ι d)) (ι (A.straight d)) j) :
    SegCond B A ι d := by
  obtain ⟨h1, -, h3⟩ := h
  refine ⟨j, fun i hi => ?_, ?_⟩
  · have : ¬ ∃ e, ι e = (B.straight ^ i) (B.straight (ι d)) := h3 i hi
    rw [← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply, hrange,
      B.crossingOf_straight, not_not] at this
    exact this
  · rw [← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply, B.straight_apply,
      A.straight_apply, ι_σσ hrange hσ] at h1
    have h2 := congrArg (fun y => B.σ (B.σ y)) h1
    simp only [B.σ_σ_σ_σ] at h2
    exact h2.symm

end Pca.Great
