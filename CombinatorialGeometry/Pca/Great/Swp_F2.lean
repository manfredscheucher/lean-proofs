/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The sweep: passing cells (`doc/pca/great.md` 4.4)

`PassAt B ι d`: the first piece of the segment of `ι d` ends on the new curve. A dart that is
not passed keeps its segment (`unpassed_α`). Flips away from a witness keep it (`passAt_flip`);
a cell not passed stays not passed under a flip away from its corners (`unpassed_flip`); a cell
not passed with a corner at the old corner of the flipped triangle becomes passed (`passAt_apex`).
-/
import Pca.Great.Swp_Del2

open Equiv Finset

namespace Pca.Great

variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] {n : ℕ}
  {A : Arrangement n D} {B : Arrangement (n + 1) D'} {ι : D → D'}

/-- The segment of `ι d` is cut by the new curve right away. -/
def PassAt (B : Arrangement (n + 1) D') (ι : D → D') (d : D) : Prop :=
  Fin.last n ∈ Arrangement.Crossing.curves B (B.crossingOf (B.α (ι d)))

theorem passes_iff {f : A.Cell} : Passes B ι f ↔ ∃ d ∈ f.darts, PassAt B ι d := Iff.rfl

variable (hD : IsDeletion B A ι)
include hD

theorem unpassed_α {d : D} (h : ¬ PassAt B ι d) : B.α (ι d) = ι (A.α d) := by
  obtain ⟨k, hk, he⟩ := hD.α d
  rcases k with _ | k
  · exact he.symm
  · exact absurd (hk 0 (by omega)) h

theorem unpassed_φ {d : D} (h : ¬ PassAt B ι d) : B.φ (ι d) = ι (A.φ d) := by
  rw [B.φ_apply, unpassed_α hD h, ← hD.σ]; rfl

theorem old_crossing (d : D) : Fin.last n ∉ Arrangement.Crossing.curves B (B.crossingOf (ι d)) :=
  (hD.range _).1 ⟨d, rfl⟩

omit hD in
theorem passAt_flip {t : D'} (hT : B.IsTriangle (B.cellOf t)) {d : D} (h : PassAt B ι d)
    (h1 : ¬ B.IsCorner t (ι d)) (h2 : ¬ B.IsCorner t (B.α (ι d))) : PassAt (B.flip t hT) ι d := by
  show Fin.last n ∈ Arrangement.Crossing.curves B (B.crossingOf (Arrangement.flipα hT (ι d)))
  rw [Arrangement.flipα_apply, Arrangement.flipρ_of_not_corner hT h1,
    Arrangement.flipρ_of_not_corner hT h2]
  exact h

/-- A cell not passed stays not passed under a flip away from its corners. -/
theorem unpassed_flip {t : D'} (hT : B.IsTriangle (B.cellOf t)) {f : A.Cell}
    (hf : ∀ d ∈ f.darts, ¬ PassAt B ι d)
    (hc : ∀ d ∈ f.darts, B.crossingOf (ι d) ∉ Arrangement.Cell.corners B (B.cellOf t)) :
    ∀ d ∈ f.darts, ¬ PassAt (B.flip t hT) ι d := by
  intro d hd
  have h1 : ¬ B.IsCorner t (ι d) := hc d hd
  have hφ : A.φ d ∈ f.darts := by
    rw [Orbit.mem_darts] at hd ⊢; rw [← hd]; exact A.cellOf_φ d
  have h2 : ¬ B.IsCorner t (B.α (ι d)) := by
    intro h
    apply hc _ hφ
    rw [← unpassed_φ hD (hf d hd), B.crossingOf_φ]; exact h
  show ¬ Fin.last n ∈ Arrangement.Crossing.curves B (B.crossingOf (Arrangement.flipα hT (ι d)))
  rw [Arrangement.flipα_apply, Arrangement.flipρ_of_not_corner hT h1,
    Arrangement.flipρ_of_not_corner hT h2]
  exact hf d hd

/-- **The old corner of a flipped triangle**: a cell not passed with a corner there becomes
passed. -/
theorem passAt_apex {t : D'} (hT : B.IsTriangle (B.cellOf t))
    (hL : Fin.last n ∈ Arrangement.Cell.curves B (B.cellOf t)) {f : A.Cell}
    (hf : ∀ d ∈ f.darts, ¬ PassAt B ι d) {d₀ : D} (hd₀ : d₀ ∈ f.darts)
    (hx : B.crossingOf (ι d₀) ∈ Arrangement.Cell.corners B (B.cellOf t)) :
    PassAt (B.flip t hT) ι d₀ ∧
      B.crossingOf ((B.flip t hT).α (ι d₀)) ∈ Arrangement.Cell.corners B (B.cellOf t) := by
  obtain ⟨g, hg, hgx⟩ := mem_image.1 hx
  have hgT : B.cellOf g = B.cellOf t := Orbit.mem_darts.1 hg
  have hTg := Arrangement.isTriangle_of hT hgT
  have hold := old_crossing hD d₀
  -- the corner at the end of the side of `g` is on the new curve
  have hαg : Fin.last n ∈ Arrangement.Crossing.curves B (B.crossingOf (B.α g)) := by
    rcases two_corners hT hL (Arrangement.isCorner_α_of_mem (A := B) hgT) hx
      (by rw [← hgx]; exact tri_cross_ne hTg) with h | h
    · exact h
    · exact absurd h hold
  have hl := B.crossingOf_eq_iff.1 hgx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h
  · -- `ι d₀ = g`
    exact absurd (by rw [PassAt, h]; exact hαg) (hf d₀ hd₀)
  · -- `ι d₀ = σ g`: its cell contains `α g`, which is not old
    exfalso
    have hcell : ∀ k : ℕ, ∃ d ∈ f.darts, (B.φ ^ k) (ι d₀) = ι d := by
      intro k
      induction k with
      | zero => exact ⟨d₀, hd₀, rfl⟩
      | succ k ih =>
        obtain ⟨d, hd, hk⟩ := ih
        refine ⟨A.φ d, ?_, ?_⟩
        · rw [Orbit.mem_darts] at hd ⊢; rw [← hd]; exact A.cellOf_φ d
        · rw [pow_succ', Perm.mul_apply, hk, unpassed_φ hD (hf d hd)]
    have hsc : B.φ.SameCycle (ι d₀) (B.α g) := by
      rw [← B.cellOf_eq_iff, h, B.cellOf_σ]
    obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
    obtain ⟨d, -, hd⟩ := hcell k
    rw [hk] at hd
    exact old_crossing hD d (by rw [← hd]; exact hαg)
  · -- `ι d₀ = σ² g`: the new segment ends on the new curve
    refine ⟨?_, ?_⟩
    · show Fin.last n ∈ Arrangement.Crossing.curves B
        (B.crossingOf (Arrangement.flipα hT (ι d₀)))
      rw [Arrangement.flipα_apply, h, Arrangement.flipρ_σσ_of_mem hT hgT,
        B.isArrangement.α_α, Arrangement.flipρ_of_mem hT hgT, B.crossingOf_straight]
      exact hαg
    · show B.crossingOf (Arrangement.flipα hT (ι d₀)) ∈ _
      rw [Arrangement.flipα_apply, h, Arrangement.flipρ_σσ_of_mem hT hgT,
        B.isArrangement.α_α, Arrangement.flipρ_of_mem hT hgT, B.crossingOf_straight]
      exact Arrangement.isCorner_α_of_mem (A := B) hgT
  · -- `ι d₀ = σ³ g = α (φ² g)`
    exfalso
    rw [Arrangement.tri_σσσ hTg] at h
    have hφφ : B.cellOf (B.φ (B.φ g)) = B.cellOf t := by rw [B.cellOf_φ, B.cellOf_φ, hgT]
    have hne : B.crossingOf (B.φ (B.φ g)) ≠ B.crossingOf (ι d₀) := by
      rw [h]; exact (tri_cross_ne (Arrangement.isTriangle_of hT hφφ)).symm
    rcases two_corners hT hL (Arrangement.isCorner_of_mem (A := B) hφφ) hx hne with h' | h'
    · apply hf d₀ hd₀
      show Fin.last n ∈ Arrangement.Crossing.curves B (B.crossingOf (B.α (ι d₀)))
      rw [h, B.isArrangement.α_α]; exact h'
    · exact hold h'

end Pca.Great
