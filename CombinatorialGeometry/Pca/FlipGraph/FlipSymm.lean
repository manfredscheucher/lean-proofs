/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): flipping the flipped triangle gives back the arrangement

Let `A' = A.flip d hT` and `T'` the flipped triangle (the cell of `σ² d` in `A'`). The involution
`ρ'` of the second flip equals `ρ` (on the darts `σ² b`, `straight b` of the sides of `T'` it
swaps along the new straight walk exactly as `ρ` does), hence `α'' = ρ ρ α ρ ρ = α`
(`flip_flip`). The cells correspond back: `Φ' (Φ (cellOf y)) = cellOf y` (`flip_flip_cellOf`).
-/
import Pca.FlipGraph.Basic

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement

variable {A : Arrangement n D} {d : D} (hT : A.IsTriangle (A.cellOf d))

/-- The flipped triangle is a triangle of the flipped arrangement. -/
theorem flip_tri' : (A.flip d hT).IsTriangle ((A.flip d hT).cellOf (A.σ (A.σ d))) :=
  flip_isTriangle hT

section

variable {b : D} (hb : A.cellOf b = A.cellOf d)
include hb

theorem flip_cellOf_σσ_mem :
    (A.flip d hT).cellOf (A.σ (A.σ b)) = (A.flip d hT).cellOf (A.σ (A.σ d)) := by
  rw [flip_cellOf, flipG'_σσ hb, hb, flip_cellOf, flipG'_σσ rfl]

theorem flip_α_σσ : (A.flip d hT).α (A.σ (A.σ b)) = A.straight b := by
  rw [flip_α, flipα_apply, flipρ_σσ_of_mem hT hb, α_α, flipρ_of_mem hT hb]

theorem flip_straight_σσ : (A.flip d hT).straight (A.σ (A.σ b)) = A.α b := by
  change straightPerm A.σ (flipα hT) _ = _
  rw [flip_straightPerm, flipρ_σσ_of_mem hT hb, straight_α, flipρ_σσ_of_mem hT hb]

theorem flip_φ_σσ : (A.flip d hT).φ (A.σ (A.σ b)) = A.σ (A.σ (A.φ b)) := by
  rw [flip_φ]; exact flipφ_σσ hT hb

end

theorem flip_isCorner_iff (w : D) :
    (A.flip d hT).IsCorner (A.σ (A.σ d)) w ↔ A.IsCorner d w := by
  unfold IsCorner Cell.corners
  rw [flip_darts_triangle, image_image]
  simp only [Function.comp_def, flip_crossingOf, crossingOf_σσ]
  exact Iff.rfl

/-- The reverse correspondence of the second flip, followed by that of the first, keeps cells. -/
theorem flipG'_flipG' (w : D) :
    A.cellOf (flipG' A d (flipG' (A.flip d hT) (A.σ (A.σ d)) w)) = A.cellOf w := by
  have hT' := flip_tri' hT
  by_cases hw : A.IsCorner d w
  · obtain ⟨b, hb, h | h | h | h⟩ := corner_cases hT hw
    · -- `w = b = σ² (σ² b)`
      subst h
      have h1 := flipG'_σσ (A := A.flip d hT) (flip_cellOf_σσ_mem hT hb)
      rw [flip_σ, A.σ_σ_σ_σ] at h1
      rw [h1, flipG'_σσ hb]
    · -- `w = α b = straight' (σ² b)`
      subst h
      have hφb : A.cellOf (A.φ b) = A.cellOf d := by rw [A.cellOf_φ, hb]
      have hφφb : A.cellOf (A.φ (A.φ b)) = A.cellOf d := by rw [A.cellOf_φ, hφb]
      have h1 := flipG'_straight hT' (flip_cellOf_σσ_mem hT hb)
      rw [flip_straight_σσ hT hb, flip_φ_σσ hT hb, flip_φ_σσ hT hφb, flip_σ, A.σ_σ_σ_σ] at h1
      rw [h1, flipG'_of_mem hT hφφb, ← tri_σ (hb ▸ hT), A.cellOf_σ]
    · -- `w = straight b = α' (σ² b)`
      subst h
      have h1 := flipG'_α hT' (flip_cellOf_σσ_mem hT hb)
      rw [flip_α_σσ hT hb, flip_σ, A.σ_σ_σ_σ] at h1
      rw [h1, flipG'_of_mem hT hb]
    · -- `w = σ² b`
      subst h
      have h1 := flipG'_of_mem hT' (flip_cellOf_σσ_mem hT hb)
      rw [flip_straight_σσ hT hb] at h1
      rw [h1, flipG'_α hT hb]
  · have hw' : ¬ (A.flip d hT).IsCorner (A.σ (A.σ d)) w := by rwa [flip_isCorner_iff]
    rw [flipG'_of_not_corner hw', flipG'_of_not_corner hw]

/-- The involution of the second flip is the involution of the first. -/
theorem flipρ_flip (y : D) : flipρ (flip_tri' hT) y = flipρ hT y := by
  have hT' := flip_tri' hT
  by_cases hy : A.IsCorner d y
  · obtain ⟨b, hb, h | h | h | h⟩ := corner_cases hT hy
    · -- `b = straight' (straight b)`, `straight b ∈ sideDarts'`
      subst h
      have hb' := flip_cellOf_σσ_mem hT hb
      have h1 := flipρ_α_of_mem hT' hb'
      rw [flip_α_σσ hT hb] at h1
      -- `ρ' (straight b) = σ² σ² b = b`, so `ρ' b = straight b`
      rw [flip_σ, A.σ_σ_σ_σ] at h1
      have h2 := congrArg (flipρ hT') h1
      rw [flipρ_flipρ] at h2
      rw [flipρ_of_mem hT hb, ← h2]
    · subst h
      have h1 := flipρ_straight_of_mem hT' (flip_cellOf_σσ_mem hT hb)
      rw [flip_straight_σσ hT hb] at h1
      rw [h1, flipρ_α_of_mem hT hb]
    · subst h
      have h1 := flipρ_α_of_mem hT' (flip_cellOf_σσ_mem hT hb)
      rw [flip_α_σσ hT hb, flip_σ, A.σ_σ_σ_σ] at h1
      rw [h1, flipρ_straight_of_mem hT hb]
    · subst h
      have h1 := flipρ_of_mem hT' (flip_cellOf_σσ_mem hT hb)
      rw [flip_straight_σσ hT hb] at h1
      rw [h1, flipρ_σσ_of_mem hT hb]
  · have hy' : ¬ (A.flip d hT).IsCorner (A.σ (A.σ d)) y := by rwa [flip_isCorner_iff]
    rw [flipρ_of_not_corner hT' hy', flipρ_of_not_corner hT hy]

/-- **Flipping the flipped triangle gives back the arrangement.** -/
theorem flip_flip : (A.flip d hT).flip (A.σ (A.σ d)) (flip_tri' hT) = A := by
  obtain ⟨σ, α, curve, h⟩ := A
  have hα : flipα (flip_tri' hT) = α := by
    ext y
    rw [flipα_apply, flipρ_flip, flip_α, flipα_apply, flipρ_flipρ, flipρ_flip, flipρ_flipρ]
  simp only [Arrangement.flip, Arrangement.mk.injEq, true_and]
  exact ⟨hα, trivial⟩

/-- The cells correspond back after the second flip. -/
theorem flip_flip_cellOf (y : D) :
    ((A.flip d hT).flip (A.σ (A.σ d)) (flip_tri' hT)).cellOf y =
      flipCellEquiv (flip_tri' hT) (flipCellEquiv hT (A.cellOf y)) := by
  rw [flip_cellOf, flip_cellOf, ← flipG'_flipG' hT y]

end Pca.FlipGraph
