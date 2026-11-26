/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package M, helpers: the triangle flip on a sweep configuration

Port of `Pca/Flip.lean` (`Arrangement.flip`) to `SConf`, for a triangle `T = cellOf t` with the
side `t` on `S` (`MTri`). The construction is literally the same: same darts, same `σ`, same
labels, `α' = ρ α ρ` with the involution `ρ = swapAlong straight (sideDarts T)` (`mρ`); the cells
correspond through the maps `mG`, `mG'` (`flipG`, `flipG'` of `Pca/Flip.lean`) and the four
conditions `m_C1`-`m_C4`. The proofs follow `Pca/Flip.lean` line by line; the only change is
where the triangle facts N1-N3, O1, O2 come from (`Pca/Sweep/M_Tri.lean`: local arguments and a
parity argument with the side function instead of the arrangement axiom "intersecting").

New compared to `Pca/Flip.lean`: connectivity of the flipped map (`m_flip_connected`, every old
segment's ends stay connected) and the side function after the flip (`mSide'`, `m_flip_isSide`):
the side of the old cell, except that the flipped triangle `T'` moves to the other side of `S`.
-/
import Pca.Sweep.M_Tri

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- The six darts of the sides of `T = cellOf t`: its darts and their reverses. -/
def mSideDarts (Γ : SConf n D) (t : D) : Finset D :=
  univ.filter (fun y => Γ.cellOf y = Γ.cellOf t ∨ Γ.cellOf (Γ.α y) = Γ.cellOf t)

section Flip

variable {t : D} (hT : Γ.MTri t)

theorem m_mem_sideDarts {y : D} :
    y ∈ Γ.mSideDarts t ↔ Γ.cellOf y = Γ.cellOf t ∨ Γ.cellOf (Γ.α y) = Γ.cellOf t := by
  simp [mSideDarts]

theorem m_mem_sideDarts_α {y : D} : Γ.α y ∈ Γ.mSideDarts t ↔ y ∈ Γ.mSideDarts t := by
  rw [m_mem_sideDarts, m_mem_sideDarts, m_α_α, or_comm]

include hT in
theorem m_straight_not_mem_sideDarts :
    ∀ y ∈ Γ.mSideDarts t, Γ.straight y ∉ Γ.mSideDarts t := by
  intro y hy
  rw [m_mem_sideDarts] at hy ⊢
  rcases hy with hy | hy
  · rw [not_or]
    refine ⟨m_tri_straight_ne hT hy, fun h => ?_⟩
    exact m_not_corner_end_straight hT hy (m_isCorner_of_mem h)
  · rw [m_straight_apply, not_or]
    refine ⟨m_tri_σσ_ne hT hy, fun h => ?_⟩
    exact m_not_corner_end_σσ hT hy (m_isCorner_of_mem h)

/-- The involution `ρ`: it swaps each dart `y` of a side of `T` with `straight y`. -/
def mρ : Perm D :=
  Function.Involutive.toPerm _ (swapAlong_involutive (m_straight_not_mem_sideDarts hT))

theorem mρ_apply (y : D) : mρ hT y = swapAlong Γ.straight (Γ.mSideDarts t) y := rfl

theorem mρ_mρ (y : D) : mρ hT (mρ hT y) = y :=
  swapAlong_involutive (m_straight_not_mem_sideDarts hT) y

theorem mρ_of_mem {b : D} (hb : Γ.cellOf b = Γ.cellOf t) : mρ hT b = Γ.straight b := by
  rw [mρ_apply, swapAlong, if_pos (m_mem_sideDarts.2 (Or.inl hb))]

theorem mρ_α_of_mem {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    mρ hT (Γ.α b) = Γ.σ (Γ.σ b) := by
  rw [mρ_apply, swapAlong, if_pos (m_mem_sideDarts.2 (Or.inr (by rw [m_α_α, hb]))),
    m_straight_α]

theorem mρ_straight_of_mem {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    mρ hT (Γ.straight b) = b := by
  have hb' : b ∈ Γ.mSideDarts t := m_mem_sideDarts.2 (Or.inl hb)
  rw [mρ_apply, swapAlong, if_neg (m_straight_not_mem_sideDarts hT b hb'),
    Equiv.symm_apply_apply, if_pos hb']

theorem mρ_σσ_of_mem {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    mρ hT (Γ.σ (Γ.σ b)) = Γ.α b := by
  have hb' : Γ.α b ∈ Γ.mSideDarts t := m_mem_sideDarts.2 (Or.inr (by rw [m_α_α, hb]))
  have h := m_straight_not_mem_sideDarts hT _ hb'
  rw [m_straight_α] at h
  rw [mρ_apply, swapAlong, if_neg h, m_straight_symm_apply, Γ.m_σ4, if_pos hb']

theorem mρ_of_not_corner {y : D} (hy : ¬ Γ.MCorner t y) : mρ hT y = y := by
  have h1 : y ∉ Γ.mSideDarts t := by
    rw [m_mem_sideDarts, not_or]
    refine ⟨m_not_mem_of_not_corner hy, fun h => hy ?_⟩
    have := m_isCorner_α_of_mem h
    rwa [m_α_α] at this
  have h2 : Γ.straight.symm y ∉ Γ.mSideDarts t := by
    rw [m_straight_symm_apply, m_mem_sideDarts_α, m_mem_sideDarts, not_or]
    refine ⟨fun h => hy ?_, fun h => hy ?_⟩
    · have := m_isCorner_of_mem h
      rwa [m_isCorner_σσ] at this
    · have := m_isCorner_α_of_mem h
      rwa [m_α_α, m_isCorner_σσ] at this
  rw [mρ_apply, swapAlong, if_neg h1, if_neg h2]

/-- `ρ` commutes with `σ²`. -/
theorem mρ_σσ (y : D) : mρ hT (Γ.σ (Γ.σ y)) = Γ.σ (Γ.σ (mρ hT y)) := by
  have hdis := m_straight_not_mem_sideDarts hT
  simp only [mρ_apply, swapAlong]
  by_cases h1 : y ∈ Γ.mSideDarts t
  · have h2 : Γ.σ (Γ.σ y) ∉ Γ.mSideDarts t := by
      have := hdis _ (m_mem_sideDarts_α.2 h1)
      rwa [m_straight_α] at this
    rw [if_pos h1, if_neg h2, m_straight_symm_apply, Γ.m_σ4, if_pos (m_mem_sideDarts_α.2 h1),
      Γ.m_σσ_straight]
  · rw [if_neg h1]
    by_cases h3 : Γ.straight.symm y ∈ Γ.mSideDarts t
    · rw [if_pos h3]
      rw [m_straight_symm_apply] at h3 ⊢
      rw [if_pos (m_mem_sideDarts_α.1 h3), m_straight_apply, m_straight_symm_apply]
    · rw [if_neg h3]
      rw [m_straight_symm_apply] at h3
      have h4 : Γ.σ (Γ.σ y) ∉ Γ.mSideDarts t := fun h => h3 (m_mem_sideDarts_α.2 h)
      have h5 : Γ.straight.symm (Γ.σ (Γ.σ y)) ∉ Γ.mSideDarts t := by
        rw [m_straight_symm_apply, Γ.m_σ4, m_mem_sideDarts_α]; exact h1
      rw [if_neg h4, if_neg h5]

/-! ### Darts not in `T` -/

section NotMem

variable {b : D} (hb : Γ.cellOf b = Γ.cellOf t)
include hT hb

theorem m_ne_α : Γ.cellOf (Γ.α b) ≠ Γ.cellOf t := m_tri_α_ne hT hb

theorem m_ne_σσ : Γ.cellOf (Γ.σ (Γ.σ b)) ≠ Γ.cellOf t := m_tri_σσ_ne hT hb

theorem m_ne_straight : Γ.cellOf (Γ.straight b) ≠ Γ.cellOf t := m_tri_straight_ne hT hb

theorem m_ne_end_straight : Γ.cellOf (Γ.α (Γ.straight b)) ≠ Γ.cellOf t :=
  m_not_mem_of_not_corner (m_not_corner_end_straight hT hb)

theorem m_ne_end_σσ : Γ.cellOf (Γ.α (Γ.σ (Γ.σ b))) ≠ Γ.cellOf t :=
  m_not_mem_of_not_corner (m_not_corner_end_σσ hT hb)

end NotMem

include hT in
/-- Every dart is generic, an outer dart (the reverse of `straight b` or of `σ² b`), or a dart
at a corner. -/
theorem m_dart_cases (y : D) :
    (¬ Γ.MCorner t y ∧ ¬ Γ.MCorner t (Γ.α y)) ∨
    (∃ b, Γ.cellOf b = Γ.cellOf t ∧ (y = Γ.α (Γ.straight b) ∨ y = Γ.α (Γ.σ (Γ.σ b)))) ∨
    (∃ b, Γ.cellOf b = Γ.cellOf t ∧
      (y = b ∨ y = Γ.α b ∨ y = Γ.straight b ∨ y = Γ.σ (Γ.σ b))) := by
  by_cases hy : Γ.MCorner t y
  · exact Or.inr (Or.inr (m_corner_cases hT hy))
  by_cases hα : Γ.MCorner t (Γ.α y)
  · obtain ⟨b, hb, h | h | h | h⟩ := m_corner_cases hT hα
    · exact absurd (by rw [← Γ.m_α_α y, h]; exact m_isCorner_α_of_mem hb) hy
    · exact absurd (by rw [← Γ.m_α_α y, h, m_α_α]; exact m_isCorner_of_mem hb) hy
    · exact Or.inr (Or.inl ⟨b, hb, Or.inl (by rw [← h, m_α_α])⟩)
    · exact Or.inr (Or.inl ⟨b, hb, Or.inr (by rw [← h, m_α_α])⟩)
  · exact Or.inl ⟨hy, hα⟩

/-! ### The flipped edge involution `α' = ρ α ρ` -/

/-- The edge involution after the flip. -/
def mα : Perm D := mρ hT * Γ.α * mρ hT

theorem mα_apply (y : D) : mα hT y = mρ hT (Γ.α (mρ hT y)) := rfl

theorem m_curve_ρ (y : D) : Γ.curve (mρ hT y) = Γ.curve y := by
  rw [mρ_apply, swapAlong]
  split_ifs
  · exact Γ.m_curve_straight y
  · rw [← Γ.m_curve_straight (Γ.straight.symm y), Equiv.apply_symm_apply]
  · rfl

/-! ### The flipped face permutation `φ' = σ α'` near `T` -/

section FaceValues

variable {b : D} (hb : Γ.cellOf b = Γ.cellOf t)
include hb

theorem m_φ'_of_mem : (Γ.σ * mα hT) b = Γ.φ (Γ.straight b) := by
  rw [Perm.mul_apply, mα_apply, mρ_of_mem hT hb,
    mρ_of_not_corner hT (m_not_corner_end_straight hT hb), m_φ_apply]

theorem m_φ'_α : (Γ.σ * mα hT) (Γ.α b) = Γ.φ (Γ.σ (Γ.σ b)) := by
  rw [Perm.mul_apply, mα_apply, mρ_α_of_mem hT hb,
    mρ_of_not_corner hT (m_not_corner_end_σσ hT hb), m_φ_apply]

theorem m_φ'_straight : (Γ.σ * mα hT) (Γ.straight b) = Γ.σ (Γ.σ (Γ.σ b)) := by
  rw [Perm.mul_apply, mα_apply, mρ_straight_of_mem hT hb, mρ_α_of_mem hT hb]

theorem m_φ'_σσ : (Γ.σ * mα hT) (Γ.σ (Γ.σ b)) = Γ.σ (Γ.σ (Γ.φ b)) := by
  rw [Perm.mul_apply, mα_apply, mρ_σσ_of_mem hT hb, m_α_α, mρ_of_mem hT hb,
    m_straight_apply, m_φ_apply]

theorem m_φ'_end_straight : (Γ.σ * mα hT) (Γ.α (Γ.straight b)) = Γ.σ b := by
  rw [Perm.mul_apply, mα_apply, mρ_of_not_corner hT (m_not_corner_end_straight hT hb), m_α_α,
    mρ_straight_of_mem hT hb]

theorem m_φ'_end_σσ : (Γ.σ * mα hT) (Γ.α (Γ.σ (Γ.σ b))) = Γ.φ b := by
  rw [Perm.mul_apply, mα_apply, mρ_of_not_corner hT (m_not_corner_end_σσ hT hb), m_α_α,
    mρ_σσ_of_mem hT hb, m_φ_apply]

end FaceValues

theorem m_φ'_generic {y : D} (hy : ¬ Γ.MCorner t y) (hα : ¬ Γ.MCorner t (Γ.α y)) :
    (Γ.σ * mα hT) y = Γ.φ y := by
  rw [Perm.mul_apply, mα_apply, mρ_of_not_corner hT hy, mρ_of_not_corner hT hα, m_φ_apply]

/-! ### Corresponding darts -/

/-- Old dart ↦ a dart of the corresponding cell after the flip (`flipG` of `Pca/Flip.lean`). -/
def mG (Γ : SConf n D) (t y : D) : D :=
  if Γ.cellOf y = Γ.cellOf t then Γ.σ (Γ.σ y)
  else if Γ.cellOf (Γ.α y) = Γ.cellOf t then Γ.φ (Γ.φ (Γ.α y))
  else if Γ.cellOf (Γ.α (Γ.σ (Γ.σ y))) = Γ.cellOf t ∨ Γ.cellOf (Γ.σ (Γ.σ y)) = Γ.cellOf t then
    Γ.α (Γ.σ (Γ.σ y))
  else y

/-- New dart ↦ a dart of the corresponding old cell (`flipG'` of `Pca/Flip.lean`). -/
def mG' (Γ : SConf n D) (t y : D) : D :=
  if Γ.cellOf (Γ.σ (Γ.σ y)) = Γ.cellOf t then Γ.σ (Γ.σ y)
  else if Γ.cellOf y = Γ.cellOf t ∨ Γ.cellOf (Γ.α y) = Γ.cellOf t then Γ.σ (Γ.σ (Γ.α y))
  else if Γ.cellOf (Γ.α (Γ.σ (Γ.σ y))) = Γ.cellOf t then
    Γ.σ (Γ.σ (Γ.φ (Γ.φ (Γ.α (Γ.σ (Γ.σ y))))))
  else y

section Eval

variable {b : D} (hb : Γ.cellOf b = Γ.cellOf t)
include hb

theorem mG_of_mem : mG Γ t b = Γ.σ (Γ.σ b) := by rw [mG, if_pos hb]

include hT

theorem mG_α : mG Γ t (Γ.α b) = Γ.φ (Γ.φ b) := by
  rw [mG, if_neg (m_ne_α hT hb), if_pos (by rw [m_α_α]; exact hb), m_α_α]

theorem mG_straight : mG Γ t (Γ.straight b) = b := by
  rw [mG, if_neg (m_ne_straight hT hb), if_neg (m_ne_end_straight hT hb),
    if_pos (Or.inl (by rw [Γ.m_σσ_straight, m_α_α]; exact hb)), Γ.m_σσ_straight, m_α_α]

theorem mG_σσ : mG Γ t (Γ.σ (Γ.σ b)) = Γ.α b := by
  rw [mG, if_neg (m_ne_σσ hT hb), if_neg (m_ne_end_σσ hT hb),
    if_pos (Or.inr (by rw [Γ.m_σ4]; exact hb)), Γ.m_σ4]

omit hT in
theorem mG'_σσ : mG' Γ t (Γ.σ (Γ.σ b)) = b := by
  rw [mG', if_pos (by rw [Γ.m_σ4]; exact hb), Γ.m_σ4]

theorem mG'_of_mem : mG' Γ t b = Γ.straight b := by
  rw [mG', if_neg (m_ne_σσ hT hb), if_pos (Or.inl hb), m_straight_apply]

theorem mG'_α : mG' Γ t (Γ.α b) = Γ.σ (Γ.σ b) := by
  rw [mG', if_neg (show ¬ Γ.cellOf (Γ.σ (Γ.σ (Γ.α b))) = Γ.cellOf t from m_ne_straight hT hb),
    if_pos (Or.inr (by rw [m_α_α]; exact hb)), m_α_α]

theorem mG'_straight : mG' Γ t (Γ.straight b) = Γ.σ (Γ.σ (Γ.φ (Γ.φ b))) := by
  rw [mG', Γ.m_σσ_straight, if_neg (m_ne_α hT hb),
    if_neg (not_or.2 ⟨m_ne_straight hT hb, m_ne_end_straight hT hb⟩),
    if_pos (by rw [m_α_α]; exact hb), m_α_α]

end Eval

theorem mG_of_not_corner {y : D} (hy : ¬ Γ.MCorner t y) : mG Γ t y = y := by
  have h1 := m_not_mem_of_not_corner hy
  have h2 : Γ.cellOf (Γ.α y) ≠ Γ.cellOf t := fun h => hy (by
    have := m_isCorner_α_of_mem h; rwa [m_α_α] at this)
  have h3 : ¬ (Γ.cellOf (Γ.α (Γ.σ (Γ.σ y))) = Γ.cellOf t ∨
      Γ.cellOf (Γ.σ (Γ.σ y)) = Γ.cellOf t) := by
    rintro (h | h)
    · have := m_isCorner_α_of_mem h; rw [m_α_α, m_isCorner_σσ] at this; exact hy this
    · have := m_isCorner_of_mem h; rw [m_isCorner_σσ] at this; exact hy this
  rw [mG, if_neg h1, if_neg h2, if_neg h3]

theorem mG'_of_not_corner {y : D} (hy : ¬ Γ.MCorner t y) : mG' Γ t y = y := by
  have h1 : Γ.cellOf (Γ.σ (Γ.σ y)) ≠ Γ.cellOf t := fun h => hy (by
    have := m_isCorner_of_mem h; rwa [m_isCorner_σσ] at this)
  have h2 : ¬ (Γ.cellOf y = Γ.cellOf t ∨ Γ.cellOf (Γ.α y) = Γ.cellOf t) := by
    rintro (h | h)
    · exact hy (m_isCorner_of_mem h)
    · have := m_isCorner_α_of_mem h; rw [m_α_α] at this; exact hy this
  have h3 : Γ.cellOf (Γ.α (Γ.σ (Γ.σ y))) ≠ Γ.cellOf t := fun h => hy (by
    have := m_isCorner_α_of_mem h; rwa [m_α_α, m_isCorner_σσ] at this)
  rw [mG', if_neg h1, if_neg h2, if_neg h3]

/-! ### The four correspondence conditions -/

theorem m_C1 (y : D) : (Γ.σ * mα hT).SameCycle (mG Γ t y) (mG Γ t (Γ.φ y)) := by
  rcases m_dart_cases hT y with ⟨hy, hα⟩ | ⟨b, hb, h | h⟩ | ⟨b, hb, h | h | h | h⟩
  · rw [mG_of_not_corner hy, mG_of_not_corner (m_isCorner_φ.not.2 hα),
      ← m_φ'_generic hT hy hα]
    exact sameCycle_self_apply _ _
  all_goals subst y
  all_goals
    have hφb : Γ.cellOf (Γ.φ b) = Γ.cellOf t := m_tri_φ hb
    have hφφb : Γ.cellOf (Γ.φ (Γ.φ b)) = Γ.cellOf t := m_tri_φφ hb
  · -- `y = α (straight b)`
    have e1 : Γ.φ (Γ.α (Γ.straight b)) = Γ.σ (Γ.σ (Γ.φ b)) := by
      rw [m_φ_apply, m_α_α, m_straight_apply, m_φ_apply]
    have e2 : (Γ.σ * mα hT) (Γ.α (Γ.straight b)) = Γ.straight (Γ.φ (Γ.φ b)) := by
      rw [m_φ'_end_straight hT hb, m_tri_σ hT hb]
    have e3 : (Γ.σ * mα hT) (Γ.straight (Γ.φ (Γ.φ b))) = Γ.α (Γ.φ b) := by
      rw [m_φ'_straight hT hφφb, m_tri_σσσ hT hφφb, m_tri_φφφ hT hφb]
    rw [mG_of_not_corner (m_not_corner_end_straight hT hb), e1, mG_σσ hT hφb]
    have := sameCycle_two (Γ.σ * mα hT) (Γ.α (Γ.straight b))
    rwa [e2, e3] at this
  · -- `y = α (σ² b)`
    rw [mG_of_not_corner (m_not_corner_end_σσ hT hb), m_φ_apply, m_α_α, m_tri_σσσ hT hb,
      mG_α hT hφφb, m_tri_φφφ hT hφb, ← m_φ'_end_σσ hT hb]
    exact sameCycle_self_apply _ _
  · -- `y = b`
    rw [mG_of_mem hb, mG_of_mem hφb, ← m_φ'_σσ hT hb]
    exact sameCycle_self_apply _ _
  · -- `y = α b`
    rw [mG_α hT hb, m_φ_α, m_tri_σ hT hb, mG_straight hT hφφb]
  · -- `y = straight b`
    have hnc : ¬ Γ.MCorner t (Γ.φ (Γ.straight b)) := by
      rw [m_isCorner_φ]; exact m_not_corner_end_straight hT hb
    rw [mG_straight hT hb, mG_of_not_corner hnc, ← m_φ'_of_mem hT hb]
    exact sameCycle_self_apply _ _
  · -- `y = σ² b`
    have hnc : ¬ Γ.MCorner t (Γ.φ (Γ.σ (Γ.σ b))) := by
      rw [m_isCorner_φ]; exact m_not_corner_end_σσ hT hb
    rw [mG_σσ hT hb, mG_of_not_corner hnc, ← m_φ'_α hT hb]
    exact sameCycle_self_apply _ _

theorem m_C2 (y : D) :
    Γ.φ.SameCycle (mG' Γ t y) (mG' Γ t ((Γ.σ * mα hT) y)) := by
  rcases m_dart_cases hT y with ⟨hy, hα⟩ | ⟨b, hb, h | h⟩ | ⟨b, hb, h | h | h | h⟩
  · rw [m_φ'_generic hT hy hα, mG'_of_not_corner hy,
      mG'_of_not_corner (m_isCorner_φ.not.2 hα)]
    exact sameCycle_self_apply _ _
  all_goals subst y
  all_goals
    have hφb : Γ.cellOf (Γ.φ b) = Γ.cellOf t := m_tri_φ hb
    have hφφb : Γ.cellOf (Γ.φ (Γ.φ b)) = Γ.cellOf t := m_tri_φφ hb
  · -- `y = α (straight b)`
    have e1 : Γ.φ (Γ.α (Γ.straight b)) = Γ.σ (Γ.σ (Γ.φ b)) := by
      rw [m_φ_apply, m_α_α, m_straight_apply, m_φ_apply]
    rw [mG'_of_not_corner (m_not_corner_end_straight hT hb), m_φ'_end_straight hT hb,
      m_tri_σ hT hb, mG'_straight hT hφφb, m_tri_φφφ hT hφb, ← e1]
    exact sameCycle_self_apply _ _
  · -- `y = α (σ² b)`
    have e1 : Γ.φ (Γ.φ (Γ.α (Γ.σ (Γ.σ b)))) = Γ.straight (Γ.φ b) := by
      rw [Γ.m_φ_apply (Γ.α _), m_α_α, m_tri_σσσ hT hb, m_φ_α, m_tri_σ hT hφφb,
        m_tri_φφφ hT hφb]
    rw [mG'_of_not_corner (m_not_corner_end_σσ hT hb), m_φ'_end_σσ hT hb,
      mG'_of_mem hT hφb, ← e1]
    exact sameCycle_two _ _
  · -- `y = b`
    have hnc : ¬ Γ.MCorner t (Γ.φ (Γ.straight b)) := by
      rw [m_isCorner_φ]; exact m_not_corner_end_straight hT hb
    rw [mG'_of_mem hT hb, m_φ'_of_mem hT hb, mG'_of_not_corner hnc]
    exact sameCycle_self_apply _ _
  · -- `y = α b`
    have hnc : ¬ Γ.MCorner t (Γ.φ (Γ.σ (Γ.σ b))) := by
      rw [m_isCorner_φ]; exact m_not_corner_end_σσ hT hb
    rw [mG'_α hT hb, m_φ'_α hT hb, mG'_of_not_corner hnc]
    exact sameCycle_self_apply _ _
  · -- `y = straight b`
    rw [mG'_straight hT hb, m_φ'_straight hT hb, m_tri_σσσ hT hb, mG'_α hT hφφb]
  · -- `y = σ² b`
    rw [mG'_σσ hb, m_φ'_σσ hT hb, mG'_σσ hφb]
    exact sameCycle_self_apply _ _

include hT in
theorem m_C3 (y : D) : Γ.φ.SameCycle y (mG' Γ t (mG Γ t y)) := by
  by_cases hy : Γ.MCorner t y
  · obtain ⟨b, hb, h | h | h | h⟩ := m_corner_cases hT hy
    all_goals subst y
    · rw [mG_of_mem hb, mG'_σσ hb]
    · have hφφb : Γ.cellOf (Γ.φ (Γ.φ b)) = Γ.cellOf t := m_tri_φφ hb
      rw [mG_α hT hb, mG'_of_mem hT hφφb, ← m_tri_σ hT hb, ← m_φ_α]
      exact sameCycle_self_apply _ _
    · rw [mG_straight hT hb, mG'_of_mem hT hb]
    · rw [mG_σσ hT hb, mG'_α hT hb]
  · rw [mG_of_not_corner hy, mG'_of_not_corner hy]

theorem m_C4 (y : D) : (Γ.σ * mα hT).SameCycle y (mG Γ t (mG' Γ t y)) := by
  by_cases hy : Γ.MCorner t y
  · obtain ⟨b, hb, h | h | h | h⟩ := m_corner_cases hT hy
    all_goals subst y
    · rw [mG'_of_mem hT hb, mG_straight hT hb]
    · rw [mG'_α hT hb, mG_σσ hT hb]
    · have hφφb : Γ.cellOf (Γ.φ (Γ.φ b)) = Γ.cellOf t := m_tri_φφ hb
      rw [mG'_straight hT hb, mG_σσ hT hφφb, ← m_tri_σσσ hT hb, ← m_φ'_straight hT hb]
      exact sameCycle_self_apply _ _
    · rw [mG'_σσ hb, mG_of_mem hb]
  · rw [mG'_of_not_corner hy, mG_of_not_corner hy]

/-- The cells before and after the flip correspond (`flipCellEquivRaw`). -/
def mCellEquiv : Orbit Γ.φ ≃ Orbit (Γ.σ * mα hT) :=
  orbitEquiv (mG Γ t) (mG' Γ t) (m_C1 hT) (m_C2 hT) (m_C3 hT) (m_C4 hT)

theorem mCellEquiv_symm_mk (y : D) :
    (mCellEquiv hT).symm (Orbit.mk (Γ.σ * mα hT) y) = Γ.cellOf (mG' Γ t y) := rfl

/-- The segments before and after the flip correspond (via `ρ`). -/
def mSegEquiv : Orbit Γ.α ≃ Orbit (mα hT) :=
  orbitEquiv (mρ hT) (mρ hT)
    (fun y => by
      have h : mα hT (mρ hT y) = mρ hT (Γ.α y) := by rw [mα_apply, mρ_mρ]
      rw [← h]; exact sameCycle_self_apply _ _)
    (fun y => by
      have h : mρ hT (mα hT y) = Γ.α (mρ hT y) := by rw [mα_apply, mρ_mρ]
      rw [h]; exact sameCycle_self_apply _ _)
    (fun y => by rw [mρ_mρ])
    (fun y => by rw [mρ_mρ])

theorem m_flip_straightPerm (y : D) :
    straightPerm Γ.σ (mα hT) y = mρ hT (Γ.straight (mρ hT y)) := by
  show Γ.σ (Γ.σ (mα hT y)) = _
  rw [mα_apply, ← mρ_σσ, m_straight_apply]

end Flip

end SConf

end Pca.Sweep
