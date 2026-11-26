/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package M, helpers: rewriting lemmas for sweep configurations

Basic facts on `SConf` (axioms 1-5 and the side function only), in the form used by the moves
(`Pca/Sweep/Moves.lean`). They are the `SConf` versions of the rewriting lemmas of
`Pca/Digon.lean` and `Pca/Excess.lean` (prefix `m_`, to keep the shared namespace free).
-/
import Pca.Sweep.Basic
import Pca.Flip

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

theorem m_zmod2_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide

theorem m_zmod2_eq_add_of_add_eq {a b c : ZMod 2} (h : a + b = c) : b = a + c := by
  subst h; rw [← add_assoc, m_zmod2_add_self, zero_add]

/-! ## Rewriting lemmas -/

theorem m_straight_apply (y : D) : Γ.straight y = Γ.σ (Γ.σ (Γ.α y)) := rfl

theorem m_φ_apply (y : D) : Γ.φ y = Γ.σ (Γ.α y) := rfl

theorem m_α_α (y : D) : Γ.α (Γ.α y) = y := Γ.isSConf.α_α y

theorem m_α_ne (y : D) : Γ.α y ≠ y := Γ.isSConf.α_ne y

theorem m_curve_α (y : D) : Γ.curve (Γ.α y) = Γ.curve y := Γ.isSConf.curve_α y

theorem m_curve_σσ (y : D) : Γ.curve (Γ.σ (Γ.σ y)) = Γ.curve y := Γ.isSConf.curve_σσ y

theorem m_curve_σ (y : D) : Γ.curve (Γ.σ y) ≠ Γ.curve y := Γ.isSConf.curve_σ y

theorem m_curve_straight (y : D) : Γ.curve (Γ.straight y) = Γ.curve y := by
  rw [m_straight_apply, m_curve_σσ, m_curve_α]

theorem m_period_σ (y : D) : period Γ.σ y = 4 := by
  rw [← card_orbitFinset]; exact Γ.isSConf.card_crossing y

theorem m_σ4 (y : D) : Γ.σ (Γ.σ (Γ.σ (Γ.σ y))) = y := by
  have h := iterate_period Γ.σ y
  rw [Γ.m_period_σ] at h
  simpa using h

theorem m_orbitList_σ (y : D) :
    orbitList Γ.σ y = [y, Γ.σ y, Γ.σ (Γ.σ y), Γ.σ (Γ.σ (Γ.σ y))] := by
  simp [orbitList, Γ.m_period_σ, List.range_succ]

theorem m_σ_ne (y : D) : Γ.σ y ≠ y := fun h => Γ.m_curve_σ y (by rw [h])

theorem m_σσ_ne (y : D) : Γ.σ (Γ.σ y) ≠ y := by
  have h := orbitList_nodup Γ.σ y
  rw [m_orbitList_σ] at h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact fun e => h.1.2.1 e.symm

theorem m_σσσ_ne (y : D) : Γ.σ (Γ.σ (Γ.σ y)) ≠ y := by
  have h := orbitList_nodup Γ.σ y
  rw [m_orbitList_σ] at h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact fun e => h.1.2.2 e.symm

theorem m_curve_σσσ (y : D) : Γ.curve (Γ.σ (Γ.σ (Γ.σ y))) = Γ.curve (Γ.σ y) :=
  Γ.m_curve_σσ (Γ.σ y)

theorem m_curve_σσσ_ne (y : D) : Γ.curve (Γ.σ (Γ.σ (Γ.σ y))) ≠ Γ.curve y := by
  intro h
  have := Γ.m_curve_σ (Γ.σ (Γ.σ (Γ.σ y)))
  rw [Γ.m_σ4, h] at this
  exact this rfl

theorem m_eq_σσσ_of_σ_eq {x y : D} (h : Γ.σ x = y) : x = Γ.σ (Γ.σ (Γ.σ y)) := by
  rw [← h, Γ.m_σ4]

theorem m_straight_symm_apply (y : D) : Γ.straight.symm y = Γ.α (Γ.σ (Γ.σ y)) := by
  rw [Equiv.symm_apply_eq, m_straight_apply, m_α_α, m_σ4]

theorem m_straight_α (y : D) : Γ.straight (Γ.α y) = Γ.σ (Γ.σ y) := by
  rw [m_straight_apply, m_α_α]

theorem m_σσ_straight (y : D) : Γ.σ (Γ.σ (Γ.straight y)) = Γ.α y := by
  rw [m_straight_apply, m_σ4]

theorem m_φ_α (y : D) : Γ.φ (Γ.α y) = Γ.σ y := by rw [m_φ_apply, m_α_α]

/-! ## Crossings and cells -/

theorem m_crossingOf_eq_iff {a b : D} :
    Γ.crossingOf a = Γ.crossingOf b ↔ b ∈ [a, Γ.σ a, Γ.σ (Γ.σ a), Γ.σ (Γ.σ (Γ.σ a))] := by
  rw [crossingOf, crossingOf, Orbit.mk_eq_mk, ← mem_orbitList, m_orbitList_σ]

theorem m_crossingOf_σ (y : D) : Γ.crossingOf (Γ.σ y) = Γ.crossingOf y := by
  rw [crossingOf, crossingOf, Orbit.mk_eq_mk]
  exact Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl _ _)

theorem m_crossingOf_σσ (y : D) : Γ.crossingOf (Γ.σ (Γ.σ y)) = Γ.crossingOf y := by
  rw [m_crossingOf_σ, m_crossingOf_σ]

theorem m_crossingOf_σσσ (y : D) : Γ.crossingOf (Γ.σ (Γ.σ (Γ.σ y))) = Γ.crossingOf y := by
  rw [m_crossingOf_σ, m_crossingOf_σ, m_crossingOf_σ]

theorem m_crossingOf_φ (y : D) : Γ.crossingOf (Γ.φ y) = Γ.crossingOf (Γ.α y) :=
  Γ.m_crossingOf_σ _

theorem m_crossingOf_straight (y : D) : Γ.crossingOf (Γ.straight y) = Γ.crossingOf (Γ.α y) := by
  rw [m_straight_apply, m_crossingOf_σσ]

/-- Two darts of the same curve at one crossing are equal or opposite. -/
theorem m_eq_or_eq_σσ {a b : D} (hx : Γ.crossingOf a = Γ.crossingOf b)
    (hc : Γ.curve a = Γ.curve b) : b = a ∨ b = Γ.σ (Γ.σ a) := by
  have h0 := (Γ.m_crossingOf_eq_iff).1 hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
  rcases h0 with h | h | h | h
  · exact Or.inl h
  · subst h; exact absurd hc.symm (Γ.m_curve_σ a)
  · exact Or.inr h
  · subst h; exact absurd hc.symm (Γ.m_curve_σσσ_ne a)

theorem m_cellOf_eq_iff {a b : D} : Γ.cellOf a = Γ.cellOf b ↔ Γ.φ.SameCycle a b := by
  rw [cellOf, cellOf, Orbit.mk_eq_mk]

theorem m_cellOf_φ (y : D) : Γ.cellOf (Γ.φ y) = Γ.cellOf y := by
  rw [m_cellOf_eq_iff]
  exact Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl _ _)

theorem m_cellOf_σ (y : D) : Γ.cellOf (Γ.σ y) = Γ.cellOf (Γ.α y) := by
  rw [← m_φ_α, m_cellOf_φ]

theorem m_mem_darts_cellOf {y e : D} : e ∈ (Γ.cellOf y).darts ↔ Γ.cellOf e = Γ.cellOf y :=
  Orbit.mem_darts

theorem m_size_cellOf (y : D) : (Γ.cellOf y).size = period Γ.φ y := by
  rw [Orbit.size, cellOf, Orbit.darts_mk, card_orbitFinset]

/-- No dart is fixed by `φ` (a cell has at least two darts). -/
theorem m_φ_ne (y : D) : Γ.φ y ≠ y := by
  intro h
  rw [m_φ_apply] at h
  have h1 := Γ.m_eq_σσσ_of_σ_eq h
  have h2 := Γ.m_curve_σσσ_ne y
  rw [← h1, m_curve_α] at h2
  exact h2 rfl

theorem m_curve_φ_ne (y : D) : Γ.curve (Γ.φ y) ≠ Γ.curve y := by
  rw [m_φ_apply]; intro h; exact Γ.m_curve_σ (Γ.α y) (by rw [h, m_curve_α])

/-! ## The side function -/

/-- `1` on the darts of `S`, `0` elsewhere. -/
def mS (y : D) : ZMod 2 := if Γ.curve y = Γ.S then 1 else 0

/-- The side of the cell of a dart (the cell to its right). -/
def mSide (y : D) : ZMod 2 := Γ.side (Γ.cellOf y)

theorem m_isSide (y : D) : Γ.mSide y + Γ.mSide (Γ.α y) = Γ.mS y := Γ.isSide y

theorem m_mS_α (y : D) : Γ.mS (Γ.α y) = Γ.mS y := by rw [mS, mS, m_curve_α]

theorem m_mS_σσ (y : D) : Γ.mS (Γ.σ (Γ.σ y)) = Γ.mS y := by rw [mS, mS, m_curve_σσ]

theorem m_mS_straight (y : D) : Γ.mS (Γ.straight y) = Γ.mS y := by
  rw [mS, mS, m_curve_straight]

theorem m_side_α (y : D) : Γ.mSide (Γ.α y) = Γ.mSide y + Γ.mS y :=
  m_zmod2_eq_add_of_add_eq (Γ.m_isSide y)

theorem m_side_σ (y : D) : Γ.mSide (Γ.σ y) = Γ.mSide y + Γ.mS y := by
  rw [mSide, m_cellOf_σ, ← mSide, m_side_α]

theorem m_side_φ (y : D) : Γ.mSide (Γ.φ y) = Γ.mSide y := by rw [mSide, mSide, m_cellOf_φ]

/-- Walking straight on, the side of the cell to the right changes exactly when the crossing
passed is a crossing with `S` (seen from a dart not on `S`). -/
theorem m_side_straight (y : D) :
    Γ.mSide (Γ.straight y) = Γ.mSide y + Γ.mS (Γ.σ (Γ.α y)) := by
  rw [m_straight_apply, m_side_σ, m_side_σ, m_side_α, m_mS_α, add_assoc (Γ.mSide y),
    m_zmod2_add_self, add_zero]

end SConf

end Pca.Sweep
