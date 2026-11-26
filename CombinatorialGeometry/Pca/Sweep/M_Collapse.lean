/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package M, helpers: the digon collapse (local data)

Setting: `d` a sweep dart whose upper cell is a digon (`EmptyHumpAt d`). The digon has the darts
`α d` (on `S`, from `i + 1` to `i`) and `σ d` (on `γ = curve (σ d)`, from `i` to `i + 1`), its
corners are `i = crossingOf d` and `i + 1 = crossingOf (α d)`.

The collapse deletes the eight darts at the two corners. A dart is **kept** (`mKept`) iff it is
not at a corner. Exactly four kept darts have their reverse deleted, the **outer darts**:

* `p₁ = α (σ² d)` (`S`, into `i`), `q₁ = α (σ² (α d))` (`S`, into `i + 1`),
* `p₂ = α (σ³ d)` (`γ`, into `i`), `q₂ = α (σ (α d))` (`γ`, into `i + 1`);

the new edge involution `α'` pairs `p₁ ↔ q₁` (the three segments of `S` at the digon are joined)
and `p₂ ↔ q₂` (the same for `γ`), and is `α` elsewhere (`mαc`).

Validity: the outer darts are kept iff `S` and `γ` each cross something besides each other at
`i`, `i + 1` (`hS`, `hc`); see `Pca/Sweep/Moves.lean` for the full list of hypotheses.
-/
import Pca.Sweep.M_Tri

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

/-- `y` is kept by the collapse at `d`: it is not at a corner of the digon above `d`. -/
def mKept (d y : D) : Prop := Γ.crossingOf y ≠ Γ.crossingOf d ∧ Γ.crossingOf y ≠ Γ.crossingOf (Γ.α d)

instance (d : D) : DecidablePred (Γ.mKept d) := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The outer darts. -/
def mp₁ (d : D) : D := Γ.α (Γ.σ (Γ.σ d))
def mq₁ (d : D) : D := Γ.α (Γ.σ (Γ.σ (Γ.α d)))
def mp₂ (d : D) : D := Γ.α (Γ.σ (Γ.σ (Γ.σ d)))
def mq₂ (d : D) : D := Γ.α (Γ.σ (Γ.α d))

/-- The edge involution after the collapse (on the kept darts). -/
def mαc (d y : D) : D :=
  if y = Γ.mp₁ d then Γ.mq₁ d else if y = Γ.mq₁ d then Γ.mp₁ d
  else if y = Γ.mp₂ d then Γ.mq₂ d else if y = Γ.mq₂ d then Γ.mp₂ d else Γ.α y

/-- A straight walk of period two only meets the crossings at the ends of its first segment. -/
theorem m_period_two_crossings {b : D} (h2 : Γ.straight (Γ.straight b) = b) (e : D)
    (he : Γ.curve e = Γ.curve b) :
    Γ.crossingOf e = Γ.crossingOf b ∨ Γ.crossingOf e = Γ.crossingOf (Γ.α b) := by
  rcases Γ.isSConf.straight b e he.symm with h | h
  · rcases m_sameCycle_of_period_two (Γ := Γ) h2 h with h' | h'
    · left; rw [h']
    · right; rw [h', m_crossingOf_straight]
  · rcases m_sameCycle_of_period_two (Γ := Γ) h2 h with h' | h'
    · left; rw [← Γ.m_crossingOf_σσ e, h']
    · right; rw [← Γ.m_crossingOf_σσ e, h', m_crossingOf_straight]

variable {Γ} {d : D} (h : Γ.EmptyHumpAt d)
include h

theorem m_dig_φσ : Γ.φ (Γ.σ d) = Γ.α d := by
  have hp : period Γ.φ (Γ.α d) = 2 := by rw [← m_size_cellOf]; exact h.2
  have := iterate_period Γ.φ (Γ.α d)
  rw [hp] at this
  simpa [m_φ_α] using this

theorem m_dig_ασ : Γ.α (Γ.σ d) = Γ.σ (Γ.σ (Γ.σ (Γ.α d))) :=
  Γ.m_eq_σσσ_of_σ_eq (m_dig_φσ h)

theorem m_dig_curve_d : Γ.curve d = Γ.S := h.1.1.1

theorem m_dig_cross_ne : Γ.crossingOf d ≠ Γ.crossingOf (Γ.α d) := by
  intro hx
  rcases Γ.m_eq_or_eq_σσ hx (Γ.m_curve_α d).symm with h1 | h1
  · exact Γ.m_α_ne d h1
  · have := m_dig_ασ h
    rw [h1, Γ.m_σ4] at this
    exact Γ.m_α_ne _ this

theorem m_dig_curve_γ_ne : Γ.curve (Γ.σ d) ≠ Γ.S := by
  rw [← m_dig_curve_d h]; exact Γ.m_curve_σ d

omit h in
/-- The darts at the corners. -/
theorem m_not_kept_iff {y : D} : ¬ Γ.mKept d y ↔
    (y = d ∨ y = Γ.σ d ∨ y = Γ.σ (Γ.σ d) ∨ y = Γ.σ (Γ.σ (Γ.σ d))) ∨
    (y = Γ.α d ∨ y = Γ.σ (Γ.α d) ∨ y = Γ.σ (Γ.σ (Γ.α d)) ∨ y = Γ.σ (Γ.σ (Γ.σ (Γ.α d)))) := by
  rw [mKept, not_and_or, not_not, not_not]
  have e1 := @Γ.m_crossingOf_eq_iff _ _ _ _ d y
  have e2 := @Γ.m_crossingOf_eq_iff _ _ _ _ (Γ.α d) y
  simp only [List.mem_cons, List.not_mem_nil, or_false] at e1 e2
  rw [eq_comm, e1, eq_comm (a := Γ.crossingOf y), e2]

omit h in
theorem m_kept_σ {y : D} : Γ.mKept d (Γ.σ y) ↔ Γ.mKept d y := by
  rw [mKept, mKept, m_crossingOf_σ]

/-- The corners lie on `S` and on `γ`. -/
theorem m_kept_of_not_onCurve {y : D} (hy : ∀ e, Γ.crossingOf e = Γ.crossingOf y →
    Γ.curve e ≠ Γ.S) : Γ.mKept d y := by
  refine ⟨fun hx => hy d hx.symm (m_dig_curve_d h), fun hx => hy (Γ.α d) hx.symm ?_⟩
  rw [m_curve_α]; exact m_dig_curve_d h

theorem m_kept_of_not_onCurve_γ {y : D} (hy : ∀ e, Γ.crossingOf e = Γ.crossingOf y →
    Γ.curve e ≠ Γ.curve (Γ.σ d)) : Γ.mKept d y := by
  refine ⟨fun hx => hy (Γ.σ d) ((Γ.m_crossingOf_σ d).trans hx.symm) rfl, fun hx => ?_⟩
  refine hy (Γ.α (Γ.σ d)) ?_ (Γ.m_curve_α _)
  rw [m_dig_ασ h, m_crossingOf_σσσ, hx]

section Outer

variable (hS : ∃ e, Γ.curve e = Γ.S ∧ Γ.mKept d e)
  (hc : ∃ e, Γ.curve e = Γ.curve (Γ.σ d) ∧ Γ.mKept d e)

include hS in
/-- `S` does not close up after `d` and the next segment. -/
theorem m_straight_d_ne : Γ.straight d ≠ Γ.mp₁ d := by
  intro he
  have h2 : Γ.straight (Γ.straight d) = d := by
    rw [he, mp₁, m_straight_apply, m_α_α, Γ.m_σ4]
  obtain ⟨e, heS, hek⟩ := hS
  rcases Γ.m_period_two_crossings h2 e (heS.trans (m_dig_curve_d h).symm) with hx | hx
  · exact hek.1 hx
  · exact hek.2 hx

include hc in
/-- `γ` does not close up after the hump and the next segment. -/
theorem m_straight_σd_ne : Γ.straight (Γ.σ d) ≠ Γ.mp₂ d := by
  intro he
  have h2 : Γ.straight (Γ.straight (Γ.σ d)) = Γ.σ d := by
    rw [he, mp₂, m_straight_apply, m_α_α, Γ.m_σ4]
  obtain ⟨e, heS, hek⟩ := hc
  rcases Γ.m_period_two_crossings h2 e heS with hx | hx
  · exact hek.1 (hx.trans (Γ.m_crossingOf_σ d))
  · apply hek.2
    rw [hx, m_dig_ασ h, m_crossingOf_σσσ]

theorem m_straight_σd : Γ.straight (Γ.σ d) = Γ.σ (Γ.α d) := by
  rw [m_straight_apply, m_dig_ασ h, Γ.m_σ4]

include hS in
theorem m_kept_p₁ : Γ.mKept d (Γ.mp₁ d) := by
  have hcur : Γ.curve (Γ.σ (Γ.σ d)) = Γ.curve (Γ.mp₁ d) := by rw [mp₁, m_curve_α]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · rcases Γ.m_eq_or_eq_σσ ((Γ.m_crossingOf_σσ d).trans hx.symm) hcur with h1 | h1
    · exact Γ.m_α_ne _ h1
    · rw [Γ.m_σ4, mp₁] at h1
      have : Γ.σ (Γ.σ d) = Γ.α d := by have := congrArg Γ.α h1; rwa [m_α_α] at this
      exact m_dig_cross_ne h ((Γ.m_crossingOf_σσ d).symm.trans (congrArg Γ.crossingOf this))
  · have hcur' : Γ.curve (Γ.α d) = Γ.curve (Γ.mp₁ d) := by
      rw [← hcur, m_curve_σσ, m_curve_α]
    rcases Γ.m_eq_or_eq_σσ hx.symm hcur' with h1 | h1
    · rw [mp₁] at h1
      exact Γ.m_σσ_ne d (Γ.α.injective h1)
    · exact m_straight_d_ne h hS (by rw [m_straight_apply, ← h1])

include hS in
theorem m_kept_q₁ : Γ.mKept d (Γ.mq₁ d) := by
  have hcur : Γ.curve (Γ.σ (Γ.σ (Γ.α d))) = Γ.curve (Γ.mq₁ d) := by rw [mq₁, m_curve_α]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hcur' : Γ.curve d = Γ.curve (Γ.mq₁ d) := by
      rw [← hcur, m_curve_σσ, m_curve_α]
    rcases Γ.m_eq_or_eq_σσ hx.symm hcur' with h1 | h1
    · rw [mq₁] at h1
      have : Γ.σ (Γ.σ (Γ.α d)) = Γ.α d := by rw [← m_α_α Γ (Γ.σ (Γ.σ (Γ.α d))), h1]
      exact Γ.m_σσ_ne _ this
    · apply m_straight_d_ne h hS
      rw [m_straight_apply, mp₁, ← h1, mq₁, m_α_α]
  · rcases Γ.m_eq_or_eq_σσ ((Γ.m_crossingOf_σσ _).trans hx.symm) hcur with h1 | h1
    · exact Γ.m_α_ne _ h1
    · rw [Γ.m_σ4, mq₁] at h1
      have : Γ.σ (Γ.σ (Γ.α d)) = d := by rw [← m_α_α Γ (Γ.σ (Γ.σ (Γ.α d))), h1, m_α_α]
      exact m_dig_cross_ne h ((congrArg Γ.crossingOf this).symm.trans (Γ.m_crossingOf_σσ _))

include hc in
theorem m_kept_p₂ : Γ.mKept d (Γ.mp₂ d) := by
  have hcur : Γ.curve (Γ.σ (Γ.σ (Γ.σ d))) = Γ.curve (Γ.mp₂ d) := by rw [mp₂, m_curve_α]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · rcases Γ.m_eq_or_eq_σσ ((Γ.m_crossingOf_σσσ d).trans hx.symm) hcur with h1 | h1
    · exact Γ.m_α_ne _ h1
    · rw [Γ.m_σ4, mp₂] at h1
      have h2 : Γ.σ (Γ.σ (Γ.σ d)) = Γ.α (Γ.σ d) := by
        have := congrArg Γ.α h1; rwa [m_α_α] at this
      rw [m_dig_ασ h] at h2
      exact Γ.m_α_ne d (Γ.σ.injective (Γ.σ.injective (Γ.σ.injective h2))).symm
  · have hcur' : Γ.curve (Γ.α (Γ.σ d)) = Γ.curve (Γ.mp₂ d) := by
      rw [← hcur, m_curve_α, m_curve_σσ]
    have hx' : Γ.crossingOf (Γ.α (Γ.σ d)) = Γ.crossingOf (Γ.mp₂ d) := by
      rw [hx, m_dig_ασ h, m_crossingOf_σσσ]
    rcases Γ.m_eq_or_eq_σσ hx' hcur' with h1 | h1
    · rw [mp₂] at h1
      exact Γ.m_σσ_ne (Γ.σ d) (Γ.α.injective h1)
    · apply m_straight_σd_ne h hc
      rw [m_straight_apply, h1]

include hc in
theorem m_kept_q₂ : Γ.mKept d (Γ.mq₂ d) := by
  have hcur : Γ.curve (Γ.σ (Γ.α d)) = Γ.curve (Γ.mq₂ d) := by rw [mq₂, m_curve_α]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hcur' : Γ.curve (Γ.σ d) = Γ.curve (Γ.mq₂ d) := by
      rw [← hcur, ← m_straight_σd h, m_curve_straight]
    rcases Γ.m_eq_or_eq_σσ ((Γ.m_crossingOf_σ d).trans hx.symm) hcur' with h1 | h1
    · -- `σ (α d) = α (σ d) = σ³ (α d)`
      rw [mq₂] at h1
      have h2 : Γ.σ (Γ.α d) = Γ.σ (Γ.σ (Γ.σ (Γ.α d))) := by rw [← m_dig_ασ h, ← h1, m_α_α]
      exact Γ.m_σσ_ne (Γ.σ (Γ.α d)) h2.symm
    · apply m_straight_σd_ne h hc
      rw [m_straight_σd h, mp₂, ← h1, mq₂, m_α_α]
  · rcases Γ.m_eq_or_eq_σσ ((Γ.m_crossingOf_σ _).trans hx.symm) hcur with h1 | h1
    · exact Γ.m_α_ne _ h1
    · rw [mq₂] at h1
      have h2 : Γ.σ (Γ.α d) = Γ.σ d := by
        rw [← m_α_α Γ (Γ.σ (Γ.α d)), h1, ← m_dig_ασ h, m_α_α]
      exact Γ.m_α_ne d (Γ.σ.injective h2)

end Outer

omit h in
theorem m_p₁_ne_q₁ : Γ.mp₁ d ≠ Γ.mq₁ d := fun he =>
  Γ.m_α_ne d (Γ.σ.injective (Γ.σ.injective (Γ.α.injective he))).symm

theorem m_p₂_ne_q₂ : Γ.mp₂ d ≠ Γ.mq₂ d := fun he => by
  have := congrArg Γ.crossingOf (Γ.α.injective he)
  rw [m_crossingOf_σσσ, m_crossingOf_σ] at this
  exact m_dig_cross_ne h this

theorem m_curve_p₁ : Γ.curve (Γ.mp₁ d) = Γ.S := by rw [mp₁, m_curve_α, m_curve_σσ, m_dig_curve_d h]
theorem m_curve_q₁ : Γ.curve (Γ.mq₁ d) = Γ.S := by
  rw [mq₁, m_curve_α, m_curve_σσ, m_curve_α, m_dig_curve_d h]
omit h in
theorem m_curve_p₂ : Γ.curve (Γ.mp₂ d) = Γ.curve (Γ.σ d) := by
  rw [mp₂, m_curve_α, m_curve_σσσ]
theorem m_curve_q₂ : Γ.curve (Γ.mq₂ d) = Γ.curve (Γ.σ d) := by
  rw [mq₂, m_curve_α, ← m_straight_σd h, m_curve_straight]

theorem m_p₁_ne_p₂ : Γ.mp₁ d ≠ Γ.mp₂ d := fun he => m_dig_curve_γ_ne h (by
  rw [← m_curve_p₂, ← he, m_curve_p₁ h])
theorem m_p₁_ne_q₂ : Γ.mp₁ d ≠ Γ.mq₂ d := fun he => m_dig_curve_γ_ne h (by
  rw [← m_curve_q₂ h, ← he, m_curve_p₁ h])
theorem m_q₁_ne_p₂ : Γ.mq₁ d ≠ Γ.mp₂ d := fun he => m_dig_curve_γ_ne h (by
  rw [← m_curve_p₂, ← he, m_curve_q₁ h])
theorem m_q₁_ne_q₂ : Γ.mq₁ d ≠ Γ.mq₂ d := fun he => m_dig_curve_γ_ne h (by
  rw [← m_curve_q₂ h, ← he, m_curve_q₁ h])

/-- A kept dart other than the outer darts has a kept reverse. -/
theorem m_kept_α {y : D} (hy : Γ.mKept d y) (h1 : y ≠ Γ.mp₁ d) (h2 : y ≠ Γ.mq₁ d)
    (h3 : y ≠ Γ.mp₂ d) (h4 : y ≠ Γ.mq₂ d) : Γ.mKept d (Γ.α y) := by
  by_contra hn
  rw [m_not_kept_iff] at hn
  have hy' := fun z => (m_not_kept_iff (Γ := Γ) (d := d) (y := z)).2
  rcases hn with (e | e | e | e) | (e | e | e | e)
  · exact hy' y (Or.inr (Or.inl (by rw [← m_α_α Γ y, e]))) hy
  · exact hy' y (Or.inr (Or.inr (Or.inr (Or.inr (by rw [← m_α_α Γ y, e, m_dig_ασ h]))))) hy
  · exact h1 (by rw [mp₁, ← e, m_α_α])
  · exact h3 (by rw [mp₂, ← e, m_α_α])
  · exact hy' y (Or.inl (Or.inl (by rw [← m_α_α Γ y, e, m_α_α]))) hy
  · exact h4 (by rw [mq₂, ← e, m_α_α])
  · exact h2 (by rw [mq₁, ← e, m_α_α])
  · exact hy' y (Or.inl (Or.inr (Or.inl (by rw [← m_α_α Γ y, e, ← m_dig_ασ h, m_α_α])))) hy

end SConf

end Pca.Sweep
