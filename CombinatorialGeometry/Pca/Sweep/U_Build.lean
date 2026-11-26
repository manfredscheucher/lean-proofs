/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package U, helpers: the new segments and labels of the untangling

`uαf`: the new edge involution (`doc/pca/sweep.md`): on the twelve changed darts `uM` it is
the pairing `uPI`, elsewhere `α`. `uCurve`: the darts of `γ1` at the crossings of the leg from `i`
get the label of `γ2` and vice versa. `uSideD`: the darts at `v` (now the new crossing below `S`)
are below the sweep, every other dart keeps its side.
-/
import Pca.Sweep.U_Hyp

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

/-- The new edge involution (as a function). -/
noncomputable def uαf (d a : D) (x : D) : D :=
  if h : ∃ i, Γ.uM d a i = x then Γ.uM d a (uPI (Classical.choose h)) else Γ.α x

/-- The crossings of the leg from `i` (including `i`). -/
def uC1 (d : D) (k : ℕ) : Finset Γ.Crossing :=
  (range k).image (fun j => Γ.crossingOf ((Γ.straight ^ j) (Γ.ub1 d)))

/-- The crossings of the leg from `i + 1` (including `i + 1`). -/
def uC2 (d : D) (k : ℕ) : Finset Γ.Crossing :=
  (range k).image (fun j => Γ.crossingOf ((Γ.straight ^ j) (Γ.ub2 d)))

/-- `x` is a dart of `γ1` on the leg from `i`. -/
def uR1 (d : D) (k : ℕ) (x : D) : Prop :=
  Γ.crossingOf x ∈ Γ.uC1 d k ∧ Γ.curve x = Γ.curve (Γ.ub1 d)

/-- `x` is a dart of `γ2` on the leg from `i + 1`. -/
def uR2 (d : D) (k : ℕ) (x : D) : Prop :=
  Γ.crossingOf x ∈ Γ.uC2 d k ∧ Γ.curve x = Γ.curve (Γ.ub2 d)

instance (d : D) (k : ℕ) (x : D) : Decidable (Γ.uR1 d k x) := by unfold uR1; infer_instance
instance (d : D) (k : ℕ) (x : D) : Decidable (Γ.uR2 d k x) := by unfold uR2; infer_instance

/-- The new labels. -/
def uCurve (d : D) (k : ℕ) (x : D) : Fin n :=
  if Γ.uR1 d k x then Γ.curve (Γ.ub2 d)
  else if Γ.uR2 d k x then Γ.curve (Γ.ub1 d) else Γ.curve x

/-- The new labels of the changed darts: `false = γ1`, `true = γ2`. -/
def uKI' : Fin 12 → Bool
  | 0 => true | 1 => false | 2 => true | 3 => false | 4 => false | 5 => false | 6 => true
  | 7 => true | 8 => true | 9 => false | 10 => false | 11 => true

theorem uKI'_uPI (i : Fin 12) : uKI' (uPI i) = uKI' i := by revert i; decide

variable {Γ} {d a : D} {k : ℕ} {γ : Fin n}

section Hyp

variable (H : Γ.UHyp d a k γ)
include H

/-! ### The edge involution -/

theorem UHyp.uαf_uM (i : Fin 12) : Γ.uαf d a (Γ.uM d a i) = Γ.uM d a (uPI i) := by
  have h : ∃ j, Γ.uM d a j = Γ.uM d a i := ⟨i, rfl⟩
  rw [uαf, dif_pos h, H.uM_inj (Classical.choose_spec h)]

theorem UHyp.uαf_of {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) : Γ.uαf d a x = Γ.α x := by
  rw [uαf, dif_neg (by push Not; exact hx)]

theorem UHyp.α_uM (i : Fin 12) : Γ.α (Γ.uM d a i) = Γ.uM d a (uAI i) := by
  fin_cases i <;> simp only [uM, uAI, j_α_α]

theorem UHyp.notM_α {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) : ∀ i, Γ.uM d a i ≠ Γ.α x := by
  intro i hi
  apply hx (uAI i)
  rw [← H.α_uM, hi, j_α_α]

theorem UHyp.uαf_invol : Function.Involutive (Γ.uαf d a) := by
  intro x
  by_cases hx : ∃ i, Γ.uM d a i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [H.uαf_uM, H.uαf_uM, uPI_uPI]
  · push Not at hx
    rw [H.uαf_of hx, H.uαf_of (H.notM_α hx), j_α_α]

theorem UHyp.uαf_ne (x : D) : Γ.uαf d a x ≠ x := by
  by_cases hx : ∃ i, Γ.uM d a i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [H.uαf_uM]
    exact fun h => uPI_ne i (H.uM_inj h)
  · push Not at hx
    rw [H.uαf_of hx]; exact Γ.isSConf.α_ne x

/-- `σ` on the darts at `v`. -/
theorem UHyp.σ_uM0 : Γ.σ (Γ.uM d a 0) = Γ.uM d a 1 := rfl
theorem UHyp.σ_uM1 : Γ.σ (Γ.uM d a 1) = Γ.uM d a 2 := rfl
theorem UHyp.σ_uM2 : Γ.σ (Γ.uM d a 2) = Γ.uM d a 3 := rfl
theorem UHyp.σ_uM3 : Γ.σ (Γ.uM d a 3) = Γ.uM d a 0 := Γ.j_σ4 a

/-! ### The legs as sets of darts -/

theorem UHyp.uR1_iff {x : D} : Γ.uR1 d k x ↔
    ∃ j < k, x = (Γ.straight ^ j) (Γ.ub1 d) ∨ x = Γ.σ (Γ.σ ((Γ.straight ^ j) (Γ.ub1 d))) := by
  constructor
  · rintro ⟨hc, hk⟩
    obtain ⟨j, hj, hx⟩ := mem_image.1 hc
    rw [mem_range] at hj
    exact ⟨j, hj, Γ.u_eq_or_σσ hx.symm (by rw [hk, u_curve_pow])⟩
  · rintro ⟨j, hj, rfl | rfl⟩
    · exact ⟨mem_image.2 ⟨j, mem_range.2 hj, rfl⟩, u_curve_pow _ _ _⟩
    · refine ⟨mem_image.2 ⟨j, mem_range.2 hj, ?_⟩, by rw [j_curve_σσ, u_curve_pow]⟩
      rw [j_crossingOf_σ, j_crossingOf_σ]

theorem UHyp.uR2_iff {x : D} : Γ.uR2 d k x ↔
    ∃ j < k, x = (Γ.straight ^ j) (Γ.ub2 d) ∨ x = Γ.σ (Γ.σ ((Γ.straight ^ j) (Γ.ub2 d))) := by
  constructor
  · rintro ⟨hc, hk⟩
    obtain ⟨j, hj, hx⟩ := mem_image.1 hc
    rw [mem_range] at hj
    exact ⟨j, hj, Γ.u_eq_or_σσ hx.symm (by rw [hk, u_curve_pow])⟩
  · rintro ⟨j, hj, rfl | rfl⟩
    · exact ⟨mem_image.2 ⟨j, mem_range.2 hj, rfl⟩, u_curve_pow _ _ _⟩
    · refine ⟨mem_image.2 ⟨j, mem_range.2 hj, ?_⟩, by rw [j_curve_σσ, u_curve_pow]⟩
      rw [j_crossingOf_σ, j_crossingOf_σ]

theorem UHyp.not_R1_R2 {x : D} (h1 : Γ.uR1 d k x) : ¬ Γ.uR2 d k x :=
  fun h2 => H.c12 (h1.2.symm.trans h2.2)

/-- On a leg, `α` stays on the leg (except at the two changed darts). -/
theorem UHyp.uR1_α {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) : Γ.uR1 d k x → Γ.uR1 d k (Γ.α x) := by
  intro h
  obtain ⟨j, hj, rfl | rfl⟩ := H.uR1_iff.1 h
  · rcases Nat.lt_or_ge (j + 1) k with hj1 | hj1
    · refine H.uR1_iff.2 ⟨j + 1, hj1, Or.inr ?_⟩
      rw [Γ.u_α_straight, u_pow_succ]
    · exact absurd (by simp only [uM]; rw [H.pos7, show k - 1 = j by omega]) (hx 7)
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd H.pos8 (hx 8)
    · refine H.uR1_iff.2 ⟨j - 1, by omega, Or.inl ?_⟩
      rw [show j = j - 1 + 1 by omega, u_pow_succ, j_straight_apply, Γ.j_σ4, j_α_α,
        Nat.add_sub_cancel]

theorem UHyp.uR2_α {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) : Γ.uR2 d k x → Γ.uR2 d k (Γ.α x) := by
  intro h
  obtain ⟨j, hj, rfl | rfl⟩ := H.uR2_iff.1 h
  · rcases Nat.lt_or_ge (j + 1) k with hj1 | hj1
    · refine H.uR2_iff.2 ⟨j + 1, hj1, Or.inr ?_⟩
      rw [Γ.u_α_straight, u_pow_succ]
    · exact absurd (by simp only [uM]; rw [H.pos4, show k - 1 = j by omega]) (hx 4)
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact absurd H.pos10 (hx 10)
    · refine H.uR2_iff.2 ⟨j - 1, by omega, Or.inl ?_⟩
      rw [show j = j - 1 + 1 by omega, u_pow_succ, j_straight_apply, Γ.j_σ4, j_α_α,
        Nat.add_sub_cancel]

theorem UHyp.uR1_α_iff {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) :
    Γ.uR1 d k (Γ.α x) ↔ Γ.uR1 d k x :=
  ⟨fun h => by have := H.uR1_α (H.notM_α hx) h; rwa [j_α_α] at this, H.uR1_α hx⟩

theorem UHyp.uR2_α_iff {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) :
    Γ.uR2 d k (Γ.α x) ↔ Γ.uR2 d k x :=
  ⟨fun h => by have := H.uR2_α (H.notM_α hx) h; rwa [j_α_α] at this, H.uR2_α hx⟩

/-- Which changed darts lie on the legs. -/
theorem UHyp.uR1_uM (i : Fin 12) : Γ.uR1 d k (Γ.uM d a i) ↔ i = 7 ∨ i = 8 := by
  have hP := H.kP1
  have hk := H.k_pos
  constructor
  · intro h
    have hc := h.2
    rw [H.c_uM] at hc
    obtain ⟨j, hj, h1 | h1⟩ := H.uR1_iff.1 h
    · rcases H.fwd1 (by omega) h1 with ⟨-, h2⟩ | ⟨h2, -⟩ | ⟨-, h2⟩
      · omega
      · exact Or.inl h2
      · omega
    · fin_cases i <;> simp only [uKI, if_true, if_false, Bool.false_eq_true] at hc
      all_goals first | exact absurd hc H.c12.symm | skip
      all_goals simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, or_false, or_true,
        false_or]
      all_goals simp only [uM] at h1
      · have h3 : Γ.uM d a 3 = (Γ.straight ^ j) (Γ.ub1 d) := by
          simp only [uM]; rw [h1, Γ.j_σ4]
        rcases H.fwd1 (by omega) h3 with ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ <;> exact absurd h4 (by decide)
      · have h3 : Γ.uM d a 1 = (Γ.straight ^ j) (Γ.ub1 d) := by
          simp only [uM]; rw [← Γ.j_σ4 (Γ.σ a), h1, Γ.j_σ4]
        rcases H.fwd1 (by omega) h3 with ⟨-, h4⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
        · omega
        · exact absurd h4 (by decide)
        · exact absurd h4 (by decide)
      · rw [H.pos5] at h1
        have := u_pow_inj (by omega) (by omega)
          (Γ.σ.injective (Γ.σ.injective h1))
        omega
      · rw [H.pos9] at h1
        exact absurd h1.symm (Γ.u_ne_rev _ _ _)
  · rintro (rfl | rfl)
    · exact H.uR1_iff.2 ⟨k - 1, by omega, Or.inl H.pos7⟩
    · exact H.uR1_iff.2 ⟨0, hk, Or.inr H.pos8⟩

theorem UHyp.uR2_uM (i : Fin 12) : Γ.uR2 d k (Γ.uM d a i) ↔ i = 4 ∨ i = 10 := by
  have hP := H.kP2
  have hk := H.k_pos
  constructor
  · intro h
    have hc := h.2
    rw [H.c_uM] at hc
    obtain ⟨j, hj, h1 | h1⟩ := H.uR2_iff.1 h
    · rcases H.fwd2 (by omega) h1 with ⟨-, h2⟩ | ⟨h2, -⟩ | ⟨-, h2⟩
      · omega
      · exact Or.inl h2
      · omega
    · fin_cases i <;> simp only [uKI, if_true, if_false, Bool.false_eq_true] at hc
      all_goals first | exact absurd hc H.c12 | skip
      all_goals simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, or_false, or_true,
        false_or]
      all_goals simp only [uM] at h1
      · have h3 : Γ.uM d a 2 = (Γ.straight ^ j) (Γ.ub2 d) := by
          simp only [uM]; rw [h1, Γ.j_σ4]
        rcases H.fwd2 (by omega) h3 with ⟨-, h4⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
        · omega
        · exact absurd h4 (by decide)
        · exact absurd h4 (by decide)
      · have h3 : Γ.uM d a 0 = (Γ.straight ^ j) (Γ.ub2 d) := by
          simp only [uM]; rw [← Γ.j_σ4 a, h1, Γ.j_σ4]
        rcases H.fwd2 (by omega) h3 with ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ <;> exact absurd h4 (by decide)
      · rw [H.pos6] at h1
        have := u_pow_inj (by omega) (by omega)
          (Γ.σ.injective (Γ.σ.injective h1))
        omega
      · rw [H.pos11] at h1
        exact absurd h1.symm (Γ.u_ne_rev _ _ _)
  · rintro (rfl | rfl)
    · exact H.uR2_iff.2 ⟨k - 1, by omega, Or.inl H.pos4⟩
    · exact H.uR2_iff.2 ⟨0, hk, Or.inr H.pos10⟩

/-- The new labels of the changed darts. -/
theorem UHyp.uCurve_uM (i : Fin 12) :
    Γ.uCurve d k (Γ.uM d a i) = if uKI' i then Γ.curve (Γ.ub2 d) else Γ.curve (Γ.ub1 d) := by
  unfold uCurve
  have h1 := H.uR1_uM i
  have h2 := H.uR2_uM i
  have hc := H.c_uM i
  fin_cases i <;> simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, or_false, or_true,
    false_or, iff_false, iff_true, uKI, uKI', if_true, if_false, Bool.false_eq_true] at h1 h2 hc ⊢
  all_goals first
    | rw [if_pos h1]
    | rw [if_neg h1, if_pos h2]
    | rw [if_neg h1, if_neg h2, hc]

end Hyp

end SConf

end Pca.Sweep
