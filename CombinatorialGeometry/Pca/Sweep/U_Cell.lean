/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package U, helpers: cells, side function and Euler of the untangling

* `ph = σ * α'`, the new cell permutation; it agrees with `φ` off the changed darts;
* the side function `uSideD` (the darts at `v`, now the new crossing below `S`, get `0`) is
  constant on new cells and is a side function of `S`;
* Euler: `uG` maps every dart to an old cell (`T ↦ B`; the new triangle `↦ T`; the darts at `v`
  to the cells below `S` they now lie in), constant on new cells and onto, so `F' ≥ F`; with
  `V' = V`, `E' = E` and `V' - E' + F' ≤ 2` (`Pca.MapFacts.euler_le_two`) this gives Euler.
-/
import Pca.Sweep.U_Two
import Pca.Great.Map_Euler

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {d a : D} {k : ℕ} {γ : Fin n}

/-- The new cell permutation. -/
noncomputable def UHyp.ph (H : Γ.UHyp d a k γ) : Perm D := Γ.σ * H.α'

variable (Γ) in
/-- The new side of a dart: the darts at `v` are below the sweep. -/
def uSideD (a : D) (x : D) : ZMod 2 :=
  if Γ.crossingOf x = Γ.crossingOf a then 0 else Γ.side (Γ.cellOf x)

/-- The new sides of the changed darts. -/
def uSV (i : Fin 12) : ZMod 2 := if i.val < 4 then 0 else if (uCI i).val < 4 then 1 else 0

theorem uSV_pair (i : Fin 12) : uSV i = uSV (uPI i) := by revert i; decide

theorem uSV_ph (i : Fin 12) :
    uSV i = if (uPI i).val < 4 then 0 else if (uCI (uAI (uPI i))).val < 4 then 1 else 0 := by
  revert i; decide

variable (Γ) in
/-- The old cell of a dart, adjusted so that it is constant on new cells. -/
def uG (d a : D) (x : D) : Γ.Cell :=
  if x = d ∨ x = Γ.uM d a 10 ∨ x = Γ.uM d a 0 then Γ.uCell d a 2
  else if x = Γ.uM d a 1 then Γ.uCell d a 5
  else if x = Γ.uM d a 2 then Γ.uCell d a 4
  else if x = Γ.uM d a 3 then Γ.uCell d a 6
  else if Γ.cellOf x = Γ.uCell d a 2 then Γ.uCell d a 0 else Γ.cellOf x

section Hyp

variable (H : Γ.UHyp d a k γ)
include H

theorem UHyp.ph_apply (x : D) : H.ph x = Γ.σ (H.α' x) := rfl

theorem UHyp.ph_of {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) : H.ph x = Γ.φ x := by
  rw [H.ph_apply, H.α'_of hx]; rfl

theorem UHyp.ph_uM (i : Fin 12) : H.ph (Γ.uM d a i) = Γ.σ (Γ.uM d a (uPI i)) := by
  rw [H.ph_apply, H.α'_uM]

theorem UHyp.uM_ne_d (i : Fin 12) : Γ.uM d a i ≠ d := by
  intro h
  have := congrArg Γ.curve h
  rw [H.c_uM, H.c_d] at this
  split_ifs at this
  · exact H.c2S this
  · exact H.c1S this

theorem UHyp.uM_eq_iff (i j : Fin 12) : Γ.uM d a i = Γ.uM d a j ↔ i = j :=
  H.uM_inj.eq_iff

/-- The darts at `v`. -/
theorem UHyp.v_iff {x : D} : Γ.crossingOf x = Γ.crossingOf a ↔
    x = Γ.uM d a 0 ∨ x = Γ.uM d a 1 ∨ x = Γ.uM d a 2 ∨ x = Γ.uM d a 3 := by
  constructor
  · exact Γ.u_mem_of_crossing
  · rintro (rfl | rfl | rfl | rfl)
    · rfl
    · exact j_crossingOf_σ _ _
    · simp only [uM, j_crossingOf_σ]
    · simp only [uM, j_crossingOf_σ]

theorem UHyp.notv_of_notM {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) :
    Γ.crossingOf x ≠ Γ.crossingOf a := by
  intro h
  rcases H.v_iff.1 h with h | h | h | h <;> exact hx _ h.symm

theorem UHyp.notv_uM {i : Fin 12} (hi : 4 ≤ i.val) :
    Γ.crossingOf (Γ.uM d a i) ≠ Γ.crossingOf a := by
  intro h
  rcases H.v_iff.1 h with h' | h' | h' | h' <;> rw [H.uM_eq_iff] at h' <;> subst h' <;>
    simp at hi

theorem UHyp.notv_φ {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) :
    Γ.crossingOf (Γ.φ x) ≠ Γ.crossingOf a := by
  rw [j_φ_apply, j_crossingOf_σ]
  exact H.notv_of_notM (H.notM_α hx)

/-! ### The side function -/

theorem UHyp.uSideD_uM (i : Fin 12) : Γ.uSideD a (Γ.uM d a i) = uSV i := by
  unfold uSideD uSV
  by_cases hi : i.val < 4
  · rw [if_pos (H.v_iff.2 (by fin_cases i <;> simp at hi ⊢)), if_pos hi]
  · rw [if_neg (H.notv_uM (by omega)), if_neg hi, H.cell_uM, H.side_uCell]

theorem UHyp.uSideD_σuM (j : Fin 12) : Γ.uSideD a (Γ.σ (Γ.uM d a j)) =
    if j.val < 4 then 0 else if (uCI (uAI j)).val < 4 then 1 else 0 := by
  unfold uSideD
  by_cases hj : j.val < 4
  · rw [if_pos, if_pos hj]
    rw [j_crossingOf_σ]; exact H.v_iff.2 (by fin_cases j <;> simp at hj ⊢)
  · rw [if_neg, if_neg hj, j_cellOf_σ, H.α_uM, H.cell_uM, H.side_uCell]
    rw [j_crossingOf_σ]; exact H.notv_uM (by omega)

theorem UHyp.uSideD_ph (x : D) : Γ.uSideD a (H.ph x) = Γ.uSideD a x := by
  by_cases hx : ∃ i, Γ.uM d a i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [H.ph_uM, H.uSideD_σuM, H.uSideD_uM, uSV_ph]
  · push Not at hx
    rw [H.ph_of hx]
    unfold uSideD
    rw [if_neg (H.notv_φ hx), if_neg (H.notv_of_notM hx), j_cellOf_φ]

theorem UHyp.uSideD_pow (x : D) (i : ℕ) : Γ.uSideD a ((H.ph ^ i) x) = Γ.uSideD a x := by
  induction i with
  | zero => rfl
  | succ i ih => rw [u_pow_succ, H.uSideD_ph, ih]

/-- The new side function, on new cells. -/
noncomputable def UHyp.side' : Orbit H.ph → ZMod 2 :=
  Quotient.lift (Γ.uSideD a) (fun x y (h : H.ph.SameCycle x y) => by
    obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
    exact (H.uSideD_pow x i).symm)

theorem UHyp.side'_mk (x : D) : H.side' (Orbit.mk H.ph x) = Γ.uSideD a x := rfl

theorem UHyp.isSide' (y : D) : H.side' (Orbit.mk H.ph y) + H.side' (Orbit.mk H.ph (H.α' y)) =
    if Γ.uCurve d k y = Γ.S then 1 else 0 := by
  simp only [H.side'_mk, H.uCurve_ne_S_iff]
  by_cases hx : ∃ i, Γ.uM d a i = y
  · obtain ⟨i, rfl⟩ := hx
    rw [H.α'_uM, H.uSideD_uM, H.uSideD_uM, ← uSV_pair, j_zmod2_add_self, if_neg]
    rw [H.c_uM]; split_ifs
    · exact H.c2S
    · exact H.c1S
  · push Not at hx
    rw [H.α'_of hx]
    unfold uSideD
    rw [if_neg (H.notv_of_notM hx), if_neg (H.notv_of_notM (H.notM_α hx))]
    exact Γ.isSide y

/-! ### Euler -/

theorem UHyp.uG_of {x : D} {c : Fin 7} (hc : Γ.cellOf x = Γ.uCell d a c)
    (hsp : ¬ (x = d ∨ x = Γ.uM d a 10 ∨ x = Γ.uM d a 0 ∨ x = Γ.uM d a 1 ∨ x = Γ.uM d a 2 ∨
      x = Γ.uM d a 3)) :
    Γ.uG d a x = if c = 2 then Γ.uCell d a 0 else Γ.uCell d a c := by
  simp only [not_or] at hsp
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hsp
  unfold uG
  rw [if_neg (by tauto), if_neg h4, if_neg h5, if_neg h6, hc]
  by_cases h : c = 2
  · subst h; simp
  · rw [if_neg (fun h' => h (H.uCell_inj h')), if_neg h]

/-- A dart is not special if it is not one of the special darts of its cell. -/
theorem UHyp.notSp {x : D} {c : Fin 7} (hc : Γ.cellOf x = Γ.uCell d a c)
    (h0 : c = 0 → x ≠ Γ.uM d a 0) (h1 : c = 1 → x ≠ Γ.uM d a 1) (h2 : c = 2 → x ≠ Γ.uM d a 2)
    (h3 : c = 3 → x ≠ Γ.uM d a 3) (h4 : c = 4 → x ≠ d ∧ x ≠ Γ.uM d a 10) :
    ¬ (x = d ∨ x = Γ.uM d a 10 ∨ x = Γ.uM d a 0 ∨ x = Γ.uM d a 1 ∨ x = Γ.uM d a 2 ∨
      x = Γ.uM d a 3) := by
  have cd : Γ.cellOf d = Γ.uCell d a 4 := rfl
  have key : ∀ (y : D) (c' : Fin 7), Γ.cellOf y = Γ.uCell d a c' → x = y → c = c' := by
    intro y c' hy hxy
    subst hxy
    exact H.uCell_inj (hc.symm.trans hy)
  rintro (h | h | h | h | h | h)
  · have := key _ 4 cd h; exact (h4 this).1 h
  · have := key _ 4 (H.cell_uM 10) h; exact (h4 this).2 h
  · exact h0 (key _ 0 (H.cell_uM 0) h) h
  · exact h1 (key _ 1 (H.cell_uM 1) h) h
  · exact h2 (key _ 2 (H.cell_uM 2) h) h
  · exact h3 (key _ 3 (H.cell_uM 3) h) h

theorem UHyp.uG_gen {x : D}
    (hsp : ¬ (x = d ∨ x = Γ.uM d a 10 ∨ x = Γ.uM d a 0 ∨ x = Γ.uM d a 1 ∨ x = Γ.uM d a 2 ∨
      x = Γ.uM d a 3)) :
    Γ.uG d a x = if Γ.cellOf x = Γ.uCell d a 2 then Γ.uCell d a 0 else Γ.cellOf x := by
  simp only [not_or] at hsp
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hsp
  unfold uG
  rw [if_neg (by tauto), if_neg h4, if_neg h5, if_neg h6]

theorem UHyp.uG_ph_generic {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) (hd : x ≠ d) :
    Γ.uG d a (H.ph x) = Γ.uG d a x := by
  rw [H.ph_of hx]
  have e1 : Γ.φ x ≠ d := by
    intro h
    apply hx 9
    apply Γ.φ.injective
    rw [h]; show Γ.σ (Γ.α (Γ.α (Γ.up1 d))) = d
    rw [j_α_α]; unfold up1; rw [Γ.j_σ4]
  have e10 : Γ.φ x ≠ Γ.uM d a 10 := by
    intro h; apply hd; apply Γ.φ.injective; rw [h]; rfl
  have epre : ∀ i j, Γ.φ (Γ.uM d a j) = Γ.uM d a i → Γ.φ x ≠ Γ.uM d a i := by
    intro i j hij h
    exact hx j (Γ.φ.injective (hij.trans h.symm))
  have e0 : Γ.φ x ≠ Γ.uM d a 0 := epre 0 7 (by
    simp only [uM]; rw [j_φ_apply, j_α_α, Γ.j_σ4])
  have e1' : Γ.φ x ≠ Γ.uM d a 1 := epre 1 4 (by simp only [uM]; rw [j_φ_apply, j_α_α])
  have e2 : Γ.φ x ≠ Γ.uM d a 2 := epre 2 5 (by simp only [uM]; rw [j_φ_apply, j_α_α])
  have e3 : Γ.φ x ≠ Γ.uM d a 3 := epre 3 6 (by simp only [uM]; rw [j_φ_apply, j_α_α])
  rw [H.uG_gen (by rintro (h | h | h | h | h | h); exacts [e1 h, e10 h, e0 h, e1' h, e2 h, e3 h]),
    H.uG_gen (by
      rintro (h | h | h | h | h | h)
      exacts [hd h, hx 10 h.symm, hx 0 h.symm, hx 1 h.symm, hx 2 h.symm, hx 3 h.symm]),
    j_cellOf_φ]

theorem UHyp.uG_d : Γ.uG d a d = Γ.uCell d a 2 := by
  unfold uG; rw [if_pos (Or.inl rfl)]

theorem UHyp.uG_uM_sp (i : Fin 12) (hi : i = 0 ∨ i = 10) : Γ.uG d a (Γ.uM d a i) = Γ.uCell d a 2 := by
  unfold uG; rcases hi with rfl | rfl
  · rw [if_pos (Or.inr (Or.inr rfl))]
  · rw [if_pos (Or.inr (Or.inl rfl))]

theorem UHyp.uG_uMv (i : Fin 12) (hi : i = 1 ∨ i = 2 ∨ i = 3) :
    Γ.uG d a (Γ.uM d a i) = Γ.uCell d a (if i = 1 then 5 else if i = 2 then 4 else 6) := by
  have ne := fun (i j : Fin 12) (h : i ≠ j) => (H.uM_inj.ne h)
  have nd := H.uM_ne_d
  have h0 : ¬ (Γ.uM d a i = d ∨ Γ.uM d a i = Γ.uM d a 10 ∨ Γ.uM d a i = Γ.uM d a 0) := by
    rintro (h | h | h)
    · exact nd i h
    · exact ne i 10 (by rcases hi with rfl | rfl | rfl <;> decide) h
    · exact ne i 0 (by rcases hi with rfl | rfl | rfl <;> decide) h
  unfold uG
  rw [if_neg h0]
  rcases hi with rfl | rfl | rfl
  · rw [if_pos rfl]; rfl
  · rw [if_neg (ne 2 1 (by decide)), if_pos rfl]; rfl
  · rw [if_neg (ne 3 1 (by decide)), if_neg (ne 3 2 (by decide)), if_pos rfl]; rfl

theorem UHyp.uG_ph (x : D) : Γ.uG d a (H.ph x) = Γ.uG d a x := by
  by_cases hd : x = d
  · rw [hd]
    rw [H.ph_of (fun i => H.uM_ne_d i), H.uG_d]
    show Γ.uG d a (Γ.uM d a 10) = _
    exact H.uG_uM_sp 10 (Or.inr rfl)
  by_cases hx : ∃ i, Γ.uM d a i = x
  swap
  · push Not at hx; exact H.uG_ph_generic hx hd
  obtain ⟨i, rfl⟩ := hx
  rw [H.ph_uM]
  have ne := fun (i j : Fin 12) (h : i ≠ j) => (H.uM_inj.ne h)
  have nd := H.uM_ne_d
  have hcell := H.cell_uM
  -- the new cells through the changed darts, case by case
  fin_cases i
  · -- `a`: next is `d`
    show Γ.uG d a (Γ.σ (Γ.up1 d)) = Γ.uG d a (Γ.uM d a 0)
    rw [H.uG_uM_sp 0 (Or.inl rfl), show Γ.σ (Γ.up1 d) = d by unfold up1; rw [Γ.j_σ4], H.uG_d]
  · -- `σ a`: next is `φ (up1)`, in `P1`
    show Γ.uG d a (Γ.φ (Γ.up1 d)) = Γ.uG d a (Γ.uM d a 1)
    have hc : Γ.cellOf (Γ.φ (Γ.up1 d)) = Γ.uCell d a 5 := by rw [j_cellOf_φ]; rfl
    rw [H.uG_of hc (H.notSp hc (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)))]
    rw [H.uG_uMv 1 (by decide)]
    simp [uCI]
  · -- `σ² a`: next is `φ (up2)`, in `Q`
    show Γ.uG d a (Γ.φ (Γ.up2 d)) = Γ.uG d a (Γ.uM d a 2)
    have hc : Γ.cellOf (Γ.φ (Γ.up2 d)) = Γ.uCell d a 4 := by
      rw [j_cellOf_φ]; exact hcell 10
    have h1 : Γ.φ (Γ.up2 d) ≠ d := by
      intro h
      apply ne 9 10 (by decide)
      apply Γ.φ.injective
      show Γ.σ (Γ.α (Γ.α (Γ.up1 d))) = Γ.φ (Γ.up2 d)
      rw [h, j_α_α]; unfold up1; rw [Γ.j_σ4]
    have h2 : Γ.φ (Γ.up2 d) ≠ Γ.uM d a 10 := by
      intro h
      apply nd 10
      apply Γ.φ.injective
      show Γ.φ (Γ.up2 d) = Γ.up2 d
      exact h
    rw [H.uG_of hc (H.notSp hc (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => ⟨h1, h2⟩))]
    rw [H.uG_uMv 2 (by decide)]
    simp [uCI]
  · -- `σ³ a`: next is `σ up2`, in `P2`
    show Γ.uG d a (Γ.σ (Γ.up2 d)) = Γ.uG d a (Γ.uM d a 3)
    have hc : Γ.cellOf (Γ.σ (Γ.up2 d)) = Γ.uCell d a 6 := by rw [j_cellOf_σ]; rfl
    rw [H.uG_of hc (H.notSp hc (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)))]
    rw [H.uG_uMv 3 (by decide)]
    simp [uCI]
  · -- `α a` (in `L`): next is `φ (σ a)`
    show Γ.uG d a (Γ.φ (Γ.σ a)) = Γ.uG d a (Γ.uM d a 4)
    have hc : Γ.cellOf (Γ.φ (Γ.σ a)) = Γ.uCell d a 1 := by rw [j_cellOf_φ]; rfl
    have h1 : Γ.φ (Γ.σ a) ≠ Γ.uM d a 1 := by
      intro h; apply ne 5 0 (by decide); simp only [uM]
      have : Γ.σ (Γ.α (Γ.σ a)) = Γ.σ a := h
      exact Γ.σ.injective (this.trans (rfl : Γ.σ a = Γ.σ a)) |>.trans rfl
    rw [H.uG_of hc (H.notSp hc (fun h => absurd h (by decide)) (fun _ => h1) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))),
      H.uG_of (hcell 4) (H.notSp (hcell 4) (fun h => absurd h (by decide)) (fun _ => ne 4 1 (fun h => absurd h (by decide)))
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)))]
    rfl
  · -- `α σ a` (in `T`): next is `φ a`, in `B`
    show Γ.uG d a (Γ.φ a) = Γ.uG d a (Γ.uM d a 5)
    have hc : Γ.cellOf (Γ.φ a) = Γ.uCell d a 0 := by rw [j_cellOf_φ]; rfl
    have h1 : Γ.φ a ≠ Γ.uM d a 0 := by
      intro h; apply ne 4 3 (by decide)
      have h' : Γ.σ (Γ.α a) = a := h
      have := congrArg (fun z => Γ.σ (Γ.σ (Γ.σ z))) h'
      simp only [Γ.j_σ4] at this
      exact this
    rw [H.uG_of hc (H.notSp hc (fun _ => h1) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))),
      H.uG_of (hcell 5) (H.notSp (hcell 5) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
        (fun _ => ne 5 2 (fun h => absurd h (by decide))) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)))]
    rfl
  · -- `α σ² a` (in `R`): next is `φ (σ³ a)`
    show Γ.uG d a (Γ.φ (Γ.σ (Γ.σ (Γ.σ a)))) = Γ.uG d a (Γ.uM d a 6)
    have hc : Γ.cellOf (Γ.φ (Γ.σ (Γ.σ (Γ.σ a)))) = Γ.uCell d a 3 := by rw [j_cellOf_φ]; rfl
    have h1 : Γ.φ (Γ.σ (Γ.σ (Γ.σ a))) ≠ Γ.uM d a 3 := by
      intro h; apply ne 7 2 (by decide)
      have : Γ.σ (Γ.α (Γ.σ (Γ.σ (Γ.σ a)))) = Γ.σ (Γ.σ (Γ.σ a)) := h
      exact Γ.σ.injective this
    rw [H.uG_of hc (H.notSp hc (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => h1) (fun h => absurd h (by decide))),
      H.uG_of (hcell 6) (H.notSp (hcell 6) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
        (fun _ => ne 6 3 (fun h => absurd h (by decide))) (fun h => absurd h (by decide)))]
    rfl
  · -- `α σ³ a` (in `B`): next is `φ (σ² a)`, in `T`
    show Γ.uG d a (Γ.φ (Γ.σ (Γ.σ a))) = Γ.uG d a (Γ.uM d a 7)
    have hc : Γ.cellOf (Γ.φ (Γ.σ (Γ.σ a))) = Γ.uCell d a 2 := by rw [j_cellOf_φ]; rfl
    have h1 : Γ.φ (Γ.σ (Γ.σ a)) ≠ Γ.uM d a 2 := by
      intro h; apply ne 6 1 (by decide)
      have : Γ.σ (Γ.α (Γ.σ (Γ.σ a))) = Γ.σ (Γ.σ a) := h
      exact Γ.σ.injective this
    rw [H.uG_of hc (H.notSp hc (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => h1) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))),
      H.uG_of (hcell 7) (H.notSp (hcell 7) (fun _ => ne 7 0 (fun h => absurd h (by decide))) (fun h => absurd h (by decide))
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)))]
    rfl
  · -- `up1` (in `P1`): next is `σ a`
    show Γ.uG d a (Γ.uM d a 1) = Γ.uG d a (Γ.uM d a 8)
    rw [H.uG_of (hcell 8) (H.notSp (hcell 8) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)))]
    rw [H.uG_uMv 1 (by decide)]
    simp [uCI]
  · -- `α up1` (in `Q`): next is `σ² a`
    show Γ.uG d a (Γ.uM d a 2) = Γ.uG d a (Γ.uM d a 9)
    rw [H.uG_of (hcell 9) (H.notSp (hcell 9) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => ⟨nd 9, ne 9 10 (fun h => absurd h (by decide))⟩))]
    rw [H.uG_uMv 2 (by decide)]
    simp [uCI]
  · -- `up2` (in `Q`): next is `a`
    show Γ.uG d a (Γ.σ (Γ.uM d a 3)) = Γ.uG d a (Γ.uM d a 10)
    rw [H.σ_uM3, H.uG_uM_sp 0 (Or.inl rfl), H.uG_uM_sp 10 (Or.inr rfl)]
  · -- `α up2` (in `P2`): next is `σ³ a`
    show Γ.uG d a (Γ.uM d a 3) = Γ.uG d a (Γ.uM d a 11)
    rw [H.uG_of (hcell 11) (H.notSp (hcell 11) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)))]
    rw [H.uG_uMv 3 (by decide)]
    simp [uCI]

end Hyp

end SConf

end Pca.Sweep
