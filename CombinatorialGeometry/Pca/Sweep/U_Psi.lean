/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package U, helpers: the new cells above the sweep

The new cell of `α σ³ a` is `(B ∖ {a}) ∪ (T ∖ {σ² a})`, the new cell of `α a` is `L ∖ {σ a}`, the
new cell of `α σ² a` is `R ∖ {σ³ a}`; every other cell above `S` is unchanged. `uψ` maps old
cells to new cells.
-/
import Pca.Sweep.U_Euler

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {d a : D} {k : ℕ} {γ : Fin n}

variable (Γ) in
/-- The special darts of `uG`. -/
def uSp (d a : D) (x : D) : Prop :=
  x = d ∨ x = Γ.uM d a 10 ∨ x = Γ.uM d a 0 ∨ x = Γ.uM d a 1 ∨ x = Γ.uM d a 2 ∨ x = Γ.uM d a 3

section Hyp

variable (H : Γ.UHyp d a k γ)
include H

theorem UHyp.notSp_of {x : D} (hu : Γ.side (Γ.cellOf x) = 1)
    (hv : Γ.crossingOf x ≠ Γ.crossingOf a) : ¬ Γ.uSp d a x := by
  have hlow : ∀ y, Γ.cellOf y = Γ.uCell d a 4 → Γ.side (Γ.cellOf y) ≠ 1 := by
    intro y hy; rw [hy, H.side_uCell]; decide
  rintro (h | h | h | h | h | h) <;> rw [h] at hu hv
  · exact hlow d rfl hu
  · exact hlow _ (H.cell_uM 10) hu
  · exact hv (H.v_iff.2 (Or.inl rfl))
  · exact hv (H.v_iff.2 (Or.inr (Or.inl rfl)))
  · exact hv (H.v_iff.2 (Or.inr (Or.inr (Or.inl rfl))))
  · exact hv (H.v_iff.2 (Or.inr (Or.inr (Or.inr rfl))))

theorem UHyp.uG_up {x : D} (hu : Γ.side (Γ.cellOf x) = 1)
    (hv : Γ.crossingOf x ≠ Γ.crossingOf a) :
    Γ.uG d a x = if Γ.cellOf x = Γ.uCell d a 2 then Γ.uCell d a 0 else Γ.cellOf x :=
  H.uG_gen (H.notSp_of hu hv)

theorem UHyp.uG_spec {y : D} {f : Γ.Cell} (hf : f ≠ Γ.uCell d a 2) (hf4 : f ≠ Γ.uCell d a 4)
    (hf5 : f ≠ Γ.uCell d a 5) (hf6 : f ≠ Γ.uCell d a 6) (h : Γ.uG d a y = f) :
    ¬ Γ.uSp d a y ∧ (if Γ.cellOf y = Γ.uCell d a 2 then Γ.uCell d a 0 else Γ.cellOf y) = f := by
  unfold uG at h
  split_ifs at h with h1 h2 h3 h4 h5
  · exact absurd h.symm hf
  · exact absurd h.symm hf5
  · exact absurd h.symm hf4
  · exact absurd h.symm hf6
  · refine ⟨?_, by rw [if_pos h5]; exact h⟩; unfold uSp; tauto
  · refine ⟨?_, by rw [if_neg h5]; exact h⟩; unfold uSp; tauto

theorem UHyp.ph_eq_of : ∀ x, ¬ (fun x => ∃ i, Γ.uM d a i = x) x → H.ph x = Γ.φ x := by
  intro x hx
  push Not at hx
  exact H.ph_of hx

theorem UHyp.cellOf_pow_φ (x : D) (i : ℕ) : Γ.cellOf ((Γ.φ ^ i) x) = Γ.cellOf x := by
  induction i with
  | zero => rfl
  | succ i ih => rw [u_pow_succ, j_cellOf_φ, ih]

/-- In a cell whose only changed darts are `e` and `φ e`, every dart other than `φ e` is reached
by the new walk from `φ (φ e)`. -/
theorem UHyp.reach_cell {c : Fin 7} {ie iv : Fin 12} (honly : ∀ i, uCI i = c → i = ie ∨ i = iv)
    (hie : uCI ie = c) (hφ : Γ.φ (Γ.uM d a ie) = Γ.uM d a iv) {x : D}
    (hx : Γ.cellOf x = Γ.uCell d a c) (hne : x ≠ Γ.uM d a iv) :
    H.ph.SameCycle (Γ.φ (Γ.uM d a iv)) x := by
  rw [← hφ] at hne ⊢
  have hsc : Γ.φ.SameCycle (Γ.φ (Γ.φ (Γ.uM d a ie))) x := by
    rw [← Orbit.mk_eq_mk]
    change Γ.cellOf _ = Γ.cellOf x
    rw [j_cellOf_φ, j_cellOf_φ, H.cell_uM, hie, hx]
  obtain ⟨j, hj, hav⟩ := u_reach_before hsc hne
  rw [← hj, ← u_pow_eq_of_avoid H.ph_eq_of _ j ?_]
  · exact u_sameCycle_pow _ _ _
  intro i hi ⟨m, hm⟩
  have hc : Γ.cellOf (Γ.uM d a m) = Γ.uCell d a c := by
    rw [hm, H.cellOf_pow_φ, j_cellOf_φ, j_cellOf_φ, H.cell_uM, hie]
  rw [H.cell_uM] at hc
  rcases honly m (H.uCell_inj hc) with rfl | rfl
  · exact (hav i hi).1 hm.symm
  · exact (hav i hi).2 (hm.symm.trans hφ.symm)

theorem UHyp.ph_uM7 : H.ph (Γ.uM d a 7) = Γ.φ (Γ.uM d a 2) := by
  rw [H.ph_uM]; rfl
theorem UHyp.ph_uM5 : H.ph (Γ.uM d a 5) = Γ.φ (Γ.uM d a 0) := by
  rw [H.ph_uM]; rfl
theorem UHyp.ph_uM4 : H.ph (Γ.uM d a 4) = Γ.φ (Γ.uM d a 1) := by
  rw [H.ph_uM]; rfl
theorem UHyp.ph_uM6 : H.ph (Γ.uM d a 6) = Γ.φ (Γ.uM d a 3) := by
  rw [H.ph_uM]; rfl

theorem UHyp.φ_uM7 : Γ.φ (Γ.uM d a 7) = Γ.uM d a 0 := by
  show Γ.σ (Γ.α (Γ.α (Γ.σ (Γ.σ (Γ.σ a))))) = a
  rw [j_α_α, Γ.j_σ4]
theorem UHyp.φ_uM5 : Γ.φ (Γ.uM d a 5) = Γ.uM d a 2 := by
  show Γ.σ (Γ.α (Γ.α (Γ.σ a))) = Γ.σ (Γ.σ a); rw [j_α_α]
theorem UHyp.φ_uM4 : Γ.φ (Γ.uM d a 4) = Γ.uM d a 1 := by
  show Γ.σ (Γ.α (Γ.α a)) = Γ.σ a; rw [j_α_α]
theorem UHyp.φ_uM6 : Γ.φ (Γ.uM d a 6) = Γ.uM d a 3 := by
  show Γ.σ (Γ.α (Γ.α (Γ.σ (Γ.σ a)))) = Γ.σ (Γ.σ (Γ.σ a)); rw [j_α_α]

/-- The merged cell. -/
theorem UHyp.sc_T {x : D} (hx : Γ.cellOf x = Γ.uCell d a 2) (hne : x ≠ Γ.uM d a 2) :
    H.ph.SameCycle (Γ.uM d a 7) x := by
  have := H.reach_cell (c := 2) (ie := 5) (iv := 2) (by decide) rfl H.φ_uM5 hx hne
  rw [← H.ph_uM7] at this
  exact (u_sameCycle_apply _ _).trans this

theorem UHyp.sc_B {x : D} (hx : Γ.cellOf x = Γ.uCell d a 0) (hne : x ≠ Γ.uM d a 0) :
    H.ph.SameCycle (Γ.uM d a 7) x := by
  have h5 := H.sc_T (H.cell_uM 5) (H.uM_inj.ne (by decide))
  have := H.reach_cell (c := 0) (ie := 7) (iv := 0) (by decide) rfl H.φ_uM7 hx hne
  rw [← H.ph_uM5] at this
  exact h5.trans ((u_sameCycle_apply _ _).trans this)

theorem UHyp.sc_L {x : D} (hx : Γ.cellOf x = Γ.uCell d a 1) (hne : x ≠ Γ.uM d a 1) :
    H.ph.SameCycle (Γ.uM d a 4) x := by
  have := H.reach_cell (c := 1) (ie := 4) (iv := 1) (by decide) rfl H.φ_uM4 hx hne
  rw [← H.ph_uM4] at this
  exact (u_sameCycle_apply _ _).trans this

theorem UHyp.sc_R {x : D} (hx : Γ.cellOf x = Γ.uCell d a 3) (hne : x ≠ Γ.uM d a 3) :
    H.ph.SameCycle (Γ.uM d a 6) x := by
  have := H.reach_cell (c := 3) (ie := 6) (iv := 3) (by decide) rfl H.φ_uM6 hx hne
  rw [← H.ph_uM6] at this
  exact (u_sameCycle_apply _ _).trans this

/-- Cells above `S` other than `B, L, T, R` do not change. -/
theorem UHyp.orbit_other {x : D} (hu : Γ.side (Γ.cellOf x) = 1)
    (hc : ∀ c : Fin 7, c.val < 4 → Γ.cellOf x ≠ Γ.uCell d a c) :
    orbitFinset H.ph x = orbitFinset Γ.φ x := by
  refine u_orbitFinset_of_avoid H.ph_eq_of fun i ⟨m, hm⟩ => ?_
  have h1 : Γ.cellOf (Γ.uM d a m) = Γ.cellOf x := by rw [hm, H.cellOf_pow_φ]
  rw [H.cell_uM] at h1
  have hs := H.side_uCell (uCI m)
  rw [h1, hu] at hs
  by_cases h4 : (uCI m).val < 4
  · exact hc _ h4 h1.symm
  · rw [if_neg h4] at hs; exact absurd hs (by decide)

theorem UHyp.uG_of_mem {x y : D} (h : y ∈ orbitFinset H.ph x) : Γ.uG d a y = Γ.uG d a x := by
  obtain ⟨i, rfl⟩ := (mem_orbitFinset.1 h).exists_nat_pow_eq
  exact H.uG_pow x i

theorem UHyp.uCell_ne {c c' : Fin 7} (h : c ≠ c') : Γ.uCell d a c ≠ Γ.uCell d a c' :=
  fun h' => h (H.uCell_inj h')

theorem UHyp.up_uM {i : Fin 12} (hi : 4 ≤ i.val) (hc : (uCI i).val < 4) :
    Γ.side (Γ.cellOf (Γ.uM d a i)) = 1 := by
  rw [H.cell_uM, H.side_uCell, if_pos hc]

theorem UHyp.orbit_merge : orbitFinset H.ph (Γ.uM d a 7) =
    (orbitFinset Γ.φ a).erase a ∪ (orbitFinset Γ.φ (Γ.σ (Γ.σ a))).erase (Γ.σ (Γ.σ a)) := by
  have hG : Γ.uG d a (Γ.uM d a 7) = Γ.uCell d a 0 := by
    rw [H.uG_up (H.up_uM (by decide) (by decide)) (H.notv_uM (by decide)), H.cell_uM]
    exact if_neg (H.uCell_ne (by decide))
  ext y
  simp only [mem_union, mem_erase, mem_orbitFinset]
  constructor
  · intro hy
    have h1 := (H.uG_of_mem (mem_orbitFinset.2 hy)).trans hG
    obtain ⟨hsp, h2⟩ := H.uG_spec (H.uCell_ne (by decide)) (H.uCell_ne (by decide))
      (H.uCell_ne (by decide)) (H.uCell_ne (by decide)) h1
    unfold uSp at hsp
    split_ifs at h2 with h3
    · right
      refine ⟨fun h => hsp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))), ?_⟩
      rw [← Orbit.mk_eq_mk]; exact h3.symm
    · left
      refine ⟨fun h => hsp (Or.inr (Or.inr (Or.inl h))), ?_⟩
      rw [← Orbit.mk_eq_mk]; exact h2.symm
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact H.sc_B (Orbit.mk_eq_mk.2 h2).symm h1
    · exact H.sc_T (Orbit.mk_eq_mk.2 h2).symm h1

theorem UHyp.orbit_L : orbitFinset H.ph (Γ.uM d a 4) =
    (orbitFinset Γ.φ (Γ.σ a)).erase (Γ.σ a) := by
  have hG : Γ.uG d a (Γ.uM d a 4) = Γ.uCell d a 1 := by
    rw [H.uG_up (H.up_uM (by decide) (by decide)) (H.notv_uM (by decide)), H.cell_uM]
    exact if_neg (H.uCell_ne (by decide))
  ext y
  simp only [mem_erase, mem_orbitFinset]
  constructor
  · intro hy
    have h1 := (H.uG_of_mem (mem_orbitFinset.2 hy)).trans hG
    obtain ⟨hsp, h2⟩ := H.uG_spec (H.uCell_ne (by decide)) (H.uCell_ne (by decide))
      (H.uCell_ne (by decide)) (H.uCell_ne (by decide)) h1
    unfold uSp at hsp
    split_ifs at h2 with h3
    · exact absurd h2 (H.uCell_ne (by decide))
    · refine ⟨fun h => hsp (Or.inr (Or.inr (Or.inr (Or.inl h)))), ?_⟩
      rw [← Orbit.mk_eq_mk]; exact h2.symm
  · rintro ⟨h1, h2⟩
    exact H.sc_L (Orbit.mk_eq_mk.2 h2).symm h1

theorem UHyp.orbit_R : orbitFinset H.ph (Γ.uM d a 6) =
    (orbitFinset Γ.φ (Γ.σ (Γ.σ (Γ.σ a)))).erase (Γ.σ (Γ.σ (Γ.σ a))) := by
  have hG : Γ.uG d a (Γ.uM d a 6) = Γ.uCell d a 3 := by
    rw [H.uG_up (H.up_uM (by decide) (by decide)) (H.notv_uM (by decide)), H.cell_uM]
    exact if_neg (H.uCell_ne (by decide))
  ext y
  simp only [mem_erase, mem_orbitFinset]
  constructor
  · intro hy
    have h1 := (H.uG_of_mem (mem_orbitFinset.2 hy)).trans hG
    obtain ⟨hsp, h2⟩ := H.uG_spec (H.uCell_ne (by decide)) (H.uCell_ne (by decide))
      (H.uCell_ne (by decide)) (H.uCell_ne (by decide)) h1
    unfold uSp at hsp
    split_ifs at h2 with h3
    · exact absurd h2 (H.uCell_ne (by decide))
    · refine ⟨fun h => hsp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))), ?_⟩
      rw [← Orbit.mk_eq_mk]; exact h2.symm
  · rintro ⟨h1, h2⟩
    exact H.sc_R (Orbit.mk_eq_mk.2 h2).symm h1

end Hyp

end SConf

end Pca.Sweep
