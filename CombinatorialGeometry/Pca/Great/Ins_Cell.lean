/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Inserting a new curve: the cells (`doc/pca/great.md` 4.1)

Each visited cell splits into two cells: the label `Λ` (old cell, or the index of the new half)
is constant on the cells of the new map and takes every value, so the new map has at least
`F + K` cells.
-/
import Pca.Great.Ins_Count

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

/-- `z` is the first point of the forward `f`-orbit of `d` satisfying `P`. -/
def FirstHit {X : Type*} (f : Perm X) (P : X → Prop) (d z : X) : Prop :=
  ∃ k : ℕ, (f ^ k) d = z ∧ P z ∧ ∀ j < k, ¬ P ((f ^ j) d)

theorem firstHit_self {X : Type*} {f : Perm X} {P : X → Prop} {d : X} (h : P d) :
    FirstHit f P d d := ⟨0, rfl, h, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

theorem firstHit_of_next {X : Type*} {f : Perm X} {P : X → Prop} {d z : X} (h : ¬ P d)
    (hz : FirstHit f P (f d) z) : FirstHit f P d z := by
  obtain ⟨k, rfl, hP, hmin⟩ := hz
  refine ⟨k + 1, by rw [pow_succ, Perm.mul_apply], hP, fun j hj => ?_⟩
  rcases j with _ | j
  · exact h
  · rw [pow_succ, Perm.mul_apply]; exact hmin j (by omega)

theorem firstHit_unique {X : Type*} {f : Perm X} {P : X → Prop} {d z z' : X}
    (h : FirstHit f P d z) (h' : FirstHit f P d z') : z = z' := by
  obtain ⟨k, rfl, hP, hmin⟩ := h
  obtain ⟨k', rfl, hP', hmin'⟩ := h'
  rcases lt_trichotomy k k' with hk | rfl | hk
  · exact absurd hP (hmin' k hk)
  · rfl
  · exact absurd hP' (hmin k' hk)

theorem exists_firstHit {X : Type*} {f : Perm X} {P : X → Prop} {d : X}
    (h : ∃ k : ℕ, P ((f ^ k) d)) : ∃ z, FirstHit f P d z := by
  classical
  exact ⟨_, Nat.find h, rfl, Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

/-- In a cycle containing exactly the two hits `a ≠ b`, the first hit after `a` is `b`. -/
theorem firstHit_next {X : Type*} [Finite X] {f : Perm X} {P : X → Prop} {a b : X} (hab : a ≠ b)
    (hb : P b) (hsc : f.SameCycle a b) (honly : ∀ z, f.SameCycle a z → P z → z = a ∨ z = b) :
    FirstHit f P (f a) b := by
  classical
  have hex : ∃ m : ℕ, (f ^ (m + 1)) a = b := by
    obtain ⟨k, hk⟩ := hsc.exists_nat_pow_eq
    rcases k with _ | k
    · exact absurd hk hab
    · exact ⟨k, hk⟩
  refine ⟨Nat.find hex, ?_, hb, fun j hj hP => ?_⟩
  · have := Nat.find_spec hex; rwa [pow_succ, Perm.mul_apply] at this
  · rw [← Perm.mul_apply, ← pow_succ] at hP
    rcases honly _ (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)) hP with h | h
    · -- back at `a` before reaching `b`
      have hm := Nat.find_spec hex
      have e : (f ^ (Nat.find hex + 1)) a = (f ^ (Nat.find hex - (j + 1) + 1)) ((f ^ (j + 1)) a) := by
        rw [← Perm.mul_apply, ← pow_add]; congr 2; omega
      rw [h] at e
      exact Nat.find_min hex (show Nat.find hex - (j + 1) < Nat.find hex by omega) (e.symm.trans hm)
    · exact Nat.find_min hex hj h

namespace InsWalk

variable {A : Arrangement n D} {K : ℕ} (W : InsWalk A K)

/-- The crossed darts. -/
def Hit (d : D) : Prop := (∃ i, W.t i = d) ∨ ∃ j, A.α (W.t j) = d

theorem hit_of_cell {i : Fin K} {z : D} (hz : A.cellOf z = A.cellOf (W.t i)) (h : W.Hit z) :
    z = W.t i ∨ z = A.α (W.t (W.pv i)) := by
  rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; rw [W.cell_inj hz]
  · right
    rw [W.adj] at hz
    have := W.cell_inj hz
    change W.nx k = i at this
    rw [← this, W.pv_nx]

open Classical in
/-- The label of a cell half. -/
noncomputable def lab (z : D) : A.Cell ⊕ Fin K :=
  if hz : ∃ j, A.α (W.t j) = z then .inr (Classical.choose hz) else .inl (A.cellOf z)

theorem lab_t (i : Fin K) : W.lab (W.t i) = .inl (A.cellOf (W.t i)) := by
  have : ¬ ∃ j, A.α (W.t j) = W.t i := fun ⟨j, hj⟩ => W.t_ne_α i j hj.symm
  simp only [lab, dif_neg this]

theorem lab_αt (j : Fin K) : W.lab (A.α (W.t j)) = .inr j := by
  have h : ∃ k, A.α (W.t k) = A.α (W.t j) := ⟨j, rfl⟩
  simp only [lab, dif_pos h]
  rw [W.αt_inj (Classical.choose_spec h)]

open Classical in
/-- The label of a dart of the new map. -/
noncomputable def Λ : D ⊕ (Fin K × Fin 4) → A.Cell ⊕ Fin K
  | .inl d =>
    if h : ∃ k : ℕ, W.Hit ((A.φ ^ k) d) then W.lab ((A.φ ^ Nat.find h) d) else .inl (A.cellOf d)
  | .inr (i, r) =>
    if r = 0 then .inl (A.cellOf (W.t (W.nx i)))
    else if r = 1 then .inr (W.pv i)
    else if r = 2 then .inr i
    else .inl (A.cellOf (W.t i))

open Classical in
theorem Λ_hit {d z : D} (h : FirstHit A.φ W.Hit d z) : W.Λ (.inl d) = W.lab z := by
  obtain ⟨k, hk, hP, hmin⟩ := h
  have hex : ∃ k : ℕ, W.Hit ((A.φ ^ k) d) := ⟨k, hk ▸ hP⟩
  simp only [Λ, dif_pos hex]
  congr 1
  exact firstHit_unique ⟨_, rfl, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩ ⟨k, hk, hP, hmin⟩

open Classical in
theorem Λ_nohit {d : D} (h : ¬ ∃ k : ℕ, W.Hit ((A.φ ^ k) d)) :
    W.Λ (.inl d) = .inl (A.cellOf d) := by
  simp only [Λ, dif_neg h]

theorem Λ_u (i : Fin K) : W.Λ (.inr (i, 0)) = .inl (A.cellOf (W.t (W.nx i))) := rfl
theorem Λ_v (i : Fin K) : W.Λ (.inr (i, 1)) = .inr (W.pv i) := rfl
theorem Λ_p (i : Fin K) : W.Λ (.inr (i, 2)) = .inr i := rfl
theorem Λ_q (i : Fin K) : W.Λ (.inr (i, 3)) = .inl (A.cellOf (W.t i)) := rfl

/-- The new face permutation. -/
noncomputable abbrev φ' : Perm (D ⊕ (Fin K × Fin 4)) := W.σ' * W.α'

theorem φ'_apply (x : D ⊕ (Fin K × Fin 4)) : W.φ' x = W.σ' (W.α' x) := rfl

theorem two_hits (i : Fin K) : FirstHit A.φ W.Hit (A.φ (A.α (W.t (W.pv i)))) (W.t i) := by
  have hc : A.cellOf (A.α (W.t (W.pv i))) = A.cellOf (W.t i) := by
    rw [W.adj]; show A.cellOf (W.t (W.nx (W.pv i))) = _; rw [W.nx_pv]
  refine firstHit_next (fun h => W.t_ne_α _ _ h.symm) (Or.inl ⟨i, rfl⟩)
    (A.cellOf_eq_iff.1 hc) fun z hz hP => ?_
  have := W.hit_of_cell ((A.cellOf_eq_iff.2 hz).symm.trans hc) hP
  tauto

theorem two_hits' (i : Fin K) : FirstHit A.φ W.Hit (A.φ (W.t i)) (A.α (W.t (W.pv i))) := by
  have hc : A.cellOf (A.α (W.t (W.pv i))) = A.cellOf (W.t i) := by
    rw [W.adj]; show A.cellOf (W.t (W.nx (W.pv i))) = _; rw [W.nx_pv]
  refine firstHit_next (fun h => W.t_ne_α _ _ h) (Or.inr ⟨_, rfl⟩)
    (A.cellOf_eq_iff.1 hc.symm) fun z hz hP => W.hit_of_cell (A.cellOf_eq_iff.2 hz).symm hP

theorem Λ_φ' (x : D ⊕ (Fin K × Fin 4)) : W.Λ (W.φ' x) = W.Λ x := by
  rcases x with d | ⟨i, r⟩
  · by_cases h1 : ∃ i, W.t i = d
    · obtain ⟨i, rfl⟩ := h1
      rw [φ'_apply, α'_apply, W.αfun_t, W.σ'_inr, W.Λ_hit (firstHit_self (Or.inl ⟨i, rfl⟩)),
        W.lab_t]
      rfl
    by_cases h2 : ∃ i, A.α (W.t i) = d
    · obtain ⟨i, rfl⟩ := h2
      rw [φ'_apply, α'_apply, W.αfun_αt, W.σ'_inr, W.Λ_hit (firstHit_self (Or.inr ⟨i, rfl⟩)),
        W.lab_αt]
      rfl
    push Not at h1 h2
    have hnot : ¬ W.Hit d := by rintro (⟨i, hi⟩ | ⟨i, hi⟩); exacts [h1 i hi, h2 i hi]
    rw [φ'_apply, W.α'_free ⟨h1, h2⟩, W.σ'_inl]
    change W.Λ (.inl (A.φ d)) = _
    by_cases hex : ∃ k : ℕ, W.Hit ((A.φ ^ k) (A.φ d))
    · obtain ⟨z, hz⟩ := exists_firstHit hex
      rw [W.Λ_hit hz, W.Λ_hit (firstHit_of_next hnot hz)]
    · have hex' : ¬ ∃ k : ℕ, W.Hit ((A.φ ^ k) d) := by
        rintro ⟨k, hk⟩
        rcases k with _ | k
        · exact hnot hk
        · exact hex ⟨k, by rwa [pow_succ, Perm.mul_apply] at hk⟩
      rw [W.Λ_nohit hex, W.Λ_nohit hex', A.cellOf_φ]
  · fin_cases r
    · -- `u i`
      show W.Λ (W.σ' (W.αfun (.inr (i, 0)))) = W.Λ (.inr (i, 0))
      rw [W.αfun_u, W.σ'_inl]
      have h := W.two_hits (W.nx i)
      rw [W.pv_nx, A.φ_apply, A.isArrangement.α_α] at h
      rw [W.Λ_hit h, W.lab_t, W.Λ_u]
    · -- `v i`
      show W.Λ (W.σ' (W.αfun (.inr (i, 1)))) = W.Λ (.inr (i, 1))
      rw [W.αfun_v, W.σ'_inl]
      have h := W.two_hits' i
      rw [A.φ_apply] at h
      rw [W.Λ_hit h, W.lab_αt, W.Λ_v]
    · -- `p i`
      show W.Λ (W.σ' (W.αfun (.inr (i, 2)))) = W.Λ (.inr (i, 2))
      rw [W.αfun_p, W.σ'_inr]
      show W.Λ (.inr (W.nx i, 1)) = W.Λ (.inr (i, 2))
      rw [W.Λ_v, W.Λ_p, W.pv_nx]
    · -- `q i`
      show W.Λ (W.σ' (W.αfun (.inr (i, 3)))) = W.Λ (.inr (i, 3))
      rw [W.αfun_q, W.σ'_inr]
      show W.Λ (.inr (W.pv i, 0)) = W.Λ (.inr (i, 3))
      rw [W.Λ_u, W.Λ_q, W.nx_pv]

theorem Λ_surj : Function.Surjective W.Λ := by
  rintro (g | j)
  · by_cases hv : ∃ i, A.cellOf (W.t i) = g
    · obtain ⟨i, rfl⟩ := hv
      exact ⟨.inr (i, 3), W.Λ_q i⟩
    · obtain ⟨d, rfl⟩ := g.exists_mk
      refine ⟨.inl d, W.Λ_nohit ?_⟩
      rintro ⟨k, hk⟩
      have hc : A.cellOf ((A.φ ^ k) d) = A.cellOf d :=
        A.cellOf_eq_iff.2 (Perm.sameCycle_pow_left.2 (Perm.SameCycle.refl _ _))
      rcases hk with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact hv ⟨i, by rw [hi, hc]; rfl⟩
      · exact hv ⟨W.nx i, by rw [← W.adj, hi, hc]; rfl⟩
  · exact ⟨.inr (j, 2), W.Λ_p j⟩

theorem card_F' : Fintype.card (Orbit A.φ) + K ≤ Fintype.card (Orbit W.φ') := by
  have hinv : ∀ a b, W.φ'.SameCycle a b → W.Λ a = W.Λ b := by
    intro a b h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply, W.Λ_φ']
      exact ih (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _))
  let L : Orbit W.φ' → A.Cell ⊕ Fin K := Quotient.lift W.Λ hinv
  have hL : Function.Surjective L := by
    intro y
    obtain ⟨x, hx⟩ := W.Λ_surj y
    exact ⟨Orbit.mk _ x, hx⟩
  have := Fintype.card_le_of_surjective L hL
  rw [Fintype.card_sum, Fintype.card_fin] at this
  exact this

end InsWalk

end Pca.Great
