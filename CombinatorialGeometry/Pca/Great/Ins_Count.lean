/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Inserting a new curve: connectivity and the counts of crossings and segments
-/
import Pca.Great.Ins_Walk
import Pca.Great.Map_Euler

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

namespace InsWalk

variable {A : Arrangement n D} {K : ℕ} (W : InsWalk A K)

/-- One step of the new map. -/
def Step' (a b : D ⊕ (Fin K × Fin 4)) : Prop := b = W.σ' a ∨ b = W.α' a

theorem conn_σ (x : D ⊕ (Fin K × Fin 4)) : Relation.EqvGen W.Step' x (W.σ' x) :=
  .rel _ _ (Or.inl rfl)
theorem conn_α (x : D ⊕ (Fin K × Fin 4)) : Relation.EqvGen W.Step' x (W.α' x) :=
  .rel _ _ (Or.inr rfl)

theorem conn_old_α (d : D) : Relation.EqvGen W.Step' (.inl d) (.inl (A.α d)) := by
  by_cases h1 : ∃ i, W.t i = d
  · obtain ⟨i, rfl⟩ := h1
    have e1 := W.conn_α (.inl (W.t i))
    rw [α'_apply, W.αfun_t] at e1
    have e2 := W.conn_σ (.inr (i, 0))
    have e3 := W.conn_σ (W.σ' (.inr (i, 0)))
    rw [W.σσ'_u] at e3
    have e4 := W.conn_α (.inr (i, 1))
    rw [α'_apply, W.αfun_v] at e4
    exact e1.trans _ _ _ (e2.trans _ _ _ (e3.trans _ _ _ e4))
  by_cases h2 : ∃ i, A.α (W.t i) = d
  · obtain ⟨i, rfl⟩ := h2
    have e1 := W.conn_α (.inl (A.α (W.t i)))
    rw [α'_apply, W.αfun_αt] at e1
    have e2 := W.conn_σ (.inr (i, 1))
    have e3 := W.conn_σ (W.σ' (.inr (i, 1)))
    rw [W.σσ'_v] at e3
    have e4 := W.conn_α (.inr (i, 0))
    rw [α'_apply, W.αfun_u] at e4
    rw [A.isArrangement.α_α]
    exact e1.trans _ _ _ (e2.trans _ _ _ (e3.trans _ _ _ e4))
  push Not at h1 h2
  have := W.conn_α (.inl d)
  rwa [W.α'_free ⟨h1, h2⟩] at this

theorem conn_old (d e : D) : Relation.EqvGen W.Step' (.inl d) (.inl e) := by
  induction A.connected d e with
  | rel a b h =>
    rcases h with rfl | rfl
    · exact W.conn_σ (.inl a)
    · exact W.conn_old_α a
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2

theorem conn_new (i : Fin K) (r : Fin 4) :
    Relation.EqvGen W.Step' (.inr (i, r)) (.inl (W.t i)) := by
  have h0 : Relation.EqvGen W.Step' (.inr (i, 0)) (.inl (W.t i)) := by
    have := W.conn_α (.inr (i, 0)); rwa [α'_apply, W.αfun_u] at this
  have e1 := W.conn_σ (.inr (i, 0))
  have e2 := W.conn_σ (.inr (i, 3))
  have e3 := W.conn_σ (.inr (i, 1))
  rw [W.σ'_inr] at e1 e2 e3
  change Relation.EqvGen W.Step' (.inr (i, 0)) (.inr (i, 3)) at e1
  change Relation.EqvGen W.Step' (.inr (i, 3)) (.inr (i, 1)) at e2
  change Relation.EqvGen W.Step' (.inr (i, 1)) (.inr (i, 2)) at e3
  fin_cases r
  · exact h0
  · exact (e2.symm.trans _ _ _ e1.symm).trans _ _ _ h0
  · exact (e3.symm.trans _ _ _ (e2.symm.trans _ _ _ e1.symm)).trans _ _ _ h0
  · exact e1.symm.trans _ _ _ h0

theorem conn (x y : D ⊕ (Fin K × Fin 4)) : Relation.EqvGen W.Step' x y := by
  have h : ∀ z, ∃ d, Relation.EqvGen W.Step' z (.inl d) := by
    intro z
    rcases z with d | ⟨i, r⟩
    · exact ⟨d, .refl _⟩
    · exact ⟨W.t i, W.conn_new i r⟩
  obtain ⟨d, hd⟩ := h x
  obtain ⟨e, he⟩ := h y
  exact hd.trans _ _ _ ((W.conn_old d e).trans _ _ _ he.symm)

omit [DecidableEq D] in
theorem card_D' (K : ℕ) : Fintype.card (D ⊕ (Fin K × Fin 4)) = Fintype.card D + 4 * K := by
  simp [Fintype.card_sum, Fintype.card_prod, mul_comm]

theorem card_V' : Fintype.card (Orbit W.σ') = Fintype.card (Orbit A.σ) + K := by
  have h1 := card_eq_sum_size W.σ'
  have h2 := card_eq_sum_size A.σ
  have s1 : ∀ o : Orbit W.σ', o.size = 4 := fun o => by
    obtain ⟨y, rfl⟩ := o.exists_mk
    show (Orbit.mk W.σ' y).darts.card = 4
    rw [Orbit.darts_mk]; exact W.card_crossing' y
  have s2 : ∀ o : Orbit A.σ, o.size = 4 := fun o => by
    obtain ⟨y, rfl⟩ := o.exists_mk
    show (Orbit.mk A.σ y).darts.card = 4
    rw [Orbit.darts_mk]; exact A.isArrangement.card_crossing y
  simp only [s1, s2, sum_const, card_univ, smul_eq_mul] at h1 h2
  rw [card_D'] at h1
  omega

theorem card_E' : Fintype.card (Orbit W.α') = Fintype.card (Orbit A.α) + 2 * K := by
  have h1 := MapFacts.card_eq_two_mul_card_orbit W.α' (fun x => W.αfun_αfun x) W.α'_ne
  have h2 := MapFacts.card_eq_two_mul_card_orbit A.α A.isArrangement.α_α A.isArrangement.α_ne
  rw [card_D'] at h1
  omega

end InsWalk

end Pca.Great
