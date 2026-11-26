/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Inserting a new curve: the local axioms and the straight walks (`doc/pca/great.md` 4.1)
-/
import Pca.Great.Ins_Base

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

theorem period_eq_of_iff {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {f : Perm X} {g : Perm Y} {x : X} {y : Y} (h : ∀ k, (f^[k]) x = x ↔ (g^[k]) y = y) :
    period f x = period g y := by
  apply le_antisymm
  · exact Nat.find_min' _ ⟨period_pos g y, (h _).2 (iterate_period g y)⟩
  · exact Nat.find_min' _ ⟨period_pos f x, (h _).1 (iterate_period f x)⟩

namespace InsWalk

variable {A : Arrangement n D} {K : ℕ} (W : InsWalk A K)

theorem σ'_inl (d : D) : W.σ' (.inl d) = .inl (A.σ d) := rfl
theorem σ'_inr (i : Fin K) (r : Fin 4) :
    W.σ' (.inr (i, r)) = .inr (i, s4 r) := rfl

theorem σ'_iterate_inl (k : ℕ) (d : D) :
    (W.σ'^[k]) (.inl d) = .inl ((A.σ^[k]) d) := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, W.σ'_inl, ih, ← Function.iterate_succ_apply]

theorem σ'_iterate_inr (k : ℕ) (i : Fin K) (r : Fin 4) :
    (W.σ'^[k]) (.inr (i, r)) = .inr (i, (s4^[k]) r) := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, W.σ'_inr, ih, ← Function.iterate_succ_apply]

theorem s4_facts : ∀ r : Fin 4, (s4^[4]) r = r ∧ ∀ m < 4, 0 < m → (s4^[m]) r ≠ r := by decide

theorem card_crossing' (x : D ⊕ (Fin K × Fin 4)) :
    (orbitFinset W.σ' x).card = 4 := by
  rw [card_orbitFinset]
  rcases x with d | ⟨i, r⟩
  · refine (period_eq_of_iff (g := A.σ) (y := d) fun k => ?_).trans (A.period_σ d)
    rw [W.σ'_iterate_inl]
    exact ⟨fun h => Sum.inl_injective h, fun h => by rw [h]⟩
  · have hf := s4_facts r
    unfold period
    rw [Nat.find_eq_iff]
    refine ⟨⟨by norm_num, by rw [W.σ'_iterate_inr, hf.1]⟩, fun m hm ⟨hm0, hmx⟩ => ?_⟩
    rw [W.σ'_iterate_inr] at hmx
    exact hf.2 m hm hm0 (by simpa using hmx)

theorem α'_ne (x : D ⊕ (Fin K × Fin 4)) : W.α' x ≠ x := by
  rw [α'_apply]
  rcases x with d | ⟨i, r⟩
  · by_cases h1 : ∃ i, W.t i = d
    · obtain ⟨i, rfl⟩ := h1; rw [W.αfun_t]; simp
    by_cases h2 : ∃ i, A.α (W.t i) = d
    · obtain ⟨i, rfl⟩ := h2; rw [W.αfun_αt]; simp
    push Not at h1 h2
    rw [W.αfun_inl h1 h2]
    intro h
    exact A.isArrangement.α_ne d (Sum.inl_injective h)
  · fin_cases r
    · simp only [Fin.zero_eta, Fin.isValue]; rw [W.αfun_u]; simp
    · simp only [Fin.mk_one, Fin.isValue]; rw [W.αfun_v]; simp
    · show W.αfun (.inr (i, 2)) ≠ .inr (i, 2)
      rw [W.αfun_p]; simp
    · show W.αfun (.inr (i, 3)) ≠ .inr (i, 3)
      rw [W.αfun_q]; simp

theorem curve'_α (x : D ⊕ (Fin K × Fin 4)) : W.curve' (W.α' x) = W.curve' x := by
  rw [α'_apply]
  rcases x with d | ⟨i, r⟩
  · by_cases h1 : ∃ i, W.t i = d
    · obtain ⟨i, rfl⟩ := h1; rw [W.αfun_t]; simp [curve']
    by_cases h2 : ∃ i, A.α (W.t i) = d
    · obtain ⟨i, rfl⟩ := h2; rw [W.αfun_αt]; simp [curve', A.isArrangement.curve_α]
    push Not at h1 h2
    rw [W.αfun_inl h1 h2]; simp [curve', A.isArrangement.curve_α]
  · fin_cases r
    · simp only [Fin.zero_eta, Fin.isValue]; rw [W.αfun_u]; simp [curve']
    · simp only [Fin.mk_one, Fin.isValue]; rw [W.αfun_v]; simp [curve', A.isArrangement.curve_α]
    · show W.curve' (W.αfun (.inr (i, 2))) = W.curve' (.inr (i, 2))
      rw [W.αfun_p]; simp [curve']
    · show W.curve' (W.αfun (.inr (i, 3))) = W.curve' (.inr (i, 3))
      rw [W.αfun_q]; simp [curve']

theorem curve'_σ (x : D ⊕ (Fin K × Fin 4)) :
    W.curve' (W.σ' x) ≠ W.curve' x := by
  rcases x with d | ⟨i, r⟩
  · rw [W.σ'_inl]; simp only [curve']
    intro h; exact A.isArrangement.curve_σ d (Fin.castSucc_injective _ h)
  · rw [W.σ'_inr]
    fin_cases r <;> simp [curve', s4, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem curve'_σσ (x : D ⊕ (Fin K × Fin 4)) :
    W.curve' (W.σ' (W.σ' x)) =
      W.curve' x := by
  rcases x with d | ⟨i, r⟩
  · rw [W.σ'_inl, W.σ'_inl]; simp only [curve', A.isArrangement.curve_σσ]
  · rw [W.σ'_inr, W.σ'_inr]
    fin_cases r <;> simp [curve', s4]

end InsWalk

end Pca.Great
