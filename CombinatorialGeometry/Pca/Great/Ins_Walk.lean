/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Inserting a new curve: straight walks (`doc/pca/great.md` 4.1)

Along an old curve the new walk is the old walk with `v i` inserted after `t i` and `u i` after
`α (t i)`; the new curve is the walk `p i ↦ p (i+1)` (and `q i ↦ q (i-1)` backwards).
-/
import Pca.Great.Ins_Cross

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

namespace InsWalk

variable {A : Arrangement n D} {K : ℕ} (W : InsWalk A K)

/-- The new straight permutation. -/
noncomputable abbrev st : Perm (D ⊕ (Fin K × Fin 4)) := straightPerm W.σ' W.α'

theorem st_apply (x : D ⊕ (Fin K × Fin 4)) : W.st x = W.σ' (W.σ' (W.α' x)) := rfl

/-- `d` is not one of the crossed darts. -/
def Free (d : D) : Prop := (∀ i, W.t i ≠ d) ∧ ∀ i, A.α (W.t i) ≠ d

theorem α'_free {d : D} (h : W.Free d) : W.α' (.inl d) = .inl (A.α d) := W.αfun_inl h.1 h.2

theorem st_free {d : D} (h : W.Free d) : W.st (.inl d) = .inl (A.straight d) := by
  rw [st_apply, W.α'_free h, W.σ'_inl, W.σ'_inl]; rfl

theorem st_t (i : Fin K) : W.st (.inl (W.t i)) = .inr (i, 1) := by
  rw [st_apply, α'_apply, W.αfun_t, W.σ'_inr, W.σ'_inr]; rfl

theorem st_v (i : Fin K) : W.st (.inr (i, 1)) = .inl (A.straight (W.t i)) := by
  rw [st_apply, α'_apply, W.αfun_v, W.σ'_inl, W.σ'_inl]; rfl

theorem st_αt (i : Fin K) : W.st (.inl (A.α (W.t i))) = .inr (i, 0) := by
  rw [st_apply, α'_apply, W.αfun_αt, W.σ'_inr, W.σ'_inr]; rfl

theorem st_u (i : Fin K) : W.st (.inr (i, 0)) = .inl (A.straight (A.α (W.t i))) := by
  rw [st_apply, α'_apply, W.αfun_u, W.σ'_inl, W.σ'_inl, A.straight_apply, A.isArrangement.α_α]

theorem st_p (i : Fin K) : W.st (.inr (i, 2)) = .inr (W.nx i, 2) := by
  rw [st_apply, α'_apply, W.αfun_p, W.σ'_inr, W.σ'_inr]; rfl

theorem st_q (i : Fin K) : W.st (.inr (i, 3)) = .inr (W.pv i, 3) := by
  rw [st_apply, α'_apply, W.αfun_q, W.σ'_inr, W.σ'_inr]; rfl

theorem σσ'_inl (d : D) : W.σ' (W.σ' (.inl d)) = .inl (A.σ (A.σ d)) := rfl
theorem σσ'_u (i : Fin K) : W.σ' (W.σ' (.inr (i, 0))) = .inr (i, 1) := rfl
theorem σσ'_v (i : Fin K) : W.σ' (W.σ' (.inr (i, 1))) = .inr (i, 0) := rfl
theorem σσ'_p (i : Fin K) : W.σ' (W.σ' (.inr (i, 2))) = .inr (i, 3) := rfl
theorem σσ'_q (i : Fin K) : W.σ' (W.σ' (.inr (i, 3))) = .inr (i, 2) := rfl

theorem sc_st (x : D ⊕ (Fin K × Fin 4)) : W.st.SameCycle x (W.st x) := ⟨1, by simp⟩

theorem sc_inl_straight (d : D) : W.st.SameCycle (.inl d) (.inl (A.straight d)) := by
  by_cases h1 : ∃ i, W.t i = d
  · obtain ⟨i, rfl⟩ := h1
    have h1 := W.sc_st (.inl (W.t i))
    have h2 := W.sc_st (.inr (i, 1))
    rw [W.st_t] at h1; rw [W.st_v] at h2
    exact h1.trans h2
  by_cases h2 : ∃ i, A.α (W.t i) = d
  · obtain ⟨i, rfl⟩ := h2
    have h1 := W.sc_st (.inl (A.α (W.t i)))
    have h2 := W.sc_st (.inr (i, 0))
    rw [W.st_αt] at h1; rw [W.st_u] at h2
    exact h1.trans h2
  push Not at h1 h2
  have := W.sc_st (.inl d)
  rwa [W.st_free ⟨h1, h2⟩] at this

theorem sc_lift {d e : D} (h : A.straight.SameCycle d e) : W.st.SameCycle (.inl d) (.inl e) := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  induction k with
  | zero => exact Perm.SameCycle.refl _ _
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply]
    exact (ih (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _))).trans
      (W.sc_inl_straight _)

/-- Every dart on an old curve is on the walk of an old dart, compatibly with `σ²`. -/
theorem exists_rep (x : D ⊕ (Fin K × Fin 4)) (hx : W.curve' x ≠ Fin.last n) :
    ∃ d, W.st.SameCycle x (.inl d) ∧ W.st.SameCycle (W.σ' (W.σ' x)) (.inl (A.σ (A.σ d))) ∧
      W.curve' x = Fin.castSucc (A.curve d) := by
  rcases x with d | ⟨i, r⟩
  · exact ⟨d, Perm.SameCycle.refl _ _, Perm.SameCycle.refl _ _, rfl⟩
  · fin_cases r
    · refine ⟨A.α (W.t i), ?_, ?_, ?_⟩
      · have := W.sc_st (.inl (A.α (W.t i))); rw [W.st_αt] at this; exact this.symm
      · show W.st.SameCycle (W.σ' (W.σ' (.inr (i, 0)))) _
        rw [W.σσ'_u]
        have := W.sc_st (.inr (i, 1)); rw [W.st_v, A.straight_apply] at this; exact this
      · simp [curve', A.isArrangement.curve_α]
    · refine ⟨W.t i, ?_, ?_, ?_⟩
      · have := W.sc_st (.inl (W.t i)); rw [W.st_t] at this; exact this.symm
      · show W.st.SameCycle (W.σ' (W.σ' (.inr (i, 1)))) _
        rw [W.σσ'_v]
        have := W.sc_st (.inr (i, 0))
        rw [W.st_u, A.straight_apply, A.isArrangement.α_α] at this; exact this
      · simp [curve']
    · exact absurd (by simp [curve']) hx
    · exact absurd (by simp [curve']) hx

theorem curve'_st (x : D ⊕ (Fin K × Fin 4)) : W.curve' (W.st x) = W.curve' x := by
  rw [st_apply, W.curve'_σσ, W.curve'_α]

theorem curve'_sc {x y : D ⊕ (Fin K × Fin 4)} (h : W.st.SameCycle x y) :
    W.curve' y = W.curve' x := by
  obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, W.curve'_st]
    exact ih (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _))

theorem fin_all {R : Fin K → Fin K → Prop} (hR : Equivalence R) (h : ∀ i, R i (W.nx i))
    (i j : Fin K) : R i j := by
  have h0 : ∀ m (hm : m < K), R ⟨0, by omega⟩ ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero => intro _; exact hR.refl _
    | succ m ih =>
      intro hm
      have heq : (⟨m + 1, hm⟩ : Fin K) = W.nx ⟨m, by omega⟩ := by
        apply Fin.ext; rw [W.nx_val]; simp only; rw [if_neg (by omega)]
      rw [heq]; exact hR.trans (ih (by omega)) (h _)
  exact hR.trans (hR.symm (h0 i.1 i.2)) (h0 j.1 j.2)

/-- The straight axiom for the new map. -/
theorem straight' (x y : D ⊕ (Fin K × Fin 4)) (h : W.curve' x = W.curve' y) :
    W.st.SameCycle x y ∨ W.st.SameCycle x (W.σ' (W.σ' y)) := by
  by_cases hx : W.curve' x = Fin.last n
  · have hy : W.curve' y = Fin.last n := h ▸ hx
    have hP : ∀ i j : Fin K, W.st.SameCycle (.inr (i, 2)) (.inr (j, 2)) := by
      refine W.fin_all (R := fun i j => W.st.SameCycle (.inr (i, 2)) (.inr (j, 2)))
        ⟨fun _ => Perm.SameCycle.refl _ _, fun h => h.symm, fun h h' => h.trans h'⟩ ?_
      intro i; have := W.sc_st (.inr (i, 2)); rwa [W.st_p] at this
    have hQ : ∀ i j : Fin K, W.st.SameCycle (.inr (i, 3)) (.inr (j, 3)) := by
      refine W.fin_all (R := fun i j => W.st.SameCycle (.inr (i, 3)) (.inr (j, 3)))
        ⟨fun _ => Perm.SameCycle.refl _ _, fun h => h.symm, fun h h' => h.trans h'⟩ ?_
      intro i; have := W.sc_st (.inr (W.nx i, 3)); rw [W.st_q, W.pv_nx] at this; exact this.symm
    have hnew : ∀ z, W.curve' z = Fin.last n → ∃ i, z = .inr (i, 2) ∨ z = .inr (i, 3) := by
      intro z hz
      rcases z with d | ⟨i, r⟩
      · exact absurd hz (Fin.castSucc_ne_last _)
      · refine ⟨i, ?_⟩
        fin_cases r
        · simp [curve'] at hz
        · simp [curve'] at hz
        · left; rfl
        · right; rfl
    obtain ⟨i, rfl | rfl⟩ := hnew x hx <;> obtain ⟨j, rfl | rfl⟩ := hnew y hy
    · exact Or.inl (hP i j)
    · right; rw [W.σσ'_q]; exact hP i j
    · right; rw [W.σσ'_p]; exact hQ i j
    · exact Or.inl (hQ i j)
  · obtain ⟨d, hd1, -, hd3⟩ := W.exists_rep x hx
    obtain ⟨e, he1, he2, he3⟩ := W.exists_rep y (h ▸ hx)
    have hde : A.curve d = A.curve e := Fin.castSucc_injective _ (hd3.symm.trans (h.trans he3))
    rcases A.isArrangement.straight d e hde with h1 | h1
    · exact Or.inl (hd1.trans ((W.sc_lift h1).trans he1.symm))
    · exact Or.inr (hd1.trans ((W.sc_lift h1).trans he2.symm))

end InsWalk

end Pca.Great
