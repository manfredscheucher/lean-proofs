/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Inserting a new curve: crossings (`doc/pca/great.md` 4.1)

The crossings of the new map are the old crossings (`inl`) and one new crossing per index `i`
(`inr (i, _)`); every pair of curves still crosses exactly twice.
-/
import Pca.Great.Ins_Ax1

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

namespace InsWalk

variable {A : Arrangement n D} {K : ℕ} (W : InsWalk A K)

theorem period_inl (d : D) : period W.σ' (.inl d) = period A.σ d := by
  rw [← card_orbitFinset, W.card_crossing' (.inl d), ← card_orbitFinset]
  exact (A.isArrangement.card_crossing d).symm

theorem orbitList_inl (d : D) :
    orbitList W.σ' (.inl d) = (orbitList A.σ d).map Sum.inl := by
  simp only [orbitList, W.period_inl, List.map_map]
  congr 1; funext k; simp [W.σ'_iterate_inl]

theorem sc_inl {a b : D} : W.σ'.SameCycle (.inl a) (.inl b) ↔ A.σ.SameCycle a b := by
  rw [← mem_orbitList, W.orbitList_inl, ← mem_orbitList]
  simp

theorem not_sc_inl_inr (a : D) (y : Fin K × Fin 4) : ¬ W.σ'.SameCycle (.inl a) (.inr y) := by
  rw [← mem_orbitList, W.orbitList_inl]; simp

theorem sc_inr {i j : Fin K} {r r' : Fin 4} :
    W.σ'.SameCycle (.inr (i, r)) (.inr (j, r')) ↔ i = j := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [Perm.coe_pow, W.σ'_iterate_inr] at hk
    simp only [Sum.inr.injEq, Prod.mk.injEq] at hk
    exact hk.1
  · rintro rfl
    have hall : ∀ r r' : Fin 4, ∃ k : Fin 4, (s4^[k.val]) r = r' := by decide
    obtain ⟨k, hk4⟩ := hall r r'
    refine ⟨(k.val : ℤ), ?_⟩
    rw [zpow_natCast, Perm.coe_pow, W.σ'_iterate_inr, hk4]

theorem crossCurves_inl (d : D) :
    crossingCurves W.σ' W.curve' (Orbit.mk W.σ' (.inl d)) =
      (crossingCurves A.σ A.curve (Orbit.mk A.σ d)).map Fin.castSuccEmb := by
  simp only [crossingCurves, Orbit.darts_mk, orbitFinset, W.orbitList_inl]
  ext c
  simp only [mem_image, List.mem_toFinset, List.mem_map, mem_map, Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨_, ⟨d', hd', rfl⟩, rfl⟩; exact ⟨_, ⟨d', hd', rfl⟩, rfl⟩
  · rintro ⟨_, ⟨d', hd', rfl⟩, rfl⟩; exact ⟨_, ⟨d', hd', rfl⟩, rfl⟩

theorem crossCurves_inr (i : Fin K) (r : Fin 4) :
    crossingCurves W.σ' W.curve' (Orbit.mk W.σ' (.inr (i, r))) =
      {Fin.castSucc (A.curve (W.t i)), Fin.last n} := by
  ext c
  simp only [crossingCurves, Orbit.darts_mk, mem_image, mem_orbitFinset, mem_insert,
    mem_singleton]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases x with d | ⟨j, r'⟩
    · exact absurd hx.symm (W.not_sc_inl_inr d _)
    · rw [W.sc_inr] at hx; subst hx
      simp only [curve']; split_ifs <;> simp
  · rintro (rfl | rfl)
    · exact ⟨.inr (i, 0), W.sc_inr.2 rfl, by simp [curve']⟩
    · exact ⟨.inr (i, 2), W.sc_inr.2 rfl, by simp [curve']⟩

/-- The old crossings embed. -/
def oldX : Orbit A.σ → Orbit W.σ' :=
  Quotient.map (Sum.inl) (fun _ _ h => (W.sc_inl).2 h)

theorem oldX_mk (d : D) : W.oldX (Orbit.mk A.σ d) = Orbit.mk W.σ' (.inl d) := rfl

theorem oldX_inj : Function.Injective W.oldX := by
  intro x y h
  obtain ⟨a, rfl⟩ := x.exists_mk
  obtain ⟨b, rfl⟩ := y.exists_mk
  rw [oldX_mk, oldX_mk, Orbit.mk_eq_mk, W.sc_inl] at h
  exact Orbit.mk_eq_mk.2 h

theorem intersecting' (c c' : Fin (n + 1)) (h : c ≠ c') :
    (univ.filter (fun x : Orbit W.σ' => crossingCurves W.σ' W.curve' x = {c, c'})).card = 2 := by
  -- the pair with the new curve
  have hnew : ∀ e : Fin n,
      (univ.filter (fun x : Orbit W.σ' =>
        crossingCurves W.σ' W.curve' x = {Fin.castSucc e, Fin.last n})).card = 2 := by
    intro e
    rw [← W.twice e]
    symm
    refine card_bij (fun i _ => Orbit.mk W.σ' (.inr (i, 0))) ?_ ?_ ?_
    · intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      rw [W.crossCurves_inr, hi]
    · intro i _ j _ hij
      exact W.sc_inr.1 (Orbit.mk_eq_mk.1 hij)
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      obtain ⟨y, rfl⟩ := x.exists_mk
      rcases y with d | ⟨i, r⟩
      · rw [W.crossCurves_inl] at hx
        have : Fin.last n ∈ (crossingCurves A.σ A.curve (Orbit.mk A.σ d)).map Fin.castSuccEmb := by
          rw [hx]; simp
        simp only [mem_map, Fin.castSuccEmb_apply] at this
        obtain ⟨a, -, ha⟩ := this
        exact absurd ha (Fin.castSucc_ne_last a)
      · refine ⟨i, ?_, Orbit.mk_eq_mk.2 (W.sc_inr.2 rfl)⟩
        rw [W.crossCurves_inr] at hx
        simp only [mem_filter, mem_univ, true_and]
        have : Fin.castSucc (A.curve (W.t i)) ∈ ({Fin.castSucc e, Fin.last n} : Finset _) := by
          rw [← hx]; simp
        simp only [mem_insert, mem_singleton, Fin.castSucc_inj] at this
        rcases this with h1 | h1
        · exact h1
        · exact absurd h1 (Fin.castSucc_ne_last _)
  -- the old pairs
  have hold : ∀ a b : Fin n, a ≠ b →
      (univ.filter (fun x : Orbit W.σ' =>
        crossingCurves W.σ' W.curve' x = {Fin.castSucc a, Fin.castSucc b})).card = 2 := by
    intro a b hab
    rw [← A.isArrangement.intersecting a b hab]
    symm
    refine card_bij (fun x _ => W.oldX x) ?_ (fun x _ y _ h => W.oldX_inj h) ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      obtain ⟨d, rfl⟩ := x.exists_mk
      rw [oldX_mk, W.crossCurves_inl, hx]
      simp [Finset.map_insert]
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      obtain ⟨y, rfl⟩ := x.exists_mk
      rcases y with d | ⟨i, r⟩
      · refine ⟨Orbit.mk A.σ d, ?_, rfl⟩
        simp only [mem_filter, mem_univ, true_and]
        rw [W.crossCurves_inl] at hx
        apply Finset.map_injective Fin.castSuccEmb
        rw [hx]; simp [Finset.map_insert]
      · rw [W.crossCurves_inr] at hx
        have : Fin.last n ∈ ({Fin.castSucc a, Fin.castSucc b} : Finset _) := by
          rw [← hx]; simp
        simp only [mem_insert, mem_singleton] at this
        rcases this with h1 | h1 <;> exact absurd h1.symm (Fin.castSucc_ne_last _)
  induction c using Fin.lastCases with
  | last =>
    induction c' using Fin.lastCases with
    | last => exact absurd rfl h
    | cast b =>
      have := hnew b
      rwa [pair_comm] at this
  | cast a =>
    induction c' using Fin.lastCases with
    | last => exact hnew a
    | cast b => exact hold a b (fun h' => h (by rw [h']))

end InsWalk

end Pca.Great
