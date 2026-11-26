/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Inserting a new curve along an antipodally symmetric walk keeps the arrangement great

If `t (i + n) = α (ant (t i))` (indices shifted by `n` steps of the walk), the crossing sequences
of the new arrangement are antipodal (`AntW`), so it is great.
-/
import Pca.Great.Ins_Arr
import Pca.Great.AntW
import Pca.Flip

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

theorem not_sc_α (A : Arrangement n D) (d : D) : ¬ A.straight.SameCycle d (A.α d) := by
  intro h
  have h2 : A.straight.SameCycle (A.α d) (A.σ (A.σ d)) := ⟨1, by simp [A.straight_α]⟩
  exact A.not_sameCycle_straight_σσ d (h.trans h2)

theorem straight_pow_mod (A : Arrangement n D) (d : D) (k : ℕ) :
    (A.straight ^ k) d = (A.straight ^ (k % (2 * (n - 1)))) d := by
  conv_lhs => rw [← Nat.mod_add_div k (2 * (n - 1))]
  rw [pow_add, Perm.mul_apply, pow_mul]
  congr 1
  generalize k / (2 * (n - 1)) = q
  induction q with
  | zero => rfl
  | succ q ih => rw [pow_succ, Perm.mul_apply, straight_pow_period, ih]

namespace InsWalk

variable {A : Arrangement n D} {K : ℕ} (W : InsWalk A K)

/-- The shift by `n` steps of the walk. -/
def sh (i : Fin K) : Fin K := (W.nx)^[n] i

/-- Antipodal symmetry of the walk. -/
def Sym : Prop := ∀ i, W.t (W.sh i) = A.α (ant A (W.t i))

/-- The number of crossed darts among the first `k` darts of the walk of `d`. -/
noncomputable def hits (d : D) (k : ℕ) : ℕ :=
  by classical exact ((range k).filter (fun j => W.Hit ((A.straight ^ j) d))).card

open Classical in
theorem hits_succ (d : D) (k : ℕ) :
    W.hits d (k + 1) = W.hits d k + if W.Hit ((A.straight ^ k) d) then 1 else 0 := by
  classical
  simp only [hits, range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem st_hit_free {d : D} (h : ¬ W.Hit d) : W.st (.inl d) = .inl (A.straight d) :=
  W.st_free ⟨fun i hi => h (Or.inl ⟨i, hi⟩), fun i hi => h (Or.inr ⟨i, hi⟩)⟩

theorem st_hit_two {d : D} (h : W.Hit d) : W.st (W.st (.inl d)) = .inl (A.straight d) := by
  rcases h with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [W.st_t, W.st_v]
  · rw [W.st_αt, W.st_u]

open Classical in
theorem st_walk (d : D) (k : ℕ) :
    (W.st ^ (k + W.hits d k)) (.inl d) = .inl ((A.straight ^ k) d) := by
  induction k with
  | zero => simp [hits]
  | succ k ih =>
    rw [W.hits_succ]
    split_ifs with h
    · rw [show k + 1 + (W.hits d k + 1) = 2 + (k + W.hits d k) by omega, pow_add,
        Perm.mul_apply, ih, pow_two, Perm.mul_apply, W.st_hit_two h, pow_succ', Perm.mul_apply]
    · rw [show k + 1 + (W.hits d k + 0) = 1 + (k + W.hits d k) by omega, pow_add,
        Perm.mul_apply, ih, pow_one, W.st_hit_free h, pow_succ', Perm.mul_apply]

variable (hA : A.IsGreat) (hS : W.Sym)
include hA hS

omit hA in
theorem hit_ant {w : D} (h : W.Hit w) : W.Hit (ant A w) := by
  rcases h with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · right; refine ⟨W.sh i, ?_⟩; rw [hS, A.isArrangement.α_α]
  · left; refine ⟨W.sh i, ?_⟩; rw [hS, ant_α]

/-- Exactly one crossed dart among the first `n - 1` darts of every walk. -/
theorem hits_half (d : D) : W.hits d (n - 1) = 1 := by
  classical
  have hn := A.two_le_n
  haveI : Nonempty (Fin K) := ⟨⟨0, by have := W.three_le; omega⟩⟩
  set J := (range (2 * (n - 1))).filter (fun j => W.Hit ((A.straight ^ j) d)) with hJ
  -- at most two hits
  have hJ2 : J.card ≤ 2 := by
    have hT : (univ.filter (fun i => A.curve (W.t i) = A.curve d)).card = 2 := W.twice _
    rw [← hT]
    have hc : ∀ j ∈ J, ∃ i, A.curve (W.t i) = A.curve d ∧
        ((A.straight ^ j) d = W.t i ∨ (A.straight ^ j) d = A.α (W.t i)) := by
      intro j hj
      rcases (mem_filter.1 hj).2 with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact ⟨i, by rw [hi, curve_straight_pow], Or.inl hi.symm⟩
      · refine ⟨i, ?_, Or.inr hi.symm⟩
        rw [← A.isArrangement.curve_α, hi, curve_straight_pow]
    choose! g hg using hc
    refine card_le_card_of_injOn g (fun j hj => by simp [(hg j hj).1]) ?_
    intro j hj j' hj' hjj
    have hjr := mem_range.1 (mem_filter.1 hj).1
    have hjr' := mem_range.1 (mem_filter.1 hj').1
    have hsc : ∀ a b : ℕ, A.straight.SameCycle ((A.straight ^ a) d) ((A.straight ^ b) d) :=
      fun a b => Perm.sameCycle_pow_left.2 (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _))
    have heq : (A.straight ^ j) d = (A.straight ^ j') d := by
      rcases (hg j hj).2 with h1 | h1 <;> rcases (hg j' hj').2 with h2 | h2 <;>
        simp only [hjj] at h1
      · rw [h1, h2]
      · have := hsc j j'; rw [h1, h2] at this; exact absurd this (not_sc_α A _)
      · have := hsc j' j; rw [h1, h2] at this; exact absurd this (not_sc_α A _)
      · rw [h1, h2]
    exact straight_pow_inj hjr hjr' (by rw [heq])
  -- at least one hit
  have hJ1 : ∃ j < 2 * (n - 1), W.Hit ((A.straight ^ j) d) := by
    obtain ⟨i, hi⟩ : ∃ i, A.curve (W.t i) = A.curve d := by
      have hT : (univ.filter (fun i => A.curve (W.t i) = A.curve d)).card = 2 := W.twice _
      obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < (univ.filter
        (fun i => A.curve (W.t i) = A.curve d)).card)
      exact ⟨i, (mem_filter.1 hi).2⟩
    rcases A.isArrangement.straight d (W.t i) hi.symm with h | h
    · obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
      refine ⟨k % (2 * (n - 1)), Nat.mod_lt _ (by omega), Or.inl ⟨i, ?_⟩⟩
      rw [← straight_pow_mod]; exact hk.symm
    · obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
      refine ⟨(k + (2 * (n - 1) - 1)) % (2 * (n - 1)), Nat.mod_lt _ (by omega), Or.inr ⟨i, ?_⟩⟩
      rw [← straight_pow_mod]
      apply A.straight.injective
      have e : A.straight ((A.straight ^ (k + (2 * (n - 1) - 1))) d) =
          (A.straight ^ (2 * (n - 1))) ((A.straight ^ k) d) := by
        rw [← Perm.mul_apply, ← pow_succ', ← Perm.mul_apply, ← pow_add]; congr 2; omega
      rw [e, straight_pow_period, A.straight_α]; exact hk.symm
  -- the hits come in antipodal pairs
  obtain ⟨j, hj, hjH⟩ := hJ1
  have hpair : ∀ j < n - 1, W.Hit ((A.straight ^ j) d) →
      W.Hit ((A.straight ^ (j + (n - 1))) d) := by
    intro j _ h
    have := W.hit_ant hS h
    rwa [ant, ← Perm.mul_apply, ← pow_add, add_comm] at this
  have hpair' : ∀ j, n - 1 ≤ j → j < 2 * (n - 1) → W.Hit ((A.straight ^ j) d) →
      W.Hit ((A.straight ^ (j - (n - 1))) d) := by
    intro j h1 _ h
    have := W.hit_ant hS h
    rw [ant, ← Perm.mul_apply, ← pow_add, straight_pow_mod] at this
    rwa [show (n - 1 + j) % (2 * (n - 1)) = j - (n - 1) by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega] at this
  obtain ⟨p, hpm, hP1⟩ : ∃ p < n - 1, W.Hit ((A.straight ^ p) d) := by
    by_cases hjm : j < n - 1
    · exact ⟨j, hjm, hjH⟩
    · exact ⟨j - (n - 1), by omega, hpair' j (by omega) hj hjH⟩
  have hP2 := hpair p hpm hP1
  have hJeq : J = {p, p + (n - 1)} := by
    have hsub : ({p, p + (n - 1)} : Finset ℕ) ⊆ J := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem_filter.2 ⟨mem_range.2 (by omega), hP1⟩
      · exact mem_filter.2 ⟨mem_range.2 (by omega), hP2⟩
    exact (eq_of_subset_of_card_le hsub (by rw [card_pair (by omega)]; exact hJ2)).symm
  have : (range (n - 1)).filter (fun j => W.Hit ((A.straight ^ j) d)) = {p} := by
    ext x
    simp only [mem_filter, mem_range, mem_singleton]
    constructor
    · rintro ⟨hx, hxH⟩
      have : x ∈ J := mem_filter.2 ⟨mem_range.2 (by omega), hxH⟩
      rw [hJeq] at this
      simp only [mem_insert, mem_singleton] at this
      omega
    · rintro rfl; exact ⟨hpm, hP1⟩
  simp only [hits]
  convert card_singleton p

end InsWalk

end Pca.Great
