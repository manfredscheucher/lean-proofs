/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Positions along a walk in a great arrangement (`doc/pca/great.md` section 3.2)

Along the walk `straight^k d` (`k < 2 (n - 1)`) every other curve `e` is met exactly twice, at
antipodal positions `k₁ < n - 1` and `k₁ + (n - 1)`; so the side of `e` along the walk changes
exactly there.
-/
import Pca.Great.Basic

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

theorem straight_pow_add (A : Arrangement n D) (i j : ℕ) (d : D) :
    (A.straight ^ (i + j)) d = (A.straight ^ i) ((A.straight ^ j) d) := by
  rw [pow_add, Perm.mul_apply]

variable (hA : A.IsGreat)
include hA

/-- The two positions of a curve `e` along the walk of `d`. -/
theorem pos_two (d : D) {e : Fin n} (he : e ≠ A.curve d) :
    ∃ k₁ < n - 1, ∀ j < 2 * (n - 1),
      e ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d)) ↔
        j = k₁ ∨ j = k₁ + (n - 1) := by
  have hn := A.two_le_n
  -- a crossing of `curve d` and `e`
  obtain ⟨x, hx⟩ : ∃ x : A.Crossing, Arrangement.Crossing.curves A x = {A.curve d, e} := by
    have h2 := A.card_curves_eq_pair (A.curve d) e he.symm
    obtain ⟨x, hx⟩ := card_pos.1 (by rw [h2]; omega)
    exact ⟨x, (mem_filter.1 hx).2⟩
  obtain ⟨k, hk, hkx⟩ := exists_straight_pow_eq (d := d) (x := x) (by rw [hx]; simp)
  -- reduce to `k₁ < n - 1`
  have key : ∀ k₁, k₁ < n - 1 → e ∈ Arrangement.Crossing.curves A
      (A.crossingOf ((A.straight ^ k₁) d)) → ∀ j < 2 * (n - 1),
      (e ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d)) ↔
        j = k₁ ∨ j = k₁ + (n - 1)) := by
    intro k₁ hk₁ hmem j hj
    have hc : ∀ i, A.curve d ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ i) d)) :=
      fun i => by rw [← curve_straight_pow i d]; exact A.mem_curves_crossingOf _
    have hpair : ∀ i, e ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ i) d)) →
        Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ i) d)) = {A.curve d, e} :=
      fun i hi => A.curves_eq_pair (hc i) hi he.symm
    constructor
    · intro hj'
      have heq : Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d)) =
          Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ k₁) d)) := by
        rw [hpair j hj', hpair k₁ hmem]
      rcases le_or_gt k₁ j with hle | hlt
      · have := (crossingOf_straight_pow_eq_iff hA ((A.straight ^ k₁) d) (k := j - k₁)
          (by omega)).1 (by rw [← straight_pow_add, Nat.sub_add_cancel hle]; exact heq)
        omega
      · have := (crossingOf_straight_pow_eq_iff hA ((A.straight ^ j) d) (k := k₁ - j)
          (by omega)).1 (by rw [← straight_pow_add, Nat.sub_add_cancel hlt.le]; exact heq.symm)
        omega
    · rintro (rfl | rfl)
      · exact hmem
      · rw [add_comm, straight_pow_add]
        have := curves_ant hA ((A.straight ^ k₁) d)
        unfold ant at this
        rw [this]; exact hmem
  by_cases hk' : k < n - 1
  · exact ⟨k, hk', key k hk' (by rw [hkx, hx]; simp)⟩
  · refine ⟨k - (n - 1), by omega, key _ (by omega) ?_⟩
    have h := curves_ant hA ((A.straight ^ (k - (n - 1))) d)
    unfold ant at h
    rw [← straight_pow_add, Nat.add_sub_cancel' (by omega)] at h
    rw [← h, hkx, hx]; simp

/-- The side of `e` along the walk of `d` changes exactly at the two positions of `e`. -/
theorem side_walk (d : D) {e : Fin n} (he : e ≠ A.curve d) {s : A.Cell → ZMod 2}
    (hs : A.IsSide e s) {k₁ : ℕ}
    (hk₁ : ∀ j < 2 * (n - 1),
      e ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d)) ↔
        j = k₁ ∨ j = k₁ + (n - 1)) (hk : k₁ < n - 1) {j : ℕ} (hj : j < 2 * (n - 1)) :
    s (A.cellOf ((A.straight ^ j) d)) = s (A.cellOf d) +
      ((if 0 < k₁ ∧ k₁ ≤ j then 1 else 0) + if k₁ + (n - 1) ≤ j then 1 else 0) := by
  have hn := A.two_le_n
  rw [side_straight_pow hs (Ne.symm he) j]
  congr 1
  have hset : (Ioc 0 j).filter (fun i =>
      e ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ i) d))) =
      (Ioc 0 j).filter (fun i => i = k₁ ∨ i = k₁ + (n - 1)) := by
    apply filter_congr
    intro i hi
    exact hk₁ i (by simp at hi; omega)
  rw [hset]
  by_cases h1 : 0 < k₁ ∧ k₁ ≤ j <;> by_cases h2 : k₁ + (n - 1) ≤ j
  · have : (Ioc 0 j).filter (fun i => i = k₁ ∨ i = k₁ + (n - 1)) = {k₁, k₁ + (n - 1)} := by
      ext i; simp only [mem_filter, mem_Ioc, mem_insert, mem_singleton]; omega
    rw [this, card_pair (by omega), if_pos h1, if_pos h2]; norm_num
  · have : (Ioc 0 j).filter (fun i => i = k₁ ∨ i = k₁ + (n - 1)) = {k₁} := by
      ext i; simp only [mem_filter, mem_Ioc, mem_singleton]; omega
    rw [this, card_singleton, if_pos h1, if_neg h2]; norm_num
  · have : (Ioc 0 j).filter (fun i => i = k₁ ∨ i = k₁ + (n - 1)) = {k₁ + (n - 1)} := by
      ext i; simp only [mem_filter, mem_Ioc, mem_singleton]; omega
    rw [this, card_singleton, if_neg h1, if_pos h2]; norm_num
  · have : (Ioc 0 j).filter (fun i => i = k₁ ∨ i = k₁ + (n - 1)) = ∅ := by
      ext i; simp only [mem_filter, mem_Ioc, notMem_empty, iff_false]; omega
    rw [this, card_empty, if_neg h1, if_neg h2]; norm_num

end Pca.Great
