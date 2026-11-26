/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Great arrangements from antipodal crossing sequences

`AntW A`: walking `n - 1` steps along a curve from a crossing reaches a crossing of the same two
curves. This implies `IsGreat` (`isGreat_of_antW`), by the counting argument of `side_ant`.
-/
import Pca.Great.Walk

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- Antipodal crossing sequences. -/
def AntW (A : Arrangement n D) : Prop :=
  ∀ d, Arrangement.Crossing.curves A (A.crossingOf (ant A d)) =
    Arrangement.Crossing.curves A (A.crossingOf d)

theorem antW_of_isGreat (hA : A.IsGreat) : AntW A := curves_ant hA

variable (hW : AntW A)
include hW

theorem ant_ne_W (d : D) : A.crossingOf (ant A d) ≠ A.crossingOf d := by
  have hn := A.two_le_n
  intro h
  have := straight_pow_inj_zero (d := d) (j := n - 1) (by omega) h
  omega

theorem eq_iff_W (d : D) {k : ℕ} (hk : k < 2 * (n - 1)) :
    Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ k) d)) =
        Arrangement.Crossing.curves A (A.crossingOf d) ↔ k = 0 ∨ k = n - 1 := by
  have hn := A.two_le_n
  constructor
  · intro h
    by_cases h0 : A.crossingOf ((A.straight ^ k) d) = A.crossingOf d
    · exact Or.inl (straight_pow_inj_zero hk h0)
    · exact Or.inr (straight_pow_inj hk (by omega)
        (eq_of_curves_eq h (hW d) h0 (ant_ne_W hW d)))
  · rintro (rfl | rfl)
    · rw [pow_zero]; rfl
    · exact hW d

theorem pos_two_W (d : D) {e : Fin n} (he : e ≠ A.curve d) :
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
      · have := (eq_iff_W hW ((A.straight ^ k₁) d) (k := j - k₁)
          (by omega)).1 (by rw [← straight_pow_add, Nat.sub_add_cancel hle]; exact heq)
        omega
      · have := (eq_iff_W hW ((A.straight ^ j) d) (k := k₁ - j)
          (by omega)).1 (by rw [← straight_pow_add, Nat.sub_add_cancel hlt.le]; exact heq.symm)
        omega
    · rintro (rfl | rfl)
      · exact hmem
      · rw [add_comm, straight_pow_add]
        have := hW ((A.straight ^ k₁) d)
        unfold ant at this
        rw [this]; exact hmem
  by_cases hk' : k < n - 1
  · exact ⟨k, hk', key k hk' (by rw [hkx, hx]; simp)⟩
  · refine ⟨k - (n - 1), by omega, key _ (by omega) ?_⟩
    have h := hW ((A.straight ^ (k - (n - 1))) d)
    unfold ant at h
    rw [← straight_pow_add, Nat.add_sub_cancel' (by omega)] at h
    rw [← h, hkx, hx]; simp

theorem isGreat_of_antW : A.IsGreat := by
  have hn := A.two_le_n
  intro a b c hab hac hbc s hs x y hxy hx hy d hd e he
  have hdx : A.crossingOf d = x := Orbit.mem_darts.1 hd
  have hey : A.crossingOf e = y := Orbit.mem_darts.1 he
  subst hdx hey
  have hcx : c ∉ Arrangement.Crossing.curves A (A.crossingOf d) := by
    rw [hx]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hac, Ne.symm hbc⟩
  have hcd : c ≠ A.curve d := fun h => hcx (h ▸ A.mem_curves_crossingOf d)
  have hz : A.crossingOf e = A.crossingOf (ant A d) :=
    eq_of_curves_eq (hy.trans hx.symm) (hW d) hxy.symm (ant_ne_W hW d)
  have hcy : c ∉ Arrangement.Crossing.curves A (A.crossingOf e) := by
    rw [hy]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hac, Ne.symm hbc⟩
  rw [← crossSide_eq hs hcy, hz, crossSide_eq hs (by rwa [← hz]), ant,
    side_straight_pow hs (Ne.symm hcd)]
  obtain ⟨k₁, hk₁, hpos⟩ := pos_two_W hW d hcd
  have hk0 : k₁ ≠ 0 := by
    rintro rfl
    exact hcx (by simpa using (hpos 0 (by omega)).2 (Or.inl rfl))
  have hset : (Ioc 0 (n - 1)).filter (fun j =>
      c ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d))) = {k₁} := by
    ext j
    simp only [mem_filter, mem_Ioc, mem_singleton]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      rcases (hpos j (by omega)).1 h2 with h | h <;> omega
    · rintro rfl
      exact ⟨⟨by omega, by omega⟩, (hpos _ (by omega)).2 (Or.inl rfl)⟩
  rw [hset, card_singleton, Nat.cast_one]
  have : ∀ a : ZMod 2, a ≠ a + 1 := by decide
  exact this _

end Pca.Great
