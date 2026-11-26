/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Doubling a curve: distinct cells

The cells left of `c` along `m + 1` consecutive segments are distinct (a curve crossing `c` in
between separates them), and so are the cells right of `c`; cells on different sides of `c` differ.
-/
import Pca.Great.Dbl_Sym

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

namespace Dbl

variable {A : Arrangement n D} (hA : A.IsGreat) (y0 : D)
include hA

theorem curve_y (k : ℕ) : A.curve (y A y0 k) = A.curve y0 := curve_straight_pow k y0

/-- Two left cells `m` or fewer segments apart differ in the side of a curve crossed between. -/
theorem sep_side (j l : ℕ) (hl0 : 0 < l) (hlm : l ≤ n - 1) :
    ∃ e, ∃ s : A.Cell → ZMod 2, A.IsSide e s ∧ e ≠ A.curve y0 ∧
      s (A.cellOf (y A y0 (j + l))) ≠ s (A.cellOf (y A y0 j)) := by
  have hn := A.two_le_n
  set e := A.curve (A.σ (y A y0 (j + l)))
  have he : e ≠ A.curve (y A y0 j) := by
    rw [curve_y hA, ← curve_y hA y0 (j + l)]; exact A.isArrangement.curve_σ _
  obtain ⟨s, hs⟩ := Arrangement.exists_isSide (A := A) e
  obtain ⟨k₁, hk₁, hpos⟩ := pos_two hA (y A y0 j) he
  have hwalk : ∀ i, (A.straight ^ i) (y A y0 j) = y A y0 (j + i) := fun i => by
    simp only [y, ← Perm.mul_apply, ← pow_add, add_comm]
  have hl : l = k₁ ∨ l = k₁ + (n - 1) := by
    refine (hpos l (by omega)).1 ?_
    rw [hwalk]; exact A.mem_curves_crossingOf_σ _
  have h := side_walk hA (y A y0 j) he hs hpos hk₁ (j := l) (by omega)
  rw [hwalk] at h
  refine ⟨e, s, hs, by rwa [curve_y hA] at he, ?_⟩
  rw [h]
  rcases hl with rfl | rfl
  · rw [if_pos ⟨hl0, le_rfl⟩, if_neg (by omega)]
    have : ∀ a : ZMod 2, a + (1 + 0) ≠ a := by decide
    exact this _
  · rw [if_neg (by omega), if_pos le_rfl]
    have : ∀ a : ZMod 2, a + (0 + 1) ≠ a := by decide
    exact this _

theorem sep_L (j l : ℕ) (hl0 : 0 < l) (hlm : l ≤ n - 1) :
    A.cellOf (y A y0 (j + l)) ≠ A.cellOf (y A y0 j) := by
  obtain ⟨e, s, -, -, h⟩ := sep_side hA y0 j l hl0 hlm
  exact fun h' => h (by rw [h'])

theorem sep_R (j l : ℕ) (hl0 : 0 < l) (hlm : l ≤ n - 1) :
    A.cellOf (A.α (y A y0 (j + l))) ≠ A.cellOf (A.α (y A y0 j)) := by
  obtain ⟨e, s, hs, he, h⟩ := sep_side hA y0 j l hl0 hlm
  have hα : ∀ k, s (A.cellOf (A.α (y A y0 k))) = s (A.cellOf (y A y0 k)) := fun k => by
    have := Arrangement.zmod2_eq_add_of_add_eq (hs (y A y0 k))
    rw [this, if_neg (by rw [curve_y hA]; exact he.symm), add_zero]
  intro h'
  apply h
  rw [← hα, ← hα, h']

theorem sep_LR (j k : ℕ) : A.cellOf (y A y0 j) ≠ A.cellOf (A.α (y A y0 k)) := by
  obtain ⟨s, hs⟩ := Arrangement.exists_isSide (A := A) (A.curve y0)
  have h1 := Arrangement.zmod2_eq_add_of_add_eq (hs (y A y0 k))
  rw [if_pos (curve_y hA y0 k)] at h1
  have h2 := side_straight_pow_self hs (d := y0) rfl j
  have h3 := side_straight_pow_self hs (d := y0) rfl k
  intro h
  have : s (A.cellOf (y A y0 j)) = s (A.cellOf (A.α (y A y0 k))) := by rw [h]
  rw [h1, h2, h3] at this
  have : ∀ a : ZMod 2, a ≠ a + 1 := by decide
  exact this _ (by assumption)

variable (hn : 2 ≤ n)
include hn

theorem cell_inj : Function.Injective (fun i => A.cellOf (t A y0 i)) := by
  -- left/right representation
  have rep : ∀ i : Fin (2 * n),
      (1 ≤ i.val ∧ i.val ≤ n ∧ A.cellOf (t A y0 i) =
          A.cellOf (A.α (y A y0 (if i.val = n then n - 1 else 2 * (n - 1) + 1 - i.val)))) ∨
      (¬ (1 ≤ i.val ∧ i.val ≤ n) ∧ A.cellOf (t A y0 i) =
          A.cellOf (y A y0 (if i.val = 0 then 0 else 2 * n - i.val))) := by
    intro i
    have hi := i.isLt
    by_cases h0 : i.val = 0
    · right; refine ⟨by omega, ?_⟩; rw [t_0 A y0 h0, if_pos h0]
    by_cases h1 : i.val ≤ n - 1
    · left; refine ⟨by omega, by omega, ?_⟩
      rw [t_R A y0 h0 h1, if_neg (by omega), A.cellOf_σ]
    by_cases h2 : i.val = n
    · left; refine ⟨by omega, by omega, ?_⟩; rw [t_n A y0 h0 h1 h2, if_pos h2]
    · right; refine ⟨by omega, ?_⟩; rw [t_L A y0 h0 h1 h2, if_neg h0, cellOf_ασσσ]
  intro i i' h
  simp only at h
  apply Fin.ext
  have hi := i.isLt
  have hi' := i'.isLt
  by_contra hne
  rcases rep i with ⟨a1, a2, ha⟩ | ⟨a1, ha⟩ <;> rcases rep i' with ⟨b1, b2, hb⟩ | ⟨b1, hb⟩
  · rw [ha, hb] at h
    generalize hk : (if i.val = n then n - 1 else 2 * (n - 1) + 1 - i.val) = k at h
    generalize hk' : (if i'.val = n then n - 1 else 2 * (n - 1) + 1 - i'.val) = k' at h
    have hkk : k ≠ k' ∧ n - 1 ≤ k ∧ k ≤ 2 * (n - 1) ∧ n - 1 ≤ k' ∧ k' ≤ 2 * (n - 1) := by
      split_ifs at hk hk' <;> omega
    rcases lt_or_gt_of_ne hkk.1 with hlt | hlt
    · have := sep_R hA y0 k (k' - k) (by omega) (by omega)
      rw [Nat.add_sub_cancel' hlt.le] at this; exact this h.symm
    · have := sep_R hA y0 k' (k - k') (by omega) (by omega)
      rw [Nat.add_sub_cancel' hlt.le] at this; exact this h
  · rw [ha, hb] at h; exact sep_LR hA y0 _ _ h.symm
  · rw [ha, hb] at h; exact sep_LR hA y0 _ _ h
  · rw [ha, hb] at h
    generalize hk : (if i.val = 0 then 0 else 2 * n - i.val) = k at h
    generalize hk' : (if i'.val = 0 then 0 else 2 * n - i'.val) = k' at h
    have hkk : k ≠ k' ∧ k ≤ n - 1 ∧ k' ≤ n - 1 := by
      split_ifs at hk hk' <;> omega
    rcases lt_or_gt_of_ne hkk.1 with hlt | hlt
    · have := sep_L hA y0 k (k' - k) (by omega) (by omega)
      rw [Nat.add_sub_cancel' hlt.le] at this; exact this h.symm
    · have := sep_L hA y0 k' (k - k') (by omega) (by omega)
      rw [Nat.add_sub_cancel' hlt.le] at this; exact this h

end Dbl

end Pca.Great
