/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Milestone 6: the main theorem (`thm:main`, `cor:main` of the notes)

For every simple intersecting arrangement of `n ≥ 4` pseudocircles, using the digon theorem
(`digon_bound`, an axiom):

* `Arrangement.main_theorem`: `3 p_3 ≤ 4 binom(n,2) + 2n - 2 - 3 p_2` (in `ℤ`),
* `Arrangement.main_theorem_rat`: `p_3 ≤ 4/3 binom(n,2) + (2n-2)/3 - p_2` (in `ℚ`),
* `Arrangement.excess_le`: `e ≤ 2n - 2 - 3 p_2`,
* `Arrangement.main_digon_free`: `p_2 = 0` implies `p_3 ≤ 4/3 binom(n,2) + (2n-2)/3`,
* `Arrangement.cor_main`, `Arrangement.cor_main_floor`: `p_3 ≤ ⌊2(n²-1)/3⌋`
  `= ⌊4/3 binom(n,2) + (2n-2)/3⌋`.
-/
import Pca.Potential
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.LinearCombination

open Finset

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd

/-- The ingredients of Step 5 in `ℕ`: `3 p_3 + 3 p_2 ≤ 2 n(n-1) + 2n - 2`. -/
theorem main_nat (hn : 4 ≤ n) : 3 * A.p 3 + 3 * A.p 2 ≤ 2 * (n * (n - 1)) + (2 * n - 2) := by
  have he := A.excess_eq_X'_sub_deficiency_of_four_le hn
  have hd := A.two_p2_le_deficiency hn
  have hp := potential_lemma hn A
  have hX := A.card_X
  rw [excess, hX] at he
  generalize n * (n - 1) = N at *
  omega

/-- **Main theorem** (`thm:main`, integer form): `3 p_3 ≤ 4 binom(n,2) + 2n - 2 - 3 p_2`. -/
theorem main_theorem (hn : 4 ≤ n) :
    3 * (A.p 3 : ℤ) ≤ 4 * (n.choose 2 : ℤ) + (2 * (n : ℤ) - 2) - 3 * A.p 2 := by
  have h := A.main_nat hn
  have hc := two_mul_choose_two n
  have h1 : 2 * n - 2 + 2 = 2 * n := by omega
  zify [show 2 ≤ 2 * n by omega] at h
  have hc' : (2 * (n.choose 2 : ℤ)) = ((n * (n - 1) : ℕ) : ℤ) := by exact_mod_cast hc
  push_cast at hc' h
  linarith

/-- **Main theorem** (`thm:main`): `p_3 ≤ 4/3 binom(n,2) + (2n-2)/3 - p_2`. -/
theorem main_theorem_rat (hn : 4 ≤ n) :
    (A.p 3 : ℚ) ≤ 4 / 3 * (n.choose 2 : ℚ) + (2 * (n : ℚ) - 2) / 3 - A.p 2 := by
  have h := A.main_theorem hn
  have h' : 3 * (A.p 3 : ℚ) ≤ 4 * (n.choose 2 : ℚ) + (2 * (n : ℚ) - 2) - 3 * A.p 2 := by
    exact_mod_cast h
  linarith

/-- In terms of the excess: `e ≤ 2n - 2 - 3 p_2`. -/
theorem excess_le (hn : 4 ≤ n) : A.excess ≤ 2 * (n : ℤ) - 2 - 3 * A.p 2 := by
  have h := A.main_theorem hn
  have hc := two_mul_choose_two n
  have hc' : (2 * (n.choose 2 : ℤ)) = ((n * (n - 1) : ℕ) : ℤ) := by exact_mod_cast hc
  rw [excess, card_X]
  linarith

/-- **Digon-free arrangements**: `p_3 ≤ 4/3 binom(n,2) + (2n-2)/3`. -/
theorem main_digon_free (hn : 4 ≤ n) (h2 : A.p 2 = 0) :
    (A.p 3 : ℚ) ≤ 4 / 3 * (n.choose 2 : ℚ) + (2 * (n : ℚ) - 2) / 3 := by
  have h := A.main_theorem_rat hn
  rw [h2, Nat.cast_zero, sub_zero] at h
  exact h

/-- **`cor:main`** (natural numbers): `p_3 ≤ ⌊2(n²-1)/3⌋`. -/
theorem cor_main (hn : 4 ≤ n) : A.p 3 ≤ 2 * (n ^ 2 - 1) / 3 := by
  have h := A.main_nat hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : (k + 1) ^ 2 - 1 = (k + 1) * k + k := by
    rw [show (k + 1) ^ 2 = (k + 1) * k + k + 1 by ring]; omega
  rw [Nat.add_sub_cancel] at h
  rw [hk, Nat.le_div_iff_mul_le (by norm_num)]
  generalize (k + 1) * k = N at *
  omega

/-- **`cor:main`** (as stated in the notes): `p_3 ≤ ⌊4/3 binom(n,2) + (2n-2)/3⌋`, and this floor
is `⌊2(n²-1)/3⌋`. -/
theorem cor_main_floor (hn : 4 ≤ n) :
    (A.p 3 : ℤ) ≤ ⌊4 / 3 * (n.choose 2 : ℚ) + (2 * (n : ℚ) - 2) / 3⌋ ∧
      4 / 3 * (n.choose 2 : ℚ) + (2 * (n : ℚ) - 2) / 3 = 2 * ((n : ℚ) ^ 2 - 1) / 3 := by
  refine ⟨Int.le_floor.2 ?_, ?_⟩
  · have h := A.main_theorem_rat hn
    have : (0 : ℚ) ≤ A.p 2 := Nat.cast_nonneg _
    push_cast
    linarith
  · have hc := two_mul_choose_two n
    have hc' : (2 * (n.choose 2 : ℚ)) = (n : ℚ) * ((n : ℚ) - 1) := by
      rw [show ((n : ℚ) - 1) = ((n - 1 : ℕ) : ℚ) by push_cast [show 1 ≤ n by omega]; ring]
      exact_mod_cast hc
    linear_combination (2 / 3 : ℚ) * hc'

end Pca.Arrangement
