/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Doubling a curve: every curve is crossed twice; the doubling walk
-/
import Pca.Great.Dbl_Cells

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

namespace Dbl

/-- The other curve at the `k`-th crossing of the walk. -/
abbrev f (A : Arrangement n D) (y0 : D) (k : ℕ) : Fin n := A.curve (A.σ (y A y0 k))

variable {A : Arrangement n D} (hA : A.IsGreat) (y0 : D)
include hA

theorem f_ne (k : ℕ) : f A y0 k ≠ A.curve y0 := by
  rw [← curve_y hA y0 k]; exact A.isArrangement.curve_σ _

theorem f_iff {e : Fin n} (he : e ≠ A.curve y0) {k₁ : ℕ} (hk₁ : k₁ < n - 1)
    (hpos : ∀ j < 2 * (n - 1),
      e ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) y0)) ↔
        j = k₁ ∨ j = k₁ + (n - 1)) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * (n - 1)) :
    f A y0 k = e ↔ k = k₁ ∨ k = k₁ + (n - 1) ∨ (k₁ = 0 ∧ k = 2 * (n - 1)) := by
  have hmem : ∀ j, e ∈ Arrangement.Crossing.curves A (A.crossingOf (y A y0 j)) ↔ f A y0 j = e := by
    intro j
    rw [A.curves_crossingOf, mem_insert, mem_singleton, curve_y hA]
    constructor
    · rintro (h | h); exacts [absurd h he, h.symm]
    · intro h; exact Or.inr h.symm
  by_cases hk : k < 2 * (n - 1)
  · rw [← hmem, hpos k hk]; omega
  · have hk' : k = 2 * (n - 1) := by omega
    subst hk'
    have : f A y0 (2 * (n - 1)) = f A y0 0 := by
      simp only [f]; rw [show 2 * (n - 1) = 0 + 2 * (n - 1) by omega, y_mod]
    rw [this, ← hmem, hpos 0 (by have := A.two_le_n; omega)]
    omega

variable (hn : 2 ≤ n)
include hn

theorem curve_t (i : Fin (2 * n)) :
    A.curve (t A y0 i) = if i.val = 0 ∨ i.val = n then A.curve y0
      else f A y0 (if i.val ≤ n - 1 then 2 * (n - 1) + 1 - i.val else 2 * n - i.val) := by
  by_cases h0 : i.val = 0
  · rw [t_0 A y0 h0, if_pos (Or.inl h0)]; rfl
  by_cases h1 : i.val ≤ n - 1
  · rw [t_R A y0 h0 h1, if_neg (by omega), if_pos h1]
  by_cases h2 : i.val = n
  · rw [t_n A y0 h0 h1 h2, if_pos (Or.inr h2), A.isArrangement.curve_α, curve_y hA]
  · rw [t_L A y0 h0 h1 h2, if_neg (by omega), if_neg h1, A.isArrangement.curve_α,
      A.curve_σσσ]

theorem twice (e : Fin n) : (univ.filter (fun i => A.curve (t A y0 i) = e)).card = 2 := by
  have key : ∀ a b : ℕ, a < 2 * n → b < 2 * n → a ≠ b →
      (∀ i : Fin (2 * n), A.curve (t A y0 i) = e ↔ i.val = a ∨ i.val = b) →
      (univ.filter (fun i => A.curve (t A y0 i) = e)).card = 2 := by
    intro a b ha hb hab h
    have : univ.filter (fun i => A.curve (t A y0 i) = e) = {⟨a, ha⟩, ⟨b, hb⟩} := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, h, Fin.ext_iff]
    rw [this, card_pair (by simp [Fin.ext_iff, hab])]
  by_cases hec : e = A.curve y0
  · subst hec
    refine key 0 n (by omega) (by omega) (by omega) fun i => ?_
    rw [curve_t hA y0 hn]
    by_cases h : i.val = 0 ∨ i.val = n
    · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
    · rw [if_neg h]; exact ⟨fun h' => absurd h' (f_ne hA y0 _), fun h' => absurd h' h⟩
  obtain ⟨k₁, hk₁, hpos⟩ := pos_two hA y0 (e := e) hec
  have hfi := f_iff hA y0 hec hk₁ hpos
  by_cases hk0 : k₁ = 0
  · subst hk0
    refine key 1 (n + 1) (by omega) (by omega) (by omega) fun i => ?_
    have hi := i.isLt
    rw [curve_t hA y0 hn]
    split_ifs with h h1
    · exact ⟨fun h' => absurd h'.symm hec, fun h' => by omega⟩
    · rw [hfi _ (by omega) (by omega)]; omega
    · rw [hfi _ (by omega) (by omega)]; omega
  · refine key (n - k₁) (2 * n - k₁) (by omega) (by omega) (by omega) fun i => ?_
    have hi := i.isLt
    rw [curve_t hA y0 hn]
    split_ifs with h h1
    · exact ⟨fun h' => absurd h'.symm hec, fun h' => by omega⟩
    · rw [hfi _ (by omega) (by omega)]; omega
    · rw [hfi _ (by omega) (by omega)]; omega

/-- **The doubling walk** of the curve of `y0`. -/
def walk : InsWalk A (2 * n) where
  t := t A y0
  three_le := by omega
  adj := adj A y0 hn
  cell_inj := cell_inj hA y0 hn
  twice := twice hA y0 hn

theorem walk_sym : (walk hA y0 hn).Sym := fun i => sym A y0 hn hA i

theorem walk_t0 : (walk hA y0 hn).t ⟨0, by omega⟩ = y0 :=
  t_0 A y0 (i := ⟨0, by omega⟩) rfl

end Dbl

end Pca.Great
