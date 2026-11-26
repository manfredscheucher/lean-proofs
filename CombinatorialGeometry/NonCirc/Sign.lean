/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import NonCirc.Lorentz
import Mathlib.Data.Sign.Basic

/-! # Three-valued signs of identities

Every identity used by the certificates has the form "a sum of real terms is `0`". On signs
(`SignType`: `-1, 0, 1`) this gives `NAE`: either all terms are `0`, or both signs occur. Zero
terms are allowed, so no genericity assumption is needed.
-/

namespace NonCirc

/-- "Not all equal" for three-valued signs: all zero, or both `1` and `-1` occur. -/
def NAE (l : List SignType) : Prop := (∀ x ∈ l, x = 0) ∨ ((1 : SignType) ∈ l ∧ (-1 : SignType) ∈ l)

instance (l : List SignType) : Decidable (NAE l) := by unfold NAE; infer_instance

lemma all_zero_of_nonneg_sum : ∀ l : List ℝ, (∀ x ∈ l, 0 ≤ x) → l.sum = 0 → ∀ x ∈ l, x = 0
  | [], _, _ => by simp
  | a :: l, h, hs => by
    simp only [List.sum_cons] at hs
    have ha : 0 ≤ a := h a (by simp)
    have hl : ∀ x ∈ l, 0 ≤ x := fun x hx => h x (by simp [hx])
    have hl0 : 0 ≤ l.sum := List.sum_nonneg hl
    have ha0 : a = 0 := by linarith
    have := all_zero_of_nonneg_sum l hl (by linarith)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha0
    · exact this x hx

/-- A sum of real numbers that vanishes has `NAE` signs. -/
lemma nae_of_sum (l : List ℝ) (h : l.sum = 0) : NAE (l.map SignType.sign) := by
  by_cases hp : ∃ x ∈ l, 0 < x
  · by_cases hn : ∃ x ∈ l, x < 0
    · obtain ⟨x, hx, hx0⟩ := hp
      obtain ⟨y, hy, hy0⟩ := hn
      exact Or.inr ⟨List.mem_map.2 ⟨x, hx, sign_pos hx0⟩, List.mem_map.2 ⟨y, hy, sign_neg hy0⟩⟩
    · push Not at hn
      obtain ⟨x, hx, hx0⟩ := hp
      have := all_zero_of_nonneg_sum l hn h x hx
      linarith
  · push Not at hp
    have hsum : ∀ l : List ℝ, (l.map (- ·)).sum = -l.sum := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    have h' := all_zero_of_nonneg_sum (l.map (- ·))
      (fun y hy => by obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy; exact neg_nonneg.mpr (hp x hx))
      (by rw [hsum, h, neg_zero])
    left
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    have : -x = 0 := h' (-x) (List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [neg_eq_zero.mp this, sign_zero]

end NonCirc
