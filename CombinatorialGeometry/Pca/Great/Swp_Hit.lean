/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# First hits along a permutation, and swapping consecutive pairs (`doc/pca/great.md` 4.3)

`Hit s O v w j`: walking along `s` from `v`, the first point in `O` is `w`, reached after `j`
steps. If `ρ` swaps `y ↔ s y` for `y ∈ S` (`swapAlong`) and no pair has both points in `O`, then
the first hits of `O ∘ ρ` are the `ρ`-images of the first hits of `O`. Consequently first returns
are the same for `s` and for `ρ s ρ`. This is the core of "a flip of a triangle with a side on the
new curve keeps the deletion".
-/
import Pca.Flip

open Equiv Finset

namespace Pca.Great

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The first point of `O` on the `s`-walk from `v` is `w`, after `j` steps. -/
def Hit (s : Perm X) (O : X → Prop) (v w : X) (j : ℕ) : Prop :=
  (s ^ j) v = w ∧ O w ∧ ∀ i < j, ¬ O ((s ^ i) v)

variable {s : Perm X} {S : Finset X} (hS : ∀ y ∈ S, s y ∉ S) {O : X → Prop}
  (hO : ∀ y ∈ S, ¬ (O y ∧ O (s y)))
include hS hO

theorem swapAlong_cases (x : X) :
    (x ∈ S ∧ swapAlong s S x = s x) ∨ (s.symm x ∈ S ∧ swapAlong s S x = s.symm x) ∨
      (x ∉ S ∧ s.symm x ∉ S ∧ swapAlong s S x = x) := by
  unfold swapAlong
  by_cases hx : x ∈ S
  · exact Or.inl ⟨hx, if_pos hx⟩
  · by_cases hy : s.symm x ∈ S
    · exact Or.inr (Or.inl ⟨hy, by rw [if_neg hx, if_pos hy]⟩)
    · exact Or.inr (Or.inr ⟨hx, hy, by rw [if_neg hx, if_neg hy]⟩)

omit hO in
theorem swapAlong_of_mem {y : X} (hy : y ∈ S) : swapAlong s S y = s y := by
  unfold swapAlong; rw [if_pos hy]

omit hO in
theorem swapAlong_s_of_mem {y : X} (hy : y ∈ S) : swapAlong s S (s y) = y := by
  unfold swapAlong; rw [if_neg (hS y hy), Equiv.symm_apply_apply, if_pos hy]

/-- **Key lemma.** -/
theorem hit_swap {v w : X} {j : ℕ} (hv : s.symm v ∉ S) (h : Hit s O v w j) :
    ∃ j', Hit s (fun x => O (swapAlong s S x)) v (swapAlong s S w) j' := by
  obtain ⟨hw, hOw, hmin⟩ := h
  have hsucc : ∀ p : ℕ, s ((s ^ p) v) = (s ^ (p + 1)) v := fun p => by
    rw [pow_succ', Perm.mul_apply]
  have G : ∀ p < j, ¬ ((s ^ p) v ∈ S ∧ p + 1 = j) → ¬ O (swapAlong s S ((s ^ p) v)) := by
    intro p hp hex
    rcases swapAlong_cases hS hO ((s ^ p) v) with ⟨hx, e⟩ | ⟨hx, e⟩ | ⟨-, -, e⟩
    · rw [e, hsucc]; exact hmin _ (by by_contra hc; exact hex ⟨hx, by omega⟩)
    · rw [e]
      rcases p with _ | p
      · exact absurd hx (by simpa using hv)
      · rw [← hsucc p, Equiv.symm_apply_apply]; exact hmin p (by omega)
    · rw [e]; exact hmin p hp
  by_cases hwS : w ∈ S
  · -- (b)
    refine ⟨j + 1, ?_, ?_, fun p hp => ?_⟩
    · rw [← hsucc, hw, swapAlong_of_mem hS hwS]
    · show O (swapAlong s S (swapAlong s S w))
      rw [swapAlong_of_mem hS hwS, swapAlong_s_of_mem hS hwS]; exact hOw
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
      · refine G p hp fun ⟨hx, hpj⟩ => hS _ hx ?_
        rw [hsucc, hpj, hw]; exact hwS
      · show ¬ O (swapAlong s S ((s ^ _) v))
        rw [hw, swapAlong_of_mem hS hwS]
        exact fun h' => hO w hwS ⟨hOw, h'⟩
  by_cases hwS' : s.symm w ∈ S
  · -- (c)
    have hj : j ≠ 0 := by
      rintro rfl; rw [pow_zero] at hw; exact hv (by rw [← hw] at hwS'; exact hwS')
    have hwp : (s ^ (j - 1)) v = s.symm w := by
      rw [← hw, show j = (j - 1) + 1 by omega, ← hsucc, Equiv.symm_apply_apply,
        Nat.add_sub_cancel]
    have e : swapAlong s S w = s.symm w := by
      unfold swapAlong; rw [if_neg hwS, if_pos hwS']
    refine ⟨j - 1, by rw [hwp, e], ?_, fun p hp => G p (by omega) fun ⟨_, h'⟩ => by omega⟩
    show O (swapAlong s S (swapAlong s S w))
    rw [e, swapAlong_of_mem hS hwS', Equiv.apply_symm_apply]; exact hOw
  · -- (a)
    have e : swapAlong s S w = w := by unfold swapAlong; rw [if_neg hwS, if_neg hwS']
    refine ⟨j, by rw [hw, e], by show O (swapAlong s S (swapAlong s S w)); rw [e, e]; exact hOw,
      fun p hp => G p hp fun ⟨hx, hpj⟩ => hwS' ?_⟩
    rw [← hw, ← hpj, ← hsucc, Equiv.symm_apply_apply]; exact hx

omit [Fintype X] [DecidableEq X] hS hO in
/-- The conjugated walk. -/
theorem hit_conj {ρ : Perm X} (hρ : ∀ x, ρ (ρ x) = x) {u w : X} {j : ℕ}
    (h : Hit s (fun x => O (ρ x)) u w j) : Hit (ρ * s * ρ) O (ρ u) (ρ w) j := by
  have hpow : ∀ p : ℕ, ((ρ * s * ρ) ^ p) (ρ u) = ρ ((s ^ p) u) := by
    intro p
    induction p with
    | zero => rfl
    | succ p ih =>
      rw [pow_succ', Perm.mul_apply, ih, Perm.mul_apply, Perm.mul_apply, hρ, pow_succ',
        Perm.mul_apply]
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [hpow, h1], h2, fun i hi => by rw [hpow]; exact h3 i hi⟩

end Pca.Great
