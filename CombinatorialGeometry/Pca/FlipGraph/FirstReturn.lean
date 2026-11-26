/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): first returns and adjacent swaps

Pure permutation facts for P1/P2 of `Delete.lean`. The straight map of `A − C'` is the first
return of `straight` to the kept darts, and the flip changes `straight` to `ρ ∘ straight ∘ ρ`
where `ρ = swapAlong straight U` swaps every side dart `u ∈ U` with `straight u` (two consecutive
darts of a straight walk exchange their order).

* `IsFirst f K x e`: `e` is the first return of `x` to `K` under `f`; unique (`IsFirst.unique`).
* `isFirst_conj`: if `ρ` is an involution preserving `K`, first returns of `ρ f ρ` are the
  `ρ`-images of first returns of `f` (P2: every swapped pair is kept).
* `isFirst_swap`: if no swapped pair `{u, f u}` is entirely in `K`, then `ρ f ρ` and `f` have the
  same first returns from `K` (P1).
-/
import Pca.Flip

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]

/-- `e` is the first return of `x` to `K` under `f`, after `k` steps. -/
def IsFirstAt (f : Perm D) (K : D → Prop) (x : D) (k : ℕ) (e : D) : Prop :=
  0 < k ∧ (f ^ k) x = e ∧ K e ∧ ∀ j, 0 < j → j < k → ¬ K ((f ^ j) x)

/-- `e` is the first return of `x` to `K` under `f`. -/
def IsFirst (f : Perm D) (K : D → Prop) (x e : D) : Prop := ∃ k, IsFirstAt f K x k e

variable {f g : Perm D} {K : D → Prop}

theorem pow_succ_apply' (f : Perm D) (k : ℕ) (x : D) : (f ^ (k + 1)) x = (f ^ k) (f x) := by
  rw [pow_succ, Perm.mul_apply]

theorem IsFirst.unique {x e e' : D} (h : IsFirst f K x e) (h' : IsFirst f K x e') : e = e' := by
  obtain ⟨k, hk0, rfl, hk, hlt⟩ := h
  obtain ⟨k', hk0', rfl, hk', hlt'⟩ := h'
  rcases lt_trichotomy k k' with h | rfl | h
  · exact absurd hk (hlt' k hk0 h)
  · rfl
  · exact absurd hk' (hlt k' hk0' h)

theorem isFirst_one {x : D} (h : K (f x)) : IsFirst f K x (f x) :=
  ⟨1, one_pos, by rw [pow_one], h, fun j h0 h1 => by omega⟩

theorem isFirst_step {x e : D} (h : ¬ K (f x)) (he : IsFirst f K (f x) e) : IsFirst f K x e := by
  obtain ⟨k, hk0, hke, hk, hlt⟩ := he
  refine ⟨k + 1, by omega, by rw [pow_succ_apply', hke], hk, fun j h0 h1 => ?_⟩
  rcases Nat.lt_or_ge j 2 with hj | hj
  · obtain rfl : j = 1 := by omega
    rwa [pow_one]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [pow_succ_apply']
    exact hlt i (by omega) (by omega)

/-- Unfolding one step of a first return. -/
theorem IsFirstAt.cases {x e : D} {k : ℕ} (h : IsFirstAt f K x k e) :
    (K (f x) ∧ e = f x) ∨ (¬ K (f x) ∧ ∃ k', k' < k ∧ IsFirstAt f K (f x) k' e) := by
  obtain ⟨hk0, hke, hk, hlt⟩ := h
  by_cases h1 : K (f x)
  · left
    refine ⟨h1, ?_⟩
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · obtain rfl : k = 1 := by omega
      rw [← hke, pow_one]
    · exact absurd (by rwa [pow_one]) (hlt 1 one_pos (by omega))
  · right
    refine ⟨h1, k - 1, by omega, ?_, ?_, hk, fun j h0 h2 => ?_⟩
    · have := hk0
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · obtain rfl : k = 1 := by omega
        rw [pow_one] at hke; exact absurd (hke ▸ hk) h1
      · omega
    · rw [← hke, ← pow_succ_apply', Nat.sub_add_cancel hk0]
    · rw [← pow_succ_apply']; exact hlt _ (by omega) (by omega)

/-! ## Conjugation by a `K`-preserving involution -/

theorem isFirst_conj {ρ : Perm D} (hρ : ∀ x, ρ (ρ x) = x) (hK : ∀ x, K (ρ x) ↔ K x)
    (hg : ∀ x, g x = ρ (f (ρ x))) {x e : D} (h : IsFirst f K (ρ x) e) :
    IsFirst g K x (ρ e) := by
  have hpow : ∀ j : ℕ, (g ^ j) x = ρ ((f ^ j) (ρ x)) := by
    intro j
    induction j with
    | zero => simp [hρ]
    | succ j ih => rw [pow_succ', Perm.mul_apply, ih, hg, hρ, pow_succ', Perm.mul_apply]
  obtain ⟨k, hk0, hke, hk, hlt⟩ := h
  refine ⟨k, hk0, by rw [hpow, hke], (hK e).2 hk, fun j h0 h1 => ?_⟩
  rw [hpow, hK]
  exact hlt j h0 h1

/-! ## Swapping consecutive pairs with at most one kept dart -/

section Swap

variable {U : Finset D} (hU1 : ∀ u ∈ U, f u ∉ U) (hU2 : ∀ u ∈ U, f (f u) ∉ U)
  (hg : ∀ x, g x = swapAlong f U (f (swapAlong f U x)))

include hU1 in
theorem swap_fst {u : D} (hu : u ∈ U) : swapAlong f U u = f u := by
  rw [swapAlong, if_pos hu]

include hU1 in
theorem swap_snd {u : D} (hu : u ∈ U) : swapAlong f U (f u) = u := by
  rw [swapAlong, if_neg (hU1 u hu), Equiv.symm_apply_apply, if_pos hu]

theorem swap_out {x : D} (h1 : x ∉ U) (h2 : f.symm x ∉ U) : swapAlong f U x = x := by
  rw [swapAlong, if_neg h1, if_neg h2]

include hU1 hU2 hg in
theorem g_out {x : D} (h1 : x ∉ U) (h2 : f.symm x ∉ U) (h3 : f x ∉ U) : g x = f x := by
  rw [hg, swap_out h1 h2, swap_out h3 (by simpa using h1)]

include hU1 hU2 hg in
theorem g_pre {x : D} (h1 : x ∉ U) (h2 : f.symm x ∉ U) (h3 : f x ∈ U) : g x = f (f x) := by
  rw [hg, swap_out h1 h2, swap_fst hU1 h3]

include hU1 hU2 hg in
theorem g_snd {u : D} (hu : u ∈ U) : g (f u) = u := by
  rw [hg, swap_snd hU1 hu, swap_snd hU1 hu]

include hU1 hU2 hg in
theorem g_fst {u : D} (hu : u ∈ U) : g u = f (f u) := by
  rw [hg, swap_fst hU1 hu, swap_out (hU2 u hu) (by simpa using hU1 u hu)]

variable (hmix : ∀ u ∈ U, ¬ (K u ∧ K (f u)))

include hU1 hU2 hg hmix in
theorem isFirst_swap_out (k : ℕ) : ∀ x e, x ∉ U → f.symm x ∉ U → IsFirstAt f K x k e →
    IsFirst g K x e := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro x e h1 h2 h
  by_cases h3 : f x ∈ U
  · have hgx := g_pre hU1 hU2 hg h1 h2 h3
    have hsnd := g_snd hU1 hU2 hg h3
    have hfst := g_fst hU1 hU2 hg h3
    rcases h.cases with ⟨hKu, rfl⟩ | ⟨hKu, k1, hk1, h4⟩
    · have hfu : ¬ K (f (f x)) := fun h => hmix _ h3 ⟨hKu, h⟩
      have h5 : IsFirst g K (f (f x)) (g (f (f x))) := isFirst_one (by rw [hsnd]; exact hKu)
      rw [hsnd] at h5
      exact isFirst_step (by rw [hgx]; exact hfu) (by rw [hgx]; exact h5)
    rcases h4.cases with ⟨hKfu, rfl⟩ | ⟨hKfu, k2, hk2, h5⟩
    · have h6 : IsFirst g K x (g x) := isFirst_one (by rw [hgx]; exact hKfu)
      rwa [hgx] at h6
    have step1 : IsFirst g K (f (f x)) e → IsFirst g K x e := fun h =>
      isFirst_step (by rw [hgx]; exact hKfu) (by rw [hgx]; exact h)
    have step2 : IsFirst g K (f x) e → IsFirst g K (f (f x)) e := fun h =>
      isFirst_step (by rw [hsnd]; exact hKu) (by rw [hsnd]; exact h)
    refine step1 (step2 ?_)
    rcases h5.cases with ⟨hKw, rfl⟩ | ⟨hKw, k3, hk3, h6⟩
    · have h7 : IsFirst g K (f x) (g (f x)) := isFirst_one (by rw [hfst]; exact hKw)
      rwa [hfst] at h7
    · refine isFirst_step (by rw [hfst]; exact hKw) ?_
      rw [hfst]
      exact ih k3 (by omega) _ _ (hU2 _ h3) (by simpa using hU1 _ h3) h6
  · have hgx := g_out hU1 hU2 hg h1 h2 h3
    rcases h.cases with ⟨hK1, rfl⟩ | ⟨hK1, k1, hk1, h4⟩
    · have h5 : IsFirst g K x (g x) := isFirst_one (by rw [hgx]; exact hK1)
      rwa [hgx] at h5
    · refine isFirst_step (by rw [hgx]; exact hK1) ?_
      rw [hgx]
      exact ih k1 hk1 _ _ h3 (by simpa using h1) h4

include hU1 hU2 hg hmix in
theorem isFirst_swap_pair {u e : D} {k : ℕ} (hu : u ∈ U) (h : IsFirstAt f K (f u) k e) :
    IsFirst g K u e := by
  have hfst := g_fst hU1 hU2 hg hu
  rcases h.cases with ⟨hKw, rfl⟩ | ⟨hKw, k2, -, h4⟩
  · have h5 : IsFirst g K u (g u) := isFirst_one (by rw [hfst]; exact hKw)
    rwa [hfst] at h5
  · refine isFirst_step (by rw [hfst]; exact hKw) ?_
    rw [hfst]
    exact isFirst_swap_out hU1 hU2 hg hmix k2 _ _ (hU2 _ hu) (by simpa using hU1 _ hu) h4

include hU1 hU2 hg hmix in
/-- P1 form: with no swapped pair entirely in `K`, first returns from `K` do not change. -/
theorem isFirst_swap {x e : D} (hx : K x) (h : IsFirst f K x e) : IsFirst g K x e := by
  obtain ⟨k, h⟩ := h
  by_cases h1 : x ∈ U
  · rcases h.cases with ⟨hK1, -⟩ | ⟨-, k1, -, h4⟩
    · exact absurd ⟨hx, hK1⟩ (hmix x h1)
    · exact isFirst_swap_pair hU1 hU2 hg hmix h1 h4
  by_cases h2 : f.symm x ∈ U
  · have hx' : f (f.symm x) = x := f.apply_symm_apply x
    have hKu : ¬ K (f.symm x) := fun h => hmix _ h2 ⟨h, by rw [hx']; exact hx⟩
    rw [← hx'] at h ⊢
    have hsnd := g_snd hU1 hU2 hg h2
    exact isFirst_step (by rw [hsnd]; exact hKu)
      (by rw [hsnd]; exact isFirst_swap_pair hU1 hU2 hg hmix h2 h)
  · exact isFirst_swap_out hU1 hU2 hg hmix k x e h1 h2 h

end Swap

end Pca.FlipGraph
