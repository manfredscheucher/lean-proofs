/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package R (removal), generic facts on maps

Helper file for `Pca/Sweep/Removal.lean`, independent of sweep configurations:

* `r_euler_of_cut`: a connected nonempty map in which every cycle of segments is a cut satisfies
  Euler `V - E + F = 2` (the converse of `j_mem_range_of_mem_ker`, with the boundary maps of
  `Pca/Great/Map_Euler.lean`);
* `r_tau_le_iff`: the returns of a first-return map up to time `N` are counted by the darts of `K`
  on the walk up to time `N`.
-/
import Pca.Great.Map_Euler

open Equiv Finset Module

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u v


section Euler

variable {X : Type u} [Fintype X] [DecidableEq X] (σ α : Perm X)

theorem r_sum_orbits {M : Type*} [AddCommMonoid M] (f : Perm X) (F : X → M) :
    ∑ o : Orbit f, ∑ y ∈ o.darts, F y = ∑ y, F y := by
  have h := Finset.sum_fiberwise (s := (univ : Finset X)) (g := Orbit.mk f) F
  rw [← h]
  refine sum_congr rfl fun o _ => ?_
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and, Orbit.mem_darts]

variable {σ α} (hαα : ∀ x, α (α x) = x) (hαne : ∀ x, α x ≠ x)
  (hconn : ∀ x y, Relation.EqvGen (fun a b => b = σ a ∨ b = α a) x y)
include hαα hαne hconn

theorem r_sumAll_segBdry (h : Orbit α → ZMod 2) : MapFacts.sumAll σ (MapFacts.segBdry σ α h) = 0 := by
  change ∑ x : Orbit σ, ∑ y ∈ x.darts, h (Orbit.mk α y) = 0
  rw [r_sum_orbits σ (fun y => h (Orbit.mk α y)), ← r_sum_orbits α (fun y => h (Orbit.mk α y))]
  refine sum_eq_zero fun s _ => ?_
  obtain ⟨y, rfl⟩ := s.exists_mk
  have hd : (Orbit.mk α y).darts = {y, α y} := by
    rw [Orbit.darts_mk, MapFacts.orbitFinset_inv α hαα]
  have hs : Orbit.mk α (α y) = Orbit.mk α y := by
    rw [Orbit.mk_eq_mk]; exact (MapFacts.sameCycle_of_pow α y 1).symm
  rw [hd, sum_pair (hαne y).symm, hs]
  exact MapFacts.zmod2_add_self _

/-- **Euler from Jordan**: a connected nonempty map in which every cycle is a cut is a sphere. -/
theorem r_euler_of_cut [Nonempty X]
    (hcut : ∀ h, MapFacts.segBdry σ α h = 0 → ∃ g, MapFacts.cellBdry σ α g = h) :
    (Fintype.card (Orbit σ) : ℤ) - Fintype.card (Orbit α) + Fintype.card (Orbit (σ * α)) = 2 := by
  have hle : LinearMap.range (MapFacts.cellBdry σ α) ≤ LinearMap.ker (MapFacts.segBdry σ α) := by
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]; exact MapFacts.segBdry_cellBdry hαα hαne hconn g
  have hge : LinearMap.ker (MapFacts.segBdry σ α) ≤ LinearMap.range (MapFacts.cellBdry σ α) := by
    intro h hh
    obtain ⟨g, hg⟩ := hcut h hh
    exact ⟨g, hg⟩
  have heq := le_antisymm hle hge
  have hL := LinearMap.finrank_range_add_finrank_ker (MapFacts.cellBdry σ α)
  have hB := LinearMap.finrank_range_add_finrank_ker (MapFacts.segBdry σ α)
  rw [finrank_fintype_fun_eq_card] at hL hB
  have hk := MapFacts.finrank_ker_cellBdry_le hαα hαne hconn
  have hk1 : 1 ≤ finrank (ZMod 2) (LinearMap.ker (MapFacts.cellBdry σ α)) := by
    have hmem : (fun _ => (1 : ZMod 2)) ∈ LinearMap.ker (MapFacts.cellBdry σ α) := by
      rw [LinearMap.mem_ker]
      funext s
      obtain ⟨y, rfl⟩ := s.exists_mk
      rw [MapFacts.cellBdry_mk hαα hαne hconn, Pi.zero_apply]
      exact MapFacts.zmod2_add_self _
    have hne : (fun _ => (1 : ZMod 2)) ≠ (0 : Orbit (σ * α) → ZMod 2) := by
      obtain ⟨y⟩ := ‹Nonempty X›
      intro h0
      have := congrFun h0 (Orbit.mk (σ * α) y)
      simp at this
    have h1 := finrank_span_singleton (K := ZMod 2) hne
    rw [← h1]
    exact Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).2 hmem)
  have hr := MapFacts.card_le_finrank_range_segBdry hαα hαne hconn
  have hr2 : finrank (ZMod 2) (LinearMap.range (MapFacts.segBdry σ α)) + 1 ≤
      Fintype.card (Orbit σ) := by
    have hle2 : LinearMap.range (MapFacts.segBdry σ α) ≤ LinearMap.ker (MapFacts.sumAll σ) := by
      rintro _ ⟨h, rfl⟩
      rw [LinearMap.mem_ker]; exact r_sumAll_segBdry hαα hαne hconn h
    have h1 := LinearMap.finrank_range_add_finrank_ker (MapFacts.sumAll σ)
    rw [finrank_fintype_fun_eq_card] at h1
    have h2 : 1 ≤ finrank (ZMod 2) (LinearMap.range (MapFacts.sumAll σ)) := by
      obtain ⟨y⟩ := ‹Nonempty X›
      have hmem : (1 : ZMod 2) ∈ LinearMap.range (MapFacts.sumAll σ) := by
        refine ⟨Pi.single (Orbit.mk σ y) 1, ?_⟩
        change ∑ x, Pi.single (Orbit.mk σ y) (1 : ZMod 2) x = 1
        simp
      have h1' := finrank_span_singleton (K := ZMod 2) (one_ne_zero : (1 : ZMod 2) ≠ 0)
      rw [← h1']
      exact Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).2 hmem)
    have h3 := Submodule.finrank_mono hle2
    omega
  rw [← heq] at hB
  omega

end Euler

/-! ## Counting returns -/

section Count

variable {X : Type u} [Fintype X] [DecidableEq X] {X' : Type v} [Fintype X'] [DecidableEq X']
  {f : Perm X} {f' : Perm X'} {ι : X' → X} {K : X → Prop} [DecidablePred K]

/-- The returns up to time `N` are the first `c` returns, `c` the number of darts of `K` on the
walk at times `1, …, N`. -/
theorem r_tau_le_iff (h : MapFacts.IsFR f f' ι K) (hK : ∀ x', K (ι x')) (x' : X') (N : ℕ) (j : ℕ) :
    h.tau x' j ≤ N ↔ j ≤ ((range N).filter (fun t => K ((f ^ (t + 1)) (ι x')))).card := by
  induction N generalizing j with
  | zero =>
    simp only [range_zero, filter_empty, card_empty, nonpos_iff_eq_zero]
    constructor
    · intro hj
      by_contra hne
      have := h.tau_strictMono x' (Nat.pos_of_ne_zero hne)
      simp [MapFacts.IsFR.tau] at this; omega
    · rintro rfl; simp [MapFacts.IsFR.tau]
  | succ N ih =>
    rw [range_add_one, filter_insert]
    by_cases hKN : K ((f ^ (N + 1)) (ι x'))
    · rw [if_pos hKN, card_insert_of_notMem (by simp)]
      obtain ⟨j0, hj0⟩ := h.mem_of_mem hK x' (N + 1) hKN
      set c := ((range N).filter (fun t => K ((f ^ (t + 1)) (ι x')))).card
      have hc : c + 1 = j0 := by
        have h1 : ¬ h.tau x' (c + 1) ≤ N := fun h' => by have := (ih _).1 h'; omega
        have h2 : ¬ j0 ≤ c := fun h' => by have := (ih _).2 h'; omega
        have h3 : h.tau x' j0 ≤ h.tau x' (c + 1) := by omega
        have h4 := (h.tau_strictMono x').le_iff_le.1 h3
        omega
      constructor
      · intro hj
        rcases Nat.lt_or_ge N (h.tau x' j) with hlt | hge
        · have : h.tau x' j = h.tau x' j0 := by omega
          have := (h.tau_strictMono x').injective this; omega
        · have := (ih j).1 hge; omega
      · intro hj
        rcases Nat.lt_or_ge c j with hlt | hge
        · have : j = j0 := by omega
          subst this; omega
        · have := (ih j).2 hge; omega
    · rw [if_neg hKN]
      constructor
      · intro hj
        rcases Nat.lt_or_ge N (h.tau x' j) with hlt | hge
        · have he : h.tau x' j = N + 1 := by omega
          have := hK ((f' ^ j) x')
          rw [h.pow_apply, he] at this
          exact absurd this hKN
        · exact (ih j).1 hge
      · intro hj; exact ((ih j).2 hj).trans (Nat.le_succ N)

end Count

end Pca.Sweep
