/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): FROS Claim B (the digraph `A|_Q` has a source)

FROS, Claim B: "The directed graph of the arrangement `A|_Q` is acyclic." Then "there is at least
one source". Graph language: `Pred x' x` (the forward chord segment arriving at the vertex `x`
starts at the vertex `x'`). A vertex that is not a source has a predecessor (`exists_pred`).
`exists_source`: a lens with a vertex has a source; this is the acyclicity of `Pred` (FROS: a
minimal directed cycle bounds a cell, which is impossible): otherwise following predecessors gives
a simple directed cycle (`cyc_of_pred`); a cycle that is not tight has one with a smaller region
(`Cyc.exists_smaller`), and no cycle is tight (`Cyc.not_good`). Details in `doc/pca/flipgraph.md`
(Track F, F-D6).
-/
import Pca.FlipGraph.CycleMin

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement' Chain

namespace Lens

variable {A : Arrangement n D} (Λ : Lens A)

/-- `x'` precedes `x` in `A|_Q`: a forward chord dart runs from the vertex `x'` to the vertex `x`. -/
def Pred (x' x : A.Crossing) : Prop :=
  Λ.IsVertex x' ∧ Λ.IsVertex x ∧
    ∃ w, Λ.Fwd w ∧ A.crossingOf w = x' ∧ A.crossingOf (A.α w) = x

variable {Λ}

/-- A forward dart that is not a foot dart starts at a vertex. -/
theorem isVertex_start (ht : Λ.Transversal) {w : D} (hw : Λ.Fwd w) (hnf : ¬ Λ.L (A.σ w)) :
    Λ.IsVertex (A.crossingOf w) := by
  obtain ⟨z₀, k, hz, hc, rfl⟩ := exists_foot ht hw
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0; exact absurd (by simpa using hz) hnf
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Walk.pow_succ_apply]
    exact isVertex_passed (hc k' (by omega)) (by rw [← Walk.pow_succ_apply]; exact hc _ le_rfl)

/-- A vertex that is not a source has a predecessor. -/
theorem exists_pred (ht : Λ.Transversal) {x : A.Crossing} (hx : Λ.IsVertex x)
    (hns : ¬ Λ.SourceV x) : ∃ x', Λ.Pred x' x := by
  have : ∃ w, Λ.Fwd w ∧ A.crossingOf (A.α w) = x ∧ ¬ Λ.L (A.σ w) := by
    by_contra h
    push_neg at h
    exact hns ⟨hx, fun w hw hwx => h w hw hwx⟩
  obtain ⟨w, hw, hwx, hnf⟩ := this
  exact ⟨_, isVertex_start ht hw hnf, hx, w, hw, rfl, hwx⟩

/-- **FROS Claim B** (in the form used): a lens with a vertex has a source. -/
theorem exists_source (hs : Λ.Sep) (ht : Λ.Transversal) (hv : ∃ x, Λ.IsVertex x) :
    ∃ x, Λ.SourceV x := by
  classical
  by_contra hno
  push_neg at hno
  obtain ⟨x₀, hx₀⟩ := hv
  have hpre : ∀ x, Λ.IsVertex x → ∃ w, Λ.Fwd w ∧ A.crossingOf (A.α w) = x ∧
      Λ.IsVertex (A.crossingOf w) := by
    intro x hx
    obtain ⟨x', hx', -, w, hw, rfl, hwx⟩ := exists_pred ht hx (hno x)
    exact ⟨w, hw, hwx, hx'⟩
  haveI : Nonempty D := by obtain ⟨y, -⟩ := x₀.exists_mk; exact ⟨y⟩
  choose! p hp using hpre
  obtain ⟨Z, -⟩ := cyc_of_pred Λ.IsVertex p
    (fun x hx => ⟨(hp x hx).1, (hp x hx).2.1, (hp x hx).2.2, hx⟩) hx₀
  -- infinite descent on the size of the region
  suffices h : ∀ N, ∀ Z : Λ.Cyc, Z.size = N → False from h _ Z rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro Z hZ
    obtain ⟨Z', hZ'⟩ := Z.exists_smaller hs ht (Z.not_good hs ht)
    exact ih _ (hZ ▸ hZ') Z' rfl

end Lens

end Pca.FlipGraph
