/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH p. 325: the sweep never gets stuck (graph language)

"Lemma 3.3 states that if we remove one curve from the smallest counterexample, then some
operation applies. Lemmas 3.4 and 3.8, however, say that the operations of taking a curve or
passing a hump never apply after removing one curve. Lemma 3.11 proves the existence of a curve
whose removal does not leave a triangle. This contradiction proves that any arrangement of
bi-infinite, two-intersecting curves in the Euclidean plane can be swept by a curve that maintains
the two-intersection property."

`not_stuck`: every sweep configuration is finished or one of the three operations applies (only
the first move is needed for `SweepFirstMove`; the full sweep is not stated). Proved from Lemma 3.11,
`removal_leaves_triangle` and `exists_removal` (no `sorry` here).
-/
import Pca.Sweep.L311

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

variable (Γ) in
/-- A stuck configuration gives a minimal counterexample (the size order is well-founded). -/
theorem exists_minCE (h : Γ.Stuck) : ∃ (n' : ℕ) (K : Conf.{u} n'), K.Γ.MinCE := by
  let r : ℕ × ℕ → ℕ × ℕ → Prop := Prod.Lex (· < ·) (· < ·)
  have hwf : WellFounded r := WellFounded.prod_lex wellFounded_lt wellFounded_lt
  let P : Set (ℕ × ℕ) := {p | ∃ (n' : ℕ) (K : Conf.{u} n'), K.Γ.Stuck ∧
    (K.Γ.numVertices, K.Γ.numCurves) = p}
  have hne : P.Nonempty := ⟨_, n, ⟨D, Γ⟩, h, rfl⟩
  obtain ⟨n', K, hK, hp⟩ := hwf.min_mem P hne
  refine ⟨n', K, hK, fun n'' K' hlt hK' => ?_⟩
  have hmem : (K'.Γ.numVertices, K'.Γ.numCurves) ∈ P := ⟨n'', K', hK', rfl⟩
  apply hwf.not_lt_min P hmem
  rw [← hp]
  exact Prod.lex_def.mpr hlt

variable (Γ) in
/-- **SH p. 325**: the sweep never gets stuck. -/
theorem not_stuck : ¬ Γ.Stuck := by
  intro hS
  obtain ⟨n', K, hK⟩ := exists_minCE Γ hS
  obtain ⟨γ, hγ, hno⟩ := hK.lemma_3_11
  obtain ⟨X⟩ := exists_removal (Γ := K.Γ) {γ} (by
    rw [Finset.mem_singleton]; exact fun h => hγ.1 h.symm)
  obtain ⟨d', hd'⟩ := hK.removal_leaves_triangle hγ X
  exact hno X d' hd'

variable (Γ) in
/-- Every configuration is finished or can make progress. -/
theorem terminal_or_progress : Γ.Terminal ∨ Γ.Progress := by
  by_contra h
  push Not at h
  exact Γ.not_stuck h

end SConf

end Pca.Sweep
