/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH sweep in graph language: the sweeping lemma

`Pca.Sweep.sweepFirstMove : A.SweepFirstMove`, derived from the sweep
(`SConf.terminal_or_progress`) and the start configuration (`exists_ofSide`). Re-exported as
`Arrangement.sweepFirstMove` in `Pca/SweepLemma.lean`.
-/
import Pca.Sweep.Instance
import Pca.Sweep

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

/-- The first move of the sweep on the side of `cellOf y`, avoiding `cellOf y`. -/
theorem first_move (A : Pca.Arrangement n D) (C : Fin n) (s : A.Cell → ZMod 2)
    (hs : A.IsSide C s) (y : D) (hy : A.curve y = C) :
    ∃ g : A.Cell, g ≠ A.cellOf y ∧ s g = s (A.cellOf y) ∧ (∃ d ∈ g.darts, A.curve d = C) ∧
      (A.IsDigon g ∨ A.IsTriangle g) := by
  obtain ⟨Γ, hT, hL, hP⟩ := exists_ofSide A C s hs y hy
  rcases Γ.terminal_or_progress with h | h
  · exact absurd h hT
  rcases h with ⟨t, ht⟩ | ⟨t, ht⟩ | h
  · exact hP t (Or.inl ht)
  · exact hP t (Or.inr ht)
  · exact absurd h hL

/-- **Sweeping lemma** (FS2021 form), from the SH sweep in graph language. -/
theorem sweepFirstMove (A : Pca.Arrangement n D) : A.SweepFirstMove := by
  intro C s hs f₀
  by_cases h : ∃ d ∈ f₀.darts, A.curve d = C
  · obtain ⟨d, hd, hdC⟩ := h
    have hf : A.cellOf d = f₀ := Pca.Orbit.mem_darts.1 hd
    obtain ⟨g, hne, hsg, rest⟩ := first_move A C s hs d hdC
    exact ⟨g, hf ▸ hne, hf ▸ hsg, rest⟩
  · obtain ⟨y, hy, hys⟩ := Pca.Arrangement.exists_dart_on_side hs (s f₀)
    obtain ⟨g, -, hsg, hC, hk⟩ := first_move A C s hs y hy
    refine ⟨g, ?_, hsg.trans hys, hC, hk⟩
    rintro rfl
    exact h hC

/-- **Two digons or triangles on each side** of every pseudocircle (SH Lemma 4.1's argument). -/
theorem sweepTwoCells (A : Pca.Arrangement n D) : A.SweepTwoCells :=
  (A.sweepFirstMove_iff).1 (sweepFirstMove A)

end Pca.Sweep
