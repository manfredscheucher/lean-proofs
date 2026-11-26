/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Sanity properties checked on the test instances

`BasicFacts` collects the facts of milestone 1 and the identities of milestone 2 that hold
for every `n ≥ 2`; `NotesFacts` collects facts from the notes that need `n ≥ 4`. They are
checked on concrete instances with `native_decide`. Most of them are also proved in general
(see the docstrings below and `doc/pca/pca.md`).
-/
import Pca.Counting

open Finset

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

/-- Facts that hold for every arrangement. Proved in general (`Pca/Derived.lean`,
`Pca/Excess.lean`) except two parts that are only checked here: `|corners f| = |sides f| =
size f` for every cell (proved for digons and triangles), and `|Segment.cells s| = 2` for every
segment (proved for sides of digons and triangles). -/
def BasicFacts : Prop :=
  -- milestone 1: |X| = n(n-1), 2(n-1) crossings per pseudocircle, 2|X| segments, |X|+2 cells
  A.X.card = n * (n - 1) ∧
  (∀ C : Fin n, (A.crossingsOn C).card = 2 * (n - 1)) ∧
  (∀ C : Fin n, (A.segmentsOn C).card = 2 * (n - 1)) ∧
  Fintype.card A.Segment = 2 * A.X.card ∧
  Fintype.card A.Cell = A.X.card + 2 ∧
  -- a k-cell has k distinct corners and k distinct sides; a crossing has two curves
  (∀ f : A.Cell, (Cell.corners A f).card = f.size ∧ (Cell.sides A f).card = f.size) ∧
  (∀ x : A.Crossing, (Crossing.curves A x).card = 2) ∧
  (∀ s : A.Segment, (Segment.curves A s).card = 1 ∧ (Segment.cells A s).card = 2) ∧
  -- counting triangles at corners: by cells and by angles
  (∀ x : A.Crossing, A.t x = A.tCorners x ∧ A.t x = A.tAngles x) ∧
  -- milestone 2 identities that hold for all n
  3 * A.p 3 = ∑ x, A.t x ∧
  A.excess = (A.numDiamond : ℤ) - A.numTrigophobic ∧
  A.excess = ∑ C : Fin n, ((A.tC C : ℤ) - 2 * (n - 1 : ℕ)) ∧
  (∀ C : Fin n, (A.tC C : ℤ) - 2 * (n - 1 : ℕ) =
    (A.numDiamondOn C : ℤ) - A.numTrigophobicOn C) ∧
  A.excess % 3 = ((n * (n - 1) : ℕ) : ℤ) % 3

instance : Decidable A.BasicFacts := by unfold BasicFacts; infer_instance

/-- Facts from the notes that need `n ≥ 4` (for example `e = |X'| - def` fails for the Krupp
arrangement, `n = 3`, where `t x = 4`). The first three are proved in general for `n ≥ 4`
(`t_le_three`, `excess_eq_X'_sub_deficiency_of_four_le`, `two_p2_le_deficiency`); the potential
bound `|X'| + p_2 ≤ 2n - 2` is open (milestone 6). -/
def NotesFacts : Prop :=
  (∀ x : A.Crossing, A.t x ≤ 3) ∧
  A.excess = (A.X'.card : ℤ) - A.deficiency ∧
  A.deficiency ≥ 2 * A.p 2 ∧
  A.X'.card + A.p 2 ≤ 2 * n - 2

instance : Decidable A.NotesFacts := by unfold NotesFacts; infer_instance

end Pca.Arrangement
