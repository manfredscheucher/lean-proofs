/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Counting notions on an arrangement

Cells, corners, sides, `k`-cells, digons, triangles, `p k`, `t x`, `X'`, deficiency, excess,
neighbors, diamond and trigophobic segments, and `t_C`. See `doc/pca/model.md`.
-/
import Pca.Model

open Equiv Finset

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

/-! ## Incidences -/

/-- The set `X` of crossings. -/
def X : Finset A.Crossing := univ

/-- The two curves through a crossing. -/
def Crossing.curves (x : A.Crossing) : Finset (Fin n) := crossingCurves A.σ A.curve x

/-- The curve of a segment (as a finset of labels; it is a singleton by `curve_α`). -/
def Segment.curves (s : A.Segment) : Finset (Fin n) := s.darts.image A.curve

/-- The corners of a cell: the crossings on its boundary. -/
def Cell.corners (f : A.Cell) : Finset A.Crossing := f.darts.image A.crossingOf

/-- The sides of a cell: the segments on its boundary. -/
def Cell.sides (f : A.Cell) : Finset A.Segment := f.darts.image A.segmentOf

/-- A `k`-cell is a cell whose face orbit has `k` darts (`Orbit.size`). For an arrangement on the
sphere this is the number of corners and the number of sides. Proved for `k = 2, 3`
(`Pca/Excess.lean`: `Digon.card_corners`, `Triangle.card_corners`, ...), for general `k` only
checked on the test instances. -/
def IsKCell (k : ℕ) (f : A.Cell) : Prop := f.size = k

instance (k : ℕ) (f : A.Cell) : Decidable (A.IsKCell k f) :=
  inferInstanceAs (Decidable (f.size = k))

/-- A digon is a 2-cell. -/
def IsDigon (f : A.Cell) : Prop := A.IsKCell 2 f
/-- A triangle is a 3-cell. -/
def IsTriangle (f : A.Cell) : Prop := A.IsKCell 3 f

instance (f : A.Cell) : Decidable (A.IsDigon f) := inferInstanceAs (Decidable (f.size = 2))
instance (f : A.Cell) : Decidable (A.IsTriangle f) := inferInstanceAs (Decidable (f.size = 3))

/-- `p k`: the number of `k`-cells. -/
def p (k : ℕ) : ℕ := (univ.filter (A.IsKCell k)).card

/-- The set of triangles. -/
def triangles : Finset A.Cell := univ.filter A.IsTriangle

/-- `t x`: the number of triangles incident to the crossing `x`. A cell has `x` as a corner iff
it is the cell of one of the four darts at `x`, so this is the number of distinct triangles
among the cells of the darts at `x`. (`tCorners` is the same count via `Cell.corners`; they
agree by definition of corners, proved: `t_eq_tCorners`.) -/
def t (x : A.Crossing) : ℕ :=
  ((x.darts.filter (fun d => A.IsTriangle (A.cellOf d))).image A.cellOf).card

/-- `X'`: the crossings incident to three triangles. -/
def X' : Finset A.Crossing := univ.filter (fun x => A.t x = 3)

/-- The deficiency `def = ∑_{x : t x ≤ 1} (2 - t x)`. -/
def deficiency : ℕ := ∑ x ∈ univ.filter (fun x => A.t x ≤ 1), (2 - A.t x)

/-- The excess `e = 3 p_3 - 2 |X|`. -/
def excess : ℤ := 3 * (A.p 3 : ℤ) - 2 * (A.X.card : ℤ)

/-- Two crossings are neighbors if a segment joins them. -/
def Neighbors (x y : A.Crossing) : Prop := ∃ d ∈ x.darts, A.crossingOf (A.α d) = y

instance (x y : A.Crossing) : Decidable (A.Neighbors x y) :=
  inferInstanceAs (Decidable (∃ d ∈ x.darts, A.crossingOf (A.α d) = y))

/-- The two cells incident to a segment: for a dart `d` of the segment, `cellOf d` is the cell
on its right and `cellOf (α d)` the cell on its left. -/
def Segment.cells (s : A.Segment) : Finset A.Cell := s.darts.image A.cellOf

/-- A diamond segment: both cells incident to it are triangles. -/
def IsDiamond (s : A.Segment) : Prop := ∀ d ∈ s.darts, A.IsTriangle (A.cellOf d)

/-- A trigophobic segment: no cell incident to it is a triangle. -/
def IsTrigophobic (s : A.Segment) : Prop := ∀ d ∈ s.darts, ¬ A.IsTriangle (A.cellOf d)

instance (s : A.Segment) : Decidable (A.IsDiamond s) :=
  inferInstanceAs (Decidable (∀ d ∈ s.darts, A.IsTriangle (A.cellOf d)))
instance (s : A.Segment) : Decidable (A.IsTrigophobic s) :=
  inferInstanceAs (Decidable (∀ d ∈ s.darts, ¬ A.IsTriangle (A.cellOf d)))

/-- `δ`: the number of diamond segments. -/
def numDiamond : ℕ := (univ.filter A.IsDiamond).card
/-- `φ` (the number, not the face permutation): the number of trigophobic segments. -/
def numTrigophobic : ℕ := (univ.filter A.IsTrigophobic).card

/-! ## Per pseudocircle -/

/-- The crossings on the pseudocircle `C`. -/
def crossingsOn (C : Fin n) : Finset A.Crossing := univ.filter (fun x => C ∈ Crossing.curves A x)

/-- The segments of the pseudocircle `C`. -/
def segmentsOn (C : Fin n) : Finset A.Segment := univ.filter (fun s => C ∈ Segment.curves A s)

/-- `t_C`: the number of triangles with a side on `C`. -/
def tC (C : Fin n) : ℕ := (A.triangles.filter (fun f => ∃ d ∈ f.darts, A.curve d = C)).card

/-- `δ_C`: the number of diamond segments on `C`. -/
def numDiamondOn (C : Fin n) : ℕ := ((A.segmentsOn C).filter A.IsDiamond).card
/-- `φ_C`: the number of trigophobic segments on `C`. -/
def numTrigophobicOn (C : Fin n) : ℕ := ((A.segmentsOn C).filter A.IsTrigophobic).card

/-! ## Cells at a crossing -/

/-- `t x` via corners: the number of triangles having `x` as a corner. -/
def tCorners (x : A.Crossing) : ℕ := (A.triangles.filter (fun f => x ∈ Cell.corners A f)).card

/-- The number of angles at `x` that lie in a triangle (the four darts of `x` are the four
angles; the angle of `d` lies in `cellOf d`). Equal to `t x` because a triangle visits a
crossing at most once (proved: `t_eq_tAngles`). -/
def tAngles (x : A.Crossing) : ℕ := (x.darts.filter (fun d => A.IsTriangle (A.cellOf d))).card

end Pca.Arrangement
