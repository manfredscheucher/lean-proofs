/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH sweep in graph language: the notions of SH section 2 (definitions only, no `sorry`)

Every notion of SH pp. 313-318 as a property of the cells and darts of a sweep configuration
(`Pca/Sweep/Conf.lean`). Table in `doc/pca/sweep.md`, section 4.

Orientation: a **sweep dart** is a dart of `S` with the upper side on its left (SH p. 313: `c` is
oriented left to right, "above" is the counterclockwise side). The segment of a sweep dart `d`
from vertex `i` to vertex `i + 1` is SH's edge `[i, i + 1]`; the cell above it is
`upperCell d = cellOf (α d)` (the cell to the right of `α d`).
-/
import Pca.Sweep.Conf

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

/-! ## Derived permutations and orbits (as in `Pca/Model.lean`) -/

/-- Face permutation `d ↦ σ (α d)`. -/
def φ : Perm D := Γ.σ * Γ.α
/-- Go straight: `d ↦ σ (σ (α d))`. -/
def straight : Perm D := straightPerm Γ.σ Γ.α

abbrev Crossing := Orbit Γ.σ
abbrev Segment := Orbit Γ.α
abbrev Cell := Orbit Γ.φ

def crossingOf (d : D) : Γ.Crossing := Orbit.mk Γ.σ d
def segmentOf (d : D) : Γ.Segment := Orbit.mk Γ.α d
def cellOf (d : D) : Γ.Cell := Orbit.mk Γ.φ d

/-- The curves through a crossing. -/
def curves (x : Γ.Crossing) : Finset (Fin n) := crossingCurves Γ.σ Γ.curve x

/-! ## Above and below the sweep -/

/-- The cell `f` lies above the sweep. -/
def Up (f : Γ.Cell) : Prop := Γ.side f = 1

instance (f : Γ.Cell) : Decidable (Γ.Up f) := inferInstanceAs (Decidable (Γ.side f = 1))

/-- `d` is a **sweep dart**: a dart of `S` with the upper side on its left. -/
def IsSweepDart (d : D) : Prop := Γ.curve d = Γ.S ∧ Γ.Up (Γ.cellOf (Γ.α d))

/-- The cell above the segment of the sweep dart `d`. -/
def upperCell (d : D) : Γ.Cell := Γ.cellOf (Γ.α d)

/-- `d` is a dart of a curve other than `S` lying above the sweep. -/
def Above (d : D) : Prop := Γ.curve d ≠ Γ.S ∧ Γ.Up (Γ.cellOf d)

/-- `x` is a crossing with the sweep. -/
def OnSweep (x : Γ.Crossing) : Prop := Γ.S ∈ Γ.curves x

/-- The darts of the ∞-arc: `straight^i infStart`, `i ≤ infLen`. -/
def infArc : Finset D := arcOf Γ.σ Γ.α Γ.infStart Γ.infLen

/-- `x` is a crossing strictly inside the ∞-arc (a point where a ray reaches `∞`; not a vertex of
SH's graph `G`): the end of `straight^i infStart` for some `i < infLen`. -/
def IsInfVertex (x : Γ.Crossing) : Prop :=
  ∃ z ∈ Γ.infStart, ∃ i < Γ.infLen, Γ.crossingOf (Γ.α ((Γ.straight ^ i) z)) = x

/-- `x` is a **vertex on the sweep** (SH p. 314: "vertices `1, …, m` on `c`"). -/
def IsFinVertex (x : Γ.Crossing) : Prop := Γ.OnSweep x ∧ ¬ Γ.IsInfVertex x

/-- `x` is a vertex above the sweep (a crossing of two curves other than `S`, above `S`). -/
def IsAboveVertex (x : Γ.Crossing) : Prop := ¬ Γ.OnSweep x ∧ ∃ d ∈ x.darts, Γ.Above d

/-- `x` lies on the curve `γ`. -/
def OnCurve (γ : Fin n) (x : Γ.Crossing) : Prop := γ ∈ Γ.curves x

/-- The segment of the sweep dart `d` is a finite edge `[i, i + 1]` of `c` (not in the ∞-arc). -/
def IsFinSeg (d : D) : Prop := Γ.IsSweepDart d ∧ d ∉ Γ.infArc

/-! ## Curves (SH p. 314, p. 322) -/

/-- `γ` is a curve of SH's arrangement: it has a part above the sweep. Curves that lie entirely
below `S` are not seen by the sweep (SH Lemma 3.5 cuts them away). -/
def Present (γ : Fin n) : Prop := γ ≠ Γ.S ∧ ∃ d, Γ.curve d = γ ∧ Γ.Above d

/-- `γ` intersects the sweep (at a vertex on the sweep, not at `∞`). -/
def MeetsSweep (γ : Fin n) : Prop := ∃ x, Γ.IsFinVertex x ∧ Γ.OnCurve γ x

open Classical in
/-- Number of vertices on the sweep of `γ`. -/
noncomputable def numSweepHits (γ : Fin n) : ℕ :=
  (univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve γ x)).card

/-- `γ` is a **loop** (SH p. 322): it intersects the sweep twice (its part above `S` is one arc,
`Pca/Sweep/Jordan.lean`, so it is "connected in the above component"). -/
def IsLoop (γ : Fin n) : Prop := Γ.numSweepHits γ = 2

/-- `γ` is a **ray** (SH p. 314, "an edge `⟨u, ∞⟩` is an infinite ray"): one vertex on the sweep,
the other end of its upper arc at `∞`. -/
def IsRay (γ : Fin n) : Prop :=
  Γ.numSweepHits γ = 1 ∧ ∃ x, Γ.IsInfVertex x ∧ Γ.OnCurve γ x

open Classical in
/-- Number of crossings of `γ` and `γ'` above the sweep. -/
noncomputable def crossAbove (γ γ' : Fin n) : ℕ :=
  (univ.filter (fun x : Γ.Crossing => Γ.IsAboveVertex x ∧ Γ.curves x = {γ, γ'})).card

/-! ## Positions along the sweep (SH p. 314) -/

open Classical in
/-- The position of a vertex along the sweep: `pos x = k` for the `k`-th vertex (`1, …, m`),
counted along the sweep darts from the end of the ∞-arc (the end of `straight^infLen infStart` is
vertex `1`). Crossings not on the sweep get junk values; the empty map gets `0`. -/
noncomputable def pos (x : Γ.Crossing) : ℕ :=
  Γ.infStart.elim 0 fun z =>
    1 + (orbitList Γ.straight ((Γ.straight ^ (Γ.infLen + 1)) z)).findIdx
      (fun d => decide (Γ.crossingOf d = x))

open Classical in
/-- The positions of the vertices on the sweep of `γ`. -/
noncomputable def sweepEnds (γ : Fin n) : Finset ℕ :=
  (univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve γ x)).image Γ.pos

/-- `γ` is a loop with endpoints `i < j`. -/
def LoopEnds (γ : Fin n) (i j : ℕ) : Prop := Γ.IsLoop γ ∧ i < j ∧ Γ.sweepEnds γ = {i, j}

/-- SH p. 323: the loop `γ` is **inside** the loop `γ'` (`i' < i < j < j'`). -/
def Inside (γ γ' : Fin n) : Prop :=
  ∃ i j i' j', Γ.LoopEnds γ i j ∧ Γ.LoopEnds γ' i' j' ∧ i' < i ∧ j < j'

/-! ## Humps and triangles (SH pp. 314-315) -/

/-- A **hump** `⟨i, j⟩`: a segment of a curve, above the sweep, with both ends vertices on the
sweep (`a` points from `i` to `j`). -/
def IsHump (a : D) : Prop :=
  Γ.Above a ∧ Γ.IsFinVertex (Γ.crossingOf a) ∧ Γ.IsFinVertex (Γ.crossingOf (Γ.α a))

/-- A **triangle** `Δ(k, v, l)`: segments `⟨k, v⟩` (dart `a`) and `⟨l, v⟩` (dart `b`) above the
sweep, on two distinct curves, `k ≠ l` vertices on the sweep, `v` a vertex above the sweep. -/
def IsTri (a b : D) : Prop :=
  Γ.Above a ∧ Γ.Above b ∧ Γ.IsFinVertex (Γ.crossingOf a) ∧ Γ.IsFinVertex (Γ.crossingOf b) ∧
    Γ.crossingOf a ≠ Γ.crossingOf b ∧ Γ.crossingOf (Γ.α a) = Γ.crossingOf (Γ.α b) ∧
    Γ.IsAboveVertex (Γ.crossingOf (Γ.α a)) ∧ Γ.curve a ≠ Γ.curve b

/-- An **empty hump** above the finite edge of `d`: the cell above it is a digon. ("Empty: it
contains no other curves" is "it is a cell"; in a connected map nothing can hide inside.) -/
def EmptyHumpAt (d : D) : Prop := Γ.IsFinSeg d ∧ (Γ.upperCell d).size = 2

/-- An **empty triangle** `Δ(i, v, i + 1)` above the finite edge of `d`: the cell above it is a
triangle. -/
def EmptyTriAt (d : D) : Prop := Γ.IsFinSeg d ∧ (Γ.upperCell d).size = 3

/-- The apex `v` of the empty triangle at `d` (the darts of the cell are `α d` from `i + 1` to
`i`, `σ d` from `i` to `v`, and `φ (σ d)` from `v` to `i + 1`). -/
def apex (d : D) : Γ.Crossing := Γ.crossingOf (Γ.φ (Γ.σ d))

/-! ## Operations and the minimal counterexample (SH pp. 315-318) -/

/-- **Taking a loop** applies (SH p. 315, operation 1, `k = 2`): a curve that does not intersect
the sweep has a segment on a cell above an edge of the sweep ("visible from `c`", p. 314). In the
dart model the operation itself is a **digon create** (`Pca/Sweep/Moves.lean`). -/
def CanTakeLoop : Prop :=
  ∃ d e : D, Γ.IsSweepDart d ∧ e ∈ (Γ.upperCell d).darts ∧ Γ.curve e ≠ Γ.S ∧
    ¬ Γ.MeetsSweep (Γ.curve e)

/-- The sweep **can make progress** (SH p. 316) with the three operations of Lemma 3.2: passing
an empty hump (digon collapse), passing an empty triangle (triangle flip), taking a loop (digon
create). -/
def Progress : Prop := (∃ d, Γ.EmptyHumpAt d) ∨ (∃ d, Γ.EmptyTriAt d) ∨ Γ.CanTakeLoop

/-- The sweep is **finished** (SH p. 316: "there are no curves above the sweep or the only curves
above the sweep are nonintersecting rays"). -/
def Terminal : Prop := (∀ x, ¬ Γ.IsAboveVertex x) ∧ ∀ γ, Γ.Present γ → Γ.IsRay γ

/-- The sweep is **stuck** (a counterexample): not finished and no operation applies. -/
def Stuck : Prop := ¬ Γ.Terminal ∧ ¬ Γ.Progress

open Classical in
/-- `|V|` of SH p. 318: the vertices on and above the sweep. -/
noncomputable def numVertices : ℕ :=
  (univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∨ Γ.IsAboveVertex x)).card

open Classical in
/-- `n` of SH p. 318: the number of curves (with a part above the sweep). -/
noncomputable def numCurves : ℕ := (univ.filter Γ.Present).card

/-- The size order of SH p. 318: `(|V|, n)` lexicographically. -/
def SizeLT {n₁ n₂ : ℕ} {D₁ D₂ : Type*} [Fintype D₁] [DecidableEq D₁] [Fintype D₂]
    [DecidableEq D₂] (Γ₁ : SConf n₁ D₁) (Γ₂ : SConf n₂ D₂) : Prop :=
  Γ₁.numVertices < Γ₂.numVertices ∨
    (Γ₁.numVertices = Γ₂.numVertices ∧ Γ₁.numCurves < Γ₂.numCurves)

/-- A **minimal counterexample** (SH p. 318): stuck, and every smaller configuration is not
stuck. -/
def MinCE : Prop :=
  Γ.Stuck ∧ ∀ (n' : ℕ) (K : Conf.{u} n'), SizeLT K.Γ Γ → ¬ K.Γ.Stuck

end SConf

end Pca.Sweep
