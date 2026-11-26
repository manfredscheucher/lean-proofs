/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Great-pseudocircle arrangements: the core definitions (milestone 9, track P)

Spec and decisions: `doc/pca/flipgraph.md` (Track P). Source: Alves Radtke, Felsner, Obenaus, Roch,
Scheucher, *Flip Graph Connectivity for Arrangements of Pseudolines and Pseudocircles* (FROS),
https://arxiv.org/abs/2310.19711.

* `Arrangement.IsGreat` (P1): FROS, introduction: "great-pseudocircle arrangements ... are
  intersecting arrangements with the property that for any three pseudocircles `C_i`, `C_j`, `C_k`
  the two intersection points of `C_i` and `C_j` are on different sides of `C_k`" (section 2
  phrases it as "every triple of pseudocircles from the arrangement induces a Krupp
  subarrangement"). Intersecting is axiom 6 of the model.
* `Arrangement.IsAntipodalTri`, `Arrangement.AFlip` (P2): FROS, footnote in the introduction: "For
  great-pseudocircle arrangements, a flip must consist of two simultaneous triangle flips applied
  to a pair of 'antipodal' triangles". Here: flip a triangle and its antipodal
  triangle (the triangle on the same three curves at the other three crossings) simultaneously.
* `Great.Iso` (decision D3 of `doc/pca/flipgraph.md`): a dart bijection commuting with `σ` and `α`,
  compatible with a permutation of the curves (orientation preserving, FROS section 2).
* `Great.IsDeletion`, `Great.Passes` (P4): `A'` with `n + 1` curves is `A` plus the new curve
  `Fin.last n`; `ι` embeds the darts of `A` (the darts at crossings not on the new curve), and
  removing the new curve joins the pieces of a segment (as `Pca.Sweep.SConf.IsRemoval`). The new
  curve passes through a cell `f` of `A` if it crosses a side of `f`.
-/
import Pca.Flip
import Pca.Side

open Equiv Finset

namespace Pca

namespace Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

/-- **Great-pseudocircle arrangement** (FROS, introduction): for any three distinct curves `a`,
`b`, `c`, the two crossings of `a` and `b` lie on different sides of `c`. A crossing `x` not on `c`
lies on the side of the cells at `x` (all four darts at `x` have their cell on the same side). -/
def IsGreat : Prop :=
  ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → ∀ s : A.Cell → ZMod 2, A.IsSide c s →
    ∀ x y : A.Crossing, x ≠ y → Crossing.curves A x = {a, b} → Crossing.curves A y = {a, b} →
      ∀ d ∈ x.darts, ∀ e ∈ y.darts, s (A.cellOf d) ≠ s (A.cellOf e)

/-- The curves of a cell (the curves of its sides). -/
def Cell.curves (f : A.Cell) : Finset (Fin n) := f.darts.image A.curve

/-- `T'` is the **antipodal triangle** of the triangle `T`: a triangle whose corners are the other
crossings of the pairs of curves of `T` (the crossings on two curves of `T` that are not corners of
`T`). -/
def IsAntipodalTri (T T' : A.Cell) : Prop :=
  A.IsTriangle T ∧ A.IsTriangle T' ∧
    Cell.corners A T' =
      univ.filter (fun x => Crossing.curves A x ⊆ Cell.curves A T ∧ x ∉ Cell.corners A T)

/-- One **antipodal flip** `A → B` (same darts): flip the triangle `cellOf d` and then its antipodal
triangle `cellOf e` (which must still be a triangle after the first flip). -/
def AFlip (B : Arrangement n D) : Prop :=
  ∃ (d e : D) (hT : A.IsTriangle (A.cellOf d)),
    A.IsAntipodalTri (A.cellOf d) (A.cellOf e) ∧
    ∃ hT' : (A.flip d hT).IsTriangle ((A.flip d hT).cellOf e), B = (A.flip d hT).flip e hT'

/-- The side of a crossing `x` with respect to a side function `s` (of a curve not through `x`):
the value of `s` on the cell of a dart at `x` (chosen; all four agree, `crossSide_eq`). -/
noncomputable def crossSide (s : A.Cell → ZMod 2) (x : A.Crossing) : ZMod 2 :=
  s (A.cellOf (Quotient.out (s := Perm.SameCycle.setoid A.σ) x))

end Arrangement

namespace Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

/-- **Isomorphism** of arrangements (decision D3): a dart bijection commuting with `σ` and `α` and
mapping curves by a permutation of the labels. It preserves the orientation (`σ` is the
counter-clockwise rotation), as in FROS section 2. -/
structure Iso {D' : Type*} [Fintype D'] [DecidableEq D'] (A : Arrangement n D)
    (B : Arrangement n D') where
  /-- the dart bijection -/
  toEquiv : D ≃ D'
  /-- the induced bijection of the curves -/
  curveEquiv : Perm (Fin n)
  map_σ : ∀ d, toEquiv (A.σ d) = B.σ (toEquiv d)
  map_α : ∀ d, toEquiv (A.α d) = B.α (toEquiv d)
  map_curve : ∀ d, B.curve (toEquiv d) = curveEquiv (A.curve d)

/-- `A'` (with `n + 1` curves) is `A` with the new curve `Fin.last n` added; `ι` embeds the darts
of `A`. Equivalently: deleting `Fin.last n` from `A'` gives `A` (the darts at crossings on the new
curve disappear, the pieces of a segment are joined; the same specification as
`Pca.Sweep.SConf.IsRemoval`, which determines the result up to isomorphism). -/
structure IsDeletion {D' : Type*} [Fintype D'] [DecidableEq D'] (A' : Arrangement (n + 1) D')
    (A : Arrangement n D) (ι : D → D') : Prop where
  inj : Function.Injective ι
  /-- the embedded darts are exactly the darts at crossings not on the new curve -/
  range : ∀ y, (∃ d, ι d = y) ↔ Fin.last n ∉ Arrangement.Crossing.curves A' (A'.crossingOf y)
  curve : ∀ d, A'.curve (ι d) = Fin.castSucc (A.curve d)
  σ : ∀ d, ι (A.σ d) = A'.σ (ι d)
  /-- a segment of `A` is a run of segments of `A'` through crossings with the new curve -/
  α : ∀ d, ∃ k : ℕ,
    (∀ i < k, Fin.last n ∈
      Arrangement.Crossing.curves A' (A'.crossingOf (A'.α ((A'.straight ^ i) (ι d))))) ∧
    ι (A.α d) = A'.α ((A'.straight ^ k) (ι d))

/-- The new curve of `A'` **passes through** the cell `f` of `A`: it crosses a side of `f` (the
first piece of the segment of some dart of `f` ends at a crossing with the new curve). -/
def Passes {D' : Type*} [Fintype D'] [DecidableEq D'] (A' : Arrangement (n + 1) D')
    {A : Arrangement n D} (ι : D → D') (f : A.Cell) : Prop :=
  ∃ d ∈ f.darts, Fin.last n ∈ Arrangement.Crossing.curves A' (A'.crossingOf (A'.α (ι d)))

end Great

end Pca
