/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (FROS, Track F): marked arrangements, interiors, flips, isomorphism

Source: Alves Radtke, Felsner, Obenaus, Roch, Scheucher, *Flip Graph Connectivity for Arrangements
of Pseudolines and Pseudocircles* (cited as FROS), section 2. Plan and decisions:
`doc/pca/flipgraph.md` (Track F).

FROS work in the plane. An arrangement of pseudocircles in the plane is an arrangement on the
sphere (`Pca/Model.lean`) together with the cell that contains the point at infinity, the
**unbounded cell** (decision D2). In graph language:

* `Marked n D`: an arrangement with a marked cell `z`.
* `Marked.Inside C f`: the cell `f` lies in the interior of the pseudocircle `C`, i.e. on the side
  of `C` not containing `z` (FROS: "a pseudocircle `C` partitions the plane into a bounded region,
  the interior, and an unbounded region, the exterior").
* `FlipStep M M'`: `M'` is obtained from `M` by flipping a triangle (`Arrangement.flip`) other than
  the marked cell; the marked cell is carried along by the cell bijection of the flip (FROS: only
  bounded triangles are flipped).
* `IsIso M M'` (decision D3, FROS section 2: "a bijection between the pseudocircles that induces
  incidence preserving bijections of vertices, edges, and cells, while also keeping the
  ccw-orientations"): a bijection of the darts commuting with `σ` (rotation, so orientation is
  kept) and `α`, compatible with a permutation of the curve labels, mapping the marked cell to the
  marked cell.
* `Cylindrical M`: some cell lies in the interior of every pseudocircle (FROS: "a point which
  belongs to the bounded interior of each pseudocircle").
-/
import Pca.Flip
import Pca.Side

open Equiv Finset

namespace Pca.FlipGraph

universe u v

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- A **marked arrangement**: an arrangement of pseudocircles on the sphere with a marked cell, the
unbounded cell of the arrangement in the plane (FROS works in the plane; decision D2). -/
structure Marked (n : ℕ) (D : Type u) [Fintype D] [DecidableEq D] where
  /-- the arrangement (on the sphere) -/
  A : Arrangement n D
  /-- the marked cell (the unbounded cell) -/
  z : A.Cell

namespace Marked

variable (M : Marked n D)

/-- The cell `f` lies in the **interior** of the pseudocircle `C`: it lies on the side of `C`
that does not contain the marked cell. Side functions of `C` are unique up to swapping the two
sides (`IsSide.eq_or_eq_add_one`), so this does not depend on the choice of `s`. -/
def Inside (C : Fin n) (f : M.A.Cell) : Prop :=
  ∀ s : M.A.Cell → ZMod 2, M.A.IsSide C s → s f ≠ s M.z

/-- The arrangement is **cylindrical**: some cell (a *center*) lies in the interior of every
pseudocircle. -/
def Cylindrical : Prop := ∃ p : M.A.Cell, ∀ C : Fin n, M.Inside C p

/-- `C` has a side on the cell `f` (a dart of `f` lies on `C`). -/
def HasSideOn (C : Fin n) (f : M.A.Cell) : Prop := ∃ y ∈ f.darts, M.A.curve y = C

end Marked

/-! ## Flips -/

/-- **One step of the triangle flip graph** (in the plane): `M'` is obtained from `M` by flipping
a triangle `T` that is not the marked cell; the marked cell of `M'` is the image of the marked
cell of `M` under the cell bijection of the flip (`flipCellEquiv`). -/
def FlipStep (M M' : Marked n D) : Prop :=
  ∃ (d : D) (hT : M.A.IsTriangle (M.A.cellOf d)), M.A.cellOf d ≠ M.z ∧
    M' = ⟨M.A.flip d hT, Arrangement.flipCellEquiv hT M.z⟩

/-- Reachability by a finite sequence of flips. -/
def Reach : Marked n D → Marked n D → Prop := Relation.ReflTransGen FlipStep

/-- A flip between cylindrical arrangements (an edge of the flip graph of cylindrical
arrangements, FROS Theorem 4). -/
def CylStep (M M' : Marked n D) : Prop := FlipStep M M' ∧ M.Cylindrical ∧ M'.Cylindrical

/-- Reachability inside the class of cylindrical arrangements. -/
def CylReach : Marked n D → Marked n D → Prop := Relation.ReflTransGen CylStep

/-! ## Isomorphism -/

/-- An **isomorphism** of marked arrangements (decision D3): a bijection of the darts commuting
with the rotation `σ` (this keeps the orientation) and with `α`, compatible with a permutation `π`
of the curve labels, that maps the marked cell to the marked cell. It induces incidence preserving
bijections of the crossings (`σ`-orbits), segments (`α`-orbits) and cells (`φ`-orbits). -/
structure Iso {D' : Type v} [Fintype D'] [DecidableEq D'] (M : Marked n D) (M' : Marked n D')
    where
  e : D ≃ D'
  π : Equiv.Perm (Fin n)
  map_σ : ∀ d, e (M.A.σ d) = M'.A.σ (e d)
  map_α : ∀ d, e (M.A.α d) = M'.A.α (e d)
  map_curve : ∀ d, M'.A.curve (e d) = π (M.A.curve d)
  map_z : ∀ d, M.A.cellOf d = M.z → M'.A.cellOf (e d) = M'.z

/-- `M` and `M'` are isomorphic. -/
def IsIso {D' : Type v} [Fintype D'] [DecidableEq D'] (M : Marked n D) (M' : Marked n D') :
    Prop := Nonempty (Iso M M')

/-! ## The sphere version (no marked cell) -/

/-- A triangle flip on the sphere (any triangle may be flipped). -/
def SphereStep (A A' : Arrangement n D) : Prop :=
  ∃ (d : D) (hT : A.IsTriangle (A.cellOf d)), A' = A.flip d hT

/-- An isomorphism of arrangements on the sphere (no marked cell; orientation kept). -/
def SphereIso {D' : Type v} [Fintype D'] [DecidableEq D'] (A : Arrangement n D)
    (A' : Arrangement n D') : Prop :=
  ∃ (e : D ≃ D') (π : Equiv.Perm (Fin n)), (∀ d, e (A.σ d) = A'.σ (e d)) ∧
    (∀ d, e (A.α d) = A'.α (e d)) ∧ ∀ d, A'.curve (e d) = π (A.curve d)

end Pca.FlipGraph
