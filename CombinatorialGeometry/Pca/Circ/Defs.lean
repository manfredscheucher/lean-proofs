/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: the core definitions (`doc/pca/circ.md`, decisions C-D1 ff.)

Source: S. Felsner, M. Scheucher, *Arrangements of Pseudocircles: On Circularizability*,
https://arxiv.org/abs/1712.02149 (v6). Section 1: "An arrangement of pseudocircles is
circularizable if there is an isomorphic arrangement of circles"; section 2: circles on the unit
sphere `S` are the intersections `E ∩ S` of planes `E`, and the arrangement of planes `ℰ(𝒞)`.

* `IsCircleRep A u h pt sgn` (C-D1): the planes `E_i = {x | ⟨u_i, x⟩ = h_i}` meet `S` in circles
  (`h_i² < ⟨u_i, u_i⟩`); `pt` is a bijection from the crossings of `A` to the intersection points
  of the circles (each crossing on the circles of its two curves, injective, every intersection
  point hit); `sgn d = ±1` says whether the dart `d` runs along its circle in the positive
  direction (counter-clockwise around `u_i`, tangent `u_i ⨯₃ p`) or the negative one. Order: the
  crossing of `α d` is the next crossing after the crossing of `d` on the circle in direction
  `sgn d` (`next`). Orientation: `σ` is the counter-clockwise rotation seen from outside the
  sphere (`rot`).
* `CircleRep A`, `GreatRep A` (all `h_i = 0`), `Circularizable A`.
* `IsStretchable A` (C-D3): `A` is great (the double cover of a projective pseudoline
  arrangement) and has a representation by great circles, i.e. by planes through `0`, i.e. by
  lines of the projective plane.
* `KruppPair`, `IsKrupp`, `IsNonKrupp`: the subarrangement of three curves is a Krupp
  (FROS characterisation, as `Arrangement.IsGreat`: each pair is separated by the third).
-/
import Pca.Great.Basic
import Pca.Circ.Vec

open Equiv Finset Matrix

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

/-- The tangent vector of the dart `d` at its crossing (given the point `p` of the crossing). -/
def tangent (u : V) (s : ℝ) (p : V) : V := s • (u ⨯₃ p)

/-- **Circle representation** (C-D1): planes `(u, h)`, crossing points `pt` and dart directions
`sgn` realize the arrangement `A` on the unit sphere. -/
structure IsCircleRep (A : Arrangement n D) (u : Fin n → V) (h : Fin n → ℝ)
    (pt : A.Crossing → V) (sgn : D → ℝ) : Prop where
  /-- every plane meets the sphere in a circle -/
  isCircle : ∀ i, h i ^ 2 < u i ⬝ᵥ u i
  /-- the crossing points are on the sphere -/
  on_sphere : ∀ x, pt x ⬝ᵥ pt x = 1
  /-- the point of a crossing lies on the circles of its curves -/
  on_plane : ∀ d, u (A.curve d) ⬝ᵥ pt (A.crossingOf d) = h (A.curve d)
  /-- distinct crossings have distinct points -/
  inj : Function.Injective pt
  /-- every intersection point of two circles is the point of a crossing -/
  surj : ∀ (i j : Fin n) (p : V), i ≠ j → p ⬝ᵥ p = 1 → u i ⬝ᵥ p = h i → u j ⬝ᵥ p = h j →
    ∃ x, pt x = p
  /-- directions are `±1` -/
  sgn_pm : ∀ d, sgn d = 1 ∨ sgn d = -1
  sgn_α : ∀ d, sgn (A.α d) = - sgn d
  sgn_σσ : ∀ d, sgn (A.σ (A.σ d)) = - sgn d
  /-- cyclic order: the crossing of `α d` is the next crossing on the circle of `d` in direction
  `sgn d`, i.e. every other crossing `z` on that circle comes after it -/
  next : ∀ (d : D) (z : A.Crossing), A.curve d ∈ Arrangement.Crossing.curves A z →
    z ≠ A.crossingOf d → z ≠ A.crossingOf (A.α d) →
    0 < sgn d * orient (u (A.curve d)) (pt (A.crossingOf d)) (pt (A.crossingOf (A.α d))) (pt z)
  /-- orientation: `σ d` is the counter-clockwise successor of `d` seen from outside -/
  rot : ∀ d, 0 < det3 (tangent (u (A.curve d)) (sgn d) (pt (A.crossingOf d)))
    (tangent (u (A.curve (A.σ d))) (sgn (A.σ d)) (pt (A.crossingOf d))) (pt (A.crossingOf d))

/-- A **circle representation** of `A` (C-D1). -/
structure CircleRep (A : Arrangement n D) where
  u : Fin n → V
  h : Fin n → ℝ
  pt : A.Crossing → V
  sgn : D → ℝ
  isRep : IsCircleRep A u h pt sgn

/-- A **great-circle representation**: a circle representation by planes through the origin. -/
structure GreatRep (A : Arrangement n D) extends CircleRep A where
  h_eq_zero : ∀ i, h i = 0

/-- `A` is **circularizable**: it has a circle representation. -/
def Circularizable (A : Arrangement n D) : Prop := Nonempty (CircleRep A)

/-- **Stretchable** (C-D3): `A` is an arrangement of great-pseudocircles (the double cover of an
arrangement of pseudolines in the projective plane) with a great-circle representation (planes
through `0`, i.e. lines in the projective plane). -/
def IsStretchable (A : Arrangement n D) : Prop := A.IsGreat ∧ Nonempty (GreatRep A)

/-! ## Krupp triples -/

/-- The two crossings of `a` and `b` lie on different sides of `c`. -/
def KruppPair (A : Arrangement n D) (a b c : Fin n) : Prop :=
  ∀ s : A.Cell → ZMod 2, A.IsSide c s →
    ∀ x y : A.Crossing, x ≠ y → Arrangement.Crossing.curves A x = {a, b} →
      Arrangement.Crossing.curves A y = {a, b} →
      ∀ d ∈ x.darts, ∀ e ∈ y.darts, s (A.cellOf d) ≠ s (A.cellOf e)

/-- The three curves `a, b, c` form a **Krupp**: every pair is separated by the third. -/
def IsKrupp (A : Arrangement n D) (a b c : Fin n) : Prop :=
  KruppPair A a b c ∧ KruppPair A b c a ∧ KruppPair A c a b

/-- The three (pairwise crossing) curves `a, b, c` form a **NonKrupp**. -/
def IsNonKrupp (A : Arrangement n D) (a b c : Fin n) : Prop := ¬ IsKrupp A a b c

theorem isGreat_iff (A : Arrangement n D) :
    A.IsGreat ↔ ∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c → IsKrupp A a b c := by
  constructor
  · intro hA a b c hab hac hbc
    exact ⟨fun s hs => hA a b c hab hac hbc s hs, fun s hs => hA b c a hbc hab.symm hac.symm s hs,
      fun s hs => hA c a b hac.symm hbc.symm hab s hs⟩
  · intro h a b c hab hac hbc s hs
    exact (h a b c hab hac hbc).1 s hs

/-- The planes of `a, b, c` meet in a single point, inside the sphere (Fact 1, right side). -/
def MeetInside (u : Fin n → V) (h : Fin n → ℝ) (a b c : Fin n) : Prop :=
  det3 (u a) (u b) (u c) ≠ 0 ∧
    ∃ p : V, u a ⬝ᵥ p = h a ∧ u b ⬝ᵥ p = h b ∧ u c ⬝ᵥ p = h c ∧ p ⬝ᵥ p < 1

end Pca.Circ
