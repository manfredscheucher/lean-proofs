# PcaCirc: circularizability

Library `PcaCirc`, root `CombinatorialGeometry/PcaCirc.lean`, files `Pca/Circ/`. In progress: the
corollaries and the axiom file are partly not committed yet.

## Setting

An arrangement in the dart model (`model.md`) is circularizable if it can be drawn with circles on
the sphere. In Lean (`Defs.lean`, namespace `Pca.Circ`):

* `IsCircleRep A u h pt sgn`: planes `⟨u_i, x⟩ = h_i` in `ℝ³` that meet the unit sphere in
  circles, a bijection `pt` from the crossings of `A` to the intersection points of the circles,
  and a direction `sgn d = ±1` of every dart along its circle, such that the cyclic order of the
  crossings along each curve and the rotation `σ` at each crossing (seen from outside the sphere)
  are those of the circles.
* `CircleRep A`, `Circularizable A := Nonempty (CircleRep A)`.
* `GreatRep A`: a representation by great circles (all `h_i = 0`).
* `IsStretchable A := A.IsGreat ∧ Nonempty (GreatRep A)`: a great arrangement, the double cover
  of a projective pseudoline arrangement, realized by lines.

## What is proved

| paper | Lean | file |
|---|---|---|
| Fact 1: three circles form a Krupp iff their planes meet in a point inside the sphere | `Pca.Circ.IsCircleRep.fact1` | `Fact1.lean` |
| Theorem 1 (Great-Circle Theorem): a great arrangement is circularizable iff it has a great-circle representation | `Pca.Circ.greatCircle_theorem` | `GreatCircle.lean` |
| Corollary 9: stretchable iff circularizable, for great arrangements | `Pca.Circ.stretchable_iff_circularizable` | `GreatCircle.lean` |
| Theorem 16: digon-free and every triangle NonKrupp implies not circularizable | `Pca.Circ.thm16` | `Thm16Final.lean` |
| Theorem 19: not great and every triangle Krupp implies not circularizable | `Pca.Circ.thm19` | `Thm19Final.lean` |

These use no axioms beyond `propext`, `Classical.choice`, `Quot.sound`. Work in progress
(`Cor.lean`, not committed): Corollary 11 (`cor11_le_eight`, `cor11_nine`) and Corollary 13
(`cor13`). Planned: Corollaries 10 and 12, Theorem 27, Propositions 25 and 26.

## Axioms

Literature results about pseudoline arrangements that are not proved here enter as `axiom` in
`Pca/Circ/Axioms.lean` (not committed yet), each translated to the dart model through great
arrangements. Nothing from the paper itself is an axiom.

* `stretchable_of_le_eight`: every simple arrangement of at most 8 pseudolines is stretchable
  (Goodman, Pollack, J. Combin. Theory Ser. A 29 (1980)). Used for Corollary 11.
* `nonPappus_unique`: the non-Pappus arrangement is the unique non-stretchable simple
  arrangement of 9 pseudolines (Richter-Gebert; Felsner, Goodman, Handbook of Discrete and
  Computational Geometry, 3rd ed., 2018). Used for Corollary 11.
* `suvorov`: there is a line arrangement whose realization space is not connected (Suvorov,
  LNM 1346, 1988). Used for Corollary 13.

## Source

S. Felsner, M. Scheucher, *Arrangements of Pseudocircles: On Circularizability*,
https://arxiv.org/abs/1712.02149.

## Deviations from the paper

* Representations are semialgebraic data (planes and points), not drawings. Which of the two
  mirror images is meant is fixed by "seen from outside"; circularizability does not depend on
  it.
* Changing a representation continuously without an event (no triple point, no tangency) keeps
  the arrangement (`Transfer.lean`); scaling the planes is the explicit path (`Scaling.lean`).
* The paper assumes general position implicitly. Here every circularizable arrangement gets a
  generic representation by a moment-curve perturbation (`Perturb.lean`, `Generic.lean`,
  `Generic2.lean`).
* Theorems 16 and 19 move the planes and look at the first event. Lean proves the same
  statically: choose the triple point (Theorem 19) or the event (Theorem 16) of extremal norm in a
  generic representation and show that the corresponding three or two crossings bound a
  triangle or a digon (`Cone.lean`, `Thm19*.lean`, `Thm16*.lean`).
* "Intersecting" and "connected" hypotheses of the paper hold in the model automatically.
