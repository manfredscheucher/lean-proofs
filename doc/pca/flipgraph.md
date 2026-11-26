# PcaFlipGraph: triangle flip connectivity of intersecting arrangements

Library `PcaFlipGraph`, root `CombinatorialGeometry/PcaFlipGraph.lean`, files `Pca/FlipGraph/`.

## What is proved

The main results of Alves Radtke, Felsner, Obenaus, Roch, Scheucher, Vogtenhuber (FROS below) on
arrangements of pseudocircles (`model.md`), all in namespace `Pca.FlipGraph`:

* `Marked.zipping` (`Zip.lean`, FROS Lemma 2): a lens of two curves whose arcs are all
  transversal can be swept by triangle flips until it contains no crossing.
* `thm_main_cipa` (`Final.lean`, FROS Theorem 4): the triangle flip graph of intersecting
  cylindrical arrangements of `n` pseudocircles is connected. Any two are joined by flips through
  cylindrical arrangements, up to isomorphism.
* `thm_main_ipa` (FROS Theorem 3): the triangle flip graph of intersecting arrangements of `n`
  pseudocircles is connected.
* `sphere_connected`: the same on the sphere, where every triangle may be flipped.

## Main definitions (`Basic.lean`)

* `Marked n D`: an arrangement with a marked cell, the unbounded cell of a drawing in the plane.
  `Marked.Inside C f`: `f` is on the side of `C` that does not contain the marked cell.
  `Marked.Cylindrical`: some cell is inside every curve.
* `FlipStep`: flip of a triangle other than the marked cell (`Arrangement.flip`), with the marked
  cell carried along. `Reach` is its reflexive-transitive closure, `CylStep`, `CylReach` the
  versions through cylindrical arrangements. The flip graph is undirected (`flipStep_symm`).
* `Iso`, `IsIso`: a dart bijection commuting with `σ` and `α`, with a permutation of the curves,
  mapping the marked cell to the marked cell.
* `SphereStep`, `SphereIso`: the same without a marked cell.

## Axioms

None beyond `propext`, `Classical.choice`, `Quot.sound`. The sweeping lemma is used as a theorem
(`Pca.Arrangement.sweepFirstMove`, proved in `PcaSweep`).

## Source

Y. Alves Radtke, S. Felsner, J. Obenaus, S. Roch, M. Scheucher, B. Vogtenhuber, *Flip Graph
Connectivity for Arrangements of Pseudolines and Pseudocircles*, https://arxiv.org/abs/2310.19711.

## Deviations from the paper

* Plane vs. sphere. FROS draw arrangements in the plane and flip only bounded triangles. Here the
  unbounded cell is a marked cell; the sphere version follows.
* Isomorphism keeps the orientation (no mirrors), as in FROS section 2.
* Zipping (Lemma 2) is proved as in FROS through Claims A and B (a source vertex gives a triangle
  with a side on the swept arc). Claim B uses simple directed cycles of chords and their regions,
  given as cuts over `ZMod 2`, with infinite descent on the size of the region, instead of FROS'
  induction. The lemma carries the crossing form of transversality, which a flip preserves
  literally. A lens with a closed chord is excluded by an extra hypothesis (`Lens.Sep`).
* Theorem 4 does not use the representation by pseudoparabolas. The canonical arrangement is
  characterized by sides (`Marked.Canon`, unique up to isomorphism by `canon_iso`). Sweeping a
  curve downwards becomes zipping the lens between it and the curves already processed. The
  order of the curves is read off from the nesting of their crossings on the first curve
  (`Order.lean`), by parity along walks.
* Theorem 3. Deleting a curve (`Arrangement.deleteOn`, `Delete.lean`) reuses the removal of the
  sweep proof and lives on a subtype of the darts, so flips of `A` and of `A − C'` act on the same
  darts. A flip with a side on `C'` does not change the deletion, and a flip without a corner on
  `C'` commutes with it. The mimicking step (`MimicRel`, `mimic_step`) follows FROS' three cases.
  The induction is on `n` (`reach_cylindrical`).
* FROS' remark that Lemma 2 also follows from Snoeyink–Hershberger is not used: the sweep may
  return a triangle at a corner of the lens, whose flip leaves the lens.
