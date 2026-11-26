# The dart model

All pseudocircle libraries (`Pca`, `PcaSweep`, `PcaGreat`, `PcaFlipGraph`, `PcaCirc`) work with
one combinatorial model of an arrangement, defined in `Pca/Model.lean`. There is no topology in it:
an arrangement is a plane graph given by half-edges and a rotation system.

## Darts, σ, α

A simple intersecting arrangement of `n` pseudocircles on the sphere is described by its
arrangement graph: the vertices are the crossings, the edges are the segments of the curves
between consecutive crossings. Every crossing has degree 4.

* `D` is a finite type of darts. A dart is one end of a segment, oriented away from its crossing.
  Every crossing has four darts.
* `σ : Perm D` (rotation) maps a dart to the next dart counter-clockwise at the same crossing.
* `α : Perm D` (edge involution) maps a dart to the dart at the other end of its segment.
* `curve : D → Fin n` is the pseudocircle the dart runs along.

Derived maps:

* `φ = σ α` (face permutation): walk along `d` to the next crossing and turn to the next dart
  counter-clockwise. The `φ`-orbit of `d` is the cell to the right of `d`, `cellOf d`.
* `straight = σ² α`: walk along `d` and continue on the same curve.

Crossings are `σ`-orbits, segments are `α`-orbits, cells are `φ`-orbits. A `k`-cell is a cell
whose `φ`-orbit has `k` darts; digons and triangles are 2- and 3-cells. `p k` is the number of
`k`-cells.

## Axioms (`IsArrangement`)

1. Every `σ`-orbit has 4 darts.
2. `α` is a fixed-point-free involution.
3. A segment lies on one curve: `curve (α d) = curve d`.
4. Around a crossing the curves alternate between two distinct curves: `curve (σ d) ≠ curve d`,
   `curve (σ² d) = curve d`. So exactly two curves pass through a crossing, and they cross.
5. One closed curve per label: darts of the same curve lie on one `straight`-orbit, up to
   reversing direction (`σ²`).
6. Intersecting: two distinct curves share exactly two crossings.
7. Sphere: `#crossings − #segments + #cells = 2`.

Connectivity is not an axiom; it follows from 5 and 6 (`Arrangement.connected`). Together with
Euler's formula it says that the map has genus 0. Every model has `n ≥ 2` (`two_le_n`).

## Sides

There is no inside or outside on the sphere. A side function of a curve `C` is
`s : Cell → ZMod 2` such that the two cells at a segment get different values exactly when the
segment lies on `C` (`IsSide`, `Pca/Side.lean`). It exists (`exists_side`, a combinatorial Jordan
curve theorem, proved by linear algebra over `𝔽₂` in `Pca/Jordan.lean`) and is unique up to
swapping 0 and 1. The two sides of `C` are the cells with `s = 0` and with `s = 1`.

## Triangle flip

`Arrangement.flip A d hT` (`Pca/Flip.lean`) flips the triangle `T = cellOf d`: each side of `T` is
pushed over the opposite corner. On the same dart type, `σ` and `curve` stay the same and only `α`
changes, by conjugation with the involution that swaps the darts of the sides of `T` with their
`straight` successors. The result is again an arrangement (`flip_isArrangement`), and the cell
sizes change as expected (`flip_size_across`, `flip_size_opposite`, `flip_size_of_ne`).

## Modelling assumption

The objects in Lean are connected genus-0 maps with these properties, not curves. That every
simple intersecting arrangement of pseudocircles gives such a map and that every such map comes
from an arrangement, unique up to homeomorphism of the sphere, is the classical correspondence
between cellular embeddings and rotation systems. It is used as the link to the papers and is not
proved here. A map and its mirror image (`σ ↦ σ⁻¹`) describe mirror arrangements.

Fingerprints (the list format used to enumerate arrangements) are turned into maps by
`Pca/Fingerprint.lean`; `Describes` checks that a map is the arrangement of a given fingerprint.
