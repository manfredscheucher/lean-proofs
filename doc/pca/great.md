# PcaGreat: great-pseudocircle arrangements, Ringel, Levi

Library `PcaGreat`, root `CombinatorialGeometry/PcaGreat.lean`, files `Pca/Great/`.

A projective arrangement of pseudolines lifts to an arrangement of great-pseudocircles on the
sphere (its double cover). In the dart model (`model.md`) these are the arrangements in which
every three curves form a Krupp arrangement. Everything here is stated for them.

## What is proved

* `Pca.Arrangement.IsGreat` (`Defs.lean`): for distinct curves `a, b, c`, the two crossings of
  `a` and `b` lie on different sides of `c`.
* Antipodal flips. In a great arrangement every triangle has an antipodal triangle on the same
  three curves (`Pca.Great.exists_antipodalTri`). `Arrangement.AFlip A B` flips a triangle and its
  antipode; the result is again great (`Pca.Great.aflip_isGreat`). This is the flip of the
  projective arrangement.
* Ringel's theorem (`Pca.Great.ringel`, `Ringel.lean`): any two great arrangements of `n` curves
  are joined by a sequence of antipodal flips, up to isomorphism (`Pca.Great.Iso`).
* Levi's extension lemma (`Pca.Great.levi`, `Main.lean`): for a great arrangement `A` and two cells
  `f₁, f₂` there is a great arrangement with one more curve that passes through both cells and
  whose deletion gives back `A` (`Pca.Great.IsDeletion`, `Pca.Great.Passes`).
* Levi's extension lemma for signotopes (`Pca.Great.Sig.levi`, `SigLevi.lean`; `IsSig`, `IsFliple` in `SigDefs.lean`): for a
  3-signotope on `[n]` and two disjoint 2-subsets `I, J` there is a 3-signotope on `[n+1]` that
  restricts to it and in which the lifts of `I` and `J` are fliples (Bergold–Felsner–Scheucher,
  Theorem 1.2, rank 3).
* Levi's triangle theorem (`Pca/Great/Tri/Levi.lean`, `n ≥ 3`): every curve has at least six
  triangles with a side on it (`Pca.Great.six_le_tC`), hence `2n ≤ p_3` (`two_mul_le_p3`); for
  `n ≥ 4` there are at least three on each side of every curve (`three_le_side`). Projectively:
  every pseudoline touches at least three triangles, and there are at least `n` triangles.

## Axioms

None beyond `propext`, `Classical.choice`, `Quot.sound`.

## Sources

* F. Levi, *Die Teilung der projektiven Ebene durch Gerade oder Pseudogerade* (1926): extension
  lemma, triangle theorem.
* G. Ringel, *Teilungen der Ebene durch Geraden oder topologische Geraden*, Math. Z. 64 (1956):
  flip connectivity.
* Y. Alves Radtke, S. Felsner, J. Obenaus, S. Roch, M. Scheucher, B. Vogtenhuber, *Flip Graph
  Connectivity for Arrangements of Pseudolines and Pseudocircles*,
  https://arxiv.org/abs/2310.19711: great-pseudocircle setting, antipodal flips.
* E. Bergold, S. Felsner, M. Scheucher, *An extension theorem for signotopes*,
  https://arxiv.org/abs/2303.04079.

## Proof routes and deviations

* Everything is done on the sphere with side functions; there is no projective plane and no
  region argument. The central tool is a quarter lemma (`Quarter.lean`, `Q_*.lean`): fix a frame
  curve `c₀`, one of its sides `H` and a line `ℓ`; a quarter of `H` cut by `ℓ` that contains a
  crossing of the relevant curves contains a triangle with a side on `ℓ`. This is a sweep of a
  lune by triangle flips.
* Ringel: triple signs relative to the frame, and a canonical form in which all triples are
  positive. A great arrangement that is not canonical has a negative triangle, its antipodal flip
  changes exactly that triple, and two canonical arrangements are isomorphic (an explicit rotation
  table in frame coordinates).
* Levi (great version): double a curve through `f₁` (insert a new curve along a closed walk,
  `Ins_*.lean`), then sweep it by antipodal flips of triangles with a side on the new curve until
  it passes `f₂`. Such flips keep the deletion. The measure is the number of pairs of old curves
  whose crossing is still on the unswept side.
* Levi (signotopes): as in the paper (partial order on 2-subsets, extension of a down-set,
  rotations). The paper cites Felsner–Weil for the fact that the relation on 2-subsets is a
  partial order; here acyclicity is proved from the paper's own lemmas (`prec_irrefl`). Instead
  of relabelling the elements after each rotation, the order key changes. The signotope version
  is not connected to the dart-model version.
* Triangle theorem: proved with the quarter lemma, not with the Snoeyink–Hershberger sweep, since
  the latter only gives one antipodal pair of triangles and does not say where they are.
* `Pca.Great.Iso` is orientation preserving; mirror images are not identified.
