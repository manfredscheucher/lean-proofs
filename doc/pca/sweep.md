# PcaSweep: the Snoeyink–Hershberger sweeping lemma

Library `PcaSweep`, root `CombinatorialGeometry/PcaSweep.lean`, files `Pca/Sweep/`. It is also
built as part of `Pca`, which uses the result for its lower bounds.

## What is proved

The sweeping lemma for arrangements of pseudocircles, in the two forms used in the literature:

* `Pca.Arrangement.sweepFirstMove` (`Pca/SweepLemma.lean`): for every curve `C`, side function `s`
  of `C` and cell `f₀`, there is a digon or triangle `g ≠ f₀` with a side on `C` and on the same
  side of `C` as `f₀`. This is the first move of a sweep that starts at `C` with `f₀` as the
  unbounded cell, as Felsner and Scheucher use it.
* `Pca.Arrangement.sweepTwoCells`: on each side of every curve there are two distinct digons or
  triangles with a side on it (Snoeyink–Hershberger, Lemma 4.1). The two forms are equivalent
  (`sweepFirstMove_iff`).

The proof is Snoeyink and Hershberger's: a minimal counterexample to "the sweep can always make
progress" leads to a contradiction through their Lemmas 3.3 to 3.11. Everything is stated over
the dart model (`model.md`) instead of curves in the plane.

## Main declarations

* `Pca.Sweep.SConf`, `IsSConf` (`Conf.lean`): a sweep configuration. Darts, `σ`, `α`, `curve` as
  in the model, a sweep curve `S`, a side function of `S` (the upper side is the part not yet
  swept) and the ∞-arc, a marked run of darts of `S`.
* `SConf.Progress`, `SConf.Terminal`, `SConf.Stuck`, `SConf.MinCE` (`Basic.lean`): the
  operations of the sweep (pass an empty triangle, pass an empty hump, take a loop), finished
  sweeps, and the minimal counterexample.
* `SConf.MinCE.lemma_3_3`, `lemma_3_4`, `lemma_3_6`, `lemma_3_7`, `lemma_3_8`, `lemma_3_9`,
  `lemma_3_11`, and `SConf.lemma_3_10_12`, `lemma_3_10_23`, `lemma_3_10_31`: the lemmas of the
  paper, one file each (`L33.lean` … `L311.lean`).
* `SConf.not_stuck`, `SConf.terminal_or_progress` (`Main.lean`): the sweep never gets stuck.
* `Pca.Sweep.sweepFirstMove`, `sweepTwoCells` (`Final.lean`): the result for arrangements.
* `Moves.lean`: the three moves (triangle flip, digon collapse, digon create) as operations on
  sweep configurations. They are not needed for the lemma.

## Axioms

None beyond `propext`, `Classical.choice`, `Quot.sound`.

## Source

J. Snoeyink, J. Hershberger, *Sweeping arrangements of curves*, DIMACS Series in Discrete
Mathematics and Theoretical Computer Science 6 (1991), 309–349. Page and lemma numbers in the code
refer to this version.

## Deviations from the paper

* Setting. Snoeyink and Hershberger work in the plane with a bi-infinite sweep curve. Here the
  sphere is punctured along the ∞-arc of `S`, so the linear order of the vertices on the sweep,
  rays, and "the unbounded face" all become statements about darts.
* Class of configurations. Inside the proof, curves may cross in 0 or 2 points and may miss the
  sweep curve. So "exactly two crossings per pair" is relaxed to "at most two", and connectivity
  is added as an axiom of `IsSConf`. Removing curves drops components that are not connected to
  `S`; after Lemma 3.4 nothing is dropped.
* The lower side of `S` is irrelevant (their Lemma 3.5): everything depends only on the cells on
  the upper side (`Lower.lean`). Where the paper changes the upper side (untangling a crossing in
  3.9, the surgery in 3.11), a new lower side is built.
* Lemma 3.6 is proved for all triangles (`MinCE.x_no_tri`), not only the convex ones. The paper's
  argument misses the reflex case, which Lemma 3.8 needs.
* Lemma 3.3 says that after a removal some operation applies. Minimality only gives "finished or
  progress"; the missing step is `MinCE.removal_not_terminal` (`G1.lean`).
* Lemmas 3.7 and 3.10 are only sketched in the paper, and the uniqueness of responsible edges and
  the inside order of loops are claimed without proof. All are proved here
  (`responsible_unique`, `Inside.lean`).
* In Case 1 of Lemma 3.9 the remark "by minimality, there are no curves `γ(m)` with `m < i` or
  `j < m`" is not needed. In Case 2 the paper's closing argument ("the middle of `γ` does not
  intersect the sweep, so no triangles are formed") is replaced by Case 1 applied to the removal
  of the other leg's curve.
* Lemma 3.11 is done by directing a curve to the ∞-arc and removing it, without a new lower side.
* Lemma 4.1 is false for `n = 1`; every model has `n ≥ 2`.
