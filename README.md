# lean-proofs

This repository provides Lean proofs of results from my research, of the theory it builds on, and of
some related results that, as far as I know, had not been formalized in Lean before. The purpose is
evidence that the proofs are correct.

Mathlib already covers a lot of mathematics, in particular combinatorics: graphs and other discrete
structures can often be modelled quite directly. Geometry and topology are a different story.
Combinatorial properties of geometric or topological structures, such as curves in the plane
(arrangements of lines, pseudolines or pseudocircles, topological drawings of graphs), are harder:
formalizing them pulls in topology, geometry, algebra and analysis and takes much more work.

The standard way to work with such structures is to axiomatize and discretize: curves and their
crossings cut the plane into cells, and the arrangement is described by a combinatorial object, such
as a plane graph given by half-edges (darts) and a rotation system, an oriented matroid or a
signotope.

Many proofs in this area are case analyses over dozens of pages. Snoeyink and Hershberger's sweeping
lemma (1991) takes about 40 pages. Levi's extension lemma and his sweep (1926) are a hundred years
old, written in German, and available only as a scan, if you get hold of the original at all. Both
are proved here. A formal proof is a bulletproof check that anyone can run.

## What is here

One Lake project, one Lean library per paper or topic, grouped by field.

| field | library | content | status |
|---|---|---|---|
| combinatorial geometry | `Pca` | arrangements of pseudocircles: model, counting, digon/fan lemmas, triangle flip, max triangles `p_3 ≤ 4/3·C(n,2) + (2n−2)/3 − p_2`, lower bounds | proved; one axiom `digon_bound` (Ackerman et al. 2025) |
| | `PcaSweep` | Snoeyink–Hershberger sweeping lemma, in graph language | proved, no axiom |
| | `PcaGreat` | great-pseudocircle (projective pseudoline) arrangements: antipodal flips, Ringel's flip connectivity, Levi's extension lemma, also via signotopes (Bergold–Felsner–Scheucher); Levi's triangle theorem (every curve has ≥ 6 triangles on it, `p_3 ≥ 2n`; projective: ≥ 3 per pseudoline, ≥ n in total) | proved, no axiom |
| | `PcaFlipGraph` | triangle flip connectivity of intersecting arrangements (Alves Radtke, Felsner, Obenaus, Roch, Scheucher, Vogtenhuber) | proved, no axiom |
| | `PcaCirc` | circularizability (Felsner–Scheucher): Great-Circle Theorem and its corollaries | in progress |
| | `NonCirc`, `NonCircCerts` | non-circularizability certificates | in progress |
| | `PcaInstances` | `native_decide` checks on all arrangements with n ≤ 4 | checks |
| stochastic geometry | `KHoles` | k-holes in random point sets, Theorem 7 of [arXiv:2111.12533](https://arxiv.org/abs/2111.12533), with the limit constants in closed form | proved; not yet rebuilt in this repository |

Details per project in `doc/README.md` (one page per library). Each library's root file lists its
sources.

## Build

Lean 4.33.1 with the Mathlib of `lake-manifest.json`. Build with the guard script, which runs one
Lean process at a time and aborts if a `lean` process uses more than 1 GB of its own memory:

```
scripts/build.sh
scripts/build.sh PcaSweep
```

Without arguments it builds the default target `Pca`; otherwise any library or module.

Mathlib is currently a local path dependency in `lakefile.toml`; a git dependency will follow.

## License

Apache 2.0, see `LICENSE`.
