/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import Pca.Model
import Pca.Counting
import Pca.Derived
import Pca.Fingerprint
import Pca.Excess
import Pca.Digon
import Pca.Fan
import Pca.Jordan
import Pca.Flip
import Pca.DigonAxiom
import Pca.Potential
import Pca.Main
import Pca.Side
import Pca.SweepLemma
import Pca.Sweep
import Pca.LowerBound

/-!
# Sources

* S. Felsner, M. Scheucher, *Arrangements of Pseudocircles: Triangles and Drawings*,
  https://arxiv.org/abs/1708.06449 (setting, lower bounds, sweeping lemma as used there).
* Upper bound on the number of triangles (`Pca.Main`): new result by M. Scheucher, not yet published.
* Digon theorem (axiom `digon_bound`): E. Ackerman, G. Damásdi, B. Keszegh, R. Pinchasi,
  R. Raffay, https://arxiv.org/abs/2412.10023.
* Sweeping lemma: J. Snoeyink, J. Hershberger, *Sweeping arrangements of curves*, DIMACS Series 6
  (1991), 309-349.
-/
