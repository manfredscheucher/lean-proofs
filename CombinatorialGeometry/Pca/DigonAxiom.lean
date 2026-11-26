/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The digon theorem (axiom)

The only axiom of the project so far.
-/
import Pca.Counting

namespace Pca

/-- **Digon theorem**: every simple
intersecting arrangement of `n ≥ 3` pseudocircles has at most `2n - 2` digons.

E. Ackerman, G. Damásdi, B. Keszegh, R. Pinchasi, R. Raffay, *The Maximum Number of Digons
Formed by Pairwise Intersecting Pseudocircles*, 41st International Symposium on Computational
Geometry (SoCG 2025), LIPIcs, 2:1-2:14, 2025; arXiv:2412.10023.

Taken as an axiom (not proved in Lean). `p 2` counts the cells whose face orbit has two darts,
as everywhere in the model. -/
axiom digon_bound : ∀ {n : ℕ} {D : Type*} [Fintype D] [DecidableEq D] (A : Arrangement n D),
  3 ≤ n → A.p 2 ≤ 2 * n - 2

end Pca
