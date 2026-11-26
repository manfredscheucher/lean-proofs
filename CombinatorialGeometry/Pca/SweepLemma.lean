/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The sweeping lemma (milestone 7), proved

The sweeping lemma in the two forms of `Pca/Sweep.lean`, for every arrangement. The proof follows
Snoeyink-Hershberger's sweep argument, translated into the language of the arrangement graph
(`Pca/Sweep/`, `doc/pca/sweep.md`); it uses no axioms beyond Lean's standard ones.
-/
import Pca.Sweep.Final

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

/-- **Sweeping lemma** (first move of a sweep): on the side of a pseudocircle `C` containing a
cell `f₀` there is a digon or triangle `≠ f₀` with a side on `C`. -/
theorem sweepFirstMove : A.SweepFirstMove := Pca.Sweep.sweepFirstMove A

/-- **Two digons or triangles on each side** of every pseudocircle. -/
theorem sweepTwoCells : A.SweepTwoCells := Pca.Sweep.sweepTwoCells A

end Pca.Arrangement
