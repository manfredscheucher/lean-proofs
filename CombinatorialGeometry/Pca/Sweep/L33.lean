/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.3 (p. 318), graph language (package A)

"LEMMA 3.3. Removing any curve `γ` from the arrangement `Γ` allows the sweep to progress.
PROOF. By minimality of the arrangement."

Removal of curves: `Pca/Sweep/Removal.lean`. Minimality gives only "not stuck" (finished or
progress); the finished case is excluded by the gap lemma `removal_not_terminal`
(`Pca/Sweep/G1.lean`), not in SH.
-/
import Pca.Sweep.Removal

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- **SH Lemma 3.3** (p. 318): after removing curves (one of them with a part above the sweep)
from a minimal counterexample, the sweep is not stuck. -/
theorem MinCE.lemma_3_3 (hΓ : Γ.MinCE) {R : Finset (Fin n)} (hR : ∃ γ ∈ R, Γ.Present γ)
    (X : Γ.Removal R) : ¬ X.Γ'.Stuck :=
  hΓ.2 n ⟨X.D', X.Γ'⟩ (X.sizeLT hR)

end SConf

end Pca.Sweep
