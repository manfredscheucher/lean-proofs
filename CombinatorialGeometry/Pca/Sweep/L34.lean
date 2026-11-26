/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.4 (p. 318), graph language (package B)

"LEMMA 3.4. All curves in `Γ` intersect the sweeping curve `c`.
PROOF. Since the sweep cannot make progress by taking a new curve, any curve `γ` that does not
intersect `c` is not visible from `c`. But removing such a curve `γ` does not change `c`'s
ability to make progress. Therefore, all curves in the smallest counterexample intersect the
sweeping curve `c`."

Graph language: a curve with a part above `S` and no vertex on the sweep has no segment on a cell
above an edge of `S` (else `CanTakeLoop`). Removing it (`Removal {γ}`; curves that only met `γ`
drop out with it, and they are invisible for the same reason) leaves every cell above an edge of
`S` unchanged, so an operation of `Γ − γ` (Lemma 3.3) is one of `Γ`; and `Γ − γ` is not finished
(else `γ` would be visible).
-/
import Pca.Sweep.L33
import Pca.Sweep.AB_L34

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- **SH Lemma 3.4** (p. 318). -/
theorem MinCE.lemma_3_4 (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) : Γ.MeetsSweep γ := by
  by_contra hms
  obtain ⟨hγS, d0, hd0, hA⟩ := hγ
  obtain ⟨X⟩ := exists_removal (Γ := Γ) {γ} (fun h => hγS (mem_singleton.1 h).symm)
  exact hΓ.lemma_3_3 ⟨γ, mem_singleton_self γ, hγS, d0, hd0, hA⟩ X
    (ab_l34_core hΓ.1.2 hms hγS X hd0 hA)

end SConf

end Pca.Sweep
