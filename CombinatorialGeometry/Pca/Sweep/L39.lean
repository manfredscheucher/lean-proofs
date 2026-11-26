/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.9 (pp. 320-322), graph language

"LEMMA 3.9. Suppose that the arrangement `Γ − {γ}` has an empty triangle `Δ(i, v, i + 1)`. Then,
in the original arrangement `Γ`, the face above the edge `[i, i + 1]` has `v` as a vertex."

Assembled from the hiding step and the two cases (no `sorry` here). The face above `[i, i + 1]` in
`Γ` is `upperCell (ι d')` (by Lemma 3.7 the edge is a segment of `Γ`).
-/
import Pca.Sweep.L39Case2

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- **SH Lemma 3.9** (pp. 320-322). -/
theorem MinCE.lemma_3_9 (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) (X : Γ.Removal {γ})
    {d' : X.D'} (h : X.Γ'.EmptyTriAt d') : ApexVisible X d' := by
  by_contra hv
  rcases hΓ.lemma_3_9_hide hγ X h hv with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact hΓ.lemma_3_9_case1 hγ X h hv h₁ h₂
  · exact hΓ.lemma_3_9_case2 hγ X h hv h₁ h₂

end SConf

end Pca.Sweep
