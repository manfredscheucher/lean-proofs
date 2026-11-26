/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.9 (pp. 320-322), the hiding step (package G)

"PROOF. Suppose that `v` is not a vertex of the face above the edge `[i, i+1]`. Then the curve `γ`
must *hide* `v` from that portion of the sweep by intersecting both legs, `⟨i, v⟩` and
`⟨i + 1, v⟩`, of the triangle `Δ(i, v, i + 1)`. Lemma 3.7 implies that `γ` intersects both legs
once or both legs twice; we consider these possibilities in two separate cases." (p. 320)

Graph language: the legs of `Γ − γ` are `σ d'` (from `i` to `v`) and `φ (σ d')` (from `v` to
`i + 1`); `hits` counts the crossings with `γ` on them in `Γ` (`Removal.hits`). "Hide": if no
crossing with `γ` were on a leg, that leg would be a segment of `Γ` and `v` a corner of the cell
above `[i, i+1]` (walk around the cell). "Both once or both twice" from Lemma 3.7: parity (`γ`
enters and leaves the triangle region, Jordan) and at most two crossings per pair; one leg
`0`, the other `2` is excluded because `v` is hidden; `1`/`2` mixed is odd.
-/
import Pca.Sweep.L38
import Pca.Sweep.GK_Tri

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- `v` (the apex of the empty triangle of `Γ − γ` at `d'`, seen in `Γ`) is a corner of the cell of
`Γ` above `[i, i + 1]`. -/
def ApexVisible {γ : Fin n} (X : Γ.Removal {γ}) (d' : X.D') : Prop :=
  ∃ e ∈ (Γ.upperCell (X.ι d')).darts,
    Γ.crossingOf e = Γ.crossingOf (X.ι (X.Γ'.φ (X.Γ'.σ d')))

/-- **SH Lemma 3.9**, hiding step (p. 320). -/
theorem MinCE.lemma_3_9_hide (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) (X : Γ.Removal {γ})
    {d' : X.D'} (h : X.Γ'.EmptyTriAt d') (hv : ¬ ApexVisible X d') :
    (X.hits (X.Γ'.σ d') = 1 ∧ X.hits (X.Γ'.φ (X.Γ'.σ d')) = 1) ∨
    (X.hits (X.Γ'.σ d') = 2 ∧ X.hits (X.Γ'.φ (X.Γ'.σ d')) = 2) := by
  have T := gk_tri X h (hΓ.lemma_3_7 X (Or.inr h))
  have h1 := T.k1le
  have h2 := T.k2le
  have hp := T.parity
  have hnz : X.hits (X.Γ'.σ d') ≠ 0 ∧ X.hits (X.Γ'.φ (X.Γ'.σ d')) ≠ 0 := by
    by_contra hc
    exact hv ⟨_, Orbit.mem_darts.2 (T.cell_b_of_zero (by omega)), rfl⟩
  omega

end SConf

end Pca.Sweep
