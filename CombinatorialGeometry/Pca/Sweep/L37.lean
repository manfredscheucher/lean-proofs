/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.7 (p. 319), graph language (package E, sketch only in source)

"LEMMA 3.7. For any vertex `j` on the sweep, the removal of the curve `γ(j)` cannot leave an
empty hump or empty triangle with vertices `i` and `k` satisfying `i < j < k`.
PROOF. By case analysis; we sketch the idea: Lemma 3.6 implies that the curve `γ(j)` intersects
the triangle or hump that is formed if `γ(j)` is removed. That intersection point forms a new
empty triangle. To break up the new triangle, `γ(j)` must reenter it, but in doing so, the curve
`γ(j)` creates another triangle that cannot be avoided."

**Sketch only in source; the proof is reconstructed from the sketch and figures** (chord lemma,
noncrossing lemma, K-side / I-side cases, a statement about the cell of `Γ − γ` and the darts of
`γ` inside it).

Graph form: the finite edge `[i, k]` below the hump or triangle of `Γ − γ` is a single segment of
`S` in `Γ` (no vertex of `γ` on it): `α` of `Γ − γ` at that edge is `α` of `Γ`. The vertices
of `S` strictly between `i` and `k` in `Γ` are exactly the deleted crossings on that joined
segment, so this is SH's statement.

Proof (package E, the reconstruction of `doc/pca/sweep.md` ported to the dart model):
`E_Seg.lean` (pieces of the joined segments, every dart above the sweep off `γ` is a piece, by
Lemma 3.4), `E_Face.lean` (the boundary walk of the cell of `Γ − γ` in `Γ`, Jordan for it),
`E_Chord.lean` (chord lemma, noncrossing lemma), `E_Main.lean` (case analysis: a hump, a convex
triangle at `K` or at `I` (Lemma 3.6), three crossings of `γ` with one leg, or crossing chords).
The triangles found are convex (`φ a = α b`, positions increasing along the finite edge), as
required by the statement of Lemma 3.6.
-/
import Pca.Sweep.G1
import Pca.Sweep.E_Main

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- **SH Lemma 3.7** (p. 319). -/
theorem MinCE.lemma_3_7 (hΓ : Γ.MinCE) {γ : Fin n} (X : Γ.Removal {γ}) {d' : X.D'}
    (h : X.Γ'.EmptyHumpAt d' ∨ X.Γ'.EmptyTriAt d') : X.ι (X.Γ'.α d') = Γ.α (X.ι d') :=
  Removal.e_main (fun _ hδ => hΓ.lemma_3_4 hδ)
    ⟨hΓ.lemma_3_6.1, hΓ.lemma_3_6.2⟩ h

end SConf

end Pca.Sweep
