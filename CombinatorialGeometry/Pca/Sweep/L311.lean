/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.11 (pp. 324-325), graph language (package P)

"LEMMA 3.11. There exists a curve `γ` whose removal does not leave a triangle.
PROOF. In the plane, there is at least one loop. Choose `γ` to be a loop with no loop inside it, if
there are many innermost loops, then choose one arbitrarily. Let the endpoints of `γ` be `k` and
`l`, with `k < l`.
Suppose that the removal of `γ` leaves the empty triangle `Δ(i, v, j)`, with `i = j ± 1`. By Lemma
3.9, the curve `γ` intersects only one leg. Without loss of generality, `γ` intersects leg
`⟨j, v⟩`, and Lemma 3.7 implies that it does so twice. By the way we chose `γ`, the curve containing
this leg, curve `γ(j)`, cannot be inside `γ`. Thus, Lemma 3.10 (3), tells us that either `j < k` or
`j > l`. Without loss of generality, `j < k`.
Let `u` be the intersection point of `γ` and `γ(j)` that is nearest to the vertex `j` in the original
arrangement `Γ`, equivalently, let `⟨j, u⟩` be an edge of `γ(j)`. Let `β` denote the portion of the
curve `γ` between vertices `k` and `u`. There are two cases, both portrayed in Figure 13, depending
on whether the empty triangle `Δ(i, v, j)` left after removing `γ` has `i = j + 1` or `i = j − 1`.
In both cases, the edge `⟨j, u⟩` and the curve `β`, together, partition the plane above the sweep into
a bounded and an unbounded component. We perform radical surgery in the unbounded component to
obtain a smaller counterexample. Discard all portions of the arrangement that lie in the unbounded
component of the plane above the sweep. Any curves that are cut by this process are cut where they
intersect `β`. We replace the discarded portions by rays to infinity, following the procedure used
in the proof of Lemma 3.5. Let `Γ'` denote the resulting arrangement. The cutting process may
increase the number of curves, but it does not give more intersections. In fact, we eliminated at
least the vertex `l`; and, therefore, the sweep can make progress in `Γ'`.
But how can the sweep make progress? Which operation can apply? Suppose that `Γ'` contains a hump
or triangle with vertices `m` and `m + 1` on the sweep. Since the surgery leaves no vertices in the
unbounded component, we have `j ≤ m < m + 1 ≤ k`. But this means that the hump or triangle was
contained in the bounded component above the sweep and was not affected by the cutting process.
Thus, it exists in the original arrangement `Γ`, a contradiction.
Therefore, we must have a curve that does not intersect the sweep in `Γ'`. Since all curves in `Γ`
do intersect the sweep by Lemma 3.4, there must be some curve `α` that has a portion in the bounded
component and is cut during the surgery. Curve `α` must enter and leave the bounded component
without intersecting the sweep `c` or the edge `⟨j, u⟩`. Thus, `α` crosses `β` twice and, as a result,
`α` is a loop with respect to `γ` above the sweep. However, this is equivalent to `α` being inside
`γ`, by Lemma 3.10 (2). This contradicts the choice of `γ`.
Therefore, the sweep cannot make progress in `Γ'`. This contradiction proves that there is some
curve whose removal does not leave an empty triangle."

Graph language (`doc/pca/sweep.md`, proof in `Pca/Sweep/P_*.lean`, package P): the bounded
component is the set of cells above `S` with `r = 1` for the cut `r` of the closed walk `⟨j, u⟩` +
`β` + `S[j, k]` (Jordan, `c_lid_cut`). The surgery is a redirect followed by a removal: the ∞-arc
is extended to all of `S` outside `[j, k]` (SH's "rays to infinity": `l` and every other vertex
outside `[j, k]` stops being a vertex on the sweep, so `numVertices` drops), then every curve
without a dart above `S` in the bounded component is removed. Both steps are already known to give
sweep configurations, so no new lower side is built (O1 does not arise here). Curves crossing `β`
are kept whole; outside the bounded component there is no finite edge, so they do not matter.
`u` stays a vertex above the sweep, so the result is not finished. SH's `j < k or j > l` is shown
by the parity of `δ = γ(j)` against the region of `γ` (`p_step1`); both cases are handled
(`p_case_left`, `p_case_right`, no mirror needed).
-/
import Pca.Sweep.Responsible
import Pca.Sweep.Inside
import Pca.Sweep.L310
import Pca.Sweep.P_Final

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- SH pp. 324-325: the surgery and what SH read off it. For an innermost loop `γ` whose removal
leaves an empty triangle there is a smaller configuration that is not finished, has no empty hump
and no empty triangle (they would be cells of `Γ` inside the bounded component), and in which a loop
can be taken only if some loop is inside `γ` (the cut curve `α` crosses `β` twice, Lemma 3.10 (2)). -/
theorem MinCE.l311_surgery (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) (hloop : Γ.IsLoop γ)
    (hin : ∀ γ', ¬ Γ.Inside γ' γ) (X : Γ.Removal {γ}) {d' : X.D'} (ht : X.Γ'.EmptyTriAt d') :
    ∃ (n' : ℕ) (K : Conf.{u} n'), SizeLT K.Γ Γ ∧ ¬ K.Γ.Terminal ∧
      (∀ d, ¬ K.Γ.EmptyHumpAt d) ∧ (∀ d, ¬ K.Γ.EmptyTriAt d) ∧
      (K.Γ.CanTakeLoop → ∃ α, Γ.Inside α γ) :=
  p_l311_surgery hΓ hγ hloop hin X ht

/-- **SH Lemma 3.11** (pp. 324-325): some curve's removal does not leave a triangle. -/
theorem MinCE.lemma_3_11 (hΓ : Γ.MinCE) :
    ∃ γ, Γ.Present γ ∧ ∀ (X : Γ.Removal {γ}) (d' : X.D'), ¬ X.Γ'.EmptyTriAt d' := by
  obtain ⟨γ, hγ, hloop, hin⟩ := exists_innermost hΓ.exists_loop
  refine ⟨γ, hγ, fun X d' ht => ?_⟩
  obtain ⟨n', K, hlt, hT, hH, hTr, hL⟩ := hΓ.l311_surgery hγ hloop hin X ht
  apply hΓ.2 n' K hlt
  refine ⟨hT, ?_⟩
  rintro (⟨d, hd⟩ | ⟨d, hd⟩ | h)
  · exact hH d hd
  · exact hTr d hd
  · obtain ⟨α, hα⟩ := hL h
    exact hin α hα

end SConf

end Pca.Sweep
