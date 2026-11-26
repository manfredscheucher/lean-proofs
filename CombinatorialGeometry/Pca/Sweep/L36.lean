/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.6 (pp. 318-319), graph language (package C)

(SH Lemma 3.5 is `Pca/Sweep/Lower.lean`: on the sphere it says that only the upper side of `S`
matters.)

"LEMMA 3.6. The arrangement `Γ` cannot contain a hump or a triangle.
PROOF. The arrangement certainly cannot contain an empty triangle or hump; otherwise, the sweep
could make progress. Suppose, however, that `Γ` contains vertices `i` and `j` on the sweep, with
`i < j`, which are the ends of a hump or a triangle. Since none of the curves that intersect the
sweep between `i + 1` and `j − 1` intersect the hump or triangle, the smaller arrangement
`Γ' = {γ(i+1), γ(i+2), …, γ(j−1)}` lies completely inside the hump or triangle. But, by
minimality, the sweep can make progress in the arrangement `Γ'`. This contradicts the fact that
`Γ` is unsweepable and establishes the lemma."

Graph language: `Γ'` = `Γ` with all curves removed except those with a vertex on the sweep
strictly between `i` and `j` (`Removal`). The legs (resp. the hump) are segments, so carry no
crossing; by Jordan (`exists_cut` for the closed walk legs + `S[i, j]`) a curve with a vertex in
`(i, j)` stays in the region and the cells of `Γ'` above edges in `(i, j)` are cells of `Γ`. If no
curve is left (`j = i + 1`), the hump or triangle is itself a cell above `[i, i+1]` (connectivity:
nothing hides inside), i.e. empty.

Proof (package C, `Pca/Sweep/C_Core.lean`, `C_Trans.lean`, `C_Lid.lean`): the region is the cut
`r` of the closed walk `S[i, j]` + hump / legs (Jordan). SH's `Γ'` is the removal of every curve
with no dart inside the region off the lid (`cR`); such a kept curve lies inside (`c_kept`), so it
is no ray and `Γ'` is not finished; a loop of `Γ'` contradicts Lemma 3.4; an empty hump or triangle
of `Γ'` is a cell of `Γ` above a finite edge (`c_transfer`). If no vertex lies strictly between
`i` and `j`, the hump or triangle is the cell above `[i, i + 1]`.

**Statement change.** Triangles are restricted to the
**convex** orientation (`IsConvexTri`): legs `a = ⟨k, v⟩`, `b = ⟨l, v⟩` with `k < l` and
`φ a = α b`, i.e. the region at `v` is the angle between the legs (SH's figures; an empty
triangle is convex). In the "reflex" orientation (`φ b = α a` with `k < l`) both curves of the
triangle continue into the region after `v`, so they belong to `Γ'` and possibly no curve with a
part above `S` is removed; SH's sentence "none of the curves ... intersect the hump or triangle"
does not cover it (`doc/pca/sweep.md`, O3).
-/
import Pca.Sweep.L34
import Pca.Sweep.C_Lid

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

variable (Γ) in
/-- A **convex** triangle `Δ(k, v, l)`: `a = ⟨k, v⟩`, `b = ⟨l, v⟩`, `k < l` on the sweep, and the
region bounded by the legs and `S[k, l]` has at `v` only the angle between the legs
(`φ a = α b`: the cell to the right of `a` turns at `v` into `α b`). -/
def IsConvexTri (a b : D) : Prop :=
  Γ.IsTri a b ∧ Γ.pos (Γ.crossingOf a) < Γ.pos (Γ.crossingOf b) ∧ Γ.φ a = Γ.α b

/-- **SH Lemma 3.6** (pp. 318-319): no hump and no convex triangle at all (empty or not). -/
theorem MinCE.lemma_3_6 (hΓ : Γ.MinCE) :
    (∀ a, ¬ Γ.IsHump a) ∧ ∀ a b, ¬ Γ.IsConvexTri a b := by
  have hzex : ∀ d : D, ∃ z, Γ.infStart = some z := fun d =>
    Option.isSome_iff_exists.1 (Γ.infStart_isSome ⟨d⟩)
  -- a vertex on the sweep is the start of a sweep dart `noC z t`, `t + infLen < period`
  have hfin : ∀ {z : D}, Γ.infStart = some z → ∀ {y : D}, Γ.Above y →
      Γ.IsFinVertex (Γ.crossingOf y) →
      ∃ t, t + Γ.infLen < period Γ.straight z ∧ y = Γ.σ (Γ.noC z t) := by
    intro z hz y hy hf
    obtain ⟨t, ht, hx⟩ := no_onSweep_noC hz hf.1
    exact ⟨t, (no_noC_fin hz ht).1 (hx ▸ hf), c_eq_σ_noC hz hy hx.symm⟩
  refine ⟨fun a ha => ?_, fun a b ⟨⟨hA, hB, hfa, hfb, _, hv, hvA, hab⟩, hpos, hconv⟩ => ?_⟩
  · obtain ⟨z, hz⟩ := hzex a
    have hαA : Γ.Above (Γ.α a) :=
      ⟨by rw [j_curve_α]; exact ha.1.1, by unfold Up; rw [no_side_α ha.1.1]; exact ha.1.2⟩
    obtain ⟨t1, ht1, h1⟩ := hfin hz ha.1 ha.2.1
    obtain ⟨t2, ht2, h2⟩ := hfin hz hαA ha.2.2
    rcases lt_trichotomy t1 t2 with h | rfl | h
    · exact c_hump_core hΓ hz h ht2 h1 h2
    · exact Γ.isSConf.α_ne a (h2.trans h1.symm)
    · exact c_hump_core hΓ hz h ht1 h2 (by rw [j_α_α]; exact h1)
  · obtain ⟨z, hz⟩ := hzex a
    obtain ⟨t1, ht1, h1⟩ := hfin hz hA hfa
    obtain ⟨t2, ht2, h2⟩ := hfin hz hB hfb
    have hlt : t1 < t2 := by
      rw [h1, h2, j_crossingOf_σ, j_crossingOf_σ, no_noC_pos hz (by omega),
        no_noC_pos hz (by omega)] at hpos
      omega
    exact c_tri_core hΓ hz hlt ht2 h1 h2 hv hvA.1 hab hconv

end SConf

end Pca.Sweep
