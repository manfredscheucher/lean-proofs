/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.9, Case 2 (pp. 321-322), graph language (package I)

"CASE 2. The curve `γ` intersects each of the legs `⟨i, v⟩` and `⟨i+1, v⟩` twice. Without loss of
generality, the curve `γ` hits leg `⟨i, v⟩` before leg `⟨i + 1, v⟩`, as shown in Figure 9. Again, we
eliminate `v` by untangling it. We form the arrangement `Γ'` in which the sweep must make progress
by finding an empty triangle.
As in Case 1, two faces that lose the vertex `v` gain no new vertices, one on the right and one on
the left, as shown in Figure 9. By choosing our arrangement in accordance with Lemma 3.5 (so that
curves go to infinity after crossing the sweep), we know that the curve `γ` cannot intersect the
sweep between its two intersection points with leg `⟨i, v⟩`. Since the face on the right has a
portion of `γ` on its boundary, it cannot become a triangle. Thus, the face on the left becomes an
empty triangle.
Here we know enough about the structure of `Γ` to completely eliminate a curve; this is a trickier
procedure than what we have done so far. Suppose that we remove the curve `γ(i+1)` from `Γ` as in
Figure 10. Only the face `F`, which is to the right of both `γ(i)` and `γ`, and adjacent to the vertex
`v`, can become an empty triangle, the other faces keep the same number of vertices. But we argued
above that the middle of `γ` does not intersect the sweep `c`, so no triangles are formed when we
remove `γ(i+1)`. This contradicts the minimality of our counterexample and proves that the face
above `[i, i + 1]` has the point `v` as a vertex."

Graph language: SH's use of Lemma 3.5 here ("`γ` cannot intersect the sweep between its two
intersection points with leg `⟨i, v⟩`") is `upper_arc` (`Pca/Sweep/Jordan.lean`): the part of `γ`
above `S` is one arc, its only vertices on the sweep are its two ends. The second removal is
`Removal {γ(i+1)}`; Lemma 3.3 and G1 give an operation of `Γ − γ(i+1)`, Lemmas 3.4, 3.8 exclude loop and
hump, so it is an empty triangle, contradicting the cell count. The untangling of the first
paragraph is only used to locate the face `F`; whether it is needed at all in graph language is
open point O5.

Route taken (package I, `doc/pca/sweep.md`, 3.9 Case 2):
1. `i_b3` (`I_Chord.lean`, chord and noncrossing lemmas of package E): the edges of `γ` inside the
   triangle join `u₁–w₂` and `u₂–w₁` (Figure 9), so the cell between the legs below `v` is the
   triangle `v, w₁, u₂`.
2. `case2_untangle` (package U): untangle `v` as in Case 1; `Γ'` is smaller, so it makes progress
   above a minus face of `Γ` with four corners (exactly as in Case 1).
3. `i_case_L`, `i_case_R` (`I_Cases.lean`): that face is `w₁, v, y, j` (resp. `u₂, v, j, m`), i.e.
   `γ` runs straight from `w₁` (resp. `u₂`) to the sweep. Removing the curve of the other leg
   (`γ(i+1)`, resp. `γ(i)`; SH's Figure 10) leaves an empty triangle above that face's edge whose
   legs are each crossed once by the removed curve and whose apex is hidden: Case 1 for that removal
   (`i_reduce`, `I_Red.lean`, via `lemma_3_9_case1`). This replaces SH's "the middle of `γ` does not
   intersect the sweep, so no triangles are formed".
-/
import Pca.Sweep.I_Cases

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- Case 2, step 2 (package U): the untangling of the apex `v` at the dart `b` from `v` along the
second leg (`cellOf b` is the cell between the legs below `v`), as in Case 1, with "not finished"
(`γ` still crosses both new curves above `S`) and "no loop can be taken" (every curve still meets
the sweep). Here each leg is crossed twice by `γ` (`k = 3` in `doc/pca/sweep.md`). -/
theorem MinCE.case2_untangle (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) (X : Γ.Removal {γ})
    {d' : X.D'} (h : X.Γ'.EmptyTriAt d') (hv : ¬ ApexVisible X d')
    (h₁ : X.hits (X.Γ'.σ d') = 2) (h₂ : X.hits (X.Γ'.φ (X.Γ'.σ d')) = 2) :
    ∃ U : Γ.Untangle (X.ι (X.Γ'.φ (X.Γ'.σ d'))), ¬ U.Γ'.Terminal ∧ ¬ U.Γ'.CanTakeLoop := by
  have h37 := hΓ.lemma_3_7 X (Or.inr h)
  have T := gk_tri X h h37
  rw [h₁, h₂] at T
  have hd : Γ.IsSweepDart (X.ι d') := f_ι_sweep X h.1.1
  have hfd : Γ.IsFinVertex (Γ.crossingOf (X.ι d')) :=
    (X.r_finVertex (X.Γ'.crossingOf d')).1 (f_finSeg_fin h.1).1
  have hfd' : Γ.IsFinVertex (Γ.crossingOf (Γ.α (X.ι d'))) := by
    rw [← h37]; exact (X.r_finVertex (X.Γ'.crossingOf (X.Γ'.α d'))).1 (f_finSeg_fin h.1).2
  exact (UHyp.of_gkTri T hd (by norm_num)).exists_untangle (by norm_num) hfd hfd'
    (fun c hc => hΓ.lemma_3_4 hc)

/-- **SH Lemma 3.9, Case 2** (pp. 321-322): impossible. -/
theorem MinCE.lemma_3_9_case2 (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) (X : Γ.Removal {γ})
    {d' : X.D'} (h : X.Γ'.EmptyTriAt d') (hv : ¬ ApexVisible X d')
    (h₁ : X.hits (X.Γ'.σ d') = 2) (h₂ : X.hits (X.Γ'.φ (X.Γ'.σ d')) = 2) : False := by
  have h37 := hΓ.lemma_3_7 X (Or.inr h)
  have T := gk_tri X h h37
  rw [h₁, h₂] at T
  have hb3 := i_b3 hΓ X h hv h₁ h₂
  set b := X.ι (X.Γ'.φ (X.Γ'.σ d')) with hb
  obtain ⟨U, hnt, hnl⟩ : ∃ U : Γ.Untangle b, ¬ U.Γ'.Terminal ∧ ¬ U.Γ'.CanTakeLoop :=
    hΓ.case2_untangle hγ X h hv h₁ h₂
  have hd : Γ.IsSweepDart (X.ι d') := f_ι_sweep X h.1.1
  -- the second leg is above the sweep
  have hAb : Γ.Above b := by
    refine X.r_above ⟨?_, ?_⟩
    · rw [X.isRemoval.curve, ← hb]; exact T.c2S ∘ (·.trans X.isRemoval.S)
    · unfold Up
      rw [j_cellOf_φ, j_cellOf_σ]; exact h.1.1.2
  -- `Γ` is stuck: no cell above a finite edge has two or three corners
  have hsz : ∀ e, Γ.IsFinSeg e → (Γ.upperCell e).size ≠ 2 ∧ (Γ.upperCell e).size ≠ 3 :=
    fun e he => ⟨fun h2 => hΓ.1.2 (Or.inl ⟨e, he, h2⟩),
      fun h3 => hΓ.1.2 (Or.inr (Or.inl ⟨e, he, h3⟩))⟩
  -- `Γ'` is smaller, hence not stuck, hence it makes progress by an empty hump or triangle
  have hlt : SizeLT U.Γ' Γ := Or.inl (by have := U.numVertices; omega)
  have hprog : U.Γ'.Progress := by
    by_contra hp
    exact hΓ.2 U.n' ⟨U.D', U.Γ'⟩ hlt ⟨hnt, hp⟩
  obtain ⟨d'', hd'', hs⟩ : ∃ d'', U.Γ'.IsFinSeg d'' ∧
      ((U.Γ'.upperCell d'').size = 2 ∨ (U.Γ'.upperCell d'').size = 3) := by
    rcases hprog with ⟨d'', hd''⟩ | ⟨d'', hd''⟩ | hl
    · exact ⟨d'', hd''.1, Or.inl hd''.2⟩
    · exact ⟨d'', hd''.1, Or.inr hd''.2⟩
    · exact absurd hl hnl
  obtain ⟨e, he, hψ⟩ := U.finSeg' d'' hd''
  rw [hψ] at hs
  have hUp : Γ.Up (Γ.upperCell e) := he.1.2
  have hse := hsz e he
  have h2f := i_two_le_size (Γ := Γ) (Γ.α e)
  change 2 ≤ (Γ.upperCell e).size at h2f
  by_cases hcL : Γ.upperCell e = Γ.cellOf (Γ.σ b)
  · have := U.size_L
    rw [← hcL] at this
    exact i_case_L hΓ T hb3 hAb he hcL (by rw [← hcL]; omega)
  by_cases hcR : Γ.upperCell e = Γ.cellOf (Γ.σ (Γ.σ (Γ.σ b)))
  · have := U.size_R
    rw [← hcR] at this
    exact i_case_R hΓ T hb3 hd he hcR (by rw [← hcR]; omega)
  by_cases hcM : Γ.upperCell e = Γ.cellOf b ∨ Γ.upperCell e = Γ.cellOf (Γ.σ (Γ.σ b))
  · have hm := U.size_merge
    have h2b := i_two_le_size (Γ := Γ) b
    have h2b' := i_two_le_size (Γ := Γ) (Γ.σ (Γ.σ b))
    rcases hcM with hc | hc
    · rw [← hc] at hm; omega
    · rw [U.merge, ← hc] at hm; omega
  have hso := U.size_other (Γ.upperCell e) hUp (by
    intro x hx hxb
    have hfx : Γ.cellOf x = Γ.upperCell e := Orbit.mem_darts.1 hx
    rcases no_mem_crossing hxb with rfl | rfl | rfl | rfl
    · exact hcM (Or.inl hfx.symm)
    · exact hcL hfx.symm
    · exact hcM (Or.inr hfx.symm)
    · exact hcR hfx.symm)
  omega

end SConf

end Pca.Sweep
