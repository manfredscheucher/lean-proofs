/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): the zipping lemma (FROS Lemma 2, `lemma:zipping`)

FROS: "Let `Q` be a lens bounded by the arcs `L` and `R`. If all the arcs of `Q` are transversal,
then, using only triangle flips, `L` can be swept towards `R` until the interior of `Q` does not
contain a vertex of the arrangement."

FROS prove it directly (Claim A: two arcs crossing twice cross in the same order; Claim B: the
digraph of the arcs, oriented from `L` to `R`, is acyclic; a source gives a triangle with an edge
on `L` that can be flipped). Graph language:

* `zipStep`: if `Q` has a vertex, there is a source triangle (a triangle of `Q` with a side on `L`
  whose apex is a vertex of `Q`) -- Claims A and B.
* `LensFlip`: a flip of such a triangle in the lens of two curves.
* `zipping` (Lemma 2 for the lens of two curves): a sequence of such flips ends with no vertex in
  `Q`. It is stated for the crossing form of transversality (`Marked.TwoTransversal`), which a
  source flip keeps literally (the flip moves `C_L` over the apex only; `C_R` is not a side of the
  triangle); all applications have the crossing form. Induction on the number of darts at vertices
  of `Q` (a source flip removes the apex, `isVertex_flip`).
-/
import Pca.FlipGraph.FlipCross
import Pca.FlipGraph.Trap
import Pca.FlipGraph.ClaimB

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- **Claims A and B of FROS Lemma 2**: if all arcs of the lens are transversal and `Q` contains a
vertex, there is a source triangle. Extra hypothesis `Sep` (no chord runs on a curve of `L` or
`R`; it excludes closed chords, for which `Transversal` is vacuous, `doc/pca/flipgraph.md` F-D6). -/
theorem Lens.zipStep {A : Arrangement n D} (Λ : Lens A) (hs : Λ.Sep) (ht : Λ.Transversal)
    (hv : ∃ x, Λ.IsVertex x) : ∃ d, Λ.SourceTri d := by
  obtain ⟨x, hx⟩ := Λ.exists_source hs ht hv
  exact Λ.sourceTri_of_source hs ht hx

namespace Marked

/-- One step of the zipping of the lens of two curves: the flip of a source triangle. -/
def LensFlip {C_L C_R : Fin n} (h : C_L ≠ C_R) (pL pR : Prop) (M M' : Marked n D) : Prop :=
  ∃ (d : D) (hT : M.A.IsTriangle (M.A.cellOf d)),
    (M.twoLens h pL pR).SourceTri d ∧ M' = M.flip d hT

/-- The marked cell lies in `TwoQ` depending on `pL`, `pR` only. -/
theorem twoQ_z_iff (M : Marked n D) (C_L C_R : Fin n) (pL pR : Prop) :
    M.TwoQ C_L C_R pL pR M.z ↔ ¬ pL ∧ ¬ pR := by
  unfold TwoQ; simp only [M.not_inside_z, false_iff]

/-- A chord dart of the lens of two curves is on neither curve. -/
theorem chord_curve {M : Marked n D} {C_L C_R : Fin n} {h : C_L ≠ C_R} {pL pR : Prop} {w : D}
    (hw : (M.twoLens h pL pR).Chord w) : M.A.curve w ≠ C_L ∧ M.A.curve w ≠ C_R :=
  ⟨fun hc => M.not_twoQ_α_of_L w hc hw.1 hw.2, fun hc => M.not_twoQ_α_of_R w hc hw.1 hw.2⟩

/-- The lens of two curves is separated: chords run on neither curve. -/
theorem twoLens_sep (M : Marked n D) {C_L C_R : Fin n} (h : C_L ≠ C_R) (pL pR : Prop) :
    (M.twoLens h pL pR).Sep := by
  rintro y z hy (hz | hz) e
  · exact (chord_curve hy).1 (e.trans hz.1)
  · exact (chord_curve hy).2 (e.trans hz.1)

/-- The vertices of the lens of two curves are the crossings not on `C_L`, `C_R` on the sides
`pL`, `pR`. -/
theorem twoLens_isVertex_iff (M : Marked n D) {C_L C_R : Fin n} (h : C_L ≠ C_R) (pL pR : Prop)
    (y : D) : (M.twoLens h pL pR).IsVertex (M.A.crossingOf y) ↔
      C_L ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) ∧
      C_R ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) ∧
      (M.CrossInside C_L (M.A.crossingOf y) ↔ pL) ∧ (M.CrossInside C_R (M.A.crossingOf y) ↔ pR) := by
  constructor
  · intro hv
    have hL : C_L ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := fun hm => by
      obtain ⟨w, hw, hwc⟩ := mem_image.1 hm
      exact (chord_curve (hv w hw)).1 hwc
    have hR : C_R ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := fun hm => by
      obtain ⟨w, hw, hwc⟩ := mem_image.1 hm
      exact (chord_curve (hv w hw)).2 hwc
    have hy := (hv y (Orbit.mem_darts.2 rfl)).1
    exact ⟨hL, hR, (M.crossInside_iff hL).trans hy.1, (M.crossInside_iff hR).trans hy.2⟩
  · rintro ⟨hL, hR, iL, iR⟩ w hw
    have hwx : M.A.crossingOf w = M.A.crossingOf y := Orbit.mem_darts.1 hw
    have hcL : M.A.curve w ≠ C_L := fun hc =>
      hL (by rw [← hwx, ← hc]; exact M.A.mem_curves_crossingOf w)
    have hcR : M.A.curve w ≠ C_R := fun hc =>
      hR (by rw [← hwx, ← hc]; exact M.A.mem_curves_crossingOf w)
    have tq : M.TwoQ C_L C_R pL pR (M.A.cellOf w) :=
      ⟨(M.crossInside_iff (hwx ▸ hL)).symm.trans (hwx ▸ iL),
        (M.crossInside_iff (hwx ▸ hR)).symm.trans (hwx ▸ iR)⟩
    exact ⟨tq, (M.twoQ_α_of_ne w hcL hcR).2 tq⟩

/-- **A source flip** in the lens of two curves keeps the crossing form of transversality and
removes exactly the apex from the vertices of `Q`. -/
theorem isVertex_flip (M : Marked n D) {C_L C_R : Fin n} (h : C_L ≠ C_R) {pL pR : Prop}
    (hz : ¬ M.TwoQ C_L C_R pL pR M.z) {d : D} (hs : (M.twoLens h pL pR).SourceTri d)
    (hT : M.A.IsTriangle (M.A.cellOf d)) (ht : M.TwoTransversal C_L C_R pL pR) :
    (M.flip d hT).TwoTransversal C_L C_R pL pR ∧
      (∀ y, ((M.flip d hT).twoLens h pL pR).IsVertex ((M.flip d hT).A.crossingOf y) →
        (M.twoLens h pL pR).IsVertex (M.A.crossingOf y) ∧
          M.A.crossingOf y ≠ M.A.crossingOf (M.A.φ (M.A.φ d))) := by
  obtain ⟨⟨hdc, hdq⟩, -, hv⟩ := hs
  have hzT : M.A.cellOf d ≠ M.z := fun he => hz (he ▸ hdq)
  have hv' := (M.twoLens_isVertex_iff h pL pR _).1 hv
  -- `C_R` is not a side of the triangle
  have noR : ¬ M.HasSideOn C_R (M.A.cellOf d) := by
    rintro ⟨w, hw, hwc⟩
    rcases (Arrangement.tri_mem_iff hT).1 (Orbit.mem_darts.1 hw) with rfl | rfl | rfl
    · exact h (hdc.symm.trans hwc)
    · have hm : M.A.α (M.A.φ d) ∈ (M.A.crossingOf (M.A.φ (M.A.φ d))).darts := by
        rw [Orbit.mem_darts]; exact (M.A.crossingOf_φ _).symm
      exact (chord_curve (hv _ hm)).2 (by rw [M.A.curve_α]; exact hwc)
    · exact (chord_curve (hv _ (Orbit.mem_darts.2 rfl))).2 hwc
  have hasL : M.HasSideOn C_L (M.A.cellOf d) := ⟨d, M.A.mem_darts_cellOf_self d, hdc⟩
  -- the corners of the triangle: two on `C_L`, and the apex
  have hcorner : ∀ y, M.A.IsCorner d y →
      C_L ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf y) ∨
        M.A.crossingOf y = M.A.crossingOf (M.A.φ (M.A.φ d)) := by
    intro y hy
    have hy' : M.A.crossingOf y ∈ Arrangement.Cell.corners M.A (M.A.cellOf d) := hy
    rw [Arrangement.corners_tri hT, mem_insert, mem_insert, mem_singleton] at hy'
    rcases hy' with e | e | e
    · left; rw [e, ← hdc]; exact M.A.mem_curves_crossingOf d
    · left; rw [e, M.A.crossingOf_φ, ← hdc]; exact M.A.mem_curves_end d
    · right; exact e
  have apexCorner : M.A.IsCorner d (M.A.φ (M.A.φ d)) := by
    show M.A.crossingOf _ ∈ Arrangement.Cell.corners M.A (M.A.cellOf d)
    rw [Arrangement.corners_tri hT]
    exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  -- the interior status after the flip
  have stR : ∀ y, C_R ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) →
      ((M.flip d hT).CrossInside C_R (M.A.crossingOf y) ↔ M.CrossInside C_R (M.A.crossingOf y)) :=
    fun y hy => by
      rw [crossInside_flip M hT hzT y hy]
      simp only [noR, and_false, not_false_eq_true, iff_true]
  have stL : ∀ y, C_L ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) →
      ((M.flip d hT).CrossInside C_L (M.A.crossingOf y) ↔
        (M.CrossInside C_L (M.A.crossingOf y) ↔ ¬ M.A.IsCorner d y)) := fun y hy => by
    rw [crossInside_flip M hT hzT y hy]
    simp only [hasL, and_true]
  refine ⟨fun c hcL hcR => ?_, fun y hy => ?_⟩
  · have tL : ∀ x : (M.flip d hT).A.Crossing,
        Arrangement.Crossing.curves (M.flip d hT).A x = {c, C_L} →
        ((M.flip d hT).CrossInside C_R x ↔ M.CrossInside C_R x) ∧
          Arrangement.Crossing.curves M.A x = {c, C_L} := by
      intro x hx
      obtain ⟨y, rfl⟩ := x.exists_mk
      have hx' : Arrangement.Crossing.curves M.A (M.A.crossingOf y) = {c, C_L} := hx
      refine ⟨stR y ?_, hx'⟩
      rw [hx', mem_insert, mem_singleton]
      rintro (e | e)
      · exact hcR e.symm
      · exact h e.symm
    have tR : ∀ x : (M.flip d hT).A.Crossing,
        Arrangement.Crossing.curves (M.flip d hT).A x = {c, C_R} →
        ((M.flip d hT).CrossInside C_L x ↔ M.CrossInside C_L x) ∧
          Arrangement.Crossing.curves M.A x = {c, C_R} := by
      intro x hx
      obtain ⟨y, rfl⟩ := x.exists_mk
      have hx' : Arrangement.Crossing.curves M.A (M.A.crossingOf y) = {c, C_R} := hx
      have hnL : C_L ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := by
        rw [hx', mem_insert, mem_singleton]
        rintro (e | e)
        · exact hcL e.symm
        · exact h e
      have hnc : ¬ M.A.IsCorner d y := fun hc => by
        rcases hcorner y hc with hm | e
        · exact hnL hm
        · exact hv'.2.1 (by rw [← e, hx']; simp)
      refine ⟨?_, hx'⟩
      change (M.flip d hT).CrossInside C_L (M.A.crossingOf y) ↔ M.CrossInside C_L (M.A.crossingOf y)
      rw [stL y hnL]
      simp only [hnc, not_false_eq_true, iff_true]
    rcases ht c hcL hcR with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨fun x hx => (tL x hx).1.trans (h1 x (tL x hx).2),
        fun x hx => (tR x hx).1.trans (h2 x (tR x hx).2)⟩
    · right
      exact ⟨fun x hx => fun e => h1 x (tL x hx).2 ((tL x hx).1.symm.trans e),
        fun x hx => fun e => h2 x (tR x hx).2 ((tR x hx).1.symm.trans e)⟩
  · obtain ⟨hL, hR, iL, iR⟩ := ((M.flip d hT).twoLens_isVertex_iff h pL pR y).1 hy
    change C_L ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) at hL
    change C_R ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) at hR
    change (M.flip d hT).CrossInside C_L (M.A.crossingOf y) ↔ pL at iL
    change (M.flip d hT).CrossInside C_R (M.A.crossingOf y) ↔ pR at iR
    have hnc : ¬ M.A.IsCorner d y := fun hc => by
      rcases hcorner y hc with hm | e
      · exact hL hm
      · have := (stL y hL).symm.trans iL
        simp only [hc, not_true_eq_false, iff_false] at this
        rw [e] at this
        exact prop_aux3 hv'.2.2.1 this
    rw [stL y hL] at iL
    simp only [hnc, not_false_eq_true, iff_true] at iL
    refine ⟨(M.twoLens_isVertex_iff h pL pR y).2 ⟨hL, hR, iL, (stR y hR).symm.trans iR⟩, ?_⟩
    intro e
    exact hnc (by show M.A.crossingOf y ∈ _; rw [e]; exact apexCorner)

/-- **FROS Lemma 2 (zipping)** for the lens `Q` of two curves `C_L`, `C_R` (bounded: the marked
cell is not in `Q`): if all arcs of `Q` are transversal (crossing form), flips of source
triangles (triangles in `Q` with a side on `L ⊂ C_L` and apex in `Q`) sweep `L` towards `R` until
`Q` contains no vertex. The lens stays transversal. -/
theorem zipping (M : Marked n D) {C_L C_R : Fin n} (h : C_L ≠ C_R) (pL pR : Prop)
    (hz : ¬ M.TwoQ C_L C_R pL pR M.z) (ht : M.TwoTransversal C_L C_R pL pR) :
    ∃ N, Relation.ReflTransGen (LensFlip h pL pR) M N ∧
      (∀ x, ¬ (N.twoLens h pL pR).IsVertex x) ∧ N.TwoTransversal C_L C_R pL pR := by
  classical
  let μ : Marked n D → ℕ := fun N =>
    (univ.filter (fun y : D => (N.twoLens h pL pR).IsVertex (N.A.crossingOf y))).card
  suffices H : ∀ m (M : Marked n D), μ M = m → ¬ M.TwoQ C_L C_R pL pR M.z →
      M.TwoTransversal C_L C_R pL pR → ∃ N, Relation.ReflTransGen (LensFlip h pL pR) M N ∧
        (∀ x, ¬ (N.twoLens h pL pR).IsVertex x) ∧ N.TwoTransversal C_L C_R pL pR from
    H _ M rfl hz ht
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro M hm hz ht
  by_cases hv : ∃ x, (M.twoLens h pL pR).IsVertex x
  · obtain ⟨d, hs⟩ := (M.twoLens h pL pR).zipStep (M.twoLens_sep h pL pR) (M.twoLens_transversal h ht) hv
    have hT := hs.2.1
    obtain ⟨ht', hsub⟩ := M.isVertex_flip h hz hs hT ht
    have hz' : ¬ (M.flip d hT).TwoQ C_L C_R pL pR (M.flip d hT).z := by
      rw [twoQ_z_iff] at hz ⊢; exact hz
    have hlt : μ (M.flip d hT) < μ M := by
      apply card_lt_card
      refine ⟨fun y hy => ?_, fun hsub' => ?_⟩
      · rw [mem_filter] at hy ⊢
        exact ⟨mem_univ _, (hsub y hy.2).1⟩
      · have hm' := hsub' (mem_filter.2 ⟨mem_univ (M.A.φ (M.A.φ d)), hs.2.2⟩)
        exact (hsub _ (mem_filter.1 hm').2).2 rfl
    obtain ⟨N, hN, hv', ht''⟩ := ih _ (hm ▸ hlt) (M.flip d hT) rfl hz' ht'
    exact ⟨N, Relation.ReflTransGen.head ⟨d, hT, hs, rfl⟩ hN, hv', ht''⟩
  · exact ⟨M, Relation.ReflTransGen.refl, fun x hx => hv ⟨x, hx⟩, ht⟩

/-- A lens flip is a flip of the triangle graph (the triangle is not the marked cell). -/
theorem LensFlip.flipStep {C_L C_R : Fin n} {h : C_L ≠ C_R} {pL pR : Prop} {M M' : Marked n D}
    (hz : ¬ M.TwoQ C_L C_R pL pR M.z) (hf : LensFlip h pL pR M M') : FlipStep M M' := by
  obtain ⟨d, hT, ⟨⟨-, hq⟩, -, -⟩, rfl⟩ := hf
  exact ⟨d, hT, fun h' => hz (h' ▸ hq), rfl⟩

end Marked

end Pca.FlipGraph
