/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): parallel curves and mimicking a flip sequence (proof of FROS Theorem 3)

FROS: "We say that two pseudocircles `C` and `C'` are parallel in `𝒜` if every vertex of
`𝒜 − {C, C'}` lies in `(int C ∩ int C') ∪ (ext C ∩ ext C')`." [...] "Next consider the arrangement
`𝒜' := 𝒜 − {C'}`. By the induction hypothesis, `𝒜'` can be transformed into a cylindrical
arrangement by a finite sequence of triangle flips. We now carefully mimic this flip sequence on
`𝒜`, while maintaining that `C` and `C'` are parallel. Suppose that a triangle `T` in `𝒜'` is
flipped. If none of the edges of `T` belongs to `C`, we can directly apply this triangle flip also
in `𝒜`. If one of the edges `e` of `T` belongs to `C` and `e` is crossed by `C'`, then the digon `D`
is located along `e`. In this case, we apply two triangle flips to `C'` so that the digon is
transferred to one of the two neighboring edges of `C` [...], obtaining that `e` is not crossed by
`C'` (without changing `𝒜'`). Finally, if `e` is not crossed by `C'`, then we apply the according
triangle flip twice, namely, once for `C` and once for `C'`."

Graph language:

* `Par M C C'`: the digon `D` (sides on `C` and `C'`, in `ext C ∩ int C'`) and no crossing of two
  other curves in `int C ∩ ext C'` (with the digon, `ext C ∩ int C'` is the digon, so this is FROS'
  "parallel").
* `MimicRel`: `M` has `C`, `C'` parallel, `M'` is `M − C'` (`deleteOn`, literally), and the marked
  cell of `M'` contains the marked cell of `M` (through a kept dart).
* `mimic_step`: one flip of `M − C'` is mimicked by flips of `M` (FROS' three cases).
-/
import Pca.FlipGraph.Delete
import Pca.FlipGraph.MimicFlip
import Pca.FlipGraph.MimicAgree
import Pca.FlipGraph.ParZip
import Pca.FlipGraph.MimicWalk
import Pca.FlipGraph.MimicCut
import Pca.FlipGraph.MimicDigonMove

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n m : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- The mimicking relation between `M` (curves `C`, `C'` parallel) and `M' = M − C'`. -/
structure MimicRel (C C' : Fin (m + 1)) (hm : 2 ≤ m) (K : D → Prop) [DecidablePred K]
    (M : Marked (m + 1) D) (M' : Marked m {d // K d}) : Prop where
  hK : ∀ d, K d ↔ Keep M.A C' d
  par : M.Par C C'
  del : M'.A = M.A.deleteOn C' hm K hK
  mark : ∃ w : {d // K d}, M.A.cellOf w.val = M.z ∧ M'.A.cellOf w = M'.z

/-- Start of the mimicking: with `C`, `C'` parallel (and at least three curves), the marked cell
has a kept dart, so `M − C'` is a marked arrangement related to `M`. -/
theorem exists_mimicRel {C C' : Fin (m + 1)} (hm : 2 ≤ m) (M : Marked (m + 1) D)
    (hpar : M.Par C C') :
    ∃ M' : Marked m {d // Keep M.A C' d}, MimicRel C C' hm (Keep M.A C') M M' := by
  have hCC := hpar.1
  obtain ⟨w, hw, hwK⟩ : ∃ w, M.A.cellOf w = M.z ∧ Keep M.A C' w := by
    by_contra hno
    push Not at hno
    have hon : ∀ y, M.A.cellOf y = M.z → C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf y) :=
      fun y hy => by
        by_contra h; exact hno y hy ((keep_iff_not_mem y).2 h)
    obtain ⟨y0, hy0⟩ := M.z.exists_mk
    change M.A.cellOf y0 = M.z at hy0
    obtain ⟨y, hy, hyC'⟩ : ∃ y, M.A.cellOf y = M.z ∧ M.A.curve y ≠ C' := by
      by_cases h : M.A.curve y0 = C'
      · exact ⟨M.A.φ y0, by rw [M.A.cellOf_φ, hy0], by rw [← h]; exact M.A.curve_φ_ne _⟩
      · exact ⟨y0, hy0, h⟩
    have hs := hon y hy
    have he : C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α y)) := by
      have := hon (M.A.φ y) (by rw [M.A.cellOf_φ, hy]); rwa [M.A.φ_apply, M.A.crossingOf_σ] at this
    have hst := M.walk_status hyC' hs he
    obtain ⟨e2, he2y, he2C', he2C⟩ : ∃ e2, e2 ≠ M.A.curve y ∧ e2 ≠ C' ∧
        (M.A.curve y = C ∨ e2 = C) := by
      by_cases h : M.A.curve y = C
      · obtain ⟨c, hc1, hc2⟩ := exists_third hm C' C; exact ⟨c, h ▸ hc1, hc2, Or.inl h⟩
      · exact ⟨C, Ne.symm h, hCC, Or.inr rfl⟩
    have hc2 := Walk.card_flipsOn M.A (Ne.symm he2y)
    obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < (Walk.flipsOn M.A e2 y).card)
    rw [Walk.mem_flipsOn] at hi
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero, Perm.one_apply, (M.A.mem_curves_end_iff hyC').1 he] at hi
      exact he2C' hi.2.symm
    have hcu : M.A.curve ((M.A.straight ^ i) y) = M.A.curve y := Walk.curve_pow M.A y i
    have hu : M.Inside C' (M.A.cellOf ((M.A.straight ^ i) y)) := by
      rw [hst i (by omega) hi.1, hy]; exact M.not_inside_z C'
    refine M.par_outside_C'_end hpar (by rw [hcu]; exact hyC') ?_ ?_ hu
    · rw [M.A.curves_crossingOf, M.A.curve_α, hcu, hi.2]
      rcases he2C with h | h
      · rw [h]; exact mem_insert_self _ _
      · rw [h]; exact mem_insert_of_mem (mem_singleton_self _)
    · rw [M.A.mem_curves_end_iff (by rw [hcu]; exact hyC'), hi.2]; exact he2C'
  exact ⟨⟨M.A.deleteOn C' hm (Keep M.A C') (fun _ => Iff.rfl),
    (M.A.deleteOn C' hm (Keep M.A C') (fun _ => Iff.rfl)).cellOf ⟨w, hwK⟩⟩,
    ⟨fun _ => Iff.rfl, hpar, rfl, ⟨w, hwK⟩, hw, rfl⟩⟩

/-- The interiors in `M − C'` are those of `M` (through kept darts). -/
theorem MimicRel.inside_iff {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} {M' : Marked m {d // K d}} (hr : MimicRel C C' hm K M M') (c : Fin m)
    (w : {d // K d}) :
    M'.Inside c (M'.A.cellOf w) ↔ M.Inside (C'.succAbove c) (M.A.cellOf w.val) := by
  obtain ⟨A', z'⟩ := M'
  obtain ⟨hK, -, hdel, w0, hw0, hw0'⟩ := hr
  dsimp only at hdel hw0' ⊢
  subst hdel
  obtain ⟨s, hs⟩ := M.A.exists_isSide (C'.succAbove c)
  obtain ⟨s', hs', hss⟩ := deleteOn_isSide M.A C' hm K hK hs
  rw [Marked.inside_iff ⟨_, z'⟩ hs', M.inside_iff hs]
  dsimp only
  rw [← hw0', hss, hss, hw0]

/-- FROS, first case: "If none of the edges of `T` belongs to `C`, we can directly apply this
triangle flip also in `𝒜`." -/
theorem mimic_noC {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} {M' : Marked m {d // K d}} (hr : MimicRel C C' hm K M M')
    {d : {d // K d}} (hT : M'.A.IsTriangle (M'.A.cellOf d)) (hz : M'.A.cellOf d ≠ M'.z)
    (hC : ∀ b, M'.A.cellOf b = M'.A.cellOf d → M.A.curve b.val ≠ C) :
    ∃ N, Reach M N ∧ MimicRel C C' hm K N ⟨M'.A.flip d hT, Arrangement.flipCellEquiv hT M'.z⟩ := by
  obtain ⟨A', z'⟩ := M'
  obtain ⟨hK, hpar, hdel, w, hw, hw'⟩ := hr
  dsimp only at hdel hw' hT hz hC ⊢
  subst hdel
  set δ := M.A.deleteOn C' hm K hK
  -- (1) the corners of `T` are not on `C`, its sides are not crossed by `C'`
  have hno := fun b hb => noC_no_cross hK hpar (d := d) hC b hb
  -- (2) `T` is a triangle of `M` with the same darts, all kept
  obtain ⟨hTM, hKc⟩ := tri_of_del hK hT (fun b hb => (hno b hb).2)
  have hσ : ∀ x, (δ.σ x).val = M.A.σ x.val := fun x => deleteOn_σ M.A C' hm K hK x
  have hα : ∀ b, δ.cellOf b = δ.cellOf d → (δ.α b).val = M.A.α b.val := fun b hb => (hno b hb).2
  have hcell := agree_cell_iff hσ hT hα
  -- `T` is not the marked cell of `M`: the marked kept dart would be a dart of `T`
  have hdz : M.A.cellOf d.val ≠ M.z := fun h => hz (by rw [← hw', (hcell w).2 (hw.trans h.symm)])
  have hcor : ∀ y, M.A.cellOf y = M.A.cellOf d.val →
      C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) ∧
        C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := fun y hy =>
    ⟨(hno ⟨y, hKc y hy⟩ ((hcell ⟨y, hKc y hy⟩).2 hy)).1, ((hK y).1 (hKc y hy)).2⟩
  -- (3) the flip in `M` (P2: no corner on `C'`)
  have hK' : ∀ e, K e ↔ Keep (M.A.flip d.val hTM) C' e := hK
  obtain ⟨hd, hT', heq⟩ := deleteOn_flip_of_no_corner M.A C' hm K hK hTM
    (fun y hy => (hcor y (M.A.cellOf_eq_iff.2 (M.A.mem_darts_cellOf.1 hy)).symm).2) hK'
  refine ⟨M.flip d.val hTM, Relation.ReflTransGen.single ⟨d.val, hTM, hdz, rfl⟩,
    ⟨hK', par_flip_away M hpar hTM hdz hcor, heq.symm, ?_⟩⟩
  -- (5) the marked dart moves to `flipG` in both arrangements
  refine ⟨Arrangement.flipG δ d w, ?_, ?_⟩
  · change (M.A.flip d.val hTM).cellOf _ = Arrangement.flipCellEquiv hTM M.z
    rw [agree_flipG hσ hT hα hKc w, ← Arrangement.flipCellEquiv_cellOf, hw]
  · rw [← hw']; rfl

/-- FROS, second case: "If one of the edges `e` of `T` belongs to `C` and `e` is crossed by `C'`,
then the digon `D` is located along `e`. In this case, we apply two triangle flips to `C'` so that
the digon is transferred to one of the two neighboring edges of `C` [...], obtaining that `e` is not
crossed by `C'` (without changing `𝒜'`)." Here `b` is the dart of `T` on `e`; "`e` is crossed by
`C'`" means that `α` of `M − C'` at `b` is not `α` of `M`. -/
theorem mimic_move_digon {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} {M' : Marked m {d // K d}} (hr : MimicRel C C' hm K M M')
    {d : {d // K d}} (hT : M'.A.IsTriangle (M'.A.cellOf d)) (hz : M'.A.cellOf d ≠ M'.z)
    {b : {d // K d}} (hb : M'.A.cellOf b = M'.A.cellOf d) (hbC : M.A.curve b.val = C)
    (hx : (M'.A.α b).val ≠ M.A.α b.val) :
    ∃ N, Reach M N ∧ MimicRel C C' hm K N M' ∧ N.A.curve = M.A.curve ∧
      (M'.A.α b).val = N.A.α b.val := by
  obtain ⟨A', z'⟩ := M'
  obtain ⟨hK, hpar, hdel, w, hw, hw'⟩ := hr
  dsimp only at hdel hw' hT hz hb hx ⊢
  subst hdel
  obtain ⟨hCC, ⟨a, hD, ha, hφa, hout, hin⟩, -⟩ := id hpar
  obtain ⟨N, hN, hK', hdelN, hparN, hcN, ⟨w', hw'K, hw'z, hw'δ⟩, hαN⟩ :=
    digon_move hm hK hpar hD ha hφa hout hin w.2 hw
  refine ⟨N, hN, ⟨hK', hparN, hdelN.symm, ⟨⟨w', hw'K⟩, hw'z, ?_⟩⟩, hcN, ?_⟩
  · rw [← hw']; exact hw'δ
  -- the run of `b` passes the two corners of the digon (`k = 2`)
  have hbk := (hK _).1 b.2
  obtain ⟨k, hk, hkC, hkα⟩ := deleteOn_α M.A C' hm K hK b
  have hk0 : k ≠ 0 := by
    rintro rfl; rw [pow_zero, Perm.one_apply] at hkα; exact hx hkα
  have h0 := hk 0 (by omega)
  rw [pow_zero, Perm.one_apply] at h0
  have hZ2 := digon_corner M.A hD rfl
  rw [ha, hφa] at hZ2
  have hZ1 := digon_corner M.A hD (M.A.cellOf_φ a)
  rw [ha, hφa, M.A.crossingOf_φ] at hZ1
  have haC' : M.A.curve a ≠ C' := by rw [ha]; exact hCC
  have hX0 := M.digon_X0 (by omega) haC' hZ2.2 hZ1.2
  have hX1 := (M.band_tri (by omega) hpar hD ha hφa hout hin).2.2
  have hk2 : ∀ (y : D), (M.A.straight ^ 2) b.val = y →
      C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α b.val)) →
      C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α (M.A.straight b.val))) →
      C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α y)) → k = 2 := by
    intro y hy e0 e1 e2
    rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with h | h | h
    · subst h; rw [pow_one] at hkC; exact absurd e1 hkC
    · exact h
    · exact absurd (hy ▸ hk 2 (by omega)) e2
  rcases M.par_CC'_dart hCC hD ha hφa hout hin (x := M.A.α b.val) (by rw [M.A.curve_α, hbC])
      h0 with h | h | h | h
  · exfalso; apply hbk.2; rw [← M.A.α_α b.val, h]; exact hZ1.2
  · -- `b = α (σ² a)`: the run is `b`, `a`, `straight a`
    have hs1 : M.A.straight b.val = a := by rw [M.A.straight_apply, h, M.A.σ_σ_σ_σ]
    have hs2 : (M.A.straight ^ 2) b.val = M.A.straight a := by
      rw [pow_two, Perm.mul_apply, hs1]
    have hk2' := hk2 _ hs2 (by rw [h, M.A.crossingOf_σσ]; exact hZ2.2) (by rw [hs1]; exact hZ1.2) hX0
    subst hk2'
    have hb' : b.val = M.A.α (M.A.σ (M.A.σ a)) := by rw [← h, M.A.α_α]
    rw [hkα, hs2, hb', ← hαN, N.A.α_α]
  · exfalso; apply hbk.2; rw [← M.A.α_α b.val, h, M.A.α_α]; exact hZ2.2
  · -- `b = α (straight a)`: the run is `b`, `α a`, `σ² a`
    have hs1 : M.A.straight b.val = M.A.α a := by rw [M.A.straight_apply, h, M.A.σ_σ_σ_σ]
    have hs2 : (M.A.straight ^ 2) b.val = M.A.σ (M.A.σ a) := by
      rw [pow_two, Perm.mul_apply, hs1, M.A.straight_α]
    have hk2' := hk2 _ hs2 (by rw [h, M.A.crossingOf_σσ]; exact hZ1.2)
      (by rw [hs1, M.A.α_α]; exact hZ2.2) hX1
    subst hk2'
    rw [hkα, hs2, ← hαN]
    congr 1
    rw [← M.A.α_α b.val, h]; rfl

/-- Third case when `T` is a triangle of `M` (no side of `T` is crossed by `C'`): flip `T` (P2;
`T` is outside `C`, its apex enters `int C ∩ ext C'`), then zip the lens `int C ∩ ext C'` (flips
of triangles with a side on `C'`, P1; for the single new vertex this is FROS' flip "for `C'`").
Decision F-D12 (`doc/pca/flipgraph.md`). -/
theorem mimic_tri_core {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} (hK : ∀ e, K e ↔ Keep M.A C' e) (hCC : C ≠ C') {a : D}
    (hD : M.A.IsDigon (M.A.cellOf a)) (ha : M.A.curve a = C) (hφa : M.A.curve (M.A.φ a) = C')
    (hout : ¬ M.Inside C (M.A.cellOf a)) (hin : M.Inside C' (M.A.cellOf a))
    (hinC : ∀ v, C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf v) →
      C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf v) → M.Inside C (M.A.cellOf v))
    (houtC' : ∀ v, C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf v) →
      C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf v) → ¬ M.Inside C' (M.A.cellOf v))
    {A' : Arrangement m {d // K d}} (hdel : A' = M.A.deleteOn C' hm K hK)
    {z' : A'.Cell} (w : {d // K d}) (hw : M.A.cellOf w.val = M.z)
    (hw' : A'.cellOf w = z') {d : {d // K d}} (hT : A'.IsTriangle (A'.cellOf d))
    (hz : A'.cellOf d ≠ z')
    (hα : ∀ b, A'.cellOf b = A'.cellOf d → (A'.α b).val = M.A.α b.val) :
    ∃ N, Reach M N ∧ MimicRel C C' hm K N ⟨A'.flip d hT, Arrangement.flipCellEquiv hT z'⟩ := by
  subst hdel
  set δ := M.A.deleteOn C' hm K hK
  obtain ⟨hTM, hKc⟩ := tri_of_del hK hT hα
  have hσ : ∀ x, (δ.σ x).val = M.A.σ x.val := fun x => deleteOn_σ M.A C' hm K hK x
  have hcell := agree_cell_iff hσ hT hα
  have hdz : M.A.cellOf d.val ≠ M.z := fun h => hz (by rw [← hw', (hcell w).2 (hw.trans h.symm)])
  -- the crossings at the corners of `T` are not on `C'`
  have hcor : ∀ y, M.A.IsCorner d.val y → C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := mem_image.1 hy
    rw [← hty]
    exact ((hK t).1 (hKc t (M.A.cellOf_eq_iff.2 (M.A.mem_darts_cellOf.1 ht)).symm)).2
  have hK' : ∀ e, K e ↔ Keep (M.A.flip d.val hTM) C' e := hK
  obtain ⟨hd, hT', heq⟩ := deleteOn_flip_of_no_corner M.A C' hm K hK hTM
    (fun y hy => ((hK y).1 (hKc y (M.A.cellOf_eq_iff.2 (M.A.mem_darts_cellOf.1 hy)).symm)).2) hK'
  have hw₁ : (M.flip d.val hTM).A.cellOf (Arrangement.flipG δ d w).val = (M.flip d.val hTM).z := by
    change (M.A.flip d.val hTM).cellOf _ = Arrangement.flipCellEquiv hTM M.z
    rw [agree_flipG hσ hT hα hKc w, ← Arrangement.flipCellEquiv_cellOf, hw]
  -- the digon is untouched
  have hna : ¬ M.A.IsCorner d.val a := fun h =>
    hcor a h (by rw [← hφa]; exact (digon_corner M.A hD rfl).2)
  have hnαa : ¬ M.A.IsCorner d.val (M.A.α a) := fun h =>
    hcor _ h (by
      have := (digon_corner M.A hD (M.A.cellOf_φ a)).2
      rwa [hφa, M.A.φ_apply, M.A.crossingOf_σ] at this)
  obtain ⟨hD₁, hφ₁, hC₁⟩ := digon_keep_flip M hTM hdz hD hna hnαa C
  have hC'₁ := (digon_keep_flip M hTM hdz hD hna hnαa C').2.2
  -- the lens `int C ∩ ext C'` is transversal after the flip (only corners of `T` change status)
  have htr : (M.flip d.val hTM).TwoTransversal C' C False True := by
    intro c hc1 hc2
    left
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨y, rfl⟩ := x.exists_mk
      change Arrangement.Crossing.curves M.A (M.A.crossingOf y) = {c, C'} at hx
      have hC : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := by
        rw [hx]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hc2, hCC⟩
      have hy' : C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := by
        rw [hx]; exact mem_insert_of_mem (mem_singleton_self _)
      change (M.flip d.val hTM).CrossInside C (M.A.crossingOf y) ↔ True
      rw [crossInside_flip M hTM hdz y hC, M.crossInside_iff hC]
      have : ¬ M.A.IsCorner d.val y := fun h => hcor y h hy'
      simp only [this, false_and, not_false_eq_true, iff_true]
      exact hinC y hy' hC
    · obtain ⟨y, rfl⟩ := x.exists_mk
      change Arrangement.Crossing.curves M.A (M.A.crossingOf y) = {c, C} at hx
      have hC' : C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := by
        rw [hx]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hc1, Ne.symm hCC⟩
      have hy' : C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := by
        rw [hx]; exact mem_insert_of_mem (mem_singleton_self _)
      change (M.flip d.val hTM).CrossInside C' (M.A.crossingOf y) ↔ False
      rw [crossInside_flip M hTM hdz y hC', M.crossInside_iff hC']
      have hns : ¬ M.HasSideOn C' (M.A.cellOf d.val) := by
        rintro ⟨t, ht, htC⟩
        exact ((hK t).1 (hKc t (M.A.cellOf_eq_iff.2 (M.A.mem_darts_cellOf.1 ht)).symm)).1 htC
      simp only [hns, and_false, not_false_eq_true, iff_true, iff_false]
      exact houtC' y hy' hC'
  -- zip the lens
  have hzQ : ¬ (M.flip d.val hTM).TwoQ C' C False True (M.flip d.val hTM).z := by
    rw [Marked.twoQ_z_iff]; simp
  obtain ⟨N, hN, hv, -⟩ := (M.flip d.val hTM).zipping (Ne.symm hCC) False True hzQ htr
  have hφa₁ : (M.flip d.val hTM).A.curve ((M.flip d.val hTM).A.φ a) = C' := by
    rw [hφ₁]; exact hφa
  have hparN := par_of_zipping_CC (Ne.symm hCC) _ hD₁ ha hφa₁ (by rwa [hC₁]) (by rwa [hC'₁]) hN hv
  obtain ⟨hKN, hdelN, hwN⟩ := zip_del (Ne.symm hCC) hm hN hK' (Arrangement.flipG δ d w).2 hw₁
  refine ⟨N, (Relation.ReflTransGen.single ⟨d.val, hTM, hdz, rfl⟩).trans (reach_of_zip _ hN),
    ⟨hKN, hparN, ?_, Arrangement.flipG δ d w, hwN, ?_⟩⟩
  · rw [hdelN]; exact heq.symm
  · rw [← hw']; rfl

theorem mimic_tri {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} {M' : Marked m {d // K d}} (hr : MimicRel C C' hm K M M')
    {d : {d // K d}} (hT : M'.A.IsTriangle (M'.A.cellOf d)) (hz : M'.A.cellOf d ≠ M'.z)
    (hα : ∀ b, M'.A.cellOf b = M'.A.cellOf d → (M'.A.α b).val = M.A.α b.val) :
    ∃ N, Reach M N ∧ MimicRel C C' hm K N ⟨M'.A.flip d hT, Arrangement.flipCellEquiv hT M'.z⟩ := by
  obtain ⟨A', z'⟩ := M'
  obtain ⟨hK, hpar, hdel, w, hw, hw'⟩ := hr
  dsimp only at hdel hw' hT hz hα ⊢
  subst hdel
  obtain ⟨hCC, ⟨a, hD, ha, hφa, hout, hin⟩, -⟩ := id hpar
  exact mimic_tri_core hK hCC hD ha hφa hout hin (fun v h1 h2 => M.par_inside_C hpar h1 h2)
    (fun v h1 h2 => M.par_outside_C' hpar h1 h2) rfl w hw hw' hT hz hα

/-- Third case when a side of `T` is crossed by `C'` (`T` lies in `int C`, its apex in `int C'`):
first the flip "for `C'`" (the triangle `T₂` cut off from `T` by `C'`, a triangle of `M` by
`tri_cut`; P1), after which `T` is a triangle of the arrangement with the same `α` on its darts,
then `mimic_tri_core` (the flip "for `C`" and the zipping, which does nothing here). -/
theorem mimic_side_C_cross {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} {M' : Marked m {d // K d}} (hr : MimicRel C C' hm K M M')
    {d : {d // K d}} (hT : M'.A.IsTriangle (M'.A.cellOf d)) (hz : M'.A.cellOf d ≠ M'.z)
    {b : {d // K d}} (hb : M'.A.cellOf b = M'.A.cellOf d) (hbC : M.A.curve b.val = C)
    (hx : (M'.A.α b).val = M.A.α b.val)
    (hc : ¬ ∀ b, M'.A.cellOf b = M'.A.cellOf d → (M'.A.α b).val = M.A.α b.val) :
    ∃ N, Reach M N ∧ MimicRel C C' hm K N ⟨M'.A.flip d hT, Arrangement.flipCellEquiv hT M'.z⟩ := by
  obtain ⟨A', z'⟩ := M'
  obtain ⟨hK, hpar, hdel, w, hw, hw'⟩ := hr
  dsimp only at hdel hw' hT hz hb hx hc ⊢
  subst hdel
  set δ := M.A.deleteOn C' hm K hK with hδ
  obtain ⟨hCC, ⟨a, hD, ha, hφa, hout, hin⟩, hX⟩ := id hpar
  have hTb : δ.IsTriangle (δ.cellOf b) := by rw [hb]; exact hT
  have hqb : δ.φ (δ.φ (δ.φ b)) = b := Arrangement.tri_φφφ hTb
  have hKv : ∀ x : {d // K d}, Keep M.A C' x.val := fun x => (hK _).1 x.2
  have hcv : ∀ x y : {d // K d}, δ.curve x ≠ δ.curve y → M.A.curve x.val ≠ M.A.curve y.val :=
    fun x y h e => h (C'.succAbove_right_injective (by
      rw [deleteOn_curve M.A C' hm K hK, deleteOn_curve M.A C' hm K hK, e]))
  set p := δ.φ b with hpdef
  set q := δ.φ p with hqdef
  have nbp : M.A.curve b.val ≠ M.A.curve p.val := hcv _ _ (δ.curve_φ_ne b).symm
  have npq : M.A.curve p.val ≠ M.A.curve q.val := hcv _ _ (δ.curve_φ_ne p).symm
  have nqb : M.A.curve q.val ≠ M.A.curve b.val := by
    have := hcv _ _ (δ.curve_φ_ne q).symm; rwa [hqb] at this
  have hpC' : M.A.curve p.val ≠ C' := (hKv p).1
  have hqC' : M.A.curve q.val ≠ C' := (hKv q).1
  -- the darts of `T`
  have hcellT : ∀ y, δ.cellOf y = δ.cellOf d → y = b ∨ y = p ∨ y = q := by
    intro y hy
    have : y ∈ orbitFinset δ.φ b :=
      mem_orbitFinset.2 (δ.mem_darts_cellOf.1 (by rw [hb, ← hy]; exact δ.mem_darts_cellOf_self y))
    rwa [orbitFinset_three hqb, mem_insert, mem_insert, mem_singleton] at this
  -- the runs of the sides `p` and `q`
  obtain ⟨kp, hkp, hkpC, hpα⟩ := deleteOn_α M.A C' hm K hK p
  obtain ⟨kq, hkq, hkqC, hqα⟩ := deleteOn_α M.A C' hm K hK q
  have pval : p.val = M.A.φ b.val :=
    deleteOn_φ_val (hK := hK) (by rw [← hx]; exact (δ.α b).2)
  have qval : q.val = M.A.φ ((M.A.straight ^ kp) p.val) := by
    show M.A.σ (δ.α p).val = _; rw [hpα, M.A.φ_apply]
  have bval : b.val = M.A.φ ((M.A.straight ^ kq) q.val) := by
    conv_lhs => rw [← hqb]
    show M.A.σ (δ.α q).val = _; rw [hqα, M.A.φ_apply]
  have hcU_p : M.A.cellOf p.val = M.A.cellOf b.val := by rw [pval, M.A.cellOf_φ]
  have hcU_q : M.A.cellOf ((M.A.straight ^ kq) q.val) = M.A.cellOf b.val := by
    rw [bval, M.A.cellOf_φ]
  have hbC' : C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf b.val) := by
    rw [← hbC]; exact M.A.mem_curves_crossingOf _
  have hUout : ¬ M.Inside C' (M.A.cellOf b.val) := M.par_outside_C' hpar hbC' (hKv b).2
  -- curves at the end of a step on `C'`
  have hend : ∀ (y : {d // K d}) (i : ℕ),
      C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y.val))) →
      C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y.val))) ∨
        M.A.curve y.val = C := by
    intro y i h
    rw [M.A.curves_crossingOf, M.A.curve_α, Walk.curve_pow, mem_insert, mem_singleton] at h ⊢
    rcases h with h | h
    · exact absurd h.symm (hKv y).1
    by_cases hyC : M.A.curve y.val = C
    · exact Or.inr hyC
    · left
      rintro (h' | h')
      · exact hyC h'.symm
      · exact hCC (h'.trans h.symm)
  -- `T` lies inside `C` (else no side is crossed)
  have hUin : M.Inside C (M.A.cellOf b.val) := by
    by_contra hUC
    have kp0 : kp = 0 := by
      by_contra h0
      have h1 := hkp 0 (by omega)
      rw [pow_zero, Perm.one_apply] at h1
      have h2 : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α p.val)) := by
        rcases hend p 0 (by rwa [pow_zero, Perm.one_apply]) with h | h
        · rwa [pow_zero, Perm.one_apply] at h
        · exact absurd (h.trans hbC.symm) (Ne.symm nbp)
      apply hUC
      rw [← hcU_p, ← M.A.cellOf_φ, M.A.φ_apply]
      exact M.par_inside_C hpar (by rwa [M.A.crossingOf_σ]) (by rwa [M.A.crossingOf_σ])
    have kq0 : kq = 0 := by
      by_contra h0
      have h1 := hkq (kq - 1) (by omega)
      rw [← M.A.crossingOf_straight, ← Walk.pow_succ_apply, Nat.sub_add_cancel (by omega)] at h1
      have h2 : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf ((M.A.straight ^ kq) q.val)) := by
        rcases hend q (kq - 1) (by rwa [← M.A.crossingOf_straight, ← Walk.pow_succ_apply,
            Nat.sub_add_cancel (by omega)]) with h | h
        · rwa [← M.A.crossingOf_straight, ← Walk.pow_succ_apply, Nat.sub_add_cancel (by omega)] at h
        · exact absurd (h.trans hbC.symm) nqb
      exact hUC (by rw [← hcU_q]; exact M.par_inside_C hpar h1 h2)
    apply hc
    intro y hy
    rcases hcellT y hy with rfl | rfl | rfl
    · exact hx
    · rw [hpα, kp0, pow_zero, Perm.one_apply]
    · rw [hqα, kq0, pow_zero, Perm.one_apply]
  -- the sides `p`, `q` are crossed by `C'` once each
  have hX2 : M.A.crossingOf (M.A.α ((M.A.straight ^ kp) p.val)) = M.A.crossingOf q.val := by
    rw [qval, M.A.φ_apply, M.A.crossingOf_σ]
  have hX2C : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf q.val) := by
    rw [qval, M.A.curves_crossingOf_φ, Walk.curve_pow, ← qval, mem_insert, mem_singleton]
    rintro (h | h)
    · exact nbp (hbC.trans h)
    · exact nqb (h.symm.trans hbC.symm)
  have kp1 : kp = 1 := M.k_one_out hpar hpC' (hKv p).2 hkp hkpC (by rw [hX2]; exact hX2C)
    (by rw [hcU_p]; exact hUin) (by rw [hcU_p]; exact hUout)
  subst kp1
  rw [pow_one] at hpα qval hX2
  have hs₀C : M.Inside C (M.A.cellOf (M.A.straight p.val)) := by
    rw [M.inside_straight, hcU_p]
    have h1 := hkp 0 (by omega)
    rw [pow_zero, Perm.one_apply] at h1
    rw [(M.A.mem_curves_end_iff hpC').1 h1]
    simp [hUin, Ne.symm hCC]
  have hqIn : M.Inside C' (M.A.cellOf q.val) := by
    have hcq : M.A.cellOf q.val = M.A.cellOf (M.A.straight p.val) := by rw [qval, M.A.cellOf_φ]
    have h := hX (M.A.crossingOf q.val) hX2C (hKv q).2
    rw [M.crossInside_iff hX2C, M.crossInside_iff (hKv q).2, hcq] at h
    rw [hcq]; by_contra h'; exact h ⟨hs₀C, h'⟩
  have kq1 : kq = 1 := M.k_one_in hqC' (hKv q).2 hkq hqIn (by rw [hcU_q]; exact hUout)
  subst kq1
  rw [pow_one] at hqα bval hcU_q
  -- the triangle `T₂ = (s₀, q, φ q)` cut off by `C'` (`tri_cut`)
  have hY₁ : C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.straight p.val)) := by
    rw [M.A.crossingOf_straight]; have := hkp 0 (by omega); rwa [pow_zero, Perm.one_apply] at this
  have hY₂ : C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.straight q.val)) := by
    rw [M.A.crossingOf_straight]; have := hkq 0 (by omega); rwa [pow_zero, Perm.one_apply] at this
  have htri : M.A.φ (M.A.φ q.val) = M.A.straight p.val :=
    Chain.tri_cut pval.symm rfl qval.symm rfl bval.symm hY₁ hY₂ (hKv b).2 (hKv p).2 (hKv q).2
  have hφq : M.A.curve (M.A.φ q.val) = C' := by
    rw [M.A.φ_apply]
    exact (M.A.mem_curves_end_iff hqC').1 (by have := hkq 0 (by omega); rwa [pow_zero, Perm.one_apply] at this)
  have hcs₀ : M.A.curve (M.A.straight p.val) = M.A.curve p.val := M.A.curve_straight _
  have h3 : M.A.φ (M.A.φ (M.A.φ (M.A.straight p.val))) = M.A.straight p.val := by rw [← qval, htri]
  have hT2 : M.A.IsTriangle (M.A.cellOf (M.A.straight p.val)) := by
    refine Lens.isTriangle_of h3 (fun h => (hKv q).2 ?_) (fun h => ?_)
    · rw [qval, h]; exact hY₁
    · rw [← qval] at h; rw [← h, hφq] at hcs₀; exact hpC' hcs₀.symm
  have hcs₀q : M.A.cellOf (M.A.straight p.val) = M.A.cellOf q.val := by rw [qval, M.A.cellOf_φ]
  have hz2 : M.A.cellOf (M.A.straight p.val) ≠ M.z := fun h =>
    M.not_inside_z C' (by rw [← h, hcs₀q]; exact hqIn)
  -- the corners of `T₂`: `Y₁`, `X₂`, `Y₂` (no `C`)
  have hcor2 : ∀ y, M.A.IsCorner (M.A.straight p.val) y →
      C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) ∧
        (C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf y) ∨
          M.A.crossingOf y = M.A.crossingOf q.val) := by
    intro y hy
    obtain ⟨t, ht, hty⟩ := mem_image.1 hy
    have ht' : t ∈ orbitFinset M.A.φ (M.A.straight p.val) := mem_orbitFinset.2 (M.A.mem_darts_cellOf.1 ht)
    rw [orbitFinset_three h3, mem_insert, mem_insert, mem_singleton, ← qval] at ht'
    rw [← hty]
    rcases ht' with rfl | rfl | rfl
    · refine ⟨?_, Or.inl hY₁⟩
      rw [← htri, M.A.curves_crossingOf_φ, htri, hφq, hcs₀, mem_insert, mem_singleton]
      rintro (h | h)
      · exact hCC h
      · exact nbp (hbC.trans h)
    · exact ⟨hX2C, Or.inr rfl⟩
    · refine ⟨?_, Or.inl (by rw [M.A.curves_crossingOf_φ, hφq]; simp)⟩
      rw [M.A.curves_crossingOf_φ, hφq, mem_insert, mem_singleton]
      rintro (h | h)
      · exact nqb (h.symm.trans hbC.symm)
      · exact hCC h
  have hnc : ∀ y, C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf y) →
      ¬ M.A.IsCorner (M.A.straight p.val) y := fun y h hc => (hcor2 y hc).1 h
  have hmemC : ∀ y, M.A.curve y = C → C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf y) :=
    fun y h => by rw [← h]; exact M.A.mem_curves_crossingOf y
  have hna : ¬ M.A.IsCorner (M.A.straight p.val) a := hnc a (hmemC a ha)
  have hnαa : ¬ M.A.IsCorner (M.A.straight p.val) (M.A.α a) :=
    hnc _ (hmemC _ (by rw [M.A.curve_α]; exact ha))
  obtain ⟨hD₁, hφ₁, hC₁⟩ := digon_keep_flip M hT2 hz2 hD hna hnαa C
  have hC'₁ := (digon_keep_flip M hT2 hz2 hD hna hnαa C').2.2
  -- the flip of `T₂` (P1: `M − C'` does not change)
  have hside : ∃ y ∈ (M.A.cellOf (M.A.straight p.val)).darts, M.A.curve y = C' :=
    ⟨M.A.φ q.val, by rw [hcs₀q, ← M.A.cellOf_φ]; exact M.A.mem_darts_cellOf_self _, hφq⟩
  have hK₁ : ∀ e, K e ↔ Keep (M.flip (M.A.straight p.val) hT2).A C' e := hK
  have hdel₁ := deleteOn_flip_of_side M.A C' hm K hK hT2 hside hK₁
  have hT2side : ¬ M.HasSideOn C (M.A.cellOf (M.A.straight p.val)) := by
    rintro ⟨t, ht, htC⟩
    have ht' : t ∈ orbitFinset M.A.φ (M.A.straight p.val) := mem_orbitFinset.2 (M.A.mem_darts_cellOf.1 ht)
    rw [orbitFinset_three h3, mem_insert, mem_insert, mem_singleton, ← qval] at ht'
    rcases ht' with rfl | rfl | rfl
    · exact nbp (hbC.trans (htC.symm.trans hcs₀))
    · exact nqb (htC.trans hbC.symm)
    · exact hCC (htC.symm.trans hφq)
  have hinC₁ : ∀ v, C' ∈ Arrangement.Crossing.curves (M.flip (M.A.straight p.val) hT2).A
      ((M.flip (M.A.straight p.val) hT2).A.crossingOf v) →
      C ∉ Arrangement.Crossing.curves (M.flip (M.A.straight p.val) hT2).A
        ((M.flip (M.A.straight p.val) hT2).A.crossingOf v) →
      (M.flip (M.A.straight p.val) hT2).Inside C ((M.flip (M.A.straight p.val) hT2).A.cellOf v) := by
    intro v h1 h2
    have h1' : C' ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf v) := h1
    have h2' : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf v) := h2
    rw [← (M.flip (M.A.straight p.val) hT2).crossInside_iff h2]
    change (M.flip (M.A.straight p.val) hT2).CrossInside C (M.A.crossingOf v)
    rw [crossInside_flip M hT2 hz2 v h2', M.crossInside_iff h2']
    simp only [hT2side, and_false, not_false_eq_true, iff_true]
    exact M.par_inside_C hpar h1' h2'
  have houtC'₁ : ∀ v, C ∈ Arrangement.Crossing.curves (M.flip (M.A.straight p.val) hT2).A
      ((M.flip (M.A.straight p.val) hT2).A.crossingOf v) →
      C' ∉ Arrangement.Crossing.curves (M.flip (M.A.straight p.val) hT2).A
        ((M.flip (M.A.straight p.val) hT2).A.crossingOf v) →
      ¬ (M.flip (M.A.straight p.val) hT2).Inside C' ((M.flip (M.A.straight p.val) hT2).A.cellOf v) := by
    intro v h1 h2
    have h1' : C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf v) := h1
    have h2' : C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf v) := h2
    rw [← (M.flip (M.A.straight p.val) hT2).crossInside_iff h2]
    change ¬ (M.flip (M.A.straight p.val) hT2).CrossInside C' (M.A.crossingOf v)
    rw [crossInside_flip M hT2 hz2 v h2', M.crossInside_iff h2']
    simp only [hnc v h1', false_and, not_false_eq_true, iff_true]
    exact M.par_outside_C' hpar h1' h2'
  -- the marked kept dart is not a corner of `T₂`
  have hwnc : ¬ M.A.IsCorner (M.A.straight p.val) w.val := by
    intro hc'
    rcases (hcor2 _ hc').2 with h | h
    · exact (hKv w).2 h
    · apply M.not_inside_z C'
      rw [← hw, ← M.crossInside_iff (hKv w).2, h, M.crossInside_iff (hKv q).2]
      exact hqIn
  have hw₁ : (M.flip (M.A.straight p.val) hT2).A.cellOf w.val =
      (M.flip (M.A.straight p.val) hT2).z := by
    change (M.A.flip _ hT2).cellOf w.val = Arrangement.flipCellEquiv hT2 M.z
    rw [Arrangement.flip_cellOf_of_not_corner hT2 hwnc, hw]
  -- after the flip of `T₂`, `T` is a triangle of the arrangement with the same `α` on its darts
  have hα₁ : ∀ y, δ.cellOf y = δ.cellOf d →
      (δ.α y).val = (M.flip (M.A.straight p.val) hT2).A.α y.val := by
    intro y hy
    change _ = Arrangement.flipα hT2 y.val
    rw [Arrangement.flipα_apply]
    rcases hcellT y hy with rfl | rfl | rfl
    · rw [Arrangement.flipρ_of_not_corner hT2 (hnc _ (hmemC _ hbC)),
        Arrangement.flipρ_of_not_corner hT2 (hnc _ (hmemC _ (by rw [M.A.curve_α]; exact hbC)))]
      exact hx
    · have hpX : C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf p.val) := by
        rw [pval, M.A.φ_apply, M.A.crossingOf_σ]; exact hmemC _ (by rw [M.A.curve_α]; exact hbC)
      have hαp : M.A.α p.val = M.A.σ (M.A.σ (M.A.straight p.val)) := by
        rw [M.A.straight_apply, M.A.σ_σ_σ_σ]
      rw [Arrangement.flipρ_of_not_corner hT2 (hnc _ hpX), hαp,
        Arrangement.flipρ_σσ_of_mem hT2 rfl]
      exact hpα
    · have hbX : C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α (M.A.straight q.val))) := by
        have : M.A.crossingOf b.val = M.A.crossingOf (M.A.α (M.A.straight q.val)) := by
          rw [bval, M.A.φ_apply, M.A.crossingOf_σ]
        rw [← this]; exact hmemC _ hbC
      rw [Arrangement.flipρ_of_mem hT2 hcs₀q.symm, Arrangement.flipρ_of_not_corner hT2 (hnc _ hbX)]
      exact hqα
  obtain ⟨N, hN, hrel⟩ := mimic_tri_core (M := M.flip (M.A.straight p.val) hT2) hK₁ hCC hD₁ ha
    (by rw [hφ₁]; exact hφa) (by rwa [hC₁]) (by rwa [hC'₁]) hinC₁ houtC'₁ hdel₁.symm w hw₁ hw' hT hz
    hα₁
  exact ⟨N, (Relation.ReflTransGen.single ⟨_, hT2, hz2, rfl⟩).trans hN, hrel⟩

/-- FROS, third case: "if `e` is not crossed by `C'`, then we apply the according triangle flip
twice, namely, once for `C` and once for `C'`." -/
theorem mimic_side_C {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} {M' : Marked m {d // K d}} (hr : MimicRel C C' hm K M M')
    {d : {d // K d}} (hT : M'.A.IsTriangle (M'.A.cellOf d)) (hz : M'.A.cellOf d ≠ M'.z)
    {b : {d // K d}} (hb : M'.A.cellOf b = M'.A.cellOf d) (hbC : M.A.curve b.val = C)
    (hx : (M'.A.α b).val = M.A.α b.val) :
    ∃ N, Reach M N ∧ MimicRel C C' hm K N ⟨M'.A.flip d hT, Arrangement.flipCellEquiv hT M'.z⟩ := by
  by_cases hα : ∀ b, M'.A.cellOf b = M'.A.cellOf d → (M'.A.α b).val = M.A.α b.val
  · exact mimic_tri hr hT hz hα
  · exact mimic_side_C_cross hr hT hz hb hbC hx hα

/-- **Mimicking one flip of `M − C'`** by a sequence of flips of `M` (FROS' three cases), keeping
`C` and `C'` parallel. -/
theorem mimic_step {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} {M' M'' : Marked m {d // K d}} (hr : MimicRel C C' hm K M M')
    (hs : FlipStep M' M'') : ∃ N, Reach M N ∧ MimicRel C C' hm K N M'' := by
  obtain ⟨d, hT, hz, rfl⟩ := hs
  by_cases hC : ∃ b, M'.A.cellOf b = M'.A.cellOf d ∧ M.A.curve b.val = C
  · obtain ⟨b, hb, hbC⟩ := hC
    by_cases hx : (M'.A.α b).val = M.A.α b.val
    · exact mimic_side_C hr hT hz hb hbC hx
    · obtain ⟨N, hN, hrN, hcN, hxN⟩ := mimic_move_digon hr hT hz hb hbC hx
      obtain ⟨N', hN', hrN'⟩ := mimic_side_C hrN hT hz hb ((congrFun hcN _).trans hbC) hxN
      exact ⟨N', hN.trans hN', hrN'⟩
  · push Not at hC
    exact mimic_noC hr hT hz hC

theorem mimic_reach {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} {M' M'' : Marked m {d // K d}} (hr : MimicRel C C' hm K M M')
    (hs : Reach M' M'') : ∃ N, Reach M N ∧ MimicRel C C' hm K N M'' := by
  induction hs with
  | refl => exact ⟨M, Relation.ReflTransGen.refl, hr⟩
  | tail _ hst ih =>
    obtain ⟨N, hN, hr'⟩ := ih
    obtain ⟨N', hN', hr''⟩ := mimic_step hr' hst
    exact ⟨N', hN.trans hN', hr''⟩

/-- **End of the mimicking**: if `M − C'` is cylindrical and `C`, `C'` are parallel, then `M` is
cylindrical. -/
theorem MimicRel.cylindrical {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} {M' : Marked m {d // K d}} (hr : MimicRel C C' hm K M M')
    (hc : M'.Cylindrical) : M.Cylindrical := by
  obtain ⟨p', hp'⟩ := hc
  obtain ⟨w, rfl⟩ := p'.exists_mk
  have hall : ∀ C0, C0 ≠ C' → M.Inside C0 (M.A.cellOf w.val) := fun C0 h0 => by
    have := (hr.inside_iff (predLabel C' hm C0) w).1 (hp' _)
    rwa [succAbove_predLabel h0] at this
  have hCC := hr.par.1
  have hfC := hall C hCC
  by_cases hin : M.Inside C' (M.A.cellOf w.val)
  · exact ⟨_, fun C0 => if h : C0 = C' then h ▸ hin else hall C0 h⟩
  by_cases hside : ∃ y, M.A.cellOf y = M.A.cellOf w.val ∧ M.A.curve y = C'
  · -- across a side on `C'`
    obtain ⟨y, hy, hyC⟩ := hside
    refine ⟨M.A.cellOf (M.A.α y), fun C0 => ?_⟩
    rw [M.inside_α C0 y, hy]
    by_cases h : C0 = C'
    · subst h; simp [hin, hyC]
    · simp [hall C0 h, hyC, Ne.symm h]
  exfalso
  push Not at hside
  set f := M.A.cellOf w.val with hf
  -- every corner of `f` is on `C` (else it is a crossing in `int C ∩ ext C'`)
  have hend : ∀ y, M.A.cellOf y = f → M.A.curve y = C ∨ M.A.curve (M.A.φ y) = C := by
    intro y hy
    have hX : Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.φ y)) =
        {M.A.curve y, M.A.curve (M.A.φ y)} := by
      rw [M.A.φ_apply, M.A.crossingOf_σ, M.A.curves_crossingOf, M.A.curve_α]
    by_contra hno
    push Not at hno
    have hφf : M.A.cellOf (M.A.φ y) = f := by rw [M.A.cellOf_φ, hy]
    have h1 : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.φ y)) := by
      rw [hX]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hno.1, Ne.symm hno.2⟩
    have h2 : C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.φ y)) := by
      rw [hX]; simp only [mem_insert, mem_singleton, not_or]
      exact ⟨Ne.symm (hside y hy), Ne.symm (hside _ hφf)⟩
    apply hr.par.2.2 (M.A.crossingOf (M.A.φ y)) h1 h2
    rw [M.crossInside_iff h1, M.crossInside_iff h2, hφf]
    exact ⟨hfC, hin⟩
  -- a side of `f` on a curve `c ≠ C`; both its ends are on `C`
  obtain ⟨y, hy, hyC⟩ : ∃ y, M.A.cellOf y = f ∧ M.A.curve y ≠ C := by
    by_cases h : M.A.curve w.val = C
    · exact ⟨M.A.φ w.val, M.A.cellOf_φ _, by rw [← h]; exact M.A.curve_φ_ne _⟩
    · exact ⟨w.val, rfl, h⟩
  have hyC' := hside y hy
  have he : C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α y)) := by
    rcases hend y hy with h | h
    · exact absurd h hyC
    · rw [M.A.curves_crossingOf, M.A.curve_α, ← M.A.φ_apply, h]; exact mem_insert_of_mem (mem_singleton_self _)
  have hs : C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := by
    have hxy : M.A.φ (M.A.φ.symm y) = y := M.A.φ.apply_symm_apply y
    have hx : M.A.cellOf (M.A.φ.symm y) = f := by rw [← hy, ← M.A.cellOf_φ, hxy]
    rcases hend _ hx with h | h
    · have := M.A.mem_curves_end (M.A.φ.symm y)
      rwa [h, ← M.A.crossingOf_σ, ← M.A.φ_apply, hxy] at this
    · rw [hxy] at h; exact absurd h hyC
  -- `c` crosses `C'` on its arc outside `C`, but crossings of `C'` are inside `C`
  have hst := M.walk_status hyC hs he
  have hc2 := Walk.card_flipsOn M.A hyC'
  obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < (Walk.flipsOn M.A C' y).card)
  rw [Walk.mem_flipsOn] at hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, Perm.one_apply, (M.A.mem_curves_end_iff hyC).1 he] at hi
    exact hCC hi.2
  have hcu : M.A.curve ((M.A.straight ^ i) y) = M.A.curve y := Walk.curve_pow M.A y i
  have hu : ¬ M.Inside C (M.A.cellOf ((M.A.straight ^ i) y)) := by
    rw [hst i (by omega) hi.1, hy]; exact not_not.2 hfC
  refine hu (M.par_inside_C_end hr.par (by rw [hcu]; exact hyC) ?_ ?_)
  · rw [M.A.mem_curves_end_iff (by rw [hcu]; exact hyC')]; exact hi.2
  · rw [M.A.mem_curves_end_iff (by rw [hcu]; exact hyC), hi.2]; exact Ne.symm hCC

end Pca.FlipGraph
