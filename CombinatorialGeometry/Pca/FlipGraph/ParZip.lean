/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): zipping the lens `int C ∩ ext C'` keeps the digon and ends with `C`, `C'`
parallel

Moved from `Thm3.lean` (used there for the digon case and in `Mimic.lean` to restore `Par` after
a flip of the mimicking).
-/
import Pca.FlipGraph.Zip
import Pca.FlipGraph.MimicPar

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- A lens flip does not touch the digon `D ⊂ ext C ∩ int C'` (its corners are crossings of `C`
and `C'`, which are not corners of the flipped triangle). -/
theorem lensFlip_keeps_digon {C C' : Fin n} (h : C' ≠ C) {N : Marked n D} {a d : D}
    (hT : N.A.IsTriangle (N.A.cellOf d)) (hsrc : (N.twoLens h False True).SourceTri d)
    (hD : N.A.IsDigon (N.A.cellOf a)) (ha : N.A.curve a = C) (hφa : N.A.curve (N.A.φ a) = C')
    (hout : ¬ N.Inside C (N.A.cellOf a)) (hin : N.Inside C' (N.A.cellOf a)) :
    let N' := N.flip d hT
    N'.A.IsDigon (N'.A.cellOf a) ∧ N'.A.φ a = N.A.φ a ∧ ¬ N'.Inside C (N'.A.cellOf a) ∧
      N'.Inside C' (N'.A.cellOf a) := by
  intro N'
  obtain ⟨⟨hdC, hdQ⟩, -, hv⟩ := hsrc
  have hφφ : N.A.φ (N.A.φ a) = a := N.A.φ_φ_of_digon hD
  -- chord darts are not on `C` or `C'`
  have hchord : ∀ y, (N.twoLens h False True).Chord y → N.A.curve y ≠ C ∧ N.A.curve y ≠ C' := by
    rintro y ⟨h1, h2⟩
    exact ⟨fun hy => N.not_twoQ_α_of_R y hy h1 h2, fun hy => N.not_twoQ_α_of_L y hy h1 h2⟩
  have hapex : ∀ y, N.A.crossingOf y = N.A.crossingOf (N.A.φ (N.A.φ d)) →
      N.A.curve y ≠ C ∧ N.A.curve y ≠ C' := fun y hy =>
    hchord y (hv y (Orbit.mem_darts.2 hy))
  -- the two corners of the digon lie on `C` and `C'`
  have hcor : ∀ x, x = N.A.crossingOf a ∨ x = N.A.crossingOf (N.A.α a) →
      C ∈ Arrangement.Crossing.curves N.A x ∧ C' ∈ Arrangement.Crossing.curves N.A x := by
    rintro x (rfl | rfl)
    · refine ⟨ha ▸ N.A.mem_curves_crossingOf a, ?_⟩
      rw [← hφφ, N.A.φ_apply, N.A.crossingOf_σ, ← hφa, ← N.A.curve_α]
      exact N.A.mem_curves_crossingOf _
    · refine ⟨by rw [← ha, ← N.A.curve_α]; exact N.A.mem_curves_crossingOf _, ?_⟩
      rw [← N.A.crossingOf_σ, ← N.A.φ_apply, ← hφa]; exact N.A.mem_curves_crossingOf _
  have hnot : ∀ x, x = N.A.crossingOf a ∨ x = N.A.crossingOf (N.A.α a) →
      x ∉ Arrangement.Cell.corners N.A (N.A.cellOf d) := by
    intro x hx hxc
    obtain ⟨hC, hC'⟩ := hcor x hx
    rw [Arrangement.corners_tri hT] at hxc
    simp only [mem_insert, mem_singleton] at hxc
    rcases hxc with rfl | rfl | rfl
    · -- the start of `d`: the other curve there is the curve of `φ² d`, a chord curve
      rw [N.A.curves_crossingOf, mem_insert, mem_singleton, Arrangement.curve_σ_tri hT] at hC
      rcases hC with h1 | h1
      · exact h (hdC.symm.trans h1.symm)
      · exact (hapex _ rfl).1 h1.symm
    · -- the end of `d`: the other curve is the curve of `φ d`, which ends at the apex
      rw [N.A.φ_apply, N.A.crossingOf_σ, N.A.curves_crossingOf, mem_insert, mem_singleton,
        N.A.curve_α] at hC
      rcases hC with h1 | h1
      · exact h (hdC.symm.trans h1.symm)
      · have := (hapex (N.A.α (N.A.φ d)) (by
          rw [← N.A.crossingOf_σ (N.A.α (N.A.φ d)), ← N.A.φ_apply])).1
        apply this
        rw [N.A.curve_α]
        have e : N.A.curve (N.A.σ (N.A.α d)) = N.A.curve (N.A.φ d) := rfl
        rw [← e]; exact h1.symm
    · exact (hapex _ rfl).1 (by
        rw [N.A.curves_crossingOf, mem_insert, mem_singleton] at hC
        rcases hC with h1 | h1
        · exact h1.symm
        · exfalso
          rw [N.A.curves_crossingOf, mem_insert, mem_singleton] at hC'
          rcases hC' with h2 | h2
          · exact (hapex _ rfl).2 h2.symm
          · exact (hapex (N.A.σ (N.A.φ (N.A.φ d))) (N.A.crossingOf_σ _)).2 h2.symm)
  have hna : ¬ N.A.IsCorner d a := hnot _ (Or.inl rfl)
  have hnαa : ¬ N.A.IsCorner d (N.A.α a) := hnot _ (Or.inr rfl)
  have hdin : N.Inside C (N.A.cellOf d) := hdQ.2.2 trivial
  have hdz : N.A.cellOf d ≠ N.z := fun e => N.not_inside_z C (e ▸ hdin)
  have hgT : N.A.cellOf a ≠ N.A.cellOf d := fun e => hout (by rw [e]; exact hdin)
  have hcell : (N.A.flip d hT).cellOf a = Arrangement.flipCellEquiv hT (N.A.cellOf a) :=
    Arrangement.flip_cellOf_of_not_corner hT hna
  refine ⟨?_, Arrangement.flipφ_generic hT hna hnαa, ?_, ?_⟩
  · change Orbit.size ((N.A.flip d hT).cellOf a) = 2
    rw [hcell, Arrangement.flip_size_of_ne hT]
    · exact hD
    intro c hc
    have hcc : N.A.IsCorner d c := Arrangement.isCorner_of_mem hc
    have corner_of : ∀ y, N.A.crossingOf c = N.A.crossingOf y → N.A.IsCorner d y :=
      fun y e => by unfold Arrangement.IsCorner at hcc ⊢; rwa [← e]
    have hφ_cross : N.A.crossingOf (N.A.φ a) = N.A.crossingOf (N.A.α a) := by
      rw [N.A.φ_apply, N.A.crossingOf_σ]
    have hαφ_cross : N.A.crossingOf (N.A.α (N.A.φ a)) = N.A.crossingOf a := by
      rw [← N.A.crossingOf_σ, ← N.A.φ_apply, hφφ]
    constructor
    · intro e
      rcases two_cycle hφφ ((Arrangement.cellOf_eq_iff N.A).1 e) with e' | e'
      · exact hnαa (corner_of _ (by rw [← e', N.A.α_α]))
      · exact hna (corner_of _ (by rw [← hαφ_cross, ← e', N.A.α_α]))
    · intro e
      rcases two_cycle hφφ ((Arrangement.cellOf_eq_iff N.A).1 e) with e' | e'
      · exact hna (corner_of _ (by rw [← N.A.crossingOf_σσ c, e']))
      · exact hnαa (corner_of _ (by rw [← N.A.crossingOf_σσ c, e', hφ_cross]))
  · change ¬ (N.flip d hT).Inside C ((N.A.flip d hT).cellOf a)
    rw [hcell, flip_inside N hT hdz C]
    tauto
  · change (N.flip d hT).Inside C' ((N.A.flip d hT).cellOf a)
    rw [hcell, flip_inside N hT hdz C']
    tauto

/-- After zipping the lens `int C ∩ ext C'` (FROS: "expand `C'` until `C` and `C'` are parallel")
the digon is still there and `C`, `C'` are parallel. -/
theorem par_of_zipping' (M : Marked n D) {a : D} (hD : M.A.IsDigon (M.A.cellOf a))
    (hout : ¬ M.Inside (M.A.curve a) (M.A.cellOf a))
    (hin : M.Inside (M.A.curve (M.A.φ a)) (M.A.cellOf a))
    (h : M.A.curve (M.A.φ a) ≠ M.A.curve a) {N : Marked n D}
    (hN : Relation.ReflTransGen (Marked.LensFlip h False True) M N)
    (hv : ∀ x, ¬ (N.twoLens h False True).IsVertex x) :
    N.Par (M.A.curve a) (M.A.curve (M.A.φ a)) := by
  have key : N.A.IsDigon (N.A.cellOf a) ∧ N.A.φ a = M.A.φ a ∧ N.A.curve = M.A.curve ∧
      ¬ N.Inside (M.A.curve a) (N.A.cellOf a) ∧ N.Inside (M.A.curve (M.A.φ a)) (N.A.cellOf a) := by
    clear hv
    induction hN with
    | refl => exact ⟨hD, rfl, rfl, hout, hin⟩
    | tail _ hs ih =>
      obtain ⟨hD₁, hφ₁, hc₁, ho₁, hi₁⟩ := ih
      obtain ⟨d, hT, hsrc, rfl⟩ := hs
      obtain ⟨hD₂, hφ₂, ho₂, hi₂⟩ := lensFlip_keeps_digon h hT hsrc hD₁ (by rw [hc₁])
        (by rw [hφ₁, hc₁]) ho₁ hi₁
      exact ⟨hD₂, hφ₂.trans hφ₁, hc₁, ho₂, hi₂⟩
  obtain ⟨hD₁, hφ₁, hc₁, ho₁, hi₁⟩ := key
  refine ⟨h.symm, ⟨a, hD₁, by rw [hc₁], by rw [hφ₁, hc₁], ho₁, hi₁⟩, fun x hx hx' hxin => ?_⟩
  apply hv x
  obtain ⟨y, rfl⟩ := x.exists_mk
  -- every dart at `x` has both cells inside `C` and outside `C'`
  have hall : ∀ w, N.A.crossingOf w = N.A.crossingOf y →
      N.TwoQ (M.A.curve (M.A.φ a)) (M.A.curve a) False True (N.A.cellOf w) := by
    intro w hw
    change M.A.curve a ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf y) at hx
    change M.A.curve (M.A.φ a) ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf y) at hx'
    change N.CrossInside _ (N.A.crossingOf y) ∧ ¬ N.CrossInside _ (N.A.crossingOf y) at hxin
    rw [← hw] at hx hx' hxin
    exact ⟨by rw [iff_false, ← N.crossInside_iff hx']; exact hxin.2,
      by rw [iff_true, ← N.crossInside_iff hx]; exact hxin.1⟩
  intro w hw
  rw [Orbit.mem_darts] at hw
  change N.A.crossingOf w = N.A.crossingOf y at hw
  refine ⟨hall w hw, ?_⟩
  rw [← N.A.cellOf_σ]
  exact hall _ (by rw [N.A.crossingOf_σ, hw])


/-- `par_of_zipping'` with the curves named. -/
theorem par_of_zipping_CC {C C' : Fin n} (h : C' ≠ C) (M : Marked n D) {a : D}
    (hD : M.A.IsDigon (M.A.cellOf a)) (ha : M.A.curve a = C) (hφa : M.A.curve (M.A.φ a) = C')
    (hout : ¬ M.Inside C (M.A.cellOf a)) (hin : M.Inside C' (M.A.cellOf a)) {N : Marked n D}
    (hN : Relation.ReflTransGen (Marked.LensFlip h False True) M N)
    (hv : ∀ x, ¬ (N.twoLens h False True).IsVertex x) : N.Par C C' := by
  subst ha; subst hφa; exact par_of_zipping' M hD hout hin h hN hv

/-- Zipping `int C ∩ ext C'` is a sequence of flips. -/
theorem reach_of_zip {C C' : Fin n} (h : C' ≠ C) {M N : Marked n D}
    (hN : Relation.ReflTransGen (Marked.LensFlip h False True) M N) : Reach M N := by
  have hzQ : ∀ N : Marked n D, ¬ N.TwoQ C' C False True N.z :=
    fun N h => N.not_inside_z _ (h.2.2 trivial)
  induction hN with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (Marked.LensFlip.flipStep (hzQ _) hs)

/-- **Zipping `int C ∩ ext C'` does not change `M − C'`** (every flip has a side on `L ⊂ C'`,
P1), and a kept dart of the marked cell stays in the marked cell (it is not a corner of a
flipped triangle: two corners are on `C'`, the apex is a vertex of the lens). -/
theorem zip_del {m : ℕ} {C C' : Fin (m + 1)} (h : C' ≠ C) (hm : 2 ≤ m) {K : D → Prop}
    [DecidablePred K] {M N : Marked (m + 1) D}
    (hN : Relation.ReflTransGen (Marked.LensFlip h False True) M N)
    (hK : ∀ e, K e ↔ Keep M.A C' e) {w : D} (hwK : K w) (hw : M.A.cellOf w = M.z) :
    ∃ hK' : (∀ e, K e ↔ Keep N.A C' e),
      N.A.deleteOn C' hm K hK' = M.A.deleteOn C' hm K hK ∧ N.A.cellOf w = N.z := by
  induction hN with
  | refl => exact ⟨hK, rfl, hw⟩
  | @tail N₁ N₂ _ hs ih =>
    obtain ⟨hK₁, hdel, hw₁⟩ := ih
    obtain ⟨d, hT, hsrc, rfl⟩ := hs
    obtain ⟨⟨hdC, -⟩, -, hv⟩ := hsrc
    have hK₂ : ∀ e, K e ↔ Keep (N₁.flip d hT).A C' e := hK₁
    have hwk := (hK₁ w).1 hwK
    refine ⟨hK₂, ?_, ?_⟩
    · rw [← hdel]
      exact deleteOn_flip_of_side N₁.A C' hm K hK₁ hT ⟨d, N₁.A.mem_darts_cellOf_self d, hdC⟩ hK₂
    · have hnc : ¬ N₁.A.IsCorner d w := by
        intro hc
        obtain ⟨y, hy, hyw⟩ := mem_image.1 hc
        have hy' : y ∈ orbitFinset N₁.A.φ d :=
          mem_orbitFinset.2 (N₁.A.mem_darts_cellOf.1 hy)
        rw [orbitFinset_three (Arrangement.tri_φφφ hT), mem_insert, mem_insert,
          mem_singleton] at hy'
        rcases hy' with rfl | rfl | rfl
        · apply hwk.2; rw [← hyw, ← hdC]; exact N₁.A.mem_curves_crossingOf y
        · apply hwk.2
          rw [← hyw, N₁.A.φ_apply, N₁.A.crossingOf_σ, ← hdC, ← N₁.A.curve_α]
          exact N₁.A.mem_curves_crossingOf _
        · have := (hv w (Orbit.mem_darts.2 hyw.symm)).1
          change N₁.TwoQ C' C False True (N₁.A.cellOf w) at this
          rw [hw₁, Marked.twoQ_z_iff] at this
          exact this.2 trivial
      change (N₁.A.flip d hT).cellOf w = Arrangement.flipCellEquiv hT N₁.z
      rw [Arrangement.flip_cellOf_of_not_corner hT hnc, hw₁]

end Pca.FlipGraph
