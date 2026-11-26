/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package A (gap lemma G1): triangles with a curve reaching the ∞-arc are convex

Lemma 3.6 (package C) excludes only **convex** triangles (`IsConvexTri`, statement change O3).
G1 finds triangles one of whose curves reaches the ∞-arc. Such a triangle is convex in one of
its two orders (`ab_tri_convex`): in the "reflex" orientation both curves continue from the apex
`v` into the region bounded by the legs and `S[k, l]` (the cut `r` of this closed walk is
`ρ + 1` there and `ρ` at the ∞-arc), and the curve that reaches the ∞-arc would have to cross
the boundary of the region, which it cannot (the legs are single segments).
-/
import Pca.Sweep.AB_G1
import Pca.Sweep.L36

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- Jordan for a walk `P` of segments of curves other than `S` from `l` to `k`, closed along
`S`: a cut that changes across the segments of `P` (and some segments of `S`). -/
theorem ab_mkcut {z : D} (hz : Γ.infStart = some z) {l k : Γ.Crossing} (hl : Γ.OnSweep l)
    (hk : Γ.OnSweep k) (P : Γ.Segment → ZMod 2)
    (hP : Γ.jSegBdry P = Pi.single l 1 + Pi.single k 1) :
    ∃ g : Γ.Cell → ZMod 2, ∀ y, Γ.curve y ≠ Γ.S →
      g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = P (Γ.segmentOf y) := by
  classical
  obtain ⟨tl, -, htl'⟩ := no_onSweep_noC hz hl
  obtain ⟨tk, -, htk'⟩ := no_onSweep_noC hz hk
  obtain ⟨p, q, hpq, hpts⟩ : ∃ p q, p ≤ q ∧
      (Pi.single (Γ.crossingOf (Γ.noC z p)) 1 + Pi.single (Γ.crossingOf (Γ.noC z q)) 1 :
        Γ.Crossing → ZMod 2) = Pi.single l 1 + Pi.single k 1 := by
    rcases le_total tl tk with h | h
    · exact ⟨tl, tk, h, by rw [htl', htk']⟩
    · exact ⟨tk, tl, h, by rw [htl', htk', add_comm]⟩
  let h : Γ.Segment → ZMod 2 :=
    (∑ t ∈ Ico p q, (Pi.single (Γ.segmentOf (Γ.noC z t)) 1 : Γ.Segment → ZMod 2)) + P
  have hB : Γ.jSegBdry h = 0 := by
    have hc : ∀ t, Γ.crossingOf (Γ.α (Γ.noC z t)) = Γ.crossingOf (Γ.noC z (t + 1)) := fun t => by
      rw [← no_crossingOf_α_straight, no_noC_straight]
    simp only [h, map_add, map_sum, j_segBdry_single, hc]
    rw [ab_telescope (fun m => by funext x; exact j_zmod2_add_self _)
      (fun t => (Pi.single (Γ.crossingOf (Γ.noC z t)) 1 : Γ.Crossing → ZMod 2)) hpq, hpts, hP]
    funext x
    simp only [Pi.add_apply, Pi.zero_apply]
    exact j_zmod2_add_self _
  obtain ⟨g, hg⟩ := Γ.j_mem_range_of_mem_ker h hB
  refine ⟨g, fun y hy => ?_⟩
  rw [← j_cellBdry_segmentOf, hg]
  simp only [h, Pi.add_apply, Finset.sum_apply]
  rw [sum_eq_zero (fun t _ => ?_), zero_add]
  rw [Pi.single_apply,
    if_neg (ab_seg_ne_of_curve (by rw [(no_noC_sweep hz t).1]; exact fun h => hy h.symm))]

/-- Walking straight, a cut changes only across the crossing curves. -/
theorem ab_walk_const {g : Γ.Cell → ZMod 2} {F : D → ZMod 2}
    (hr : ∀ y, g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = F y) {a : D} {j : ℕ}
    (hF : ∀ i < j, F (Γ.σ (Γ.α ((Γ.straight ^ i) a))) = 0) :
    g (Γ.cellOf ((Γ.straight ^ j) a)) = g (Γ.cellOf a) := by
  induction j with
  | zero => rw [pow_zero, Perm.one_apply]
  | succ j ih =>
    rw [no_pow_succ, no_walk_straight hr, ih (fun i hi => hF i (by omega)), hF j (by omega),
      add_zero]

/-- Walking along the upper side of `S` from the ∞-arc. -/
theorem ab_sweep_val {g : Γ.Cell → ZMod 2} {F : D → ZMod 2}
    (hr : ∀ y, g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = F y)
    (hF : ∀ y, Γ.curve y ≠ Γ.S → Γ.IsInfVertex (Γ.crossingOf y) → F y = 0) {z : D}
    (hz : Γ.infStart = some z) (t : ℕ) :
    g (Γ.upperCell (Γ.noC z t)) =
      g (Γ.upperCell z) + ∑ i ∈ range (t + 1), F (Γ.σ (Γ.noC z i)) := by
  induction t with
  | zero =>
    have h0 : Γ.noC z 0 = Γ.straight ((Γ.straight ^ Γ.infLen) z) := by
      unfold noC; rw [pow_zero, Perm.one_apply, no_pow_succ]
    rw [sum_range_one, h0]
    unfold upperCell
    rw [no_walk_sweep hr]
    have := ab_cut_arc hr hF hz Γ.infLen le_rfl
    unfold upperCell at this
    rw [this]
  | succ t ih =>
    rw [sum_range_succ, ← add_assoc, ← ih, ← no_noC_straight]
    unfold upperCell
    rw [no_walk_sweep hr]

/-- A triangle in the reflex orientation (`k < l`, `φ b = α a`) one of whose curves reaches
the ∞-arc does not exist. -/
theorem ab_reflex {a b : D} (hT : Γ.IsTri a b) {z : D} (hz : Γ.infStart = some z)
    {ta tb : ℕ} (hta : ta < period Γ.straight z) (htb : tb < period Γ.straight z)
    (hka : Γ.crossingOf (Γ.noC z ta) = Γ.crossingOf a)
    (hkb : Γ.crossingOf (Γ.noC z tb) = Γ.crossingOf b) (hlt : ta < tb)
    (hφ : Γ.φ b = Γ.α a) {e : D} (he : e = a ∨ e = b)
    (hinf : ∃ x, Γ.IsInfVertex x ∧ Γ.curve e ∈ Γ.curves x) : False := by
  classical
  obtain ⟨hA, hB, hfa, hfb, hab, hv, hvA, hcab⟩ := hT
  have haS : Γ.S ∈ Γ.curves (Γ.crossingOf a) := hfa.1
  have hbS : Γ.S ∈ Γ.curves (Γ.crossingOf b) := hfb.1
  -- the cut of `S[k, l]` + legs
  let P : Γ.Segment → ZMod 2 :=
    Pi.single (Γ.segmentOf a) 1 + Pi.single (Γ.segmentOf b) 1
  have hP : Γ.jSegBdry P = Pi.single (Γ.crossingOf a) 1 + Pi.single (Γ.crossingOf b) 1 := by
    simp only [P, map_add, j_segBdry_single, hv]
    funext x
    simp only [Pi.add_apply]
    generalize (Pi.single (Γ.crossingOf a) 1 : Γ.Crossing → ZMod 2) x = A
    generalize (Pi.single (Γ.crossingOf b) 1 : Γ.Crossing → ZMod 2) x = B
    generalize (Pi.single (Γ.crossingOf (Γ.α b)) 1 : Γ.Crossing → ZMod 2) x = V
    revert A B V
    decide
  obtain ⟨g, hg⟩ := ab_mkcut hz haS hbS P hP
  set F : D → ZMod 2 := fun y => g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) with hFdef
  have hr : ∀ y, g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = F y := fun _ => rfl
  have hF0 : ∀ y, Γ.curve y ≠ Γ.S → y ≠ a → y ≠ Γ.α a → y ≠ b → y ≠ Γ.α b → F y = 0 := by
    intro y hy h1 h2 h3 h4
    have hα : ∀ e, y ≠ Γ.α e → e ≠ Γ.α y := fun e he he' => he (by rw [he', j_α_α])
    show g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = 0
    rw [hg y hy]
    simp only [P, Pi.add_apply, Pi.single_apply]
    rw [if_neg (ab_seg_ne (Ne.symm h1) (hα a h2)), if_neg (ab_seg_ne (Ne.symm h3) (hα b h4)),
      add_zero]
  have hvx : Γ.crossingOf (Γ.α b) = Γ.crossingOf (Γ.α a) := hv.symm
  have hF0' : ∀ y, Γ.curve y ≠ Γ.S → Γ.crossingOf y ≠ Γ.crossingOf a →
      Γ.crossingOf y ≠ Γ.crossingOf b → Γ.crossingOf y ≠ Γ.crossingOf (Γ.α a) → F y = 0 :=
    fun y hy h1 h2 h3 => hF0 y hy (fun e => h1 (by rw [e])) (fun e => h3 (by rw [e]))
      (fun e => h2 (by rw [e])) (fun e => h3 (by rw [e, hvx]))
  have hFa : F a = 1 := by
    show g (Γ.cellOf a) + g (Γ.cellOf (Γ.α a)) = 1
    rw [hg a hA.1]
    simp only [P, Pi.add_apply, Pi.single_apply]
    rw [if_neg (ab_seg_ne_of_curve (Ne.symm hcab))]
    simp
  have hF_inf : ∀ y, Γ.curve y ≠ Γ.S → Γ.IsInfVertex (Γ.crossingOf y) → F y = 0 :=
    fun y hy hi => hF0' y hy (fun e => hfa.2 (by rw [← e]; exact hi))
      (fun e => hfb.2 (by rw [← e]; exact hi))
      (fun e => hvA.1 (by rw [← e]; exact ab_infVertex_onSweep hi))
  set ρ := g (Γ.upperCell z) with hρ
  -- the cell to the right of `a` is above the edge starting at `k`: `r = ρ + 1`
  have hσa : Γ.σ (Γ.noC z ta) = a := by
    have hsw := no_noC_sweep hz ta
    refine ab_above_unique hA (no_above_σ hsw) haS ?_ (by rw [j_crossingOf_σ, hka])
    exact (ab_other_curve (by rw [hka]; exact ab_mem_curves_self a)
      (by rw [hsw.1]; exact hA.1)).symm
  have hga : g (Γ.cellOf a) = ρ + 1 := by
    have h1 : Γ.cellOf a = Γ.upperCell (Γ.noC z ta) := by
      unfold upperCell; rw [← hσa, j_cellOf_σ]
    rw [h1, ab_sweep_val hr hF_inf hz, sum_range_succ, hσa, hFa, sum_eq_zero, zero_add]
    intro i hi
    rw [mem_range] at hi
    have hsw := no_noC_sweep hz i
    refine hF0' _ (no_above_σ hsw).1 ?_ ?_ ?_ <;> rw [j_crossingOf_σ]
    · rw [← hka]; intro h; have := no_noC_inj hz (by omega) hta h; omega
    · rw [← hkb]; intro h; have := no_noC_inj hz (by omega) htb h; omega
    · intro h; apply hvA.1; rw [← h]; exact no_S_mem_noC hz i
  -- reflex: both continuations after `v` lie in the region
  have hφa : Γ.φ a = Γ.straight b := by
    rw [j_φ_apply, ← hφ, j_φ_apply, j_straight_apply]
  have hσsb : Γ.σ (Γ.straight b) = Γ.straight a := by
    rw [j_straight_apply, j_straight_apply, ← j_φ_apply, hφ]
  have hsv : ∀ y, Γ.crossingOf (Γ.straight y) = Γ.crossingOf (Γ.α y) := no_crossingOf_α_straight
  have hFs : ∀ y, (y = a ∨ y = b) → F (Γ.straight y) = 0 := by
    rintro y (rfl | rfl)
    · refine hF0 _ (by rw [j_curve_straight]; exact hA.1) (fun e => hvA.1 ?_)
        (by rw [j_straight_apply]; exact Γ.j_σσ_ne _) (fun e => hcab ?_) (fun e => hcab ?_)
      · rw [← hsv, e]; exact haS
      · rw [← j_curve_straight Γ y, e]
      · rw [← j_curve_straight Γ y, e, j_curve_α]
    · refine hF0 _ (by rw [j_curve_straight]; exact hB.1) (fun e => hcab ?_) (fun e => hcab ?_)
        (fun e => hvA.1 ?_) (by rw [j_straight_apply]; exact Γ.j_σσ_ne _)
      · rw [← j_curve_straight Γ y, e]
      · rw [← j_curve_straight Γ y, e, j_curve_α]
      · rw [← hvx, ← hsv, e]; exact hbS
  have hgsb : g (Γ.cellOf (Γ.straight b)) = ρ + 1 := by rw [← hφa, j_cellOf_φ, hga]
  have hgs : ∀ y, (y = a ∨ y = b) → g (Γ.cellOf (Γ.straight y)) = ρ + 1 := by
    rintro y (rfl | rfl)
    · have := no_corner hr (Γ.straight b)
      rw [hσsb, hFs b (Or.inr rfl), hgsb] at this
      rw [j_zmod2_eq_add_of_add_eq this, add_zero]
    · exact hgsb
  -- the curve of `e` walks from the ∞-arc to `v` without crossing the boundary
  have heA : Γ.Above e := by rcases he with rfl | rfl <;> assumption
  have heS : Γ.S ∈ Γ.curves (Γ.crossingOf e) := by rcases he with rfl | rfl <;> assumption
  have hefin : Γ.IsFinVertex (Γ.crossingOf e) := by rcases he with rfl | rfl <;> assumption
  have hev : Γ.crossingOf (Γ.straight e) = Γ.crossingOf (Γ.α a) := by
    rcases he with rfl | rfl
    · exact hsv _
    · rw [hsv, hvx]
  have hseA : Γ.Above (Γ.straight e) := ab_above_of_aboveVertex hvA hev
  have hgse := hgs e he
  have hgαse : g (Γ.cellOf (Γ.α (Γ.straight e))) = ρ + 1 := by
    have := hr (Γ.straight e)
    rw [hFs e he, hgse] at this
    rw [j_zmod2_eq_add_of_add_eq this, add_zero]
  have hsαse : Γ.straight (Γ.α (Γ.straight e)) = Γ.α e := by
    rw [j_straight_apply, j_α_α, j_straight_apply, Γ.j_σ4]
  obtain ⟨x, hxinf, hxe⟩ := hinf
  obtain ⟨a', ha'x, ha'c, ha'A, -, -⟩ := ab_up_dart (ab_infVertex_onSweep hxinf) hxe heA.1
  have ha'S : Γ.S ∈ Γ.curves (Γ.crossingOf a') := by
    rw [ha'x]; exact ab_infVertex_onSweep hxinf
  have hga' : g (Γ.cellOf a') = ρ := ab_cut_inf hr hF_inf hz ha'A (by rw [ha'x]; exact hxinf)
  have hc' : Γ.curve a' = Γ.curve (Γ.straight e) := by rw [ha'c, j_curve_straight]
  rcases upper_arc ha'A hseA hc' with ⟨j, hj, hje⟩ | h | ⟨j, hj, hje⟩ | h
  · rcases j with _ | j
    · rw [pow_zero, Perm.one_apply] at hje
      exact hvA.1 (by rw [← hev, ← hje]; exact ha'S)
    · rw [no_pow_succ] at hje
      have hje' := Γ.straight.injective hje
      rcases j with _ | j
      · rw [pow_zero, Perm.one_apply] at hje'
        exact hefin.2 (by rw [← hje', ha'x]; exact hxinf)
      · exact no_enter heA heS (hj j (by omega)) (by rw [← no_pow_succ]; exact hje')
  · have := no_upperWalk_to ha'A ha'S h
    exact hvA.1 (by rw [← hev, this]; exact ha'S)
  · have hall : ∀ i ≤ j + 1, Γ.Above ((Γ.straight ^ i) a') := by
      intro i hi
      by_cases h : i ≤ j
      · exact hj i h
      · rw [show i = j + 1 by omega, no_pow_succ, hje, hsαse]
        exact ab_above_α heA
    have hwalk := ab_walk_const hr (a := a') (j := j) (fun i hi => by
      have hx : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ((Γ.straight ^ i) a'))) := fun hS =>
        no_exit (hj i (by omega)) hS (by rw [← no_pow_succ]; exact hj (i + 1) hi)
      refine hF0' _ (ab_curves_ne_S hx (j_crossingOf_σ _ _)) ?_ ?_ ?_ <;> rw [j_crossingOf_σ]
      · exact fun e => hx (by rw [e]; exact haS)
      · exact fun e => hx (by rw [e]; exact hbS)
      · intro e
        have h1 : Γ.crossingOf (Γ.α a) = Γ.crossingOf ((Γ.straight ^ (j + 1)) a') := by
          rcases he with rfl | rfl
          · rw [no_pow_succ, hje, hsαse]
          · rw [no_pow_succ, hje, hsαse, hvx]
        rw [h1, ← no_crossingOf_α_straight, ← no_pow_succ] at e
        have := ab_walk_inj ha'A ha'S hall (by omega) le_rfl e
        omega)
    rw [hje, hga'] at hwalk
    exact ab_ne_add_one ρ (hgαse.symm.trans hwalk)
  · have := no_upperWalk_to ha'A ha'S h
    exact ab_ne_add_one ρ (hgαse.symm.trans (by rw [this]; exact hga'))

/-- A triangle one of whose curves reaches the ∞-arc is convex (in one of its two orders). -/
theorem ab_tri_convex {a b : D} (hT : Γ.IsTri a b) {e : D} (he : e = a ∨ e = b)
    (hinf : ∃ x, Γ.IsInfVertex x ∧ Γ.curve e ∈ Γ.curves x) :
    Γ.IsConvexTri a b ∨ Γ.IsConvexTri b a := by
  obtain ⟨x, ⟨z, hz, -⟩, -⟩ := id hinf
  have hz' : Γ.infStart = some z := hz
  obtain ⟨hA, hB, hfa, hfb, hab, hv, hvA, hcab⟩ := id hT
  have hT' : Γ.IsTri b a := ⟨hB, hA, hfb, hfa, Ne.symm hab, hv.symm, by rw [← hv]; exact hvA,
    Ne.symm hcab⟩
  obtain ⟨ta, hta, hka⟩ := no_onSweep_noC hz' hfa.1
  obtain ⟨tb, htb, hkb⟩ := no_onSweep_noC hz' hfb.1
  have hpa : Γ.pos (Γ.crossingOf a) = ta + 1 := by rw [← hka]; exact no_noC_pos hz' hta
  have hpb : Γ.pos (Γ.crossingOf b) = tb + 1 := by rw [← hkb]; exact no_noC_pos hz' htb
  have hne : ta ≠ tb := fun h => hab (by rw [← hka, ← hkb, h])
  -- the orientation at the apex
  have hor : Γ.φ a = Γ.α b ∨ Γ.φ b = Γ.α a := by
    rcases no_mem_crossing hv.symm with h | h | h | h
    · exact absurd (congrArg Γ.crossingOf (Γ.α.injective h)).symm hab
    · exact Or.inl (by rw [j_φ_apply, h])
    · exact absurd (by rw [← j_curve_α Γ b, h, j_curve_σσ, j_curve_α]) hcab.symm
    · exact Or.inr (by rw [j_φ_apply, h, Γ.j_σ4])
  rcases lt_or_gt_of_ne hne with hlt | hlt <;> rcases hor with hφ | hφ
  · exact Or.inl ⟨hT, by omega, hφ⟩
  · exact (ab_reflex hT hz' hta htb hka hkb hlt hφ he hinf).elim
  · exact (ab_reflex hT' hz' htb hta hkb hka hlt hφ he.symm hinf).elim
  · exact Or.inr ⟨hT', by omega, hφ⟩

end SConf

end Pca.Sweep
