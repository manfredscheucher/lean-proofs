/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: an antipodal flip changes the sign of exactly one triple (`doc/pca/great.md` 3.4)
-/
import Pca.Great.R_Pot

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

namespace Frame

variable (F : Frame A) (hA : A.IsGreat)
include hA

theorem neg_iff' {a b c : Fin n} (hb : b ≠ F.c0) (hc : c ≠ F.c0) (hbc : b ≠ c) {x : A.Crossing}
    (hx : Arrangement.Crossing.curves A x = {b, c}) (hs : A.crossSide F.s0 x = 1) :
    F.Neg a b c ↔ A.crossSide (F.sR a) x = 0 := by
  constructor
  · intro h; exact h x hx hs
  · intro h y hy hys
    rw [F.hcross_unique hA hb hc hbc hy hys, ← F.hcross_unique hA hb hc hbc hx hs]; exact h

variable {d : D} (hT : A.IsTriangle (A.cellOf d))
  (hc0 : F.c0 ∉ Arrangement.Cell.curves A (A.cellOf d)) (hH : F.s0 (A.cellOf d) = 1)
include hT hc0 hH

/-- The flipped arrangement and its frame. -/
theorem neg_aflip :
    ∃ hT' : (A.flip d hT).IsTriangle ((A.flip d hT).cellOf (A.α (ant A d))),
      ∃ hc0' : F.c0 ∉ Arrangement.Cell.curves (A.flip d hT) ((A.flip d hT).cellOf (A.α (ant A d))),
        ∀ a b c : Fin n, a ≠ F.c0 → b ≠ F.c0 → c ≠ F.c0 → a ≠ b → a ≠ c → b ≠ c →
          (((F.flipF hT).flipF hT').Neg a b c ↔
            (F.Neg a b c ↔ ¬ ({a, b, c} : Finset (Fin n)) = Arrangement.Cell.curves A (A.cellOf d))) := by
  have hanti := isAntipodalTri_ant hA hT
  set e := A.α (ant A d)
  have hT' := flip_isTriangle_antipodal hT hanti
  have hdarts := flip_darts_antipodal hT hanti
  have hcurE : Arrangement.Cell.curves (A.flip d hT) ((A.flip d hT).cellOf e) =
      Arrangement.Cell.curves A (A.cellOf d) := by
    rw [← curves_antipodal hanti]; simp only [Arrangement.Cell.curves]; rw [hdarts]; rfl
  have hcorE : Arrangement.Cell.corners (A.flip d hT) ((A.flip d hT).cellOf e) =
      Arrangement.Cell.corners A (A.cellOf e) := by
    simp only [Arrangement.Cell.corners]; rw [hdarts]; rfl
  have hc0' : F.c0 ∉ Arrangement.Cell.curves (A.flip d hT) ((A.flip d hT).cellOf e) := by
    rw [hcurE]; exact hc0
  refine ⟨hT', hc0', ?_⟩
  intro a b c ha hb hc hab hac hbc
  have hB : ((A.flip d hT).flip e hT').IsGreat := AFlip.isGreat hA ⟨d, e, hT, hanti, hT', rfl⟩
  set F1 := F.flipF hT
  set FB := F1.flipF hT'
  set x := A.crossingOf ((A.straight ^ F.hpos b c) (F.β b))
  have hxc := F.curves_hcross hA hb hc hbc
  have hx0 : F.c0 ∉ Arrangement.Crossing.curves A x := by
    rw [hxc, mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hb, Ne.symm hc⟩
  have hxa : a ∉ Arrangement.Crossing.curves A x := by
    rw [hxc, mem_insert, mem_singleton, not_or]; exact ⟨hab, hac⟩
  have hxs : A.crossSide F.s0 x = 1 := by
    rw [crossSide_eq F.isSide_s0 hx0]; exact F.s0_cell hA hb (F.hpos_spec hA hb hc hbc).2.1
  -- sides in `B`
  have hsB : ((A.flip d hT).flip e hT').crossSide FB.s0 x = 1 := by
    rw [F1.flip_s0 hT' hc0' x hx0, F.flip_s0 hT hc0 x hx0, hxs]
  have hrB := FB.neg_iff' hB (a := a) hb hc hbc hxc hsB
  -- `x` is not a corner of the antipodal triangle (it lies in `H`)
  have hnot' : x ∉ Arrangement.Cell.corners A (A.cellOf e) := by
    intro hm
    rw [hanti.2.2, mem_filter] at hm
    obtain ⟨-, hsub, hnc⟩ := hm
    obtain ⟨y, hy, hyx⟩ := tri_pair hT hsub
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hy
    have hwT : A.cellOf w = A.cellOf d := Orbit.mem_darts.1 hw
    have hne : A.crossingOf w ≠ x := fun h => hnc (h ▸ hy)
    have := hA b c F.c0 hbc hb hc F.s0 F.isSide_s0 _ _ hne (hyx.trans hxc) hxc w
      (Orbit.mem_darts.2 rfl) ((A.straight ^ F.hpos b c) (F.β b)) (Orbit.mem_darts.2 rfl)
    apply this
    rw [hwT, hH, F.s0_cell hA hb (F.hpos_spec hA hb hc hbc).2.1]
  have hnot1 : x ∉ Arrangement.Cell.corners (A.flip d hT) ((A.flip d hT).cellOf e) := by
    rw [hcorE]; exact hnot'
  have key : ((A.flip d hT).flip e hT').crossSide (FB.sR a) x = A.crossSide (F.sR a) x +
      (if x ∈ Arrangement.Cell.corners A (A.cellOf d) ∧
        a ∈ Arrangement.Cell.curves A (A.cellOf d) then 1 else 0) := by
    rw [F1.flip_sR hT' hc0' a x hxa, if_neg (fun h => hnot1 h.1), add_zero,
      F.flip_sR hT hc0 a x hxa]
  rw [hrB, F.neg_iff' hA hb hc hbc hxc hxs, key]
  -- the corner condition is the triple condition
  have hiff : (x ∈ Arrangement.Cell.corners A (A.cellOf d) ∧
      a ∈ Arrangement.Cell.curves A (A.cellOf d)) ↔
      ({a, b, c} : Finset (Fin n)) = Arrangement.Cell.curves A (A.cellOf d) := by
    have h3 : (Arrangement.Cell.curves A (A.cellOf d)).card = 3 :=
      Arrangement.Triangle.card_curves hT
    constructor
    · rintro ⟨hx, ha'⟩
      have hsub := curves_corner_sub hT hx
      rw [hxc] at hsub
      refine eq_of_subset_of_card_le ?_ ?_
      · intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact ha'
        · exact hsub (by simp)
        · exact hsub (by simp)
      · rw [h3, card_insert_of_notMem (by simp [hab, hac]), card_pair hbc]
    · intro h
      refine ⟨?_, h ▸ by simp⟩
      have hsub : Arrangement.Crossing.curves A x ⊆ Arrangement.Cell.curves A (A.cellOf d) := by
        rw [hxc, ← h]; intro z hz; simp only [mem_insert, mem_singleton] at hz ⊢; tauto
      obtain ⟨y, hy, hyx⟩ := tri_pair hT hsub
      obtain ⟨w, hw, rfl⟩ := mem_image.1 hy
      have hwT : A.cellOf w = A.cellOf d := Orbit.mem_darts.1 hw
      have hy0 : F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf w) := by rw [hyx]; exact hx0
      have hys : A.crossSide F.s0 (A.crossingOf w) = 1 := by
        rw [crossSide_eq F.isSide_s0 hy0, hwT]; exact hH
      rw [F.hcross_unique hA hb hc hbc (hyx.trans hxc) hys] at hy
      exact hy
  by_cases h : ({a, b, c} : Finset (Fin n)) = Arrangement.Cell.curves A (A.cellOf d)
  · rw [if_pos (hiff.2 h)]
    have : ∀ u : ZMod 2, (u + 1 = 0 ↔ (u = 0 ↔ ¬ True)) := by decide
    simpa [h] using this (A.crossSide (F.sR a) x)
  · rw [if_neg (fun h' => h (hiff.1 h')), add_zero]
    simp only [h, not_false_eq_true, iff_true]
    exact Iff.rfl

end Frame

end Pca.Great
