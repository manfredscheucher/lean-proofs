/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The antipodal flip (P2, package A, `doc/pca/great.md` section 3.1)

* flip side lemma: after flipping the triangle `T = cellOf d`, every side function of a curve `C`
  carries over; cells away from the corners of `T` keep their side; a crossing changes its side of
  `C` iff it is a corner of `T` and `C` is the curve of `T` not through it,
* P2: in a great arrangement every triangle has an antipodal triangle (`cellOf (α (ant d))`), it
  is still a triangle after flipping `T`, and the antipodal flip of a great arrangement is great.
-/
import Pca.Great.Basic

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- The indicator `[curve y = C]` in `ZMod 2`. -/
private abbrev ind (A : Arrangement n D) (C : Fin n) (y : D) : ZMod 2 :=
  if A.curve y = C then 1 else 0

/-- `C` is a curve of the triangle of `b` iff it is the curve of one of its three darts (at most
one, the three curves are distinct). -/
private theorem ind_curves {b : D} (hTb : A.IsTriangle (A.cellOf b)) (C : Fin n) :
    (if C ∈ Arrangement.Cell.curves A (A.cellOf b) then (1 : ZMod 2) else 0) =
      ind A C b + ind A C (A.φ b) + ind A C (A.φ (A.φ b)) := by
  have hmem : ∀ c, A.cellOf c = A.cellOf b ↔ c = b ∨ c = A.φ b ∨ c = A.φ (A.φ b) :=
    fun c => Arrangement.tri_mem_iff hTb
  have h1 : A.curve b ≠ A.curve (A.φ b) := (A.curve_φ_ne b).symm
  have h2 : A.curve (A.φ b) ≠ A.curve (A.φ (A.φ b)) := (A.curve_φ_ne (A.φ b)).symm
  have h3 : A.curve b ≠ A.curve (A.φ (A.φ b)) := by
    intro h
    have := A.curve_φ_ne (A.φ (A.φ b))
    rw [Arrangement.tri_φφφ hTb] at this
    exact this h
  have hC : C ∈ Arrangement.Cell.curves A (A.cellOf b) ↔
      C = A.curve b ∨ C = A.curve (A.φ b) ∨ C = A.curve (A.φ (A.φ b)) := by
    simp only [Arrangement.Cell.curves, mem_image, Orbit.mem_darts]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rcases (hmem c).1 hc with rfl | rfl | rfl <;> simp
    · rintro (h | h | h) <;> refine ⟨_, ?_, h.symm⟩
      · rfl
      · exact A.cellOf_φ b
      · show A.cellOf (A.φ (A.φ b)) = A.cellOf b
        rw [A.cellOf_φ, A.cellOf_φ]
  simp only [ind]
  by_cases ha : A.curve b = C <;> by_cases hb : A.curve (A.φ b) = C <;>
    by_cases hc : A.curve (A.φ (A.φ b)) = C <;>
    simp_all [eq_comm]

/-- **Flip side lemma.** -/
theorem flip_isSide {d : D} (hT : A.IsTriangle (A.cellOf d)) {C : Fin n}
    {s : A.Cell → ZMod 2} (hs : A.IsSide C s) :
    ∃ s' : (A.flip d hT).Cell → ZMod 2, (A.flip d hT).IsSide C s' ∧
      (∀ y, ¬ A.IsCorner d y → s' ((A.flip d hT).cellOf y) = s (A.cellOf y)) ∧
      ∀ x : A.Crossing, C ∉ Arrangement.Crossing.curves A x →
        (A.flip d hT).crossSide s' x = A.crossSide s x +
          (if x ∈ Arrangement.Cell.corners A (A.cellOf d) ∧
              C ∈ Arrangement.Cell.curves A (A.cellOf d) then 1 else 0) := by
  classical
  set T := A.cellOf d with hTdef
  set c : ZMod 2 := if C ∈ Arrangement.Cell.curves A T then 1 else 0 with hc
  let s' : (A.flip d hT).Cell → ZMod 2 := fun F =>
    s ((Arrangement.flipCellEquiv hT).symm F) +
      if (Arrangement.flipCellEquiv hT).symm F = T then c else 0
  have hval : ∀ y, s' ((A.flip d hT).cellOf y) = s (A.cellOf (Arrangement.flipG' A d y)) +
      if A.cellOf (Arrangement.flipG' A d y) = T then c else 0 := fun y => by
    simp only [s', Arrangement.flipCellEquiv_symm_cellOf]
    rfl
  have hgen : ∀ y, ¬ A.IsCorner d y → s' ((A.flip d hT).cellOf y) = s (A.cellOf y) := by
    intro y hy
    rw [hval, Arrangement.flipG'_of_not_corner hy, if_neg (Arrangement.not_mem_of_not_corner hy),
      add_zero]
  -- the four cells at a corner of `T` after the flip
  have hcorner : ∀ b, A.cellOf b = T →
      s' ((A.flip d hT).cellOf b) = s T + ind A C (A.φ b) ∧
      s' ((A.flip d hT).cellOf (A.σ b)) = s T + ind A C b + ind A C (A.φ b) ∧
      s' ((A.flip d hT).cellOf (A.σ (A.σ b))) = s T + c ∧
      s' ((A.flip d hT).cellOf (A.σ (A.σ (A.σ b)))) =
        s T + ind A C (A.φ (A.φ b)) + ind A C (A.φ b) := by
    intro b hb
    have hTb := Arrangement.isTriangle_of hT hb
    have hφb : A.cellOf (A.φ b) = T := by rw [A.cellOf_φ, hb]
    have hφφb : A.cellOf (A.φ (A.φ b)) = T := by rw [A.cellOf_φ, hφb]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hval, Arrangement.flipG'_of_mem hT hb, if_neg (Arrangement.ne_straight hT hb),
        add_zero, A.cellOf_straight, Arrangement.zmod2_eq_add_of_add_eq (hs (A.φ b)), hφb]
    · rw [Arrangement.tri_σ hTb, hval, Arrangement.flipG'_straight hT hφφb,
        Arrangement.tri_φφφ (Arrangement.tri_φ hTb),
        if_neg (Arrangement.ne_σσ hT hφb), add_zero, A.side_σσ hs, hφb, A.curve_σ_φ]
      simp only [ind]; ring
    · rw [hval, Arrangement.flipG'_σσ hb, if_pos hb, hb]
    · rw [Arrangement.tri_σσσ hTb, hval, Arrangement.flipG'_α hT hφφb,
        if_neg (Arrangement.ne_σσ hT hφφb), add_zero, A.side_σσ hs, hφφb, A.curve_σ_φ]
  have hcb : ∀ b, A.cellOf b = T → c = ind A C b + ind A C (A.φ b) + ind A C (A.φ (A.φ b)) :=
    fun b hb => by
      have := ind_curves (Arrangement.isTriangle_of hT hb) C
      rw [hb] at this
      exact this
  -- the corner darts
  have hcases : ∀ y, A.IsCorner d y → ∃ b, A.cellOf b = T ∧
      (y = b ∨ y = A.σ b ∨ y = A.σ (A.σ b) ∨ y = A.σ (A.σ (A.σ b))) := by
    intro y hy
    obtain ⟨b, hb, hby⟩ := mem_image.1 hy
    refine ⟨b, Orbit.mem_darts.1 hb, ?_⟩
    have := A.crossingOf_eq_iff.1 hby
    simpa using this
  have hz : ∀ a p q r : ZMod 2, a + p + (a + q + p) = q ∧ a + q + p + (a + (q + p + r)) = r ∧
      a + (q + p + r) + (a + r + p) = q ∧ a + r + p + (a + p) = r := by decide
  have hside : (A.flip d hT).IsSide C s' := by
    intro y
    rw [← (A.flip d hT).cellOf_σ y]
    change s' ((A.flip d hT).cellOf y) + s' ((A.flip d hT).cellOf (A.σ y)) =
      if A.curve y = C then 1 else 0
    by_cases hy : A.IsCorner d y
    · obtain ⟨b, hb, h⟩ := hcases y hy
      obtain ⟨e1, e2, e3, e4⟩ := hcorner b hb
      have hTb := Arrangement.isTriangle_of hT hb
      rw [hcb b hb] at e3
      rcases h with h | h | h | h <;> rw [h]
      · rw [e1, e2]; exact (hz (s T) (ind A C (A.φ b)) (ind A C b) (ind A C (A.φ (A.φ b)))).1
      · rw [e2, e3, Arrangement.curve_σ_tri hTb]; exact (hz (s T) (ind A C (A.φ b)) (ind A C b) (ind A C (A.φ (A.φ b)))).2.1
      · rw [e3, e4, A.isArrangement.curve_σσ]; exact (hz (s T) (ind A C (A.φ b)) (ind A C b) (ind A C (A.φ (A.φ b)))).2.2.1
      · rw [e4, A.σ_σ_σ_σ, e1, A.curve_σσσ, Arrangement.curve_σ_tri hTb]
        exact (hz (s T) (ind A C (A.φ b)) (ind A C b) (ind A C (A.φ (A.φ b)))).2.2.2
    · have hσy : ¬ A.IsCorner d (A.σ y) := by
        intro h; apply hy; unfold Arrangement.IsCorner at h ⊢; rwa [A.crossingOf_σ] at h
      rw [hgen y hy, hgen _ hσy, A.side_σ hs]
      have hw : ∀ a e : ZMod 2, a + (a + e) = e := by decide
      exact hw _ _
  refine ⟨s', hside, hgen, ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := x.exists_mk
  change C ∉ Arrangement.Crossing.curves A (A.crossingOf y) at hx
  change (A.flip d hT).crossSide s' ((A.flip d hT).crossingOf y) = A.crossSide s (A.crossingOf y) +
    (if A.IsCorner d y ∧ C ∈ Arrangement.Cell.curves A T then 1 else 0)
  rw [crossSide_eq hside (d := y) hx, crossSide_eq hs hx]
  by_cases hy : A.IsCorner d y
  · obtain ⟨b, hb, h⟩ := hcases y hy
    obtain ⟨e1, e2, e3, e4⟩ := hcorner b hb
    have hTb := Arrangement.isTriangle_of hT hb
    have hcur : A.curve b ≠ C ∧ A.curve (A.σ b) ≠ C := by
      have hxb : A.crossingOf y = A.crossingOf b := by
        rcases h with h | h | h | h <;> subst h <;> simp [A.crossingOf_σ]
      rw [hxb, A.curves_crossingOf, mem_insert, mem_singleton, not_or] at hx
      exact ⟨Ne.symm hx.1, Ne.symm hx.2⟩
    have i1 : ind A C b = 0 := if_neg hcur.1
    have i3 : ind A C (A.φ (A.φ b)) = 0 := by
      simp only [ind]; rw [← Arrangement.curve_σ_tri hTb, if_neg hcur.2]
    have hcφ : c = ind A C (A.φ b) := by rw [hcb b hb, i1, i3]; ring
    have hside_y : s (A.cellOf y) = s T := by
      have q1 : s (A.cellOf (A.σ b)) = s T := by rw [A.side_σ hs, if_neg hcur.1, add_zero, hb]
      have q2 : s (A.cellOf (A.σ (A.σ b))) = s T := by
        rw [A.side_σ hs, q1, if_neg hcur.2, add_zero]
      have q3 : s (A.cellOf (A.σ (A.σ (A.σ b)))) = s T := by
        rw [A.side_σ hs, q2, A.isArrangement.curve_σσ, if_neg hcur.1, add_zero]
      rcases h with h | h | h | h <;> subst h
      · rw [hb]
      · exact q1
      · exact q2
      · exact q3
    have hif : (if A.IsCorner d y ∧ C ∈ Arrangement.Cell.curves A T then (1 : ZMod 2) else 0) =
        c := by
      rw [hc]; simp only [hy, true_and]
    rw [hif, hside_y, hcφ]
    rcases h with h | h | h | h <;> subst h
    · exact e1
    · rw [e2, i1, add_zero]
    · rw [e3, hcφ]
    · rw [e4, i3, add_zero]
  · rw [hgen y hy, if_neg (fun h => hy h.1), add_zero]

/-! ## Corners of a triangle -/

section TriCorners

variable {b : D} (hTb : A.IsTriangle (A.cellOf b))
include hTb

theorem tri_curves :
    Arrangement.Cell.curves A (A.cellOf b) = {A.curve b, A.curve (A.φ b), A.curve (A.φ (A.φ b))} := by
  ext C
  simp only [Arrangement.Cell.curves, mem_image, Orbit.mem_darts, mem_insert, mem_singleton]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases (Arrangement.tri_mem_iff hTb).1 hc with rfl | rfl | rfl <;> simp
  · rintro (h | h | h) <;> refine ⟨_, ?_, h.symm⟩
    · rfl
    · exact A.cellOf_φ b
    · show A.cellOf (A.φ (A.φ b)) = A.cellOf b
      rw [A.cellOf_φ, A.cellOf_φ]

theorem tri_corner_curves :
    Arrangement.Crossing.curves A (A.crossingOf b) = {A.curve b, A.curve (A.φ (A.φ b))} := by
  rw [A.curves_crossingOf, Arrangement.curve_σ_tri hTb]

theorem tri_mem_corners {x : A.Crossing} :
    x ∈ Arrangement.Cell.corners A (A.cellOf b) ↔
      x = A.crossingOf b ∨ x = A.crossingOf (A.φ b) ∨ x = A.crossingOf (A.φ (A.φ b)) := by
  simp only [Arrangement.Cell.corners, mem_image, Orbit.mem_darts]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases (Arrangement.tri_mem_iff hTb).1 hc with rfl | rfl | rfl <;> simp
  · rintro (h | h | h) <;> refine ⟨_, ?_, h.symm⟩
    · rfl
    · exact A.cellOf_φ b
    · show A.cellOf (A.φ (A.φ b)) = A.cellOf b
      rw [A.cellOf_φ, A.cellOf_φ]

theorem tri_curve_ne :
    A.curve b ≠ A.curve (A.φ b) ∧ A.curve (A.φ b) ≠ A.curve (A.φ (A.φ b)) ∧
      A.curve b ≠ A.curve (A.φ (A.φ b)) := by
  refine ⟨(A.curve_φ_ne b).symm, (A.curve_φ_ne (A.φ b)).symm, fun h => ?_⟩
  have := A.curve_φ_ne (A.φ (A.φ b))
  rw [Arrangement.tri_φφφ hTb] at this
  exact this h

/-- A crossing on two curves of a triangle has the curves of a corner. -/
theorem tri_pair {x : A.Crossing}
    (hx : Arrangement.Crossing.curves A x ⊆ Arrangement.Cell.curves A (A.cellOf b)) :
    ∃ y ∈ Arrangement.Cell.corners A (A.cellOf b),
      Arrangement.Crossing.curves A y = Arrangement.Crossing.curves A x := by
  obtain ⟨w, rfl⟩ := x.exists_mk
  change Arrangement.Crossing.curves A (A.crossingOf w) ⊆ _ at hx
  show ∃ y ∈ _, _ = Arrangement.Crossing.curves A (A.crossingOf w)
  have hw := A.curves_crossingOf w
  have hne := A.isArrangement.curve_σ w
  rw [hw, tri_curves hTb] at hx
  have h1 := hx (mem_insert_self _ _)
  have h2 := hx (mem_insert_of_mem (mem_singleton_self _))
  simp only [mem_insert, mem_singleton] at h1 h2
  obtain ⟨n1, n2, n3⟩ := tri_curve_ne hTb
  have c0 := tri_corner_curves hTb
  have c1 := tri_corner_curves (Arrangement.tri_φ hTb)
  have c2 := tri_corner_curves (Arrangement.tri_φφ hTb)
  rw [Arrangement.tri_φφφ hTb] at c1
  rw [Arrangement.tri_φφφ (Arrangement.tri_φ hTb)] at c2
  have m0 : A.crossingOf b ∈ Arrangement.Cell.corners A (A.cellOf b) :=
    (tri_mem_corners hTb).2 (Or.inl rfl)
  have m1 : A.crossingOf (A.φ b) ∈ Arrangement.Cell.corners A (A.cellOf b) :=
    (tri_mem_corners hTb).2 (Or.inr (Or.inl rfl))
  have m2 : A.crossingOf (A.φ (A.φ b)) ∈ Arrangement.Cell.corners A (A.cellOf b) :=
    (tri_mem_corners hTb).2 (Or.inr (Or.inr rfl))
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    first
    | exact absurd (h2.trans h1.symm) hne
    | (refine ⟨_, m0, ?_⟩; rw [c0, hw, h1, h2]; done)
    | (refine ⟨_, m0, ?_⟩; rw [c0, hw, h1, h2, pair_comm]; done)
    | (refine ⟨_, m1, ?_⟩; rw [c1, hw, h1, h2]; done)
    | (refine ⟨_, m1, ?_⟩; rw [c1, hw, h1, h2, pair_comm]; done)
    | (refine ⟨_, m2, ?_⟩; rw [c2, hw, h1, h2]; done)
    | (refine ⟨_, m2, ?_⟩; rw [c2, hw, h1, h2, pair_comm]; done)
    | (refine ⟨_, m0, ?_⟩; rw [c0, hw, h1, h2]; exact pair_comm _ _)
    | (refine ⟨_, m1, ?_⟩; rw [c1, hw, h1, h2]; exact pair_comm _ _)
    | (refine ⟨_, m2, ?_⟩; rw [c2, hw, h1, h2]; exact pair_comm _ _)

/-- Distinct corners of a triangle have distinct curve pairs. -/
theorem tri_corner_inj {x y : A.Crossing} (hx : x ∈ Arrangement.Cell.corners A (A.cellOf b))
    (hy : y ∈ Arrangement.Cell.corners A (A.cellOf b))
    (h : Arrangement.Crossing.curves A x = Arrangement.Crossing.curves A y) : x = y := by
  obtain ⟨n1, n2, n3⟩ := tri_curve_ne hTb
  have c0 := tri_corner_curves hTb
  have c1 := tri_corner_curves (Arrangement.tri_φ hTb)
  have c2 := tri_corner_curves (Arrangement.tri_φφ hTb)
  rw [Arrangement.tri_φφφ hTb] at c1
  rw [Arrangement.tri_φφφ (Arrangement.tri_φ hTb)] at c2
  rcases (tri_mem_corners hTb).1 hx with rfl | rfl | rfl <;>
    rcases (tri_mem_corners hTb).1 hy with rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso
       simp only [c0, c1, c2] at h
       have a1 := Finset.ext_iff.1 h (A.curve b)
       have a2 := Finset.ext_iff.1 h (A.curve (A.φ (A.φ b)))
       simp [n1, n2, n3, Ne.symm n1, Ne.symm n2, Ne.symm n3] at a1 a2)

end TriCorners

/-- P2 (a): every triangle of a great arrangement has an antipodal triangle. -/
theorem isAntipodalTri_ant (hA : A.IsGreat) {d : D} (hT : A.IsTriangle (A.cellOf d)) :
    A.IsAntipodalTri (A.cellOf d) (A.cellOf (A.α (ant A d))) := by
  classical
  have hinv : ∀ e, A.α (ant A (A.α (ant A e))) = e := fun e => by
    rw [ant_α, A.α_α, ant_ant]
  have hmem : ∀ e, e ∈ (A.cellOf (A.α (ant A d))).darts ↔ A.α (ant A e) ∈ (A.cellOf d).darts :=
    fun e => mem_darts_cellOf_α_ant hA
  -- the antipodal crossing of a corner
  have hcross : ∀ b, A.crossingOf (A.α (ant A b)) = A.crossingOf (ant A (A.α b)) := fun b => by
    rw [ant_α]
  refine ⟨hT, ?_, ?_⟩
  · -- the dart map `e ↦ α (ant e)` is a bijection between the two cells
    change (A.cellOf (A.α (ant A d))).darts.card = 3
    have : (A.cellOf (A.α (ant A d))).darts = (A.cellOf d).darts.image (fun e => A.α (ant A e)) := by
      ext e
      rw [hmem, mem_image]
      exact ⟨fun h => ⟨_, h, hinv e⟩, fun ⟨b, hb, he⟩ => by rw [← he, hinv]; exact hb⟩
    rw [this, card_image_of_injective _ (fun x y h => by rw [← hinv x, h, hinv])]
    exact hT
  · ext x
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · -- a corner of the antipodal cell is the antipode of a corner of `T`
      intro hx
      obtain ⟨e, he, rfl⟩ := mem_image.1 hx
      have hb : A.α (ant A e) ∈ (A.cellOf d).darts := (hmem e).1 he
      set b := A.α (ant A e)
      have hbT : A.cellOf b = A.cellOf d := Orbit.mem_darts.1 hb
      have heb : e = A.α (ant A b) := (hinv e).symm
      have hTb := Arrangement.isTriangle_of hT hbT
      rw [heb, hcross]
      have hyc : A.crossingOf (A.α b) ∈ Arrangement.Cell.corners A (A.cellOf d) := by
        rw [← hbT, ← A.crossingOf_φ]
        exact (tri_mem_corners hTb).2 (Or.inr (Or.inl rfl))
      have hcur := curves_ant hA (A.α b)
      refine ⟨?_, fun hc => crossingOf_ant_ne hA (A.α b) ?_⟩
      · rw [hcur]
        intro C hC
        obtain ⟨z, hz, hzc⟩ := mem_image.1 hyc
        rw [← hzc] at hC
        simp only [Arrangement.Cell.curves]
        rw [A.curves_crossingOf, mem_insert, mem_singleton] at hC
        have hzT : A.cellOf z = A.cellOf d := Orbit.mem_darts.1 hz
        rcases hC with rfl | rfl
        · exact mem_image.2 ⟨z, hz, rfl⟩
        · rw [Arrangement.curve_σ_tri (Arrangement.isTriangle_of hT hzT)]
          refine mem_image.2 ⟨_, ?_, rfl⟩
          rw [Orbit.mem_darts]
          show A.cellOf (A.φ (A.φ z)) = _
          rw [A.cellOf_φ, A.cellOf_φ, hzT]
      · rw [← hbT] at hc hyc
        exact tri_corner_inj hTb hc hyc hcur
    · rintro ⟨hsub, hnot⟩
      obtain ⟨d0, hd0⟩ := A.exists_cellOf (A.cellOf d)
      have hTd := hT
      obtain ⟨y, hy, hyx⟩ := tri_pair hTd hsub
      obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
      have hzT : A.cellOf z = A.cellOf d := Orbit.mem_darts.1 hz
      -- `x` is the other crossing of the curves of the corner `crossingOf z`
      set w := A.φ (A.φ z)
      have hwT : A.cellOf w = A.cellOf d := by
        show A.cellOf (A.φ (A.φ z)) = _
        rw [A.cellOf_φ, A.cellOf_φ, hzT]
      have hzw : A.crossingOf (A.α w) = A.crossingOf z := by
        rw [← A.crossingOf_φ]
        show A.crossingOf (A.φ (A.φ (A.φ z))) = _
        rw [Arrangement.tri_φφφ (Arrangement.isTriangle_of hT hzT)]
      have hx : x = A.crossingOf (ant A (A.α w)) := by
        refine eq_of_curves_eq (x := A.crossingOf z) hyx.symm ?_ (fun h => hnot (h ▸ hy)) ?_
        · rw [curves_ant hA, hzw]
        · rw [← hzw]; exact crossingOf_ant_ne hA _
      rw [hx, ← hcross]
      refine mem_image.2 ⟨_, (hmem _).2 ?_, rfl⟩
      rw [hinv]
      exact Orbit.mem_darts.2 hwT

/-- The darts of the antipodal triangle are not at corners of `T`. -/
theorem not_corner_of_antipodal {d e : D} (h : A.IsAntipodalTri (A.cellOf d) (A.cellOf e))
    {y : D} (hy : A.cellOf y = A.cellOf e) : ¬ A.IsCorner d y ∧ ¬ A.IsCorner d (A.α y) := by
  have hc : ∀ z, A.cellOf z = A.cellOf e → ¬ A.IsCorner d z := fun z hz hzc => by
    have hmem : A.crossingOf z ∈ Arrangement.Cell.corners A (A.cellOf e) :=
      mem_image.2 ⟨z, Orbit.mem_darts.2 hz, rfl⟩
    rw [h.2.2, mem_filter] at hmem
    exact hmem.2.2 hzc
  refine ⟨hc y hy, fun hα => hc (A.φ y) (by rw [A.cellOf_φ, hy]) ?_⟩
  unfold Arrangement.IsCorner at hα ⊢
  rwa [A.crossingOf_φ]

/-- After flipping `T`, the antipodal triangle has the same darts. -/
theorem flip_darts_antipodal {d e : D} (hT : A.IsTriangle (A.cellOf d))
    (h : A.IsAntipodalTri (A.cellOf d) (A.cellOf e)) :
    ((A.flip d hT).cellOf e).darts = (A.cellOf e).darts := by
  have hφ : ∀ y, A.cellOf y = A.cellOf e → (A.flip d hT).φ y = A.φ y := fun y hy => by
    obtain ⟨h1, h2⟩ := not_corner_of_antipodal h hy
    exact Arrangement.flipφ_generic hT h1 h2
  have hpow : ∀ k : ℕ, ((A.flip d hT).φ ^ k) e = (A.φ ^ k) e := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply, ih, pow_succ', Perm.mul_apply, hφ]
      rw [A.cellOf_eq_iff]
      exact (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)).symm
  ext z
  rw [Orbit.mem_darts, Orbit.mem_darts]
  change (A.flip d hT).cellOf z = (A.flip d hT).cellOf e ↔ A.cellOf z = A.cellOf e
  rw [(A.flip d hT).cellOf_eq_iff, A.cellOf_eq_iff]
  constructor
  · intro hz
    obtain ⟨k, hk⟩ := hz.symm.exists_nat_pow_eq
    rw [hpow] at hk
    rw [← hk]
    exact (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)).symm
  · intro hz
    obtain ⟨k, hk⟩ := hz.symm.exists_nat_pow_eq
    rw [← hpow] at hk
    rw [← hk]
    exact (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)).symm

/-- The antipodal triangle lies on the same three curves. -/
theorem curves_antipodal {d e : D} (h : A.IsAntipodalTri (A.cellOf d) (A.cellOf e)) :
    Arrangement.Cell.curves A (A.cellOf e) = Arrangement.Cell.curves A (A.cellOf d) := by
  refine eq_of_subset_of_card_le ?_ ?_
  · intro C hC
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hC
    have hmem : A.crossingOf w ∈ Arrangement.Cell.corners A (A.cellOf e) := mem_image.2 ⟨w, hw, rfl⟩
    rw [h.2.2, mem_filter] at hmem
    exact hmem.2.1 (A.mem_curves_crossingOf w)
  · rw [Arrangement.Cell.curves, Arrangement.Cell.curves, Arrangement.Triangle.card_curves h.1,
      Arrangement.Triangle.card_curves h.2.1]

/-- P2 (b): the antipodal triangle is still a triangle (with the same darts) after flipping `T`. -/
theorem flip_isTriangle_antipodal {d e : D} (hT : A.IsTriangle (A.cellOf d))
    (h : A.IsAntipodalTri (A.cellOf d) (A.cellOf e)) :
    (A.flip d hT).IsTriangle ((A.flip d hT).cellOf e) := by
  change ((A.flip d hT).cellOf e).darts.card = 3
  rw [flip_darts_antipodal hT h]
  exact h.2.1

/-- P2 (c): an antipodal flip of a great arrangement is great. -/
theorem AFlip.isGreat {B : Arrangement n D} (hA : A.IsGreat) (h : A.AFlip B) : B.IsGreat := by
  obtain ⟨d, e, hT, hanti, hT', rfl⟩ := h
  intro a b c hab hac hbc s hs x y hxy hx hy d₁ hd₁ e₁ he₁
  obtain ⟨s₀, hs₀⟩ := Arrangement.exists_isSide (A := A) c
  obtain ⟨s₁, hs₁, -, hx₁⟩ := flip_isSide hT hs₀
  obtain ⟨s₂, hs₂, -, hx₂⟩ := flip_isSide hT' hs₁
  have hcx : ∀ z : A.Crossing, Arrangement.Crossing.curves A z = {a, b} →
      c ∉ Arrangement.Crossing.curves A z := fun z hz => by
    rw [hz, mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hac, Ne.symm hbc⟩
  -- the correction of the side of a crossing of `a, b` is the same for both crossings
  set T := A.cellOf d
  set T' := A.cellOf e
  have hcor' : Arrangement.Cell.corners (A.flip d hT) ((A.flip d hT).cellOf e) =
      Arrangement.Cell.corners A T' := by
    simp only [Arrangement.Cell.corners]; rw [flip_darts_antipodal hT hanti]; rfl
  have hcur' : Arrangement.Cell.curves (A.flip d hT) ((A.flip d hT).cellOf e) =
      Arrangement.Cell.curves A T' := by
    simp only [Arrangement.Cell.curves]; rw [flip_darts_antipodal hT hanti]; rfl
  have hsubT : ∀ z ∈ Arrangement.Cell.corners A T,
      Arrangement.Crossing.curves A z ⊆ Arrangement.Cell.curves A T := by
    intro z hz C hC
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hz
    have hwT : A.cellOf w = T := Orbit.mem_darts.1 hw
    rw [A.curves_crossingOf, mem_insert, mem_singleton] at hC
    rcases hC with rfl | rfl
    · exact mem_image.2 ⟨w, hw, rfl⟩
    · rw [Arrangement.curve_σ_tri (Arrangement.isTriangle_of hT hwT)]
      refine mem_image.2 ⟨_, ?_, rfl⟩
      rw [Orbit.mem_darts]
      show A.cellOf (A.φ (A.φ w)) = _
      rw [A.cellOf_φ, A.cellOf_φ, hwT]
  have hδ : ∀ z : A.Crossing,
      ((if z ∈ Arrangement.Cell.corners A T ∧ c ∈ Arrangement.Cell.curves A T then (1 : ZMod 2)
        else 0) +
        if z ∈ Arrangement.Cell.corners A T' ∧ c ∈ Arrangement.Cell.curves A T then 1 else 0) =
      if Arrangement.Crossing.curves A z ⊆ Arrangement.Cell.curves A T ∧
        c ∈ Arrangement.Cell.curves A T then 1 else 0 := by
    intro z
    have hT'c : z ∈ Arrangement.Cell.corners A T' ↔
        Arrangement.Crossing.curves A z ⊆ Arrangement.Cell.curves A T ∧
          z ∉ Arrangement.Cell.corners A T := by
      rw [hanti.2.2, mem_filter]; simp
    by_cases hc : c ∈ Arrangement.Cell.curves A T
    · by_cases hz : z ∈ Arrangement.Cell.corners A T
      · rw [if_pos ⟨hz, hc⟩, if_neg (fun h => ((hT'c.1 h.1).2 hz)), if_pos ⟨hsubT z hz, hc⟩,
          add_zero]
      · rw [if_neg (fun h => hz h.1), zero_add]
        by_cases hs : Arrangement.Crossing.curves A z ⊆ Arrangement.Cell.curves A T
        · rw [if_pos ⟨hT'c.2 ⟨hs, hz⟩, hc⟩, if_pos ⟨hs, hc⟩]
        · rw [if_neg (fun h => hs (hT'c.1 h.1).1), if_neg (fun h => hs h.1)]
    · rw [if_neg (fun h => hc h.2), if_neg (fun h => hc h.2), if_neg (fun h => hc h.2),
        add_zero]
  have hside : ∀ z : A.Crossing, Arrangement.Crossing.curves A z = {a, b} →
      ((A.flip d hT).flip e hT').crossSide s₂ z = A.crossSide s₀ z +
        if {a, b} ⊆ Arrangement.Cell.curves A T ∧ c ∈ Arrangement.Cell.curves A T then 1
        else 0 := by
    intro z hz
    have h1 := hx₁ z (hcx z hz)
    have h2 := hx₂ z (hcx z hz)
    rw [hcor', hcur', curves_antipodal hanti] at h2
    rw [h2, h1, add_assoc, ← hz]
    exact congrArg _ (hδ z)
  have hcd : ∀ (z : A.Crossing) (w : D), w ∈ z.darts → Arrangement.Crossing.curves A z = {a, b} →
      s₂ (((A.flip d hT).flip e hT').cellOf w) = s₀ (A.cellOf w) +
        if {a, b} ⊆ Arrangement.Cell.curves A T ∧ c ∈ Arrangement.Cell.curves A T then 1
        else 0 := by
    intro z w hw hz
    have hzw : A.crossingOf w = z := Orbit.mem_darts.1 hw
    subst hzw
    rw [← crossSide_eq hs₂ (d := w) (hcx _ hz), ← crossSide_eq hs₀ (hcx _ hz)]
    exact hside _ hz
  have hK := hA a b c hab hac hbc s₀ hs₀ x y hxy hx hy d₁ hd₁ e₁ he₁
  have e1 := hcd x d₁ hd₁ hx
  have e2 := hcd y e₁ he₁ hy
  rcases hs₂.eq_or_eq_add_one hs with h | h <;> subst h
  · rw [e1, e2]; intro hc; exact hK (add_right_cancel hc)
  · show s₂ _ + 1 ≠ s₂ _ + 1
    rw [e1, e2]; intro hc; exact hK (add_right_cancel (add_right_cancel hc))

/-- In a great arrangement every triangle can be flipped antipodally. -/
theorem exists_aflip (hA : A.IsGreat) {d : D} (hT : A.IsTriangle (A.cellOf d)) :
    ∃ hT' : (A.flip d hT).IsTriangle ((A.flip d hT).cellOf (A.α (ant A d))),
      A.AFlip ((A.flip d hT).flip (A.α (ant A d)) hT') :=
  ⟨flip_isTriangle_antipodal hT (isAntipodalTri_ant hA hT),
    _, _, hT, isAntipodalTri_ant hA hT, _, rfl⟩

end Pca.Great
