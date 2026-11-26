/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The quarter lemma, final form (`doc/pca/great.md` section 3.3)
-/
import Pca.Great.Quarter

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

namespace Frame

variable (F : Frame A) (hA : A.IsGreat)
include hA

/-- The triangle of `ℓ, w, w'` from consecutive crossings: `w` follows `w'` along `ℓ`. -/
theorem tri_of_adj {ℓ w w' : Fin n} (hℓ : ℓ ≠ F.c0) (hw : w ≠ F.c0) (hw' : w' ≠ F.c0)
    (hℓw : ℓ ≠ w) (hℓw' : ℓ ≠ w') (hww' : w ≠ w') (hl : F.hpos ℓ w = F.hpos ℓ w' + 1)
    (aw : F.hpos w w' = F.hpos w ℓ + 1 ∨ F.hpos w w' + 1 = F.hpos w ℓ)
    (aw' : F.hpos w' w = F.hpos w' ℓ + 1 ∨ F.hpos w' w + 1 = F.hpos w' ℓ) (N : ZMod 2)
    (hN : F.sR ℓ (F.cell w (F.hpos w w')) = N) :
    ∃ d : D, A.IsTriangle (A.cellOf d) ∧ A.curve d = ℓ ∧ F.sR ℓ (A.cellOf d) = N ∧
      F.s0 (A.cellOf d) = 1 ∧ Arrangement.Cell.curves A (A.cellOf d) = {ℓ, w, w'} := by
  have hn := A.two_le_n
  have kw := (F.hpos_spec hA hℓ hw hℓw).2.1
  set z := (A.straight ^ F.hpos ℓ w') (F.β ℓ)
  have hz : A.curve z = ℓ := by rw [curve_straight_pow, F.curve_β hA hℓ]
  have hxw' : A.crossingOf z = A.crossingOf ((A.straight ^ F.hpos w' ℓ) (F.β w')) :=
    F.crossingOf_hpos hA hℓ hw' hℓw'
  have hxw : A.crossingOf (A.α z) = A.crossingOf ((A.straight ^ F.hpos w ℓ) (F.β w)) := by
    rw [F.far_fwd hA, ← hl]; exact F.crossingOf_hpos hA hℓ hw hℓw
  have hsz : F.sR ℓ (A.cellOf z) = 1 := by
    rw [side_straight_pow_self (F.isSide_sR ℓ) (F.curve_β hA hℓ)]; exact F.sR_β ℓ
  have hv : A.crossingOf ((A.straight ^ F.hpos w w') (F.β w)) =
      A.crossingOf ((A.straight ^ F.hpos w' w) (F.β w')) := F.crossingOf_hpos hA hw hw' hww'
  have hvℓ : ℓ ∉ Arrangement.Crossing.curves A
      (A.crossingOf ((A.straight ^ F.hpos w w') (F.β w))) := by
    rw [F.curves_hcross hA hw hw' hww', mem_insert, mem_singleton, not_or]; exact ⟨hℓw, hℓw'⟩
  have hN' : F.sR ℓ (F.cell w' (F.hpos w' w)) = N := by
    rw [← hN]; exact (side_same_crossing (F.isSide_sR ℓ) hv hvℓ).symm
  have hs0z : F.s0 (A.cellOf z) = 1 :=
    F.s0_cell hA hℓ (by have := (F.hpos_spec hA hℓ hw' hℓw').2.1; omega)
  -- the curves of the triangle
  have hcurves : ∀ {d : D}, A.IsTriangle (A.cellOf d) → A.curve d = ℓ →
      ∀ {u u' : Fin n}, A.curve (A.φ d) = u → A.curve (A.φ (A.φ d)) = u' →
      Arrangement.Cell.curves A (A.cellOf d) = {ℓ, u, u'} := by
    intro d hT hd u u' h1 h2
    ext C
    simp only [Arrangement.Cell.curves, mem_image, Orbit.mem_darts, mem_insert, mem_singleton]
    constructor
    · rintro ⟨c, hc, rfl⟩
      rcases (Arrangement.tri_mem_iff hT).1 hc with rfl | rfl | rfl
      · exact Or.inl hd
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h2)
    · rintro (h | h | h)
      · exact ⟨d, rfl, hd.trans h.symm⟩
      · exact ⟨A.φ d, A.cellOf_φ d, h1.trans h.symm⟩
      · exact ⟨A.φ (A.φ d), by show A.cellOf (A.φ (A.φ d)) = _; rw [A.cellOf_φ, A.cellOf_φ],
          h2.trans h.symm⟩
  have hNc : N = 0 ∨ N = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) N
  rcases hNc with rfl | rfl
  · -- the dart from the crossing with `w` back to the crossing with `w'`
    set y := (A.straight ^ F.hpos ℓ w) (F.β ℓ)
    have hy : A.curve y = ℓ := by rw [curve_straight_pow, F.curve_β hA hℓ]
    have hσy : A.curve (A.σ y) ≠ ℓ := by rw [← hy]; exact A.isArrangement.curve_σ y
    have hxy : A.crossingOf y = A.crossingOf ((A.straight ^ F.hpos w ℓ) (F.β w)) :=
      F.crossingOf_hpos hA hℓ hw hℓw
    have hσyw : A.curve (A.σ y) = w := by
      have hm := A.mem_curves_crossingOf_σ y
      rw [hxy, F.curves_hcross hA hw hℓ (Ne.symm hℓw), mem_insert, mem_singleton] at hm
      rcases hm with hm | hm
      · exact hm
      · exact absurd hm hσy
    have hdc : A.curve (A.σ (A.σ y)) = ℓ := by rw [A.isArrangement.curve_σσ, hy]
    have h1 : A.crossingOf (A.σ (A.σ y)) = A.crossingOf ((A.straight ^ F.hpos w ℓ) (F.β w)) := by
      rw [A.crossingOf_σ, A.crossingOf_σ]; exact hxy
    have h2 : A.crossingOf (A.α (A.σ (A.σ y))) =
        A.crossingOf ((A.straight ^ F.hpos w' ℓ) (F.β w')) := by
      show A.crossingOf (A.α (A.σ (A.σ ((A.straight ^ F.hpos ℓ w) (F.β ℓ))))) = _
      rw [hl, F.far_bwd hA]; exact hxw'
    have hsd : F.sR ℓ (A.cellOf (A.σ (A.σ y))) = 0 := by
      rw [A.side_σσ (F.isSide_sR ℓ), if_pos hy, if_neg hσy, add_zero,
        side_straight_pow_self (F.isSide_sR ℓ) (F.curve_β hA hℓ), F.sR_β]
      decide
    obtain ⟨hT, hc1, hc2⟩ := F.tri_cell hA hℓ hw' hw hℓw' hℓw (Ne.symm hww') hdc h1 h2
      (hsd.trans hN'.symm) aw' (aw.symm.imp (fun h => h) (fun h => h) |> fun h => by
        rcases aw with h | h
        · exact Or.inr h.symm
        · exact Or.inl h.symm)
    refine ⟨_, hT, hdc, hsd, ?_, ?_⟩
    · rw [A.side_σσ F.isSide_s0, if_neg (by rw [hy]; exact hℓ), if_neg (by rw [hσyw]; exact hw),
        add_zero, add_zero]
      exact F.s0_cell hA hℓ kw
    · rw [hcurves hT hdc hc1 hc2, pair_comm w' w]
  · obtain ⟨hT, hc1, hc2⟩ := F.tri_cell hA hℓ hw hw' hℓw hℓw' hww' hz hxw' hxw
      (hsz.trans hN.symm) aw (by rcases aw' with h | h
                                 · exact Or.inr h.symm
                                 · exact Or.inl h.symm)
    exact ⟨z, hT, hz, hsz, hs0z, hcurves hT hz hc1 hc2⟩

/-- Two crossings on a chord with no crossing of a chord of `T` strictly between them, and no
curve outside `T` separating them, are consecutive. -/
theorem adj_pair {T : Finset (Fin n)}
    (hout : ∀ t, t ∉ T → ∀ d d' : D,
      F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d) →
      Arrangement.Crossing.curves A (A.crossingOf d) ⊆ T → F.s0 (A.cellOf d) = 1 →
      F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d') →
      Arrangement.Crossing.curves A (A.crossingOf d') ⊆ T → F.s0 (A.cellOf d') = 1 →
      F.sR t (A.cellOf d) = F.sR t (A.cellOf d'))
    {t a b : Fin n} (ht : t ≠ F.c0) (ha : a ≠ F.c0) (hb : b ≠ F.c0) (hta : t ≠ a) (htb : t ≠ b)
    (hab : a ≠ b) (htT : t ∈ T) (haT : a ∈ T) (hbT : b ∈ T)
    (hT : ∀ u ∈ T, u ≠ F.c0 → u ≠ t → u ≠ a → u ≠ b →
      ¬ Comb.Bet (F.hpos t u) (F.hpos t a) (F.hpos t b)) :
    F.hpos t a = F.hpos t b + 1 ∨ F.hpos t b = F.hpos t a + 1 := by
  have hne : F.hpos t a ≠ F.hpos t b := fun h => hab (by
    have := (F.chordSys hA).H_inj ⟨t, ht⟩ ⟨a, ha⟩ ⟨b, hb⟩ (fun h' => hta (congrArg Subtype.val h').symm)
      (fun h' => htb (congrArg Subtype.val h').symm) h
    exact congrArg Subtype.val this)
  have ka := (F.hpos_spec hA ht ha hta).2.1
  have kb := (F.hpos_spec hA ht hb htb).2.1
  have hno : ∀ {x y : ℕ}, (x = F.hpos t a ∧ y = F.hpos t b) ∨ (x = F.hpos t b ∧ y = F.hpos t a) →
      ∀ u, u ≠ F.c0 → u ≠ t → ¬ (x < F.hpos t u ∧ F.hpos t u < y) := by
    intro x y hxy u hu0 hut hbet
    have hbet' : Comb.Bet (F.hpos t u) (F.hpos t a) (F.hpos t b) := by
      unfold Comb.Bet; omega
    have hua : u ≠ a := by rintro rfl; unfold Comb.Bet at hbet'; omega
    have hub : u ≠ b := by rintro rfl; unfold Comb.Bet at hbet'; omega
    by_cases huT : u ∈ T
    · exact hT u huT hu0 hut hua hub hbet'
    · exact F.no_out_between hA hout ht ha hb hta htb htT haT hbT huT hu0 hut hbet'
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact Or.inr (F.adj_of hA ht h kb (hno (Or.inl ⟨rfl, rfl⟩)))
  · exact Or.inl (F.adj_of hA ht h ka (hno (Or.inr ⟨rfl, rfl⟩)))

/-- **Quarter lemma** (relative form). -/
theorem quarter {ℓ : Fin n} (hℓ : ℓ ≠ F.c0) (N : ZMod 2)
    (T : Finset (Fin n)) (hℓT : ℓ ∈ T)
    (hv : ∃ d : D, F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d) ∧
      ℓ ∉ Arrangement.Crossing.curves A (A.crossingOf d) ∧
      Arrangement.Crossing.curves A (A.crossingOf d) ⊆ T ∧
      F.s0 (A.cellOf d) = 1 ∧ F.sR ℓ (A.cellOf d) = N)
    (hout : ∀ t, t ∉ T → ∀ d d' : D,
      F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d) →
      Arrangement.Crossing.curves A (A.crossingOf d) ⊆ T → F.s0 (A.cellOf d) = 1 →
      F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d') →
      Arrangement.Crossing.curves A (A.crossingOf d') ⊆ T → F.s0 (A.cellOf d') = 1 →
      F.sR t (A.cellOf d) = F.sR t (A.cellOf d')) :
    ∃ d : D, A.IsTriangle (A.cellOf d) ∧ A.curve d = ℓ ∧
      F.c0 ∉ Arrangement.Cell.curves A (A.cellOf d) ∧
      Arrangement.Cell.curves A (A.cellOf d) ⊆ T ∧
      F.s0 (A.cellOf d) = 1 ∧ F.sR ℓ (A.cellOf d) = N := by
  classical
  have hn := A.two_le_n
  set S := F.chordSys hA
  let ℓ' : F.Ch := ⟨ℓ, hℓ⟩
  let T' : Finset F.Ch := T.subtype (fun e => e ≠ F.c0)
  have memT' : ∀ e : F.Ch, e ∈ T' ↔ e.1 ∈ T := fun e => mem_subtype
  have hℓT' : ℓ' ∈ T' := (memT' ℓ').2 hℓT
  -- `Rt` and the quarter in terms of side functions
  have hInQ : ∀ (t : F.Ch), t ≠ ℓ' → ∀ k, k < n - 1 →
      (S.InQ ℓ' (N = 1) t k ↔ F.sR ℓ (F.cell t.1 k) = N) := by
    intro t ht k hk
    unfold Comb.ChordSys.InQ
    rw [F.rt_iff hA (Ne.symm ht) hk]
    have : ∀ a : ZMod 2, (a = 1 ↔ N = 1) ↔ a = N := by
      intro a
      have h1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
      have h2 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) N
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> decide
    exact this _
  -- the given crossing
  obtain ⟨d0, h0c, h0ℓ, h0T, h0s, h0N⟩ := hv
  set a := A.curve d0
  set b := A.curve (A.σ d0)
  have hab : a ≠ b := (A.isArrangement.curve_σ d0).symm
  have hcur0 := A.curves_crossingOf d0
  have ha0 : a ≠ F.c0 := fun h => h0c (by rw [← h]; exact A.mem_curves_crossingOf d0)
  have hb0 : b ≠ F.c0 := fun h => h0c (by rw [← h]; exact A.mem_curves_crossingOf_σ d0)
  have haℓ : a ≠ ℓ := fun h => h0ℓ (by rw [← h]; exact A.mem_curves_crossingOf d0)
  have hbℓ : b ≠ ℓ := fun h => h0ℓ (by rw [← h]; exact A.mem_curves_crossingOf_σ d0)
  have hx0 := F.eq_hcross hA ha0 hb0 hab hcur0 h0s
  have hex : ∃ e f, e ∈ T' ∧ e ≠ ℓ' ∧ S.Cand ℓ' (N = 1) T' e f := by
    refine ⟨⟨a, ha0⟩, ⟨b, hb0⟩, (memT' _).2 (h0T (A.mem_curves_crossingOf d0)),
      fun h => haℓ (congrArg Subtype.val h), (memT' _).2 (h0T (A.mem_curves_crossingOf_σ d0)),
      fun h => hbℓ (congrArg Subtype.val h), fun h => hab (congrArg Subtype.val h).symm, ?_⟩
    refine (hInQ ⟨a, ha0⟩ (fun h => haℓ (congrArg Subtype.val h)) (F.hpos a b)
      (F.hpos_spec hA ha0 hb0 hab).2.1).2 ?_
    rw [← h0N]
    exact (side_same_crossing (F.isSide_sR ℓ) hx0 h0ℓ).symm
  obtain ⟨i, j, hiT, hiℓ, hij, C1, C3⟩ :=
    Comb.ChordSys.exists_tri_aux (S := S) (ℓ := ℓ') (Nq := N = 1) (T := T') hℓT' hex
  obtain ⟨⟨hjT, hjℓ, hji, hQij⟩, hfirst⟩ := hij
  obtain ⟨i0, hi0⟩ := i
  obtain ⟨j0, hj0⟩ := j
  have hiℓ0 : i0 ≠ ℓ := fun h => hiℓ (Subtype.ext h)
  have hjℓ0 : j0 ≠ ℓ := fun h => hjℓ (Subtype.ext h)
  have hji0 : j0 ≠ i0 := fun h => hji (Subtype.ext h)
  have hiT0 : i0 ∈ T := (memT' _).1 hiT
  have hjT0 : j0 ∈ T := (memT' _).1 hjT
  have toCh : ∀ {u : Fin n} (hu : u ≠ F.c0), u ∈ T → (⟨u, hu⟩ : F.Ch) ∈ T' :=
    fun hu h => (memT' _).2 h
  -- adjacency along `ℓ`
  have aℓ := F.adj_pair hA hout hℓ hi0 hj0 (Ne.symm hiℓ0) (Ne.symm hjℓ0) (Ne.symm hji0) hℓT
    hiT0 hjT0 (fun u huT hu0 huℓ hui huj => C1 ⟨u, hu0⟩ (toCh hu0 huT)
      (fun h => huℓ (congrArg Subtype.val h)) (fun h => hui (congrArg Subtype.val h))
      (fun h => huj (congrArg Subtype.val h)))
  -- adjacency along `i`
  have ai := F.adj_pair hA hout hi0 hℓ hj0 hiℓ0 (Ne.symm hji0) (Ne.symm hjℓ0) hiT0 hℓT hjT0
    (fun u huT hu0 hui huℓ huj hbet => by
      have hc : S.Cand ℓ' (N = 1) T' ⟨i0, hi0⟩ ⟨u, hu0⟩ :=
        ⟨toCh hu0 huT, fun h => huℓ (congrArg Subtype.val h),
          fun h => hui (congrArg Subtype.val h),
          Comb.ChordSys.inQ_of_bet (fun h => hiℓ h) hQij hbet⟩
      have := hfirst ⟨u, hu0⟩ hc (fun h => huj (congrArg Subtype.val h))
      change Comb.Bet (F.hpos i0 j0) (F.hpos i0 ℓ) (F.hpos i0 u) at this
      unfold Comb.Bet at this hbet; omega)
  -- adjacency along `j`
  have aj := F.adj_pair hA hout hj0 hℓ hi0 hjℓ0 hji0 (Ne.symm hiℓ0) hjT0 hℓT hiT0
    (fun u huT hu0 huj huℓ hui => C3 ⟨u, hu0⟩ (toCh hu0 huT)
      (fun h => huℓ (congrArg Subtype.val h)) (fun h => hui (congrArg Subtype.val h))
      (fun h => huj (congrArg Subtype.val h)))
  -- the side of the crossing `v` of `i` and `j`
  have hvi : F.sR ℓ (F.cell i0 (F.hpos i0 j0)) = N :=
    (hInQ ⟨i0, hi0⟩ hiℓ (F.hpos i0 j0) (F.hpos_spec hA hi0 hj0 (Ne.symm hji0)).2.1).1 hQij
  have hvj : F.sR ℓ (F.cell j0 (F.hpos j0 i0)) = N := by
    rw [← hvi]
    refine side_same_crossing (F.isSide_sR ℓ) (F.crossingOf_hpos hA hj0 hi0 hji0) ?_
    rw [F.curves_hcross hA hj0 hi0 hji0, mem_insert, mem_singleton, not_or]
    exact ⟨Ne.symm hjℓ0, Ne.symm hiℓ0⟩
  have fin : ∀ {w w' : Fin n}, w ≠ F.c0 → w' ≠ F.c0 → ℓ ≠ w → ℓ ≠ w' → w ≠ w' → w ∈ T →
      w' ∈ T → F.hpos ℓ w = F.hpos ℓ w' + 1 →
      (F.hpos w ℓ = F.hpos w w' + 1 ∨ F.hpos w w' = F.hpos w ℓ + 1) →
      (F.hpos w' ℓ = F.hpos w' w + 1 ∨ F.hpos w' w = F.hpos w' ℓ + 1) →
      F.sR ℓ (F.cell w (F.hpos w w')) = N →
      ∃ d : D, A.IsTriangle (A.cellOf d) ∧ A.curve d = ℓ ∧
        F.c0 ∉ Arrangement.Cell.curves A (A.cellOf d) ∧
        Arrangement.Cell.curves A (A.cellOf d) ⊆ T ∧
        F.s0 (A.cellOf d) = 1 ∧ F.sR ℓ (A.cellOf d) = N := by
    intro w w' hw hw' hℓw hℓw' hww' hwT hw'T hl aw aw' hN
    obtain ⟨d, hT, hd, hsN, hs0, hcur⟩ := F.tri_of_adj hA hℓ hw hw' hℓw hℓw' hww' hl
      (aw.symm.imp id id |> fun _ => by rcases aw with h | h
                                        · exact Or.inr h.symm
                                        · exact Or.inl h)
      (by rcases aw' with h | h
          · exact Or.inr h.symm
          · exact Or.inl h) N hN
    refine ⟨d, hT, hd, ?_, ?_, hs0, hsN⟩
    · rw [hcur]; simp only [mem_insert, mem_singleton, not_or]
      exact ⟨Ne.symm hℓ, Ne.symm hw, Ne.symm hw'⟩
    · rw [hcur]; intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
  rcases aℓ with h | h
  · exact fin hi0 hj0 (Ne.symm hiℓ0) (Ne.symm hjℓ0) (Ne.symm hji0) hiT0 hjT0 h ai
      (by rcases aj with h' | h'
          · exact Or.inl h'
          · exact Or.inr h') hvi
  · exact fin hj0 hi0 (Ne.symm hjℓ0) (Ne.symm hiℓ0) hji0 hjT0 hiT0 h aj ai hvj

end Frame

end Pca.Great
