/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: Theorem 16, the cells at the first event (`doc/pca/circ.md`)

* `digon_of_sides`: two crossings `x, y` of a pair `a, b` that are consecutive on both circles
  bound a digon (either orientation of the lens closes up),
* `exists_outer`: the outward crossing of a line through an inner point `P`,
* `foot_comm`, `foot_norm_comm`: the foot point does not depend on the order of the planes.
-/
import Pca.Circ.Thm16

open Equiv Finset Matrix

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- A dart whose face orbit closes after two distinct steps bounds a digon. -/
theorem isDigon_of_φ2 {d : D} (h2 : A.φ (A.φ d) = d) (h1 : A.φ d ≠ d) :
    A.IsDigon (A.cellOf d) := by
  unfold Arrangement.IsDigon Arrangement.IsKCell
  rw [A.size_cellOf]
  unfold period
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, by simpa using h2⟩, fun m hm ⟨hm0, hmd⟩ => ?_⟩
  interval_cases m
  exact h1 (by simpa using hmd)

theorem foot_norm_comm {ui uj : V} {hi hj : ℝ} (hw : ui ⨯₃ uj ≠ 0) :
    foot uj ui hj hi ⬝ᵥ foot uj ui hj hi = foot ui uj hi hj ⬝ᵥ foot ui uj hi hj := by
  have hw' : uj ⨯₃ ui ≠ 0 := by
    intro e; apply hw; rw [← cross_anticomm, e, neg_zero]
  apply le_antisymm
  · exact foot_le hw' (dot_foot_right _ _ _ _ hw) (dot_foot_left _ _ _ _ hw)
  · exact foot_le hw (dot_foot_right _ _ _ _ hw') (dot_foot_left _ _ _ _ hw')

namespace IsCircleRep

variable {u : Fin n → V} {h : Fin n → ℝ} {pt : A.Crossing → V} {sgn : D → ℝ}
variable (R : IsCircleRep A u h pt sgn)
include R

/-- Both darts along a segment `X Y` of the circle `a`, given a reference sign `r`: every other
crossing `z` has `orient (X, Y, z) * r < 0`. -/
theorem heading_pair_r {a : Fin n} {X Y : A.Crossing} (haX : a ∈ Arrangement.Crossing.curves A X)
    (haY : a ∈ Arrangement.Crossing.curves A Y) (hXY : X ≠ Y) {r : ℝ} (hr : r ≠ 0)
    (hC : ∀ z, a ∈ Arrangement.Crossing.curves A z → z ≠ X → z ≠ Y →
      orient (u a) (pt X) (pt Y) (pt z) * r < 0) :
    ∃ d d' : D, A.crossingOf d = X ∧ A.curve d = a ∧ sgn d = (if 0 < r then -1 else 1) ∧
      A.crossingOf d' = Y ∧ A.curve d' = a ∧ sgn d' = -(if 0 < r then -1 else 1) ∧
      A.α d = d' ∧ A.α d' = d := by
  obtain ⟨hsn, hpm⟩ := sign_choice hr
  set s := (if 0 < r then (-1 : ℝ) else 1)
  obtain ⟨d, hdX, hda, hds, hdY⟩ := R.exists_heading haX haY hXY hpm
    (fun z hz h1 h2 => pos_of_two_neg (hC z hz h1 h2) hsn)
  obtain ⟨d', hd'Y, hd'a, hd's, hd'X⟩ := R.exists_heading haY haX hXY.symm
    (s := -s) (by rcases hpm with e | e <;> rw [e] <;> norm_num)
    (fun z hz h1 h2 => by
      rw [orient_swap]
      have := pos_of_two_neg (hC z hz h2 h1) hsn
      linarith)
  have e1 : A.α d = d' := R.dart_unique (by rw [hd'Y, hdY]) (by rw [A.curve_α, hda, hd'a])
    (by rw [R.sgn_α, hds, hd's])
  exact ⟨d, d', hdX, hda, hds, hd'Y, hd'a, hd's, e1, by rw [← e1, A.isArrangement.α_α]⟩

/-- **The lens.** If the two crossings `x, y` of `a, b` are consecutive on the circle `a` and on
the circle `b`, the arrangement has a digon. -/
theorem digon_of_sides {a b : Fin n} (hab : a ≠ b) {x y : A.Crossing} (hxy : x ≠ y)
    (hx : Arrangement.Crossing.curves A x = {a, b}) (hy : Arrangement.Crossing.curves A y = {a, b})
    {ra rb : ℝ} (hra : ra ≠ 0) (hrb : rb ≠ 0)
    (Ca : ∀ z, a ∈ Arrangement.Crossing.curves A z → z ≠ x → z ≠ y →
      orient (u a) (pt x) (pt y) (pt z) * ra < 0)
    (Cb : ∀ z, b ∈ Arrangement.Crossing.curves A z → z ≠ x → z ≠ y →
      orient (u b) (pt x) (pt y) (pt z) * rb < 0) :
    ∃ f : A.Cell, A.IsDigon f := by
  have memx : a ∈ Arrangement.Crossing.curves A x ∧ b ∈ Arrangement.Crossing.curves A x :=
    ⟨by rw [hx]; simp, by rw [hx]; simp⟩
  have memy : a ∈ Arrangement.Crossing.curves A y ∧ b ∈ Arrangement.Crossing.curves A y :=
    ⟨by rw [hy]; simp, by rw [hy]; simp⟩
  obtain ⟨dxy, dyx, h1, h2, h3, h4, h5, h6, αd, αd'⟩ :=
    R.heading_pair_r memx.1 memy.1 hxy hra Ca
  obtain ⟨exy, eyx, k1, k2, k3, k4, k5, k6, αe, αe'⟩ :=
    R.heading_pair_r memx.2 memy.2 hxy hrb Cb
  obtain ⟨l, hl0, ex, ey, -⟩ := R.pair_lam hab hxy hx hy
  have hw := R.cross_ne_zero hab
  have hpos := dot_self_pos hw
  have dx : det3 (u a) (u b) (pt x) = l * ((u a ⨯₃ u b) ⬝ᵥ (u a ⨯₃ u b)) := by
    rw [det3_cross, ex, dotProduct_add, cross_dot_foot, zero_add, dotProduct_smul, smul_eq_mul]
  have dy : det3 (u a) (u b) (pt y) = -(l * ((u a ⨯₃ u b) ⬝ᵥ (u a ⨯₃ u b))) := by
    rw [det3_cross, ey, dotProduct_sub, cross_dot_foot, zero_sub, dotProduct_smul, smul_eq_mul]
  set sa := (if 0 < ra then (-1 : ℝ) else 1)
  set sb := (if 0 < rb then (-1 : ℝ) else 1)
  have hsa : sa = 1 ∨ sa = -1 := (sign_choice hra).2
  have hsb : sb = 1 ∨ sb = -1 := (sign_choice hrb).2
  have hne : sa * sb * l ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hl0 <;>
      [rcases hsa with e | e; rcases hsb with e | e] <;> rw [e] <;> norm_num
  rcases lt_or_gt_of_ne hne with hneg | hposi
  · -- the digon `dxy, eyx`
    have σy : A.σ dyx = eyx := R.σ_eq_of_det (by rw [k4, h4]) (by rw [k5, h5]; exact hab.symm)
      (by rw [h5, k5, h4, h6, k6, dy]; nlinarith [mul_pos hpos (neg_pos.2 hneg)])
    have σx : A.σ exy = dxy := R.σ_eq_of_det (by rw [h1, k1]) (by rw [h2, k2]; exact hab)
      (by rw [k2, h2, k1, k3, h3, det3_swap, dx]; nlinarith [mul_pos hpos (neg_pos.2 hneg)])
    have φ1 : A.φ dxy = eyx := by rw [Arrangement.φ_apply, αd, σy]
    have φ2 : A.φ eyx = dxy := by rw [Arrangement.φ_apply, αe', σx]
    exact ⟨_, isDigon_of_φ2 (d := dxy) (by rw [φ1, φ2]) (by
      rw [φ1]; intro e; have := congrArg A.curve e; rw [k5, h2] at this; exact hab this.symm)⟩
  · -- the digon `exy, dyx`
    have σy : A.σ eyx = dyx := R.σ_eq_of_det (by rw [h4, k4]) (by rw [h5, k5]; exact hab)
      (by rw [k5, h5, k4, k6, h6, det3_swap, dy]; nlinarith [mul_pos hpos hposi])
    have σx : A.σ dxy = exy := R.σ_eq_of_det (by rw [k1, h1]) (by rw [k2, h2]; exact hab.symm)
      (by rw [h2, k2, h1, h3, k3, dx]; nlinarith [mul_pos hpos hposi])
    have φ1 : A.φ exy = dyx := by rw [Arrangement.φ_apply, αe, σy]
    have φ2 : A.φ dyx = exy := by rw [Arrangement.φ_apply, αd', σx]
    exact ⟨_, isDigon_of_φ2 (d := exy) (by rw [φ1, φ2]) (by
      rw [φ1]; intro e; have := congrArg A.curve e; rw [h5, k2] at this; exact hab this)⟩

/-- The outward crossing of the line `E_i ∩ E_j` through an inner point `P` (not the foot point):
`P = X + τ (X' - X)` with `τ > 0`, `⟨X - P, P - m⟩ > 0`, and `X = P - a w` with
`a ⟨w, X⟩ < 0`. -/
theorem exists_outer {i j : Fin n} (hij : i ≠ j) {P : V} (hPi : u i ⬝ᵥ P = h i)
    (hPj : u j ⬝ᵥ P = h j) (hPin : P ⬝ᵥ P < 1) (hPm : P ≠ foot (u i) (u j) (h i) (h j)) :
    ∃ (X X' : A.Crossing) (τ a : ℝ), X ≠ X' ∧ Arrangement.Crossing.curves A X = {i, j} ∧
      Arrangement.Crossing.curves A X' = {i, j} ∧ 0 < τ ∧ P = pt X + τ • (pt X' - pt X) ∧
      0 < (pt X - P) ⬝ᵥ (P - foot (u i) (u j) (h i) (h j)) ∧
      pt X = P - a • (u i ⨯₃ u j) ∧ a * ((u i ⨯₃ u j) ⬝ᵥ pt X) < 0 := by
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_pair A hij
  obtain ⟨l, hl0, ex, ey, hl2⟩ := R.pair_lam hij hxy hx hy
  have hw := R.cross_ne_zero hij
  have hpos := dot_self_pos hw
  set m := foot (u i) (u j) (h i) (h j)
  set w := u i ⨯₃ u j
  have hmw : w ⬝ᵥ m = 0 := cross_dot_foot _ _ _ _
  have key := eq_smul_cross_of_perp hw (v := P - m)
    (by rw [dotProduct_sub, hPi, dot_foot_left _ _ _ _ hw, sub_self])
    (by rw [dotProduct_sub, hPj, dot_foot_right _ _ _ _ hw, sub_self])
  set π := (w ⬝ᵥ (P - m)) / (w ⬝ᵥ w)
  have hPπ : P = m + π • w := by rw [← key]; abel
  have hπ0 : π ≠ 0 := fun e => hPm (by rw [hPπ, e, zero_smul, add_zero])
  have hnorm : P ⬝ᵥ P = m ⬝ᵥ m + π ^ 2 * (w ⬝ᵥ w) := by
    rw [hPπ]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm m w, hmw]; ring
  have hπl : π ^ 2 < l ^ 2 := by
    have : π ^ 2 * (w ⬝ᵥ w) < l ^ 2 * (w ⬝ᵥ w) := by linarith
    exact lt_of_mul_lt_mul_right this hpos.le
  have hlx : w ⬝ᵥ pt x = l * (w ⬝ᵥ w) := by
    rw [ex, dotProduct_add, hmw, zero_add, dotProduct_smul, smul_eq_mul]
  have hly : w ⬝ᵥ pt y = -(l * (w ⬝ᵥ w)) := by
    rw [ey, dotProduct_sub, hmw, zero_sub, dotProduct_smul, smul_eq_mul]
  rcases lt_or_gt_of_ne (mul_ne_zero hπ0 hl0) with hs | hs
  · -- `π l < 0`: the outward crossing is `y`
    refine ⟨y, x, (π + l) / (2 * l), π + l, hxy.symm, hy, hx, ?_, ?_, ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hl0 with h1 | h1
      · exact div_pos_of_neg_of_neg (by nlinarith) (by linarith)
      · exact div_pos (by nlinarith) (by linarith)
    · rw [hPπ, ex, ey]; ext k
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; field_simp; ring
    · rw [hPπ, ey]
      have e : (m - l • w - (m + π • w)) ⬝ᵥ (m + π • w - m) = -(l + π) * π * (w ⬝ᵥ w) := by
        simp only [dot_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [e]; nlinarith
    · rw [hPπ, ey]; ext k; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    · rw [hly]; nlinarith
  · -- `π l > 0`: the outward crossing is `x`
    refine ⟨x, y, (l - π) / (2 * l), π - l, hxy, hx, hy, ?_, ?_, ?_, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hl0 with h1 | h1
      · exact div_pos_of_neg_of_neg (by nlinarith) (by linarith)
      · exact div_pos (by nlinarith) (by linarith)
    · rw [hPπ, ex, ey]; ext k
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; field_simp; ring
    · rw [hPπ, ex]
      have e : (m + l • w - (m + π • w)) ⬝ᵥ (m + π • w - m) = (l - π) * π * (w ⬝ᵥ w) := by
        simp only [dot_eq, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
      rw [e]; nlinarith
    · rw [hPπ, ex]; ext k; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    · rw [hlx]; nlinarith

end IsCircleRep

end Pca.Circ

namespace Pca.Circ

/-- The foot point does not depend on the order of the two planes. -/
theorem foot_comm {ui uj : V} {hi hj : ℝ} (hw : ui ⨯₃ uj ≠ 0) :
    foot uj ui hj hi = foot ui uj hi hj := by
  have hw' : uj ⨯₃ ui ≠ 0 := by
    intro e; apply hw; rw [← cross_anticomm, e, neg_zero]
  set v := foot uj ui hj hi - foot ui uj hi hj
  have h1 : ui ⬝ᵥ v = 0 := by
    rw [dotProduct_sub, dot_foot_right _ _ _ _ hw', dot_foot_left _ _ _ _ hw, sub_self]
  have h2 : uj ⬝ᵥ v = 0 := by
    rw [dotProduct_sub, dot_foot_left _ _ _ _ hw', dot_foot_right _ _ _ _ hw, sub_self]
  have h3 : (ui ⨯₃ uj) ⬝ᵥ v = 0 := by
    have e1 : (ui ⨯₃ uj) ⬝ᵥ foot uj ui hj hi = 0 := by
      rw [← cross_anticomm, neg_dotProduct, cross_dot_foot, neg_zero]
    rw [dotProduct_sub, e1, cross_dot_foot, sub_self]
  have key := eq_smul_cross_of_perp hw h1 h2
  rw [h3, zero_div, zero_smul] at key
  exact sub_eq_zero.1 key

end Pca.Circ
