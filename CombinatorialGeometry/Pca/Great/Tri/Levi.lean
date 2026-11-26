/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Levi's triangle theorem (`doc/pca/great.md` section 7)

In a simple arrangement of `n ≥ 3` pseudolines in the projective plane every pseudoline is adjacent
to at least `3` triangles, hence there are at least `n` triangles (Levi 1926). Great-pseudocircle
version (the double cover):

* `three_le_side`: for `n ≥ 4`, on each side of every curve `ℓ` there are at least `3` triangles
  with a side on `ℓ` (one lift of each projective triangle at `ℓ`);
* `six_le_tC`: for `n ≥ 3`, `t_ℓ ≥ 6` (`3` antipodal pairs);
* `two_mul_le_p3`: for `n ≥ 3`, `p_3 ≥ 2n`.

Proof (`n ≥ 4`): a first triangle `T₁ = {ℓ, e, f}` with a side on `ℓ` comes from the quarter lemma.
The quarter lemma with frame `e` (resp. `f`) in the projective region of `e, ℓ` (resp. `f, ℓ`) not
containing `T₁` gives `T₂` not touching `e` (resp. `T₃` not touching `f`); the region contains a
crossing by the walk lemma along `f` (resp. `e`). `T₂ ≠ T₃`: a triangle with a side on `ℓ` touching
neither `e` nor `f` and on the other side of both would have a corner on `ℓ` in the arc antipodal
to the side of `T₁` on `ℓ`, which has no crossing (walk lemma along `ℓ`). `n = 3`: every cell is a
triangle (Krupp).
-/
import Pca.Great.Tri.Quarter

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

theorem exists_not_mem (s : Finset (Fin n)) (h : s.card < n) : ∃ x, x ∉ s := by
  by_contra hc
  have : (univ : Finset (Fin n)) ⊆ s := fun x _ => by
    by_contra hx
    exact hc ⟨x, hx⟩
  have := card_le_card this
  rw [card_univ, Fintype.card_fin] at this
  omega

theorem zmod2_ne_self_add_one (a : ZMod 2) : a ≠ a + 1 := by revert a; decide

variable (hA : A.IsGreat)
include hA

/-- `n = 3`: every cell is a triangle. -/
theorem isTriangle_of_three (h3 : n = 3) (t : D) : A.IsTriangle (A.cellOf t) := by
  have fin3 : ∀ x y z w : Fin n, x ≠ y → x ≠ z → y ≠ z → w ≠ x → w ≠ z → w = y := by
    intro x y z w h1 h2 h3' h4 h5
    have := x.isLt; have := y.isLt; have := z.isLt; have := w.isLt
    simp only [ne_eq, Fin.ext_iff] at h1 h2 h3' h4 h5 ⊢
    omega
  have h3' : 3 ≤ n := h3.ge
  set a := A.curve t
  set b := A.curve (A.σ t)
  set c := A.curve (A.φ t)
  have hab : a ≠ b := (A.isArrangement.curve_σ t).symm
  have hca : c ≠ a := A.curve_φ_ne t
  have hcα : Arrangement.Crossing.curves A (A.crossingOf (A.α t)) = {a, c} := by
    rw [A.curves_crossingOf, A.curve_α]; rfl
  have hbc : b ≠ c := by
    intro h
    have := not_mem_next hA h3' t hab.symm (A.mem_curves_crossingOf_σ t)
    rw [hcα, h] at this
    exact this (by simp)
  set d2 := A.φ (A.φ t)
  -- the curve of `d2` is `b`
  have hφt : A.curve (A.φ t) = c := rfl
  have ha1 : a ∈ Arrangement.Crossing.curves A (A.crossingOf (A.φ t)) := by
    rw [Arrangement.φ_apply, A.crossingOf_σ, hcα]; simp
  have ha2 := not_mem_next hA h3' (A.φ t) (by rw [hφt]; exact hca.symm) ha1
  rw [A.curves_crossingOf, A.curve_α, hφt] at ha2
  have hd2a : A.curve d2 ≠ a := fun h => ha2 (by
    rw [show A.curve (A.σ (A.α (A.φ t))) = A.curve d2 from rfl, h]; simp)
  have hd2c : A.curve d2 ≠ c := A.curve_φ_ne (A.φ t)
  have hd2 : A.curve d2 = b := fin3 a b c _ hab hca.symm hbc hd2a hd2c
  -- the far end of `d2` is a crossing of `a` and `b`
  have hc1 : c ∈ Arrangement.Crossing.curves A (A.crossingOf d2) := by
    rw [show d2 = A.σ (A.α (A.φ t)) from rfl, A.crossingOf_σ]
    rw [← hφt, ← A.curve_α]; exact A.mem_curves_crossingOf _
  have hc2 := not_mem_next hA h3' d2 (by rw [hd2]; exact hbc.symm) hc1
  rw [A.curves_crossingOf, A.curve_α] at hc2
  have hza : A.curve (A.φ d2) = a := by
    refine fin3 b a c _ hab.symm hbc hca.symm (A.curve_φ_ne d2 |>.trans_eq hd2 |> fun h => ?_) ?_
    · exact h
    · exact fun h => hc2 (by rw [show A.curve (A.σ (A.α d2)) = A.curve (A.φ d2) from rfl, h]; simp)
  have hend : Arrangement.Crossing.curves A (A.crossingOf (A.α d2)) = {a, b} := by
    rw [A.curves_crossingOf, A.curve_α, hd2,
      show A.curve (A.σ (A.α d2)) = A.curve (A.φ d2) from rfl, hza, pair_comm]
  have hstart : Arrangement.Crossing.curves A (A.crossingOf t) = {a, b} := A.curves_crossingOf t
  have heq : A.crossingOf (A.α d2) = A.crossingOf t := by
    by_contra hne
    obtain ⟨sc, hsc⟩ := Arrangement.exists_isSide (A := A) c
    have := hA a b c hab hca.symm hbc sc hsc _ _ hne hend hstart (A.φ d2)
      (Orbit.mem_darts.2 (A.crossingOf_σ _)) t (Orbit.mem_darts.2 rfl)
    apply this
    rw [A.cellOf_φ, A.cellOf_φ, A.cellOf_φ]
  exact isTriangle_of_far_end heq (by rw [hd2]; exact hab.symm)

/-- **The three triangles**: for `n ≥ 4`, a triangle `T₁` with a side on `ℓ` has two more
triangles with a side on `ℓ` on the same side of `ℓ`. -/
theorem three_tri (h4 : 4 ≤ n) {ℓ : Fin n} {sl : A.Cell → ZMod 2} (hsl : A.IsSide ℓ sl)
    {t1 : D} (hT : A.IsTriangle (A.cellOf t1)) (ht1 : A.curve t1 = ℓ) :
    ∃ d2 d3 : D, A.IsTriangle (A.cellOf d2) ∧ A.curve d2 = ℓ ∧
      sl (A.cellOf d2) = sl (A.cellOf t1) ∧
      A.IsTriangle (A.cellOf d3) ∧ A.curve d3 = ℓ ∧ sl (A.cellOf d3) = sl (A.cellOf t1) ∧
      A.cellOf d2 ≠ A.cellOf t1 ∧ A.cellOf d3 ≠ A.cellOf t1 ∧ A.cellOf d2 ≠ A.cellOf d3 := by
  have h3 : 3 ≤ n := by omega
  have hφ3 : A.φ (A.φ (A.φ t1)) = t1 := A.φ_φ_φ_of_triangle hT
  set e := A.curve (A.φ t1)
  set f := A.curve (A.φ (A.φ t1))
  have heℓ : e ≠ ℓ := ht1 ▸ A.curve_φ_ne t1
  have hfe : f ≠ e := A.curve_φ_ne (A.φ t1)
  have hfℓ : f ≠ ℓ := by
    have := A.curve_φ_ne (A.φ (A.φ t1))
    rw [hφ3, ht1] at this; exact this.symm
  obtain ⟨g, hg⟩ := exists_not_mem {ℓ, e, f} (by
    have := card_insert_le ℓ ({e, f} : Finset (Fin n))
    have := card_insert_le e ({f} : Finset (Fin n))
    rw [card_singleton] at this; omega)
  simp only [mem_insert, mem_singleton, not_or] at hg
  obtain ⟨hgℓ, hge, hgf⟩ := hg
  obtain ⟨se, hse⟩ := Arrangement.exists_isSide (A := A) e
  obtain ⟨sf, hsf⟩ := Arrangement.exists_isSide (A := A) f
  -- the corners of `T₁`
  have m_ef_e : e ∈ Arrangement.Crossing.curves A (A.crossingOf (A.φ (A.φ t1))) := by
    rw [A.φ_apply (A.φ t1), A.crossingOf_σ]
    have := A.mem_curves_crossingOf (A.α (A.φ t1))
    rwa [A.curve_α] at this
  have m_ℓf_ℓ : ℓ ∈ Arrangement.Crossing.curves A (A.crossingOf (A.α (A.φ (A.φ t1)))) := by
    have := A.mem_curves_crossingOf_σ (A.α (A.φ (A.φ t1)))
    rwa [← Arrangement.φ_apply, hφ3, ht1] at this
  have m_ef_f : f ∈ Arrangement.Crossing.curves A (A.crossingOf (A.α (A.φ t1))) :=
    A.mem_curves_crossingOf_σ (A.α (A.φ t1))
  have m_ℓe_ℓ : ℓ ∈ Arrangement.Crossing.curves A (A.crossingOf (A.α (A.α (A.φ t1)))) := by
    rw [A.α_α, Arrangement.φ_apply, A.crossingOf_σ, ← ht1, ← A.curve_α]
    exact A.mem_curves_crossingOf _
  have m_ℓf_f : f ∈ Arrangement.Crossing.curves A (A.crossingOf t1) := by
    have := A.mem_curves_crossingOf (A.α (A.φ (A.φ t1)))
    rwa [A.curve_α, ← A.crossingOf_σ, ← Arrangement.φ_apply, hφ3] at this
  have m_ℓe_e : e ∈ Arrangement.Crossing.curves A (A.crossingOf (A.α t1)) :=
    A.mem_curves_crossingOf_σ (A.α t1)
  have c1 : A.cellOf (A.φ (A.φ t1)) = A.cellOf t1 := by rw [A.cellOf_φ, A.cellOf_φ]
  -- `T₂`: frame `e`, walk along `f`
  obtain ⟨d2, hT2, hd2, he2, hl2, hs2⟩ := tri_step hA h3 (t := A.φ (A.φ t1)) (g := g) m_ef_e m_ℓf_ℓ
    hfe.symm hfℓ.symm heℓ hgf hge hgℓ hse hsl
  rw [c1] at hl2 hs2
  -- `T₃`: frame `f`, walk along `e` (backwards)
  obtain ⟨d3, hT3, hd3, hf3, hl3, hs3⟩ := tri_step hA h3 (t := A.α (A.φ t1)) (g := g) m_ef_f
    m_ℓe_ℓ (by rw [A.curve_α]; exact hfe) (by rw [A.curve_α]; exact heℓ.symm) hfℓ
    (by rw [A.curve_α]; exact hge) hgf hgℓ hsf hsl
  have hy : ∀ {C : Fin n} {s : A.Cell → ZMod 2}, A.IsSide C s → e ≠ C →
      s (A.cellOf (A.α (A.φ t1))) = s (A.cellOf t1) := fun hs hC => by
    rw [side_α_of_ne hs hC, A.cellOf_φ]
  rw [hy hsl heℓ] at hl3
  rw [hy hsf hfe.symm] at hs3
  refine ⟨d2, d3, hT2, hd2, hl2, hT3, hd3, hl3, ?_, ?_, ?_⟩
  · intro h; rw [h] at hs2; exact zmod2_ne_self_add_one _ hs2
  · intro h; rw [h] at hs3; exact zmod2_ne_self_add_one _ hs3
  · intro h
    have hsub := curves_crossingOf_subset (A := A) d2
    have K := chi_walk hA h3 (t := t1) (d := d2) m_ℓf_f m_ℓe_e (ht1 ▸ hfℓ) (ht1 ▸ heℓ) hsf hse
      (by rw [ht1, ← hd2]; exact A.mem_curves_crossingOf d2)
      (fun hm => hf3 (h ▸ hsub hm)) (fun hm => he2 (hsub hm))
    rw [hs2, h, hs3] at K
    generalize sf (A.cellOf t1) = a at K
    generalize se (A.cellOf t1) = b at K
    revert a b; decide

/-- For `n ≥ 4` there is a triangle with a side on `ℓ` on each side of `ℓ`. -/
theorem exists_tri_side (h4 : 4 ≤ n) {ℓ : Fin n} {sl : A.Cell → ZMod 2} (hsl : A.IsSide ℓ sl)
    (v : ZMod 2) :
    ∃ t, A.IsTriangle (A.cellOf t) ∧ A.curve t = ℓ ∧ sl (A.cellOf t) = v := by
  obtain ⟨c, hc⟩ := exists_not_mem {ℓ} (by rw [card_singleton]; omega)
  obtain ⟨a, ha⟩ := exists_not_mem {ℓ, c} (by
    have := card_insert_le ℓ ({c} : Finset (Fin n)); rw [card_singleton] at this; omega)
  obtain ⟨b, hb⟩ := exists_not_mem {ℓ, c, a} (by
    have := card_insert_le ℓ ({c, a} : Finset (Fin n))
    have := card_insert_le c ({a} : Finset (Fin n))
    rw [card_singleton] at this; omega)
  simp only [mem_insert, mem_singleton, not_or] at hc ha hb
  obtain ⟨sc, hsc⟩ := Arrangement.exists_isSide (A := A) c
  obtain ⟨w, hw, hwσ⟩ := exists_dart_crossing' (A := A) (Ne.symm hb.2.2)
  have hcw : Arrangement.Crossing.curves A (A.crossingOf w) = {a, b} := by
    rw [A.curves_crossingOf, hw, hwσ]
  have nc : c ∉ Arrangement.Crossing.curves A (A.crossingOf w) := by
    rw [hcw, mem_insert, mem_singleton, not_or]; exact ⟨fun h => ha.2 h.symm, fun h => hb.2.1 h.symm⟩
  have nl : ℓ ∉ Arrangement.Crossing.curves A (A.crossingOf w) := by
    rw [hcw, mem_insert, mem_singleton, not_or]; exact ⟨fun h => ha.1 h.symm, fun h => hb.1 h.symm⟩
  have hcℓ : c ≠ ℓ := hc
  by_cases hv : sl (A.cellOf w) = v
  · obtain ⟨d, hT, hd, -, -, h2⟩ := quarter_tri hA hcℓ hsc hsl nc nl
    exact ⟨d, hT, hd, h2.trans hv⟩
  · have hant := curves_ant hA w
    obtain ⟨d, hT, hd, -, -, h2⟩ := quarter_tri hA hcℓ hsc hsl (x := ant A w)
      (by rw [hant]; exact nc) (by rw [hant]; exact nl)
    refine ⟨d, hT, hd, ?_⟩
    rw [h2, side_ant hA hsl w, if_neg (by rw [hw]; exact fun h => ha.1 h)]
    generalize sl (A.cellOf w) = x at hv
    revert x v; decide

/-- **Levi, one side** (`n ≥ 4`): on each side of `ℓ` there are at least three triangles with a
side on `ℓ`. -/
theorem three_le_side (h4 : 4 ≤ n) {ℓ : Fin n} {sl : A.Cell → ZMod 2} (hsl : A.IsSide ℓ sl)
    (v : ZMod 2) :
    3 ≤ ((A.triangles.filter (fun f => ∃ d ∈ f.darts, A.curve d = ℓ)).filter
      (fun f => sl f = v)).card := by
  obtain ⟨t1, hT, ht1, hv⟩ := exists_tri_side hA h4 hsl v
  obtain ⟨d2, d3, hT2, hd2, hl2, hT3, hd3, hl3, n21, n31, n23⟩ := three_tri hA h4 hsl hT ht1
  have mem : ∀ {d : D}, A.IsTriangle (A.cellOf d) → A.curve d = ℓ → sl (A.cellOf d) = v →
      A.cellOf d ∈ (A.triangles.filter (fun f => ∃ d ∈ f.darts, A.curve d = ℓ)).filter
        (fun f => sl f = v) := fun {d} hT hd hs => by
    simp only [mem_filter, Arrangement.triangles, mem_univ, true_and]
    exact ⟨⟨hT, d, Orbit.mem_darts.2 rfl, hd⟩, hs⟩
  calc 3 = ({A.cellOf t1, A.cellOf d2, A.cellOf d3} : Finset A.Cell).card :=
        (card_eq_three.2 ⟨_, _, _, n21.symm, n31.symm, n23, rfl⟩).symm
    _ ≤ _ := card_le_card (by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact mem hT ht1 hv
        · exact mem hT2 hd2 (hl2.trans hv)
        · exact mem hT3 hd3 (hl3.trans hv))

/-- **Levi's triangle theorem** (great version): for `n ≥ 3` every curve has at least `6` triangles
with a side on it (`3` antipodal pairs). -/
theorem six_le_tC (h3 : 3 ≤ n) (ℓ : Fin n) : 6 ≤ A.tC ℓ := by
  rcases Nat.lt_or_ge n 4 with h | h4
  · have hn : n = 3 := by omega
    rw [Arrangement.tC_eq_card_darts,
      filter_congr (q := fun d => A.curve d = ℓ) (fun d _ => by
        simp only [Arrangement.InTriangle, isTriangle_of_three hA hn d, and_true]),
      Arrangement.card_darts_on]
    omega
  · obtain ⟨sl, hsl⟩ := Arrangement.exists_isSide (A := A) ℓ
    have h0 := three_le_side hA h4 hsl 0
    have h1 := three_le_side hA h4 hsl 1
    have hsplit := card_filter_add_card_filter_not (s := A.triangles.filter
      (fun f => ∃ d ∈ f.darts, A.curve d = ℓ)) (fun f => sl f = 0)
    have hsub : ((A.triangles.filter (fun f => ∃ d ∈ f.darts, A.curve d = ℓ)).filter
        (fun f => sl f = 1)) ⊆ ((A.triangles.filter (fun f => ∃ d ∈ f.darts, A.curve d = ℓ)).filter
        (fun f => ¬ sl f = 0)) := by
      intro x hx
      simp only [mem_filter] at hx ⊢
      exact ⟨hx.1, by rw [hx.2]; decide⟩
    have := card_le_card hsub
    rw [Arrangement.tC]
    omega

/-- **Levi's triangle theorem**, count (great version): `p_3 ≥ 2n` for `n ≥ 3` (`n` antipodal
pairs; in the projective plane: at least `n` triangles). -/
theorem two_mul_le_p3 (h3 : 3 ≤ n) : 2 * n ≤ A.p 3 := by
  have h := sum_le_sum (s := (univ : Finset (Fin n))) (fun C _ => six_le_tC hA h3 C)
  rw [Arrangement.sum_tC, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
  omega

end Pca.Great
