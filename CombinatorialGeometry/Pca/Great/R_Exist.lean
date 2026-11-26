/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: a negative triangle exists while the potential is positive (`doc/pca/great.md` 3.4)

Take a negative triple `(a, b, c)` with `p a` minimal. Every chord `t` with `p t < p a` has all
crossings of chords after it on side `1` (its triples are positive), so the quarter lemma applies
to the chords from `a` on (`T`) and the side `0` of `a`: it gives a triangle in `H` with a side on
`a` whose triple is negative.
-/
import Pca.Great.R_PotFlip

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

namespace Frame

variable (F : Frame A) (hA : A.IsGreat)
include hA

theorem neg_comm {a b c : Fin n} : F.Neg a b c ↔ F.Neg a c b := by
  unfold Neg; rw [pair_comm]

/-- **A negative triangle exists** while the potential is positive. -/
theorem exists_bad_tri (hpot : 0 < F.pot) :
    ∃ d : D, A.IsTriangle (A.cellOf d) ∧ F.c0 ∉ Arrangement.Cell.curves A (A.cellOf d) ∧
      F.s0 (A.cellOf d) = 1 ∧ ∃ t, F.Bad t ∧
        ({t.1, t.2.1, t.2.2} : Finset (Fin n)) = Arrangement.Cell.curves A (A.cellOf d) := by
  classical
  have hn := A.two_le_n
  obtain ⟨t0, ht0⟩ := card_pos.1 hpot
  obtain ⟨⟨a, b, c⟩, hmem, hmin⟩ := (univ.filter F.Bad).exists_min_image (fun t => F.p t.1) ⟨t0, ht0⟩
  obtain ⟨ha, hb, hc, hab, hbc, hneg⟩ := (mem_filter.1 hmem).2
  simp only at ha hb hc hab hbc hneg
  have hab' : a ≠ b := fun h => by rw [h] at hab; omega
  have hac' : a ≠ c := fun h => by rw [h] at hab; omega
  have hbc' : b ≠ c := fun h => by rw [h] at hbc; omega
  set T : Finset (Fin n) := insert F.c0 (univ.filter fun x => x ≠ F.c0 ∧ F.p a ≤ F.p x)
  have memT : ∀ x, x ≠ F.c0 → (x ∈ T ↔ F.p a ≤ F.p x) := fun x hx => by
    simp only [T, mem_insert, hx, false_or, mem_filter, mem_univ, true_and, ne_eq,
      not_false_eq_true]
  have haT : a ∈ T := (memT a ha).2 le_rfl
  -- the given crossing
  have hv : ∃ d : D, F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d) ∧
      a ∉ Arrangement.Crossing.curves A (A.crossingOf d) ∧
      Arrangement.Crossing.curves A (A.crossingOf d) ⊆ T ∧
      F.s0 (A.cellOf d) = 1 ∧ F.sR a (A.cellOf d) = 0 := by
    refine ⟨(A.straight ^ F.hpos b c) (F.β b), ?_, ?_, ?_, F.s0_cell hA hb
      (F.hpos_spec hA hb hc hbc').2.1, ?_⟩
    · rw [F.curves_hcross hA hb hc hbc', mem_insert, mem_singleton, not_or]
      exact ⟨Ne.symm hb, Ne.symm hc⟩
    · rw [F.curves_hcross hA hb hc hbc', mem_insert, mem_singleton, not_or]; exact ⟨hab', hac'⟩
    · rw [F.curves_hcross hA hb hc hbc']
      intro x hx; simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (memT _ hb).2 hab.le
      · exact (memT _ hc).2 (hab.trans hbc).le
    · rw [← crossSide_eq (F.isSide_sR a) (by
        rw [F.curves_hcross hA hb hc hbc', mem_insert, mem_singleton, not_or]; exact ⟨hab', hac'⟩)]
      exact (F.neg_iff hA ha hb hc hab' hac' hbc').1 hneg
  -- curves before `a` have all crossings of chords from `a` on side `1`
  have hout : ∀ t, t ∉ T → ∀ d d' : D,
      F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d) →
      Arrangement.Crossing.curves A (A.crossingOf d) ⊆ T → F.s0 (A.cellOf d) = 1 →
      F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d') →
      Arrangement.Crossing.curves A (A.crossingOf d') ⊆ T → F.s0 (A.cellOf d') = 1 →
      F.sR t (A.cellOf d) = F.sR t (A.cellOf d') := by
    intro t htT
    have ht0 : t ≠ F.c0 := fun h => htT (h ▸ mem_insert_self _ _)
    have hta : F.p t < F.p a := by
      by_contra h; exact htT ((memT t ht0).2 (by omega))
    have one : ∀ d : D, F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d) →
        Arrangement.Crossing.curves A (A.crossingOf d) ⊆ T → F.s0 (A.cellOf d) = 1 →
        F.sR t (A.cellOf d) = 1 := by
      intro d h0 hsub hs
      set x := A.curve d
      set y := A.curve (A.σ d)
      have hxy : x ≠ y := (A.isArrangement.curve_σ d).symm
      have hx0 : x ≠ F.c0 := fun h => h0 (h ▸ A.mem_curves_crossingOf d)
      have hy0 : y ≠ F.c0 := fun h => h0 (h ▸ A.mem_curves_crossingOf_σ d)
      have hpx := (memT x hx0).1 (hsub (A.mem_curves_crossingOf d))
      have hpy := (memT y hy0).1 (hsub (A.mem_curves_crossingOf_σ d))
      have htx : t ≠ x := fun h => by rw [h] at hta; omega
      have hty : t ≠ y := fun h => by rw [h] at hta; omega
      have hnot : ¬ F.Neg t x y := by
        intro hN
        have hpxy : F.p x ≠ F.p y := fun h => hxy (F.p_inj hA hx0 hy0 h)
        rcases Nat.lt_or_gt_of_ne hpxy with hlt | hlt
        · have := hmin (t, x, y) (mem_filter.2 ⟨mem_univ _, ht0, hx0, hy0, by simp; omega, hlt, hN⟩)
          simp only at this; omega
        · have := hmin (t, y, x) (mem_filter.2 ⟨mem_univ _, ht0, hy0, hx0, by simp; omega, hlt,
            (F.neg_comm hA).1 hN⟩)
          simp only at this; omega
      have hxc : Arrangement.Crossing.curves A (A.crossingOf d) = {x, y} := A.curves_crossingOf d
      have ht' : t ∉ Arrangement.Crossing.curves A (A.crossingOf d) := by
        rw [hxc, mem_insert, mem_singleton, not_or]; exact ⟨htx, hty⟩
      have h1 : A.crossSide F.s0 (A.crossingOf d) = 1 := by
        rw [crossSide_eq F.isSide_s0 h0]; exact hs
      have h2 := mt (F.neg_iff' hA (a := t) hx0 hy0 hxy hxc h1).2 hnot
      rw [crossSide_eq (F.isSide_sR t) ht'] at h2
      have := (by decide : ∀ u : ZMod 2, u ≠ 0 → u = 1) _ h2
      exact this
    intro d d' h0 hsub hs h0' hsub' hs'
    rw [one d h0 hsub hs, one d' h0' hsub' hs']
  obtain ⟨d, hT, hda, hd0, hdT, hds, hdN⟩ := F.quarter hA ha 0 T haT hv hout
  refine ⟨d, hT, hd0, hds, ?_⟩
  -- the triple of the triangle
  have hcur := tri_curves hT
  set w := A.curve (A.φ d)
  set w' := A.curve (A.φ (A.φ d))
  obtain ⟨n1, n2, n3⟩ := tri_curve_ne hT
  rw [hda] at n1 n3
  have hw0 : w ≠ F.c0 := fun h => hd0 (by rw [hcur, ← h]; simp)
  have hw'0 : w' ≠ F.c0 := fun h => hd0 (by rw [hcur, ← h]; simp)
  have hpw : F.p a < F.p w := by
    have h1 := (memT w hw0).1 (hdT (by rw [hcur]; simp))
    have : F.p a ≠ F.p w := fun h => n1 (F.p_inj hA ha hw0 h)
    omega
  have hpw' : F.p a < F.p w' := by
    have h1 := (memT w' hw'0).1 (hdT (by rw [hcur]; simp))
    have : F.p a ≠ F.p w' := fun h => n3 (F.p_inj hA ha hw'0 h)
    omega
  -- the corner on `w, w'` is in `H` on side `0` of `a`
  set z := A.φ (A.φ d)
  have hzc : Arrangement.Crossing.curves A (A.crossingOf z) = {w', w} := by
    rw [A.curves_crossingOf]
    show {A.curve z, A.curve (A.σ (A.φ (A.φ d)))} = _
    rw [A.curve_σ_φ]
  have hcz : A.cellOf z = A.cellOf d := by
    show A.cellOf (A.φ (A.φ d)) = _; rw [A.cellOf_φ, A.cellOf_φ]
  have hz0 : F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf z) := by
    rw [hzc, mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hw'0, Ne.symm hw0⟩
  have hza : a ∉ Arrangement.Crossing.curves A (A.crossingOf z) := by
    rw [hzc, mem_insert, mem_singleton, not_or]; exact ⟨n3, n1⟩
  have hzs : A.crossSide F.s0 (A.crossingOf z) = 1 := by
    rw [crossSide_eq F.isSide_s0 hz0, hcz]; exact hds
  have hneg : F.Neg a w' w := by
    rw [F.neg_iff' hA hw'0 hw0 (Ne.symm n2) hzc hzs,
      crossSide_eq (F.isSide_sR a) hza, hcz, hdN]
  have hww : F.p w ≠ F.p w' := fun h => n2 (F.p_inj hA hw0 hw'0 h)
  rcases Nat.lt_or_gt_of_ne hww with hlt | hlt
  · refine ⟨(a, w, w'), ⟨ha, hw0, hw'0, hpw, hlt, (F.neg_comm hA).1 hneg⟩, ?_⟩
    rw [hcur, hda]
  · refine ⟨(a, w', w), ⟨ha, hw'0, hw0, hpw', hlt, hneg⟩, ?_⟩
    rw [hcur, hda]; simp only; rw [pair_comm]

end Frame

end Pca.Great
