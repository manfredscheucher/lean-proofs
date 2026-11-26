/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): processing the first curve

`C₀` is a curve with a side on the marked cell `z` (dart `y₀`); `T₀ = cellOf (α y₀)` is the cell
across that side. A **good triangle** is a triangle inside `C₀` with a side on `C₀`, other than
`T₀` and other than a chosen center `p`. Flipping it (`good_flip`) moves `C₀` over its apex: the
arrangement stays cylindrical (`p` is kept), the number of crossings of other curves inside `C₀`
drops (`mu`), and `z` keeps a side on `C₀`.

A good triangle exists while a crossing of two other curves lies inside `C₀` (`exists_good`):

* if `p` has no side on `C₀`: SH's lemma (`sweepFirstMove`) on the inner side of `C₀` with
  `f₀ = T₀` gives a digon or triangle `g ≠ T₀` with a side on `C₀`; a triangle is good (`p` has
  no side on `C₀`); a digon `g` of `C₀` and `a` is impossible: inside `a` it would be the whole
  region `int C₀ ∩ int a` (`digon_region`), hence `p`; outside `a` its side on `C₀` would be the
  only segment of `C₀` outside `a` (`digon_side_run`), hence the side of `z`, and `g = T₀` (FROS:
  a digon below the topmost pseudoparabola is impossible);
* if `p` has a side `u kp` on `C₀`: the zipping step for the lens `int C₀` (`FirstLens.lean`)
  gives a source triangle with base `u k`, `1 ≤ k ≤ kp`, followed by another dart of `L`; so
  `k < kp` and it is not `p`, and it is not `T₀` (base `u 0`).
-/
import Pca.FlipGraph.FirstLens
import Pca.SweepLemma

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace First

open Classical in
/-- The number of darts at crossings of other curves inside `C`. -/
noncomputable def mu (M : Marked n D) (C : Fin n) : ℕ :=
  (univ.filter (fun y : D => C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) ∧
    M.CrossInside C (M.A.crossingOf y))).card

/-- A triangle has one dart on each of its curves. -/
theorem tri_dart_eq {A : Arrangement n D} {d e : D} (hT : A.IsTriangle (A.cellOf d))
    (he : A.cellOf e = A.cellOf d) (hc : A.curve e = A.curve d) : e = d := by
  rcases (Arrangement.tri_mem_iff hT).1 he with h | h | h
  · exact h
  · exact absurd (h ▸ hc) (A.curve_φ_ne d)
  · exfalso
    have h3 : A.φ (A.φ (A.φ d)) = d := A.φ_φ_φ_of_triangle hT
    have := A.curve_φ_ne (A.φ (A.φ d))
    rw [h3, ← h, hc] at this
    exact this rfl

variable (M : Marked n D) {y₀ : D} (hy₀ : M.A.cellOf y₀ = M.z)

include hy₀ in
/-- **A good flip.** -/
theorem good_flip {p : M.A.Cell} (hp : ∀ C, M.Inside C p) {d : D}
    (hT : M.A.IsTriangle (M.A.cellOf d)) (hd : M.A.curve d = M.A.curve y₀)
    (hin : M.Inside (M.A.curve y₀) (M.A.cellOf d)) (hne : M.A.cellOf d ≠ M.A.cellOf (M.A.α y₀))
    (hnp : M.A.cellOf d ≠ p) :
    CylStep M (M.flip d hT) ∧ mu (M.flip d hT) (M.A.curve y₀) < mu M (M.A.curve y₀) ∧
      ∃ y, (M.flip d hT).A.curve y = M.A.curve y₀ ∧ (M.flip d hT).A.cellOf y = (M.flip d hT).z := by
  classical
  set C₀ := M.A.curve y₀ with hC₀
  have hzT : M.A.cellOf d ≠ M.z := fun h => M.not_inside_z C₀ (h ▸ hin)
  refine ⟨⟨⟨d, hT, hzT, rfl⟩, ⟨p, hp⟩, ⟨Arrangement.flipCellEquiv hT p, fun C =>
    (flip_inside M hT hzT C p).2 (iff_of_true (hp C) (fun h => hnp h.1.symm))⟩⟩, ?_, ?_⟩
  · -- the apex leaves the interior, nothing else changes
    have hasS : M.HasSideOn C₀ (M.A.cellOf d) := ⟨d, M.A.mem_darts_cellOf_self d, hd⟩
    have hapex : C₀ ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.φ (M.A.φ d))) := by
      rw [← hd]; exact Arrangement.tri_curve_not_mem hT
    have hapexIn : M.CrossInside C₀ (M.A.crossingOf (M.A.φ (M.A.φ d))) := by
      rw [M.crossInside_iff hapex, M.A.cellOf_φ, M.A.cellOf_φ]; exact hin
    have hcorner : ∀ y, M.A.IsCorner d y → C₀ ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) →
        M.A.crossingOf y = M.A.crossingOf (M.A.φ (M.A.φ d)) := by
      intro y hy hny
      have hy' : M.A.crossingOf y ∈ Arrangement.Cell.corners M.A (M.A.cellOf d) := hy
      rw [Arrangement.corners_tri hT, mem_insert, mem_insert, mem_singleton] at hy'
      rcases hy' with e | e | e
      · exact absurd (by rw [e, ← hd]; exact M.A.mem_curves_crossingOf d) hny
      · exact absurd (by rw [e, M.A.crossingOf_φ, ← hd]; exact M.A.mem_curves_end d) hny
      · exact e
    have apexCorner : M.A.IsCorner d (M.A.φ (M.A.φ d)) := by
      show M.A.crossingOf _ ∈ Arrangement.Cell.corners M.A (M.A.cellOf d)
      rw [Arrangement.corners_tri hT]
      exact mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
    apply card_lt_card
    refine ⟨fun y hy => ?_, fun hsub => ?_⟩
    · rw [mem_filter] at hy ⊢
      obtain ⟨-, hny, hiy⟩ := hy
      change C₀ ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) at hny
      change (M.flip d hT).CrossInside C₀ (M.A.crossingOf y) at hiy
      rw [crossInside_flip M hT hzT y hny] at hiy
      refine ⟨mem_univ _, hny, ?_⟩
      by_cases hc : M.A.IsCorner d y
      · exfalso
        have e := hcorner y hc hny
        rw [e] at hiy
        simp only [hc, hasS, and_self, not_true_eq_false, iff_false] at hiy
        exact hiy hapexIn
      · simpa [hc] using hiy
    · have hm := hsub (mem_filter.2 ⟨mem_univ (M.A.φ (M.A.φ d)), hapex, hapexIn⟩)
      rw [mem_filter] at hm
      obtain ⟨-, hny, hiy⟩ := hm
      change (M.flip d hT).CrossInside C₀ (M.A.crossingOf _) at hiy
      rw [crossInside_flip M hT hzT _ hapex] at hiy
      simp only [apexCorner, hasS, and_self, not_true_eq_false, iff_false] at hiy
      exact hiy hapexIn
  · -- the marked cell keeps a side on `C₀`
    suffices h : ∃ y, M.A.curve y = C₀ ∧ M.A.cellOf (Arrangement.flipG' M.A d y) = M.z by
      obtain ⟨y, hy, hyz⟩ := h
      refine ⟨y, hy, ?_⟩
      change (M.A.flip d hT).cellOf y = Arrangement.flipCellEquiv hT M.z
      rw [Arrangement.flip_cellOf, hyz]
    by_cases hσ : M.A.cellOf (M.A.σ (M.A.σ y₀)) = M.A.cellOf d
    · refine ⟨M.A.α (M.A.σ (M.A.σ y₀)), by rw [M.A.curve_α, M.A.isArrangement.curve_σσ], ?_⟩
      have h1 : ¬ M.A.cellOf (M.A.σ (M.A.σ (M.A.α (M.A.σ (M.A.σ y₀))))) = M.A.cellOf d := by
        rw [← M.A.straight_apply]; exact Arrangement.ne_straight hT hσ
      unfold Arrangement.flipG'
      rw [if_neg h1, if_pos (Or.inr (by rw [M.A.α_α]; exact hσ)), M.A.α_α, M.A.σ_σ_σ_σ, hy₀]
    · refine ⟨y₀, rfl, ?_⟩
      have h3 : ¬ M.A.cellOf (M.A.α (M.A.σ (M.A.σ y₀))) = M.A.cellOf d := by
        intro h
        have e := M.inside_straight C₀ (M.A.straight.symm y₀)
        rw [Equiv.apply_symm_apply, hy₀, Arrangement.straight_symm_apply, h] at e
        have hcs : M.A.curve (M.A.σ (M.A.α (M.A.α (M.A.σ (M.A.σ y₀))))) ≠ C₀ := by
          rw [M.A.α_α]
          rw [M.A.isArrangement.curve_σσ (M.A.σ y₀)]
          exact M.A.isArrangement.curve_σ y₀
        have := M.not_inside_z C₀
        tauto
      unfold Arrangement.flipG'
      rw [if_neg hσ, if_neg (by rw [hy₀]; exact not_or.2 ⟨fun h => hzT h.symm, fun h => hne h.symm⟩),
        if_neg h3, hy₀]

theorem zmod2_eq {a b c : ZMod 2} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  revert a b c; decide

include hy₀ in
/-- **A good triangle exists** while a crossing of two other curves lies inside `C₀`. -/
theorem exists_good (hc : M.Cylindrical) (hμ : 0 < mu M (M.A.curve y₀)) :
    ∃ p : M.A.Cell, (∀ C, M.Inside C p) ∧ ∃ d, ∃ hT : M.A.IsTriangle (M.A.cellOf d),
      M.A.curve d = M.A.curve y₀ ∧ M.Inside (M.A.curve y₀) (M.A.cellOf d) ∧
      M.A.cellOf d ≠ M.A.cellOf (M.A.α y₀) ∧ M.A.cellOf d ≠ p := by
  classical
  set C₀ := M.A.curve y₀ with hC₀
  obtain ⟨p, hp⟩ := hc
  refine ⟨p, hp, ?_⟩
  have hu0 : u M y₀ 0 = M.A.α y₀ := by simp [u]
  by_cases hside : ∃ e, M.A.cellOf e = p ∧ M.A.curve e = C₀
  · -- the center has a side on `C₀`: zipping step in the lens `int C₀`
    obtain ⟨e, hep, hec⟩ := hside
    obtain ⟨j, hj, rfl⟩ := dart_u M hy₀ hec (by rw [hep]; exact hp _)
    have hj1 : 1 ≤ j := by
      by_contra h0
      have h0 : j = 0 := by omega
      subst h0
      have hn := M.A.two_le_n
      obtain ⟨a, ha⟩ : ∃ a : Fin n, a ≠ C₀ := by
        by_cases h : (C₀ : ℕ) = 0
        · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
        · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h; simp at h⟩
      exact out_u0 M hy₀ ha (by rw [hep]; exact hp a)
    set Λ := firstLens M hy₀ hj1 hj
    have hs := firstLens_sep M hy₀ hj1 hj
    have ht := firstLens_transversal M hy₀ hj1 hj (fun a _ => by rw [hep]; exact hp a)
    have hv : ∃ x, Λ.IsVertex x := by
      obtain ⟨y, hy⟩ := card_pos.1 hμ
      rw [mem_filter] at hy
      obtain ⟨-, hny, hiy⟩ := hy
      refine ⟨M.A.crossingOf y, fun w hw => ⟨hiy w hw, ?_⟩⟩
      change M.Inside C₀ (M.A.cellOf (M.A.α w))
      have hwc : M.A.curve w ≠ C₀ := fun h => hny (by
        rw [← h, ← Orbit.mem_darts.1 hw]; exact M.A.mem_curves_crossingOf w)
      rw [M.inside_α]
      exact ⟨fun _ => hwc, fun _ => hiy w hw⟩
    obtain ⟨d, ⟨⟨k, hk1, hkj, rfl⟩, hT, -⟩, ⟨k', hk1', hkj', hk'⟩⟩ := Lens.zipStep' Λ hs ht hv
    refine ⟨u M y₀ k, hT, curve_u M k, in_u M hy₀ k, fun h => ?_, fun h => ?_⟩
    · rw [← hu0] at h
      have := u_inj M (by omega) (by omega)
        (tri_dart_eq hT h.symm (by rw [curve_u, curve_u]))
      omega
    · rw [← hep] at h
      have e := u_inj M hj (by omega) (tri_dart_eq hT h.symm (by rw [curve_u, curve_u]))
      subst e
      rw [← u_succ] at hk'
      rcases Nat.lt_or_ge (j + 1) (period M.A.straight (M.A.α y₀)) with h1 | h1
      · have := u_inj M h1 (by omega) hk'; omega
      · rw [show j + 1 = period M.A.straight (M.A.α y₀) by omega, u_period] at hk'
        have := u_inj M (by omega) (by omega) hk'; omega
  · -- the center has no side on `C₀`: SH's lemma with `f₀ = T₀`
    obtain ⟨s, hs⟩ := M.A.exists_isSide C₀
    have hT₀ : M.Inside C₀ (M.A.cellOf (M.A.α y₀)) := by rw [← hu0]; exact in_u M hy₀ 0
    obtain ⟨g, hg0, hsg, ⟨d, hdg, hdc⟩, hdt⟩ :=
      M.A.sweepFirstMove C₀ s hs (M.A.cellOf (M.A.α y₀))
    have hgd : M.A.cellOf d = g := Orbit.mem_darts.1 hdg
    subst hgd
    have hin : M.Inside C₀ (M.A.cellOf d) := by
      rw [M.inside_iff hs, hsg]; exact (M.inside_iff hs _).1 hT₀
    rcases hdt with hD | hT
    · exfalso
      set a := M.A.curve (M.A.φ d) with ha
      obtain ⟨s', hs'⟩ := M.A.exists_isSide a
      have hsd : M.A.IsSide (M.A.curve d) s := by rw [hdc]; exact hs
      by_cases hia : M.Inside a (M.A.cellOf d)
      · have e := digon_region hD hsd hs'
          (zmod2_eq ((M.inside_iff hs _).1 (hp C₀)) ((M.inside_iff hs _).1 hin))
          (zmod2_eq ((M.inside_iff hs' _).1 (hp a)) ((M.inside_iff hs' _).1 hia))
        exact hside ⟨d, e.symm, hdc⟩
      · have hys : s' (M.A.cellOf y₀) = s' (M.A.cellOf d) := by
          rw [hy₀]
          by_contra hne
          exact hia ((M.inside_iff hs' _).2 (Ne.symm hne))
        rcases eq_or_eq_α_of_segmentOf (digon_side_run hD hs' (hdc.symm.trans rfl) hys)
          with e | e
        · subst e; rw [hy₀] at hin; exact M.not_inside_z C₀ hin
        · exact hg0 (by rw [e, M.A.α_α])
    · exact ⟨d, hT, hdc, hin, hg0, fun h => hside ⟨d, h, hdc⟩⟩

end First

end Pca.FlipGraph
