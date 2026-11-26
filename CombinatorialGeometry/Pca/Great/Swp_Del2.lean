/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# A flip of a triangle with a side on the new curve keeps the deletion
-/
import Pca.Great.Swp_Del
import Pca.Great.R_Flip

open Equiv Finset

namespace Pca.Great

variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] {n : ℕ}
  {A : Arrangement n D}

/-- A triangle on the new curve has at most one corner off the new curve. -/
theorem two_corners {B : Arrangement (n + 1) D'} {d : D'} (hT : B.IsTriangle (B.cellOf d))
    (hL : Fin.last n ∈ Arrangement.Cell.curves B (B.cellOf d)) {x y : B.Crossing}
    (hx : x ∈ Arrangement.Cell.corners B (B.cellOf d))
    (hy : y ∈ Arrangement.Cell.corners B (B.cellOf d)) (hxy : x ≠ y) :
    Fin.last n ∈ Arrangement.Crossing.curves B x ∨ Fin.last n ∈ Arrangement.Crossing.curves B y := by
  by_contra hc
  push Not at hc
  have hcard : (Arrangement.Cell.curves B (B.cellOf d)).card ≤ 3 := by
    rw [tri_curves hT]; exact card_le_three
  have key : ∀ z : B.Crossing, z ∈ Arrangement.Cell.corners B (B.cellOf d) →
      Fin.last n ∉ Arrangement.Crossing.curves B z →
      Arrangement.Crossing.curves B z = (Arrangement.Cell.curves B (B.cellOf d)).erase (Fin.last n) := by
    intro z hz hzL
    refine eq_of_subset_of_card_le (fun C hC => mem_erase.2 ⟨fun h => hzL (h ▸ hC),
      curves_corner_sub hT hz hC⟩) ?_
    rw [card_erase_of_mem hL, B.card_curves]; omega
  exact hxy (tri_corner_inj hT hx hy ((key x hx hc.1).trans (key y hy hc.2).symm))

theorem tri_cross_ne {B : Arrangement (n + 1) D'} {b : D'} (hT : B.IsTriangle (B.cellOf b)) :
    B.crossingOf (B.α b) ≠ B.crossingOf b := by
  intro h
  have h1 := tri_corner_curves hT
  have h2 := tri_corner_curves (Arrangement.tri_φ hT)
  rw [Arrangement.tri_φφφ hT] at h2
  have e : B.crossingOf (B.φ b) = B.crossingOf (B.α b) := by
    rw [B.φ_apply]; exact (B.crossingOf_eq_iff.2 (by simp)).symm
  rw [e, h, h1] at h2
  obtain ⟨n1, n2, n3⟩ := tri_curve_ne hT
  have : B.curve (B.φ (B.φ b)) ∈ ({B.curve (B.φ b), B.curve b} : Finset (Fin (n + 1))) := by
    rw [← h2]; simp
  simp only [mem_insert, mem_singleton] at this
  rcases this with h' | h'
  · exact n2 h'.symm
  · exact n3 h'.symm

end Pca.Great

namespace Pca.Great

variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] {n : ℕ}
  {A : Arrangement n D} {B : Arrangement (n + 1) D'} {ι : D → D'}

theorem hit_prepend {X : Type*} {s : Perm X} {P : X → Prop} {v w : X} {j : ℕ}
    (h : Hit s P (s v) w j) (hv : ¬ P v) : Hit s P v w (j + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [pow_succ, Perm.mul_apply, h1], h2, fun i hi => ?_⟩
  rcases i with _ | i
  · exact hv
  · rw [pow_succ, Perm.mul_apply]; exact h3 i (by omega)

theorem hit_drop {X : Type*} {s : Perm X} {P : X → Prop} {v w : X} {j : ℕ}
    (h : Hit s P v w j) (hv : ¬ P v) : Hit s P (s v) w (j - 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hj : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, Perm.one_apply] at h1
    exact hv (h1 ▸ h2)
  refine ⟨by rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega), h1], h2,
    fun i hi => ?_⟩
  rw [← Perm.mul_apply, ← pow_succ]; exact h3 _ (by omega)

/-- **A flip of a triangle on the new curve keeps the deletion.** -/
theorem flip_isDeletion (hD : IsDeletion B A ι) {d : D'} (hT : B.IsTriangle (B.cellOf d))
    (hL : Fin.last n ∈ Arrangement.Cell.curves B (B.cellOf d)) :
    IsDeletion (B.flip d hT) A ι where
  inj := hD.inj
  range := hD.range
  curve := hD.curve
  σ := hD.σ
  α e := by
    set S := B.sideDarts d
    set s := B.straight
    set O : D' → Prop := fun y => ∃ e, ι e = y
    have hS : ∀ y ∈ S, s y ∉ S := Arrangement.straight_not_mem_sideDarts hT
    have hO : ∀ y ∈ S, ¬ (O y ∧ O (s y)) := by
      intro y hy ⟨h1, h2⟩
      have h1 : Fin.last n ∉ Arrangement.Crossing.curves B (B.crossingOf y) := (hD.range y).1 h1
      have h2 : Fin.last n ∉ Arrangement.Crossing.curves B (B.crossingOf (s y)) :=
        (hD.range _).1 h2
      rw [B.crossingOf_straight] at h2
      obtain ⟨b, hb, hyb⟩ : ∃ b, B.cellOf b = B.cellOf d ∧ (b = y ∨ B.α b = y) := by
        rcases (Arrangement.mem_sideDarts).1 hy with h | h
        · exact ⟨y, h, Or.inl rfl⟩
        · exact ⟨B.α y, h, Or.inr (B.isArrangement.α_α y)⟩
      have hc1 := Arrangement.isCorner_of_mem (A := B) hb
      have hc2 := Arrangement.isCorner_α_of_mem (A := B) hb
      have hne := tri_cross_ne (Arrangement.isTriangle_of hT hb)
      rcases two_corners hT hL hc2 hc1 hne with h | h <;> rcases hyb with rfl | rfl <;>
        (try rw [B.isArrangement.α_α] at h2) <;> first | exact h1 h | exact h2 h
    have hst : (B.flip d hT).straight = Arrangement.flipρ hT * s * Arrangement.flipρ hT := by
      ext y; exact Arrangement.flip_straightPerm hT y
    have hρ : ∀ x, Arrangement.flipρ hT x = swapAlong s S x := fun x => rfl
    have hρρ : ∀ x, Arrangement.flipρ hT (Arrangement.flipρ hT x) = x :=
      Arrangement.flipρ_flipρ hT
    obtain ⟨j, hj⟩ := hit_of_segCond hD.range hD.σ (hD.α e)
    set z := ι e
    set w := ι (A.straight e)
    have hOz : O z := ⟨e, rfl⟩
    have goal : ∃ j'', Hit (B.flip d hT).straight O ((B.flip d hT).straight z) w j'' := by
      rw [hst]
      have fin : ∀ u, (∃ j', Hit s (fun x => O (swapAlong s S x)) u (swapAlong s S w) j') →
          ∃ j'', Hit (Arrangement.flipρ hT * s * Arrangement.flipρ hT) O
            (Arrangement.flipρ hT u) w j'' := by
        rintro u ⟨j', h'⟩
        have := hit_conj (ρ := Arrangement.flipρ hT) hρρ (O := O)
          (by simpa only [← hρ] using h')
        rw [hρ w, ← hρ, hρρ] at this
        exact ⟨j', this⟩
      by_cases hz1 : z ∈ S
      · -- `ρ z = s z`
        have hρz : Arrangement.flipρ hT z = s z := by rw [hρ]; exact swapAlong_of_mem hS hz1
        have hsz : ¬ O (s z) := fun h => hO z hz1 ⟨hOz, h⟩
        have h2 := hit_drop hj hsz
        obtain ⟨j'', h''⟩ := fin _ (hit_swap hS hO (by rw [Equiv.symm_apply_apply]; exact hS z hz1) h2)
        refine ⟨j'', ?_⟩
        simp only [Perm.mul_apply, hρz]; exact h''
      by_cases hz2 : s.symm z ∈ S
      · -- `z = s y₀`
        have hρz : Arrangement.flipρ hT z = s.symm z := by
          rw [hρ]; unfold swapAlong; rw [if_neg hz1, if_pos hz2]
        have hv : s.symm (s z) ∉ S := by rw [Equiv.symm_apply_apply]; exact hz1
        obtain ⟨j', h'⟩ := hit_swap hS hO hv hj
        have hnot : ¬ O (swapAlong s S z) := by
          rw [← hρ, hρz]
          intro h
          apply hO _ hz2
          rw [Equiv.apply_symm_apply]; exact ⟨h, hOz⟩
        obtain ⟨j'', h''⟩ := fin z ⟨j' + 1, hit_prepend h' hnot⟩
        refine ⟨j'', ?_⟩
        simp only [Perm.mul_apply, hρz, Equiv.apply_symm_apply]
        rw [← hρz]; exact h''
      · -- `z` is not moved
        have hρz : Arrangement.flipρ hT z = z := by
          rw [hρ]; unfold swapAlong; rw [if_neg hz1, if_neg hz2]
        have hv : s.symm (s z) ∉ S := by rw [Equiv.symm_apply_apply]; exact hz1
        obtain ⟨j'', h''⟩ := fin _ (hit_swap hS hO hv hj)
        refine ⟨j'', ?_⟩
        simp only [Perm.mul_apply, hρz]; exact h''
    obtain ⟨j'', h''⟩ := goal
    exact segCond_of_hit (B := B.flip d hT) hD.range hD.σ h''

end Pca.Great
