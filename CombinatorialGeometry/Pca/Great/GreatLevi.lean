/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Levi's extension lemma for great-pseudocircle arrangements (P4, `doc/pca/great.md` section 4)

Double the curve `c` of a side of `f₁` (`Dbl.walk`, inserted by `InsWalk.ins`): the result is
great, its deletion is `A`, and the new curve passes `f₁` (and every cell when `n = 2`). For
`n ≥ 3` sweep the new curve (`sweep`) until it passes `f₂`.
-/
import Pca.Great.Swp_Ind
import Pca.Great.Dbl_Twice

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- A cell has a corner off any given curve (`n ≥ 3`). -/
theorem exists_corner_off (hA : A.IsGreat) (h3 : 3 ≤ n) (f : A.Cell) (C : Fin n) :
    ∃ d ∈ f.darts, C ∉ Arrangement.Crossing.curves A (A.crossingOf d) := by
  obtain ⟨d₁, rfl⟩ := f.exists_mk
  have hmem : ∀ k : ℕ, (A.φ ^ k) d₁ ∈ (Orbit.mk A.φ d₁).darts := fun k =>
    Orbit.mem_darts.2 (Orbit.mk_eq_mk.2 (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)).symm)
  obtain ⟨d, hd, hdC⟩ : ∃ d ∈ (Orbit.mk A.φ d₁).darts, A.curve d ≠ C := by
    by_cases h : A.curve d₁ = C
    · refine ⟨A.φ d₁, by simpa using hmem 1, ?_⟩
      rw [← h]; exact A.curve_φ_ne d₁
    · exact ⟨d₁, by simpa using hmem 0, h⟩
  have hφ : A.φ d ∈ (Orbit.mk A.φ d₁).darts := by
    rw [Orbit.mem_darts] at hd ⊢; rw [← hd]; exact A.cellOf_φ d
  obtain ⟨k₁, hk₁, hpos⟩ := pos_two hA d (Ne.symm hdC)
  by_cases h0 : C ∈ Arrangement.Crossing.curves A (A.crossingOf d)
  · refine ⟨A.φ d, hφ, fun h1 => ?_⟩
    rw [A.crossingOf_φ, ← A.crossingOf_straight] at h1
    have e0 := (hpos 0 (by omega)).1 (by simpa using h0)
    have e1 := (hpos 1 (by omega)).1 (by simpa using h1)
    omega
  · exact ⟨d, hd, h0⟩

variable (hA : A.IsGreat)
include hA

/-- **Levi's extension lemma, great version** (core form). -/
theorem levi_core (f₁ f₂ : A.Cell) :
    ∃ (B : Arrangement (n + 1) (D ⊕ (Fin (2 * n) × Fin 4))), B.IsGreat ∧
      IsDeletion B A Sum.inl ∧ Passes B Sum.inl f₁ ∧ Passes B Sum.inl f₂ := by
  have hn := A.two_le_n
  obtain ⟨y0, rfl⟩ := f₁.exists_mk
  have hy0 : y0 ∈ (Orbit.mk A.φ y0).darts := Orbit.mem_darts.2 rfl
  set W := Dbl.walk hA y0 hn
  have hG := W.ins_isGreat hA (Dbl.walk_sym hA y0 hn)
  have hD := W.ins_isDeletion
  have hP : PassAt W.ins Sum.inl y0 := by
    show Fin.last n ∈ Arrangement.Crossing.curves W.ins (W.ins.crossingOf (W.αfun (.inl y0)))
    have : y0 = W.t ⟨0, by omega⟩ := (Dbl.walk_t0 hA y0 hn).symm
    rw [this, W.αfun_t]; exact W.last_mem_inr _ 0
  by_cases h3 : 3 ≤ n
  · obtain ⟨d₀, hd₀, hx0⟩ := exists_corner_off hA h3 f₂ (A.curve y0)
    let F₀ : Frame W.ins := ⟨Fin.castSucc (A.curve y0), .inl y0, rfl⟩
    set b := Fin.castSucc (A.curve d₀)
    set c := Fin.castSucc (A.curve (A.σ d₀))
    have hbc : b ≠ c := fun h => A.isArrangement.curve_σ d₀ (Fin.castSucc_injective _ h).symm
    have hb0 : b ≠ F₀.c0 := fun h =>
      hx0 (by rw [← Fin.castSucc_injective _ h]; exact A.mem_curves_crossingOf d₀)
    have hc0 : c ≠ F₀.c0 := fun h =>
      hx0 (by rw [← Fin.castSucc_injective _ h]; exact A.mem_curves_crossingOf_σ d₀)
    set z := (W.ins.straight ^ F₀.hpos b c) (F₀.β b)
    have hz := F₀.curves_hcross hG hb0 hc0 hbc
    have hz0 : F₀.c0 ∉ Arrangement.Crossing.curves W.ins (W.ins.crossingOf z) := by
      rw [hz]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hb0, Ne.symm hc0⟩
    have hcs : W.ins.crossSide F₀.s0 (W.ins.crossingOf z) = 1 := by
      rw [crossSide_eq F₀.isSide_s0 hz0]; exact F₀.s0_cell hG hb0 (F₀.hpos_spec hG hb0 hc0 hbc).2.1
    set N := W.ins.crossSide (F₀.sR (Fin.last n)) (W.ins.crossingOf z)
    have hU := (neg_iff_side F₀ hG hb0 hc0 hbc (Ne.symm (Fin.castSucc_ne_last _))
      (Ne.symm (Fin.castSucc_ne_last _)) hz hcs N).2 rfl
    exact sweep hA h3 hy0 hd₀ hx0 _ W.ins F₀ N hG hD hP rfl hU rfl
  · -- `n = 2`: the doubling walk visits all four cells
    have hn2 : n = 2 := by omega
    have hcard : Fintype.card A.Cell = Fintype.card (Fin (2 * n)) := by
      rw [A.card_cells, A.card_X, Fintype.card_fin, hn2]
    have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨W.cell_inj, hcard.symm⟩
    obtain ⟨i, hi⟩ := hbij.2 f₂
    refine ⟨W.ins, hG, hD, ⟨y0, hy0, hP⟩, ?_⟩
    have := W.ins_passes i
    simp only at hi
    rwa [hi] at this

end Pca.Great
