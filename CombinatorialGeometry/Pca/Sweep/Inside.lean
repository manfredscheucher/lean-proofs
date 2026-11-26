/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH p. 323: the inside order on loops (package N, sketch only in source)

"We can define a partial order on loops. Let `γ` and `γ'` be loops with endpoints `i < j` and
`i' < j'`. We say that `γ` is *inside* `γ'` if `i' < i < j < j'`. It is not hard to see that the
inside relation is acyclic and gives a partial order."

**Sketch only in source.** With `Inside` defined by the positions of the ends (`Pca/Sweep/Basic.lean`)
this is nesting of intervals; the only graph-specific point is that a loop has exactly two
positions (`sweepEnds` has two elements).
-/
import Pca.Sweep.J_Basic

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- The ends of a loop are determined by `sweepEnds`. -/
private theorem no_loopEnds_unique {γ : Fin n} {i j i' j' : ℕ} (h : Γ.LoopEnds γ i j)
    (h' : Γ.LoopEnds γ i' j') : i = i' ∧ j = j' := by
  obtain ⟨-, hij, he⟩ := h
  obtain ⟨-, hij', he'⟩ := h'
  have hs : ({i, j} : Finset ℕ) = {i', j'} := he.symm.trans he'
  have hi : i ∈ ({i', j'} : Finset ℕ) := hs ▸ by simp
  have hj : j ∈ ({i', j'} : Finset ℕ) := hs ▸ by simp
  have hi' : i' ∈ ({i, j} : Finset ℕ) := hs ▸ by simp
  have hj' : j' ∈ ({i, j} : Finset ℕ) := hs ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hi' hj'
  omega

theorem inside_irrefl (γ : Fin n) : ¬ Γ.Inside γ γ := by
  rintro ⟨i, j, i', j', h, h', hi, -⟩
  have := (no_loopEnds_unique h h').1
  omega

theorem inside_trans {γ₁ γ₂ γ₃ : Fin n} (h₁ : Γ.Inside γ₁ γ₂) (h₂ : Γ.Inside γ₂ γ₃) :
    Γ.Inside γ₁ γ₃ := by
  obtain ⟨i₁, j₁, i₂, j₂, l₁, l₂, hi, hj⟩ := h₁
  obtain ⟨k₂, m₂, i₃, j₃, l₂', l₃, hi', hj'⟩ := h₂
  obtain ⟨e1, e2⟩ := no_loopEnds_unique l₂ l₂'
  exact ⟨i₁, j₁, i₃, j₃, l₁, l₃, by omega, by omega⟩

/-- The sweeping curve is never inside another loop: every vertex on the sweep lies on `S`, so a
loop's ends are among the (two) ends of `S`. -/
private theorem no_not_inside_S {γ : Fin n} : ¬ Γ.Inside Γ.S γ := by
  classical
  rintro ⟨i, j, i', j', ⟨-, hij, hS⟩, ⟨-, hij', hγ⟩, hi, hj⟩
  have hsub : Γ.sweepEnds γ ⊆ Γ.sweepEnds Γ.S := by
    unfold sweepEnds
    refine image_subset_image (monotone_filter_right _ ?_)
    intro x _ hx
    exact ⟨hx.1, hx.1.1⟩
  rw [hS, hγ] at hsub
  have h1 : i' ∈ ({i, j} : Finset ℕ) := hsub (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1
  omega

/-- A loop other than `S` has a dart above the sweep. -/
private theorem no_present_of_isLoop {γ : Fin n} (hγ : Γ.IsLoop γ) (hS : γ ≠ Γ.S) :
    Γ.Present γ := by
  classical
  have hpos : 0 < (univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve γ x)).card := by
    have : Γ.numSweepHits γ = 2 := hγ
    unfold numSweepHits at this
    omega
  obtain ⟨x, hx⟩ := card_pos.1 hpos
  obtain ⟨⟨hxS, -⟩, hxγ⟩ := (mem_filter.1 hx).2
  obtain ⟨y, rfl⟩ := x.exists_mk
  change Γ.S ∈ Γ.curves (Γ.crossingOf y) at hxS
  change γ ∈ Γ.curves (Γ.crossingOf y) at hxγ
  rw [j_curves_crossingOf, mem_insert, mem_singleton] at hxS hxγ
  -- a dart `w` of `γ` with `σ w` on `S`
  obtain ⟨w, hw, hσw⟩ : ∃ w, Γ.curve w = γ ∧ Γ.curve (Γ.σ w) = Γ.S := by
    rcases hxγ with h | h
    · refine ⟨y, h.symm, ?_⟩
      rcases hxS with h' | h'
      · exact absurd (h.trans h'.symm) hS
      · exact h'.symm
    · refine ⟨Γ.σ y, h.symm, ?_⟩
      rw [j_curve_σσ]
      rcases hxS with h' | h'
      · exact h'.symm
      · exact absurd (h.trans h'.symm) hS
  have hwS : Γ.curve w ≠ Γ.S := hw ▸ hS
  have h1 := Γ.isSide w
  have h2 := Γ.isSide (Γ.σ w)
  change Γ.side (Γ.cellOf w) + Γ.side (Γ.cellOf (Γ.α w)) = _ at h1
  change Γ.side (Γ.cellOf (Γ.σ w)) + Γ.side (Γ.cellOf (Γ.α (Γ.σ w))) = _ at h2
  rw [if_neg hwS] at h1
  rw [if_pos hσw, ← j_cellOf_σ Γ (Γ.σ w), j_cellOf_σ Γ w] at h2
  refine ⟨hS, ?_⟩
  rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (Γ.side (Γ.cellOf w)) with h0 | h0
  · refine ⟨Γ.σ (Γ.σ w), by rw [j_curve_σσ, hw], by rw [j_curve_σσ]; exact hwS, ?_⟩
    show Γ.side _ = 1
    have h3 : Γ.side (Γ.cellOf (Γ.α w)) = 0 := by
      rw [h0] at h1; rw [j_zmod2_eq_add_of_add_eq h1]; rfl
    rw [h3, zero_add] at h2
    exact h2
  · exact ⟨w, hw, hwS, h0⟩

/-- SH p. 324: "Choose `γ` to be a loop with no loop inside it". -/
theorem exists_innermost (h : ∃ γ, Γ.Present γ ∧ Γ.IsLoop γ) :
    ∃ γ, Γ.Present γ ∧ Γ.IsLoop γ ∧ ∀ γ', ¬ Γ.Inside γ' γ := by
  have : Std.Irrefl Γ.Inside := ⟨inside_irrefl⟩
  have : IsTrans (Fin n) Γ.Inside := ⟨fun _ _ _ => inside_trans⟩
  have hwf : WellFounded Γ.Inside := Finite.wellFounded_of_trans_of_irrefl _
  obtain ⟨γ, ⟨hγP, hγL⟩, hmin⟩ := hwf.has_min {γ | Γ.Present γ ∧ Γ.IsLoop γ} h
  refine ⟨γ, hγP, hγL, fun γ' hin => hmin γ' ?_ hin⟩
  have hL : Γ.IsLoop γ' := by obtain ⟨i, j, -, -, hl, -⟩ := hin; exact hl.1
  have hS : γ' ≠ Γ.S := by rintro rfl; exact no_not_inside_S hin
  exact ⟨no_present_of_isLoop hL hS, hL⟩

end SConf

end Pca.Sweep
