/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package F (SH Lemma 3.8), generic helpers

Small facts about sweep configurations used in `Pca/Sweep/L38.lean`: the ends of a finite edge
are vertices on the sweep, crossings along one straight walk are distinct within a period, a cell
of size `2` / `3` closes after `2` / `3` steps of `φ`, and the crossing at the end of a dart above
the sweep is a vertex above the sweep.
-/
import Pca.Sweep.NO_Sweep

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- Two darts of the same curve at one crossing are equal or opposite. -/
theorem f_eq_or_eq_σσ {a b : D} (hx : Γ.crossingOf a = Γ.crossingOf b)
    (hc : Γ.curve a = Γ.curve b) : b = a ∨ b = Γ.σ (Γ.σ a) := by
  rcases no_mem_crossing hx.symm with h | h | h | h
  · exact Or.inl h
  · exact absurd (h ▸ hc.symm) (no_curve_σ_ne a)
  · exact Or.inr h
  · exfalso
    have h1 := no_curve_σ_ne (Γ := Γ) (Γ.σ (Γ.σ a))
    rw [← h, Γ.j_curve_σσ] at h1
    exact h1 hc.symm

/-- The darts of a curve other than `S` keep being above `S` across their segment. -/
theorem f_above_α {y : D} (hy : Γ.Above y) : Γ.Above (Γ.α y) :=
  ⟨by rw [j_curve_α]; exact hy.1, by unfold Up; rw [no_side_α hy.1]; exact hy.2⟩

/-- Both ends of a finite edge are vertices on the sweep. -/
theorem f_finSeg_fin {d : D} (hd : Γ.IsFinSeg d) :
    Γ.IsFinVertex (Γ.crossingOf d) ∧ Γ.IsFinVertex (Γ.crossingOf (Γ.α d)) := by
  obtain ⟨hsw, hnot⟩ := hd
  have hS : Γ.curve d = Γ.S := hsw.1
  have hSα : Γ.curve (Γ.α d) = Γ.S := by rw [j_curve_α]; exact hS
  have hside : Γ.side (Γ.cellOf (Γ.α d)) = 1 := hsw.2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show Γ.S ∈ Γ.curves (Γ.crossingOf d)
    rw [j_curves_crossingOf, hS]; exact mem_insert_self _ _
  · rintro ⟨z, hz, i, hi, hx⟩
    have hz' : Γ.infStart = some z := hz
    have hs : Γ.IsSweepDart ((Γ.straight ^ i) z) := no_sweep_pow (no_z_sweep hz') i
    have hcur : Γ.curve (Γ.α ((Γ.straight ^ i) z)) = Γ.curve d := by
      rw [j_curve_α, hs.1, hS]
    rcases f_eq_or_eq_σσ hx hcur with h | h
    · have h0 := (no_sweep_iff hs.1).1 hs
      rw [h, j_α_α, h0] at hside
      exact absurd hside (by decide)
    · apply hnot
      rw [no_mem_infArc hz']
      exact ⟨i + 1, hi, by rw [no_pow_succ, h]; rfl⟩
  · show Γ.S ∈ Γ.curves (Γ.crossingOf (Γ.α d))
    rw [j_curves_crossingOf, hSα]; exact mem_insert_self _ _
  · rintro ⟨z, hz, i, hi, hx⟩
    have hz' : Γ.infStart = some z := hz
    have hs : Γ.IsSweepDart ((Γ.straight ^ i) z) := no_sweep_pow (no_z_sweep hz') i
    have hcur : Γ.curve (Γ.α ((Γ.straight ^ i) z)) = Γ.curve (Γ.α d) := by
      rw [j_curve_α, hs.1, hSα]
    rcases f_eq_or_eq_σσ hx hcur with h | h
    · apply hnot
      have h2 := congrArg Γ.α h
      rw [j_α_α, j_α_α] at h2
      rw [no_mem_infArc hz']
      exact ⟨i, hi.le, h2.symm⟩
    · have hs1 : Γ.IsSweepDart ((Γ.straight ^ (i + 1)) z) := no_sweep_pow (no_z_sweep hz') _
      have he : (Γ.straight ^ (i + 1)) z = Γ.α d := by rw [no_pow_succ, h]; rfl
      rw [he] at hs1
      have h0 := (no_sweep_iff hsw.1).1 hsw
      have h1 : Γ.side (Γ.cellOf (Γ.α (Γ.α d))) = 1 := hs1.2
      rw [j_α_α, h0] at h1
      exact absurd h1 (by decide)

/-- Crossings along one straight walk are distinct within a period. -/
theorem f_cross_ne {h : D} {i j : ℕ} (hij : i < j) (hj : j < period Γ.straight h) :
    Γ.crossingOf (Γ.α ((Γ.straight ^ i) h)) ≠ Γ.crossingOf (Γ.α ((Γ.straight ^ j) h)) := by
  intro hx
  have hc : Γ.curve (Γ.α ((Γ.straight ^ i) h)) = Γ.curve (Γ.α ((Γ.straight ^ j) h)) := by
    rw [j_curve_α, j_curve_α, no_curve_pow, no_curve_pow]
  rcases f_eq_or_eq_σσ hx hc with h1 | h1
  · have h2 := congrArg Γ.α h1
    rw [j_α_α, j_α_α] at h2
    have := no_pow_inj hj (by omega) h2
    omega
  · have ha : Γ.α ((Γ.straight ^ j) h) = (Γ.straight ^ (i + 1)) h := by
      rw [h1, no_pow_succ]; rfl
    have hb : Γ.σ (Γ.σ ((Γ.straight ^ (i + 1)) h)) = (Γ.straight ^ (j + 1)) h := by
      rw [show (Γ.straight ^ (j + 1)) h = Γ.straight ((Γ.straight ^ j) h) from no_pow_succ _ _,
        j_straight_apply, ha]
    apply no_not_sameCycle_straight_σσ ((Γ.straight ^ (i + 1)) h)
    rw [hb]
    exact Perm.sameCycle_pow_left.2 (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ h))

/-- A cell of size `2` closes after two steps of `φ`. -/
theorem f_φ_two {x : D} (h : (Γ.cellOf x).size = 2) : Γ.φ (Γ.φ x) = x := by
  rw [Orbit.size, cellOf, Orbit.darts_mk, card_orbitFinset] at h
  have := iterate_period Γ.φ x
  rw [h] at this
  exact this

/-- A cell of size `3` closes after three steps of `φ`. -/
theorem f_φ_three {x : D} (h : (Γ.cellOf x).size = 3) : Γ.φ (Γ.φ (Γ.φ x)) = x := by
  rw [Orbit.size, cellOf, Orbit.darts_mk, card_orbitFinset] at h
  have := iterate_period Γ.φ x
  rw [h] at this
  exact this

/-- The crossing at the end of a dart above the sweep, where the other curve is not `S`, is a
vertex above the sweep. -/
theorem f_aboveVertex {a : D} (ha : Γ.Above a) (hc : Γ.curve (Γ.σ (Γ.α a)) ≠ Γ.S) :
    Γ.IsAboveVertex (Γ.crossingOf (Γ.α a)) := by
  refine ⟨?_, Γ.α a, Orbit.mem_darts.2 rfl, f_above_α ha⟩
  show Γ.S ∉ Γ.curves _
  rw [j_curves_crossingOf, mem_insert, mem_singleton, j_curve_α]
  rintro (h | h)
  · exact ha.1 h.symm
  · exact hc h.symm

end SConf

end Pca.Sweep
