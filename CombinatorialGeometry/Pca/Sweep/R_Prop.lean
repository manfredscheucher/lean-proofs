/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package R (removal), properties of every removal

Helper file for `Pca/Sweep/Removal.lean`: from the specification `IsRemoval` alone, the
crossings of the result map injectively to crossings of `Γ` with the same curves (`rΨ`), vertices
on and above the sweep map to such vertices, and present curves stay present.
-/
import Pca.Sweep.R_Basic

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {R : Finset (Fin n)} (X : Γ.Removal R)

namespace Removal

theorem r_keep (d' : X.D') : Γ.Keep R (X.ι d') := (X.isRemoval.range _).1 ⟨d', rfl⟩

theorem r_ι_σ_pow (d' : X.D') (k : ℕ) : X.ι ((X.Γ'.σ ^ k) d') = (Γ.σ ^ k) (X.ι d') := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Perm.mul_apply, X.isRemoval.σ, ih, pow_succ', Perm.mul_apply]

theorem r_sameCycle_iff {a b : X.D'} :
    X.Γ'.σ.SameCycle a b ↔ Γ.σ.SameCycle (X.ι a) (X.ι b) := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := h.exists_nat_pow_eq
    rw [r_ι_σ_pow]; exact Pca.MapFacts.sameCycle_of_pow _ _ _
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [← r_ι_σ_pow] at hk
    rw [← X.isRemoval.inj hk]; exact Pca.MapFacts.sameCycle_of_pow _ _ _

/-- The crossings of the result as crossings of `Γ`. -/
def rΨ : X.Γ'.Crossing → Γ.Crossing :=
  Quotient.map' X.ι fun _ _ h => (r_sameCycle_iff X).1 h

theorem r_rΨ_mk (d' : X.D') : rΨ X (X.Γ'.crossingOf d') = Γ.crossingOf (X.ι d') := rfl

theorem r_rΨ_inj : Function.Injective (rΨ X) := by
  intro o1 o2 he
  obtain ⟨a, rfl⟩ := o1.exists_mk
  obtain ⟨b, rfl⟩ := o2.exists_mk
  change Γ.crossingOf (X.ι a) = Γ.crossingOf (X.ι b) at he
  unfold crossingOf at he
  rw [Orbit.mk_eq_mk] at he
  exact Orbit.mk_eq_mk.2 ((r_sameCycle_iff X).2 he)

theorem r_curves (d' : X.D') :
    X.Γ'.curves (X.Γ'.crossingOf d') = Γ.curves (Γ.crossingOf (X.ι d')) := by
  rw [j_curves_crossingOf, j_curves_crossingOf, X.isRemoval.curve, X.isRemoval.curve,
    X.isRemoval.σ]

theorem r_curves_Ψ (x' : X.Γ'.Crossing) : X.Γ'.curves x' = Γ.curves (rΨ X x') := by
  obtain ⟨d', rfl⟩ := x'.exists_mk
  exact r_curves X d'

theorem r_onSweep (x' : X.Γ'.Crossing) : X.Γ'.OnSweep x' ↔ Γ.OnSweep (rΨ X x') := by
  unfold OnSweep; rw [r_curves_Ψ, X.isRemoval.S]

theorem r_inf (x' : X.Γ'.Crossing) : X.Γ'.IsInfVertex x' ↔ Γ.IsInfVertex (rΨ X x') := by
  obtain ⟨d', rfl⟩ := x'.exists_mk
  exact X.isRemoval.infVertex d'

theorem r_finVertex (x' : X.Γ'.Crossing) : X.Γ'.IsFinVertex x' ↔ Γ.IsFinVertex (rΨ X x') := by
  unfold IsFinVertex; rw [r_onSweep, r_inf]

theorem r_above {d' : X.D'} (h : X.Γ'.Above d') : Γ.Above (X.ι d') := by
  refine ⟨by rw [← X.isRemoval.curve, ← X.isRemoval.S]; exact h.1, ?_⟩
  have h2 : X.Γ'.side (X.Γ'.cellOf d') = 1 := h.2
  exact (X.isRemoval.side d').symm.trans h2

theorem r_mem_darts {d' : X.D'} {x' : X.Γ'.Crossing} (h : d' ∈ x'.darts) :
    X.ι d' ∈ (rΨ X x').darts := by
  rw [Orbit.mem_darts] at h ⊢
  rw [← h]; rfl

theorem r_aboveVertex {x' : X.Γ'.Crossing} (h : X.Γ'.IsAboveVertex x') :
    Γ.IsAboveVertex (rΨ X x') := by
  refine ⟨by rw [← r_onSweep]; exact h.1, ?_⟩
  obtain ⟨d', hd', ha⟩ := h.2
  exact ⟨_, r_mem_darts X hd', r_above X ha⟩

theorem r_S_not_mem (d' : X.D') : Γ.S ∉ R := by
  obtain ⟨e, he, hde⟩ := (r_keep X d').2
  have := r_keep_of_eqvGen (r_keep X d') hde
  rw [← he]; exact Γ.r_curve_not_mem R this.1

theorem r_numVertices_le : X.Γ'.numVertices ≤ Γ.numVertices := by
  classical
  unfold numVertices
  refine card_le_card_of_injOn (rΨ X) ?_ (fun a _ b _ h => r_rΨ_inj X h)
  intro x hx
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
  rcases hx with h | h
  · exact Or.inl ((r_finVertex X x).1 h)
  · exact Or.inr (r_aboveVertex X h)

theorem r_present {γ : Fin n} (h : X.Γ'.Present γ) : Γ.Present γ ∧ γ ∉ R := by
  obtain ⟨hS, d', hc, ha⟩ := h
  refine ⟨⟨by rw [← X.isRemoval.S]; exact hS, X.ι d', by rw [← X.isRemoval.curve]; exact hc,
    r_above X ha⟩, ?_⟩
  rw [← hc, X.isRemoval.curve]
  exact Γ.r_curve_not_mem R (r_keep X d').1

theorem r_numCurves_lt (h : ∃ γ ∈ R, Γ.Present γ) : X.Γ'.numCurves < Γ.numCurves := by
  classical
  obtain ⟨γ, hγR, hγ⟩ := h
  unfold numCurves
  have hsub : univ.filter X.Γ'.Present ⊆ (univ.filter Γ.Present).erase γ := by
    intro c hc
    rw [mem_filter] at hc
    obtain ⟨h1, h2⟩ := r_present X hc.2
    exact mem_erase.2 ⟨fun he => h2 (he ▸ hγR), mem_filter.2 ⟨mem_univ _, h1⟩⟩
  have := card_le_card hsub
  have h2 := card_erase_lt_of_mem (mem_filter.2 ⟨mem_univ _, hγ⟩)
  convert lt_of_le_of_lt this h2

theorem r_meetsSweep_to {γ : Fin n} (h : X.Γ'.MeetsSweep γ) : Γ.MeetsSweep γ := by
  obtain ⟨x', hf, hc⟩ := h
  refine ⟨rΨ X x', (r_finVertex X x').1 hf, ?_⟩
  unfold OnCurve at hc ⊢
  rwa [← r_curves_Ψ]

theorem r_meetsSweep_of {γ : Fin n} (hγS : γ ≠ Γ.S) (hγR : γ ∉ R) (hS : Γ.S ∉ R)
    (h : Γ.MeetsSweep γ) : X.Γ'.MeetsSweep γ := by
  obtain ⟨x, hf, hc⟩ := h
  obtain ⟨y, rfl⟩ := x.exists_mk
  have hcy := j_curves_crossingOf Γ y
  have hSm : Γ.S ∈ Γ.curves (Γ.crossingOf y) := hf.1
  have hγm : γ ∈ Γ.curves (Γ.crossingOf y) := hc
  rw [hcy, mem_insert, mem_singleton] at hSm hγm
  -- a dart of `S` at `x`
  obtain ⟨y0, hy0S, hy0⟩ : ∃ y0, Γ.curve y0 = Γ.S ∧ Γ.crossingOf y0 = Γ.crossingOf y := by
    rcases hSm with h | h
    · exact ⟨y, h.symm, rfl⟩
    · exact ⟨Γ.σ y, h.symm, j_crossingOf_σ Γ y⟩
  have hK : Γ.rK R y0 := by
    intro hdel
    rw [hy0] at hdel
    obtain ⟨c, hcR, hcm⟩ := hdel
    have hcm' : c ∈ Γ.curves (Γ.crossingOf y) := hcm
    rw [hcy, mem_insert, mem_singleton] at hcm'
    -- the two curves at `x` are `S` and `γ`
    rcases hSm with h1 | h1 <;> rcases hγm with h2 | h2 <;> rcases hcm' with h3 | h3 <;>
      first
      | exact hS (h1 ▸ h3 ▸ hcR)
      | exact hγR (h2 ▸ h3 ▸ hcR)
      | exact hγS (h2.trans h1.symm)
  obtain ⟨d', hd'⟩ := (X.isRemoval.range y0).2 (r_keep_S hy0S hK)
  refine ⟨X.Γ'.crossingOf d', ?_, ?_⟩
  · rw [r_finVertex, r_rΨ_mk, hd', hy0]; exact hf
  · unfold OnCurve; rw [r_curves, hd', hy0]; exact hc

end Removal

end SConf

end Pca.Sweep
