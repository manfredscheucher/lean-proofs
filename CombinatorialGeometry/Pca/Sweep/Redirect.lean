/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH sweep in graph language: directing a curve to infinity (package D)

SH Lemma 3.9, Case 1 (p. 321): "Now we can direct `γ(j)` to infinity without causing any more
intersections or allowing `c` to make progress, as indicated by the dotted line in Figure 8. Thus,
we delete the vertex `j`." Here `j` is the last vertex on the sweep (no curves `γ(m)` with
`j < m`), so the dotted line runs along `c` from `j` to `∞` and crosses nothing.

In graph language this changes **no dart**: the last finite edge `[j − 1, j]` joins the ∞-arc, so
the vertex `j` becomes a point where a ray reaches `∞`. The cells, `σ`, `α`, the labels and the side
function stay; only the ∞-arc grows by one dart (it now starts with `d`, one more inner crossing).
-/
import Pca.Sweep.Basic

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- Extending the ∞-arc by the last finite edge (the dart `d` with `straight d` in the arc). -/
theorem exists_redirect {d : D} (hd : Γ.IsFinSeg d) (hlast : Γ.straight d ∈ Γ.infArc) :
    ∃ Γ' : SConf n D, Γ'.σ = Γ.σ ∧ Γ'.α = Γ.α ∧ Γ'.curve = Γ.curve ∧ Γ'.S = Γ.S ∧
      Γ'.infStart = some d ∧ Γ'.infLen = Γ.infLen + 1 ∧
      ∀ y, Γ'.side (Orbit.mk (Γ'.σ * Γ'.α) y) = Γ.side (Γ.cellOf y) := by
  obtain ⟨⟨hdS, hdUp⟩, hdA⟩ := hd
  obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z := by
    cases h : Γ.infStart with
    | none => simp [infArc, arcOf, h] at hlast
    | some z => exact ⟨z, rfl⟩
  have hmem : ∀ e, e ∈ Γ.infArc ↔ ∃ i ≤ Γ.infLen, (Γ.straight ^ i) z = e := by
    intro e
    simp [infArc, arcOf, hz, straight]
  -- the start of the arc is `straight d`
  have hzd : z = Γ.straight d := by
    obtain ⟨i, hi, hie⟩ := (hmem _).1 hlast
    rcases i with _ | i
    · simpa using hie
    · exfalso; apply hdA
      refine (hmem _).2 ⟨i, by omega, ?_⟩
      apply Γ.straight.injective
      rw [← hie, pow_succ', Perm.mul_apply]
  have hpow : ∀ i, (Γ.straight ^ (i + 1)) d = (Γ.straight ^ i) z := by
    intro i; rw [hzd, pow_succ, Perm.mul_apply]
  -- the arc does not yet cover the whole cycle
  have hlt : Γ.infLen + 1 ≤ period (straightPerm Γ.σ Γ.α) d := by
    have hp := period_pos (straightPerm Γ.σ Γ.α) d
    by_contra hk
    apply hdA
    refine (hmem _).2 ⟨period (straightPerm Γ.σ Γ.α) d - 1, by omega, ?_⟩
    rw [← hpow, Nat.sub_add_cancel hp]
    change (straightPerm Γ.σ Γ.α ^ period (straightPerm Γ.σ Γ.α) d) d = d
    rw [Perm.coe_pow]; exact iterate_period _ _
  refine ⟨{ Γ with
    infStart := some d
    infLen := Γ.infLen + 1
    infStart_isSome := fun _ => rfl
    infLen_le := ?_
    infArc_sweep := ?_ }, rfl, rfl, rfl, rfl, rfl, rfl, fun y => rfl⟩
  · intro z' hz'
    obtain rfl : z' = d := (Option.mem_some_iff.1 hz').symm
    exact hlt
  · intro e he
    simp only [arcOf, Option.elim, mem_image, mem_range] at he
    obtain ⟨j, hj, rfl⟩ := he
    rcases j with _ | j
    · exact ⟨hdS, hdUp⟩
    · have h := Γ.infArc_sweep ((Γ.straight ^ j) z) ((hmem _).2 ⟨j, by omega, rfl⟩)
      rw [← hpow] at h
      exact h

end SConf

end Pca.Sweep
