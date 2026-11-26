/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package I (SH Lemma 3.9, Case 2): back to Case 1 for another curve

`i_reduce`: a configuration in which removing the curve `β` leaves an empty triangle
`Δ(j, x, k)` above the finite edge `e` of `Γ`, both legs crossed once by `β` and the apex `x` hidden
from `[j, k]` by `β`, is Case 1 of SH Lemma 3.9 for the removal of `β` (`lemma_3_9_case1`), so it
does not occur. The legs are given in `Γ`: the first leg is `σ e` (crossing `β` at its end) and
`straight (σ e)`, the second leg `q = σ (α (straight (σ e)))` (crossing `β` at its end) and
`straight q`, closing up with `σ (α (straight q)) = α e`.
-/
import Pca.Sweep.I_Chord

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

open Removal

/-- A finite edge of `Γ` whose end is kept is a finite edge of `Γ − R`. -/
theorem i_finSeg {R : Finset (Fin n)} (Y : Γ.Removal R) {e₂ : Y.D'} (he : Γ.IsFinSeg (Y.ι e₂))
    (hy : ¬ Γ.Deleted R (Γ.crossingOf (Γ.α (Y.ι e₂))))
    (hα : Y.ι (Y.Γ'.α e₂) = Γ.α (Y.ι e₂)) : Y.Γ'.IsFinSeg e₂ := by
  refine ⟨⟨by rw [Y.isRemoval.curve, Y.isRemoval.S]; exact he.1.1, ?_⟩, ?_⟩
  · have := Y.isRemoval.side (Y.Γ'.α e₂)
    rw [hα] at this
    exact this.trans he.1.2
  · intro hm
    obtain ⟨z', hz'⟩ := Option.isSome_iff_exists.1 (Y.Γ'.infStart_isSome ⟨e₂⟩)
    rcases ab_inf_of_arc hz' hm with hez | hinf
    · obtain ⟨z, hz, k, hdel, hk⟩ := Y.isRemoval.infStart z' (by rw [hz']; rfl)
      rw [← hez] at hdel hk
      have hk0 : k = 0 := by
        by_contra hk0
        exact hy (by have := hdel 0 (by omega); rwa [pow_zero, Perm.one_apply] at this)
      rw [hk0, pow_zero, Perm.one_apply] at hk
      have hz2 : Γ.infStart = some z := hz
      exact he.2 ((no_mem_infArc hz2).2 ⟨0, Nat.zero_le _, by rw [pow_zero, Perm.one_apply, hk]⟩)
    · have h1 := (Y.r_inf _).1 hinf
      rw [r_rΨ_mk] at h1
      exact (f_finSeg_fin he).1.2 h1

/-- Case 1 for the removal of `β` (see module doc). -/
theorem i_reduce (hΓ : Γ.MinCE) {β : Fin n} (hβ : Γ.Present β) {e : D} (he : Γ.IsFinSeg e)
    (hj : β ∉ Γ.curves (Γ.crossingOf e)) (hy : β ∉ Γ.curves (Γ.crossingOf (Γ.α e)))
    (hp1 : β ∈ Γ.curves (Γ.crossingOf (Γ.α (Γ.σ e))))
    (hp2 : β ∉ Γ.curves (Γ.crossingOf (Γ.α (Γ.straight (Γ.σ e)))))
    (hq1 : β ∈ Γ.curves (Γ.crossingOf (Γ.α (Γ.σ (Γ.α (Γ.straight (Γ.σ e)))))))
    (hq2 : β ∉ Γ.curves (Γ.crossingOf (Γ.α (Γ.straight (Γ.σ (Γ.α (Γ.straight (Γ.σ e))))))))
    (hclose : Γ.σ (Γ.α (Γ.straight (Γ.σ (Γ.α (Γ.straight (Γ.σ e)))))) = Γ.α e)
    (hhid : ∀ x ∈ (Γ.cellOf (Γ.α e)).darts,
      Γ.crossingOf x ≠ Γ.crossingOf (Γ.σ (Γ.α (Γ.straight (Γ.σ e))))) : False := by
  have hS : Γ.S ∉ ({β} : Finset (Fin n)) := by
    rw [mem_singleton]; exact fun h => hβ.1 h.symm
  obtain ⟨Y⟩ := exists_removal _ hS
  have hdel : ∀ x, Γ.Deleted {β} x ↔ β ∈ Γ.curves x := fun x => gk_deleted_singleton
  obtain ⟨e₂, he₂⟩ := (Y.isRemoval.range e).2
    (r_keep_S he.1.1 (fun h => hj ((hdel _).1 h)))
  set q := Γ.σ (Γ.α (Γ.straight (Γ.σ e))) with hq
  -- the base
  have hh0 : Y.hits e₂ = 0 := i_hits_eq Y e₂ (fun i hi => absurd hi (Nat.not_lt_zero _))
    (by rw [pow_zero, Perm.one_apply, he₂, hdel]; exact hy)
  have hια : Y.ι (Y.Γ'.α e₂) = Γ.α e := by
    rw [(gk_hits_spec Y e₂).2.2, hh0, pow_zero, Perm.one_apply, he₂]
  -- the first leg
  have hισ : Y.ι (Y.Γ'.σ e₂) = Γ.σ e := by rw [Y.isRemoval.σ, he₂]
  have hh1 : Y.hits (Y.Γ'.σ e₂) = 1 := by
    refine i_hits_eq Y _ (fun i hi => ?_) ?_
    · rw [show i = 0 by omega, pow_zero, Perm.one_apply, hισ, hdel]; exact hp1
    · rw [pow_one, hισ, hdel]; exact hp2
  have hιφ : Y.ι (Y.Γ'.φ (Y.Γ'.σ e₂)) = q := by
    rw [j_φ_apply, Y.isRemoval.σ, (gk_hits_spec Y _).2.2, hh1, pow_one, hισ]
  -- the second leg
  have hh2 : Y.hits (Y.Γ'.φ (Y.Γ'.σ e₂)) = 1 := by
    refine i_hits_eq Y _ (fun i hi => ?_) ?_
    · rw [show i = 0 by omega, pow_zero, Perm.one_apply, hιφ, hdel]; exact hq1
    · rw [pow_one, hιφ, hdel]; exact hq2
  have hιφφ : Y.ι (Y.Γ'.φ (Y.Γ'.φ (Y.Γ'.σ e₂))) = Γ.α e := by
    rw [j_φ_apply Y.Γ' (Y.Γ'.φ _), Y.isRemoval.σ, (gk_hits_spec Y _).2.2, hh2, pow_one, hιφ,
      hclose]
  have hφφ : Y.Γ'.φ (Y.Γ'.φ (Y.Γ'.σ e₂)) = Y.Γ'.α e₂ :=
    Y.isRemoval.inj (hιφφ.trans hια.symm)
  -- the cell above `e₂` is a triangle
  have hφα : Y.Γ'.φ (Y.Γ'.α e₂) = Y.Γ'.σ e₂ := by rw [j_φ_apply, j_α_α]
  have h1 : Y.Γ'.φ (Y.Γ'.α e₂) ≠ Y.Γ'.α e₂ := by
    rw [hφα]
    intro h
    have h' := congrArg Y.ι h
    rw [hισ, hια] at h'
    have := congrArg Γ.curve h'
    rw [j_curve_α] at this
    exact no_curve_σ_ne e this
  have h3 : Y.Γ'.φ (Y.Γ'.φ (Y.Γ'.φ (Y.Γ'.α e₂))) = Y.Γ'.α e₂ := by rw [hφα, hφφ]
  have h2 : Y.Γ'.φ (Y.Γ'.φ (Y.Γ'.α e₂)) ≠ Y.Γ'.α e₂ := by
    intro h
    rw [h] at h3
    exact h1 h3
  have hfin := i_finSeg Y (by rw [he₂]; exact he)
    (by rw [he₂, hdel]; exact hy) (by rw [hια, he₂])
  have htri : Y.Γ'.EmptyTriAt e₂ := ⟨hfin, by
    unfold upperCell; rw [c_size]; exact c_period_three _ _ h1 h2 h3⟩
  have hv : ¬ ApexVisible Y e₂ := by
    rintro ⟨x, hx, hcx⟩
    rw [he₂, hιφ] at *
    exact hhid x hx hcx
  exact hΓ.lemma_3_9_case1 hβ Y htri hv hh1 hh2

end SConf

end Pca.Sweep
