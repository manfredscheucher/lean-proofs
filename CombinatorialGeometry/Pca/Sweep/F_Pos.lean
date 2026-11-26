/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package F (SH Lemma 3.8), positions across a removal

A finite edge `[k, l]` of a removal `Γ'` of `Γ` (a joined segment of `S`) has `k < l` also in
`Γ`: its joined segment does not run through the start of the ∞-arc of `Γ` (that piece belongs to
the ∞-arc of `Γ'`), so the positions along the sweep grow along it.
-/
import Pca.Sweep.C_Trans
import Pca.Sweep.F_Basic

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- The start of a finite edge of a removal is a sweep dart of `Γ`. -/
theorem f_ι_sweep {R : Finset (Fin n)} (X : Γ.Removal R) {e' : X.D'}
    (hsw : X.Γ'.IsSweepDart e') : Γ.IsSweepDart (X.ι e') := by
  refine ⟨by rw [← X.isRemoval.curve, ← X.isRemoval.S]; exact hsw.1, ?_⟩
  unfold Up
  rw [← j_cellOf_σ, ← X.isRemoval.σ]
  have h1 := X.isRemoval.side (X.Γ'.σ e')
  have h2 : X.Γ'.side (X.Γ'.cellOf (X.Γ'.σ e')) = 1 := by
    rw [j_cellOf_σ]; exact hsw.2
  exact h1.symm.trans h2

/-- **Positions along a finite edge of a removal**: `pos k < pos l` in `Γ`. -/
theorem f_pos_lt {R : Finset (Fin n)} (X : Γ.Removal R) {e' : X.D'} (hsw : X.Γ'.IsFinSeg e') :
    Γ.pos (Γ.crossingOf (X.ι e')) < Γ.pos (Γ.crossingOf (X.ι (X.Γ'.α e'))) := by
  have hs := f_ι_sweep X hsw.1
  obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z :=
    Option.isSome_iff_exists.1 (Γ.infStart_isSome ⟨X.ι e'⟩)
  have hfin : Γ.IsFinVertex (Γ.crossingOf (X.ι e')) :=
    (X.r_finVertex (X.Γ'.crossingOf e')).1 (f_finSeg_fin hsw).1
  obtain ⟨t, ht, hte⟩ := no_noC_surj hz hs
  have htf : t + Γ.infLen < period Γ.straight z := (no_noC_fin hz ht).1 (hte ▸ hfin)
  obtain ⟨e, ⟨k, hdel, rfl⟩, -, hαe⟩ := X.isRemoval.α e'
  have hpow : ∀ i, (Γ.straight ^ i) (X.ι e') = Γ.noC z (t + i) := by
    intro i
    rw [← hte]
    unfold noC
    rw [← no_pow_add, add_comm i t]
  have hend : Γ.crossingOf (X.ι (X.Γ'.α e')) = Γ.crossingOf (Γ.noC z (t + k + 1)) := by
    rw [hαe, ← no_crossingOf_α_straight, ← no_pow_succ, hpow, add_assoc]
  -- the joined segment does not pass the start `z` of the ∞-arc
  have hno : t + k + 1 + Γ.infLen < period Γ.straight z := by
    by_contra hc
    push Not at hc
    set i0 := period Γ.straight z - Γ.infLen - 1 - t with hi0
    have hzi : (Γ.straight ^ i0) (X.ι e') = z := by
      rw [hpow, noC, ← no_pow_add,
        show t + i0 + (Γ.infLen + 1) = 0 + period Γ.straight z by omega, no_pow_period]
      rfl
    have hne : Nonempty X.D' := ⟨e'⟩
    obtain ⟨z', hz'⟩ := Option.isSome_iff_exists.1 (X.Γ'.infStart_isSome hne)
    obtain ⟨z₁, hz₁, k', hdel', hk'⟩ := X.isRemoval.infStart z' (by rw [hz']; rfl)
    rw [hz, Option.mem_def, Option.some_inj] at hz₁
    subst hz₁
    have heq : X.ι z' = X.ι e' :=
      c_piece_unique (X.r_keep z').1 (X.r_keep e').1 hdel'
        (fun j hj => hdel j (by omega)) (hk'.trans hzi.symm)
    have he' : e' ∈ X.Γ'.infArc := by
      rw [no_mem_infArc hz', ← X.isRemoval.inj heq]
      exact ⟨0, Nat.zero_le _, rfl⟩
    exact hsw.2 he'
  rw [hend, ← hte, no_noC_pos hz ht, no_noC_pos hz (by omega)]
  omega

end SConf

end Pca.Sweep
