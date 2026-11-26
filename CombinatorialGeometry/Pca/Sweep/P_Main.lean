/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package P: the smaller configuration of the surgery (Lemma 3.11)

`p_surgery` (`doc/pca/sweep.md`, steps 3-4): from the data `PSurg`, the configuration
`K = pRedir Γ − pRem r` (the ∞-arc extended to everything outside `[tA, tB]`, then the curves
without a dart in the bounded component removed) is smaller than `Γ`, not finished, has no empty
hump or triangle, and a loop can be taken in `K` only if some loop is inside `γ`.
-/
import Pca.Sweep.P_Core
import Pca.Sweep.P_Redir
import Pca.Sweep.L34
import Pca.Sweep.AB_Basic
import Pca.Sweep.E_Basic
import Pca.Sweep.LD_Basic

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- No corner of a cell in the bounded component is deleted. -/
theorem p_corner_kept {r : Γ.Cell → ZMod 2} {e : D} (hu : Γ.Up (Γ.cellOf e))
    (hr : r (Γ.cellOf e) = 1) : ¬ Γ.Deleted (Γ.pRem r) (Γ.crossingOf (Γ.α e)) := by
  have hk : ∀ e', Γ.cellOf e' = Γ.cellOf e → Γ.curve e' ∉ Γ.pRem r := by
    intro e' he' hm
    by_cases hS : Γ.curve e' = Γ.S
    · exact p_S_not_mem_rem (hS ▸ hm)
    · refine (p_mem_rem.1 hm).2 ⟨e', rfl, ⟨hS, ?_⟩, by rw [he']; exact hr⟩
      unfold Up; rw [he']; exact hu
  rw [r_deleted_iff, not_or]
  refine ⟨by rw [j_curve_α]; exact hk e rfl, ?_⟩
  exact hk (Γ.φ e) (j_cellOf_φ _ _)

theorem p_corner_kept' {r : Γ.Cell → ZMod 2} {e : D} (hu : Γ.Up (Γ.cellOf e))
    (hr : r (Γ.cellOf e) = 1) : ¬ Γ.Deleted (Γ.pRem r) (Γ.crossingOf e) := by
  have h1 : Γ.cellOf (Γ.φ⁻¹ e) = Γ.cellOf e := Γ.ld_cellOf_φinv e
  have h2 := p_corner_kept (r := r) (e := Γ.φ⁻¹ e) (by rw [h1]; exact hu) (by rw [h1]; exact hr)
  rwa [Γ.ld_φinv_apply, j_α_α, Γ.ld_crossingOf_σinv] at h2

namespace PSurg

variable {γ δ : Fin n} {z : D} {tk tl tA tB tj tE m : ℕ} {rγ r : Γ.Cell → ZMod 2}
  {Lγ Lid : Finset D} {a0 b0 : D}
  (H : PSurg Γ γ δ z tk tl tA tB tj tE m rγ r Lγ Lid a0 b0)
include H

theorem δ_kept : δ ∉ Γ.pRem r := by
  have hl : a0 ∈ Lid := by
    rw [H.ha0]
    exact (H.cR.lidσ tj (by have := H.hP; have := H.tjAB; omega)).2
      (by rcases H.hj with h | h <;> [exact Or.inl h.1; exact Or.inr h.1])
  have e := H.cR.cut a0 H.a0A.1
  rw [if_pos hl] at e
  intro hm
  rcases no_z2_cases (r (Γ.cellOf a0)) with h | h
  · rw [h, zero_add] at e
    exact (p_mem_rem.1 hm).2 ⟨Γ.α a0, by rw [j_curve_α, H.hδ], ab_above_α H.a0A, e⟩
  · exact (p_mem_rem.1 hm).2 ⟨a0, H.hδ, H.a0A, h⟩

theorem γ_kept : γ ∉ Γ.pRem r := by
  have hl : b0 ∈ Lid := by
    rw [H.hb0]
    exact (H.cR.lidσ tE (by have := H.hP; have := H.tEAB; omega)).2
      (by rcases H.hj with h | h <;> [exact Or.inr h.2; exact Or.inl h.2])
  have e := H.cR.cut b0 H.b0A.1
  rw [if_pos hl] at e
  intro hm
  rcases no_z2_cases (r (Γ.cellOf b0)) with h | h
  · rw [h, zero_add] at e
    exact (p_mem_rem.1 hm).2 ⟨Γ.α b0, by rw [j_curve_α, H.hγb], ab_above_α H.b0A, e⟩
  · exact (p_mem_rem.1 hm).2 ⟨b0, H.hγb, H.b0A, h⟩

/-- The dart `α a0` (from `u` to `j`) survives the removal. -/
theorem keep_u : Γ.Keep (Γ.pRem r) (Γ.α a0) := by
  have hj : ¬ Γ.Deleted (Γ.pRem r) (Γ.crossingOf a0) := by
    rw [r_deleted_iff, not_or, H.hδ]
    refine ⟨H.δ_kept, ?_⟩
    rw [H.ha0, j_curve_σσ, (no_noC_sweep H.hz tj).1]; exact p_S_not_mem_rem
  have hu : ¬ Γ.Deleted (Γ.pRem r) (Γ.crossingOf (Γ.α a0)) := by
    rintro ⟨c, hc, hon⟩
    unfold OnCurve at hon
    rw [H.curves_u, mem_insert, mem_singleton] at hon
    rcases hon with rfl | rfl
    · exact H.δ_kept hc
    · exact H.γ_kept hc
  have hs : ¬ Γ.Deleted (Γ.pRem r) (Γ.crossingOf (Γ.noC z tj)) := by
    rw [← j_crossingOf_σ, ← H.ha0]; exact hj
  have ha : Γ.Keep (Γ.pRem r) a0 := by
    rw [H.ha0]; exact r_keep_σ (r_keep_S (no_noC_sweep H.hz tj).1 hs)
  exact r_keep_of_eqvGen ha (Relation.EqvGen.rel _ _ ⟨hj, hu, Or.inr ⟨a0,
    ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), by rw [pow_zero, Perm.one_apply]⟩, rfl⟩⟩)

/-- A finite edge of `K` is a finite edge of `Γ` with the same cell above it. -/
theorem cell_transfer (X : (Γ.pRedir H.hz tA tB).Removal (Γ.pRem r)) {d' : X.D'}
    (hd' : X.Γ'.IsFinSeg d') :
    Γ.IsFinSeg (X.ι d') ∧ (X.Γ'.upperCell d').size = (Γ.upperCell (X.ι d')).size := by
  have hP := H.hP
  have hAB := H.cR.hlt
  have hσa' : X.Γ'.Above (X.Γ'.σ d') :=
    ⟨c_curve_σ_ne_S hd'.1.1, by unfold Up; rw [j_cellOf_σ]; exact hd'.1.2⟩
  have hσa : Γ.Above (Γ.σ (X.ι d')) := by
    have := Removal.r_above X hσa'
    rw [X.isRemoval.σ] at this
    exact this
  have hsw : Γ.IsSweepDart (X.ι d') :=
    ⟨by have := X.isRemoval.curve d'; rw [hd'.1.1, X.isRemoval.S] at this; exact this.symm,
      by unfold Up; rw [← j_cellOf_σ]; exact hσa.2⟩
  obtain ⟨t, ht, hte⟩ := no_noC_surj H.hz hsw
  -- the edge starts at a vertex `tA ≤ t ≤ tB` of `(Γ.pRedir H.hz tA tB)`
  have hfin := e_finSeg_fin hd'
  have hf1 : (Γ.pRedir H.hz tA tB).IsFinVertex ((Γ.pRedir H.hz tA tB).crossingOf (X.ι d')) := (Removal.r_finVertex X _).1 hfin.1
  rw [← hte] at hf1
  have htAB := (p_redir_fin H.hz hAB.le (by omega) ht).1 hf1
  -- and `t ≠ tB`: the edge from `tB` is the start of the ∞-arc
  have htB : t ≠ tB := by
    intro htB0
    obtain ⟨z', hz'⟩ := Option.isSome_iff_exists.1 (X.Γ'.infStart_isSome ⟨d'⟩)
    obtain ⟨z0, hz0m, k, hk, hkz⟩ := X.isRemoval.infStart z' (by rw [hz']; rfl)
    have hz0 : z0 = Γ.noC z t := by
      have : (Γ.pRedir H.hz tA tB).infStart = some (Γ.noC z t) := by rw [htB0]; rfl
      rw [this, Option.mem_def, Option.some_inj] at hz0m
      exact hz0m.symm
    subst hz0
    have hdz : X.ι z' = X.ι d' :=
      c_piece_unique (Γ := (Γ.pRedir H.hz tA tB)) (Removal.r_keep X z').1 (Removal.r_keep X d').1 (i := k) (m := 0)
        hk (fun j hj => absurd hj (Nat.not_lt_zero _)) (by rw [hkz, hte, pow_zero, Perm.one_apply])
    have := X.isRemoval.inj hdz
    subst this
    exact hd'.2 ((no_mem_infArc (Γ := X.Γ') hz').2 ⟨0, Nat.zero_le _, rfl⟩)
  have htB' : t < tB := lt_of_le_of_ne htAB.2 htB
  -- the cell above the edge lies in the bounded component
  have hU : Γ.Up (Γ.cellOf (Γ.α (X.ι d'))) := hsw.2
  have hrU : r (Γ.cellOf (Γ.α (X.ι d'))) = 1 := by
    have := c_sweep H.cR ht
    unfold upperCell at this
    rw [hte, if_pos ⟨htAB.1, htB'⟩] at this
    exact this
  have hα : X.ι (X.Γ'.α d') = Γ.α (X.ι d') := by
    exact Removal.ab_ι_α X d' (p_corner_kept' hU hrU)
  have hpow : ∀ k : ℕ, X.ι ((X.Γ'.φ ^ k) (X.Γ'.α d')) = (Γ.φ ^ k) (X.ι (X.Γ'.α d')) := by
    apply Removal.ab_ι_φ_pow X
    intro k
    rw [hα]
    have hc : Γ.cellOf ((Γ.φ ^ k) (Γ.α (X.ι d'))) = Γ.cellOf (Γ.α (X.ι d')) := Γ.ld_cellOf_pow k _
    exact p_corner_kept (Γ := Γ) (e := (Γ.φ ^ k) (Γ.α (X.ι d'))) (by rw [hc]; exact hU)
      (by rw [hc]; exact hrU)
  refine ⟨⟨hsw, fun hm => ?_⟩, ?_⟩
  · rw [← hte] at hm
    have := (no_noC_arc H.hz ht).1 hm
    omega
  · unfold upperCell
    rw [Removal.ab_size_eq X _ hpow, hα]
    rfl

/-- **The surgery** (`doc/pca/sweep.md`, steps 3-4). -/
theorem surgery (hΓ : Γ.MinCE) {tO : ℕ} (hO : tO + Γ.infLen < period Γ.straight z)
    (hOout : tO < tA ∨ tB < tO) :
    ∃ (n' : ℕ) (K : Conf.{u} n'), SizeLT K.Γ Γ ∧ ¬ K.Γ.Terminal ∧
      (∀ d, ¬ K.Γ.EmptyHumpAt d) ∧ (∀ d, ¬ K.Γ.EmptyTriAt d) ∧
      (K.Γ.CanTakeLoop → ∃ α, Γ.Inside α γ) := by
  have hP := H.hP
  have hAB := H.cR.hlt
  obtain ⟨X⟩ := exists_removal (Γ := Γ.pRedir H.hz tA tB) (Γ.pRem r) p_S_not_mem_rem
  refine ⟨n, ⟨X.D', X.Γ'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- smaller: the other end of `γ` is no longer a vertex on the sweep
    exact Or.inl (lt_of_le_of_lt (Removal.r_numVertices_le X)
      (p_redir_numVertices H.hz hAB.le hP hO hOout))
  · -- not finished: `u` is a vertex above the sweep
    intro hT
    obtain ⟨d', hd'⟩ := (X.isRemoval.range _).2 H.keep_u
    apply hT.1 (X.Γ'.crossingOf d')
    refine ⟨fun hS => ?_, d', Orbit.mem_darts.2 rfl, ?_, ?_⟩
    · have := (Removal.r_onSweep X _).1 hS
      rw [Removal.r_rΨ_mk, hd'] at this
      exact H.u_not_S this
    · rw [X.isRemoval.curve, hd', X.isRemoval.S]
      exact (ab_above_α H.a0A).1
    · have := X.isRemoval.side d'
      rw [hd'] at this
      exact this.trans (ab_above_α H.a0A).2
  · rintro d' ⟨hfs, hsz⟩
    obtain ⟨hfs', hsz'⟩ := H.cell_transfer X hfs
    exact hΓ.1.2 (Or.inl ⟨_, hfs', by rw [← hsz', hsz]⟩)
  · rintro d' ⟨hfs, hsz⟩
    obtain ⟨hfs', hsz'⟩ := H.cell_transfer X hfs
    exact hΓ.1.2 (Or.inr (Or.inl ⟨_, hfs', by rw [← hsz', hsz]⟩))
  · rintro ⟨d, e, hd, he, hcS, hnm⟩
    have hce := Orbit.mem_darts.1 he
    have hea : X.Γ'.Above e :=
      ⟨hcS, by unfold Up; rw [show X.Γ'.cellOf e = _ from hce]; exact hd.2⟩
    obtain ⟨hp, hR, hiff⟩ := X.meetsSweep_iff ⟨hcS, e, rfl, hea⟩
    have hcS' : X.Γ'.curve e ≠ Γ.S := hp.1
    rcases H.meets (fun c hc => hΓ.lemma_3_4 hc) hcS' hR with ⟨t, ht1, ht2, hon⟩ | hins
    · exfalso
      apply hnm
      apply hiff.2
      refine ⟨Γ.crossingOf (Γ.noC z t), ?_, hon⟩
      exact (p_redir_fin H.hz hAB.le (by omega) (t := t) (by omega)).2 ⟨ht1, ht2⟩
    · exact ⟨_, hins⟩

end PSurg

end SConf

end Pca.Sweep
