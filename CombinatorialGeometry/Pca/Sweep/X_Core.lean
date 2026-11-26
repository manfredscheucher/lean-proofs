/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Reflex triangles, case (i): SH's argument of Lemma 3.6 with generalised region data

Package C (`C_Core.lean`, `C_Trans.lean`) runs SH's argument (p. 319) against `CLid`, whose field
`lidR` says that the lid curves leave the region after the lid. For a **reflex** triangle this is
false: both triangle curves continue into the region after the apex (`doc/pca/sweep.md`). Here
`lidR` is replaced by what the argument really uses (`XLid`):

* `kept`: every dart above `S` off the lid of a kept curve (a curve with a dart inside the region
  off the lid, i.e. not in `cR`) lies inside;
* `lidK`: the curves through the crossings of the lid are `S` or kept;
* `lidα`: the lid is closed under `α`.

`x_core`: if some present curve is removed (`cR` contains a present curve) and the curve of the
lid dart at `k` is kept, a minimal counterexample is contradicted, exactly as in `c_core`.
-/
import Pca.Sweep.C_Trans

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- Region data for SH's argument when the lid curves may continue inside (see module doc). -/
structure XLid (Γ : SConf n D) (z : D) (tk tl : ℕ) (r : Γ.Cell → ZMod 2) (Lid : Finset D) :
    Prop extends CCut Γ z tk tl r Lid where
  above : ∀ y ∈ Lid, Γ.Above y
  lidα : ∀ y ∈ Lid, Γ.α y ∈ Lid
  kept : ∀ w, Γ.Above w → w ∉ Lid → Γ.curve w ∉ Γ.cR r Lid → r (Γ.cellOf w) = 1
  lidK : ∀ y ∈ Lid, ∀ w, Γ.crossingOf w = Γ.crossingOf y →
    Γ.curve w = Γ.S ∨ Γ.curve w ∉ Γ.cR r Lid

/-! ## Walking along a curve that is not a lid curve (only `lidX` of `CLid` is used) -/

section Walk

variable {z : D} {tk tl : ℕ} {r : Γ.Cell → ZMod 2} {Lid : Finset D}

/-- `c_walk` with only the crossing condition of the lid. -/
theorem x_walk (h : CCut Γ z tk tl r Lid)
    (lidX : ∀ y ∈ Lid, ∀ w, Γ.crossingOf w = Γ.crossingOf y →
      Γ.curve w = Γ.S ∨ ∃ y' ∈ Lid, Γ.curve y' = Γ.curve w)
    {γ : Fin n} (hγ : ∀ y ∈ Lid, Γ.curve y ≠ γ)
    {p : D} (hp : Γ.curve p = γ) {k : ℕ} (hk : ∀ i ≤ k, Γ.Above ((Γ.straight ^ i) p)) :
    r (Γ.cellOf ((Γ.straight ^ k) p)) = r (Γ.cellOf p) := by
  refine c_walk_of h hk (fun i hi hl => ?_)
  set y := (Γ.straight ^ i) p
  have hy : Γ.Above y := hk i (by omega)
  have hcy : Γ.curve y = γ := by rw [no_curve_pow]; exact hp
  rcases lidX _ hl (Γ.α y) (j_crossingOf_σ Γ _).symm with hS | ⟨y', hy', hc⟩
  · rw [j_curve_α] at hS; exact hy.1 hS
  · rw [j_curve_α, hcy] at hc; exact hγ y' hy' hc

/-- `c_kept` for a curve that is not a lid curve: all its darts above `S` are inside. -/
theorem x_kept_free (h : CCut Γ z tk tl r Lid)
    (lidX : ∀ y ∈ Lid, ∀ w, Γ.crossingOf w = Γ.crossingOf y →
      Γ.curve w = Γ.S ∨ ∃ y' ∈ Lid, Γ.curve y' = Γ.curve w)
    {y0 : D} (hin : Γ.CIn r Lid y0) (hnl : ∀ y ∈ Lid, Γ.curve y ≠ Γ.curve y0) {w : D}
    (hw : Γ.curve w = Γ.curve y0) (hwa : Γ.Above w) : r (Γ.cellOf w) = 1 := by
  have hα : ∀ p, Γ.curve p = Γ.curve y0 → r (Γ.cellOf (Γ.α p)) = r (Γ.cellOf p) := by
    intro p hp
    have hpS : Γ.curve p ≠ Γ.S := hp ▸ hin.1.1
    have := h.cut p hpS
    rw [if_neg (fun hl => hnl p hl hp)] at this
    exact c_zmod2_eq_of_add this
  rcases upper_arc hin.1 hwa hw.symm with ⟨k, hk, hkw⟩ | ⟨k, hk, hkw⟩ | ⟨k, hk, hkw⟩ |
      ⟨k, hk, hkw⟩
  · have := x_walk h lidX hnl rfl hk
    rw [hkw] at this; rw [this]; exact hin.2.2
  · have := x_walk h lidX hnl hw hk
    rw [hkw] at this; rw [← this]; exact hin.2.2
  · have := x_walk h lidX hnl rfl hk
    rw [hkw, hα w hw] at this; rw [this]; exact hin.2.2
  · have := x_walk h lidX hnl (by rw [j_curve_α, hw]) hk
    rw [hkw, hα w hw] at this; rw [← this]; exact hin.2.2

end Walk

section Core

variable {z : D} {tk tl : ℕ} {r : Γ.Cell → ZMod 2} {Lid : Finset D}

/-- A kept curve meets `S` (off the lid ends) only between `k` and `l`. -/
theorem x_sweep_kept (h : XLid Γ z tk tl r Lid) {t : ℕ} (ht : t < period Γ.straight z)
    (hk : t ≠ tk) (hl : t ≠ tl) (hc : Γ.curve (Γ.σ (Γ.noC z t)) ∉ Γ.cR r Lid) :
    tk ≤ t ∧ t < tl := by
  have hs := no_noC_sweep h.hz t
  have hnl : Γ.σ (Γ.noC z t) ∉ Lid := fun hm => by
    rcases (h.lidσ t ht).1 hm with e | e
    · exact hk e
    · exact hl e
  have := h.kept _ (no_above_σ hs) hnl hc
  rw [j_cellOf_σ] at this
  have h2 := c_sweep h.toCCut ht
  unfold upperCell at h2
  rw [h2] at this
  split_ifs at this with hh
  · exact hh
  · exact absurd this (by decide)

/-- A segment of a kept curve above `S` does not end at a deleted crossing. -/
theorem x_end_kept (h : XLid Γ z tk tl r Lid) {p : D} (hp : Γ.Above p)
    (hγ : Γ.curve p ∉ Γ.cR r Lid) :
    ¬ Γ.Deleted (Γ.cR r Lid) (Γ.crossingOf (Γ.α p)) := by
  rw [r_deleted_iff, j_curve_α]
  rintro (hm | hm)
  · exact hγ hm
  · set q := Γ.σ (Γ.α p)
    have hqS : Γ.curve q ≠ Γ.S := (c_mem_cR.1 hm).1
    have hqx : Γ.crossingOf q = Γ.crossingOf (Γ.α p) := j_crossingOf_σ _ _
    by_cases hpl : p ∈ Lid
    · rcases h.lidK _ (h.lidα p hpl) q hqx with hS | hk
      · exact hqS hS
      · exact hk hm
    have hqa : Γ.Above q := ⟨hqS, by unfold Up; rw [j_cellOf_σ, j_α_α]; exact hp.2⟩
    have hqr : r (Γ.cellOf q) = 1 := by
      rw [j_cellOf_σ, j_α_α]; exact h.kept p hp hpl hγ
    by_cases hql : q ∈ Lid
    · rcases h.lidK q hql q rfl with hS | hk
      · exact hqS hS
      · exact hk hm
    · exact (c_mem_cR.1 hm).2 ⟨q, rfl, hqa, hql, hqr⟩

/-- A vertex strictly between `k` and `l` is not deleted (`c_inner_kept`, from the cut only). -/
theorem x_inner_kept (h : CCut Γ z tk tl r Lid) {t : ℕ} (h1 : tk < t) (h2 : t < tl) :
    ¬ Γ.Deleted (Γ.cR r Lid) (Γ.crossingOf (Γ.noC z t)) := by
  have hP := h.hfin
  have hs := no_noC_sweep h.hz t
  have hin : Γ.CIn r Lid (Γ.σ (Γ.noC z t)) := by
    refine ⟨no_above_σ hs, fun hl => ?_, ?_⟩
    · rcases (h.lidσ t (by omega)).1 hl with e | e <;> omega
    · rw [j_cellOf_σ]
      have := c_sweep h (t := t) (by omega)
      unfold upperCell at this
      rw [this, if_pos ⟨h1.le, h2⟩]
  rw [r_deleted_iff]
  rintro (hm | hm)
  · exact c_S_not_mem (hs.1 ▸ hm)
  · exact (c_mem_cR.1 hm).2 ⟨_, rfl, hin⟩

/-- `c_transfer` for `XLid`: an empty hump or triangle of `Γ − cR` above a finite edge is one of
`Γ`. -/
theorem x_transfer (h : XLid Γ z tk tl r Lid) (X : Γ.Removal (Γ.cR r Lid)) {d' : X.D'}
    (hd' : X.Γ'.IsFinSeg d')
    (hs : period X.Γ'.φ (X.Γ'.α d') = 2 ∨ period X.Γ'.φ (X.Γ'.α d') = 3) :
    Γ.IsFinSeg (X.ι d') ∧ period Γ.φ (Γ.α (X.ι d')) = period X.Γ'.φ (X.Γ'.α d') := by
  have hP := h.hfin
  have hlt := h.hlt
  have hσa' : X.Γ'.Above (X.Γ'.σ d') :=
    ⟨c_curve_σ_ne_S hd'.1.1, by unfold Up; rw [j_cellOf_σ]; exact hd'.1.2⟩
  have hσa : Γ.Above (Γ.σ (X.ι d')) := by
    rw [← X.isRemoval.σ]; exact Removal.r_above X hσa'
  have hσk : Γ.curve (Γ.σ (X.ι d')) ∉ Γ.cR r Lid := by
    rw [← X.isRemoval.σ]; exact Γ.r_curve_not_mem _ (Removal.r_keep X _).1
  have hsw : Γ.IsSweepDart (X.ι d') :=
    ⟨by rw [← X.isRemoval.curve, hd'.1.1, X.isRemoval.S], by
      unfold Up; rw [← j_cellOf_σ]; exact hσa.2⟩
  obtain ⟨t, ht, hte⟩ := no_noC_surj h.hz hsw
  -- the edge starts between `k` and `l`
  have htt : tk ≤ t ∧ t ≤ tl := by
    by_cases hk : t = tk
    · omega
    by_cases hl : t = tl
    · omega
    have := x_sweep_kept h ht hk hl (by rw [hte]; exact hσk)
    omega
  obtain ⟨e, ⟨k, hk, hke⟩, hne, hαe⟩ := X.isRemoval.α d'
  have hpc : ∀ i, (Γ.straight ^ i) (X.ι d') = Γ.noC z (i + t) := by
    intro i; rw [← hte]; unfold noC; rw [← no_pow_add]
  -- the joined edge does not run into the ∞-arc
  have hnw : ¬ (period Γ.straight z - Γ.infLen - 1 ≤ t + k) := by
    intro hwrap
    set i0 := period Γ.straight z - Γ.infLen - 1 - t
    have hz0 : (Γ.straight ^ i0) (X.ι d') = z := by
      rw [hpc, no_noC_eq, show i0 + t + (Γ.infLen + 1) = 0 + period Γ.straight z by omega,
        no_pow_period, pow_zero, Perm.one_apply]
    obtain ⟨z', hz'⟩ := Option.isSome_iff_exists.1 (X.Γ'.infStart_isSome ⟨d'⟩)
    obtain ⟨z0, hz0m, m, hm, hmz⟩ := X.isRemoval.infStart z' (by rw [hz']; rfl)
    rw [h.hz, Option.mem_def, Option.some_inj] at hz0m
    subst hz0m
    have hdz : X.ι d' = X.ι z' :=
      c_piece_unique (Removal.r_keep X d').1 (Removal.r_keep X z').1
        (fun j hj => hk j (by omega)) hm (hz0.trans hmz.symm)
    have := X.isRemoval.inj hdz
    subst this
    exact hd'.2 ((no_mem_infArc (Γ := X.Γ') hz').2 ⟨0, Nat.zero_le _, rfl⟩)
  have hlen : k + t + 1 < period Γ.straight z := by
    have := Nat.sub_le (period Γ.straight z) (Γ.infLen + 1)
    omega
  -- the end of the joined edge is a kept vertex
  have hend : ¬ Γ.Deleted (Γ.cR r Lid) (Γ.crossingOf (Γ.noC z (k + t + 1))) := by
    rw [← hke, hpc, ← no_crossingOf_α_straight, no_noC_straight] at hne
    exact hne
  have hendk : Γ.curve (Γ.σ (Γ.noC z (k + t + 1))) ∉ Γ.cR r Lid := by
    rw [r_deleted_iff, not_or] at hend
    exact hend.2
  have hk0 : k = 0 := by
    by_contra hk0
    have hdel1 := hk 0 (by omega)
    rw [pow_zero, Perm.one_apply, ← no_crossingOf_α_straight, ← hte, no_noC_straight] at hdel1
    by_cases ht1 : t + 1 < tl
    · exact x_inner_kept h.toCCut (by omega) ht1 hdel1
    · have := x_sweep_kept h hlen (by omega) (by omega) hendk
      omega
  subst hk0
  rw [pow_zero, Perm.one_apply] at hke
  subst hke
  -- the edge does not start at `l`
  have htl : t < tl := by
    by_contra hc
    have := x_sweep_kept h hlen (by omega) (by omega) hendk
    omega
  -- the cell above the edge, in `Γ'` and in `Γ`
  set x0 := X.Γ'.α d'
  have e0 : X.ι (X.Γ'.φ x0) = Γ.φ (X.ι x0) := by
    apply c_ιφ X
    rw [hαe, j_α_α]
    exact (Removal.r_keep X d').1
  have hx1 : X.Γ'.φ x0 = X.Γ'.σ d' := by rw [j_φ_apply, j_α_α]
  have e1 : X.ι (X.Γ'.φ (X.Γ'.φ x0)) = Γ.φ (X.ι (X.Γ'.φ x0)) := by
    apply c_ιφ X
    rw [hx1, X.isRemoval.σ]
    exact x_end_kept h hσa hσk
  have e2 : X.ι (X.Γ'.φ (X.Γ'.φ (X.Γ'.φ x0))) = Γ.φ (X.ι (X.Γ'.φ (X.Γ'.φ x0))) := by
    rcases hs with hs | hs
    · have h2 : X.Γ'.φ (X.Γ'.φ x0) = x0 := by
        have := iterate_period X.Γ'.φ x0
        rw [hs] at this
        exact this
      rw [h2]; exact e0
    · set x2 := X.Γ'.φ (X.Γ'.φ x0)
      have h3 : X.Γ'.φ x2 = x0 := by
        have := iterate_period X.Γ'.φ x0
        rw [hs] at this
        exact this
      have hx2S : X.Γ'.curve x2 ≠ X.Γ'.S := by
        intro hc
        have := c_curve_φ_ne (Γ := X.Γ') x2
        rw [h3, hc] at this
        apply this
        rw [j_curve_α]; exact hd'.1.1
      have hx2a : X.Γ'.Above x2 := ⟨hx2S, by
        unfold Up
        rw [show x2 = X.Γ'.φ (X.Γ'.φ x0) from rfl, j_cellOf_φ, j_cellOf_φ]
        exact hd'.1.2⟩
      apply c_ιφ X
      exact x_end_kept h (Removal.r_above X hx2a)
        (Γ.r_curve_not_mem _ (Removal.r_keep X x2).1)
  have hper : period Γ.φ (X.ι x0) = period X.Γ'.φ x0 := by
    apply c_period_eq _ _ _ X.isRemoval.inj
    intro j hj
    have hj3 : j ≤ 3 := by rcases hs with hs | hs <;> omega
    interval_cases j
    · rfl
    · simp only [Function.iterate_one]; exact e0
    · simp only [Function.iterate_succ_apply', Function.iterate_zero, id]
      rw [e1, e0]
    · simp only [Function.iterate_succ_apply', Function.iterate_zero, id]
      rw [e2, e1, e0]
  refine ⟨⟨hsw, fun hm => ?_⟩, ?_⟩
  · rw [← hte] at hm
    have := (no_noC_arc h.hz ht).1 hm
    omega
  · rw [← hαe]; exact hper

/-- **SH's argument of Lemma 3.6 for `XLid`** (case (i) of `doc/pca/sweep.md`): a present
curve is removed and the curve of the lid dart at `k` is kept. -/
theorem x_core (hΓ : Γ.MinCE) (h : XLid Γ z tk tl r Lid)
    (hpres : ∃ γ ∈ Γ.cR r Lid, Γ.Present γ)
    (hAk : Γ.curve (Γ.σ (Γ.noC z tk)) ∉ Γ.cR r Lid) : False := by
  have hP := h.hfin
  have hlt := h.hlt
  obtain ⟨X⟩ := exists_removal (Γ.cR r Lid) c_S_not_mem
  have hns := hΓ.lemma_3_3 hpres X
  by_cases hT : X.Γ'.Terminal
  · -- not finished: the curve `A` of the lid dart at `k` is kept and is no ray
    have hs := no_noC_sweep h.hz tk
    have hAa : Γ.Above (Γ.σ (Γ.noC z tk)) := no_above_σ hs
    have hnd : ¬ Γ.Deleted (Γ.cR r Lid) (Γ.crossingOf (Γ.noC z tk)) := by
      rw [r_deleted_iff]
      rintro (hm | hm)
      · exact c_S_not_mem (hs.1 ▸ hm)
      · exact hAk hm
    have hkeep : Γ.Keep (Γ.cR r Lid) (Γ.σ (Γ.noC z tk)) := r_keep_σ (r_keep_S hs.1 hnd)
    obtain ⟨y', hy'⟩ := (X.isRemoval.range _).2 hkeep
    have hpres' : X.Γ'.Present (Γ.curve (Γ.σ (Γ.noC z tk))) := by
      refine ⟨by rw [X.isRemoval.S]; exact hAa.1, y', by rw [X.isRemoval.curve, hy'],
        by rw [X.isRemoval.curve, hy', X.isRemoval.S]; exact hAa.1, ?_⟩
      show X.Γ'.side (Orbit.mk _ y') = 1
      rw [X.isRemoval.side, hy']
      exact hAa.2
    obtain ⟨-, x', hinf, hon⟩ := hT.2 _ hpres'
    rw [Removal.r_inf] at hinf
    unfold OnCurve at hon
    rw [Removal.r_curves_Ψ] at hon
    have hon' : Γ.OnSweep (Removal.rΨ X x') := by
      obtain ⟨z0, hz0, i, -, hx⟩ := hinf
      rw [h.hz, Option.mem_def, Option.some_inj] at hz0
      subst hz0
      change Γ.S ∈ _
      rw [← hx, j_curves_crossingOf, j_curve_α, no_curve_pow, (no_z_sweep h.hz).1]
      exact mem_insert_self _ _
    obtain ⟨t, ht, hxt⟩ := no_onSweep_noC h.hz hon'
    have hge := (no_noC_inner h.hz ht).1 (hxt ▸ hinf)
    rw [← hxt, j_curves_crossingOf, (no_noC_sweep h.hz t).1, mem_insert, mem_singleton] at hon
    rcases hon with hon | hon
    · exact hAa.1 hon
    · have := x_sweep_kept h ht (by omega) (by omega) (by rw [← hon]; exact hAk)
      omega
  · have hPr : X.Γ'.Progress := by
      by_contra hPr
      exact hns ⟨hT, hPr⟩
    rcases hPr with ⟨d', hd', hsz⟩ | ⟨d', hd', hsz⟩ | ⟨d, e, hd, he, hcS, hnm⟩
    · unfold upperCell at hsz
      rw [c_size] at hsz
      obtain ⟨hfs, hper⟩ := x_transfer h X hd' (Or.inl hsz)
      exact hΓ.1.2 (Or.inl ⟨_, hfs, by unfold upperCell; rw [c_size, hper, hsz]⟩)
    · unfold upperCell at hsz
      rw [c_size] at hsz
      obtain ⟨hfs, hper⟩ := x_transfer h X hd' (Or.inr hsz)
      exact hΓ.1.2 (Or.inr (Or.inl ⟨_, hfs, by unfold upperCell; rw [c_size, hper, hsz]⟩))
    · have hce := Orbit.mem_darts.1 he
      have hea : X.Γ'.Above e :=
        ⟨hcS, by unfold Up; rw [show X.Γ'.cellOf e = _ from hce]; exact hd.2⟩
      obtain ⟨hp, -, hiff⟩ := X.meetsSweep_iff ⟨hcS, e, rfl, hea⟩
      exact hnm (hiff.2 (hΓ.lemma_3_4 hp))

end Core

end SConf

end Pca.Sweep
