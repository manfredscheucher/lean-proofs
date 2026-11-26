/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package C: transfer from `Γ'` back to `Γ`, and the core contradiction of Lemma 3.6

`c_transfer`: an empty hump or triangle of `Γ' = Γ − cR` above a finite edge `d'` is a cell of `Γ`
above the finite edge `ι d'` (its segments pass no deleted crossing). `c_core`: SH's argument
(p. 319) with the region data `CLid` (`Pca/Sweep/C_Core.lean`), when some vertex lies strictly
between `k` and `l`.
-/
import Pca.Sweep.C_Core

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- The size of a cell is the period of `φ`. -/
theorem c_size (Γ : SConf n D) (x : D) : (Γ.cellOf x).size = period Γ.φ x := by
  unfold Orbit.size cellOf
  rw [Orbit.darts_mk, card_orbitFinset]

/-- An injective map commuting with two permutations along an orbit preserves its period. -/
theorem c_period_eq {D' : Type*} [Fintype D'] [DecidableEq D'] (f : Perm D) (f' : Perm D')
    (ι : D' → D) (hinj : Function.Injective ι) (x : D')
    (hcomm : ∀ j ≤ period f' x, ι ((f'^[j]) x) = (f^[j]) (ι x)) :
    period f (ι x) = period f' x := by
  show Nat.find (exists_iterate_eq f (ι x)) = period f' x
  rw [Nat.find_eq_iff]
  refine ⟨⟨period_pos f' x, ?_⟩, ?_⟩
  · rw [← hcomm _ le_rfl, iterate_period]
  · rintro m hm ⟨hm0, hfm⟩
    apply Nat.find_min (exists_iterate_eq f' x) (hm : m < Nat.find _)
    refine ⟨hm0, hinj ?_⟩
    rw [hcomm m hm.le]
    exact hfm

/-- Two joined segments with a common piece are equal. -/
theorem c_piece_unique {R : Finset (Fin n)} {a b : D} (ha : ¬ Γ.Deleted R (Γ.crossingOf a))
    (hb : ¬ Γ.Deleted R (Γ.crossingOf b)) {i m : ℕ}
    (hia : ∀ j < i, Γ.Deleted R (Γ.crossingOf (Γ.α ((Γ.straight ^ j) a))))
    (hmb : ∀ j < m, Γ.Deleted R (Γ.crossingOf (Γ.α ((Γ.straight ^ j) b))))
    (h : (Γ.straight ^ i) a = (Γ.straight ^ m) b) : a = b := by
  wlog him : i ≤ m generalizing a b i m
  · exact (this hb ha hmb hia h.symm (by omega)).symm
  have h2 : a = (Γ.straight ^ (m - i)) b := by
    rw [show m = i + (m - i) by omega, no_pow_add] at h
    exact (Γ.straight ^ i).injective h
  rcases Nat.eq_zero_or_pos (m - i) with h0 | h0
  · rw [h0, pow_zero, Perm.one_apply] at h2; exact h2
  · exfalso
    apply ha
    rw [h2, show m - i = (m - i - 1) + 1 by omega, no_pow_succ, no_crossingOf_α_straight]
    exact hmb _ (by omega)

section Removal

variable {R : Finset (Fin n)} (X : Γ.Removal R)

theorem c_ια {x' : X.D'} (h : ¬ Γ.Deleted R (Γ.crossingOf (Γ.α (X.ι x')))) :
    X.ι (X.Γ'.α x') = Γ.α (X.ι x') := by
  obtain ⟨e, ⟨k, hk, rfl⟩, -, he⟩ := X.isRemoval.α x'
  cases k with
  | zero => exact he
  | succ k => exact absurd (by simpa using hk 0 (Nat.succ_pos _)) h

theorem c_ιφ {x' : X.D'} (h : ¬ Γ.Deleted R (Γ.crossingOf (Γ.α (X.ι x')))) :
    X.ι (X.Γ'.φ x') = Γ.φ (X.ι x') := by
  rw [j_φ_apply, j_φ_apply, X.isRemoval.σ, c_ια X h]

end Removal

section Core

variable {z : D} {tk tl : ℕ} {r : Γ.Cell → ZMod 2} {Lid : Finset D}

/-- An empty hump or triangle of `Γ − cR` above a finite edge is one of `Γ`. -/
theorem c_transfer (h : CLid Γ z tk tl r Lid) (X : Γ.Removal (Γ.cR r Lid)) {d' : X.D'}
    (hd' : X.Γ'.IsFinSeg d')
    (hs : period X.Γ'.φ (X.Γ'.α d') = 2 ∨ period X.Γ'.φ (X.Γ'.α d') = 3) :
    Γ.IsFinSeg (X.ι d') ∧ period Γ.φ (Γ.α (X.ι d')) = period X.Γ'.φ (X.Γ'.α d') := by
  have hP := h.hfin
  -- the dart after the edge is above `S`, on a kept curve, so inside
  have hσa' : X.Γ'.Above (X.Γ'.σ d') :=
    ⟨c_curve_σ_ne_S hd'.1.1, by unfold Up; rw [j_cellOf_σ]; exact hd'.1.2⟩
  have hσa : Γ.Above (Γ.σ (X.ι d')) := by
    rw [← X.isRemoval.σ]; exact Removal.r_above X hσa'
  have hσk : Γ.curve (Γ.σ (X.ι d')) ∉ Γ.cR r Lid := by
    rw [← X.isRemoval.σ]; exact Γ.r_curve_not_mem _ (Removal.r_keep X _).1
  obtain ⟨y0, hy0, hin⟩ := c_witness hσk hσa.1
  have h1 := (c_kept h hin hy0.symm hσa).2
  rw [j_cellOf_σ] at h1
  have hsw : Γ.IsSweepDart (X.ι d') :=
    ⟨by rw [← X.isRemoval.curve, hd'.1.1, X.isRemoval.S], by unfold Up; rw [← j_cellOf_σ]; exact hσa.2⟩
  obtain ⟨t, ht, hte⟩ := no_noC_surj h.hz hsw
  have htt : tk ≤ t ∧ t < tl := by
    have := c_sweep h.toCCut ht
    unfold upperCell at this
    rw [hte, h1] at this
    split_ifs at this with hh
    · exact hh
    · exact absurd this (by decide)
  -- the edge of `d'` is one edge of `Γ`
  obtain ⟨e, ⟨k, hk, hke⟩, hne, hαe⟩ := X.isRemoval.α d'
  have hpc : ∀ i, (Γ.straight ^ i) (X.ι d') = Γ.noC z (i + t) := by
    intro i; rw [← hte]; unfold noC; rw [← no_pow_add]
  have hk0 : k = 0 := by
    by_contra hk0
    by_cases hwrap : period Γ.straight z - Γ.infLen - 1 ≤ t + k
    · -- the joined segment contains the start of the ∞-arc
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
    · push Not at hwrap
      have hdel1 := hk 0 (by omega)
      rw [pow_zero, Perm.one_apply, ← no_crossingOf_α_straight, ← hte, no_noC_straight] at hdel1
      by_cases ht1 : t + 1 < tl
      · exact (c_inner_kept h (by omega) ht1).2 hdel1
      · -- the joined segment ends at a kept vertex outside `[k, l]`
        rw [← hke, hpc, ← no_crossingOf_α_straight, no_noC_straight] at hne
        rw [r_deleted_iff, not_or] at hne
        have hs2 := no_noC_sweep h.hz (k + t + 1)
        obtain ⟨y1, hy1, hin1⟩ := c_witness hne.2 (no_above_σ hs2).1
        have hlt' : k + t + 1 < period Γ.straight z := by
          have := Nat.sub_le (period Γ.straight z) (Γ.infLen + 1)
          omega
        exact c_kept_sweep h hlt' (by omega) hin1 hy1.symm
  subst hk0
  rw [pow_zero, Perm.one_apply] at hke
  subst hke
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
    exact c_end_kept h hσa hσk
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
      exact c_end_kept h (Removal.r_above X hx2a)
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

/-- **Core of Lemma 3.6** (SH p. 319) for a region with a vertex strictly between its ends. -/
theorem c_core (hΓ : Γ.MinCE) (h : CLid Γ z tk tl r Lid) (h2 : tk + 1 < tl) : False := by
  have hP := h.hfin
  obtain ⟨X⟩ := exists_removal (Γ.cR r Lid) c_S_not_mem
  have hl0 : Γ.σ (Γ.noC z tk) ∈ Lid := (h.lidσ tk (by omega)).2 (Or.inl rfl)
  have hpres : ∃ γ ∈ Γ.cR r Lid, Γ.Present γ :=
    ⟨Γ.curve (Γ.σ (Γ.noC z tk)),
      c_mem_cR.2 ⟨(h.above _ hl0).1, fun ⟨_, hw, hin⟩ => c_not_lid h hin _ hl0 hw.symm⟩,
      (h.above _ hl0).1, _, rfl, h.above _ hl0⟩
  have hns := hΓ.lemma_3_3 hpres X
  by_cases hT : X.Γ'.Terminal
  · -- not finished: a curve with a vertex strictly between `k` and `l` is no ray
    obtain ⟨hin1, hnd1⟩ := c_inner_kept h (t := tk + 1) (by omega) h2
    have hkeep : Γ.Keep (Γ.cR r Lid) (Γ.σ (Γ.noC z (tk + 1))) :=
      r_keep_σ (r_keep_S (no_noC_sweep h.hz _).1 hnd1)
    obtain ⟨y', hy'⟩ := (X.isRemoval.range _).2 hkeep
    have hpres' : X.Γ'.Present (Γ.curve (Γ.σ (Γ.noC z (tk + 1)))) := by
      refine ⟨by rw [X.isRemoval.S]; exact hin1.1.1, y', by rw [X.isRemoval.curve, hy'],
        by rw [X.isRemoval.curve, hy', X.isRemoval.S]; exact hin1.1.1, ?_⟩
      show X.Γ'.side (Orbit.mk _ y') = 1
      rw [X.isRemoval.side, hy']
      exact hin1.1.2
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
    · exact hin1.1.1 hon
    · exact c_kept_sweep h ht (by omega) hin1 hon.symm
  · have hPr : X.Γ'.Progress := by
      by_contra hPr
      exact hns ⟨hT, hPr⟩
    rcases hPr with ⟨d', hd', hsz⟩ | ⟨d', hd', hsz⟩ | ⟨d, e, hd, he, hcS, hnm⟩
    · unfold upperCell at hsz
      rw [c_size] at hsz
      obtain ⟨hfs, hper⟩ := c_transfer h X hd' (Or.inl hsz)
      exact hΓ.1.2 (Or.inl ⟨_, hfs, by unfold upperCell; rw [c_size, hper, hsz]⟩)
    · unfold upperCell at hsz
      rw [c_size] at hsz
      obtain ⟨hfs, hper⟩ := c_transfer h X hd' (Or.inr hsz)
      exact hΓ.1.2 (Or.inr (Or.inl ⟨_, hfs, by unfold upperCell; rw [c_size, hper, hsz]⟩))
    · -- taking a loop: Lemma 3.4
      have hce := Orbit.mem_darts.1 he
      have hea : X.Γ'.Above e := ⟨hcS, by unfold Up; rw [show X.Γ'.cellOf e = _ from hce]; exact hd.2⟩
      obtain ⟨hp, -, hiff⟩ := X.meetsSweep_iff ⟨hcS, e, rfl, hea⟩
      exact hnm (hiff.2 (hΓ.lemma_3_4 hp))

end Core

end SConf

end Pca.Sweep
