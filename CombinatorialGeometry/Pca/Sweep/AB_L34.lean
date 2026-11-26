/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package B (Lemma 3.4), the core

A stuck configuration `Γ` with a present curve `γ` that does not meet the sweep. Since no loop
can be taken, `γ` has no dart on a cell above an edge of `S` (`ab_inv`). Then `γ` does not cross
`S` at all (`ab_noSγ`), every dart of `γ` lies above `S` (`ab_side_γ`), and the cells above the
edges of `S` have no corner on `γ`. After removing `γ` (`X : Γ.Removal {γ}`):

* the cell above a sweep dart of `Γ − γ` is the cell above the corresponding sweep dart of `Γ`
  (`ab_corr`), so an empty hump, an empty triangle or a loop of `Γ − γ` is one of `Γ`;
* if `Γ − γ` is finished, it has no vertex above the sweep, so every cell above `S` of `Γ − γ` is
  the cell above a sweep dart; then the kept darts are closed under `α` (a kept dart before a
  crossing on `γ` would lie on such a cell, with a dart of `γ`), so every dart is kept
  (connectivity), also those of `γ`: a contradiction.

So `Γ − γ` is stuck (`ab_l34_core`).
-/
import Pca.Sweep.AB_Basic

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- With no vertex above the sweep, every cell above `S` is the cell above a sweep dart. -/
theorem ab_up_cell (hno : ∀ x, ¬ Γ.IsAboveVertex x) {a : D} (ha : Γ.Up (Γ.cellOf a)) :
    ∃ s, Γ.IsSweepDart s ∧ a ∈ (Γ.upperCell s).darts := by
  by_cases h1 : Γ.curve a = Γ.S
  · refine ⟨Γ.α a, ⟨by rw [j_curve_α]; exact h1, by rw [j_α_α]; exact ha⟩, ?_⟩
    unfold upperCell; rw [j_α_α]; exact Orbit.mem_darts.2 rfl
  by_cases h2 : Γ.curve (Γ.φ a) = Γ.S
  · refine ⟨Γ.α (Γ.φ a), ⟨by rw [j_curve_α]; exact h2, by rw [j_α_α, j_cellOf_φ]; exact ha⟩, ?_⟩
    unfold upperCell; rw [j_α_α]; exact Orbit.mem_darts.2 (Γ.j_cellOf_φ a).symm
  exfalso
  refine hno (Γ.crossingOf (Γ.φ a)) ⟨?_, Γ.φ a, ab_self_mem_darts _, h2, ?_⟩
  · change Γ.S ∉ Γ.curves _
    rw [j_curves_crossingOf, mem_insert, mem_singleton, j_φ_apply, j_curve_σσ, j_curve_α]
    rintro (h | h)
    · exact h2 (by rw [j_φ_apply]; exact h.symm)
    · exact h1 h.symm
  · unfold Up; rw [j_cellOf_φ]; exact ha

section Core

variable {γ : Fin n} (hNP : ¬ Γ.Progress) (hms : ¬ Γ.MeetsSweep γ) (hγS : γ ≠ Γ.S)

include hNP hms hγS

/-- `γ` is invisible from `S`. -/
theorem ab_inv {d e : D} (hd : Γ.IsSweepDart d) (he : e ∈ (Γ.upperCell d).darts) :
    Γ.curve e ≠ γ := by
  intro hc
  exact hNP (Or.inr (Or.inr ⟨d, e, hd, he, by rw [hc]; exact hγS, by rw [hc]; exact hms⟩))

/-- `γ` does not cross `S`. -/
theorem ab_noSγ {y : D} (h1 : Γ.curve y = γ) (h2 : Γ.curve (Γ.σ y) = Γ.S) : False := by
  have hx : Γ.OnSweep (Γ.crossingOf y) := by
    change Γ.S ∈ _; rw [← h2]; exact ab_mem_curves_σ y
  obtain ⟨y', hy', hc, -, hsw, h4⟩ := ab_up_dart hx (by rw [← h1]; exact ab_mem_curves_self y) hγS
  refine ab_inv hNP hms hγS hsw (e := y') ?_ hc
  refine Orbit.mem_darts.2 ?_
  change Γ.cellOf y' = Γ.cellOf (Γ.α _)
  rw [← j_cellOf_σ, h4]

/-- A dart of `S` keeps its crossing when `γ` is removed. -/
theorem ab_rK_S {y : D} (hy : Γ.curve y = Γ.S) : Γ.rK {γ} y := by
  intro hdel
  rcases (Γ.r_deleted_iff {γ} y).1 hdel with h | h
  · exact hγS ((mem_singleton.1 h).symm.trans hy)
  · have h' : Γ.curve (Γ.σ (Γ.σ (Γ.σ y))) = γ := by rw [j_curve_σσ]; exact mem_singleton.1 h
    exact ab_noSγ hNP hms hγS h' (by rw [Γ.j_σ4]; exact hy)

/-- No dart of a cell above an edge of `S` ends at a crossing on `γ`. -/
theorem ab_rK_α {d a : D} (hd : Γ.IsSweepDart d) (ha : a ∈ (Γ.upperCell d).darts) :
    Γ.rK {γ} (Γ.α a) := by
  intro hdel
  rcases (Γ.r_deleted_iff {γ} (Γ.α a)).1 hdel with h | h
  · rw [j_curve_α] at h
    exact ab_inv hNP hms hγS hd ha (mem_singleton.1 h)
  · refine ab_inv hNP hms hγS hd (e := Γ.φ a) ?_ (mem_singleton.1 h)
    exact Orbit.mem_darts.2 ((Γ.j_cellOf_φ a).trans (ab_cellOf_eq_of_mem ha))

/-- Every dart of `γ` lies above `S`. -/
theorem ab_side_γ {d0 : D} (hd0 : Γ.curve d0 = γ) (hA : Γ.Above d0) {y : D}
    (hy : Γ.curve y = γ) : Γ.Up (Γ.cellOf y) := by
  have hpow : ∀ k : ℕ, Γ.Up (Γ.cellOf ((Γ.straight ^ k) d0)) := by
    intro k
    induction k with
    | zero => exact hA.2
    | succ k ih =>
      unfold Up at ih ⊢
      rw [no_pow_succ, no_side_straight, ih, if_neg, add_zero]
      intro h
      refine ab_noSγ hNP hms hγS (y := Γ.α ((Γ.straight ^ k) d0)) ?_ h
      rw [j_curve_α, no_curve_pow, hd0]
  have hσ : ∀ w, Γ.curve w = γ → Γ.curve (Γ.σ w) ≠ Γ.S :=
    fun w hw h => ab_noSγ hNP hms hγS hw h
  rcases Γ.isSConf.straight d0 y (hd0.trans hy.symm) with h | h
  · obtain ⟨k, -, rfl⟩ := no_exists_idx h
    exact hpow k
  · obtain ⟨k, -, hk⟩ := no_exists_idx h
    have := hpow k
    unfold Up at this ⊢
    rw [hk, no_side_σ, if_neg (hσ y hy), add_zero, no_side_σ, if_neg (by rw [hy]; exact hγS),
      add_zero] at this
    exact this

variable (X : Γ.Removal {γ})

/-- The cell above a sweep dart of `Γ − γ` is the cell above the corresponding sweep dart of
`Γ`. -/
theorem ab_corr {s' : X.D'} (hs' : X.Γ'.IsSweepDart s') :
    Γ.IsSweepDart (X.ι s') ∧ X.ι (X.Γ'.α s') = Γ.α (X.ι s') ∧
      ∀ k : ℕ, X.ι ((X.Γ'.φ ^ k) (X.Γ'.α s')) = (Γ.φ ^ k) (Γ.α (X.ι s')) := by
  have hcur : Γ.curve (X.ι s') = Γ.S := by
    rw [← X.isRemoval.curve, ← X.isRemoval.S]; exact hs'.1
  have hα : X.ι (X.Γ'.α s') = Γ.α (X.ι s') :=
    X.ab_ι_α s' (ab_rK_S hNP hms hγS (by rw [j_curve_α]; exact hcur))
  have hsw : Γ.IsSweepDart (X.ι s') := by
    refine ⟨hcur, ?_⟩
    have := X.isRemoval.side (X.Γ'.α s')
    rw [hα] at this
    exact this.symm.trans hs'.2
  refine ⟨hsw, hα, fun k => ?_⟩
  rw [X.ab_ι_φ_pow (X.Γ'.α s') (fun j => by
    rw [hα]; exact ab_rK_α hNP hms hγS hsw (ab_mem_cell_pow _ j)), hα]

/-- The upper cells of `Γ − γ` and `Γ` at corresponding sweep darts have the same size. -/
theorem ab_size_upper {s' : X.D'} (hs' : X.Γ'.IsSweepDart s') :
    (X.Γ'.upperCell s').size = (Γ.upperCell (X.ι s')).size := by
  obtain ⟨-, hα, hpow⟩ := ab_corr hNP hms hγS X hs'
  unfold upperCell
  rw [X.ab_size_eq (X.Γ'.α s') (fun k => by rw [hpow, hα]), hα]

/-- A finite edge of `Γ − γ` is a finite edge of `Γ`. -/
theorem ab_finSeg {d' : X.D'} (hd : X.Γ'.IsFinSeg d') : Γ.IsFinSeg (X.ι d') := by
  obtain ⟨hsw, -, -⟩ := ab_corr hNP hms hγS X hd.1
  refine ⟨hsw, fun hmem => hd.2 ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z := by
    unfold infArc arcOf at hmem
    cases h : Γ.infStart with
    | none => rw [h] at hmem; simp at hmem
    | some z => exact ⟨z, rfl⟩
  rcases ab_inf_of_arc hz hmem with h | h
  · obtain ⟨z', hz'⟩ : ∃ z', X.Γ'.infStart = some z' :=
      Option.isSome_iff_exists.1 (X.Γ'.infStart_isSome ⟨d'⟩)
    obtain ⟨z0, hz0, hp⟩ := X.isRemoval.infStart z' (by rw [hz']; rfl)
    have hz0' : z0 = z := by rw [hz] at hz0; exact (Option.some_inj.1 hz0).symm
    subst hz0'
    have hz'S : Γ.curve (X.ι z') = Γ.S := by
      rw [← X.isRemoval.curve, ← X.isRemoval.S]; exact (no_z_sweep hz').1
    obtain ⟨k, hk, hke⟩ := (Γ.r_piece_iff {γ}).1 hp
    have hk0 : k = 0 := by
      rcases k with _ | k
      · rfl
      · exact absurd (ab_rK_S hNP hms hγS (by rw [j_curve_α]; exact hz'S)) (hk 0 (by omega))
    subst hk0
    rw [pow_zero, Perm.one_apply] at hke
    have : d' = z' := X.isRemoval.inj (h.trans hke.symm)
    rw [this]
    exact (no_mem_infArc hz').2 ⟨0, Nat.zero_le _, rfl⟩
  · exact ab_arc_of_inf hd.1 ((X.isRemoval.infVertex d').2 h)

/-- **Core of Lemma 3.4**: removing an invisible curve from a stuck configuration leaves a
stuck configuration. -/
theorem ab_l34_core {d0 : D} (hd0 : Γ.curve d0 = γ) (hA : Γ.Above d0) : X.Γ'.Stuck := by
  refine ⟨fun hT => ?_, fun hP => ?_⟩
  · -- finished: every dart would be kept
    have hkα : ∀ a, Γ.Keep {γ} a → Γ.rK {γ} (Γ.α a) := by
      intro a ha
      by_contra hdel
      obtain ⟨a', rfl⟩ := (X.isRemoval.range a).2 ha
      have hφ : Γ.curve (Γ.φ (X.ι a')) = γ := by
        rcases (Γ.r_deleted_iff {γ} _).1 (not_not.1 hdel) with h | h
        · rw [j_curve_α] at h; exact absurd h (Γ.r_curve_not_mem {γ} ha.1)
        · exact mem_singleton.1 h
      have hup : Γ.Up (Γ.cellOf (X.ι a')) := by
        rw [← j_cellOf_φ]; exact ab_side_γ hNP hms hγS hd0 hA hφ
      have hup' : X.Γ'.Up (X.Γ'.cellOf a') := (X.isRemoval.side a').trans hup
      obtain ⟨s', hs', hmem⟩ := ab_up_cell hT.1 hup'
      obtain ⟨k, hk⟩ := ab_exists_pow_of_mem_cell hmem
      obtain ⟨hsw, -, hpow⟩ := ab_corr hNP hms hγS X hs'
      have he : X.ι a' = (Γ.φ ^ k) (Γ.α (X.ι s')) := by rw [← hk, hpow]
      refine ab_inv hNP hms hγS hsw (e := Γ.φ (X.ι a')) ?_ hφ
      rw [he, ← Perm.mul_apply, ← pow_succ']
      exact ab_mem_cell_pow _ _
    have hfw : ∀ a, Γ.Keep {γ} a → Γ.Keep {γ} (Γ.α a) := fun a ha =>
      r_keep_of_eqvGen ha (.rel _ _ ⟨ha.1, hkα a ha,
        Or.inr ⟨a, ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i), by rw [pow_zero,
          Perm.one_apply]⟩, rfl⟩⟩)
    obtain ⟨e0, he0⟩ := Γ.isSConf.S_mem ⟨d0⟩
    have hk0 : Γ.Keep {γ} e0 := r_keep_S he0 (ab_rK_S hNP hms hγS he0)
    have := Γ.j_eqvGen_rec (P := fun a b => Γ.Keep {γ} a ↔ Γ.Keep {γ} b)
      (fun a => (r_keep_σ_iff a).symm)
      (fun a => ⟨hfw a, fun h => by have := hfw _ h; rwa [j_α_α] at this⟩)
      (fun _ => Iff.rfl) (fun _ _ h => h.symm) (fun _ _ _ h1 h2 => h1.trans h2) e0 d0
    have hkd := (this.1 hk0).1
    exact Γ.r_curve_not_mem {γ} hkd (by rw [hd0]; exact mem_singleton_self γ)
  · -- an operation of `Γ − γ` is one of `Γ`
    rcases hP with ⟨d', hf, hsz⟩ | ⟨d', hf, hsz⟩ | ⟨d', e', hd', he', hcS, hnm⟩
    · exact hNP (Or.inl ⟨X.ι d', ab_finSeg hNP hms hγS X hf,
        by rw [← ab_size_upper hNP hms hγS X hf.1]; exact hsz⟩)
    · exact hNP (Or.inr (Or.inl ⟨X.ι d', ab_finSeg hNP hms hγS X hf,
        by rw [← ab_size_upper hNP hms hγS X hf.1]; exact hsz⟩))
    · obtain ⟨hsw, -, hpow⟩ := ab_corr hNP hms hγS X hd'
      obtain ⟨k, hk⟩ := ab_exists_pow_of_mem_cell he'
      have hpres : X.Γ'.Present (X.Γ'.curve e') :=
        ⟨hcS, e', rfl, hcS, by
          unfold Up; rw [ab_cellOf_eq_of_mem he']; exact hd'.2⟩
      have hiff := ((X.meetsSweep_iff hpres).2.2)
      refine hNP (Or.inr (Or.inr ⟨X.ι d', X.ι e', hsw, ?_, ?_, ?_⟩))
      · rw [← hk, hpow]; exact ab_mem_cell_pow _ _
      · rw [← X.isRemoval.curve, ← X.isRemoval.S]; exact hcS
      · rw [← X.isRemoval.curve]; exact fun h => hnm (hiff.2 h)

end Core

end SConf

end Pca.Sweep
