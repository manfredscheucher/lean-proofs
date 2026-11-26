/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.8 (p. 319), graph language (package F)

"LEMMA 3.8. The removal of a curve `γ(k)` cannot leave a hump.
PROOF. Suppose that the arrangement of `Γ − {γ(k)}` contains the hump `⟨i, j⟩`. Consider the
arrangement `Γ'` with only this hump removed: `Γ' = Γ − {γ(i)}`. By Lemma 3.3, the sweep can make
progress in `Γ'`. But `γ(i)` intersects only `γ(k)`; therefore, in `Γ'`, the curve `γ(k)`
contributes an edge to an empty hump or triangle; let `⟨k, v⟩` be that edge. In the original
arrangement `Γ`, however, `γ(i)` intersects `γ(k)` at some vertex `u` between `k` and `v` as shown
in Figure 6. Thus, `Δ(i, u, k)` is a triangle in `Γ`, contradicting Lemma 3.6."

"Hump" is an empty hump (a digon cell above a finite edge of `Γ − γ(k)`). Graph language: the
hump curve `γ(i)` of `Γ − γ(k)` has all its vertices above the sweep on `γ(k)` in `Γ` (its upper
arc is the hump segment of `Γ − γ(k)`, `upper_arc`); the second removal is `Removal {γ(i)}`.

Proof in graph language (uses Lemmas 3.3, 3.4, 3.6 (with reflex triangles, `Reflex.lean`) and G1). Let `h₀` be the
hump dart of `Γ − γ` seen in `Γ` (from vertex `i`), `β` its curve. The joined segment of `h₀` in
`Γ − γ` is `h₀, straight h₀, …, straight^L h₀` in `Γ`, ending at vertex `j` as `α hb`; by
`no_upper_arc` this walk is the whole part of `β` above `S`, its inner crossings `u_t` are crossings
with `γ` (deleted), and `L ≤ 2` (two-intersection property). So every crossing of `β` above `S` is
adjacent along `β` to `i` (via `h₀`) or to `j` (via `hb`) (`f_hit`: a segment from a vertex on the
sweep ending on `β` above `S` forms a triangle with that piece of `β`, Lemma 3.6). Now remove `β`
(SH: "consider the arrangement `Γ'` with only this hump removed"): by Lemmas 3.3, G1 and 3.4 it has
an empty hump or empty triangle. Its legs start at vertices on the sweep; if a leg passes a deleted
crossing (one on `β`), its first piece in `Γ` ends on `β` above `S` (SH: "`γ(i)` intersects
`γ(k)` at some vertex `u` between `k` and `v`"), a triangle by `f_hit`; otherwise the legs are
segments of `Γ`, and the hump / triangle of `Γ − β` is a hump / triangle of `Γ`, again excluded by
Lemma 3.6.
-/

import Pca.Sweep.L37
import Pca.Sweep.F_Pos
import Pca.Sweep.Reflex

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- The upper arc of the hump curve `β = curve h₀` of `Γ − γ`, seen in `Γ`: it runs from the
vertex `i` (dart `h₀`) to the vertex `j` (arriving as `α hb`) in `L ≤ 2` steps, and it is all of
`β` above the sweep. -/
private structure f_Beta (Γ : SConf n D) (h₀ hb : D) (L : ℕ) : Prop where
  a0 : Γ.Above h₀
  ab : Γ.Above hb
  curve : Γ.curve hb = Γ.curve h₀
  f0 : Γ.IsFinVertex (Γ.crossingOf h₀)
  fb : Γ.IsFinVertex (Γ.crossingOf hb)
  hL : (Γ.straight ^ L) h₀ = Γ.α hb
  L2 : L ≤ 2
  cover : ∀ y, Γ.Above y → Γ.curve y = Γ.curve h₀ →
    ∃ q ≤ L, (Γ.straight ^ q) h₀ = y ∨ (Γ.straight ^ q) h₀ = Γ.α y

/-- The hump of `Γ − γ` gives the upper arc of its curve in `Γ` ("`γ(i)` intersects only
`γ(k)`": its inner crossings are crossings with `γ`, hence at most two). -/
private theorem f_beta {γ : Fin n} (X : Γ.Removal {γ}) {d' : X.D'} (hd : X.Γ'.EmptyHumpAt d') :
    ∃ h₀ hb : D, ∃ L : ℕ, f_Beta Γ h₀ hb L := by
  obtain ⟨hsw, hsz⟩ := hd
  have hφ := f_φ_two (Γ := X.Γ') (x := X.Γ'.α d') hsz
  simp only [j_φ_apply, j_α_α] at hφ
  -- `hφ : σ' (α' (σ' d')) = α' d'`
  have hfin := f_finSeg_fin hsw
  have hA' : X.Γ'.Above (X.Γ'.σ d') := no_above_σ hsw.1
  have hx' : X.Γ'.crossingOf (X.Γ'.α (X.Γ'.σ d')) = X.Γ'.crossingOf (X.Γ'.α d') := by
    rw [← hφ, j_crossingOf_σ]
  have ha₀ : Γ.Above (X.ι (X.Γ'.σ d')) := X.r_above hA'
  have hAb : Γ.Above (X.ι (X.Γ'.α (X.Γ'.σ d'))) := X.r_above (f_above_α hA')
  have hcurve : Γ.curve (X.ι (X.Γ'.α (X.Γ'.σ d'))) = Γ.curve (X.ι (X.Γ'.σ d')) := by
    rw [← X.isRemoval.curve, ← X.isRemoval.curve, j_curve_α]
  have hf₀ : Γ.IsFinVertex (Γ.crossingOf (X.ι (X.Γ'.σ d'))) :=
    (X.r_finVertex (X.Γ'.crossingOf (X.Γ'.σ d'))).1 (by rw [j_crossingOf_σ]; exact hfin.1)
  have hfb : Γ.IsFinVertex (Γ.crossingOf (X.ι (X.Γ'.α (X.Γ'.σ d')))) :=
    (X.r_finVertex (X.Γ'.crossingOf (X.Γ'.α (X.Γ'.σ d')))).1 (by rw [hx']; exact hfin.2)
  set h₀ := X.ι (X.Γ'.σ d') with hh₀
  set hb := X.ι (X.Γ'.α (X.Γ'.σ d')) with hhb
  have hσS : Γ.curve (Γ.σ h₀) = Γ.S := by
    have := hf₀.1
    change Γ.S ∈ Γ.curves _ at this
    rw [j_curves_crossingOf, mem_insert, mem_singleton] at this
    rcases this with h | h
    · exact absurd h.symm ha₀.1
    · exact h.symm
  have hne : Γ.crossingOf h₀ ≠ Γ.crossingOf hb := by
    intro hx
    rcases f_eq_or_eq_σσ hx hcurve.symm with h | h
    · exact X.Γ'.isSConf.α_ne _ (X.isRemoval.inj h)
    · have h1 : Γ.side (Γ.cellOf hb) = 1 := hAb.2
      have e0 : Γ.side (Γ.cellOf h₀) = 1 := ha₀.2
      rw [h, no_side_σ, no_side_σ, if_neg ha₀.1, if_pos hσS, e0] at h1
      exact absurd h1 (by decide)
  obtain ⟨L, -, hL, hLp, -, hcover⟩ := no_upper_arc ha₀ hAb hcurve.symm hf₀.1 hfb.1 hne
  obtain ⟨e, ⟨m, hdel, rfl⟩, -, hαe⟩ := X.isRemoval.α (X.Γ'.σ d')
  rw [← hh₀, ← hhb] at hαe
  have hmL : (Γ.straight ^ L) h₀ = (Γ.straight ^ m) h₀ := by rw [hL, hαe, j_α_α]
  have hkeep : ¬ Γ.Deleted {γ} (Γ.crossingOf h₀) := (X.r_keep _).1
  have hm : m < period Γ.straight h₀ := by
    by_contra hc
    push Not at hc
    have hp := period_pos Γ.straight h₀
    apply hkeep
    have := hdel (period Γ.straight h₀ - 1) (by omega)
    rwa [← no_crossingOf_α_straight, ← no_pow_succ, Nat.sub_add_cancel hp, Perm.coe_pow,
      iterate_period] at this
  have hLm : L = m := no_pow_inj hLp hm hmL
  subst hLm
  have hβγ : Γ.curve h₀ ≠ γ := fun h => hkeep ⟨γ, mem_singleton_self γ, by
    show γ ∈ Γ.curves _
    rw [j_curves_crossingOf, h]; exact mem_insert_self _ _⟩
  have hcurves : ∀ t < L, Γ.curves (Γ.crossingOf (Γ.α ((Γ.straight ^ t) h₀))) =
      {Γ.curve h₀, γ} := by
    intro t ht
    obtain ⟨c, hc, hon⟩ := hdel t ht
    rw [mem_singleton] at hc
    subst hc
    refine no_mem_curves hon ?_ hβγ
    rw [j_curves_crossingOf, j_curve_α, no_curve_pow]; exact mem_insert_self _ _
  have hL2 : L ≤ 2 := by
    by_contra hc
    push Not at hc
    have h2 := Γ.isSConf.two_int (Γ.curve h₀) γ hβγ
    have hsub : ({Γ.crossingOf (Γ.α ((Γ.straight ^ 0) h₀)),
        Γ.crossingOf (Γ.α ((Γ.straight ^ 1) h₀)), Γ.crossingOf (Γ.α ((Γ.straight ^ 2) h₀))} :
          Finset Γ.Crossing) ⊆
        univ.filter (fun x : Orbit Γ.σ => crossingCurves Γ.σ Γ.curve x = {Γ.curve h₀, γ}) := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rcases hx with rfl | rfl | rfl
      · exact hcurves 0 (by omega)
      · exact hcurves 1 (by omega)
      · exact hcurves 2 (by omega)
    have h3 := card_le_card hsub
    rw [card_eq_three.2 ⟨_, _, _, f_cross_ne (by omega) (by omega),
      f_cross_ne (by omega) (by omega), f_cross_ne (by omega) (by omega), rfl⟩] at h3
    omega
  exact ⟨h₀, hb, L, ⟨ha₀, hAb, hcurve, hf₀, hfb, hL, hL2, hcover⟩⟩

/-- A segment above the sweep from a vertex on the sweep (not on `β`) cannot end on `β`: it would
form a triangle with the piece of `β` from `i` or from `j` (SH: "`Δ(i, u, k)` is a triangle in
`Γ`, contradicting Lemma 3.6").

The triangle found here can be reflex (Lemma 3.6 in `L36.lean` covers convex triangles only;
`doc/pca/sweep.md`, O10); the reflex branches use `MinCE.x_no_tri` (`Pca/Sweep/Reflex.lean`,
O3). -/
private theorem f_hit (hΓ : Γ.MinCE) {h₀ hb : D} {L : ℕ} (B : f_Beta Γ h₀ hb L) {a : D}
    (ha : Γ.Above a) (hfa : Γ.IsFinVertex (Γ.crossingOf a))
    (hna : Γ.curve h₀ ∉ Γ.curves (Γ.crossingOf a))
    (hu : Γ.curve h₀ ∈ Γ.curves (Γ.crossingOf (Γ.α a))) : False := by
  have hca : Γ.curve a ≠ Γ.curve h₀ := fun h =>
    hna (by rw [j_curves_crossingOf, h]; exact mem_insert_self _ _)
  have hy : Γ.curve (Γ.σ (Γ.α a)) = Γ.curve h₀ := by
    rw [j_curves_crossingOf, mem_insert, mem_singleton, j_curve_α] at hu
    rcases hu with h | h
    · exact absurd h.symm hca
    · exact h.symm
  have hβS : Γ.curve h₀ ≠ Γ.S := B.a0.1
  have hyA : Γ.Above (Γ.σ (Γ.α a)) :=
    ⟨by rw [hy]; exact hβS, by unfold Up; rw [← j_φ_apply, j_cellOf_φ]; exact ha.2⟩
  have hnS : Γ.S ∉ Γ.curves (Γ.crossingOf (Γ.α a)) := by
    rw [j_curves_crossingOf, mem_insert, mem_singleton, j_curve_α, hy]
    rintro (h | h)
    · exact ha.1 h.symm
    · exact hβS h.symm
  have hxy : Γ.crossingOf (Γ.σ (Γ.α a)) = Γ.crossingOf (Γ.α a) := j_crossingOf_σ _ _
  obtain ⟨q, hq, hq'⟩ := B.cover _ hyA hy
  obtain ⟨t, ht, hut⟩ : ∃ t < L,
      Γ.crossingOf (Γ.α ((Γ.straight ^ t) h₀)) = Γ.crossingOf (Γ.α a) := by
    rcases hq' with h | h
    · cases q with
      | zero =>
        exfalso
        rw [pow_zero, Perm.one_apply] at h
        apply hnS
        rw [← hxy, ← h]
        exact B.f0.1
      | succ q =>
        exact ⟨q, by omega, by rw [← no_crossingOf_α_straight, ← no_pow_succ, h, hxy]⟩
    · refine ⟨q, ?_, by rw [h, j_α_α, hxy]⟩
      rcases hq.lt_or_eq with h1 | h1
      · exact h1
      · exfalso
        have h2 : Γ.σ (Γ.α a) = hb := by
          have h3 := congrArg Γ.α (h.symm.trans (h1 ▸ B.hL))
          rwa [j_α_α, j_α_α] at h3
        apply hnS
        rw [← hxy, h2]
        exact B.fb.1
  have hpick : ∃ b, Γ.Above b ∧ Γ.curve b = Γ.curve h₀ ∧ Γ.IsFinVertex (Γ.crossingOf b) ∧
      Γ.crossingOf (Γ.α b) = Γ.crossingOf (Γ.α a) := by
    rcases (show t = 0 ∨ t + 1 = L by have := B.L2; omega) with rfl | h1
    · exact ⟨h₀, B.a0, rfl, B.f0, by rw [← hut, pow_zero, Perm.one_apply]⟩
    · refine ⟨hb, B.ab, B.curve, B.fb, ?_⟩
      rw [← hut, ← B.hL, ← h1, no_pow_succ, no_crossingOf_α_straight]
  obtain ⟨b, hbA, hbc, hbf, hbx⟩ := hpick
  have hcab : Γ.curve a ≠ Γ.curve b := by rw [hbc]; exact hca
  have hxab : Γ.crossingOf a ≠ Γ.crossingOf b := by
    intro h
    apply hna
    rw [h, j_curves_crossingOf, hbc]
    exact mem_insert_self _ _
  have hT : Γ.IsTri a b :=
    ⟨ha, hbA, hfa, hbf, hxab, hbx.symm, f_aboveVertex ha (by rw [hy]; exact hβS), hcab⟩
  have hTs : Γ.IsTri b a :=
    ⟨hbA, ha, hbf, hfa, Ne.symm hxab, hbx, hbx ▸ hT.2.2.2.2.2.2.1, Ne.symm hcab⟩
  -- the two orientations at `u`: `α b = σ (α a)` (`φ a = α b`) or `α b = σ³ (α a)` (`φ b = α a`)
  have hor : Γ.α b = Γ.σ (Γ.α a) ∨ Γ.α b = Γ.σ (Γ.σ (Γ.σ (Γ.α a))) := by
    have hc : Γ.curve (Γ.α a) ≠ Γ.curve (Γ.α b) := by rw [j_curve_α, j_curve_α]; exact hcab
    rcases no_mem_crossing hbx with h | h | h | h
    · exact absurd (by rw [h]) hc
    · exact Or.inl h
    · exact absurd (by rw [h, j_curve_σσ]) hc
    · exact Or.inr h
  rcases hor with h | h
  · by_cases hp : Γ.pos (Γ.crossingOf a) < Γ.pos (Γ.crossingOf b)
    · exact hΓ.lemma_3_6.2 a b ⟨hT, hp, by rw [j_φ_apply, h]⟩
    · -- reflex triangle: excluded by `MinCE.x_no_tri` (`Pca/Sweep/Reflex.lean`)
      exact hΓ.x_no_tri a b hT
  · by_cases hp : Γ.pos (Γ.crossingOf b) < Γ.pos (Γ.crossingOf a)
    · exact hΓ.lemma_3_6.2 b a ⟨hTs, hp, by rw [j_φ_apply, h, Γ.j_σ4]⟩
    · -- reflex triangle: excluded by `MinCE.x_no_tri` (`Pca/Sweep/Reflex.lean`)
      exact hΓ.x_no_tri a b hT

/-- In `Γ − β`, a joined segment starting above the sweep at a vertex on the sweep is a segment of
`Γ` (else `f_hit`). -/
private theorem f_no_hit (hΓ : Γ.MinCE) {h₀ hb : D} {L : ℕ} (B : f_Beta Γ h₀ hb L)
    (X : Γ.Removal {Γ.curve h₀}) (x' : X.D') (hA : Γ.Above (X.ι x'))
    (hf : Γ.IsFinVertex (Γ.crossingOf (X.ι x'))) : X.ι (X.Γ'.α x') = Γ.α (X.ι x') := by
  obtain ⟨e, ⟨k, hdel, rfl⟩, -, hα⟩ := X.isRemoval.α x'
  cases k with
  | zero => rw [hα, pow_zero, Perm.one_apply]
  | succ k =>
    exfalso
    obtain ⟨c, hc, hon⟩ := hdel 0 (Nat.succ_pos k)
    rw [mem_singleton] at hc
    rw [hc, pow_zero, Perm.one_apply] at hon
    have hkeep := (X.r_keep x').1
    exact f_hit hΓ B hA hf (fun h => hkeep ⟨_, mem_singleton_self _, h⟩) hon

/-- **SH Lemma 3.8** (p. 319). -/
theorem MinCE.lemma_3_8 (hΓ : Γ.MinCE) {γ : Fin n} (X : Γ.Removal {γ}) (d' : X.D') :
    ¬ X.Γ'.EmptyHumpAt d' := by
  intro hd
  obtain ⟨h₀, hb, L, B⟩ := f_beta X hd
  have hβ : Γ.Present (Γ.curve h₀) := ⟨B.a0.1, h₀, rfl, B.a0⟩
  have hS : Γ.S ∉ ({Γ.curve h₀} : Finset (Fin n)) := by
    rw [mem_singleton]; exact fun h => B.a0.1 h.symm
  obtain ⟨Y⟩ := exists_removal _ hS
  have h1 := hΓ.lemma_3_3 ⟨_, mem_singleton_self _, hβ⟩ Y
  have h2 := hΓ.removal_not_terminal hβ Y
  have hP : Y.Γ'.Progress := by
    by_contra h
    exact h1 ⟨h2, h⟩
  -- an empty hump or triangle of `Γ − β` gives a hump or triangle of `Γ`
  have key : ∀ e', Y.Γ'.IsFinSeg e' →
      (Y.Γ'.upperCell e').size = 2 ∨ (Y.Γ'.upperCell e').size = 3 → False := by
    intro e' hsw hsz
    have hfin := f_finSeg_fin hsw
    have hA1 : Y.Γ'.Above (Y.Γ'.σ e') := no_above_σ hsw.1
    have ha : Γ.Above (Y.ι (Y.Γ'.σ e')) := Y.r_above hA1
    have hfa : Γ.IsFinVertex (Γ.crossingOf (Y.ι (Y.Γ'.σ e'))) :=
      (Y.r_finVertex (Y.Γ'.crossingOf (Y.Γ'.σ e'))).1 (by rw [j_crossingOf_σ]; exact hfin.1)
    have hα1 := f_no_hit hΓ B Y _ ha hfa
    rcases hsz with hsz | hsz
    · -- hump: the leg is a hump of `Γ`
      have hφ := f_φ_two (Γ := Y.Γ') (x := Y.Γ'.α e') hsz
      simp only [j_φ_apply, j_α_α] at hφ
      have hx : Y.Γ'.crossingOf (Y.Γ'.α (Y.Γ'.σ e')) = Y.Γ'.crossingOf (Y.Γ'.α e') := by
        rw [← hφ, j_crossingOf_σ]
      apply hΓ.lemma_3_6.1 (Y.ι (Y.Γ'.σ e'))
      refine ⟨ha, hfa, ?_⟩
      rw [← hα1]
      exact (Y.r_finVertex (Y.Γ'.crossingOf (Y.Γ'.α (Y.Γ'.σ e')))).1 (by rw [hx]; exact hfin.2)
    · -- triangle: both legs are segments of `Γ`, a triangle of `Γ`
      have hφ := f_φ_three (Γ := Y.Γ') (x := Y.Γ'.α e') hsz
      simp only [j_φ_apply, j_α_α] at hφ
      -- `hφ : σ' (α' (σ' (α' (σ' e')))) = α' e'`
      have hx2S : Y.Γ'.curve (Y.Γ'.α (Y.Γ'.σ (Y.Γ'.α (Y.Γ'.σ e')))) ≠ Y.Γ'.S := by
        intro h
        have := no_curve_σ_ne (Γ := Y.Γ') (Y.Γ'.α (Y.Γ'.σ (Y.Γ'.α (Y.Γ'.σ e'))))
        rw [hφ, j_curve_α, hsw.1.1, h] at this
        exact this rfl
      have hl2 : Y.Γ'.curve (Y.Γ'.σ (Y.Γ'.α (Y.Γ'.σ e'))) ≠ Y.Γ'.S := by
        rw [← j_curve_α]; exact hx2S
      have hA2 : Y.Γ'.Above (Y.Γ'.α (Y.Γ'.σ (Y.Γ'.α (Y.Γ'.σ e')))) := by
        refine ⟨hx2S, ?_⟩
        unfold Up
        rw [no_side_α hl2, ← j_φ_apply, j_cellOf_φ, j_cellOf_σ]
        exact hsw.1.2
      have hb2 := Y.r_above hA2
      have hx2 : Y.Γ'.crossingOf (Y.Γ'.α (Y.Γ'.σ (Y.Γ'.α (Y.Γ'.σ e')))) =
          Y.Γ'.crossingOf (Y.Γ'.α e') := by rw [← hφ, j_crossingOf_σ]
      have hfb2 : Γ.IsFinVertex
          (Γ.crossingOf (Y.ι (Y.Γ'.α (Y.Γ'.σ (Y.Γ'.α (Y.Γ'.σ e')))))) :=
        (Y.r_finVertex (Y.Γ'.crossingOf _)).1 (by rw [hx2]; exact hfin.2)
      have hα2 := f_no_hit hΓ B Y _ hb2 hfb2
      have hab : Γ.α (Y.ι (Y.Γ'.α (Y.Γ'.σ (Y.Γ'.α (Y.Γ'.σ e'))))) =
          Γ.σ (Γ.α (Y.ι (Y.Γ'.σ e'))) := by
        rw [← hα2, j_α_α, Y.isRemoval.σ, hα1]
      -- convex: `k < l` (positions along the finite edge `[k, l]` of `Γ − β`)
      have hpos : Γ.pos (Γ.crossingOf (Y.ι (Y.Γ'.σ e'))) <
          Γ.pos (Γ.crossingOf (Y.ι (Y.Γ'.α (Y.Γ'.σ (Y.Γ'.α (Y.Γ'.σ e')))))) := by
        have h1 : Γ.crossingOf (Y.ι (Y.Γ'.σ e')) = Γ.crossingOf (Y.ι e') := by
          rw [Y.isRemoval.σ, j_crossingOf_σ]
        have h2 : Γ.crossingOf (Y.ι (Y.Γ'.α (Y.Γ'.σ (Y.Γ'.α (Y.Γ'.σ e'))))) =
            Γ.crossingOf (Y.ι (Y.Γ'.α e')) := congrArg (Removal.rΨ Y) hx2
        rw [h1, h2]
        exact f_pos_lt Y hsw
      set a := Y.ι (Y.Γ'.σ e') with ha_def
      set b := Y.ι (Y.Γ'.α (Y.Γ'.σ (Y.Γ'.α (Y.Γ'.σ e')))) with hb_def
      have hcb : Γ.curve b ≠ Γ.curve a := by
        rw [← Γ.j_curve_α b, hab]
        have := no_curve_σ_ne (Γ := Γ) (Γ.α a)
        rwa [j_curve_α] at this
      apply hΓ.lemma_3_6.2 a b
      refine ⟨⟨ha, hb2, hfa, hfb2, ?_, by rw [hab, j_crossingOf_σ], ?_, fun h => hcb h.symm⟩,
        hpos, by rw [j_φ_apply, hab]⟩
      · intro hx
        have h3 := no_mem_curves hfa.1
          (by rw [j_curves_crossingOf]; exact mem_insert_self _ _ : Γ.curve a ∈ Γ.curves _) ha.1
        have h4 : Γ.curve b ∈ Γ.curves (Γ.crossingOf a) := by
          rw [hx, j_curves_crossingOf]; exact mem_insert_self _ _
        rw [h3, mem_insert, mem_singleton] at h4
        rcases h4 with h | h
        · exact hcb h
        · exact hb2.1 h
      · exact f_aboveVertex ha (by rw [← hab, j_curve_α]; exact hb2.1)
  rcases hP with ⟨e', he'⟩ | ⟨e', he'⟩ | ⟨d, e, hd, he, hS', hm⟩
  · exact key e' he'.1 (Or.inl he'.2)
  · exact key e' he'.1 (Or.inr he'.2)
  · have hc : Y.Γ'.cellOf e = Y.Γ'.upperCell d := Orbit.mem_darts.1 he
    have hp : Y.Γ'.Present (Y.Γ'.curve e) := ⟨hS', e, rfl, hS', by rw [hc]; exact hd.2⟩
    obtain ⟨hpΓ, -, hiff⟩ := Y.meetsSweep_iff hp
    exact hm (hiff.2 (hΓ.lemma_3_4 hpΓ))

end SConf

end Pca.Sweep
