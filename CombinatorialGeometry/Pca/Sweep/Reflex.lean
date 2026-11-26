/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.6 for all triangles (open points O3, O10)

Lemma 3.6 (`Pca/Sweep/L36.lean`) is proved for humps and **convex** triangles. Here the
**reflex** triangles are excluded too, so a minimal counterexample has no triangle at all
(`MinCE.x_no_tri`). Paper proof: `doc/pca/sweep.md`.

Reflex `Δ(k, v, l)`: legs `a = ⟨k, v⟩` (curve `A`), `b = ⟨l, v⟩` (curve `B`), `k < l`,
`φ b = α a`. With the cut `r` of `S[k, l]` + legs (as in `c_tri_core`), both continuations
`straight a`, `straight b` after `v` lie inside (`r = 1`), so by `c_leg` every dart of `A` or `B`
above `S` off the legs is inside; a curve with a dart inside that is not `A`, `B` stays inside
(`x_kept_free`). Let `cR` be the curves without a dart inside off the legs.
* (i) `cR` contains a present curve: SH's argument (`x_core`, `X_Core.lean`).
* (ii) it does not: every crossing of `S` lies in `[k, l]`, so `l` is the last vertex and the
  ∞-arc is one segment; directing `l` to infinity gives a smaller stuck configuration
  (`x_redirect_false`, `X_Redir.lean`).
-/
import Pca.Sweep.L36
import Pca.Sweep.X_Core
import Pca.Sweep.X_Redir

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- **Reflex triangles**: legs `a = ⟨k, v⟩`, `b = ⟨l, v⟩`, `k < l`, with the region at `v` the
three other quadrants (`φ b = α a`), contradict minimality. -/
theorem x_reflex_core (hΓ : Γ.MinCE) {z : D} (hz : Γ.infStart = some z) {tk tl : ℕ}
    (hlt : tk < tl) (hfin : tl + Γ.infLen < period Γ.straight z) {a b : D}
    (ha : a = Γ.σ (Γ.noC z tk)) (hb : b = Γ.σ (Γ.noC z tl))
    (hv : Γ.crossingOf (Γ.α a) = Γ.crossingOf (Γ.α b))
    (hvS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α a))) (hab : Γ.curve a ≠ Γ.curve b)
    (hφ : Γ.φ b = Γ.α a) : False := by
  have hA : Γ.Above a := ha ▸ no_above_σ (no_noC_sweep hz tk)
  have hB : Γ.Above b := hb ▸ no_above_σ (no_noC_sweep hz tl)
  have hrefl : Γ.σ (Γ.α b) = Γ.α a := hφ
  have hSa : Γ.S ∈ Γ.curves (Γ.crossingOf a) := ha ▸ c_S_mem_σ_noC hz tk
  have hSb : Γ.S ∈ Γ.curves (Γ.crossingOf b) := hb ▸ c_S_mem_σ_noC hz tl
  have hαA : Γ.Above (Γ.α a) :=
    ⟨by rw [j_curve_α]; exact hA.1, by unfold Up; rw [no_side_α hA.1]; exact hA.2⟩
  have hαB : Γ.Above (Γ.α b) :=
    ⟨by rw [j_curve_α]; exact hB.1, by unfold Up; rw [no_side_α hB.1]; exact hB.2⟩
  -- the cut of `S[k, l]` + legs (as in `c_tri_core`)
  set Lid : Finset D := {b, Γ.α a, Γ.α b, a}
  have hmem : ∀ y, y ∈ Lid ↔ y = b ∨ y = Γ.α a ∨ y = Γ.α b ∨ y = a := by
    intro y; simp only [Lid, mem_insert, mem_singleton]
  set ret : ℕ → D := fun j => if j = 0 then b else Γ.α a
  obtain ⟨r, hcut, hbase⟩ := c_lid_cut hz hlt (by omega) (q := 2) two_pos ret
    (fun j _ => by
      simp only [ret]
      split_ifs
      · exact hB.1
      · rw [j_curve_α]; exact hA.1)
    (by simp only [ret, if_pos rfl]; rw [hb, j_crossingOf_σ])
    (fun j hj => by
      have : j = 0 := by omega
      subst this
      simp only [ret, if_pos rfl, show (0 + 1 = 0) = False by simp, if_false]
      exact hv.symm)
    (by simp only [ret, show (2 - 1 = 0) = False by simp, if_false]
        rw [j_α_α, ha, j_crossingOf_σ])
    (fun i hi j hj he => by
      by_contra hne
      have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [ret, if_pos rfl, show (1 = 0) = False by simp, if_false] at he
        have := c_curve_seg he
        rw [j_curve_α] at this
        exact hab this
      · simp only [ret, if_pos rfl, show (1 = 0) = False by simp, if_false] at he
        have := c_curve_seg he
        rw [j_curve_α] at this
        exact hab this.symm)
    Lid
    (fun y => by
      rw [hmem]
      constructor
      · rintro (h | h | h | h)
        · exact ⟨0, two_pos, Or.inl h⟩
        · exact ⟨1, one_lt_two, Or.inl h⟩
        · exact ⟨0, two_pos, Or.inr h⟩
        · refine ⟨1, one_lt_two, Or.inr ?_⟩
          simp only [ret, show (1 = 0) = False by simp, if_false, j_α_α]
          exact h
      · rintro ⟨j, hj, h⟩
        have : j = 0 ∨ j = 1 := by omega
        rcases this with rfl | rfl
        · simp only [ret, if_pos rfl] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
        · simp only [ret, show (1 = 0) = False by simp, if_false] at h
          rcases h with h | h
          · exact Or.inr (Or.inl h)
          · rw [j_α_α] at h; exact Or.inr (Or.inr (Or.inr h)))
  have hnS : ∀ t, Γ.σ (Γ.noC z t) ≠ Γ.α a ∧ Γ.σ (Γ.noC z t) ≠ Γ.α b := by
    intro t
    constructor
    · intro he
      apply hvS
      rw [← he, j_crossingOf_σ]; exact no_S_mem_noC hz t
    · intro he
      apply hvS
      rw [hv, ← he, j_crossingOf_σ]; exact no_S_mem_noC hz t
  have hσ : ∀ t < period Γ.straight z, (Γ.σ (Γ.noC z t) ∈ Lid ↔ t = tk ∨ t = tl) := by
    intro t ht
    rw [hmem, ha, hb]
    constructor
    · rintro (he | he | he | he)
      · exact Or.inr (c_σ_noC_inj ht (by omega) he)
      · exact absurd (by rw [ha]; exact he) (hnS t).1
      · exact absurd (by rw [hb]; exact he) (hnS t).2
      · exact Or.inl (c_σ_noC_inj ht (by omega) he)
    · rintro (rfl | rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl rfl
  have hcc : CCut Γ z tk tl r Lid := ⟨hz, hlt, hfin, hcut, hbase, hσ⟩
  have hX : ∀ y, Γ.σ (Γ.α y) ∈ Lid → ¬ Γ.OnSweep (Γ.crossingOf (Γ.α y)) →
      Γ.crossingOf (Γ.α y) = Γ.crossingOf (Γ.α a) := by
    intro y hl hn
    rw [← j_crossingOf_σ Γ (Γ.α y)]
    rcases (hmem _).1 hl with he | he | he | he
    · exact absurd (by rw [← j_crossingOf_σ Γ (Γ.α y), he]; exact hSb) hn
    · rw [he]
    · rw [he, hv]
    · exact absurd (by rw [← j_crossingOf_σ Γ (Γ.α y), he]; exact hSa) hn
  have hal : a ∈ Lid := (hmem a).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hbl : b ∈ Lid := (hmem b).2 (Or.inl rfl)
  have hαal : Γ.α a ∈ Lid := (hmem _).2 (Or.inr (Or.inl rfl))
  have hαbl : Γ.α b ∈ Lid := (hmem _).2 (Or.inr (Or.inr (Or.inl rfl)))
  -- reflex: both continuations after `v` lie inside
  have hφa : Γ.φ a = Γ.straight b := by rw [j_φ_apply, j_straight_apply, ← hrefl]
  have hrb : r (Γ.cellOf (Γ.straight b)) = 1 := by
    rw [← hφa, j_cellOf_φ, ha, j_cellOf_σ]; exact hbase
  have hsx : ∀ y, Γ.crossingOf (Γ.straight y) = Γ.crossingOf (Γ.α y) := no_crossingOf_α_straight
  have hsbL : Γ.straight b ∉ Lid := by
    rw [hmem]
    rintro (he | he | he | he)
    · apply hvS; rw [hv, ← hsx, he]; exact hSb
    · exact hab (by rw [← j_curve_straight Γ b, he, j_curve_α])
    · rw [j_straight_apply] at he; exact Γ.j_σσ_ne _ he
    · apply hvS; rw [hv, ← hsx, he]; exact hSa
  have hsaL : Γ.straight a ∉ Lid := by
    rw [hmem]
    rintro (he | he | he | he)
    · apply hvS; rw [← hsx, he]; exact hSb
    · rw [j_straight_apply] at he; exact Γ.j_σσ_ne _ he
    · exact hab (by rw [← j_curve_straight Γ a, he, j_curve_α])
    · apply hvS; rw [← hsx, he]; exact hSa
  have hra : r (Γ.cellOf (Γ.straight a)) = 1 := by
    have hsa : Γ.straight a = Γ.σ (Γ.straight b) := by
      rw [j_straight_apply, j_straight_apply, ← hrefl]
    have := hcut _ (by rw [j_curve_straight]; exact hB.1)
    rw [if_neg hsbL, hrb] at this
    rw [hsa, j_cellOf_σ]
    exact c_zmod2_eq_of_add this
  have hnσS : ∀ y, ¬ Γ.OnSweep (Γ.crossingOf (Γ.α y)) → Γ.curve (Γ.σ (Γ.α y)) ≠ Γ.S :=
    fun y hy hS => hy (by
      show Γ.S ∈ _
      rw [j_curves_crossingOf, ← hS]; exact mem_insert_of_mem (mem_singleton_self _))
  have hsaA : Γ.Above (Γ.straight a) := ⟨by rw [j_curve_straight]; exact hA.1, by
    unfold Up; rw [no_side_straight, if_neg (hnσS a hvS), add_zero]; exact hA.2⟩
  have hsbA : Γ.Above (Γ.straight b) := ⟨by rw [j_curve_straight]; exact hB.1, by
    unfold Up; rw [no_side_straight, if_neg (hnσS b (by rw [← hv]; exact hvS)), add_zero]
    exact hB.2⟩
  have hAk : Γ.curve a ∉ Γ.cR r Lid := fun hm =>
    (c_mem_cR.1 hm).2 ⟨_, j_curve_straight _ _, hsaA, hsaL, hra⟩
  have hBk : Γ.curve b ∉ Γ.cR r Lid := fun hm =>
    (c_mem_cR.1 hm).2 ⟨_, j_curve_straight _ _, hsbA, hsbL, hrb⟩
  -- the curves through the crossings of the legs
  have lidX : ∀ y ∈ Lid, ∀ w, Γ.crossingOf w = Γ.crossingOf y →
      Γ.curve w = Γ.S ∨ ∃ y' ∈ Lid, Γ.curve y' = Γ.curve w := by
    intro y hy w hcw
    have hm : Γ.curve w ∈ Γ.curves (Γ.crossingOf w) := by
      rw [j_curves_crossingOf]; exact mem_insert_self _ _
    rcases (hmem y).1 hy with rfl | rfl | rfl | rfl
    · rw [hb] at hcw; exact c_lidX_S hz (hb ▸ hbl) w hcw
    · rw [hcw, j_curves_crossingOf, mem_insert, mem_singleton, j_curve_α, ← hrefl,
        j_curve_σσ, j_curve_α] at hm
      rcases hm with hm | hm
      · exact Or.inr ⟨_, hal, hm.symm⟩
      · exact Or.inr ⟨_, hbl, hm.symm⟩
    · rw [hcw, j_curves_crossingOf, mem_insert, mem_singleton, hrefl, j_curve_α,
        j_curve_α] at hm
      rcases hm with hm | hm
      · exact Or.inr ⟨_, hbl, hm.symm⟩
      · exact Or.inr ⟨_, hal, hm.symm⟩
    · rw [ha] at hcw; exact c_lidX_S hz (ha ▸ hal) w hcw
  have hlidc : ∀ y ∈ Lid, Γ.curve y = Γ.curve a ∨ Γ.curve y = Γ.curve b := by
    intro y hy
    rcases (hmem y).1 hy with rfl | rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (j_curve_α _ _)
    · exact Or.inr (j_curve_α _ _)
    · exact Or.inl rfl
  have hXL : XLid Γ z tk tl r Lid := by
    refine ⟨hcc, ?_, ?_, ?_, ?_⟩
    · intro y hy
      rcases (hmem y).1 hy with rfl | rfl | rfl | rfl
      · exact hB
      · exact hαA
      · exact hαB
      · exact hA
    · intro y hy
      rw [hmem]
      rcases (hmem y).1 hy with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (j_α_α _ _)))
      · exact Or.inl (j_α_α _ _)
      · exact Or.inr (Or.inl rfl)
    · intro w hwa hwl hwk
      by_cases hwA : Γ.curve w = Γ.curve a
      · rw [c_leg hcc hA hSa hal hαal hX hwA hwa hwl, hra]
      by_cases hwB : Γ.curve w = Γ.curve b
      · rw [c_leg hcc hB hSb hbl hαbl (fun y h1 h2 => (hX y h1 h2).trans hv) hwB hwa hwl, hrb]
      obtain ⟨y0, hy0, hin⟩ := c_witness hwk hwa.1
      refine x_kept_free hcc lidX hin (fun y hy hc => ?_) hy0.symm hwa
      rcases hlidc y hy with h | h
      · exact hwA (by rw [← hy0, ← hc, h])
      · exact hwB (by rw [← hy0, ← hc, h])
    · intro y hy w hcw
      rcases lidX y hy w hcw with hS | ⟨y', hy', hc⟩
      · exact Or.inl hS
      · right
        rw [← hc]
        rcases hlidc y' hy' with h | h
        · rw [h]; exact hAk
        · rw [h]; exact hBk
  by_cases hc : ∃ γ ∈ Γ.cR r Lid, Γ.Present γ
  · -- case (i): SH's argument
    exact x_core hΓ hXL hc (by rw [← ha]; exact hAk)
  · -- case (ii): every curve enters the region; direct `l` to infinity
    push Not at hc
    have hall : ∀ t < period Γ.straight z, t ≠ tk → t ≠ tl → tk ≤ t ∧ t < tl := by
      intro t ht h1 h2
      have hs := no_above_σ (no_noC_sweep hz t)
      exact x_sweep_kept hXL ht h1 h2 (fun hm => hc _ hm ⟨hs.1, _, rfl, hs⟩)
    have hk0 : tk = 0 := by
      by_contra h
      have := hall 0 (by omega) (by omega) (by omega)
      omega
    have hlP : tl + 1 = period Γ.straight z := by
      by_contra h
      have := hall (period Γ.straight z - 1) (by omega) (by omega) (by omega)
      omega
    exact x_redirect_false hΓ hz (by omega) hlP (by omega)
      ⟨_, hvS, Γ.α a, Orbit.mem_darts.2 rfl, hαA⟩

/-- **SH Lemma 3.6 for all triangles**: a minimal counterexample has no triangle (convex:
`c_tri_core`, reflex: `x_reflex_core`). -/
theorem MinCE.x_no_tri (hΓ : Γ.MinCE) (a b : D) : ¬ Γ.IsTri a b := by
  rintro ⟨hA, hB, hfa, hfb, hne, hv, hvA, hab⟩
  obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z :=
    Option.isSome_iff_exists.1 (Γ.infStart_isSome ⟨a⟩)
  have hfin : ∀ {y : D}, Γ.Above y → Γ.IsFinVertex (Γ.crossingOf y) →
      ∃ t, t + Γ.infLen < period Γ.straight z ∧ y = Γ.σ (Γ.noC z t) := by
    intro y hy hf
    obtain ⟨t, ht, hx⟩ := no_onSweep_noC hz hf.1
    exact ⟨t, (no_noC_fin hz ht).1 (hx ▸ hf), c_eq_σ_noC hz hy hx.symm⟩
  obtain ⟨t1, ht1, h1⟩ := hfin hA hfa
  obtain ⟨t2, ht2, h2⟩ := hfin hB hfb
  have hor : Γ.φ a = Γ.α b ∨ Γ.φ b = Γ.α a := by
    rcases no_mem_crossing hv.symm with h | h | h | h
    · exact absurd (congrArg Γ.crossingOf (Γ.α.injective h)).symm hne
    · exact Or.inl (by rw [j_φ_apply, h])
    · exact absurd (by rw [← j_curve_α Γ b, h, j_curve_σσ, j_curve_α]) hab.symm
    · exact Or.inr (by rw [j_φ_apply, h, Γ.j_σ4])
  have hvS' : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α b)) := by rw [← hv]; exact hvA.1
  rcases lt_trichotomy t1 t2 with h | rfl | h
  · rcases hor with hφ | hφ
    · exact c_tri_core hΓ hz h ht2 h1 h2 hv hvA.1 hab hφ
    · exact x_reflex_core hΓ hz h ht2 h1 h2 hv hvA.1 hab hφ
  · exact hne (by rw [h1, h2])
  · rcases hor with hφ | hφ
    · exact x_reflex_core hΓ hz h ht1 h2 h1 hv.symm hvS' (Ne.symm hab) hφ
    · exact c_tri_core hΓ hz h ht1 h2 h1 hv.symm hvS' (Ne.symm hab) hφ

end SConf

end Pca.Sweep
