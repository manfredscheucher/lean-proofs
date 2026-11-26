/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package P: the data of the surgery from the hypotheses of Lemma 3.11

`p_ccut`: the region cut (`CCut`) of a closed walk `S[tk, tl]` + `ret` (from `tl` back to `tk`
above `S`). `p_loop_data`, `p_gamma_cut`: the ends of the loop `γ` and its region cut.
`p_l311_surgery`: `doc/pca/sweep.md`, steps 1-2, then `PSurg.surgery`.
-/
import Pca.Sweep.P_Main
import Pca.Sweep.Responsible

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- The region cut of the closed walk `S[tk, tl]` + `ret`. -/
theorem p_ccut {z : D} (hz : Γ.infStart = some z) {tk tl : ℕ} (hlt : tk < tl)
    (hfin : tl + Γ.infLen < period Γ.straight z) {q : ℕ} (hq : 0 < q) (ret : ℕ → D)
    (hS : ∀ j < q, Γ.curve (ret j) ≠ Γ.S)
    (h0 : ret 0 = Γ.σ (Γ.noC z tl))
    (hstep : ∀ j, j + 1 < q → Γ.crossingOf (Γ.α (ret j)) = Γ.crossingOf (ret (j + 1)))
    (hlast : Γ.α (ret (q - 1)) = Γ.σ (Γ.noC z tk))
    (hmid : ∀ j, 0 < j → j < q → ¬ Γ.OnSweep (Γ.crossingOf (ret j)))
    (hdist : ∀ i < q, ∀ j < q, Γ.segmentOf (ret i) = Γ.segmentOf (ret j) → i = j) :
    ∃ (r : Γ.Cell → ZMod 2) (Lid : Finset D), CCut Γ z tk tl r Lid ∧
      ∀ y, y ∈ Lid ↔ ∃ j < q, y = ret j ∨ y = Γ.α (ret j) := by
  classical
  set Lid := (range q).image ret ∪ (range q).image (fun j => Γ.α (ret j)) with hLdef
  have hLid : ∀ y, y ∈ Lid ↔ ∃ j < q, y = ret j ∨ y = Γ.α (ret j) := by
    intro y
    simp only [hLdef, mem_union, mem_image, mem_range]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨j, hj, Or.inl rfl⟩
      · exact ⟨j, hj, Or.inr rfl⟩
    · rintro ⟨j, hj, rfl | rfl⟩
      · exact Or.inl ⟨j, hj, rfl⟩
      · exact Or.inr ⟨j, hj, rfl⟩
  obtain ⟨r, hcut, hbase⟩ := c_lid_cut hz hlt (by omega) hq ret hS
    (by rw [h0, j_crossingOf_σ]) hstep (by rw [hlast, j_crossingOf_σ]) hdist Lid hLid
  refine ⟨r, Lid, ⟨hz, hlt, hfin, hcut, hbase, fun t ht => ?_⟩, hLid⟩
  have hon : Γ.OnSweep (Γ.crossingOf (Γ.σ (Γ.noC z t))) := by
    rw [j_crossingOf_σ]; exact no_S_mem_noC hz t
  rw [hLid]
  constructor
  · rintro ⟨j, hj, h | h⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [h0] at h; exact Or.inr (c_σ_noC_inj ht (by omega) h)
      · exact absurd (h ▸ hon) (hmid j hj0 hj)
    · by_cases hj1 : j + 1 < q
      · exfalso
        apply hmid (j + 1) (by omega) hj1
        rw [← hstep j hj1, ← h]; exact hon
      · have : j = q - 1 := by omega
        subst this
        rw [hlast] at h
        exact Or.inl (c_σ_noC_inj ht (by omega) h)
  · rintro (rfl | rfl)
    · exact ⟨q - 1, by omega, Or.inr hlast.symm⟩
    · exact ⟨0, hq, Or.inl h0.symm⟩

open Classical in
/-- The ends of a loop `γ ≠ S`. -/
theorem p_loop_data {z : D} (hz : Γ.infStart = some z) {γ : Fin n} (hγS : γ ≠ Γ.S)
    (hloop : Γ.IsLoop γ) :
    ∃ tk tl, tk < tl ∧ tl + Γ.infLen < period Γ.straight z ∧
      Γ.LoopEnds γ (tk + 1) (tl + 1) ∧
      ∀ t < period Γ.straight z, γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) ↔ t = tk ∨ t = tl := by
  set F := univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve γ x) with hF
  have hc : F.card = 2 := hloop
  obtain ⟨x1, x2, hx12, hFe⟩ := card_eq_two.1 hc
  have hm1 : x1 ∈ F := by rw [hFe]; simp
  have hm2 : x2 ∈ F := by rw [hFe]; simp
  obtain ⟨hf1, hc1⟩ := (mem_filter.1 hm1).2
  obtain ⟨hf2, hc2⟩ := (mem_filter.1 hm2).2
  obtain ⟨t1, ht1, rfl⟩ := no_onSweep_noC hz hf1.1
  obtain ⟨t2, ht2, rfl⟩ := no_onSweep_noC hz hf2.1
  have hfin1 := (no_noC_fin hz ht1).1 hf1
  have hfin2 := (no_noC_fin hz ht2).1 hf2
  have hne : t1 ≠ t2 := fun h => hx12 (by rw [h])
  have hends : Γ.sweepEnds γ = {t1 + 1, t2 + 1} := by
    unfold sweepEnds
    rw [← hF, hFe, image_insert, image_singleton, no_noC_pos hz ht1, no_noC_pos hz ht2]
  have hiff : ∀ t < period Γ.straight z, γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) ↔
      t = t1 ∨ t = t2 := by
    intro t ht
    constructor
    · intro hm
      have hf := no_loop_fin hloop hγS (no_S_mem_noC hz t) hm
      have hx : Γ.crossingOf (Γ.noC z t) ∈ F := mem_filter.2 ⟨mem_univ _, hf, hm⟩
      rw [hFe, mem_insert, mem_singleton] at hx
      rcases hx with h | h
      · exact Or.inl (no_noC_inj hz ht ht1 h)
      · exact Or.inr (no_noC_inj hz ht ht2 h)
    · rintro (rfl | rfl)
      · exact hc1
      · exact hc2
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨t1, t2, h, hfin2, ⟨hloop, by omega, hends⟩, hiff⟩
  · exact ⟨t2, t1, h, hfin1, ⟨hloop, by omega, by rw [hends, pair_comm]⟩,
      fun t ht => (hiff t ht).trans or_comm⟩

/-- The region cut of the loop `γ` (closed walk `S[k, l]` + the upper arc of `γ`). -/
theorem p_gamma_cut {z : D} (hz : Γ.infStart = some z) {γ : Fin n} (hγS : γ ≠ Γ.S)
    {tk tl : ℕ} (hlt : tk < tl) (hfin : tl + Γ.infLen < period Γ.straight z)
    (hiff : ∀ t < period Γ.straight z, γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) ↔
      t = tk ∨ t = tl) :
    ∃ (rγ : Γ.Cell → ZMod 2) (Lγ : Finset D), CCut Γ z tk tl rγ Lγ ∧
      (∀ y ∈ Lγ, Γ.curve y = γ) ∧ (∀ y, Γ.Above y → Γ.curve y = γ → y ∈ Lγ) := by
  obtain ⟨L, t2, A, hca, hc2⟩ := p_arc_exists hz hγS (t1 := tl) (by omega)
    ((hiff tl (by omega)).2 (Or.inr rfl))
  have ht2 : t2 = tk := by
    rcases (hiff t2 A.t2P).1 hc2 with h | h
    · exact h
    · exact absurd h.symm A.ne
  subst ht2
  set g0 := Γ.σ (Γ.noC z tl)
  have hLP := A.hLP
  obtain ⟨rγ, Lγ, hC, hL⟩ := p_ccut hz hlt hfin (q := L + 1) (Nat.succ_pos _)
    (fun i => (Γ.straight ^ i) g0)
    (fun j _ => by rw [no_curve_pow, hca]; exact hγS) (by rw [pow_zero, Perm.one_apply])
    (fun j _ => by rw [← no_crossingOf_α_straight, ← no_pow_succ])
    (by rw [Nat.add_sub_cancel, A.hL, j_α_α])
    (fun j hj0 hj => by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [no_pow_succ, no_crossingOf_α_straight]
      exact A.hnos j' (by omega))
    (fun i hi j hj h => gk_seg_pow_inj (by omega) (by omega) h)
  refine ⟨rγ, Lγ, hC, fun y hy => ?_, fun y hy hyc => ?_⟩
  · obtain ⟨j, -, rfl | rfl⟩ := (hL y).1 hy
    · rw [no_curve_pow, hca]
    · rw [j_curve_α, no_curve_pow, hca]
  · obtain ⟨q, hq, h | h⟩ := A.hcov y hy (hyc.trans hca.symm)
    · exact (hL y).2 ⟨q, by omega, Or.inl h.symm⟩
    · exact (hL y).2 ⟨q, by omega, Or.inr (by rw [h, j_α_α])⟩

/-- SH p. 324: removing `γ` leaves an empty triangle and `γ` crosses one leg twice. The foot `j`
of that leg: the dart `a0` of `δ = γ(j)` going up from `j`, whose first two crossings are with
`γ`. -/
theorem p_tri_a0 (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) (X : Γ.Removal {γ}) {d' : X.D'}
    (ht : X.Γ'.EmptyTriAt d') :
    ∃ a0, Γ.Above a0 ∧ Γ.IsFinVertex (Γ.crossingOf a0) ∧ Γ.curve a0 ≠ γ ∧
      γ ∈ Γ.curves (Γ.crossingOf (Γ.α a0)) ∧
      γ ∈ Γ.curves (Γ.crossingOf (Γ.α (Γ.straight a0))) := by
  have h37 := hΓ.lemma_3_7 X (Or.inr ht)
  have T := gk_tri X ht h37
  have hfin := f_finSeg_fin ht.1
  have hleg := hΓ.removal_one_leg hγ X ht
  generalize X.hits (X.Γ'.σ d') = k₁ at T hleg
  generalize X.hits (X.Γ'.φ (X.Γ'.σ d')) = k₂ at T hleg
  set b := X.ι (X.Γ'.φ (X.Γ'.σ d'))
  rcases hleg with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · refine ⟨X.ι (X.Γ'.σ d'), X.r_above (no_above_σ ht.1.1), ?_, T.c1γ, ?_, ?_⟩
    · have := (X.r_finVertex (X.Γ'.crossingOf (X.Γ'.σ d'))).1
        (by rw [j_crossingOf_σ]; exact hfin.1)
      exact this
    · have := T.del1 0 (by omega)
      rw [pow_zero, Perm.one_apply] at this
      have h := ab_mem_curves_σ (Γ := Γ) (Γ.α (X.ι (X.Γ'.σ d')))
      rwa [this] at h
    · have := T.del1 1 (by omega)
      rw [pow_one] at this
      have h := ab_mem_curves_σ (Γ := Γ) (Γ.α (Γ.straight (X.ι (X.Γ'.σ d'))))
      rwa [this] at h
  · set y := (Γ.straight ^ 2) b
    have hy : Γ.σ (Γ.α y) = Γ.α (X.ι d') := T.hc
    have hcy : Γ.curve y = Γ.curve b := no_curve_pow _ _
    have hup : Γ.Up (Γ.cellOf (Γ.α (X.ι d'))) := by
      have := X.isRemoval.side (X.Γ'.α d')
      rw [h37] at this
      show Γ.side _ = 1
      rw [← this]; exact ht.1.1.2
    have hyA : Γ.Above y := by
      refine ⟨by rw [hcy]; exact T.c2S, ?_⟩
      unfold Up
      rw [← gk_cell_σα, hy]; exact hup
    refine ⟨Γ.α y, ab_above_α hyA, ?_, ?_, ?_, ?_⟩
    · rw [← j_crossingOf_σ, hy, ← h37]
      exact X.r_finVertex (X.Γ'.crossingOf (X.Γ'.α d')) |>.1 hfin.2
    · rw [j_curve_α, hcy]; exact T.c2γ
    · have := T.del2 1 (by omega)
      rw [j_α_α, show y = Γ.straight ((Γ.straight ^ 1) b) from no_pow_succ _ _,
        no_crossingOf_α_straight, ← this]
      exact ab_mem_curves_σ _
    · have := T.del2 0 (by omega)
      rw [pow_zero, Perm.one_apply] at this
      have hs : Γ.straight (Γ.α y) = Γ.α (Γ.straight b) := by
        rw [r_straight_α]
        congr 1
        rw [show y = Γ.straight (Γ.straight b) by
          show (Γ.straight ^ 2) b = _; rw [pow_two, Perm.mul_apply]]
        exact r_inv_apply _ _
      rw [hs, j_α_α, no_crossingOf_α_straight, ← this]
      exact ab_mem_curves_σ _

/-- The other curve at a crossing. -/
theorem p_other {x : D} {c : Fin n} (hc : c ∈ Γ.curves (Γ.crossingOf x)) (hne : Γ.curve x ≠ c) :
    Γ.curve (Γ.σ x) = c := by
  rw [j_curves_crossingOf, mem_insert, mem_singleton] at hc
  rcases hc with h | h
  · exact absurd h.symm hne
  · exact h.symm

/-- `β`: the part of `γ` from its vertex `tE` up to `u`. -/
theorem p_beta {z : D} (hz : Γ.infStart = some z) {γ : Fin n} (hγS : γ ≠ Γ.S) {tE : ℕ}
    (htE : tE < period Γ.straight z) (hγE : γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z tE)))
    {a0 : D} (ha0 : Γ.Above a0) (hu : Γ.curve (Γ.σ (Γ.α a0)) = γ)
    (huS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α a0))) :
    ∃ m, 0 < m ∧ m ≤ period Γ.straight (Γ.σ (Γ.noC z tE)) ∧
      (∀ i < m, Γ.Above ((Γ.straight ^ i) (Γ.σ (Γ.noC z tE)))) ∧
      Γ.crossingOf (Γ.α ((Γ.straight ^ (m - 1)) (Γ.σ (Γ.noC z tE)))) =
        Γ.crossingOf (Γ.α a0) := by
  obtain ⟨L, t2, B, hcb, -⟩ := p_arc_exists hz hγS htE hγE
  set b0 := Γ.σ (Γ.noC z tE)
  have hLP := B.hLP
  set e := Γ.σ (Γ.α a0)
  have heA : Γ.Above e := ⟨by rw [hu]; exact hγS, by unfold Up; rw [gk_cell_σα]; exact ha0.2⟩
  have hex : Γ.crossingOf e = Γ.crossingOf (Γ.α a0) := j_crossingOf_σ _ _
  obtain ⟨q, hq, h | h⟩ := B.hcov e heA (hu.trans hcb.symm)
  · rcases Nat.eq_zero_or_pos q with rfl | hq0
    · exfalso; apply huS
      rw [← hex, ← h, pow_zero, Perm.one_apply, j_crossingOf_σ]; exact no_S_mem_noC hz tE
    · refine ⟨q, hq0, by omega, fun i hi => B.hall i (by omega), ?_⟩
      rw [← hex, ← h, ← no_crossingOf_α_straight, ← no_pow_succ, Nat.sub_add_cancel hq0]
  · have hqL : q < L := by
      refine lt_of_le_of_ne hq fun hqL => huS ?_
      rw [← hex, ← j_α_α Γ e, ← h, hqL, B.hL, j_α_α, j_crossingOf_σ]
      exact no_S_mem_noC hz t2
    refine ⟨q + 1, by omega, by omega, fun i hi => B.hall i (by omega), ?_⟩
    rw [Nat.add_sub_cancel, h, j_α_α, hex]

/-- The crossings of `β` before `u` are not on `S`. -/
theorem p_beta_not_S {b0 a0 : D} {m : ℕ} (hβA : ∀ i < m, Γ.Above ((Γ.straight ^ i) b0))
    (hu : Γ.crossingOf (Γ.α ((Γ.straight ^ (m - 1)) b0)) = Γ.crossingOf (Γ.α a0))
    (huS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α a0))) {i : ℕ} (hi : i < m) :
    ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ((Γ.straight ^ i) b0))) := by
  by_cases h : i + 1 < m
  · intro hS
    have h1 := hβA (i + 1) h
    rw [no_pow_succ] at h1
    exact no_exit (hβA i (by omega)) hS h1
  · rw [show i = m - 1 by omega, hu]; exact huS

end SConf

end Pca.Sweep
