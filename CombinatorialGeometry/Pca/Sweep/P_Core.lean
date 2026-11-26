/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package P: the bounded component of Lemma 3.11 and the curves kept by the surgery

`PSurg` collects the data of `doc/pca/sweep.md`, steps 1-2: the loop `γ` with ends `tk < tl`
and its region cut `rγ`; the segment `a0 = ⟨j, u⟩` of `δ = γ(j)`; the part `β` of `γ` from its end
`tE` next to `j` to `u` (`straight^i b0`, `i < m`); the cut `r` of the bounded component `R`
(`r = 1` above the edges `[tA, tB)`, `{tA, tB} = {tj, tE}`), with lid `{a0, α a0} ∪ β`.

`PSurg.meets`: every curve with a dart above `S` in `R` meets `S` at a vertex between `tA` and
`tB`, or is a loop inside `γ` (step 4, last item).
-/
import Pca.Sweep.P_Arc

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- The data of the surgery (module doc). -/
structure PSurg (Γ : SConf n D) (γ δ : Fin n) (z : D) (tk tl tA tB tj tE m : ℕ)
    (rγ r : Γ.Cell → ZMod 2) (Lγ Lid : Finset D) (a0 b0 : D) : Prop where
  hz : Γ.infStart = some z
  hγl : Γ.LoopEnds γ (tk + 1) (tl + 1)
  cγ : CCut Γ z tk tl rγ Lγ
  hLγ : ∀ y ∈ Lγ, Γ.curve y = γ
  hLγ' : ∀ y, Γ.Above y → Γ.curve y = γ → y ∈ Lγ
  cR : CCut Γ z tA tB r Lid
  hj : (tj = tA ∧ tE = tB) ∨ (tj = tB ∧ tE = tA)
  ha0 : a0 = Γ.σ (Γ.noC z tj)
  hb0 : b0 = Γ.σ (Γ.noC z tE)
  hδ : Γ.curve a0 = δ
  hγb : Γ.curve b0 = γ
  hδγ : δ ≠ γ
  hm : 0 < m
  hmP : m ≤ period Γ.straight b0
  hβA : ∀ i < m, Γ.Above ((Γ.straight ^ i) b0)
  hu : Γ.crossingOf (Γ.α ((Γ.straight ^ (m - 1)) b0)) = Γ.crossingOf (Γ.α a0)
  hLid : ∀ y ∈ Lid, y = a0 ∨ y = Γ.α a0 ∨
    ∃ i < m, y = (Γ.straight ^ i) b0 ∨ y = Γ.α ((Γ.straight ^ i) b0)
  hβL : ∀ i < m, (Γ.straight ^ i) b0 ∈ Lid
  hs0 : r (Γ.cellOf b0) + rγ (Γ.cellOf b0) = 1

open Classical in
/-- The curves removed by the surgery: no dart above `S` in the bounded component. -/
noncomputable def pRem (Γ : SConf n D) (r : Γ.Cell → ZMod 2) : Finset (Fin n) :=
  univ.filter (fun c => c ≠ Γ.S ∧ ¬ ∃ w, Γ.curve w = c ∧ Γ.Above w ∧ r (Γ.cellOf w) = 1)

theorem p_mem_rem {r : Γ.Cell → ZMod 2} {c : Fin n} :
    c ∈ Γ.pRem r ↔ c ≠ Γ.S ∧ ¬ ∃ w, Γ.curve w = c ∧ Γ.Above w ∧ r (Γ.cellOf w) = 1 := by
  classical
  unfold pRem
  simp only [mem_filter, mem_univ, true_and]

theorem p_S_not_mem_rem {r : Γ.Cell → ZMod 2} : Γ.S ∉ Γ.pRem r :=
  fun h => (p_mem_rem.1 h).1 rfl

theorem p_witness {r : Γ.Cell → ZMod 2} {c : Fin n} (h : c ∉ Γ.pRem r) (hS : c ≠ Γ.S) :
    ∃ w, Γ.curve w = c ∧ Γ.Above w ∧ r (Γ.cellOf w) = 1 := by
  by_contra hn
  exact h (p_mem_rem.2 ⟨hS, hn⟩)

namespace PSurg

variable {γ δ : Fin n} {z : D} {tk tl tA tB tj tE m : ℕ} {rγ r : Γ.Cell → ZMod 2}
  {Lγ Lid : Finset D} {a0 b0 : D}
  (H : PSurg Γ γ δ z tk tl tA tB tj tE m rγ r Lγ Lid a0 b0)
include H

theorem hP : tB + Γ.infLen < period Γ.straight z := H.cR.hfin

theorem hPγ : tl + Γ.infLen < period Γ.straight z := H.cγ.hfin

theorem γS : γ ≠ Γ.S := by rw [← H.hγb, H.hb0]; exact (no_above_σ (no_noC_sweep H.hz _)).1

theorem δS : δ ≠ Γ.S := by rw [← H.hδ, H.ha0]; exact (no_above_σ (no_noC_sweep H.hz _)).1

theorem a0A : Γ.Above a0 := by rw [H.ha0]; exact no_above_σ (no_noC_sweep H.hz _)

theorem b0A : Γ.Above b0 := by rw [H.hb0]; exact no_above_σ (no_noC_sweep H.hz _)

theorem tjAB : tA ≤ tj ∧ tj ≤ tB := by have := H.cR.hlt; rcases H.hj with h | h <;> omega

theorem tEAB : tA ≤ tE ∧ tE ≤ tB := by have := H.cR.hlt; rcases H.hj with h | h <;> omega

theorem γ_mem_E : γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z tE)) :=
  (p_curve_σ_iff (no_noC_sweep H.hz tE) H.γS).1 (by rw [← H.hb0]; exact H.hγb)

theorem δ_mem_j : δ ∈ Γ.curves (Γ.crossingOf (Γ.noC z tj)) :=
  (p_curve_σ_iff (no_noC_sweep H.hz tj) H.δS).1 (by rw [← H.ha0]; exact H.hδ)

theorem γ_mem_k : γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z tk)) := by
  have hl := (H.cγ.lidσ tk (by have := H.hPγ; have := H.cγ.hlt; omega)).2 (Or.inl rfl)
  exact (p_curve_σ_iff (no_noC_sweep H.hz tk) H.γS).1 (H.hLγ _ hl)

theorem γ_mem_l : γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z tl)) := by
  have hl := (H.cγ.lidσ tl (by have := H.hPγ; omega)).2 (Or.inr rfl)
  exact (p_curve_σ_iff (no_noC_sweep H.hz tl) H.γS).1 (H.hLγ _ hl)

theorem βcurve (i : ℕ) : Γ.curve ((Γ.straight ^ i) b0) = γ := by rw [no_curve_pow, H.hγb]

/-- The crossing `u` is a crossing of `δ` and `γ`. -/
theorem curves_u : Γ.curves (Γ.crossingOf (Γ.α a0)) = {δ, γ} := by
  have h1 : Γ.curves (Γ.crossingOf (Γ.α a0)) = {δ, Γ.curve (Γ.σ (Γ.α a0))} := by
    rw [j_curves_crossingOf, j_curve_α, H.hδ]
  have hγ : γ ∈ Γ.curves (Γ.crossingOf (Γ.α a0)) := by
    rw [← H.hu, j_curves_crossingOf, j_curve_α, H.βcurve]; exact mem_insert_self _ _
  rw [h1] at hγ ⊢
  rw [mem_insert, mem_singleton] at hγ
  rcases hγ with h | h
  · exact absurd h.symm H.hδγ
  · rw [← h]

theorem u_not_S : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α a0)) := by
  change Γ.S ∉ _
  rw [H.curves_u, mem_insert, mem_singleton]
  rintro (h | h)
  · exact H.δS h.symm
  · exact H.γS h.symm

theorem β_not_S {i : ℕ} (hi : i + 1 < m) :
    ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ((Γ.straight ^ i) b0))) := by
  intro hS
  have h1 := H.hβA (i + 1) hi
  rw [no_pow_succ] at h1
  exact no_exit (H.hβA i (by omega)) hS h1

theorem β_not_S' {i : ℕ} (hi : i < m) :
    ¬ Γ.OnSweep (Γ.crossingOf (Γ.α ((Γ.straight ^ i) b0))) := by
  by_cases h : i + 1 < m
  · exact H.β_not_S h
  · rw [show i = m - 1 by omega, H.hu]; exact H.u_not_S

/-- Along `β`, before `u`, no boundary dart of either cut is crossed. -/
theorem β_step {i : ℕ} (hi : i + 1 < m) :
    Γ.σ (Γ.α ((Γ.straight ^ i) b0)) ∉ Lid ∧ Γ.σ (Γ.α ((Γ.straight ^ i) b0)) ∉ Lγ := by
  have hne : Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ i) b0))) ≠ γ := by
    have := no_curve_σ_ne (Γ := Γ) (Γ.α ((Γ.straight ^ i) b0))
    rwa [j_curve_α, H.βcurve] at this
  refine ⟨fun hl => ?_, fun hl => hne (H.hLγ _ hl)⟩
  rcases H.hLid _ hl with h | h | ⟨i', -, h | h⟩
  · apply H.β_not_S hi
    rw [← j_crossingOf_σ, h, H.ha0, j_crossingOf_σ]; exact no_S_mem_noC H.hz tj
  · have hx : Γ.crossingOf (Γ.α ((Γ.straight ^ i) b0)) =
        Γ.crossingOf (Γ.α ((Γ.straight ^ (m - 1)) b0)) := by
      rw [← j_crossingOf_σ, h, H.hu]
    have hmP := H.hmP
    exact f_cross_ne (h := b0) (by omega) (by omega) hx
  · exact hne (by rw [h, H.βcurve])
  · exact hne (by rw [h, j_curve_α, H.βcurve])

/-- On `β`, `r + rγ = 1` (walk along `β` from `E`). -/
theorem s_beta {i : ℕ} (hi : i < m) :
    r (Γ.cellOf ((Γ.straight ^ i) b0)) + rγ (Γ.cellOf ((Γ.straight ^ i) b0)) = 1 ∧
      r (Γ.cellOf (Γ.α ((Γ.straight ^ i) b0))) +
        rγ (Γ.cellOf (Γ.α ((Γ.straight ^ i) b0))) = 1 := by
  have hcut : ∀ {g : Γ.Cell → ZMod 2} {F : Finset D}, (∀ y, Γ.curve y ≠ Γ.S →
      g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = if y ∈ F then 1 else 0) → ∀ i, i + 1 < m →
      Γ.σ (Γ.α ((Γ.straight ^ i) b0)) ∉ F →
      g (Γ.cellOf ((Γ.straight ^ (i + 1)) b0)) = g (Γ.cellOf ((Γ.straight ^ i) b0)) := by
    intro g F hg i hi hF
    rw [no_pow_succ, no_walk_straight (r := g)
      (f := fun y => g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y))) (fun y => rfl)]
    have hc : Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ i) b0))) ≠ Γ.S := by
      intro h
      apply H.β_not_S hi
      change Γ.S ∈ Γ.curves _
      rw [j_curves_crossingOf, h]; exact mem_insert_of_mem (mem_singleton_self _)
    rw [hg _ hc, if_neg hF, add_zero]
  have h1 : ∀ i < m, r (Γ.cellOf ((Γ.straight ^ i) b0)) + rγ (Γ.cellOf ((Γ.straight ^ i) b0)) =
      1 := by
    intro i
    induction i with
    | zero => intro _; rw [pow_zero, Perm.one_apply]; exact H.hs0
    | succ i ih =>
      intro hi
      obtain ⟨hl, hg⟩ := H.β_step hi
      rw [hcut (fun y hy => H.cR.cut y hy) i hi hl, hcut (fun y hy => H.cγ.cut y hy) i hi hg]
      exact ih (by omega)
  refine ⟨h1 i hi, ?_⟩
  have hS : Γ.curve ((Γ.straight ^ i) b0) ≠ Γ.S := (H.hβA i hi).1
  have e1 := H.cR.cut _ hS
  have e2 := H.cγ.cut _ hS
  rw [if_pos (H.hβL i hi)] at e1
  rw [if_pos (H.hLγ' _ (H.hβA i hi) (H.βcurve i))] at e2
  rw [j_zmod2_eq_add_of_add_eq e1, j_zmod2_eq_add_of_add_eq e2]
  rw [add_add_add_comm, h1 i hi]; decide

/-- A lid dart met by a curve other than `S`, `γ`, `δ` is a dart of `β`. -/
theorem lid_cross {c : Fin n} (hcS : c ≠ Γ.S) (hcγ : c ≠ γ) (hcδ : c ≠ δ) {y : D}
    (hy : Γ.curve y = c) (hl : Γ.σ (Γ.α y) ∈ Lid) :
    ∃ i < m, Γ.σ (Γ.α y) = (Γ.straight ^ i) b0 ∨ Γ.σ (Γ.α y) = Γ.α ((Γ.straight ^ i) b0) := by
  have hcm : c ∈ Γ.curves (Γ.crossingOf (Γ.σ (Γ.α y))) := by
    rw [j_crossingOf_σ, j_curves_crossingOf, j_curve_α, hy]; exact mem_insert_self _ _
  rcases H.hLid _ hl with h | h | h
  · exfalso
    rw [h, H.ha0, j_crossingOf_σ] at hcm
    have := no_mem_curves (no_S_mem_noC H.hz tj) H.δ_mem_j H.δS
    rw [this, mem_insert, mem_singleton] at hcm
    rcases hcm with h' | h'
    · exact hcδ h'
    · exact hcS h'
  · exfalso
    rw [h, H.curves_u, mem_insert, mem_singleton] at hcm
    rcases hcm with h' | h'
    · exact hcδ h'
    · exact hcγ h'
  · exact h

/-- Every curve with a dart above `S` in the bounded component meets the sweep between `tA` and
`tB`, or is a loop inside `γ`. -/
theorem meets (h34 : ∀ c, Γ.Present c → Γ.MeetsSweep c) {c : Fin n} (hcS : c ≠ Γ.S)
    (hc : c ∉ Γ.pRem r) :
    (∃ t, tA ≤ t ∧ t ≤ tB ∧ c ∈ Γ.curves (Γ.crossingOf (Γ.noC z t))) ∨ Γ.Inside c γ := by
  classical
  have hP := H.hP
  have hPγ := H.hPγ
  have hAB := H.cR.hlt
  have hkl := H.cγ.hlt
  by_cases hcγ : c = γ
  · subst hcγ; exact Or.inl ⟨tE, H.tEAB.1, H.tEAB.2, H.γ_mem_E⟩
  by_cases hcδ : c = δ
  · subst hcδ; exact Or.inl ⟨tj, H.tjAB.1, H.tjAB.2, H.δ_mem_j⟩
  obtain ⟨w, hwc, hwA, hwr⟩ := p_witness hc hcS
  obtain ⟨x, hxf, hxc⟩ := h34 c ⟨hcS, w, hwc, hwA⟩
  obtain ⟨t1, ht1, rfl⟩ := no_onSweep_noC H.hz hxf.1
  obtain ⟨L, t2, A, hca, hc2⟩ := p_arc_exists H.hz hcS ht1 hxc
  set a := Γ.σ (Γ.noC z t1)
  -- the cut `r` at the two ends
  have hrv : ∀ t, t < period Γ.straight z →
      r (Γ.upperCell (Γ.noC z t)) = if tA ≤ t ∧ t < tB then 1 else 0 :=
    fun t ht => c_sweep H.cR ht
  have hgv : ∀ t, t < period Γ.straight z →
      rγ (Γ.upperCell (Γ.noC z t)) = if tk ≤ t ∧ t < tl then 1 else 0 :=
    fun t ht => c_sweep H.cγ ht
  have hlidc : ∀ y ∈ Lid, Γ.curve y = δ ∨ Γ.curve y = γ := by
    intro y hy
    rcases H.hLid y hy with h | h | ⟨i, -, h | h⟩
    · left; rw [h, H.hδ]
    · left; rw [h, j_curve_α, H.hδ]
    · right; rw [h, H.βcurve]
    · right; rw [h, j_curve_α, H.βcurve]
  have hnl : ∀ y, Γ.curve y = c → y ∉ Lid := by
    intro y hy hl
    rcases hlidc y hl with h | h
    · exact hcδ (hy.symm.trans h)
    · exact hcγ (hy.symm.trans h)
  have hnlγ : ∀ y, Γ.curve y = c → y ∉ Lγ := fun y hy hl => hcγ (hy.symm.trans (H.hLγ y hl))
  have hcutR := fun y (hy : Γ.curve y ≠ Γ.S) => H.cR.cut y hy
  have hcutG := fun y (hy : Γ.curve y ≠ Γ.S) => H.cγ.cut y hy
  have hc2' : Γ.curve (Γ.σ (Γ.noC z t2)) = c := by rw [A.curve_end, hca]
  -- the two counts
  set I := fun q => (range q).filter (fun q' => Γ.σ (Γ.α ((Γ.straight ^ q') a)) ∈ Lid)
  set G := fun q => (range q).filter (fun q' => Γ.σ (Γ.α ((Γ.straight ^ q') a)) ∈ Lγ)
  have hIG : ∀ q, I q ⊆ G q := by
    intro q q' hq'
    simp only [I, G, mem_filter] at hq' ⊢
    refine ⟨hq'.1, ?_⟩
    obtain ⟨i, hi, h | h⟩ := H.lid_cross hcS hcγ hcδ (by rw [no_curve_pow]; exact hca) hq'.2
    · rw [h]; exact H.hLγ' _ (H.hβA i hi) (H.βcurve i)
    · rw [h]
      exact H.hLγ' _ (ab_above_α (H.hβA i hi)) (by rw [j_curve_α, H.βcurve])
  have hGL : (G L).card ≤ 2 := A.count_le (Ne.symm (hca ▸ hcγ)) H.hLγ
  have hend_r := A.walk_end hcutR (hnl _ hc2')
  have hend_g := A.walk_end hcutG (hnlγ _ hc2')
  -- the dart `w` lies on the arc
  obtain ⟨qw, hqw, hqw'⟩ := A.hcov w hwA (hwc.trans hca.symm)
  have hrw : r (Γ.cellOf ((Γ.straight ^ qw) a)) = 1 := by
    rcases hqw' with h | h
    · rw [h]; exact hwr
    · rw [h]
      have e := hcutR w hwA.1
      rw [if_neg (hnl w hwc)] at e
      rw [c_zmod2_eq_of_add e]; exact hwr
  have hwalk := A.walk hcutR hqw
  rw [A.cell_start] at hwalk
  by_cases h1 : tA ≤ t1 ∧ t1 < tB
  · exact Or.inl ⟨t1, h1.1, h1.2.le, hxc⟩
  by_cases h2 : tA ≤ t2 ∧ t2 < tB
  · exact Or.inl ⟨t2, h2.1, h2.2.le, hc2⟩
  right
  rw [hrv t1 ht1, if_neg h1] at hwalk hend_r
  rw [hrv t2 A.t2P, if_neg h2] at hend_r
  -- the counts: one lid crossing before `w`, two in all
  have hsub : I qw ⊆ I L := by
    intro q hq; simp only [I, mem_filter, mem_range] at hq ⊢; exact ⟨by omega, hq.2⟩
  have hc1 := card_le_card hsub
  have hc2'' := card_le_card (hIG L)
  have hIqw : (I qw).card = 1 := by
    rw [hrw, zero_add] at hwalk
    have : (I qw).card ≤ 2 := by omega
    interval_cases h : (I qw).card
    · exact absurd hwalk (by decide)
    · rfl
    · exact absurd hwalk (by decide)
  have hIL : (I L).card = 2 := by
    rw [zero_add] at hend_r
    have : (I L).card ≤ 2 := by omega
    interval_cases h : (I L).card
    · omega
    · exact absurd hend_r.symm (by decide)
    · rfl
  have hGI : G L = I L := (eq_of_subset_of_card_le (hIG L) (by omega)).symm
  -- the first lid crossing
  have hne : (I L).Nonempty := card_pos.1 (by omega)
  set q1 := (I L).min' hne
  have hq1 := (I L).min'_mem hne
  have hq1L : q1 < L := by
    have := hq1; simp only [I, mem_filter, mem_range] at this; exact this.1
  have hq1l : Γ.σ (Γ.α ((Γ.straight ^ q1) a)) ∈ Lid := by
    have := hq1; simp only [I, mem_filter] at this; exact this.2
  have hI0 : I q1 = ∅ := by
    ext q
    simp only [I, mem_filter, mem_range, notMem_empty, iff_false, not_and]
    intro hq hl
    have hm : q ∈ I L := by simp only [I, mem_filter, mem_range]; exact ⟨by omega, hl⟩
    have := (I L).min'_le q hm
    omega
  have hG0 : G q1 = ∅ := by
    ext q
    simp only [G, mem_filter, mem_range, notMem_empty, iff_false, not_and]
    intro hq hl
    have hm : q ∈ G L := by simp only [G, mem_filter, mem_range]; exact ⟨by omega, hl⟩
    rw [hGI] at hm
    have := (I L).min'_le q hm
    omega
  have hr1 := A.walk hcutR hq1L.le
  have hg1 := A.walk hcutG hq1L.le
  rw [show (range q1).filter (fun q' => Γ.σ (Γ.α ((Γ.straight ^ q') a)) ∈ Lid) = I q1 from rfl,
    hI0, card_empty, Nat.cast_zero, add_zero, A.cell_start, hrv t1 ht1, if_neg h1] at hr1
  rw [show (range q1).filter (fun q' => Γ.σ (Γ.α ((Γ.straight ^ q') a)) ∈ Lγ) = G q1 from rfl,
    hG0, card_empty, Nat.cast_zero, add_zero, A.cell_start] at hg1
  -- `r + rγ = 1` on `β`
  have hs : r (Γ.cellOf ((Γ.straight ^ q1) a)) + rγ (Γ.cellOf ((Γ.straight ^ q1) a)) = 1 := by
    have hcell : Γ.cellOf ((Γ.straight ^ q1) a) =
        Γ.cellOf (Γ.σ (Γ.α ((Γ.straight ^ q1) a))) := by rw [j_cellOf_σ, j_α_α]
    rw [hcell]
    obtain ⟨i, hi, h | h⟩ := H.lid_cross hcS hcγ hcδ (by rw [no_curve_pow]; exact hca) hq1l
    · rw [h]; exact (H.s_beta hi).1
    · rw [h]; exact (H.s_beta hi).2
  rw [hr1, hg1, zero_add] at hs
  -- both ends of `c` are strictly between `k` and `l`
  have hG2 : ((G L).card : ZMod 2) = 0 := by rw [hGI, hIL]; decide
  rw [show (range L).filter (fun q' => Γ.σ (Γ.α ((Γ.straight ^ q') a)) ∈ Lγ) = G L from rfl,
    hG2, add_zero, hs] at hend_g
  rw [hgv t1 ht1] at hs
  rw [hgv t2 A.t2P] at hend_g
  have e1 : tk ≤ t1 ∧ t1 < tl := by
    by_contra h; rw [if_neg h] at hs; exact absurd hs (by decide)
  have e2 : tk ≤ t2 ∧ t2 < tl := by
    by_contra h; rw [if_neg h] at hend_g; exact absurd hend_g (by decide)
  have hnk : ∀ t, c ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) → t ≠ tk := by
    rintro t hct rfl
    have := no_mem_curves (no_S_mem_noC H.hz _) H.γ_mem_k H.γS
    rw [this, mem_insert, mem_singleton] at hct
    rcases hct with h | h
    · exact hcγ h
    · exact hcS h
  exact p_inside_of_ends H.hz hcS H.hγl hPγ ⟨by have := hnk t1 hxc; omega, e1.2⟩
    ⟨by have := hnk t2 hc2; omega, e2.2⟩ A.ne hxc hc2

end PSurg

end SConf

end Pca.Sweep
