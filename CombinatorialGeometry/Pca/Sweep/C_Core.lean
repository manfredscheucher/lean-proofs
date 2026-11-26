/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package C, core: SH's argument for Lemma 3.6 against a region cut

Data (`CLid`): vertices `k = tk + 1 < l = tl + 1` on the sweep, a set `Lid` of darts above `S`
(the hump, or the two legs of the triangle, in both directions) and a cut `r` of the cells which
changes across `Lid` and across the edges of `S` between `k` and `l` (`r = 1` inside the region).
The curves of the lid run outside the region after leaving it (`lidR`), and the curves through a
crossing of the lid are `S` or lid curves (`lidX`).

SH (p. 319): remove every curve that has no dart inside the region off the lid (`cR`), i.e. keep
the curves `γ(k+1), …, γ(l−1)` (`c_kept`: a kept curve lies inside). By minimality the result
`Γ'` is not stuck. It is not finished (a curve with a vertex strictly between `k` and `l` stays,
and it is not a ray); a loop cannot be taken (Lemma 3.4); an empty hump or triangle of `Γ'` above
the finite edge `d'` is a cell of `Γ` (`c_transfer`: none of its segments passes a deleted
crossing), so `Γ` can make progress: contradiction.
-/
import Pca.Sweep.L34
import Pca.Sweep.NO_Sweep

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- The cut of a hump or triangle region `⟨k, …, l⟩` (see the module doc). -/
structure CCut (Γ : SConf n D) (z : D) (tk tl : ℕ) (r : Γ.Cell → ZMod 2) (Lid : Finset D) :
    Prop where
  hz : Γ.infStart = some z
  hlt : tk < tl
  hfin : tl + Γ.infLen < period Γ.straight z
  cut : ∀ y, Γ.curve y ≠ Γ.S → r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if y ∈ Lid then 1 else 0
  base : r (Γ.upperCell (Γ.noC z tk)) = 1
  lidσ : ∀ t < period Γ.straight z, (Γ.σ (Γ.noC z t) ∈ Lid ↔ t = tk ∨ t = tl)

/-- The region data of a hump or triangle `⟨k, …, l⟩` for Lemma 3.6 (see the module doc). -/
structure CLid (Γ : SConf n D) (z : D) (tk tl : ℕ) (r : Γ.Cell → ZMod 2) (Lid : Finset D) : Prop
    extends CCut Γ z tk tl r Lid where
  above : ∀ y ∈ Lid, Γ.Above y
  lidR : ∀ y ∈ Lid, ∀ w, Γ.curve w = Γ.curve y → Γ.Above w → w ∉ Lid → r (Γ.cellOf w) = 0
  lidX : ∀ y ∈ Lid, ∀ w, Γ.crossingOf w = Γ.crossingOf y →
    Γ.curve w = Γ.S ∨ ∃ y' ∈ Lid, Γ.curve y' = Γ.curve w

/-- A dart inside the region, off the lid. -/
def CIn (Γ : SConf n D) (r : Γ.Cell → ZMod 2) (Lid : Finset D) (w : D) : Prop :=
  Γ.Above w ∧ w ∉ Lid ∧ r (Γ.cellOf w) = 1

open Classical in
/-- The removed curves: no dart inside the region off the lid. -/
noncomputable def cR (Γ : SConf n D) (r : Γ.Cell → ZMod 2) (Lid : Finset D) : Finset (Fin n) :=
  univ.filter (fun γ => γ ≠ Γ.S ∧ ¬ ∃ w, Γ.curve w = γ ∧ Γ.CIn r Lid w)

theorem c_mem_cR {r : Γ.Cell → ZMod 2} {Lid : Finset D} {γ : Fin n} :
    γ ∈ Γ.cR r Lid ↔ γ ≠ Γ.S ∧ ¬ ∃ w, Γ.curve w = γ ∧ Γ.CIn r Lid w := by
  classical
  unfold cR
  simp only [mem_filter, mem_univ, true_and]

theorem c_S_not_mem {r : Γ.Cell → ZMod 2} {Lid : Finset D} : Γ.S ∉ Γ.cR r Lid :=
  fun h => (c_mem_cR.1 h).1 rfl

theorem c_witness {r : Γ.Cell → ZMod 2} {Lid : Finset D} {γ : Fin n} (h : γ ∉ Γ.cR r Lid)
    (hS : γ ≠ Γ.S) : ∃ w, Γ.curve w = γ ∧ Γ.CIn r Lid w := by
  by_contra hn
  exact h (c_mem_cR.2 ⟨hS, hn⟩)

theorem c_zmod2_eq_of_add {a b : ZMod 2} (h : a + b = 0) : b = a := by
  have := j_zmod2_eq_add_of_add_eq h
  rw [this, add_zero]

theorem c_curve_σ_ne_S {y : D} (hy : Γ.curve y = Γ.S) : Γ.curve (Γ.σ y) ≠ Γ.S :=
  hy ▸ no_curve_σ_ne y

theorem c_curve_φ_ne (y : D) : Γ.curve (Γ.φ y) ≠ Γ.curve y := by
  rw [j_φ_apply]
  have := no_curve_σ_ne (Γ := Γ) (Γ.α y)
  rwa [j_curve_α] at this

section Core

variable {z : D} {tk tl : ℕ} {r : Γ.Cell → ZMod 2} {Lid : Finset D}

/-- Walking along the upper side of `S`. -/
theorem c_step (h : CCut Γ z tk tl r Lid) (t : ℕ) :
    r (Γ.upperCell (Γ.noC z (t + 1))) = r (Γ.upperCell (Γ.noC z t)) +
      if Γ.σ (Γ.noC z (t + 1)) ∈ Lid then 1 else 0 := by
  have hw := no_walk_sweep (Γ := Γ) (r := r)
    (f := fun y => r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y))) (fun y => rfl) (Γ.noC z t)
  rw [no_noC_straight] at hw
  unfold upperCell
  rw [hw, h.cut _ (c_curve_σ_ne_S (no_noC_sweep h.hz (t + 1)).1)]

/-- (F1) The value of the cut above the edges of `S`. -/
theorem c_sweep (h : CCut Γ z tk tl r Lid) {t : ℕ} (ht : t < period Γ.straight z) :
    r (Γ.upperCell (Γ.noC z t)) = if tk ≤ t ∧ t < tl then 1 else 0 := by
  have hP := h.hfin
  have hlt := h.hlt
  have hstep : ∀ t, t + 1 < period Γ.straight z →
      r (Γ.upperCell (Γ.noC z (t + 1))) = r (Γ.upperCell (Γ.noC z t)) +
        if t + 1 = tk ∨ t + 1 = tl then 1 else 0 := by
    intro t ht
    rw [c_step h, if_congr (h.lidσ (t + 1) ht) rfl rfl]
  have hup : ∀ j, tk + j < period Γ.straight z →
      r (Γ.upperCell (Γ.noC z (tk + j))) = if tk + j < tl then 1 else 0 := by
    intro j
    induction j with
    | zero => intro _; rw [add_zero, h.base, if_pos hlt]
    | succ j ih =>
      intro hj
      rw [← add_assoc, hstep (tk + j) (by omega), ih (by omega)]
      split_ifs <;> first | decide | (exfalso; omega)
  by_cases htk : tk ≤ t
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le htk
    rw [hup j ht]
    split_ifs <;> first | rfl | (exfalso; omega)
  · push Not at htk
    rw [if_neg (by omega)]
    have h0 : r (Γ.upperCell (Γ.noC z 0)) = 0 := by
      have hPpos : 0 < period Γ.straight z := by omega
      have e := c_step h (period Γ.straight z - 1)
      rw [Nat.sub_add_cancel hPpos, no_noC_period, if_congr (h.lidσ 0 hPpos) rfl rfl,
        show Γ.noC z (period Γ.straight z - 1) = Γ.noC z (tk + (period Γ.straight z - 1 - tk))
          by congr 1; omega, hup _ (by omega)] at e
      rw [e]
      split_ifs <;> first | rfl | (exfalso; omega)
    clear ht
    induction t with
    | zero => exact h0
    | succ t ih =>
      rw [hstep t (by omega), ih (by omega)]
      split_ifs <;> first | rfl | (exfalso; omega)

/-- A lid curve is never a curve with a dart inside off the lid. -/
theorem c_not_lid (h : CLid Γ z tk tl r Lid) {y0 : D} (hin : Γ.CIn r Lid y0) :
    ∀ y ∈ Lid, Γ.curve y ≠ Γ.curve y0 := by
  intro y hy hc
  have := h.lidR y hy y0 hc.symm hin.1 hin.2.1
  rw [hin.2.2] at this
  exact absurd this (by decide)

/-- Walking along a curve above `S` without crossing the lid: `r` does not change. -/
theorem c_walk_of (h : CCut Γ z tk tl r Lid) {p : D} {k : ℕ}
    (hk : ∀ i ≤ k, Γ.Above ((Γ.straight ^ i) p))
    (hl : ∀ i < k, Γ.σ (Γ.α ((Γ.straight ^ i) p)) ∉ Lid) :
    r (Γ.cellOf ((Γ.straight ^ k) p)) = r (Γ.cellOf p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih (fun i hi => hk i (by omega)) (fun i hi => hl i (by omega))]
    set y := (Γ.straight ^ k) p
    have hy : Γ.Above y := hk k (by omega)
    have hy1 : Γ.Above (Γ.straight y) := by rw [← no_pow_succ]; exact hk (k + 1) le_rfl
    have hw := no_walk_straight (Γ := Γ) (r := r)
      (f := fun y => r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y))) (fun y => rfl) y
    rw [no_pow_succ, hw]
    have hnS : Γ.curve (Γ.σ (Γ.α y)) ≠ Γ.S := by
      intro hS
      apply no_exit hy _ hy1
      rw [j_curves_crossingOf, ← hS]
      exact mem_insert_of_mem (mem_singleton_self _)
    rw [h.cut _ hnS, if_neg (hl k (by omega)), add_zero]

/-- Walking along a curve that is not a lid curve, above `S`: `r` does not change. -/
theorem c_walk (h : CLid Γ z tk tl r Lid) {γ : Fin n} (hγ : ∀ y ∈ Lid, Γ.curve y ≠ γ)
    {p : D} (hp : Γ.curve p = γ) {k : ℕ} (hk : ∀ i ≤ k, Γ.Above ((Γ.straight ^ i) p)) :
    r (Γ.cellOf ((Γ.straight ^ k) p)) = r (Γ.cellOf p) := by
  refine c_walk_of h.toCCut hk (fun i hi hl => ?_)
  set y := (Γ.straight ^ i) p
  have hy : Γ.Above y := hk i (by omega)
  have hcy : Γ.curve y = γ := by rw [no_curve_pow]; exact hp
  rcases h.lidX _ hl (Γ.α y) (j_crossingOf_σ Γ _).symm with hS | ⟨y', hy', hc⟩
  · rw [j_curve_α] at hS; exact hy.1 hS
  · rw [j_curve_α, hcy] at hc; exact hγ y' hy' hc

/-- **Kept curves lie inside**: every dart above `S` of a curve with a dart inside off the lid
is inside and off the lid. -/
theorem c_kept (h : CLid Γ z tk tl r Lid) {y0 : D} (hin : Γ.CIn r Lid y0) {w : D}
    (hw : Γ.curve w = Γ.curve y0) (hwa : Γ.Above w) : w ∉ Lid ∧ r (Γ.cellOf w) = 1 := by
  have hnl := c_not_lid h hin
  have hα : ∀ p, Γ.curve p = Γ.curve y0 → r (Γ.cellOf (Γ.α p)) = r (Γ.cellOf p) := by
    intro p hp
    have hpS : Γ.curve p ≠ Γ.S := hp ▸ hin.1.1
    have := h.cut p hpS
    rw [if_neg (fun hl => hnl p hl hp)] at this
    exact c_zmod2_eq_of_add this
  refine ⟨fun hl => hnl w hl hw, ?_⟩
  rcases upper_arc hin.1 hwa hw.symm with ⟨k, hk, hkw⟩ | ⟨k, hk, hkw⟩ | ⟨k, hk, hkw⟩ |
      ⟨k, hk, hkw⟩
  · have := c_walk h hnl rfl hk
    rw [hkw] at this; rw [this]; exact hin.2.2
  · have := c_walk h hnl hw hk
    rw [hkw] at this; rw [← this]; exact hin.2.2
  · have := c_walk h hnl rfl hk
    rw [hkw, hα w hw] at this; rw [this]; exact hin.2.2
  · have := c_walk h hnl (by rw [j_curve_α, hw]) hk
    rw [hkw, hα w hw] at this; rw [← this]; exact hin.2.2

/-- A segment of a kept curve above `S` does not end at a deleted crossing. -/
theorem c_end_kept (h : CLid Γ z tk tl r Lid) {p : D} (hp : Γ.Above p)
    (hγ : Γ.curve p ∉ Γ.cR r Lid) :
    ¬ Γ.Deleted (Γ.cR r Lid) (Γ.crossingOf (Γ.α p)) := by
  obtain ⟨y0, hy0, hin⟩ := c_witness hγ hp.1
  obtain ⟨hpl, hpr⟩ := c_kept h hin hy0.symm hp
  rw [r_deleted_iff, j_curve_α]
  rintro (hm | hm)
  · exact hγ hm
  · set q := Γ.σ (Γ.α p)
    have hqS : Γ.curve q ≠ Γ.S := (c_mem_cR.1 hm).1
    have hqa : Γ.Above q := ⟨hqS, by unfold Up; rw [j_cellOf_σ, j_α_α]; exact hp.2⟩
    have hqr : r (Γ.cellOf q) = 1 := by rw [j_cellOf_σ, j_α_α]; exact hpr
    have hql : q ∉ Lid := by
      intro hl
      rcases h.lidX q hl (Γ.α p) (j_crossingOf_σ Γ _).symm with hS | ⟨y', hy', hc⟩
      · rw [j_curve_α] at hS; exact hp.1 hS
      · rw [j_curve_α] at hc
        exact (c_kept h hin (hc.trans hy0.symm) (h.above y' hy')).1 hy'
    exact (c_mem_cR.1 hm).2 ⟨q, rfl, hqa, hql, hqr⟩

/-- A vertex strictly between `k` and `l` is not deleted. -/
theorem c_inner_kept (h : CLid Γ z tk tl r Lid) {t : ℕ} (h1 : tk < t) (h2 : t < tl) :
    Γ.CIn r Lid (Γ.σ (Γ.noC z t)) ∧
      ¬ Γ.Deleted (Γ.cR r Lid) (Γ.crossingOf (Γ.noC z t)) := by
  have hP := h.hfin
  have hs := no_noC_sweep h.hz t
  have hin : Γ.CIn r Lid (Γ.σ (Γ.noC z t)) := by
    refine ⟨no_above_σ hs, fun hl => ?_, ?_⟩
    · rcases (h.lidσ t (by omega)).1 hl with e | e <;> omega
    · rw [j_cellOf_σ]
      have := c_sweep h.toCCut (t := t) (by omega)
      unfold upperCell at this
      rw [this, if_pos ⟨h1.le, h2⟩]
  refine ⟨hin, ?_⟩
  rw [r_deleted_iff]
  rintro (hm | hm)
  · exact c_S_not_mem (hs.1 ▸ hm)
  · exact (c_mem_cR.1 hm).2 ⟨_, rfl, hin⟩

/-- A kept curve does not meet `S` outside the edges between `k` and `l`. -/
theorem c_kept_sweep (h : CLid Γ z tk tl r Lid) {t : ℕ} (ht : t < period Γ.straight z)
    (hout : tl ≤ t) {y0 : D} (hin : Γ.CIn r Lid y0)
    (hc : Γ.curve (Γ.σ (Γ.noC z t)) = Γ.curve y0) : False := by
  have hs := no_noC_sweep h.hz t
  have := (c_kept h hin hc (no_above_σ hs)).2
  rw [j_cellOf_σ] at this
  have h2 := c_sweep h.toCCut ht
  unfold upperCell at h2
  rw [h2, if_neg (by omega)] at this
  exact absurd this (by decide)

end Core

end SConf

end Pca.Sweep
