/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.10 (pp. 323-324), graph language (package O, sketch only in source)

"LEMMA 3.10. Let the curve `γ` have endpoints `i < j` and `γ'` have `i' < j'`. The following are
equivalent:
(1) The curve `γ` is inside `γ'`.
(2) In the arrangement `{γ, γ', c}` there is an unbounded face above the sweep. Either `γ` does not
bound the face, or `γ` is a loop with respect to `γ'`.
(3) The endpoints satisfy `i' < i < j'` and `γ` intersects `γ'` in zero or two points above the
sweep.
PROOF. We sketch a proof that `1 ⇒ 2 ⇒ 3 ⇒ 1`. `1 ⇒ 2`. Suppose that `γ` bounds the face but is not a
loop with respect to `γ'`. Then one or both of its endpoints do not lie between `i'` and `j'`.
`2 ⇒ 3`. No portion of `γ` that bounds the infinite face intersects `c` by the condition of 2. Thus
the vertex `i` must lie between `i'` and `j'`. If `γ` does not bound the face, then it does not
intersect the curve `γ'`, since `γ'` does bound the face. If `γ` is a loop, then it intersects `γ'`
twice. `3 ⇒ 1`. Follows from the Jordan curve theorem."

**Sketch only in source; proof to be reconstructed** (`doc/pca/sweep.md`: facts F1-F3 carry
over to the dart model; they are statements about the cut `r` and the darts of `γ`).

Graph language: the "unbounded face above the sweep" of `{γ, γ', c}` is the cell above the ∞-arc
of `Γ − (all other curves)`. Reading of (2) as before (`doc/pca/sweep.md`): with `r` the region
cut of `γ'` (`IsRegion`: `r` changes across the segments of `γ'` above `S` and the edges of `S`
between `i'` and `j'`, `r = 0` above the ∞-arc), "`γ` does not bound the face" = all of `γ` above
`S` has `r = 1`; "`γ` is a loop with respect to `γ'`" = `γ` crosses `γ'` twice above `S` and its two end
segments have `r = 1`. (Equivalent to the literal reading in `Γ − (all other curves)` by Jordan.)
-/
import Pca.Sweep.NO_Sweep

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

variable (Γ) in
/-- The dart `y` lies on the boundary of the region of the loop `γ'`: on `γ'` above `S`, or on an
edge of `S` between its ends. -/
def OnRegionBdry (γ' : Fin n) (y : D) : Prop :=
  (Γ.Above y ∧ Γ.curve y = γ') ∨
    (Γ.IsFinSeg y ∧ ∃ i' j', Γ.LoopEnds γ' i' j' ∧ i' ≤ Γ.pos (Γ.crossingOf y) ∧
      Γ.pos (Γ.crossingOf (Γ.α y)) ≤ j')

variable (Γ) in
open Classical in
/-- `r` is the region cut of the loop `γ'` (`r = 1`: inside the region bounded by `γ'` and `S`). -/
def IsRegion (γ' : Fin n) (r : Γ.Cell → ZMod 2) : Prop :=
  (∀ d ∈ Γ.infArc, r (Γ.upperCell d) = 0) ∧
    ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) =
      if Γ.OnRegionBdry γ' y ∨ Γ.OnRegionBdry γ' (Γ.α y) then 1 else 0

variable (Γ) in
/-- Condition (2) of Lemma 3.10 (reading above). -/
def Cond2 (γ γ' : Fin n) (r : Γ.Cell → ZMod 2) : Prop :=
  (∀ y, Γ.curve y = γ → Γ.Above y → r (Γ.cellOf y) = 1) ∨
    (Γ.crossAbove γ γ' = 2 ∧
      ∀ y, Γ.curve y = γ → Γ.Above y → Γ.IsFinVertex (Γ.crossingOf y) → r (Γ.cellOf y) = 1)

variable (Γ) in
/-- Condition (3) of Lemma 3.10. -/
def Cond3 (γ γ' : Fin n) : Prop :=
  ∃ i j i' j', Γ.LoopEnds γ i j ∧ Γ.LoopEnds γ' i' j' ∧ i' < i ∧ i < j' ∧
    (Γ.crossAbove γ γ' = 0 ∨ Γ.crossAbove γ γ' = 2)

/-! ## Helpers (package O)

Facts F1-F3 of `doc/pca/sweep.md` in the dart model: the boundary of the region along the
sweep (`no_bdry_noC`), the value of `r` above the sweep (F2, `no_region_sweep`), and the parity
along the upper arc of `γ` (F3, `no_core`). -/

private theorem no_exists_z (x : Γ.Crossing) : ∃ z, Γ.infStart = some z := by
  obtain ⟨d, -⟩ := x.exists_mk
  exact Option.isSome_iff_exists.1 (Γ.infStart_isSome ⟨d⟩)

private theorem no_exists_z_of_loop {γ : Fin n} (h : Γ.IsLoop γ) : ∃ z, Γ.infStart = some z := by
  classical
  have h2 : (univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve γ x)).card = 2 := h
  obtain ⟨x, -⟩ := card_pos.1 (by omega : 0 < (univ.filter
    (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve γ x)).card)
  exact no_exists_z x

private theorem no_loopEnds_unique {γ : Fin n} {i j i' j' : ℕ} (h : Γ.LoopEnds γ i j)
    (h' : Γ.LoopEnds γ i' j') : i = i' ∧ j = j' := by
  obtain ⟨-, hij, he⟩ := h
  obtain ⟨-, hij', he'⟩ := h'
  have hs : ({i, j} : Finset ℕ) = {i', j'} := he.symm.trans he'
  have hi : i ∈ ({i', j'} : Finset ℕ) := hs ▸ by simp
  have hj : j ∈ ({i', j'} : Finset ℕ) := hs ▸ by simp
  have hi' : i' ∈ ({i, j} : Finset ℕ) := hs ▸ by simp
  have hj' : j' ∈ ({i, j} : Finset ℕ) := hs ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj hi' hj'
  omega

private theorem no_loopEnds_of_isLoop {z : D} (hz : Γ.infStart = some z) {γ : Fin n}
    (hγ : Γ.IsLoop γ) : ∃ i j, Γ.LoopEnds γ i j := by
  classical
  have hinj : Set.InjOn Γ.pos
      (univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve γ x) : Set Γ.Crossing) := by
    intro x hx y hy hxy
    obtain ⟨t, ht, rfl⟩ := no_onSweep_noC hz (mem_filter.1 (mem_coe.1 hx)).2.1.1
    obtain ⟨t', ht', rfl⟩ := no_onSweep_noC hz (mem_filter.1 (mem_coe.1 hy)).2.1.1
    rw [no_noC_pos hz ht, no_noC_pos hz ht'] at hxy
    rw [show t = t' by omega]
  have hc : (Γ.sweepEnds γ).card = 2 := by
    unfold sweepEnds; rw [card_image_of_injOn hinj]; exact hγ
  obtain ⟨a, b, hab, he⟩ := card_eq_two.1 hc
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, hγ, h, he⟩
  · exact ⟨b, a, hγ, h, by rw [he, pair_comm]⟩

private theorem no_ends_bound {z : D} (hz : Γ.infStart = some z) {γ : Fin n} {i j : ℕ}
    (h : Γ.LoopEnds γ i j) : 1 ≤ i ∧ i < j ∧ j + Γ.infLen ≤ period Γ.straight z := by
  have hi : i ∈ Γ.sweepEnds γ := by rw [h.2.2]; simp
  have hj : j ∈ Γ.sweepEnds γ := by rw [h.2.2]; simp
  obtain ⟨t, -, rfl, -⟩ := (no_mem_sweepEnds hz).1 hi
  obtain ⟨t', ht', rfl, -⟩ := (no_mem_sweepEnds hz).1 hj
  exact ⟨by omega, h.2.1, by omega⟩

/-- The loop `γ` passes the vertex `t + 1` iff `t + 1` is one of its ends. -/
private theorem no_curves_iff {z : D} (hz : Γ.infStart = some z) {γ : Fin n} (hS : γ ≠ Γ.S)
    {i j : ℕ} (h : Γ.LoopEnds γ i j) {t : ℕ} (ht : t < period Γ.straight z) :
    γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) ↔ (t + 1 = i ∨ t + 1 = j) := by
  constructor
  · intro hm
    have hf := no_loop_fin h.1 hS (no_S_mem_noC hz t) hm
    have : t + 1 ∈ Γ.sweepEnds γ :=
      (no_mem_sweepEnds hz).2 ⟨t, (no_noC_fin hz ht).1 hf, rfl, hm⟩
    rw [h.2.2] at this
    simpa using this
  · intro he
    have : t + 1 ∈ Γ.sweepEnds γ := by rw [h.2.2]; rcases he with he | he <;> simp [he]
    obtain ⟨t', -, ht', hm⟩ := (no_mem_sweepEnds hz).1 this
    rw [show t = t' by omega]; exact hm

private theorem no_curve_σ_iff {s : D} (hs : Γ.IsSweepDart s) {γ : Fin n} (hS : γ ≠ Γ.S) :
    Γ.curve (Γ.σ s) = γ ↔ γ ∈ Γ.curves (Γ.crossingOf s) := by
  rw [j_curves_crossingOf, mem_insert, mem_singleton, hs.1]
  constructor
  · exact fun h => Or.inr h.symm
  · rintro (h | h)
    · exact absurd h hS
    · exact h.symm

/-- (F1) The boundary of the region at a dart of a curve other than `S`. -/
private theorem no_bdry_curve {γ' : Fin n} {y : D} (hy : Γ.curve y ≠ Γ.S) :
    (Γ.OnRegionBdry γ' y ∨ Γ.OnRegionBdry γ' (Γ.α y)) ↔
      Γ.curve y = γ' ∧ Γ.Up (Γ.cellOf y) := by
  have hfs : ∀ w, Γ.curve w ≠ Γ.S → ¬ Γ.IsFinSeg w := fun w hw h => hw h.1.1
  have hup : Γ.Up (Γ.cellOf (Γ.α y)) ↔ Γ.Up (Γ.cellOf y) := by unfold Up; rw [no_side_α hy]
  have hyα : Γ.curve (Γ.α y) ≠ Γ.S := by rw [j_curve_α]; exact hy
  unfold OnRegionBdry Above
  rw [j_curve_α, hup]
  constructor
  · rintro ((⟨⟨-, h1⟩, h2⟩ | ⟨h, -⟩) | (⟨⟨-, h1⟩, h2⟩ | ⟨h, -⟩))
    · exact ⟨h2, h1⟩
    · exact absurd h (hfs y hy)
    · exact ⟨h2, h1⟩
    · exact absurd h (hfs _ hyα)
  · rintro ⟨h1, h2⟩
    exact Or.inl (Or.inl ⟨⟨hy, h2⟩, h1⟩)

/-- The boundary of the region at a sweep dart. -/
private theorem no_bdry_sweep {γ' : Fin n} {s : D} (hs : Γ.IsSweepDart s) :
    (Γ.OnRegionBdry γ' s ∨ Γ.OnRegionBdry γ' (Γ.α s)) ↔ Γ.IsFinSeg s ∧ ∃ i' j',
      Γ.LoopEnds γ' i' j' ∧ i' ≤ Γ.pos (Γ.crossingOf s) ∧ Γ.pos (Γ.crossingOf (Γ.α s)) ≤ j' := by
  have hnα : ¬ Γ.IsSweepDart (Γ.α s) := by
    intro h
    have h0 := (no_sweep_iff hs.1).1 hs
    have h1 : Γ.side (Γ.cellOf (Γ.α (Γ.α s))) = 1 := h.2
    rw [j_α_α, h0] at h1; exact absurd h1 (by decide)
  have hSα : Γ.curve (Γ.α s) = Γ.S := by rw [j_curve_α]; exact hs.1
  unfold OnRegionBdry
  constructor
  · rintro ((⟨h, -⟩ | h) | (⟨h, -⟩ | ⟨h, -⟩))
    · exact absurd hs.1 h.1
    · exact h
    · exact absurd hSα h.1
    · exact absurd h.1 hnα
  · intro h; exact Or.inl (Or.inr h)

private theorem no_bdry_α {γ' : Fin n} (y : D) :
    (Γ.OnRegionBdry γ' (Γ.α y) ∨ Γ.OnRegionBdry γ' (Γ.α (Γ.α y))) ↔
      (Γ.OnRegionBdry γ' y ∨ Γ.OnRegionBdry γ' (Γ.α y)) := by
  rw [j_α_α, or_comm]

/-- The boundary of the region along the sweep: the finite edge from `t + 1` to `t + 2` is on
it iff `i' ≤ t + 1 < j'`. -/
private theorem no_bdry_noC {z : D} (hz : Γ.infStart = some z) {γ' : Fin n} {i' j' : ℕ}
    (h : Γ.LoopEnds γ' i' j') {t : ℕ} (ht : t < period Γ.straight z) :
    (Γ.OnRegionBdry γ' (Γ.noC z t) ∨ Γ.OnRegionBdry γ' (Γ.α (Γ.noC z t))) ↔
      (t + Γ.infLen + 1 < period Γ.straight z ∧ i' ≤ t + 1 ∧ t + 2 ≤ j') := by
  rw [no_bdry_sweep (no_noC_sweep hz t)]
  unfold IsFinSeg
  rw [no_noC_arc hz ht]
  simp only [no_noC_sweep hz t, true_and, not_le]
  constructor
  · rintro ⟨hlt, i'', j'', h', h1, h2⟩
    obtain ⟨e1, e2⟩ := no_loopEnds_unique h' h
    rw [no_noC_pos hz ht, e1] at h1
    rw [← no_crossingOf_α_straight, no_noC_straight, no_noC_pos hz (by omega), e2] at h2
    exact ⟨hlt, h1, h2⟩
  · rintro ⟨hlt, h1, h2⟩
    refine ⟨hlt, i', j', h, by rw [no_noC_pos hz ht]; exact h1, ?_⟩
    rw [← no_crossingOf_α_straight, no_noC_straight, no_noC_pos hz (by omega)]; exact h2

/-- The region boundary at the above dart `σ s` of the vertex `t + 1`. -/
private theorem no_bdry_σ_noC {z : D} (hz : Γ.infStart = some z) {γ' : Fin n} (hS : γ' ≠ Γ.S)
    {i' j' : ℕ} (h : Γ.LoopEnds γ' i' j') {t : ℕ} (ht : t < period Γ.straight z) :
    (Γ.OnRegionBdry γ' (Γ.σ (Γ.noC z t)) ∨ Γ.OnRegionBdry γ' (Γ.α (Γ.σ (Γ.noC z t)))) ↔
      (t + 1 = i' ∨ t + 1 = j') := by
  have hs := no_noC_sweep hz t
  rw [no_bdry_curve (no_above_σ hs).1, no_curve_σ_iff hs hS, no_curves_iff hz hS h ht]
  simp only [(no_above_σ hs).2, and_true]

/-- The predecessor of the sweep dart `noC z t` on the sweep. -/
private theorem no_bdry_σσ_noC {z : D} (hz : Γ.infStart = some z) {γ' : Fin n} {i' j' : ℕ}
    (h : Γ.LoopEnds γ' i' j') {t : ℕ} (ht : t < period Γ.straight z) :
    (Γ.OnRegionBdry γ' (Γ.σ (Γ.σ (Γ.noC z t))) ∨
        Γ.OnRegionBdry γ' (Γ.α (Γ.σ (Γ.σ (Γ.noC z t))))) ↔
      (1 ≤ t ∧ t + Γ.infLen < period Γ.straight z ∧ i' ≤ t ∧ t + 1 ≤ j') := by
  have hP := period_pos Γ.straight z
  obtain ⟨u, hu, hut⟩ : ∃ u < period Γ.straight z, Γ.straight (Γ.noC z u) = Γ.noC z t ∧
      (u + 1 = t ∨ (t = 0 ∧ u + 1 = period Γ.straight z)) := by
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · refine ⟨period Γ.straight z - 1, by omega, ?_, Or.inr ⟨rfl, by omega⟩⟩
      rw [no_noC_straight, Nat.sub_add_cancel hP, no_noC_period]
    · exact ⟨t - 1, by omega, by rw [no_noC_straight, Nat.sub_add_cancel ht0], Or.inl (by omega)⟩
  have he := no_pred hut.1
  have hk := no_infLen_le hz
  have he' : Γ.σ (Γ.σ (Γ.noC z t)) = Γ.α (Γ.noC z u) := by rw [← he, j_α_α]
  rw [he', no_bdry_α, no_bdry_noC hz h hu]
  rcases hut.2 with h1 | ⟨h1, h2⟩ <;> constructor <;> intro hh <;> omega

open Classical in
private theorem no_exists_region {γ' : Fin n} (h : Γ.IsLoop γ') (hS : γ' ≠ Γ.S) :
    ∃ r, Γ.IsRegion γ' r := by
  obtain ⟨z, hz⟩ := no_exists_z_of_loop h
  obtain ⟨i', j', hends⟩ := no_loopEnds_of_isLoop hz h
  obtain ⟨hi1, hij, hjP⟩ := no_ends_bound hz hends
  have hk := no_infLen_le hz
  set E : Finset Γ.Segment := univ.filter (fun s => ∃ y ∈ s.darts, Γ.OnRegionBdry γ' y)
  have hmemE : ∀ y, Γ.segmentOf y ∈ E ↔ (Γ.OnRegionBdry γ' y ∨ Γ.OnRegionBdry γ' (Γ.α y)) := by
    intro y
    simp [E, j_darts_segmentOf]
  have hE : Γ.IsEven E := by
    intro x
    rw [← ZMod.natCast_eq_zero_iff_even, ← sum_boole]
    by_cases hx : Γ.OnSweep x
    · obtain ⟨t, ht, rfl⟩ := no_onSweep_noC hz hx
      rw [j_sum_darts_crossingOf]
      simp only [hmemE]
      have hs := no_noC_sweep hz t
      have h3 : ¬ (Γ.OnRegionBdry γ' (Γ.σ (Γ.σ (Γ.σ (Γ.noC z t)))) ∨
          Γ.OnRegionBdry γ' (Γ.α (Γ.σ (Γ.σ (Γ.σ (Γ.noC z t)))))) := by
        have hc : Γ.curve (Γ.σ (Γ.σ (Γ.σ (Γ.noC z t)))) ≠ Γ.S := by
          rw [j_curve_σσ]; exact (no_above_σ hs).1
        rw [no_bdry_curve hc]
        rintro ⟨-, hu⟩
        have h0 := (no_sweep_iff hs.1).1 hs
        have : Γ.side (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ (Γ.noC z t))))) = 1 := hu
        rw [no_side_σ, no_side_σσ_of_S hs.1, h0, if_pos (by rw [j_curve_σσ]; exact hs.1)] at this
        exact absurd this (by decide)
      simp only [no_bdry_noC hz hends ht, no_bdry_σ_noC hz hS hends ht,
        no_bdry_σσ_noC hz hends ht, h3, if_false, add_zero]
      split_ifs <;> first | decide | (exfalso; omega)
    · obtain ⟨y, rfl⟩ := x.exists_mk
      change ∑ w ∈ (Γ.crossingOf y).darts, _ = _
      rw [j_sum_darts_crossingOf]
      simp only [hmemE]
      change Γ.S ∉ Γ.curves (Γ.crossingOf y) at hx
      rw [j_curves_crossingOf, mem_insert, mem_singleton, not_or] at hx
      have c0 : Γ.curve y ≠ Γ.S := fun h => hx.1 h.symm
      have c1 : Γ.curve (Γ.σ y) ≠ Γ.S := fun h => hx.2 h.symm
      have c2 : Γ.curve (Γ.σ (Γ.σ y)) ≠ Γ.S := by rw [j_curve_σσ]; exact c0
      have c3 : Γ.curve (Γ.σ (Γ.σ (Γ.σ y))) ≠ Γ.S := by rw [j_curve_σσ]; exact c1
      have s1 : Γ.side (Γ.cellOf (Γ.σ y)) = Γ.side (Γ.cellOf y) := by
        rw [no_side_σ, if_neg c0, add_zero]
      have s2 : Γ.side (Γ.cellOf (Γ.σ (Γ.σ y))) = Γ.side (Γ.cellOf y) := by
        rw [no_side_σ, if_neg c1, add_zero, s1]
      have s3 : Γ.side (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ y)))) = Γ.side (Γ.cellOf y) := by
        rw [no_side_σ, if_neg c2, add_zero, s2]
      simp only [no_bdry_curve c0, no_bdry_curve c1, no_bdry_curve c2, no_bdry_curve c3, Up,
        s1, s2, s3, j_curve_σσ]
      split_ifs <;> decide
  obtain ⟨r0, hr0⟩ := exists_cut E hE
  have hr0' : ∀ y, r0 (Γ.cellOf y) + r0 (Γ.cellOf (Γ.α y)) =
      if Γ.OnRegionBdry γ' y ∨ Γ.OnRegionBdry γ' (Γ.α y) then 1 else 0 := by
    intro y; rw [hr0 y]; simp only [hmemE]
  refine ⟨fun c => r0 c + r0 (Γ.upperCell z), ?_, ?_⟩
  · intro d hd
    obtain ⟨i, hi, rfl⟩ := (no_mem_infArc hz).1 hd
    suffices key : r0 (Γ.upperCell ((Γ.straight ^ i) z)) = r0 (Γ.upperCell z) by
      show r0 _ + _ = 0; rw [key, j_zmod2_add_self]
    clear hd
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [← ih (by omega)]
      unfold upperCell
      rw [no_pow_succ, no_walk_sweep hr0']
      have hsw := no_sweep_pow (no_z_sweep hz) (i + 1)
      rw [← no_pow_succ]
      have hn : ¬ (Γ.OnRegionBdry γ' (Γ.σ ((Γ.straight ^ (i + 1)) z)) ∨
          Γ.OnRegionBdry γ' (Γ.α (Γ.σ ((Γ.straight ^ (i + 1)) z)))) := by
        rw [no_bdry_curve (no_above_σ hsw).1, no_curve_σ_iff hsw hS]
        rintro ⟨hm, -⟩
        have hf := no_loop_fin h hS (by
          change Γ.S ∈ _; rw [j_curves_crossingOf, hsw.1]; exact mem_insert_self _ _) hm
        apply hf.2
        exact ⟨z, by rw [hz]; rfl, i, by omega, by rw [← no_crossingOf_α_straight, ← no_pow_succ]⟩
      rw [if_neg hn, add_zero]
  · intro y
    show r0 _ + r0 (Γ.upperCell z) + (r0 _ + r0 (Γ.upperCell z)) = _
    rw [← hr0' y]
    rw [add_add_add_comm, j_zmod2_add_self, add_zero]

/-- The value of `r` above the vertex at position `p` (F2): `1` iff `i' < p < j'` (for `p` not
an end of `γ'`). -/
private def noVal (i' j' p : ℕ) : ZMod 2 :=
  (if i' ≤ p then 1 else 0) + (if j' ≤ p then 1 else 0)

/-- (F2) The value of the region above the sweep, walking along the upper side of `S` from the
∞-arc. -/
private theorem no_region_sweep {z : D} (hz : Γ.infStart = some z) {γ' : Fin n} (hS : γ' ≠ Γ.S)
    {i' j' : ℕ} (h : Γ.LoopEnds γ' i' j') {r : Γ.Cell → ZMod 2} (hr : Γ.IsRegion γ' r) {t : ℕ}
    (ht : t < period Γ.straight z) :
    r (Γ.cellOf (Γ.α (Γ.noC z t))) = noVal i' j' (t + 1) := by
  obtain ⟨hi1, hij, -⟩ := no_ends_bound hz h
  have hk := no_infLen_le hz
  have hP := period_pos Γ.straight z
  unfold noVal
  induction t with
  | zero =>
    have e : Γ.straight (Γ.noC z (period Γ.straight z - 1)) = Γ.noC z 0 := by
      rw [no_noC_straight, Nat.sub_add_cancel hP, no_noC_period]
    rw [← e, no_walk_sweep hr.2, e]
    have h0 : r (Γ.cellOf (Γ.α (Γ.noC z (period Γ.straight z - 1)))) = 0 :=
      hr.1 _ ((no_noC_arc hz (by omega)).2 (by omega))
    rw [h0, zero_add]
    simp only [no_bdry_σ_noC hz hS h ht]
    split_ifs <;> first | decide | (exfalso; omega)
  | succ t ih =>
    rw [← no_noC_straight, no_walk_sweep hr.2, no_noC_straight, ih (by omega)]
    simp only [no_bdry_σ_noC hz hS h ht]
    split_ifs <;> first | decide | (exfalso; omega)

/-- Every vertex on the sweep of a curve is one of `S`. -/
private theorem no_sweepEnds_S {z : D} (hz : Γ.infStart = some z) {γ : Fin n} {p : ℕ}
    (hp : p ∈ Γ.sweepEnds γ) : p ∈ Γ.sweepEnds Γ.S := by
  obtain ⟨t, ht, rfl, -⟩ := (no_mem_sweepEnds hz).1 hp
  exact (no_mem_sweepEnds hz).2 ⟨t, ht, rfl, no_S_mem_noC hz t⟩

private theorem no_ne_S {z : D} (hz : Γ.infStart = some z) {γ γ' : Fin n} {i j i' j' : ℕ}
    (hγ : Γ.LoopEnds γ i j) (hγ' : Γ.LoopEnds γ' i' j') (h1 : i' < i) (h2 : i < j') :
    γ ≠ Γ.S ∧ γ' ≠ Γ.S := by
  constructor
  · rintro rfl
    have := no_sweepEnds_S hz (show i' ∈ Γ.sweepEnds γ' by rw [hγ'.2.2]; simp)
    rw [hγ.2.2] at this
    have := hγ.2.1
    simp only [mem_insert, mem_singleton] at *
    omega
  · rintro rfl
    have := no_sweepEnds_S hz (show i ∈ Γ.sweepEnds γ by rw [hγ.2.2]; simp)
    rw [hγ'.2.2] at this
    simp only [mem_insert, mem_singleton] at this
    omega

open Classical in
/-- (F2 + F3) The data of Lemma 3.10 for two loops `γ ≠ γ'` other than `S` and a region `r` of
`γ'`: the ends of `γ` are not ends of `γ'`, the values of `r` above the ends of `γ` add up to the
number of crossings of `γ` and `γ'` above the sweep (parity along the upper arc of `γ`), and the
values of `r` along `γ`. -/
private theorem no_core {z : D} (hz : Γ.infStart = some z) {γ γ' : Fin n} (hne : γ ≠ γ')
    (hγS : γ ≠ Γ.S) (hγ'S : γ' ≠ Γ.S) {i j i' j' : ℕ} (hγ : Γ.LoopEnds γ i j)
    (hγ' : Γ.LoopEnds γ' i' j') {r : Γ.Cell → ZMod 2} (hr : Γ.IsRegion γ' r) :
    (i ≠ i' ∧ i ≠ j' ∧ j ≠ i' ∧ j ≠ j') ∧
    noVal i' j' i + noVal i' j' j = (Γ.crossAbove γ γ' : ZMod 2) ∧
    Γ.crossAbove γ γ' ≤ 2 ∧
    (∃ y, Γ.curve y = γ ∧ Γ.Above y ∧ Γ.IsFinVertex (Γ.crossingOf y) ∧
      r (Γ.cellOf y) = noVal i' j' i) ∧
    (∃ y, Γ.curve y = γ ∧ Γ.Above y ∧ Γ.IsFinVertex (Γ.crossingOf y) ∧
      r (Γ.cellOf y) = noVal i' j' j) ∧
    (Γ.crossAbove γ γ' = 0 → ∀ y, Γ.curve y = γ → Γ.Above y → r (Γ.cellOf y) = noVal i' j' i) ∧
    (∀ y, Γ.curve y = γ → Γ.Above y → Γ.IsFinVertex (Γ.crossingOf y) →
      r (Γ.cellOf y) = noVal i' j' i ∨ r (Γ.cellOf y) = noVal i' j' j) := by
  have hk := no_infLen_le hz
  obtain ⟨t₁, ht₁, hi, hm₁⟩ :=
    (no_mem_sweepEnds hz).1 (show i ∈ Γ.sweepEnds γ by rw [hγ.2.2]; simp)
  obtain ⟨t₂, ht₂, hj, hm₂⟩ :=
    (no_mem_sweepEnds hz).1 (show j ∈ Γ.sweepEnds γ by rw [hγ.2.2]; simp)
  have hij := hγ.2.1
  have hs₁ := no_noC_sweep hz t₁
  have hs₂ := no_noC_sweep hz t₂
  have hv : ∀ t, t < period Γ.straight z →
      r (Γ.cellOf (Γ.σ (Γ.noC z t))) = noVal i' j' (t + 1) := fun t ht => by
    rw [j_cellOf_σ]; exact no_region_sweep hz hγ'S hγ' hr ht
  -- the vertices of `γ` are not vertices of `γ'`
  have hnot : ∀ t, t < period Γ.straight z → γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) →
      t + 1 ≠ i' ∧ t + 1 ≠ j' := by
    intro t ht hm
    have hc := no_mem_curves (no_S_mem_noC hz t) hm hγS
    have hn : γ' ∉ Γ.curves (Γ.crossingOf (Γ.noC z t)) := by
      rw [hc]; simp [Ne.symm hne, hγ'S]
    rw [no_curves_iff hz hγ'S hγ' ht] at hn
    omega
  have hαeq : ∀ y, Γ.curve y = γ → r (Γ.cellOf (Γ.α y)) = r (Γ.cellOf y) := by
    intro y hy
    have hyS : Γ.curve y ≠ Γ.S := by rw [hy]; exact hγS
    have h1 := hr.2 y
    have hn : ¬ (Γ.OnRegionBdry γ' y ∨ Γ.OnRegionBdry γ' (Γ.α y)) := by
      rw [no_bdry_curve hyS]; exact fun h => hne (hy ▸ h.1)
    rw [if_neg hn] at h1
    rw [j_zmod2_eq_add_of_add_eq h1, add_zero]
  -- the two above darts at the ends of `γ` and the upper arc between them
  set a := Γ.σ (Γ.noC z t₁) with ha_def
  set b := Γ.σ (Γ.noC z t₂) with hb_def
  have ca : Γ.curve a = γ := (no_curve_σ_iff hs₁ hγS).2 hm₁
  have cb : Γ.curve b = γ := (no_curve_σ_iff hs₂ hγS).2 hm₂
  have haS : Γ.S ∈ Γ.curves (Γ.crossingOf a) := by rw [j_crossingOf_σ]; exact no_S_mem_noC hz t₁
  have hbS : Γ.S ∈ Γ.curves (Γ.crossingOf b) := by rw [j_crossingOf_σ]; exact no_S_mem_noC hz t₂
  have hcr : Γ.crossingOf a ≠ Γ.crossingOf b := by
    intro h
    rw [j_crossingOf_σ, j_crossingOf_σ] at h
    have := no_noC_inj hz (by omega) (by omega) h
    omega
  obtain ⟨L, hall, hL, hLp, hnos, hcov⟩ :=
    no_upper_arc (no_above_σ hs₁) (no_above_σ hs₂) (ca.trans cb.symm) haS hbS hcr
  replace hLp : L < period Γ.straight a := hLp
  -- walking along the arc, `r` changes at the crossings with `γ'`
  have hwalk : ∀ q ≤ L, r (Γ.cellOf ((Γ.straight ^ q) a)) = r (Γ.cellOf a) +
      (((range q).filter (fun q' => Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q') a))) = γ')).card :
        ZMod 2) := by
    intro q
    induction q with
    | zero => intro _; simp
    | succ q ih =>
      intro hq
      rw [no_pow_succ, no_walk_straight hr.2, ih (by omega), range_add_one, filter_insert]
      have hc : Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q) a))) ≠ Γ.S := by
        intro h
        apply hnos q (by omega)
        change Γ.S ∈ Γ.curves _
        rw [j_curves_crossingOf, h]; exact mem_insert_of_mem (mem_singleton_self _)
      have hup : Γ.Up (Γ.cellOf (Γ.σ (Γ.α ((Γ.straight ^ q) a)))) := by
        unfold Up; rw [j_cellOf_σ, j_α_α]; exact (hall q (by omega)).2
      have hb := no_bdry_curve (γ' := γ') hc
      by_cases hq' : Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q) a))) = γ'
      · rw [if_pos (hb.2 ⟨hq', hup⟩), if_pos hq', card_insert_of_notMem (by simp)]
        push_cast; ring
      · rw [if_neg (fun h => hq' (hb.1 h).1), if_neg hq', add_zero]
  have hcurves : ∀ q, Γ.curves (Γ.crossingOf (Γ.α ((Γ.straight ^ q) a))) =
      {γ, Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q) a)))} := by
    intro q; rw [j_curves_crossingOf, j_curve_α, no_curve_pow, ca]
  have hneγ : ∀ q, Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q) a))) ≠ γ := by
    intro q h
    apply no_curve_σ_ne (Γ.α ((Γ.straight ^ q) a))
    rw [h, j_curve_α, no_curve_pow, ca]
  -- the crossings with `γ'` on the arc are the crossings of `γ` and `γ'` above the sweep
  have hcount : ((range L).filter
      (fun q => Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q) a))) = γ')).card = Γ.crossAbove γ γ' := by
    unfold crossAbove
    apply card_bij (fun q _ => Γ.crossingOf (Γ.α ((Γ.straight ^ q) a)))
    · intro q hq
      simp only [mem_filter, mem_range] at hq
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨⟨hnos q hq.1, Γ.α ((Γ.straight ^ q) a), Orbit.mem_darts.2 rfl, ?_, ?_⟩, ?_⟩
      · rw [j_curve_α, no_curve_pow, ca]; exact hγS
      · unfold Up
        rw [no_side_α (by rw [no_curve_pow, ca]; exact hγS)]
        exact (hall q hq.1.le).2
      · rw [hcurves, hq.2]
    · intro q₁ hq₁ q₂ hq₂ h
      simp only [mem_filter, mem_range] at hq₁ hq₂
      rw [← no_crossingOf_α_straight, ← no_crossingOf_α_straight, ← no_pow_succ,
        ← no_pow_succ] at h
      rcases no_mem_crossing h with h' | h' | h' | h'
      · have := no_pow_inj (d := a) (by omega) (by omega) h'
        omega
      · exfalso
        have := congrArg Γ.curve h'
        rw [no_curve_pow] at this
        exact no_curve_σ_ne _ (by rw [← this, no_curve_pow])
      · exfalso
        apply no_not_sameCycle_straight_σσ ((Γ.straight ^ (q₂ + 1)) a)
        rw [← h']
        exact (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ a)).symm.trans
          (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ a))
      · exfalso
        have := congrArg Γ.curve h'
        rw [no_curve_pow, j_curve_σσ] at this
        exact no_curve_σ_ne _ (by rw [← this, no_curve_pow])
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      obtain ⟨⟨hnS, d, hd, hAd⟩, hcx⟩ := hx
      have hdx : Γ.crossingOf d = x := Orbit.mem_darts.1 hd
      subst hdx
      -- the dart `y` of `γ` above the sweep at `x`
      obtain ⟨y, hyx, hyγ, hyA⟩ : ∃ y, Γ.crossingOf y = Γ.crossingOf d ∧ Γ.curve y = γ ∧
          Γ.Above y := by
        have hγx : γ ∈ Γ.curves (Γ.crossingOf d) := by rw [hcx]; exact mem_insert_self _ _
        rw [j_curves_crossingOf, mem_insert, mem_singleton] at hγx
        rcases hγx with h | h
        · exact ⟨d, rfl, h.symm, hAd⟩
        · refine ⟨Γ.σ d, j_crossingOf_σ _ _, h.symm, by rw [← h]; exact hγS, ?_⟩
          unfold Up; rw [no_side_σ, if_neg hAd.1, add_zero]; exact hAd.2
      have hσγ' : ∀ q, Γ.crossingOf (Γ.α ((Γ.straight ^ q) a)) = Γ.crossingOf d →
          Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q) a))) = γ' := by
        intro q hq
        have h1 : Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q) a))) ∈ ({γ, γ'} : Finset (Fin n)) := by
          rw [← hcx, ← hq, hcurves]; exact mem_insert_of_mem (mem_singleton_self _)
        simp only [mem_insert, mem_singleton] at h1
        exact h1.resolve_left (hneγ q)
      obtain ⟨q, hqL, hq⟩ := hcov y hyA (hyγ.trans ca.symm)
      rcases hq with hq | hq
      · rcases Nat.eq_zero_or_pos q with rfl | hq0
        · exfalso; apply hnS; rw [← hyx, ← hq]; exact haS
        · refine ⟨q - 1, ?_, ?_⟩
          · have hx' : Γ.crossingOf (Γ.α ((Γ.straight ^ (q - 1)) a)) = Γ.crossingOf d := by
              rw [← no_crossingOf_α_straight, ← no_pow_succ, Nat.sub_add_cancel hq0, hq, hyx]
            simp only [mem_filter, mem_range]
            exact ⟨by omega, hσγ' _ hx'⟩
          · rw [← no_crossingOf_α_straight, ← no_pow_succ, Nat.sub_add_cancel hq0, hq, hyx]
      · have hx' : Γ.crossingOf (Γ.α ((Γ.straight ^ q) a)) = Γ.crossingOf d := by
          rw [hq, j_α_α, hyx]
        refine ⟨q, ?_, hx'⟩
        simp only [mem_filter, mem_range]
        refine ⟨lt_of_le_of_ne hqL ?_, hσγ' _ hx'⟩
        rintro rfl
        apply hnS
        rw [← hx', hL, j_α_α]; exact hbS
  have hrb : r (Γ.cellOf b) = r (Γ.cellOf a) + (Γ.crossAbove γ γ' : ZMod 2) := by
    rw [← hαeq b cb, ← hL, hwalk L le_rfl, hcount]
  have hva : r (Γ.cellOf a) = noVal i' j' i := by rw [hi]; exact hv t₁ (by omega)
  have hvb : r (Γ.cellOf b) = noVal i' j' j := by rw [hj]; exact hv t₂ (by omega)
  have hfa : Γ.IsFinVertex (Γ.crossingOf a) := by
    rw [j_crossingOf_σ]; exact (no_noC_fin hz (by omega)).2 ht₁
  have hfb : Γ.IsFinVertex (Γ.crossingOf b) := by
    rw [j_crossingOf_σ]; exact (no_noC_fin hz (by omega)).2 ht₂
  refine ⟨?_, ?_, ?_, ⟨a, ca, no_above_σ hs₁, hfa, hva⟩, ⟨b, cb, no_above_σ hs₂, hfb, hvb⟩,
    ?_, ?_⟩
  · have h1 := hnot t₁ (by omega) hm₁
    have h2 := hnot t₂ (by omega) hm₂
    omega
  · rw [← hva, ← hvb, hrb, ← add_assoc, j_zmod2_add_self, zero_add]
  · unfold crossAbove
    calc _ ≤ (univ.filter (fun x : Γ.Crossing => crossingCurves Γ.σ Γ.curve x = {γ, γ'})).card := by
          apply card_le_card
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx ⊢
          exact hx.2
      _ ≤ 2 := Γ.isSConf.two_int γ γ' hne
  · intro h0 y hy hyA
    obtain ⟨q, hqL, hq⟩ := hcov y hyA (hy.trans ca.symm)
    have hq0 : r (Γ.cellOf ((Γ.straight ^ q) a)) = r (Γ.cellOf a) := by
      rw [hwalk q hqL]
      have : ((range q).filter
          (fun q' => Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q') a))) = γ')).card = 0 := by
        have hsub := card_le_card (monotone_filter_left (p := fun q' =>
          Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q') a))) = γ') (range_subset_range.2 hqL))
        rw [hcount, h0] at hsub
        omega
      rw [this]; simp
    rw [← hva]
    rcases hq with hq | hq
    · rw [← hq, hq0]
    · rw [← hαeq y hy, ← hq, hq0]
  · intro y hy hyA hyf
    obtain ⟨hsw, hσ⟩ := no_sweep_of_above hyA hyf.1
    obtain ⟨t, ht, hte⟩ := no_noC_surj hz hsw
    have hyt : y = Γ.σ (Γ.noC z t) := by rw [hte, hσ]
    have hcr' : Γ.crossingOf y = Γ.crossingOf (Γ.noC z t) := by rw [hyt, j_crossingOf_σ]
    have hγm : γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) := by
      rw [← hcr', j_curves_crossingOf, hy]; exact mem_insert_self _ _
    have hft : t + Γ.infLen < period Γ.straight z := (no_noC_fin hz ht).1 (hcr' ▸ hyf)
    have hmem : t + 1 ∈ Γ.sweepEnds γ := (no_mem_sweepEnds hz).2 ⟨t, hft, rfl, hγm⟩
    rw [hγ.2.2] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rw [hyt, hv t ht]
    rcases hmem with h | h
    · left; rw [h]
    · right; rw [h]

open Classical in
/-- `S` itself has no region: if `S` is a loop (two vertices on the sweep), the boundary would be
the single finite edge, which is not even at vertex `1`. -/
private theorem no_not_region_S {z : D} (hz : Γ.infStart = some z) {i' j' : ℕ}
    (h : Γ.LoopEnds Γ.S i' j') {r : Γ.Cell → ZMod 2} (hr : Γ.IsRegion Γ.S r) : False := by
  have hk := no_infLen_le hz
  obtain ⟨hi1, hij, hjP⟩ := no_ends_bound hz h
  have hmem : ∀ p, p ∈ ({i', j'} : Finset ℕ) ↔ 1 ≤ p ∧ p + Γ.infLen ≤ period Γ.straight z := by
    intro p
    rw [← h.2.2, no_mem_sweepEnds hz]
    constructor
    · rintro ⟨t, ht, rfl, -⟩; omega
    · intro hp; exact ⟨p - 1, by omega, by omega, no_S_mem_noC hz _⟩
  have h1 := (hmem 1).2 ⟨le_rfl, by omega⟩
  have h2 := (hmem 2).2 ⟨by omega, by omega⟩
  simp only [mem_insert, mem_singleton] at h1 h2
  have hP : 0 < period Γ.straight z := by omega
  have hs := no_noC_sweep hz 0
  have hsum := no_corner_sum hr.2 (Γ.noC z 0)
  have c1 : Γ.curve (Γ.σ (Γ.noC z 0)) ≠ Γ.S := (no_above_σ hs).1
  have c3 : Γ.curve (Γ.σ (Γ.σ (Γ.σ (Γ.noC z 0)))) ≠ Γ.S := by rw [j_curve_σσ]; exact c1
  simp only [no_bdry_noC hz h hP, no_bdry_σσ_noC hz h hP, no_bdry_curve c1,
    no_bdry_curve c3] at hsum
  rw [if_pos (by omega), if_neg (fun h => c1 h.1), if_neg (by omega),
    if_neg (fun h => c3 h.1)] at hsum
  exact absurd hsum (by decide)

/-- The region of a loop `γ' ≠ S` (Jordan). -/
theorem exists_region {γ' : Fin n} (h : Γ.IsLoop γ') (hS : γ' ≠ Γ.S) : ∃ r, Γ.IsRegion γ' r :=
  no_exists_region h hS

/-- **SH Lemma 3.10**, `1 ⇒ 2` (sketch only in source). -/
theorem lemma_3_10_12 {γ γ' : Fin n} (hne : γ ≠ γ') {r : Γ.Cell → ZMod 2}
    (hr : Γ.IsRegion γ' r) (h : Γ.Inside γ γ') : Γ.Cond2 γ γ' r := by
  obtain ⟨i, j, i', j', hγ, hγ', h1, h2⟩ := h
  obtain ⟨z, hz⟩ := no_exists_z_of_loop hγ.1
  have hij := hγ.2.1
  obtain ⟨hγS, hγ'S⟩ := no_ne_S hz hγ hγ' h1 (by omega)
  obtain ⟨-, hsum, hle, -, -, h0, hfin⟩ := no_core hz hne hγS hγ'S hγ hγ' hr
  have hvi : noVal i' j' i = 1 := by
    unfold noVal; rw [if_pos (by omega : i' ≤ i), if_neg (by omega : ¬ j' ≤ i)]; decide
  have hvj : noVal i' j' j = 1 := by
    unfold noVal; rw [if_pos (by omega : i' ≤ j), if_neg (by omega : ¬ j' ≤ j)]; decide
  rw [hvi, hvj] at hsum
  rcases (by omega : Γ.crossAbove γ γ' = 0 ∨ Γ.crossAbove γ γ' = 1 ∨ Γ.crossAbove γ γ' = 2)
    with hc | hc | hc
  · exact Or.inl fun y hy hA => (h0 hc y hy hA).trans hvi
  · rw [hc, Nat.cast_one] at hsum; exact absurd hsum (by decide)
  · exact Or.inr ⟨hc, fun y hy hA hf => (hfin y hy hA hf).elim (·.trans hvi) (·.trans hvj)⟩

/-- **SH Lemma 3.10**, `2 ⇒ 3` (sketch only in source). -/
theorem lemma_3_10_23 {γ γ' : Fin n} (hne : γ ≠ γ') (hS : γ ≠ Γ.S) (hγ : Γ.IsLoop γ)
    (hγ' : Γ.IsLoop γ') {r : Γ.Cell → ZMod 2} (hr : Γ.IsRegion γ' r) (h : Γ.Cond2 γ γ' r) :
    Γ.Cond3 γ γ' := by
  obtain ⟨z, hz⟩ := no_exists_z_of_loop hγ
  obtain ⟨i, j, hγE⟩ := no_loopEnds_of_isLoop hz hγ
  obtain ⟨i', j', hγ'E⟩ := no_loopEnds_of_isLoop hz hγ'
  rcases eq_or_ne γ' Γ.S with rfl | hγ'S
  · exact (no_not_region_S hz hγ'E hr).elim
  obtain ⟨hb, hsum, hle, ⟨ya, ya1, ya2, ya3, ya4⟩, ⟨yb, yb1, yb2, -, yb4⟩, -, -⟩ :=
    no_core hz hne hS hγ'S hγE hγ'E hr
  obtain ⟨hi1', hij', -⟩ := no_ends_bound hz hγ'E
  have hvi : noVal i' j' i = 1 := by
    rcases h with h | ⟨-, h⟩
    · rw [← ya4]; exact h ya ya1 ya2
    · rw [← ya4]; exact h ya ya1 ya2 ya3
  have hlt : i' < i ∧ i < j' := by
    unfold noVal at hvi
    split_ifs at hvi <;> first | omega | exact absurd hvi (by decide)
  refine ⟨i, j, i', j', hγE, hγ'E, hlt.1, hlt.2, ?_⟩
  rcases h with h | ⟨h2, -⟩
  · have hvj : noVal i' j' j = 1 := by rw [← yb4]; exact h yb yb1 yb2
    rw [hvi, hvj] at hsum
    rcases (by omega : Γ.crossAbove γ γ' = 0 ∨ Γ.crossAbove γ γ' = 1 ∨ Γ.crossAbove γ γ' = 2)
      with hc | hc | hc
    · exact Or.inl hc
    · rw [hc, Nat.cast_one] at hsum; exact absurd hsum (by decide)
    · exact Or.inr hc
  · exact Or.inr h2

/-- **SH Lemma 3.10**, `3 ⇒ 1` ("Follows from the Jordan curve theorem"). -/
theorem lemma_3_10_31 {γ γ' : Fin n} (hne : γ ≠ γ') (h : Γ.Cond3 γ γ') : Γ.Inside γ γ' := by
  obtain ⟨i, j, i', j', hγ, hγ', h1, h2, hc⟩ := h
  obtain ⟨z, hz⟩ := no_exists_z_of_loop hγ.1
  obtain ⟨hγS, hγ'S⟩ := no_ne_S hz hγ hγ' h1 h2
  obtain ⟨r, hr⟩ := no_exists_region hγ'.1 hγ'S
  obtain ⟨-, hsum, -⟩ := no_core hz hne hγS hγ'S hγ hγ' hr
  have hij := hγ.2.1
  have hvi : noVal i' j' i = 1 := by
    unfold noVal; rw [if_pos (by omega : i' ≤ i), if_neg (by omega : ¬ j' ≤ i)]; decide
  have hc' : (Γ.crossAbove γ γ' : ZMod 2) = 0 := by
    rcases hc with hc | hc <;> rw [hc] <;> decide
  rw [hvi, hc'] at hsum
  refine ⟨i, j, i', j', hγ, hγ', h1, ?_⟩
  unfold noVal at hsum
  split_ifs at hsum <;> first | omega | exact absurd hsum (by decide)

end SConf

end Pca.Sweep
