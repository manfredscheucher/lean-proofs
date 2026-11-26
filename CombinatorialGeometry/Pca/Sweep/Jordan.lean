/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH sweep in graph language: Jordan facts for sweep configurations (package J)

SH use the Jordan curve theorem throughout, mostly without comment ("separates", "the region
bounded by", "inside", Lemma 3.10 `3 ⇒ 1` "follows from the Jordan curve theorem"). In the dart
model these are statements about cuts of the dual graph (a vertex per cell, an edge per segment):
an even set of segments cuts the cells into two classes. `Pca/Jordan.lean` proves this for
`Arrangement` (`exists_side`, by linear algebra over `𝔽₂`, from Euler and connectivity); package J
ports it to `SConf` (same proof; Euler and connectivity are axioms of `SConf`) and adds:

* `upper_arc`: the part of a curve above `S` is **one arc** (a curve crosses `S` at most twice,
  `two_int` with `S`; it crosses it an even number of times, by the side function). This is the
  graph-language content of SH's use of Lemma 3.5 in Lemma 3.9 Case 2 (p. 322: "so that curves go
  to infinity after crossing the sweep").
-/
import Pca.Sweep.J_Basic

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

/-- `r` cuts the cells along the set of segments `E`: the two cells at a segment get different
values iff the segment is in `E`. -/
def IsCut (E : Finset Γ.Segment) (r : Γ.Cell → ZMod 2) : Prop :=
  ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if Γ.segmentOf y ∈ E then 1 else 0

/-- `E` is even: every crossing is the end of an even number of darts with segment in `E`. -/
def IsEven (E : Finset Γ.Segment) : Prop :=
  ∀ x : Γ.Crossing, Even (x.darts.filter (fun y => Γ.segmentOf y ∈ E)).card

/-- A dart walks straight on along its curve within the upper side: `e = straight^k d` with all
darts in between above the sweep. -/
def UpperWalk (d e : D) : Prop :=
  ∃ k : ℕ, (∀ i ≤ k, Γ.Above ((Γ.straight ^ i) d)) ∧ (Γ.straight ^ k) d = e

/-! ## Helpers (package J) -/

/-- The two directions of a curve are different straight walks (port of
`Arrangement.not_sameCycle_straight_σσ`, `Pca/Side.lean`). -/
private theorem j_not_sameCycle_straight_σσ (d : D) :
    ¬ Γ.straight.SameCycle d (Γ.σ (Γ.σ d)) := by
  set τ : Perm D := Γ.σ * Γ.σ with hτdef
  have hτ : ∀ y, τ y = Γ.σ (Γ.σ y) := fun y => rfl
  have hττ : τ * τ = 1 := by
    ext y; simp only [Perm.mul_apply, hτ, Γ.j_σ4, Perm.one_apply]
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hconj : τ * Γ.straight * τ⁻¹ = Γ.straight⁻¹ := by
    rw [hτinv]
    ext y
    rw [Perm.mul_apply, Perm.mul_apply, hτ, hτ, j_straight_apply, Γ.j_σ4, eq_comm,
      Perm.inv_eq_iff_eq, j_straight_apply, j_α_α, Γ.j_σ4]
  have hcomm : ∀ j : ℤ, ∀ y, τ ((Γ.straight ^ j) y) = (Γ.straight ^ (-j)) (τ y) := by
    intro j y
    have h1 : (τ * Γ.straight * τ⁻¹) ^ j = τ * Γ.straight ^ j * τ⁻¹ := conj_zpow
    rw [hconj, inv_zpow', hτinv] at h1
    have := congrArg (fun p : Perm D => p (τ y)) h1
    simp only [Perm.mul_apply] at this
    rw [this, show τ (τ y) = y by rw [← Perm.mul_apply, hττ, Perm.one_apply]]
  rintro ⟨i, hi⟩
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' i
  · apply Γ.j_σσ_ne ((Γ.straight ^ j) d)
    rw [← hτ, hcomm, show τ d = (Γ.straight ^ i) d from hi.symm, ← Perm.mul_apply, ← zpow_add,
      hj]
    congr 2; ring
  · apply Γ.isSConf.α_ne ((Γ.straight ^ j) d)
    have h1 : τ ((Γ.straight ^ j) d) = Γ.straight ((Γ.straight ^ j) d) := by
      rw [hcomm, show τ d = (Γ.straight ^ i) d from hi.symm, ← Perm.mul_apply, ← zpow_add,
        ← Perm.mul_apply, ← zpow_one_add, hj]
      congr 2; ring
    have h2 : Γ.straight ((Γ.straight ^ j) d) = τ (Γ.α ((Γ.straight ^ j) d)) := rfl
    rw [h2] at h1
    exact (τ.injective h1).symm

private theorem j_exists_idx {d e : D} (h : Γ.straight.SameCycle d e) :
    ∃ k < period Γ.straight d, (Γ.straight ^ k) d = e := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 (mem_orbitList.2 h)
  exact ⟨k, List.mem_range.1 hk, by rw [Perm.coe_pow]⟩

private theorem j_pow_period (d : D) : (Γ.straight ^ period Γ.straight d) d = d := by
  rw [Perm.coe_pow]; exact iterate_period _ _

private theorem j_pow_inj {d : D} {i j : ℕ} (hi : i < period Γ.straight d)
    (hj : j < period Γ.straight d) (h : (Γ.straight ^ i) d = (Γ.straight ^ j) d) : i = j := by
  rw [period_eq_minimalPeriod] at hi hj
  rw [Perm.coe_pow, Perm.coe_pow] at h
  exact Function.iterate_injOn_Iio_minimalPeriod hi hj h

private theorem j_pow_succ (d : D) (i : ℕ) :
    (Γ.straight ^ (i + 1)) d = Γ.straight ((Γ.straight ^ i) d) := by
  rw [pow_succ', Perm.mul_apply]

private theorem j_curve_pow (d : D) (i : ℕ) : Γ.curve ((Γ.straight ^ i) d) = Γ.curve d := by
  induction i with
  | zero => rfl
  | succ i ih => rw [j_pow_succ, j_curve_straight, ih]

private theorem j_isSide (y : D) : Γ.side (Γ.cellOf y) + Γ.side (Γ.cellOf (Γ.α y)) =
    if Γ.curve y = Γ.S then 1 else 0 := Γ.isSide y

private theorem j_side_α {y : D} (hy : Γ.curve y ≠ Γ.S) :
    Γ.side (Γ.cellOf (Γ.α y)) = Γ.side (Γ.cellOf y) := by
  have h := Γ.j_isSide y
  rw [if_neg hy] at h
  rw [j_zmod2_eq_add_of_add_eq h, add_zero]

/-- Walking straight along a curve other than `S`, the side of `S` changes exactly at the
crossings with `S`. -/
private theorem j_side_straight (y : D) :
    Γ.side (Γ.cellOf (Γ.straight y)) =
      Γ.side (Γ.cellOf y) + if Γ.curve (Γ.σ (Γ.α y)) = Γ.S then 1 else 0 := by
  rw [j_straight_apply, j_cellOf_σ]
  have h := Γ.j_isSide (Γ.σ (Γ.α y))
  rw [← j_φ_apply, j_cellOf_φ] at h
  exact j_zmod2_eq_add_of_add_eq h

/-- The positions (within one period of the straight walk of `d`) at which the walk crosses
`S`. -/
private def j_flips (d : D) : Finset ℕ :=
  (range (period Γ.straight d)).filter
    (fun i => Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ i) d))) = Γ.S)

private theorem j_mem_flips {d : D} {i : ℕ} : i ∈ Γ.j_flips d ↔
    i < period Γ.straight d ∧ Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ i) d))) = Γ.S := by
  rw [j_flips, mem_filter, mem_range]

/-- The flips along the walk of `d` are the crossings of `curve d` with `S`. -/
private theorem j_card_flips {d : D} (hd : Γ.curve d ≠ Γ.S) :
    (Γ.j_flips d).card =
      (univ.filter (fun x : Γ.Crossing => Γ.curves x = {Γ.curve d, Γ.S})).card := by
  refine Finset.card_bij (fun i _ => Γ.crossingOf (Γ.α ((Γ.straight ^ i) d))) ?_ ?_ ?_
  · intro i hi
    rw [j_mem_flips] at hi
    rw [mem_filter, j_curves_crossingOf, j_curve_α, j_curve_pow, hi.2]
    exact ⟨mem_univ _, rfl⟩
  · intro i hi j hj h
    rw [j_mem_flips] at hi hj
    have h' : Γ.α ((Γ.straight ^ j) d) ∈ orbitList Γ.σ (Γ.α ((Γ.straight ^ i) d)) :=
      mem_orbitList.2 (Orbit.mk_eq_mk.1 h)
    rw [j_orbitList_σ] at h'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with h1 | h1 | h1 | h1
    · have h2 := congrArg Γ.α h1
      rw [j_α_α, j_α_α] at h2
      exact j_pow_inj Γ hi.1 hj.1 h2.symm
    · exfalso
      have h2 := congrArg Γ.curve h1
      rw [j_curve_α, j_curve_pow, hi.2] at h2
      exact hd h2
    · exfalso
      -- `α a_j = straight a_i`, so the walk of `d` contains both directions at `a_{i+1}`
      set a := Γ.straight ((Γ.straight ^ i) d) with ha
      have hja : (Γ.straight ^ j) d = Γ.α a := by
        rw [ha, j_straight_apply, ← h1, j_α_α]
      apply Γ.j_not_sameCycle_straight_σσ a
      have hda : Γ.straight.SameCycle d a := by
        rw [ha, ← j_pow_succ]; exact Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)
      have hdb : Γ.straight.SameCycle d (Γ.σ (Γ.σ a)) := by
        have : Γ.straight ((Γ.straight ^ j) d) = Γ.σ (Γ.σ a) := by
          rw [hja, j_straight_apply, j_α_α]
        rw [← this, ← j_pow_succ]; exact Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)
      exact hda.symm.trans hdb
    · exfalso
      have h2 := congrArg Γ.curve h1
      rw [j_curve_α, j_curve_pow, j_curve_σσ, hi.2] at h2
      exact hd h2
  · intro x hx
    rw [mem_filter] at hx
    have hγ : Γ.curve d ∈ Γ.curves x := by rw [hx.2]; exact mem_insert_self _ _
    obtain ⟨e, he, hce⟩ := mem_image.1 hγ
    have hx' : Γ.crossingOf e = x := Orbit.mem_darts.1 he
    obtain ⟨y, hy, hyx⟩ : ∃ y, Γ.straight.SameCycle d y ∧ Γ.crossingOf (Γ.α y) = x := by
      rcases Γ.isSConf.straight d e hce.symm with h | h
      · refine ⟨Γ.α (Γ.σ (Γ.σ e)), ?_, ?_⟩
        · have h3 : Γ.straight (Γ.α (Γ.σ (Γ.σ e))) = e := by
            rw [j_straight_apply, j_α_α, Γ.j_σ4]
          rw [← h3] at h
          exact Perm.sameCycle_apply_right.1 h
        · rw [j_α_α, j_crossingOf_σ, j_crossingOf_σ, hx']
      · refine ⟨Γ.α e, ?_, by rw [j_α_α, hx']⟩
        have h3 : Γ.straight (Γ.α e) = Γ.σ (Γ.σ e) := by rw [j_straight_apply, j_α_α]
        have h' : Γ.straight.SameCycle d (Γ.σ (Γ.σ e)) := h
        rw [← h3] at h'
        exact Perm.sameCycle_apply_right.1 h'
    obtain ⟨k, hk, rfl⟩ := Γ.j_exists_idx hy
    refine ⟨k, ?_, hyx⟩
    rw [j_mem_flips]
    refine ⟨hk, ?_⟩
    have h2 := hx.2
    rw [← hyx, j_curves_crossingOf, j_curve_α, j_curve_pow] at h2
    have hne := Γ.isSConf.curve_σ (Γ.α ((Γ.straight ^ k) d))
    rw [j_curve_α, j_curve_pow] at hne
    have hm : Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ k) d))) ∈ ({Γ.curve d, Γ.S} : Finset (Fin n)) := by
      rw [← h2]; exact mem_insert_of_mem (mem_singleton_self _)
    rcases mem_insert.1 hm with h | h
    · exact absurd h hne
    · exact mem_singleton.1 h

/-- The side along the walk of `d` (a curve other than `S`) is the side at `d` plus the number
of flips so far (the flips are only real crossings with `S` if `curve d ≠ S`). -/
private theorem j_side_pow (d : D) (k : ℕ) :
    Γ.side (Γ.cellOf ((Γ.straight ^ k) d)) = Γ.side (Γ.cellOf d) +
      ∑ i ∈ range k, if Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ i) d))) = Γ.S then (1 : ZMod 2) else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [j_pow_succ, Γ.j_side_straight, ih, sum_range_succ,
      add_assoc]

private theorem j_flips_even (d : D) : Even (Γ.j_flips d).card := by
  have h := Γ.j_side_pow d (period Γ.straight d)
  rw [j_pow_period, sum_boole] at h
  have h2 := congrArg (· + Γ.side (Γ.cellOf d)) h
  simp only [add_comm (Γ.side (Γ.cellOf d)), add_assoc, j_zmod2_add_self, add_zero] at h2
  exact (ZMod.natCast_eq_zero_iff_even).1 h2.symm

/-- Between two positions with different sides there is a flip. -/
private theorem j_flip_between {d : D} {a b : ℕ} (hab : a ≤ b)
    (h : Γ.side (Γ.cellOf ((Γ.straight ^ a) d)) ≠ Γ.side (Γ.cellOf ((Γ.straight ^ b) d))) :
    ∃ j, a ≤ j ∧ j < b ∧ Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ j) d))) = Γ.S := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd rfl h
  | succ b hab ih =>
    by_cases hP : Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ b) d))) = Γ.S
    · exact ⟨b, hab, Nat.lt_succ_self b, hP⟩
    · rw [j_pow_succ, Γ.j_side_straight, if_neg hP,
        add_zero] at h
      obtain ⟨j, h1, h2, h3⟩ := ih h
      exact ⟨j, h1, Nat.lt_succ_of_lt h2, h3⟩

variable {Γ}

/-- **Jordan** (cut form, SH passim): an even set of segments is a cut of the cells. -/
theorem exists_cut (E : Finset Γ.Segment) (hE : Γ.IsEven E) : ∃ r, Γ.IsCut E r := by
  obtain ⟨g, hg⟩ := Γ.j_mem_range_of_mem_ker (fun s => if s ∈ E then 1 else 0) (by
    funext x
    change ∑ y ∈ x.darts, (if Γ.segmentOf y ∈ E then (1 : ZMod 2) else 0) = 0
    rw [sum_boole]
    exact (ZMod.natCast_eq_zero_iff_even).2 (hE x))
  refine ⟨g, fun y => ?_⟩
  rw [← j_cellBdry_segmentOf, hg]

/-- The two cells at a segment are distinct. -/
theorem cellOf_α_ne (y : D) : Γ.cellOf (Γ.α y) ≠ Γ.cellOf y := by
  set c := Γ.curve y
  have hh : ∀ z, (if ∃ w ∈ (Γ.segmentOf z).darts, Γ.curve w = c then (1 : ZMod 2) else 0) =
      if Γ.curve z = c then 1 else 0 := by
    intro z
    simp only [j_darts_segmentOf, mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left,
      j_curve_α, or_self]
  obtain ⟨g, hg⟩ := Γ.j_mem_range_of_mem_ker
    (fun s => if ∃ w ∈ s.darts, Γ.curve w = c then 1 else 0) (by
      funext x
      obtain ⟨z, rfl⟩ := x.exists_mk
      change Γ.jSegBdry _ (Γ.crossingOf z) = 0
      rw [j_segBdry_crossingOf, hh, hh, hh, hh, j_curve_σσ, j_curve_σσ]
      split_ifs <;> decide)
  intro h
  have h1 := Γ.j_cellBdry_segmentOf g y
  rw [hg] at h1
  beta_reduce at h1
  rw [hh, h, j_zmod2_add_self, if_pos rfl] at h1
  exact absurd h1 (by decide)

/-- A curve `γ ≠ S` crosses the sweeping curve `0` or `2` times. -/
theorem card_sweep_crossings (γ : Fin n) (hγ : γ ≠ Γ.S) :
    (univ.filter (fun x : Γ.Crossing => Γ.curves x = {γ, Γ.S})).card = 0 ∨
    (univ.filter (fun x : Γ.Crossing => Γ.curves x = {γ, Γ.S})).card = 2 := by
  by_cases hex : ∃ d, Γ.curve d = γ
  · obtain ⟨d, rfl⟩ := hex
    rw [← Γ.j_card_flips hγ]
    have h2 : (Γ.j_flips d).card ≤ 2 := by
      rw [Γ.j_card_flips hγ]; exact Γ.isSConf.two_int _ _ hγ
    obtain ⟨r, hr⟩ := Γ.j_flips_even d
    omega
  · left
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x _ hx
    have hγx : γ ∈ Γ.curves x := by rw [hx]; exact mem_insert_self _ _
    obtain ⟨e, -, he⟩ := mem_image.1 hγx
    exact hex ⟨e, he⟩

/-- The part of a curve above the sweep is **one arc**: two darts of a curve above `S` lie on one
walk within the upper side (up to reversing directions). -/
theorem upper_arc {d e : D} (hd : Γ.Above d) (he : Γ.Above e) (h : Γ.curve d = Γ.curve e) :
    Γ.UpperWalk d e ∨ Γ.UpperWalk e d ∨ Γ.UpperWalk d (Γ.α e) ∨ Γ.UpperWalk (Γ.α e) d := by
  have hγ : Γ.curve d ≠ Γ.S := hd.1
  have hAα : Γ.Above (Γ.α e) := ⟨by rw [j_curve_α]; exact he.1, by
    show Γ.side _ = 1
    rw [Γ.j_side_α he.1]; exact he.2⟩
  suffices key : ∀ e', Γ.Above e' → Γ.straight.SameCycle d e' →
      Γ.UpperWalk d e' ∨ Γ.UpperWalk e' d by
    rcases Γ.isSConf.straight d e h with hc | hc
    · rcases key e he hc with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · have hc' : Γ.straight.SameCycle d (Γ.α e) := by
        have h3 : Γ.straight (Γ.α e) = Γ.σ (Γ.σ e) := by rw [j_straight_apply, j_α_α]
        have h' : Γ.straight.SameCycle d (Γ.σ (Γ.σ e)) := hc
        rw [← h3] at h'
        exact Perm.sameCycle_apply_right.1 h'
      rcases key _ hAα hc' with h1 | h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1))
  intro e' he' hc
  obtain ⟨k, hk, rfl⟩ := Γ.j_exists_idx hc
  by_cases hall : ∀ i ≤ k, Γ.Above ((Γ.straight ^ i) d)
  · exact Or.inl ⟨k, hall, rfl⟩
  right
  push Not at hall
  obtain ⟨i, hik, hi⟩ := hall
  have hsi : Γ.side (Γ.cellOf ((Γ.straight ^ i) d)) ≠ 1 :=
    fun hs => hi ⟨by rw [j_curve_pow]; exact hγ, hs⟩
  have hs0 : Γ.side (Γ.cellOf ((Γ.straight ^ 0) d)) = 1 := hd.2
  have hsk : Γ.side (Γ.cellOf ((Γ.straight ^ k) d)) = 1 := he'.2
  obtain ⟨j1, -, hj1, hP1⟩ := Γ.j_flip_between (Nat.zero_le i)
    (by rw [hs0]; exact fun h' => hsi h'.symm)
  obtain ⟨j2, hj2a, hj2b, hP2⟩ := Γ.j_flip_between hik (by rw [hsk]; exact hsi)
  have hF2 : (Γ.j_flips d).card ≤ 2 := by
    rw [Γ.j_card_flips hγ]; exact Γ.isSConf.two_int _ _ hγ
  have hnoflip : ∀ m, k ≤ m → m < period Γ.straight d →
      Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ m) d))) ≠ Γ.S := by
    intro m hkm hmp hm
    have hsub : ({j1, j2, m} : Finset ℕ) ⊆ Γ.j_flips d := by
      intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rw [j_mem_flips]
      rcases ht with rfl | rfl | rfl
      · exact ⟨by omega, hP1⟩
      · exact ⟨by omega, hP2⟩
      · exact ⟨hmp, hm⟩
    have h3 : ({j1, j2, m} : Finset ℕ).card = 3 :=
      card_eq_three.2 ⟨j1, j2, m, by omega, by omega, by omega, rfl⟩
    have := card_le_card hsub
    omega
  have hup : ∀ m, m + k ≤ period Γ.straight d →
      Γ.side (Γ.cellOf ((Γ.straight ^ (m + k)) d)) = 1 := by
    intro m
    induction m with
    | zero => intro _; rw [zero_add]; exact hsk
    | succ m ih =>
      intro hm
      rw [show m + 1 + k = m + k + 1 by omega, j_pow_succ,
        Γ.j_side_straight,
        if_neg (hnoflip _ (by omega) (by omega)), add_zero]
      exact ih (by omega)
  have hpow : ∀ m, (Γ.straight ^ m) ((Γ.straight ^ k) d) = (Γ.straight ^ (m + k)) d := by
    intro m; rw [← Perm.mul_apply, ← pow_add]
  refine ⟨period Γ.straight d - k, fun m hm => ?_, ?_⟩
  · rw [hpow]
    exact ⟨by rw [j_curve_pow]; exact hγ, hup m (by omega)⟩
  · rw [hpow, Nat.sub_add_cancel hk.le, j_pow_period]

end SConf

end Pca.Sweep
