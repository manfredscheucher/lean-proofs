/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Great-pseudocircle arrangements: basic facts (package A, `doc/pca/great.md` section 3.1)

* walks along a curve: every straight orbit has `2 (n - 1)` darts (any arrangement),
* in a great arrangement the crossings along a curve are antipodal: `ant d = straight^(n-1) d`
  starts at the other crossing of the same two curves,
* `ant` is an orientation-reversing automorphism: `ant σ = σ⁻¹ ant`, `ant α = α ant`,
  `ant ∘ ant = id`, and the antipodal cell `cellOf (α (ant d))` of `cellOf d` lies on the other
  side of every curve,
* sides of crossings (`crossSide`).
-/
import Pca.Great.Defs

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-! ## Walks (any arrangement) -/

theorem curve_straight_pow (k : ℕ) (d : D) : A.curve ((A.straight ^ k) d) = A.curve d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Perm.mul_apply, A.curve_straight, ih]

theorem crossingOf_straight_pow_succ (k : ℕ) (d : D) :
    A.crossingOf ((A.straight ^ (k + 1)) d) = A.crossingOf (A.α ((A.straight ^ k) d)) := by
  rw [pow_succ', Perm.mul_apply, A.crossingOf_straight]

/-- Every straight walk has `2 (n - 1)` darts (a curve has `2 (n - 1)` crossings). -/
theorem period_straight (A : Arrangement n D) (d : D) : period A.straight d = 2 * (n - 1) := by
  set S := orbitFinset A.straight d with hSdef
  have hσσ : Function.Injective (fun y => A.σ (A.σ y)) := fun x y h => by
    simpa [A.σ_σ_σ_σ] using congrArg (fun z => A.σ (A.σ z)) h
  have hU : univ.filter (fun e => A.curve e = A.curve d) =
      S ∪ S.image (fun y => A.σ (A.σ y)) := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image, hSdef, mem_orbitFinset]
    constructor
    · intro h
      rcases A.isArrangement.straight d e h.symm with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨_, h1, A.σ_σ_σ_σ e⟩
    · rintro (h1 | ⟨y, hy, rfl⟩)
      · obtain ⟨k, rfl⟩ := h1.exists_nat_pow_eq
        exact curve_straight_pow k d
      · obtain ⟨k, rfl⟩ := hy.exists_nat_pow_eq
        rw [A.curve_σσ, curve_straight_pow]
  have hdisj : Disjoint S (S.image (fun y => A.σ (A.σ y))) := by
    rw [disjoint_left]
    intro e he he'
    obtain ⟨y, hy, rfl⟩ := mem_image.1 he'
    rw [hSdef, mem_orbitFinset] at he hy
    exact A.not_sameCycle_straight_σσ y (hy.symm.trans he)
  have h := A.card_darts_on (A.curve d)
  rw [hU, card_union_of_disjoint hdisj, card_image_of_injective _ hσσ, hSdef,
    card_orbitFinset] at h
  omega

theorem straight_pow_period (A : Arrangement n D) (d : D) :
    (A.straight ^ (2 * (n - 1))) d = d := by
  rw [← period_straight A d, Perm.coe_pow]
  exact iterate_period _ _

/-- Going straight in the reverse direction: `straight (σ² e) = σ² (straight⁻¹ e)`. -/
theorem straight_σσ (A : Arrangement n D) (e : D) :
    A.straight (A.σ (A.σ e)) = A.σ (A.σ (A.straight.symm e)) := by
  rw [A.straight_symm_apply, A.straight_apply]

/-- The right cells of the darts of a curve `C` stay on the same side of `C` along the walk. -/
theorem side_straight_self {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) {y : D}
    (hy : A.curve y = C) : s (A.cellOf (A.straight y)) = s (A.cellOf y) := by
  have h1 := A.side_σσ hs (A.α y)
  have h2 := Arrangement.zmod2_eq_add_of_add_eq (hs y)
  have hσ : A.curve (A.σ (A.α y)) ≠ C := by
    rw [← hy, ← A.curve_α y]; exact A.isArrangement.curve_σ _
  rw [if_pos (by rw [A.curve_α, hy]), if_neg hσ, h2, if_pos hy] at h1
  rw [A.straight_apply, h1]
  have h3 : ∀ a : ZMod 2, a + 1 + 1 + 0 = a := by decide
  exact h3 _

theorem side_straight_pow_self {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) {d : D}
    (hd : A.curve d = C) (k : ℕ) : s (A.cellOf ((A.straight ^ k) d)) = s (A.cellOf d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, side_straight_self hs (by rw [curve_straight_pow, hd]), ih]

/-- Walking straight along a curve other than `C`, the side of `C` changes at every crossing
with `C`. -/
theorem side_straight_pow {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) {d : D}
    (hd : A.curve d ≠ C) (k : ℕ) :
    s (A.cellOf ((A.straight ^ k) d)) = s (A.cellOf d) +
      ((Ioc 0 k).filter (fun j =>
        C ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d)))).card := by
  rw [← sum_boole]
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : A.curve ((A.straight ^ k) d) ≠ C := by rwa [curve_straight_pow]
    have e : (if A.curve (A.σ (A.α ((A.straight ^ k) d))) = C then (1 : ZMod 2) else 0) =
        if C ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ (k + 1)) d))
          then 1 else 0 := by
      rw [crossingOf_straight_pow_succ]
      exact if_congr (A.mem_curves_end_iff hk).symm rfl rfl
    rw [sum_Ioc_succ_top (Nat.zero_le k), ← e, ← add_assoc, ← ih, ← A.side_straight hs hk,
      pow_succ', Perm.mul_apply]

/-- All four darts at a crossing not on `C` have their cell on the same side of `C`. -/
theorem crossSide_eq {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) {d : D}
    (hd : C ∉ Arrangement.Crossing.curves A (A.crossingOf d)) :
    A.crossSide s (A.crossingOf d) = s (A.cellOf d) := by
  unfold Arrangement.crossSide
  have hzd : A.crossingOf (Quotient.out (s := Perm.SameCycle.setoid A.σ) (A.crossingOf d)) =
      A.crossingOf d := Quotient.out_eq _
  generalize Quotient.out (s := Perm.SameCycle.setoid A.σ) (A.crossingOf d) = z at hzd ⊢
  have hc : C ∉ ({A.curve z, A.curve (A.σ z)} : Finset (Fin n)) := by
    rw [← A.curves_crossingOf, hzd]; exact hd
  simp only [mem_insert, mem_singleton, not_or] at hc
  have h1 : ∀ w, A.curve w ≠ C → s (A.cellOf (A.σ w)) = s (A.cellOf w) := fun w hw => by
    rw [A.side_σ hs, if_neg hw, add_zero]
  have h0 : A.curve z ≠ C := fun h => hc.1 h.symm
  have h0' : A.curve (A.σ z) ≠ C := fun h => hc.2 h.symm
  have hl := A.crossingOf_eq_iff.1 hzd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · rfl
  · rw [h1 _ h0]
  · rw [h1 _ h0', h1 _ h0]
  · rw [h1 _ (by rw [A.curve_σσ]; exact h0), h1 _ h0', h1 _ h0]

/-- Positions along a walk: the crossings of the first `2 (n - 1)` darts are distinct. -/
theorem straight_pow_inj {d : D} {i j : ℕ} (hi : i < 2 * (n - 1)) (hj : j < 2 * (n - 1))
    (h : A.crossingOf ((A.straight ^ i) d) = A.crossingOf ((A.straight ^ j) d)) : i = j := by
  have hcur : A.curve ((A.straight ^ j) d) = A.curve ((A.straight ^ i) d) := by
    rw [curve_straight_pow, curve_straight_pow]
  have hsc : A.straight.SameCycle ((A.straight ^ i) d) ((A.straight ^ j) d) :=
    Perm.sameCycle_pow_left.2 (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _))
  have hl := A.crossingOf_eq_iff.1 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h' | h' | h' | h'
  · rw [← period_straight A d, period_eq_minimalPeriod] at hi hj
    rw [Perm.coe_pow, Perm.coe_pow] at h'
    exact (Function.iterate_injOn_Iio_minimalPeriod hi hj h'.symm)
  · exact absurd (h' ▸ hcur) (A.isArrangement.curve_σ _)
  · exact absurd (h' ▸ hsc) (A.not_sameCycle_straight_σσ _)
  · rw [h', A.curve_σσσ] at hcur
    exact absurd hcur (A.isArrangement.curve_σ _)

theorem straight_pow_inj_zero {d : D} {j : ℕ} (hj : j < 2 * (n - 1))
    (h : A.crossingOf ((A.straight ^ j) d) = A.crossingOf d) : j = 0 :=
  straight_pow_inj (d := d) hj (by have := A.two_le_n; omega) (by rw [h, pow_zero]; rfl)

/-- Every crossing on the curve of `d` is met by the walk of `d` within `2 (n - 1)` steps. -/
theorem exists_straight_pow_eq {d : D} {x : A.Crossing}
    (hx : A.curve d ∈ Arrangement.Crossing.curves A x) :
    ∃ k < 2 * (n - 1), A.crossingOf ((A.straight ^ k) d) = x := by
  have hsub : (range (2 * (n - 1))).image (fun k => A.crossingOf ((A.straight ^ k) d)) ⊆
      A.crossingsOn (A.curve d) := by
    intro y hy
    obtain ⟨k, -, rfl⟩ := mem_image.1 hy
    simp only [Arrangement.crossingsOn, mem_filter, mem_univ, true_and]
    rw [← curve_straight_pow k d]
    exact A.mem_curves_crossingOf _
  have hcard : ((range (2 * (n - 1))).image
      (fun k => A.crossingOf ((A.straight ^ k) d))).card = 2 * (n - 1) := by
    rw [card_image_of_injOn, card_range]
    intro i hi j hj h
    exact straight_pow_inj (mem_range.1 hi) (mem_range.1 hj) h
  have heq := eq_of_subset_of_card_le hsub (by rw [hcard, A.card_crossingsOn])
  have hmem : x ∈ A.crossingsOn (A.curve d) := by
    simp only [Arrangement.crossingsOn, mem_filter, mem_univ, true_and]; exact hx
  rw [← heq] at hmem
  obtain ⟨k, hk, rfl⟩ := mem_image.1 hmem
  exact ⟨k, mem_range.1 hk, rfl⟩

/-- A pair of curves has two crossings: two crossings `≠ x` with the curves of `x` are equal. -/
theorem eq_of_curves_eq {x y z : A.Crossing}
    (hy : Arrangement.Crossing.curves A y = Arrangement.Crossing.curves A x)
    (hz : Arrangement.Crossing.curves A z = Arrangement.Crossing.curves A x)
    (hyx : y ≠ x) (hzx : z ≠ x) : y = z := by
  obtain ⟨w, rfl⟩ := x.exists_mk
  have h2 := A.card_curves_eq_pair (A.curve w) (A.curve (A.σ w))
    (A.isArrangement.curve_σ w).symm
  rw [← A.curves_crossingOf w] at h2
  obtain ⟨p, q, -, he⟩ := card_eq_two.1 h2
  have hmem : ∀ v, Arrangement.Crossing.curves A v =
      Arrangement.Crossing.curves A (A.crossingOf w) → v = p ∨ v = q := fun v hv => by
    have : v ∈ ({p, q} : Finset A.Crossing) := by rw [← he]; simpa using hv
    simpa using this
  have hx := hmem (A.crossingOf w) rfl
  have hy' := hmem y hy
  have hz' := hmem z hz
  change y ≠ A.crossingOf w at hyx
  change z ≠ A.crossingOf w at hzx
  rcases hx with hx | hx <;> rcases hy' with rfl | rfl <;> rcases hz' with rfl | rfl <;>
    first | rfl | exact absurd hx.symm hyx | exact absurd hx.symm hzx

/-! ## Antipodality in great arrangements -/

/-- The antipodal dart: `n - 1` steps straight ahead. -/
def ant (A : Arrangement n D) (d : D) : D := (A.straight ^ (n - 1)) d

theorem curve_ant (A : Arrangement n D) (d : D) : A.curve (ant A d) = A.curve d :=
  curve_straight_pow _ d

theorem ant_ant (A : Arrangement n D) (d : D) : ant A (ant A d) = d := by
  rw [ant, ant, ← Perm.mul_apply, ← pow_add, ← two_mul, straight_pow_period]

theorem straight_pow_inv_apply (A : Arrangement n D) (y : D) :
    (A.straight ^ (n - 1))⁻¹ y = (A.straight ^ (n - 1)) y := by
  rw [Perm.inv_eq_iff_eq, ← Perm.mul_apply, ← pow_add, ← two_mul, straight_pow_period]

/-- A map reversing the straight walks commutes with `ant`. -/
theorem ant_comm (τ : D → D) (hτ : ∀ y, τ (A.straight y) = A.straight⁻¹ (τ y)) (d : D) :
    τ (ant A d) = ant A (τ d) := by
  have key : ∀ k y, τ ((A.straight ^ k) y) = (A.straight ^ k)⁻¹ (τ y) := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      conv_lhs => rw [pow_succ, Perm.mul_apply]
      rw [ih, hτ, pow_succ', mul_inv_rev, Perm.mul_apply]
  rw [ant, key, straight_pow_inv_apply]
  rfl

theorem ant_α (A : Arrangement n D) (d : D) : ant A (A.α d) = A.α (ant A d) := by
  refine (ant_comm A.α (fun y => ?_) d).symm
  rw [Perm.inv_def, A.straight_symm_apply, A.straight_apply]

theorem ant_σσ (A : Arrangement n D) (d : D) : ant A (A.σ (A.σ d)) = A.σ (A.σ (ant A d)) := by
  refine (ant_comm (fun y => A.σ (A.σ y)) (fun y => ?_) d).symm
  show A.σ (A.σ (A.straight y)) = A.straight⁻¹ (A.σ (A.σ y))
  rw [A.σσ_straight, Perm.inv_def, A.straight_symm_apply, A.σ_σ_σ_σ]

variable (hA : A.IsGreat)
include hA

/-- The core of the great case: walking `n - 1` steps along `c` from a crossing `x` with `b`, one
reaches the other crossing of `b` and `c`. The other crossing is at some position `r`; every third
curve `a` separates the two crossings, so exactly one of the two crossings of `a` and `c` lies
strictly between, and counting the `r - 1` crossings strictly between gives `r - 1 = n - 2`. -/
theorem great_walk (d : D) :
    Arrangement.Crossing.curves A (A.crossingOf (ant A d)) =
        Arrangement.Crossing.curves A (A.crossingOf d) ∧
      A.crossingOf (ant A d) ≠ A.crossingOf d := by
  have hn := A.two_le_n
  have hbc : A.curve (A.σ d) ≠ A.curve d := A.isArrangement.curve_σ d
  have hx0 := A.curves_crossingOf d
  -- the other crossing `y` of the two curves at `d`
  obtain ⟨y, hy, hyx⟩ : ∃ y, Arrangement.Crossing.curves A y =
      Arrangement.Crossing.curves A (A.crossingOf d) ∧ y ≠ A.crossingOf d := by
    have h2 := A.card_curves_eq_pair (A.curve d) (A.curve (A.σ d)) hbc.symm
    obtain ⟨p, q, hpq, he⟩ := card_eq_two.1 h2
    have hmem : ∀ v, v ∈ ({p, q} : Finset A.Crossing) ↔
        Arrangement.Crossing.curves A v = {A.curve d, A.curve (A.σ d)} := fun v => by
      rw [← he]; simp
    by_cases hp : p = A.crossingOf d
    · exact ⟨q, by rw [(hmem q).1 (by simp), hx0], fun h => hpq (hp.trans h.symm)⟩
    · exact ⟨p, by rw [(hmem p).1 (by simp), hx0], hp⟩
  obtain ⟨r, hr, rfl⟩ := exists_straight_pow_eq (d := d)
    (x := y) (by rw [hy]; exact A.mem_curves_crossingOf d)
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hyx (by rw [pow_zero]; rfl)
  -- the curve crossed at position `j`, `0 < j < r`, is a third curve
  have hfib : ∀ j ∈ Ioo 0 r,
      A.curve (A.σ ((A.straight ^ j) d)) ∈ (univ.erase (A.curve (A.σ d))).erase (A.curve d) := by
    intro j hj
    obtain ⟨hj0, hjr⟩ := mem_Ioo.1 hj
    have hcj := curve_straight_pow (A := A) j d
    refine mem_erase.2 ⟨?_, mem_erase.2 ⟨fun h => ?_, mem_univ _⟩⟩
    · rw [← hcj]; exact A.isArrangement.curve_σ _
    · have hcur : Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d)) =
          Arrangement.Crossing.curves A (A.crossingOf d) := by
        rw [A.curves_crossingOf, hcj, h, hx0]
      have hne : A.crossingOf ((A.straight ^ j) d) ≠ A.crossingOf d := fun h' =>
        (Nat.pos_iff_ne_zero.1 hj0) (straight_pow_inj_zero (A := A) (by omega) h')
      have := eq_of_curves_eq hcur hy hne hyx
      exact absurd (straight_pow_inj (by omega) hr this) (by omega)
  -- every third curve is crossed exactly once strictly between
  have hcount : ∀ a ∈ (univ.erase (A.curve (A.σ d))).erase (A.curve d),
      ((Ioo 0 r).filter (fun j => A.curve (A.σ ((A.straight ^ j) d)) = a)).card = 1 := by
    intro a ha
    obtain ⟨hac, ha'⟩ := mem_erase.1 ha
    have hab := (mem_erase.1 ha').1
    obtain ⟨s, hs⟩ := Arrangement.exists_isSide (A := A) a
    have hside := side_straight_pow hs (Ne.symm hac) r
    have hF : (Ioc 0 r).filter (fun j =>
        a ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d))) =
        (Ioo 0 r).filter (fun j => A.curve (A.σ ((A.straight ^ j) d)) = a) := by
      ext j
      simp only [mem_filter, mem_Ioc, mem_Ioo, A.curves_crossingOf, curve_straight_pow,
        mem_insert, mem_singleton]
      constructor
      · rintro ⟨⟨hj0, hjr⟩, h | h⟩
        · exact absurd h hac
        · refine ⟨⟨hj0, lt_of_le_of_ne hjr fun hjr' => ?_⟩, h.symm⟩
          subst hjr'
          have hmem : a ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d)) := by
            rw [A.curves_crossingOf, curve_straight_pow, ← h]; simp
          rw [hy, hx0] at hmem
          simp only [mem_insert, mem_singleton] at hmem
          rcases hmem with h' | h'
          · exact hac h'
          · exact hab h'
      · rintro ⟨⟨hj0, hjr⟩, h⟩
        exact ⟨⟨hj0, hjr.le⟩, Or.inr h.symm⟩
    rw [hF] at hside
    have hg := hA (A.curve d) (A.curve (A.σ d)) a hbc.symm (Ne.symm hac) (Ne.symm hab) s hs
      (A.crossingOf d) (A.crossingOf ((A.straight ^ r) d)) hyx.symm hx0 (hy.trans hx0)
      d (Orbit.mem_darts.2 rfl) _ (Orbit.mem_darts.2 rfl)
    rw [hside] at hg
    have hle : ((Ioo 0 r).filter (fun j => A.curve (A.σ ((A.straight ^ j) d)) = a)).card ≤ 2 := by
      rw [← A.card_curves_eq_pair (A.curve d) a (Ne.symm hac)]
      refine card_le_card_of_injOn (fun j => A.crossingOf ((A.straight ^ j) d)) ?_ ?_
      · intro j hj
        simp only [coe_filter, Set.mem_setOf_eq, mem_Ioo] at hj
        simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
        rw [A.curves_crossingOf, curve_straight_pow, hj.2]
      · intro i hi j hj h
        simp only [coe_filter, Set.mem_setOf_eq, mem_Ioo] at hi hj
        exact straight_pow_inj (by omega) (by omega) h
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    interval_cases h : ((Ioo 0 r).filter (fun j => A.curve (A.σ ((A.straight ^ j) d)) = a)).card
    · simp at hg
    · rfl
    · rw [h2, add_zero] at hg; exact absurd rfl hg
  have hsum := card_eq_sum_card_fiberwise (fun j hj => hfib j hj)
  rw [sum_congr rfl hcount, sum_const, smul_eq_mul, mul_one,
    card_erase_of_mem (mem_erase.2 ⟨Ne.symm hbc, mem_univ _⟩), card_erase_of_mem (mem_univ _),
    card_univ, Fintype.card_fin, Nat.card_Ioo] at hsum
  have hrm : r = n - 1 := by omega
  subst hrm
  exact ⟨hy, hyx⟩

/-- The antipodal dart starts at a crossing of the same two curves ... -/
theorem curves_ant (d : D) :
    Arrangement.Crossing.curves A (A.crossingOf (ant A d)) =
      Arrangement.Crossing.curves A (A.crossingOf d) :=
  (great_walk hA d).1

/-- ... but at the other one. -/
theorem crossingOf_ant_ne (d : D) : A.crossingOf (ant A d) ≠ A.crossingOf d :=
  (great_walk hA d).2

/-- Along a curve, the crossings strictly between a crossing and its antipode meet every other
curve exactly once: for `0 < i < n - 1`, ... (the precise form is up to package A; this is the
statement used downstream). For `k ≤ 2 (n - 1)` steps, the walk of `d` meets the antipodal crossing
of `crossingOf d` exactly at `k = n - 1` among `0 < k < 2 (n - 1)`. -/
theorem crossingOf_straight_pow_eq_iff (d : D) {k : ℕ} (hk : k < 2 * (n - 1)) :
    Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ k) d)) =
        Arrangement.Crossing.curves A (A.crossingOf d) ↔ k = 0 ∨ k = n - 1 := by
  have hn := A.two_le_n
  constructor
  · intro h
    by_cases h0 : A.crossingOf ((A.straight ^ k) d) = A.crossingOf d
    · exact Or.inl (straight_pow_inj_zero hk h0)
    · exact Or.inr (straight_pow_inj hk (by omega)
        (eq_of_curves_eq h (curves_ant hA d) h0 (crossingOf_ant_ne hA d)))
  · rintro (rfl | rfl)
    · rw [pow_zero]; rfl
    · exact curves_ant hA d

/-- The side of `C` changes from `d` to `ant d` unless `d` lies on `C`. -/
theorem side_ant {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) (d : D) :
    s (A.cellOf (ant A d)) = s (A.cellOf d) + if A.curve d = C then 0 else 1 := by
  have hn := A.two_le_n
  by_cases hdC : A.curve d = C
  · rw [if_pos hdC, add_zero]; exact side_straight_pow_self hs hdC _
  rw [if_neg hdC]
  by_cases hσC : A.curve (A.σ d) = C
  · -- `C` is the other curve at `d`: it is crossed exactly at position `n - 1`
    have hF : (Ioc 0 (n - 1)).filter (fun j =>
        C ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d))) = {n - 1} := by
      ext j
      simp only [mem_filter, mem_Ioc, mem_singleton]
      constructor
      · rintro ⟨⟨hj0, hjm⟩, h⟩
        have hcur : Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d)) =
            Arrangement.Crossing.curves A (A.crossingOf d) := by
          rw [A.curves_eq_pair (A.mem_curves_crossingOf _) h (by rwa [curve_straight_pow]),
            curve_straight_pow, A.curves_crossingOf, hσC]
        rcases (crossingOf_straight_pow_eq_iff hA d (by omega)).1 hcur with h' | h'
        · omega
        · exact h'
      · rintro rfl
        refine ⟨⟨by omega, le_rfl⟩, ?_⟩
        show C ∈ Arrangement.Crossing.curves A (A.crossingOf (ant A d))
        rw [curves_ant hA d, ← hσC]
        exact A.mem_curves_crossingOf_σ d
    have h := side_straight_pow hs hdC (n - 1)
    rw [hF, card_singleton, Nat.cast_one] at h
    exact h
  · -- `C` is a third curve: it separates the two crossings
    have hg := hA (A.curve d) (A.curve (A.σ d)) C (Ne.symm (A.isArrangement.curve_σ d)) hdC hσC
      s hs (A.crossingOf d) (A.crossingOf (ant A d)) (crossingOf_ant_ne hA d).symm
      (A.curves_crossingOf d) ((curves_ant hA d).trans (A.curves_crossingOf d))
      d (Orbit.mem_darts.2 rfl) _ (Orbit.mem_darts.2 rfl)
    have hz : ∀ a b : ZMod 2, a ≠ b → b = a + 1 := by decide
    exact hz _ _ hg

/-- `ant` reverses the orientation: `ant (σ d) = σ⁻¹ (ant d)`. -/
theorem ant_σ (d : D) : ant A (A.σ d) = A.σ (A.σ (A.σ (ant A d))) := by
  obtain ⟨s, hs⟩ := Arrangement.exists_isSide (A := A) (A.curve d)
  have hc := A.isArrangement.curve_σ d
  -- `ant (σ d)` starts at the crossing of `ant d`, on the other curve
  have hx : A.crossingOf (ant A (A.σ d)) = A.crossingOf (ant A d) := by
    refine eq_of_curves_eq (x := A.crossingOf d) ?_ (curves_ant hA d) ?_ (crossingOf_ant_ne hA d)
    · rw [curves_ant hA, A.crossingOf_σ]
    · rw [← A.crossingOf_σ d]; exact crossingOf_ant_ne hA _
  have hl := A.crossingOf_eq_iff.1 hx.symm
  have hcur : A.curve (ant A (A.σ d)) = A.curve (A.σ d) := curve_ant A _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h
  · rw [h, curve_ant] at hcur; exact absurd hcur.symm hc
  · -- `ant (σ d) = σ (ant d)` is impossible: compare the sides of `curve d`
    exfalso
    have h1 := side_ant hA hs (A.σ d)
    rw [if_neg hc, A.cellOf_σ, Arrangement.zmod2_eq_add_of_add_eq (hs d), if_pos rfl, h,
      A.cellOf_σ, Arrangement.zmod2_eq_add_of_add_eq (hs (ant A d)), if_pos (curve_ant A d),
      side_ant hA hs d, if_pos rfl, add_zero] at h1
    have hz : ∀ a : ZMod 2, a + 1 ≠ a + 1 + 1 := by decide
    exact hz _ h1
  · rw [h, A.curve_σσ, curve_ant] at hcur; exact absurd hcur.symm hc
  · exact h

/-- `ant (φ d) = σ⁻¹ (α (ant d))`. -/
theorem ant_φ (d : D) : ant A (A.φ d) = A.σ (A.σ (A.σ (A.α (ant A d)))) := by
  rw [A.φ_apply, ant_σ hA, ant_α]

/-- `ant` maps cells to cells: the antipodal cell of `cellOf d` is `cellOf (α (ant d))`. -/
theorem cellOf_α_ant_eq {d e : D} (h : A.cellOf d = A.cellOf e) :
    A.cellOf (A.α (ant A d)) = A.cellOf (A.α (ant A e)) := by
  have step : ∀ z, A.cellOf (A.α (ant A (A.φ z))) = A.cellOf (A.α (ant A z)) := fun z => by
    rw [ant_φ hA, ← A.cellOf_φ (A.α (A.σ (A.σ (A.σ (A.α (ant A z)))))), A.φ_apply, A.α_α,
      A.σ_σ_σ_σ]
  have hk : ∀ k : ℕ, A.cellOf (A.α (ant A ((A.φ ^ k) d))) = A.cellOf (A.α (ant A d)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', Perm.mul_apply, step, ih]
  obtain ⟨k, rfl⟩ := (A.cellOf_eq_iff.1 h).exists_nat_pow_eq
  exact (hk k).symm

/-- The darts of the antipodal cell. -/
theorem mem_darts_cellOf_α_ant {d e : D} :
    e ∈ (A.cellOf (A.α (ant A d))).darts ↔ A.α (ant A e) ∈ (A.cellOf d).darts := by
  rw [Orbit.mem_darts, Orbit.mem_darts]
  change A.cellOf e = A.cellOf (A.α (ant A d)) ↔ A.cellOf (A.α (ant A e)) = A.cellOf d
  constructor
  · intro h
    rw [cellOf_α_ant_eq hA h, ant_α, A.α_α, ant_ant]
  · intro h
    rw [← cellOf_α_ant_eq hA h, ant_α, A.α_α, ant_ant]

/-- The antipodal cell lies on the other side of every curve. -/
theorem side_cellOf_α_ant {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) (d : D) :
    s (A.cellOf (A.α (ant A d))) = s (A.cellOf d) + 1 := by
  rw [Arrangement.zmod2_eq_add_of_add_eq (hs (ant A d)), side_ant hA hs, curve_ant]
  by_cases h : A.curve d = C
  · rw [if_pos h, if_pos h, add_zero]
  · rw [if_neg h, if_neg h, add_zero]

/-- For `n ≥ 3` a great arrangement has no digon. -/
theorem not_isDigon (h3 : 3 ≤ n) (f : A.Cell) : ¬ A.IsDigon f := by
  intro hf
  obtain ⟨d, rfl⟩ := A.exists_cellOf f
  have h0 := Arrangement.Digon.curves_corner hf (x := A.crossingOf d)
    (mem_image.2 ⟨d, A.mem_darts_cellOf_self d, rfl⟩)
  have h1 := Arrangement.Digon.curves_corner hf (x := A.crossingOf (A.φ d))
    (mem_image.2 ⟨A.φ d, by rw [← A.cellOf_φ d]; exact A.mem_darts_cellOf_self _, rfl⟩)
  have hk : Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ 1) d)) =
      Arrangement.Crossing.curves A (A.crossingOf d) := by
    rw [crossingOf_straight_pow_succ, pow_zero, Perm.one_apply, ← A.crossingOf_φ, h1, h0]
  rcases (crossingOf_straight_pow_eq_iff hA d (by omega)).1 hk with h | h <;> omega

end Pca.Great
