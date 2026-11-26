/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: combinatorial sides are geometric sides (`doc/pca/circ.md`)

For a circle representation of `A`, curves `a ≠ c` and the two crossings `z₁, z₂` of `a` and `c`:
walking along `a`, the side of `c` (a side function, `Pca/Side.lean`) changes exactly when the
point crosses the chord `z₁ z₂` of the circle of `a` (`side_ne_iff`). This is the bridge between
the combinatorial Krupp condition and the planes (Fact 1, `Pca/Circ/Fact1.lean`).
-/
import Pca.Circ.Defs
import Pca.Circ.Circle

open Equiv Finset Matrix

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}
  {u : Fin n → V} {h : Fin n → ℝ} {pt : A.Crossing → V} {sgn : D → ℝ}

/-- A crossing on the curve `i` has a dart on `i`. -/
theorem exists_dart_of_mem {x : A.Crossing} {i : Fin n}
    (hi : i ∈ Arrangement.Crossing.curves A x) : ∃ d, A.crossingOf d = x ∧ A.curve d = i := by
  obtain ⟨d, rfl⟩ := Orbit.exists_mk x
  change i ∈ Arrangement.Crossing.curves A (A.crossingOf d) at hi
  rw [A.curves_crossingOf, mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact ⟨d, rfl, rfl⟩
  · exact ⟨A.σ d, A.crossingOf_σ d, rfl⟩

theorem crossingOf_of_mem_darts {x : A.Crossing} {d : D} (hd : d ∈ x.darts) :
    A.crossingOf d = x := Orbit.mem_darts.1 hd

/-- Products of `±1`-scaled positive numbers. -/
theorem mul_pos_of_sgn {s P Q : ℝ} (hs : s = 1 ∨ s = -1) (hP : 0 < s * P) (hQ : 0 < s * Q) :
    0 < P * Q := by
  have h := mul_pos hP hQ
  rcases hs with rfl | rfl <;> nlinarith

/-- The parity bit of a nonzero real. -/
noncomputable def bit (p : ℝ) : ZMod 2 := if 0 < p then 1 else 0

theorem bit_eq_of_mul_pos {p q : ℝ} (h : 0 < p * q) : bit q = bit p := by
  unfold bit
  rcases lt_trichotomy p 0 with hp | hp | hp
  · have : q < 0 := by by_contra hc; push_neg at hc; nlinarith
    rw [if_neg (not_lt.2 this.le), if_neg (not_lt.2 hp.le)]
  · rw [hp, zero_mul] at h; exact absurd h (lt_irrefl _)
  · have : 0 < q := by by_contra hc; push_neg at hc; nlinarith
    rw [if_pos hp, if_pos this]

theorem bit_eq_add_one_of_mul_neg {p q : ℝ} (h : p * q < 0) : bit q = bit p + 1 := by
  unfold bit
  rcases lt_trichotomy p 0 with hp | hp | hp
  · have : 0 < q := by by_contra hc; push_neg at hc; nlinarith
    rw [if_pos this, if_neg (not_lt.2 hp.le)]; decide
  · rw [hp, zero_mul] at h; exact absurd h (lt_irrefl _)
  · have : q < 0 := by by_contra hc; push_neg at hc; nlinarith
    rw [if_pos hp, if_neg (not_lt.2 this.le)]; decide

theorem mul_neg_iff_bit_ne {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) : p * q < 0 ↔ bit p ≠ bit q := by
  constructor
  · intro h; rw [bit_eq_add_one_of_mul_neg h]
    generalize bit p = b; revert b; decide
  · intro h
    rcases lt_or_gt_of_ne (mul_ne_zero hp hq) with h' | h'
    · exact h'
    · exact absurd (bit_eq_of_mul_pos h').symm h

theorem zmod2_aux₂ (a b : ZMod 2) : a + b = a + (b + 1 + 1 + 0) := by revert a b; decide
theorem zmod2_aux₁ (a b : ZMod 2) : a + b + 1 = a + (b + 1 + 0) := by revert a b; decide
theorem zmod2_aux₀ (a b : ZMod 2) : a + b = a + (b + 0) := by revert a b; decide

namespace IsCircleRep

variable (R : IsCircleRep A u h pt sgn)
include R

theorem u_ne_zero (i : Fin n) : u i ≠ 0 := by
  intro h0
  have := R.isCircle i
  rw [h0, zero_dotProduct] at this
  nlinarith [sq_nonneg (h i)]

theorem onCirc {x : A.Crossing} {i : Fin n} (hi : i ∈ Arrangement.Crossing.curves A x) :
    OnCirc (u i) (h i) (pt x) := by
  obtain ⟨d, rfl, rfl⟩ := exists_dart_of_mem hi
  exact ⟨R.on_sphere _, R.on_plane d⟩

theorem sgn_straight (e : D) : sgn (A.straight e) = sgn e := by
  rw [Arrangement.straight_apply, R.sgn_σσ, R.sgn_α, neg_neg]

theorem sgn_straight_pow (k : ℕ) (d : D) : sgn ((A.straight ^ k) d) = sgn d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', Perm.mul_apply, R.sgn_straight, ih]

/-- `next` along a walk: the crossing after `X j` is `X (j + 1)`. -/
theorem next_walk (d : D) (j : ℕ) (z : A.Crossing)
    (hz : A.curve d ∈ Arrangement.Crossing.curves A z)
    (h1 : z ≠ A.crossingOf ((A.straight ^ j) d))
    (h2 : z ≠ A.crossingOf ((A.straight ^ (j + 1)) d)) :
    0 < sgn d * orient (u (A.curve d)) (pt (A.crossingOf ((A.straight ^ j) d)))
      (pt (A.crossingOf ((A.straight ^ (j + 1)) d))) (pt z) := by
  have := R.next ((A.straight ^ j) d) z (by rw [Great.curve_straight_pow]; exact hz) h1
    (by rw [← Great.crossingOf_straight_pow_succ]; exact h2)
  rwa [Great.curve_straight_pow, R.sgn_straight_pow, ← Great.crossingOf_straight_pow_succ]
    at this

end IsCircleRep

/-- The crossings with curves `{a, c}` are `z₁, z₂`. -/
theorem mem_pair_iff {a c : Fin n} {z₁ z₂ x : A.Crossing} (hz : z₁ ≠ z₂)
    (hz₁ : Arrangement.Crossing.curves A z₁ = {a, c})
    (hz₂ : Arrangement.Crossing.curves A z₂ = {a, c}) (hac : a ≠ c)
    (ha : a ∈ Arrangement.Crossing.curves A x) :
    c ∈ Arrangement.Crossing.curves A x ↔ x = z₁ ∨ x = z₂ := by
  constructor
  · intro hc
    have hx := A.curves_eq_pair ha hc hac
    by_contra hne
    push_neg at hne
    exact hz (Great.eq_of_curves_eq (x := x) (hz₁.trans hx.symm) (hz₂.trans hx.symm)
      hne.1.symm hne.2.symm)
  · rintro (rfl | rfl)
    · rw [hz₁]; simp
    · rw [hz₂]; simp

theorem orient_pair_mul {w : V} {p₁ p₂ q₁ q₂ x y : V}
    (h : (q₁ = p₁ ∧ q₂ = p₂) ∨ (q₁ = p₂ ∧ q₂ = p₁)) :
    orient w p₁ p₂ x * orient w p₁ p₂ y = orient w q₁ q₂ x * orient w q₁ q₂ y := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [orient_swap w q₂ q₁ x, orient_swap w q₂ q₁ y]; ring

namespace IsCircleRep

variable (R : IsCircleRep A u h pt sgn)
include R

/-- **Walk invariant.** Walking along the curve of `d` (from a crossing not on `c`), the side of
the chord `z₁ z₂` (the crossings of `c`) changes exactly at the crossings with `c`. -/
theorem walk_bit (d : D) {c : Fin n} (hc : A.curve d ≠ c) {z₁ z₂ : A.Crossing} (hz : z₁ ≠ z₂)
    (hz₁ : Arrangement.Crossing.curves A z₁ = {A.curve d, c})
    (hz₂ : Arrangement.Crossing.curves A z₂ = {A.curve d, c})
    (h0 : c ∉ Arrangement.Crossing.curves A (A.crossingOf d)) :
    ∀ j, j < 2 * (n - 1) → c ∉ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d)) →
      bit (orient (u (A.curve d)) (pt z₁) (pt z₂) (pt (A.crossingOf ((A.straight ^ j) d)))) =
        bit (orient (u (A.curve d)) (pt z₁) (pt z₂) (pt (A.crossingOf d))) +
          ∑ i ∈ Ioc 0 j,
            if c ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ i) d)) then 1 else 0
    := by
  set a := A.curve d
  set X : ℕ → A.Crossing := fun j => A.crossingOf ((A.straight ^ j) d) with hX
  set o : V → ℝ := orient (u a) (pt z₁) (pt z₂) with ho
  have hua := R.u_ne_zero a
  have haX : ∀ j, a ∈ Arrangement.Crossing.curves A (X j) := fun j => by
    have := A.mem_curves_crossingOf ((A.straight ^ j) d)
    rwa [Great.curve_straight_pow] at this
  have hP : ∀ j, c ∈ Arrangement.Crossing.curves A (X j) ↔ X j = z₁ ∨ X j = z₂ := fun j =>
    mem_pair_iff hz hz₁ hz₂ hc (haX j)
  have hXinj : ∀ i j, i < 2 * (n - 1) → j < 2 * (n - 1) → i ≠ j → pt (X i) ≠ pt (X j) :=
    fun i j hi hj hij he => hij (Great.straight_pow_inj hi hj (R.inj he))
  have hcz₁ : c ∈ Arrangement.Crossing.curves A z₁ := by rw [hz₁]; simp
  have hcz₂ : c ∈ Arrangement.Crossing.curves A z₂ := by rw [hz₂]; simp
  have haz₁ : a ∈ Arrangement.Crossing.curves A z₁ := by rw [hz₁]; simp
  have haz₂ : a ∈ Arrangement.Crossing.curves A z₂ := by rw [hz₂]; simp
  have hne_of : ∀ {x y : A.Crossing}, c ∈ Arrangement.Crossing.curves A x →
      c ∉ Arrangement.Crossing.curves A y → pt x ≠ pt y := fun hx hy he => by
    rw [R.inj he] at hx; exact hy hx
  have hC : ∀ j, OnCirc (u a) (h a) (pt (X j)) := fun j => R.onCirc (haX j)
  have hC₁ : OnCirc (u a) (h a) (pt z₁) := R.onCirc haz₁
  have hC₂ : OnCirc (u a) (h a) (pt z₂) := R.onCirc haz₂
  have hpz : pt z₁ ≠ pt z₂ := fun he => hz (R.inj he)
  have hsum : ∀ k, (∑ i ∈ Ioc 0 (k + 1), (if c ∈ Arrangement.Crossing.curves A (X i) then
      (1 : ZMod 2) else 0)) = (∑ i ∈ Ioc 0 k, if c ∈ Arrangement.Crossing.curves A (X i) then
      (1 : ZMod 2) else 0) + if c ∈ Arrangement.Crossing.curves A (X (k + 1)) then 1 else 0 :=
    fun k => Finset.sum_Ioc_succ_top (Nat.zero_le k) _
  have hn := A.two_le_n
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj hcj
  rcases j with _ | k
  · simp
  · by_cases hk : c ∈ Arrangement.Crossing.curves A (X k)
    · rcases k with _ | m
      · exact absurd hk h0
      · by_cases hm : c ∈ Arrangement.Crossing.curves A (X m)
        · rcases m with _ | r
          · exact absurd hm h0
          · -- double: `X (r+1)`, `X (r+2)` are `z₁, z₂`
            have hr : c ∉ Arrangement.Crossing.curves A (X r) := by
              intro hr
              have e1 := (hP r).1 hr
              have e2 := (hP (r + 1)).1 hm
              have e3 := (hP (r + 2)).1 hk
              have i1 := hXinj r (r + 1) (by omega) (by omega) (by omega)
              have i2 := hXinj r (r + 2) (by omega) (by omega) (by omega)
              have i3 := hXinj (r + 1) (r + 2) (by omega) (by omega) (by omega)
              rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rcases e3 with e3 | e3 <;>
                simp only [e1, e2, e3, ne_eq, not_true_eq_false] at i1 i2 i3
            have hpair : (X (r + 1) = z₁ ∧ X (r + 2) = z₂) ∨ (X (r + 1) = z₂ ∧ X (r + 2) = z₁) := by
              have e2 := (hP (r + 1)).1 hm
              have e3 := (hP (r + 2)).1 hk
              have i3 := hXinj (r + 1) (r + 2) (by omega) (by omega) (by omega)
              rcases e2 with e2 | e2 <;> rcases e3 with e3 | e3
              · rw [e2, e3] at i3; exact absurd rfl i3
              · exact Or.inl ⟨e2, e3⟩
              · exact Or.inr ⟨e2, e3⟩
              · rw [e2, e3] at i3; exact absurd rfl i3
            have n1 := R.next_walk d (r + 1) (X r) (haX r)
              (fun he => hXinj r (r + 1) (by omega) (by omega) (by omega) (congrArg pt he))
              (fun he => hXinj r (r + 2) (by omega) (by omega) (by omega) (congrArg pt he))
            have n2 := R.next_walk d (r + 1) (X (r + 3)) (haX (r + 3))
              (fun he => hXinj (r + 3) (r + 1) (by omega) (by omega) (by omega) (congrArg pt he))
              (fun he => hXinj (r + 3) (r + 2) (by omega) (by omega) (by omega) (congrArg pt he))
            have hprod := mul_pos_of_sgn (R.sgn_pm d) n1 n2
            have hpair' : (pt (X (r + 1)) = pt z₁ ∧ pt (X (r + 2)) = pt z₂) ∨
                (pt (X (r + 1)) = pt z₂ ∧ pt (X (r + 2)) = pt z₁) := by
              rcases hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩
              · exact Or.inl ⟨congrArg pt e1, congrArg pt e2⟩
              · exact Or.inr ⟨congrArg pt e1, congrArg pt e2⟩
            rw [← orient_pair_mul hpair'] at hprod
            have hb := bit_eq_of_mul_pos hprod
            have ih' : bit (o (pt (X r))) = bit (o (pt (X 0))) + ∑ i ∈ Ioc 0 r,
                (if c ∈ Arrangement.Crossing.curves A (X i) then (1 : ZMod 2) else 0) :=
              ih r (by omega) (by omega) hr
            change bit (o (pt (X (r + 3)))) = bit (o (pt (X 0))) + ∑ i ∈ Ioc 0 (r + 3),
              (if c ∈ Arrangement.Crossing.curves A (X i) then (1 : ZMod 2) else 0)
            rw [hb, ih', hsum (r + 2), hsum (r + 1), hsum r, if_pos hm, if_pos hk,
              if_neg (show c ∉ Arrangement.Crossing.curves A (X (r + 3)) from hcj)]
            exact zmod2_aux₂ _ _
        · -- single: `X (m+1)` is a crossing with `c`
          set z' := if X (m + 1) = z₁ then z₂ else z₁ with hz'
          have hpair : (X (m + 1) = z₁ ∧ z' = z₂) ∨ (X (m + 1) = z₂ ∧ z' = z₁) := by
            rcases (hP (m + 1)).1 hk with e | e
            · left; exact ⟨e, by rw [hz', if_pos e]⟩
            · right; refine ⟨e, ?_⟩
              rw [hz', if_neg (by rw [e]; exact hz.symm)]
          have hcz' : c ∈ Arrangement.Crossing.curves A z' := by
            rcases hpair with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> assumption
          have haz' : a ∈ Arrangement.Crossing.curves A z' := by
            rcases hpair with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> assumption
          have hz'ne : z' ≠ X (m + 1) := by
            rcases hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
            · exact hz.symm
            · exact hz
          have n1 := R.next_walk d m z' haz' (fun he => hm (cast (congrArg (fun w => c ∈ Arrangement.Crossing.curves A w) he) hcz')) hz'ne
          have n2 := R.next_walk d (m + 1) z' haz' hz'ne (fun he => hcj (cast (congrArg (fun w => c ∈ Arrangement.Crossing.curves A w) he) hcz'))
          have hprod := mul_pos_of_sgn (R.sgn_pm d) n1 n2
          -- `orient (X(m+1)) z' x = orient x (X(m+1)) z'`, `orient (X(m+1)) z' y = - ...`
          have e1 := orient_cyc (u a) (pt (X m)) (pt (X (m + 1))) (pt z')
          have e2 := orient_swap23 (u a) (pt (X (m + 1))) (pt (X (m + 2))) (pt z')
          have hneg : orient (u a) (pt (X (m + 1))) (pt z') (pt (X m)) *
              orient (u a) (pt (X (m + 1))) (pt z') (pt (X (m + 2))) < 0 := by
            rw [e1, e2]; nlinarith
          have hpair' : (pt (X (m + 1)) = pt z₁ ∧ pt z' = pt z₂) ∨
              (pt (X (m + 1)) = pt z₂ ∧ pt z' = pt z₁) := by
            rcases hpair with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · exact Or.inl ⟨congrArg pt e1, congrArg pt e2⟩
            · exact Or.inr ⟨congrArg pt e1, congrArg pt e2⟩
          rw [← orient_pair_mul hpair'] at hneg
          have hb := bit_eq_add_one_of_mul_neg hneg
          have ih' : bit (o (pt (X m))) = bit (o (pt (X 0))) + ∑ i ∈ Ioc 0 m,
              (if c ∈ Arrangement.Crossing.curves A (X i) then (1 : ZMod 2) else 0) :=
            ih m (by omega) (by omega) hm
          change bit (o (pt (X (m + 2)))) = bit (o (pt (X 0))) + ∑ i ∈ Ioc 0 (m + 2),
            (if c ∈ Arrangement.Crossing.curves A (X i) then (1 : ZMod 2) else 0)
          rw [hb, ih', hsum (m + 1), hsum m, if_pos hk,
            if_neg (show c ∉ Arrangement.Crossing.curves A (X (m + 2)) from hcj)]
          exact zmod2_aux₁ _ _
    · -- neither: `X k`, `X (k+1)` are not on `c`
      have n1 := R.next_walk d k z₁ haz₁ (fun he => hk (cast (congrArg (fun w => c ∈ Arrangement.Crossing.curves A w) he) hcz₁))
        (fun he => hcj (cast (congrArg (fun w => c ∈ Arrangement.Crossing.curves A w) he) hcz₁))
      have n2 := R.next_walk d k z₂ haz₂ (fun he => hk (cast (congrArg (fun w => c ∈ Arrangement.Crossing.curves A w) he) hcz₂))
        (fun he => hcj (cast (congrArg (fun w => c ∈ Arrangement.Crossing.curves A w) he) hcz₂))
      have hprod := mul_pos_of_sgn (R.sgn_pm d) n1 n2
      have hsep := orient_mul_pos_of_sep hua (hC k) (hC (k + 1)) hC₁ hC₂
        (hXinj k (k + 1) (by omega) hj (by omega)) hpz (hne_of hcz₁ hk).symm
        (hne_of hcz₂ hk).symm (hne_of hcz₁ hcj).symm (hne_of hcz₂ hcj).symm hprod
      have hb := bit_eq_of_mul_pos hsep
      have ih' : bit (o (pt (X k))) = bit (o (pt (X 0))) + ∑ i ∈ Ioc 0 k,
          (if c ∈ Arrangement.Crossing.curves A (X i) then (1 : ZMod 2) else 0) :=
        ih k (by omega) (by omega) hk
      change bit (o (pt (X (k + 1)))) = bit (o (pt (X 0))) + ∑ i ∈ Ioc 0 (k + 1),
        (if c ∈ Arrangement.Crossing.curves A (X i) then (1 : ZMod 2) else 0)
      rw [hb, ih', hsum k, if_neg (show c ∉ Arrangement.Crossing.curves A (X (k + 1)) from hcj)]
      exact zmod2_aux₀ _ _

/-- **Sides are geometric.** For distinct curves `a, b, c`, the two crossings `x ≠ y` of `a, b`
are on different sides of `c` iff their points are on different sides of the chord `z₁ z₂` of the
circle of `a` (the crossings of `a` and `c`). -/
theorem side_ne_iff {a b c : Fin n} (hac : a ≠ c) (hbc : b ≠ c)
    {s : A.Cell → ZMod 2} (hs : A.IsSide c s) {x y z₁ z₂ : A.Crossing}
    (hx : Arrangement.Crossing.curves A x = {a, b}) (hy : Arrangement.Crossing.curves A y = {a, b})
    (hz : z₁ ≠ z₂) (hz₁ : Arrangement.Crossing.curves A z₁ = {a, c})
    (hz₂ : Arrangement.Crossing.curves A z₂ = {a, c}) {d e : D} (hd : d ∈ x.darts)
    (he : e ∈ y.darts) :
    s (A.cellOf d) ≠ s (A.cellOf e) ↔
      orient (u a) (pt z₁) (pt z₂) (pt x) * orient (u a) (pt z₁) (pt z₂) (pt y) < 0 := by
  have hcx : c ∉ Arrangement.Crossing.curves A x := by
    rw [hx]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨hac.symm, hbc.symm⟩
  have hcy : c ∉ Arrangement.Crossing.curves A y := by
    rw [hy]; simp only [mem_insert, mem_singleton, not_or]; exact ⟨hac.symm, hbc.symm⟩
  obtain ⟨d', hd'x, hd'a⟩ := exists_dart_of_mem (show a ∈ Arrangement.Crossing.curves A x by
    rw [hx]; simp)
  obtain ⟨k, hk, hky⟩ := Great.exists_straight_pow_eq (d := d')
    (show A.curve d' ∈ Arrangement.Crossing.curves A y by rw [hd'a, hy]; simp)
  have e1 : s (A.cellOf d) = s (A.cellOf d') := by
    rw [← Great.crossSide_eq hs (by rw [crossingOf_of_mem_darts hd]; exact hcx),
      ← Great.crossSide_eq hs (by rw [hd'x]; exact hcx), crossingOf_of_mem_darts hd, hd'x]
  have e2 : s (A.cellOf e) = s (A.cellOf ((A.straight ^ k) d')) := by
    rw [← Great.crossSide_eq hs (by rw [crossingOf_of_mem_darts he]; exact hcy),
      ← Great.crossSide_eq hs (by rw [hky]; exact hcy), crossingOf_of_mem_darts he, hky]
  have e3 := Great.side_straight_pow hs (show A.curve d' ≠ c by rw [hd'a]; exact hac) k
  have hw := R.walk_bit d' (c := c) (by rw [hd'a]; exact hac) hz (by rw [hd'a]; exact hz₁)
    (by rw [hd'a]; exact hz₂) (by rw [hd'x]; exact hcx) k hk (by rw [hky]; exact hcy)
  rw [← Finset.sum_boole] at e3
  rw [e1, e2, e3]
  rw [hky, hd'x, hd'a] at hw
  have hua := R.u_ne_zero a
  have hax : a ∈ Arrangement.Crossing.curves A x := by rw [hx]; simp
  have hay : a ∈ Arrangement.Crossing.curves A y := by rw [hy]; simp
  have haz₁ : a ∈ Arrangement.Crossing.curves A z₁ := by rw [hz₁]; simp
  have haz₂ : a ∈ Arrangement.Crossing.curves A z₂ := by rw [hz₂]; simp
  have hcz₁ : c ∈ Arrangement.Crossing.curves A z₁ := by rw [hz₁]; simp
  have hcz₂ : c ∈ Arrangement.Crossing.curves A z₂ := by rw [hz₂]; simp
  have hne_of : ∀ {p q : A.Crossing}, c ∈ Arrangement.Crossing.curves A p →
      c ∉ Arrangement.Crossing.curves A q → pt p ≠ pt q := fun hp hq he => by
    rw [R.inj he] at hp; exact hq hp
  have ox := (R.onCirc haz₁).orient_ne_zero hua (R.onCirc haz₂) (R.onCirc hax)
    (fun he => hz (R.inj he)) (hne_of hcz₁ hcx) (hne_of hcz₂ hcx)
  have oy := (R.onCirc haz₁).orient_ne_zero hua (R.onCirc haz₂) (R.onCirc hay)
    (fun he => hz (R.inj he)) (hne_of hcz₁ hcy) (hne_of hcz₂ hcy)
  rw [mul_neg_iff_bit_ne ox oy, hw]
  generalize s (A.cellOf d') = p
  generalize bit (orient (u a) (pt z₁) (pt z₂) (pt x)) = q
  generalize (∑ i ∈ Ioc 0 k, if c ∈ Arrangement.Crossing.curves A
    (A.crossingOf ((A.straight ^ i) d')) then (1 : ZMod 2) else 0) = r
  revert p q r; decide

end IsCircleRep

end Pca.Circ
