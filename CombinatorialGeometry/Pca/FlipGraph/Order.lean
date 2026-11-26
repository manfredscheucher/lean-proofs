/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): the order of the curves after processing the first curve

FROS, proof of Theorem 4: after the first pseudoparabola `C_1` has been swept downwards, the other
pseudoparabolas are labelled `C_2, …, C_n` from top to bottom on the left. Graph language
(`doc/pca/flipgraph.md`, F-D4): the first curve `C₀` has no crossing of two other curves in its
interior and a side on the marked cell; walking along `C₀` from the marked cell, the crossings
with a curve `a` are at two positions `p a < q a`, and the cells between them lie inside `a`.
These intervals are nested (`order_of_first`), and the nesting order labels the curves.

Pure parity along walks, no region argument:

* `chord_ends`: inside `C₀` every other curve is a single segment joining its two crossings with
  `C₀` (a crossing on it would be a crossing inside `C₀`). Hence the two crossings of `C₀` and `a`
  are on the same side of every third curve `b` (`same_side`): the intervals do not interleave.
* `meet`: two intervals are not disjoint, since otherwise the cells inside `C₀`, `a` and `b` would
  form a set without boundary (`cell_const`), but the marked cell is outside it and the cell of
  the cylindrical arrangement inside it.
-/
import Pca.FlipGraph.Canon

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace Order

/-- A property of cells that does not change across any segment is constant. -/
theorem cell_const (M : Marked n D) {W : M.A.Cell → Prop}
    (hW : ∀ y, W (M.A.cellOf (M.A.α y)) ↔ W (M.A.cellOf y)) (d e : D) :
    W (M.A.cellOf d) ↔ W (M.A.cellOf e) := by
  induction M.A.connected d e with
  | rel a b h =>
    rcases h with rfl | rfl
    · rw [M.A.cellOf_σ]; exact (hW a).symm
    · exact (hW a).symm
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- A strict total order on `Fin n` is the order of a relabelling. -/
theorem exists_equiv_of_order {r : Fin n → Fin n → Prop} (irr : ∀ a, ¬ r a a)
    (tr : ∀ a b c, r a b → r b c → r a c) (tot : ∀ a b, a ≠ b → r a b ∨ r b a) :
    ∃ e : Fin n ≃ Fin n, ∀ a b, r a b ↔ e a < e b := by
  classical
  let R : Fin n → ℕ := fun a => (univ.filter (fun b => r b a)).card
  have hR : ∀ a, R a < n := fun a => by
    have h1 : univ.filter (fun b => r b a) ⊆ univ.erase a := fun b hb => by
      rw [mem_filter] at hb
      exact mem_erase.2 ⟨fun h => irr a (h ▸ hb.2), mem_univ _⟩
    have h2 := card_le_card h1
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at h2
    have : 0 < n := Fin.pos a
    simp only [R]; omega
  have mono : ∀ a b, r a b → R a < R b := fun a b h => by
    apply card_lt_card
    refine ⟨fun c hc => ?_, fun hs => ?_⟩
    · rw [mem_filter] at hc ⊢; exact ⟨mem_univ _, tr _ _ _ hc.2 h⟩
    · have := hs (mem_filter.2 ⟨mem_univ a, h⟩)
      exact irr a (mem_filter.1 this).2
  have inj : Function.Injective (fun a => (⟨R a, hR a⟩ : Fin n)) := fun a b h => by
    by_contra hne
    have h' : R a = R b := congrArg Fin.val h
    rcases tot a b hne with h1 | h1
    · exact absurd h' (mono _ _ h1).ne
    · exact absurd h'.symm (mono _ _ h1).ne
  refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.1 inj), fun a b => ?_⟩
  change r a b ↔ R a < R b
  refine ⟨mono a b, fun h => ?_⟩
  by_contra hn
  rcases eq_or_ne a b with rfl | hne
  · exact lt_irrefl _ h
  · rcases tot a b hne with h1 | h1
    · exact hn h1
    · exact absurd h (not_lt.2 (mono _ _ h1).le)

theorem arith_step {p q i : ℕ} (hpq : p < q) :
    (p < i + 1 ∧ i + 1 ≤ q) ↔ ((p < i ∧ i ≤ q) ↔ ¬ (i = p ∨ i = q)) := by
  omega

section Walk

variable (M : Marked n D) {C₀ : Fin n} {y₀ : D} (hy₀ : M.A.curve y₀ = C₀)
  (hz : M.A.cellOf y₀ = M.z)

/-- Walking along `C₀`, the interior status changes exactly at the crossings. -/
theorem in_succ (a : Fin n) (i : ℕ) :
    M.Inside a (M.A.cellOf ((M.A.straight ^ (i + 1)) y₀)) ↔
      (M.Inside a (M.A.cellOf ((M.A.straight ^ i) y₀)) ↔
        M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y₀))) ≠ a) := by
  rw [Walk.pow_succ_apply]; exact M.inside_straight a _

include hy₀ in
theorem curve_w (i : ℕ) : M.A.curve ((M.A.straight ^ i) y₀) = C₀ := by
  rw [Walk.curve_pow, hy₀]

include hy₀ in
theorem nx_ne (i : ℕ) : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y₀))) ≠ C₀ := by
  intro h
  apply M.A.isArrangement.curve_σ (M.A.α ((M.A.straight ^ i) y₀))
  rw [h, M.A.curve_α, curve_w M hy₀]

include hy₀ hz in
/-- The cells to the right of the walk along `C₀` are outside `C₀`. -/
theorem not_in_C₀ (i : ℕ) : ¬ M.Inside C₀ (M.A.cellOf ((M.A.straight ^ i) y₀)) := by
  induction i with
  | zero => simp only [pow_zero, Perm.one_apply, hz]; exact M.not_inside_z C₀
  | succ i ih =>
    rw [in_succ]
    have := nx_ne M hy₀ i
    tauto

include hy₀ hz in
/-- The cells to the left of the walk along `C₀` are inside `C₀`. -/
theorem in_C₀_α (i : ℕ) : M.Inside C₀ (M.A.cellOf (M.A.α ((M.A.straight ^ i) y₀))) := by
  rw [M.inside_α, curve_w M hy₀]
  have := not_in_C₀ M hy₀ hz i
  tauto

include hy₀ in
/-- The two crossings of the walk along `C₀` with `a`. -/
theorem flips (a : Fin n) : ∃ p q : ℕ, a ≠ C₀ →
    p < q ∧ Walk.flipsOn M.A a y₀ = {p, q} := by
  by_cases ha : a = C₀
  · exact ⟨0, 0, fun h => absurd ha h⟩
  · have h2 := Walk.card_flipsOn M.A (C := a) (d := y₀) (by rw [hy₀]; exact Ne.symm ha)
    obtain ⟨x, y, hxy, hs⟩ := card_eq_two.1 h2
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, y, fun _ => ⟨h, hs⟩⟩
    · exact ⟨y, x, fun _ => ⟨h, by rw [hs, pair_comm]⟩⟩

theorem nx_iff {a : Fin n} {p q : ℕ} (hs : Walk.flipsOn M.A a y₀ = {p, q}) {i : ℕ}
    (hi : i < period M.A.straight y₀) :
    M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y₀))) = a ↔ i = p ∨ i = q := by
  have := (Walk.mem_flipsOn M.A (C := a) (d := y₀) (i := i))
  rw [hs, mem_insert, mem_singleton] at this
  constructor
  · intro h; exact this.2 ⟨hi, h⟩
  · intro h; exact (this.1 h).2

theorem lt_period {a : Fin n} {p q : ℕ} (hs : Walk.flipsOn M.A a y₀ = {p, q}) :
    p < period M.A.straight y₀ ∧ q < period M.A.straight y₀ := by
  have hp := (Walk.mem_flipsOn M.A (C := a) (d := y₀) (i := p)).1 (by rw [hs]; simp)
  have hq := (Walk.mem_flipsOn M.A (C := a) (d := y₀) (i := q)).1 (by rw [hs]; simp)
  exact ⟨hp.1, hq.1⟩

include hz in
/-- The cells inside `a` along the walk form the interval `(p, q]`. -/
theorem interval {a : Fin n} {p q : ℕ} (hpq : p < q) (hs : Walk.flipsOn M.A a y₀ = {p, q})
    (i : ℕ) (hi : i ≤ period M.A.straight y₀) :
    M.Inside a (M.A.cellOf ((M.A.straight ^ i) y₀)) ↔ p < i ∧ i ≤ q := by
  induction i with
  | zero =>
    simp only [pow_zero, Perm.one_apply, hz]
    exact ⟨fun h => absurd h (M.not_inside_z a), fun h => by omega⟩
  | succ i ih =>
    rw [in_succ, ih (by omega), ne_eq, nx_iff M hs (by omega)]
    exact (arith_step hpq).symm

/-- Every dart of the walk is the straight successor of a dart of the walk within one period. -/
theorem exists_pred (k : ℕ) : ∃ j < period M.A.straight y₀,
    (M.A.straight ^ k) y₀ = M.A.straight ((M.A.straight ^ j) y₀) := by
  have hP := period_pos M.A.straight y₀
  refine ⟨(k + period M.A.straight y₀ - 1) % period M.A.straight y₀, Nat.mod_lt _ hP, ?_⟩
  have hmod : ∀ m, (M.A.straight ^ (m % period M.A.straight y₀)) y₀ = (M.A.straight ^ m) y₀ :=
    fun m => by
      rw [Perm.coe_pow, Perm.coe_pow, period_eq_minimalPeriod]
      exact Function.iterate_mod_minimalPeriod_eq
  rw [hmod, ← Walk.pow_succ_apply, show k + period M.A.straight y₀ - 1 + 1 =
    k + period M.A.straight y₀ by omega, pow_add, Perm.mul_apply, Walk.pow_period_apply]

include hy₀ in
/-- Every dart of `C₀` is a dart of the walk or the reverse of one. -/
theorem dart_C₀ {y : D} (hy : M.A.curve y = C₀) : ∃ j < period M.A.straight y₀,
    y = (M.A.straight ^ j) y₀ ∨ y = M.A.α ((M.A.straight ^ j) y₀) := by
  rcases M.A.isArrangement.straight y₀ y (hy₀.trans hy.symm) with h | h
  · obtain ⟨k, hk, hk'⟩ := Walk.exists_idx M.A h
    exact ⟨k, hk, Or.inl hk'.symm⟩
  · obtain ⟨k, -, hk'⟩ := Walk.exists_idx M.A h
    obtain ⟨j, hj, hj'⟩ := exists_pred M k
    refine ⟨j, hj, Or.inr ?_⟩
    have e1 : y = M.A.σ (M.A.σ ((M.A.straight ^ k) y₀)) := by rw [hk', M.A.σ_σ_σ_σ]
    rw [e1, hj', M.A.straight_apply, M.A.σ_σ_σ_σ]

include hy₀ in
/-- Every crossing on `C₀` is at the end of a dart of the walk. -/
theorem crossing_C₀ {X : M.A.Crossing} (hX : C₀ ∈ Arrangement.Crossing.curves M.A X) :
    ∃ j < period M.A.straight y₀, X = M.A.crossingOf (M.A.α ((M.A.straight ^ j) y₀)) := by
  obtain ⟨d, rfl⟩ := X.exists_mk
  change C₀ ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf d) at hX
  rw [M.A.curves_crossingOf, mem_insert, mem_singleton] at hX
  obtain ⟨e, he, hec⟩ : ∃ e, M.A.curve e = C₀ ∧ M.A.crossingOf e = M.A.crossingOf d := by
    rcases hX with h | h
    · exact ⟨d, h.symm, rfl⟩
    · exact ⟨M.A.σ d, h.symm, M.A.crossingOf_σ d⟩
  obtain ⟨j, hj, h | h⟩ := dart_C₀ M hy₀ he
  · obtain ⟨j', hj', e'⟩ := exists_pred M j
    refine ⟨j', hj', ?_⟩
    change M.A.crossingOf d = _
    rw [← hec, h, e', M.A.straight_apply, M.A.crossingOf_σσ]
  · refine ⟨j, hj, ?_⟩
    change M.A.crossingOf d = _
    rw [← hec, h]

include hy₀ in
theorem curves_x (i : ℕ) : Arrangement.Crossing.curves M.A
    (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y₀))) =
      {C₀, M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y₀)))} := by
  rw [M.A.curves_crossingOf, M.A.curve_α, curve_w M hy₀]

include hy₀ in
/-- The interior status of `b` at the crossing at position `i`. -/
theorem cross_x {b : Fin n} (hb : b ≠ C₀) {i : ℕ}
    (hi : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y₀))) ≠ b) :
    M.CrossInside b (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y₀))) ↔
      M.Inside b (M.A.cellOf ((M.A.straight ^ i) y₀)) := by
  have hx : b ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α ((M.A.straight ^ i) y₀))) := by
    rw [curves_x M hy₀, mem_insert, mem_singleton]
    rintro (h | h)
    · exact hb h
    · exact hi h.symm
  rw [M.crossInside_iff hx, M.inside_α, curve_w M hy₀]
  have : C₀ ≠ b := Ne.symm hb
  simp only [ne_eq, this, not_false_eq_true, iff_true]

variable (hclear : ∀ x : M.A.Crossing, C₀ ∉ Arrangement.Crossing.curves M.A x →
  ¬ M.CrossInside C₀ x)

include hclear in
/-- Inside `C₀` every segment of another curve joins two crossings with `C₀`. -/
theorem chord_ends {y : D} (hy : M.A.curve y ≠ C₀) (hin : M.Inside C₀ (M.A.cellOf y)) :
    C₀ ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf y) ∧
      C₀ ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α y)) := by
  constructor
  · by_contra h
    exact hclear _ h ((M.crossInside_iff h).2 hin)
  · by_contra h
    refine hclear _ h ((M.crossInside_iff h).2 ?_)
    rw [M.inside_α]
    simp only [hy, ne_eq, not_false_eq_true, iff_true]
    exact hin

include hy₀ in
/-- A crossing of `C₀` and `a` is at one of the two positions of `a`. -/
theorem pos_of_cross {a : Fin n} (ha : a ≠ C₀) {p q : ℕ} (hs : Walk.flipsOn M.A a y₀ = {p, q})
    {X : M.A.Crossing} (hX0 : C₀ ∈ Arrangement.Crossing.curves M.A X)
    (hXa : a ∈ Arrangement.Crossing.curves M.A X) :
    ∃ j, (j = p ∨ j = q) ∧ X = M.A.crossingOf (M.A.α ((M.A.straight ^ j) y₀)) := by
  obtain ⟨j, hj, rfl⟩ := crossing_C₀ M hy₀ hX0
  refine ⟨j, (nx_iff M hs hj).1 ?_, rfl⟩
  rw [curves_x M hy₀, mem_insert, mem_singleton] at hXa
  rcases hXa with h | h
  · exact absurd h ha
  · exact h.symm

include hy₀ hz hclear in
/-- **The two crossings of `C₀` and `a` are on the same side of every third curve `b`.** -/
theorem same_side {a b : Fin n} (ha : a ≠ C₀) (hb : b ≠ C₀) (hab : a ≠ b) {p q : ℕ}
    (hs : Walk.flipsOn M.A a y₀ = {p, q}) (hpq : p < q) :
    M.Inside b (M.A.cellOf ((M.A.straight ^ p) y₀)) ↔
      M.Inside b (M.A.cellOf ((M.A.straight ^ q) y₀)) := by
  have hP := lt_period M hs
  have hnp : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ p) y₀))) = a :=
    (nx_iff M hs hP.1).2 (Or.inl rfl)
  have hnq : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ q) y₀))) = a :=
    (nx_iff M hs hP.2).2 (Or.inr rfl)
  set w := (M.A.straight ^ p) y₀ with hw
  set u := M.A.σ (M.A.σ (M.A.σ (M.A.α w))) with hu
  have hcu : M.A.curve u = a := by rw [hu, M.A.curve_σσσ, hnp]
  have hxu : M.A.crossingOf u = M.A.crossingOf (M.A.α w) := M.A.crossingOf_σσσ _
  have hin : M.Inside C₀ (M.A.cellOf u) := by
    have e : M.A.cellOf u = M.A.cellOf (M.A.α ((M.A.straight ^ (p + 1)) y₀)) := by
      rw [hu, M.A.cellOf_σ, Walk.pow_succ_apply, M.A.straight_apply]
    rw [e]; exact in_C₀_α M hy₀ hz _
  obtain ⟨-, hend⟩ := chord_ends M hclear (hcu ▸ ha) hin
  obtain ⟨j, hj, hjx⟩ := pos_of_cross M hy₀ ha hs hend (hcu ▸ M.A.mem_curves_end u)
  have hjq : j = q := by
    rcases hj with rfl | rfl
    · exact absurd (hjx.trans hxu.symm) (M.A.crossingOf_α_ne u)
    · rfl
  subst hjq
  have hbu : b ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf u) := by
    rw [hxu, curves_x M hy₀, hnp, mem_insert, mem_singleton]
    rintro (h | h)
    · exact hb h
    · exact hab h.symm
  have hbu' : b ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf (M.A.α u)) := by
    rw [hjx, curves_x M hy₀, hnq, mem_insert, mem_singleton]
    rintro (h | h)
    · exact hb h
    · exact hab h.symm
  have h1 := M.crossInside_iff hbu
  have h2 := M.crossInside_iff hbu'
  rw [M.inside_α, hcu] at h2
  simp only [ne_eq, hab, not_false_eq_true, iff_true] at h2
  rw [← cross_x M hy₀ hb (by rw [hnp]; exact hab), ← cross_x M hy₀ hb (by rw [hnq]; exact hab), ← hxu, ← hjx,
    h1, h2]

include hy₀ hz hclear in
/-- An `a`-dart inside `C₀` is outside `b` if the intervals of `a` and `b` are disjoint. -/
theorem cap_out {a b : Fin n} (ha : a ≠ C₀) (hb : b ≠ C₀) (hab : a ≠ b) {p q : ℕ}
    (hs : Walk.flipsOn M.A a y₀ = {p, q}) (hpq : p < q)
    (hdisj : ∀ i < period M.A.straight y₀, ¬ (M.Inside a (M.A.cellOf ((M.A.straight ^ i) y₀)) ∧
      M.Inside b (M.A.cellOf ((M.A.straight ^ i) y₀))))
    {y : D} (hy : M.A.curve y = a) (hin : M.Inside C₀ (M.A.cellOf y)) :
    ¬ M.Inside b (M.A.cellOf y) := by
  have hP := lt_period M hs
  obtain ⟨hst, -⟩ := chord_ends M hclear (hy ▸ ha) hin
  obtain ⟨j, hj, hjx⟩ := pos_of_cross M hy₀ ha hs hst (hy ▸ M.A.mem_curves_crossingOf y)
  have hnj : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ j) y₀))) = a := by
    rcases hj with rfl | rfl
    · exact (nx_iff M hs hP.1).2 (Or.inl rfl)
    · exact (nx_iff M hs hP.2).2 (Or.inr rfl)
  have hby : b ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) := by
    rw [hjx, curves_x M hy₀, hnj, mem_insert, mem_singleton]
    rintro (h | h)
    · exact hb h
    · exact hab h.symm
  rw [← M.crossInside_iff hby, hjx, cross_x M hy₀ hb (by rw [hnj]; exact hab)]
  have hq := hdisj q hP.2
  have hqa := (interval M hz hpq hs q hP.2.le).2 ⟨hpq, le_rfl⟩
  have hqb : ¬ M.Inside b (M.A.cellOf ((M.A.straight ^ q) y₀)) := fun h => hq ⟨hqa, h⟩
  rcases hj with rfl | rfl
  · rw [same_side M hy₀ hz hclear ha hb hab hs hpq]; exact hqb
  · exact hqb

include hy₀ hz hclear in
/-- **The intervals of two curves meet** (cylindricity). -/
theorem meet (hc : M.Cylindrical) {a b : Fin n} (ha : a ≠ C₀) (hb : b ≠ C₀) (hab : a ≠ b)
    {p q p' q' : ℕ} (hs : Walk.flipsOn M.A a y₀ = {p, q}) (hpq : p < q)
    (hs' : Walk.flipsOn M.A b y₀ = {p', q'}) (hpq' : p' < q') :
    ∃ i < period M.A.straight y₀, M.Inside a (M.A.cellOf ((M.A.straight ^ i) y₀)) ∧
      M.Inside b (M.A.cellOf ((M.A.straight ^ i) y₀)) := by
  by_contra hdisj
  push_neg at hdisj
  have hdisj1 : ∀ i < period M.A.straight y₀,
      ¬ (M.Inside a (M.A.cellOf ((M.A.straight ^ i) y₀)) ∧
        M.Inside b (M.A.cellOf ((M.A.straight ^ i) y₀))) :=
    fun i hi h => hdisj i hi h.1 h.2
  have hdisj2 : ∀ i < period M.A.straight y₀,
      ¬ (M.Inside b (M.A.cellOf ((M.A.straight ^ i) y₀)) ∧
        M.Inside a (M.A.cellOf ((M.A.straight ^ i) y₀))) :=
    fun i hi h => hdisj i hi h.2 h.1
  let W : M.A.Cell → Prop := fun f => M.Inside C₀ f ∧ M.Inside a f ∧ M.Inside b f
  -- an `a`-dart (or `b`-dart): both cells are outside `W`
  have side_ab : ∀ y, (M.A.curve y = a ∨ M.A.curve y = b) →
      ¬ W (M.A.cellOf y) := by
    rintro y (hy | hy) ⟨h0, h1, h2⟩
    · exact cap_out M hy₀ hz hclear ha hb hab hs hpq hdisj1 hy h0 h2
    · exact cap_out M hy₀ hz hclear hb ha (Ne.symm hab) hs' hpq' hdisj2 hy h0 h1
  have hW : ∀ y, W (M.A.cellOf (M.A.α y)) ↔ W (M.A.cellOf y) := by
    intro y
    by_cases hy0 : M.A.curve y = C₀
    · obtain ⟨j, hj, rfl | rfl⟩ := dart_C₀ M hy₀ hy0
      · have h1 : ¬ W (M.A.cellOf ((M.A.straight ^ j) y₀)) := fun h => not_in_C₀ M hy₀ hz j h.1
        have h2 : ¬ W (M.A.cellOf (M.A.α ((M.A.straight ^ j) y₀))) := by
          rintro ⟨-, h1', h2'⟩
          rw [M.inside_α, curve_w M hy₀] at h1' h2'
          simp only [ne_eq, Ne.symm ha, Ne.symm hb, not_false_eq_true, iff_true] at h1' h2'
          exact hdisj1 j hj ⟨h1', h2'⟩
        exact ⟨fun h => absurd h h2, fun h => absurd h h1⟩
      · have h1 : ¬ W (M.A.cellOf ((M.A.straight ^ j) y₀)) := fun h => not_in_C₀ M hy₀ hz j h.1
        have h2 : ¬ W (M.A.cellOf (M.A.α ((M.A.straight ^ j) y₀))) := by
          rintro ⟨-, h1', h2'⟩
          rw [M.inside_α, curve_w M hy₀] at h1' h2'
          simp only [ne_eq, Ne.symm ha, Ne.symm hb, not_false_eq_true, iff_true] at h1' h2'
          exact hdisj1 j hj ⟨h1', h2'⟩
        rw [M.A.α_α]
        exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    · by_cases hyab : M.A.curve y = a ∨ M.A.curve y = b
      · have h1 := side_ab y hyab
        have h2 := side_ab (M.A.α y) (by rw [M.A.curve_α]; exact hyab)
        exact ⟨fun h => absurd h h2, fun h => absurd h h1⟩
      · push_neg at hyab
        simp only [W]
        rw [M.inside_α C₀, M.inside_α a, M.inside_α b]
        simp only [ne_eq, hy0, hyab.1, hyab.2, not_false_eq_true, iff_true]
  obtain ⟨f, hf⟩ := hc
  obtain ⟨d, rfl⟩ := f.exists_mk
  have := (cell_const M hW y₀ d).2 ⟨hf C₀, hf a, hf b⟩
  rw [hz] at this
  exact M.not_inside_z C₀ this.1

end Walk

end Order

open Order in
/-- **The order of the curves** after processing the first curve `C₀`: the arcs of `C₀` inside
the other curves are nested; labelling by this order gives the invariant for `k = 1`. -/
theorem order_of_first (M : Marked n D) (hc : M.Cylindrical) (C₀ : Fin n)
    (hclear : ∀ x : M.A.Crossing, C₀ ∉ Arrangement.Crossing.curves M.A x → ¬ M.CrossInside C₀ x)
    (hz : ∃ y, M.A.curve y = C₀ ∧ M.A.cellOf y = M.z) :
    ∃ c : Fin n ≃ Fin n, M.CanonUpTo c 1 ∧ M.MarkOnFirst c := by
  classical
  obtain ⟨y₀, hy₀, hz₀⟩ := hz
  choose p q hpq using flips M hy₀
  have hP := fun a (ha : a ≠ C₀) => lt_period M (hpq a ha).2
  -- positions as functions
  have IN : ∀ a, a ≠ C₀ → ∀ i ≤ period M.A.straight y₀,
      (M.Inside a (M.A.cellOf ((M.A.straight ^ i) y₀)) ↔ p a < i ∧ i ≤ q a) :=
    fun a ha i hi => interval M hz₀ (hpq a ha).1 (hpq a ha).2 i hi
  -- the four positions of two curves are distinct
  have dist : ∀ a b, a ≠ C₀ → b ≠ C₀ → a ≠ b →
      p a ≠ p b ∧ p a ≠ q b ∧ q a ≠ p b ∧ q a ≠ q b := by
    intro a b ha hb hab
    have ea : ∀ i, (i = p a ∨ i = q a) → M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y₀))) = a :=
      fun i hi => (nx_iff M (hpq a ha).2 (by rcases hi with rfl | rfl <;> simp [hP a ha])).2 hi
    have eb : ∀ i, (i = p b ∨ i = q b) → M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y₀))) = b :=
      fun i hi => (nx_iff M (hpq b hb).2 (by rcases hi with rfl | rfl <;> simp [hP b hb])).2 hi
    refine ⟨fun h => hab ?_, fun h => hab ?_, fun h => hab ?_, fun h => hab ?_⟩
    · rw [← ea _ (Or.inl rfl), h, eb _ (Or.inl rfl)]
    · rw [← ea _ (Or.inl rfl), h, eb _ (Or.inr rfl)]
    · rw [← ea _ (Or.inr rfl), h, eb _ (Or.inl rfl)]
    · rw [← ea _ (Or.inr rfl), h, eb _ (Or.inr rfl)]
  -- same side, in positions: `(p b < p a ≤ q b) ↔ (p b < q a ≤ q b)`
  have SS : ∀ a b, a ≠ C₀ → b ≠ C₀ → a ≠ b →
      ((p b < p a ∧ p a ≤ q b) ↔ (p b < q a ∧ q a ≤ q b)) := by
    intro a b ha hb hab
    rw [← IN b hb _ (hP a ha).1.le, ← IN b hb _ (hP a ha).2.le]
    exact same_side M hy₀ hz₀ hclear ha hb hab (hpq a ha).2 (hpq a ha).1
  have MT : ∀ a b, a ≠ C₀ → b ≠ C₀ → a ≠ b →
      ∃ i, (p a < i ∧ i ≤ q a) ∧ (p b < i ∧ i ≤ q b) := by
    intro a b ha hb hab
    obtain ⟨i, hi, h1, h2⟩ := meet M hy₀ hz₀ hclear hc ha hb hab (hpq a ha).2 (hpq a ha).1
      (hpq b hb).2 (hpq b hb).1
    exact ⟨i, (IN a ha i hi.le).1 h1, (IN b hb i hi.le).1 h2⟩
  -- `Cov a b`: the interval of `b` lies inside the one of `a`
  let r : Fin n → Fin n → Prop := fun a b =>
    (a = C₀ ∧ b ≠ C₀) ∨ (a ≠ C₀ ∧ b ≠ C₀ ∧ a ≠ b ∧ p a < p b ∧ p b < q a)
  have nest : ∀ a b, a ≠ C₀ → b ≠ C₀ → a ≠ b → p a < p b → p b < q a → q b < q a := by
    intro a b ha hb hab h1 h2
    have := SS b a hb ha (Ne.symm hab)
    have := dist a b ha hb hab
    have := (hpq b hb).1
    omega
  obtain ⟨e, he⟩ := exists_equiv_of_order (r := r)
    (fun a h => by rcases h with ⟨h1, h2⟩ | ⟨-, -, h, -⟩ <;> tauto)
    (fun a b c hab hbc => by
      rcases hab with ⟨rfl, hb⟩ | ⟨ha, hb, hab', h1, h2⟩
      · rcases hbc with ⟨h, -⟩ | ⟨-, hc', -⟩
        · exact absurd h hb
        · exact Or.inl ⟨rfl, hc'⟩
      · rcases hbc with ⟨h, -⟩ | ⟨-, hc', hbc', h3, h4⟩
        · exact absurd h hb
        · have hac : a ≠ c := by
            rintro rfl
            have := (hpq a ha).1; have := nest a b ha hb hab' h1 h2; omega
          have := nest a b ha hb hab' h1 h2
          exact Or.inr ⟨ha, hc', hac, by omega, by omega⟩)
    (fun a b hab => by
      by_cases ha : a = C₀
      · exact Or.inl (Or.inl ⟨ha, fun h => hab (ha.trans h.symm)⟩)
      by_cases hb : b = C₀
      · exact Or.inr (Or.inl ⟨hb, ha⟩)
      obtain ⟨i, hi1, hi2⟩ := MT a b ha hb hab
      have s1 := SS a b ha hb hab
      have s2 := SS b a hb ha (Ne.symm hab)
      have := dist a b ha hb hab
      have := (hpq a ha).1
      have := (hpq b hb).1
      by_cases h : p a < p b
      · left; right; exact ⟨ha, hb, hab, h, by omega⟩
      · right; right; exact ⟨hb, ha, Ne.symm hab, by omega, by omega⟩)
  have e0 : e C₀ = ⟨0, Fin.pos (e C₀)⟩ := by
    by_contra hne
    obtain ⟨b, hb⟩ := e.surjective ⟨0, Fin.pos (e C₀)⟩
    have hpos : e b < e C₀ := by
      rw [hb, Fin.lt_def]
      have : (e C₀).val ≠ 0 := fun h => hne (Fin.ext h)
      show 0 < (e C₀).val
      omega
    rcases (he b C₀).2 hpos with ⟨-, h⟩ | ⟨-, h, -⟩
    · exact h rfl
    · exact h rfl
  refine ⟨e.symm, ?_, ⟨y₀, hz₀, by rw [Equiv.symm_symm, hy₀, e0]⟩⟩
  intro i j l hij hil hjl hk x hx
  have ec : ∀ t : Fin n, e.symm t = C₀ ↔ t.val = 0 := fun t => by
    constructor
    · intro h; rw [← h, Equiv.apply_symm_apply] at e0; rw [e0]
    · intro h; rw [Equiv.symm_apply_eq, e0]; exact Fin.ext h
  rcases hk with hk | hk
  · -- `c i = C₀`: no crossing of two other curves inside `C₀`
    have hi0 : e.symm i = C₀ := (ec i).2 (by omega)
    have hj0 : e.symm j ≠ C₀ := fun h => hij (Fin.ext (by rw [(ec j).1 h]; omega))
    have hl0 : e.symm l ≠ C₀ := fun h => hil (Fin.ext (by rw [(ec l).1 h]; omega))
    rw [hi0]
    have hxC : C₀ ∉ Arrangement.Crossing.curves M.A x := by
      rw [hx, mem_insert, mem_singleton]
      rintro (h | h)
      · exact hj0 h.symm
      · exact hl0 h.symm
    simp only [hclear x hxC, false_iff, not_and]
    intro h; exact absurd h (by rw [Fin.lt_def]; omega)
  · -- `c j = C₀`: the crossings of `C₀` and `c l` lie inside `c i` iff `i < l`
    have hj0 : e.symm j = C₀ := (ec j).2 (by omega)
    have hi0 : e.symm i ≠ C₀ := fun h => hij (Fin.ext (by rw [(ec i).1 h]; omega))
    have hl0 : e.symm l ≠ C₀ := fun h => (ne_of_gt hjl) (Fin.ext (by rw [(ec l).1 h]; omega))
    set a := e.symm i with ha
    set b := e.symm l with hb
    have hab : a ≠ b := fun h => hil (e.symm.injective h)
    have hxa : C₀ ∈ Arrangement.Crossing.curves M.A x := by rw [hx, hj0]; simp
    have hxb : b ∈ Arrangement.Crossing.curves M.A x := by rw [hx]; simp
    obtain ⟨t, ht, rfl⟩ := pos_of_cross M hy₀ hl0 (hpq b hl0).2 hxa hxb
    have hnt : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ t) y₀))) = b :=
      (nx_iff M (hpq b hl0).2 (by rcases ht with rfl | rfl <;> simp [hP b hl0])).2 ht
    rw [cross_x M hy₀ hi0 (hnt ▸ Ne.symm hab),
      IN a hi0 t (by rcases ht with rfl | rfl <;> simp [(hP b hl0).1.le, (hP b hl0).2.le])]
    have hri : j < i := by rw [Fin.lt_def]; omega
    have key : r a b ↔ i < l := by
      rw [he, ha, hb, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    simp only [hri, true_and, ← key, r]
    have s1 := SS b a hl0 hi0 (Ne.symm hab)
    have s2 := SS a b hi0 hl0 hab
    have := dist a b hi0 hl0 hab
    have := (hpq a hi0).1
    have := (hpq b hl0).1
    obtain ⟨m, hm1, hm2⟩ := MT a b hi0 hl0 hab
    constructor
    · intro h; right; refine ⟨hi0, hl0, hab, ?_, ?_⟩ <;> rcases ht with rfl | rfl <;> omega
    · rintro (⟨h, -⟩ | ⟨-, -, -, h1, h2⟩)
      · exact absurd h hi0
      · rcases ht with rfl | rfl <;> omega

end Pca.FlipGraph
