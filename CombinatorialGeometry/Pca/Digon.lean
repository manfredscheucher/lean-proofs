/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Milestone 3: the digon lemma (`lem:digon-corners` of the notes)

Local facts used here and in `Pca/Fan.lean` (no hypothesis on `n` unless stated):

* `Arrangement.two_mul_le_period_straight`: a straight walk has period at least `2(n-1)`
  (every pseudocircle carries `2(n-1)` crossings), so it does not close up earlier,
* `Arrangement.eq_or_eq_σσ`: two darts at the same crossing on the same curve are equal or
  opposite,
* `Arrangement.crossingOf_α_σσ_ne` (`n ≥ 3`): the two neighbours of a crossing along a curve
  are distinct,
* `Arrangement.eq_or_eq_of_curves`: at most two crossings lie on a given pair of curves,
* `Arrangement.square` (`n ≥ 4`): two distinct crossings of a curve `C` do not have the same
  two neighbours along `C` (the curve would carry only four crossings).

The digon lemma, for `n ≥ 4` (the proof uses only `n ≥ 3`):

* `Arrangement.digon_eq_of_mem_corners`: a crossing is a corner of at most one digon,
* `Arrangement.t_le_one_of_digon`: a corner of a digon is incident to at most one triangle,
* `Arrangement.two_p2_le_deficiency`: `def ≥ 2 p_2`.
-/
import Pca.Excess

open Equiv Finset

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

/-! ## Rewriting lemmas -/

theorem straight_apply (d : D) : A.straight d = A.σ (A.σ (A.α d)) := rfl

theorem curve_straight (d : D) : A.curve (A.straight d) = A.curve d := by
  rw [straight_apply, A.isArrangement.curve_σσ, A.isArrangement.curve_α]

theorem σ_σ_ne (d : D) : A.σ (A.σ d) ≠ d := by
  have h := orbitList_nodup A.σ d
  rw [orbitList_σ] at h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact fun e => h.1.2.1 e.symm

/-- `σ⁻¹ = σ³`. -/
theorem eq_σσσ_of_σ_eq {x y : D} (h : A.σ x = y) : x = A.σ (A.σ (A.σ y)) := by
  rw [← h, A.σ_σ_σ_σ]

theorem σ5 (d : D) : A.σ (A.σ (A.σ (A.σ (A.σ d)))) = A.σ d := by rw [A.σ_σ_σ_σ]

theorem α_α (d : D) : A.α (A.α d) = d := A.isArrangement.α_α d

theorem curve_α (d : D) : A.curve (A.α d) = A.curve d := A.isArrangement.curve_α d

theorem curve_σσ (d : D) : A.curve (A.σ (A.σ d)) = A.curve d := A.isArrangement.curve_σσ d

theorem φ_α (d : D) : A.φ (A.α d) = A.σ d := by rw [φ_apply, α_α]

/-- The cell to the left of `d` is the cell of `σ d`. -/
theorem cellOf_σ (d : D) : A.cellOf (A.σ d) = A.cellOf (A.α d) := by
  rw [← φ_α, cellOf_φ]

theorem crossingOf_σσ (d : D) : A.crossingOf (A.σ (A.σ d)) = A.crossingOf d := by
  rw [crossingOf_σ, crossingOf_σ]

theorem crossingOf_σσσ (d : D) : A.crossingOf (A.σ (A.σ (A.σ d))) = A.crossingOf d := by
  rw [crossingOf_σ, crossingOf_σ, crossingOf_σ]

theorem mem_curves_crossingOf (d : D) : A.curve d ∈ Crossing.curves A (A.crossingOf d) := by
  rw [curves_crossingOf]; exact mem_insert_self _ _

theorem mem_curves_crossingOf_σ (d : D) :
    A.curve (A.σ d) ∈ Crossing.curves A (A.crossingOf d) := by
  rw [curves_crossingOf]; exact mem_insert_of_mem (mem_singleton_self _)

/-- The far end of `d` lies on the curve of `d`. -/
theorem mem_curves_end (d : D) : A.curve d ∈ Crossing.curves A (A.crossingOf (A.α d)) := by
  rw [← curve_α]; exact A.mem_curves_crossingOf _

/-- A crossing on two distinct curves `c`, `c'` has exactly these curves. -/
theorem curves_eq_pair {x : A.Crossing} {c c' : Fin n} (hc : c ∈ Crossing.curves A x)
    (hc' : c' ∈ Crossing.curves A x) (hne : c ≠ c') : Crossing.curves A x = {c, c'} := by
  symm
  refine eq_of_subset_of_card_le ?_ ?_
  · intro e he
    rw [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl <;> assumption
  · rw [A.card_curves, card_pair hne]

/-- The cell of `d` is a digon: `φ² d = d`. -/
theorem φ_φ_of_digon {d : D} (h : A.IsDigon (A.cellOf d)) : A.φ (A.φ d) = d := by
  have hp := A.period_of_size h
  have := iterate_period A.φ d
  rw [hp] at this
  simpa using this

/-- The cell of `d` is a triangle: `φ³ d = d`. -/
theorem φ_φ_φ_of_triangle {d : D} (h : A.IsTriangle (A.cellOf d)) :
    A.φ (A.φ (A.φ d)) = d := by
  have hp := A.period_of_size h
  have := iterate_period A.φ d
  rw [hp] at this
  simpa using this

/-! ## Straight walks do not close up early -/

/-- The straight walk of `d` has period at least `2(n-1)`: the `4(n-1)` darts of the curve of
`d` lie in the straight orbit of `d` or its image under `σ²` (axiom 5). -/
theorem two_mul_le_period_straight (d : D) : 2 * (n - 1) ≤ period A.straight d := by
  have hsub : univ.filter (fun e => A.curve e = A.curve d) ⊆
      orbitFinset A.straight d ∪ (orbitFinset A.straight d).image (fun e => A.σ (A.σ e)) := by
    intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    rcases A.isArrangement.straight d e he.symm with h | h
    · exact mem_union_left _ (mem_orbitFinset.2 h)
    · refine mem_union_right _ (mem_image.2 ⟨_, mem_orbitFinset.2 h, ?_⟩)
      rw [A.σ_σ_σ_σ]
  have h1 := card_le_card hsub
  have h2 := card_union_le (orbitFinset A.straight d)
    ((orbitFinset A.straight d).image (fun e => A.σ (A.σ e)))
  have h3 := card_image_le (s := orbitFinset A.straight d) (f := fun e => A.σ (A.σ e))
  rw [A.card_darts_on] at h1
  rw [card_orbitFinset] at h2 h3
  omega

/-- A straight walk does not return to its start in fewer than `2(n-1)` steps. -/
theorem straight_iterate_ne {d : D} {k : ℕ} (hk : 0 < k) (hk' : k < 2 * (n - 1)) :
    (A.straight^[k]) d ≠ d := by
  intro h
  have h1 := Function.IsPeriodicPt.minimalPeriod_le hk h
  have h2 := A.two_mul_le_period_straight d
  rw [period_eq_minimalPeriod] at h2
  omega

/-! ## Local structure at a crossing -/

/-- Two darts at the same crossing on the same curve are equal or opposite. -/
theorem eq_or_eq_σσ {b c : D} (hx : A.crossingOf b = A.crossingOf c)
    (hc : A.curve b = A.curve c) : c = b ∨ c = A.σ (A.σ b) := by
  rw [crossingOf_eq_iff] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h
  · exact Or.inl h
  · exact absurd (h ▸ hc.symm) (A.isArrangement.curve_σ b)
  · exact Or.inr h
  · exact absurd (by rw [← A.curve_σσσ, ← h, hc]) (A.isArrangement.curve_σ b)

/-- The two neighbours of a crossing along a curve are distinct (`n ≥ 3`): otherwise the
straight walk of `b` would close up after two steps. -/
theorem crossingOf_α_σσ_ne (hn : 3 ≤ n) (b : D) :
    A.crossingOf (A.α (A.σ (A.σ b))) ≠ A.crossingOf (A.α b) := by
  intro h
  rcases A.eq_or_eq_σσ h.symm (by rw [curve_α, curve_α, curve_σσ]) with h' | h'
  · have := congrArg A.α h'
    rw [α_α, α_α] at this
    exact A.σ_σ_ne b this
  · refine A.straight_iterate_ne (d := b) (k := 2) (by norm_num) (by omega) ?_
    show A.straight (A.straight b) = b
    rw [A.straight_apply b, ← h', A.straight_apply, α_α, A.σ_σ_σ_σ]

/-- At most two crossings lie on the two curves `c ≠ c'` (axiom 6). -/
theorem eq_or_eq_of_curves {x y z : A.Crossing} {c c' : Fin n} (hcc : c ≠ c')
    (hx : Crossing.curves A x = {c, c'}) (hy : Crossing.curves A y = {c, c'})
    (hz : Crossing.curves A z = {c, c'}) (hxy : x ≠ y) : z = x ∨ z = y := by
  by_contra h
  push Not at h
  have hsub : ({x, y, z} : Finset A.Crossing) ⊆
      univ.filter (fun w : A.Crossing => Crossing.curves A w = {c, c'}) := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simpa
  have h1 := card_le_card hsub
  rw [A.card_curves_eq_pair c c' hcc, card_insert_of_notMem, card_pair h.2.symm] at h1
  · omega
  · simp only [mem_insert, mem_singleton, not_or]
    exact ⟨hxy, h.1.symm⟩

/-- Every crossing has a second crossing on the same two curves (axiom 6). -/
theorem exists_ne_curves_eq (x : A.Crossing) :
    ∃ y, y ≠ x ∧ Crossing.curves A y = Crossing.curves A x := by
  obtain ⟨d, rfl⟩ := x.exists_mk
  have hne := (A.isArrangement.curve_σ d).symm
  have h := A.card_curves_eq_pair _ _ hne
  obtain ⟨y, hy, hyx⟩ := exists_mem_ne (s := univ.filter
    (fun w : A.Crossing => Crossing.curves A w = {A.curve d, A.curve (A.σ d)})) (by omega)
    (Orbit.mk A.σ d)
  refine ⟨y, hyx, ?_⟩
  rw [(mem_filter.1 hy).2, ← crossingOf, curves_crossingOf]

/-- **Square lemma** (`n ≥ 4`): two distinct crossings `x`, `x'` of a curve `C` do not have the
same two neighbours along `C`. Here `b` is a dart of `C` at `x` and `b'` one at `x'`, and the
neighbours are matched crosswise: `b` and `σ² b'` end at the same crossing, `σ² b` and `b'`
too. Then the straight walk closes after four steps, but `C` carries `2(n-1) ≥ 6` crossings. -/
theorem square (hn : 4 ≤ n) {b b' : D} (hx : A.crossingOf b ≠ A.crossingOf b')
    (hc : A.curve b = A.curve b')
    (h1 : A.crossingOf (A.α b) = A.crossingOf (A.α (A.σ (A.σ b'))))
    (h2 : A.crossingOf (A.α (A.σ (A.σ b))) = A.crossingOf (A.α b')) : False := by
  have k1 : A.straight b = A.α (A.σ (A.σ b')) := by
    rcases A.eq_or_eq_σσ h1 (by rw [curve_α, curve_α, curve_σσ, hc]) with h | h
    · have := congrArg A.α h
      rw [α_α, α_α] at this
      exact absurd (by rw [← this, crossingOf_σσ]) hx
    · exact h.symm
  have k2 : A.straight b' = A.α (A.σ (A.σ b)) := by
    rcases A.eq_or_eq_σσ h2.symm (by rw [curve_α, curve_α, curve_σσ, hc]) with h | h
    · have := congrArg A.α h
      rw [α_α, α_α] at this
      exact absurd (by rw [← this, crossingOf_σσ]) hx
    · exact h.symm
  refine A.straight_iterate_ne (d := b) (k := 4) (by norm_num) (by omega) ?_
  show A.straight (A.straight (A.straight (A.straight b))) = b
  rw [k1, A.straight_apply (A.α _), α_α, A.σ_σ_σ_σ, k2, A.straight_apply (A.α _), α_α,
    A.σ_σ_σ_σ]

/-! ## Digons -/

/-- The second side of the digon of `d`: `φ d = α (σ³ d)`. -/
theorem φ_eq_of_digon {d : D} (h : A.IsDigon (A.cellOf d)) :
    A.α (A.φ d) = A.σ (A.σ (A.σ d)) :=
  A.eq_σσσ_of_σ_eq (A.φ_φ_of_digon h)

/-- A digon and a triangle do not share a side: the second side of the triangle at either end
of the common side would lie on the same curve. -/
theorem not_triangle_α_of_digon {d : D} (h : A.IsDigon (A.cellOf d)) :
    ¬ A.IsTriangle (A.cellOf (A.α d)) := by
  intro ht
  have h3 := A.φ_φ_φ_of_triangle ht
  rw [φ_α] at h3
  -- `g = φ (σ d)` is followed by `α d` in the triangle
  have hg : A.α (A.φ (A.σ d)) = A.σ (A.σ (A.σ (A.α d))) := A.eq_σσσ_of_σ_eq h3
  have hc : A.curve (A.φ (A.σ d)) = A.curve (A.σ d) := by
    rw [← curve_α, hg, curve_σσσ, ← φ_apply, ← curve_α, φ_eq_of_digon A h, curve_σσσ]
  exact A.curve_φ_ne _ hc

/-- Two digons do not share a side (`n ≥ 3`): the straight walk along the curve of `σ d` would
close up after two steps. -/
theorem not_digon_α_of_digon (hn : 3 ≤ n) {d : D} (h : A.IsDigon (A.cellOf d)) :
    ¬ A.IsDigon (A.cellOf (A.α d)) := by
  intro h'
  have h2 := A.φ_φ_of_digon h'
  rw [φ_α] at h2
  have hs : A.α (A.σ d) = A.σ (A.σ (A.σ (A.α d))) := A.eq_σσσ_of_σ_eq h2
  refine A.straight_iterate_ne (d := A.σ d) (k := 2) (by norm_num) (by omega) ?_
  show A.straight (A.straight (A.σ d)) = A.σ d
  rw [A.straight_apply (A.σ d), hs, A.σ5, ← φ_apply, A.straight_apply, φ_eq_of_digon A h,
    A.σ5]

/-- Two digons are not opposite at a crossing (`n ≥ 3`): their second corners would be two
distinct crossings on the curves of `x` besides `x`, or equal, so that the curve of `d` has
only two crossings. -/
theorem not_digon_σσ_of_digon (hn : 3 ≤ n) {d : D} (h : A.IsDigon (A.cellOf d)) :
    ¬ A.IsDigon (A.cellOf (A.σ (A.σ d))) := by
  intro h'
  have hne := A.isArrangement.curve_σ d
  have hx : Crossing.curves A (A.crossingOf d) = {A.curve d, A.curve (A.σ d)} :=
    curves_crossingOf A d
  have hy : Crossing.curves A (A.crossingOf (A.α d)) = {A.curve d, A.curve (A.σ d)} := by
    rw [← crossingOf_φ, curves_crossingOf_φ, ← curve_α (d := A.φ d), φ_eq_of_digon A h,
      curve_σσσ]
  have hy' : Crossing.curves A (A.crossingOf (A.α (A.σ (A.σ d)))) =
      {A.curve d, A.curve (A.σ d)} := by
    rw [← crossingOf_φ, curves_crossingOf_φ, ← curve_α (d := A.φ _), φ_eq_of_digon A h',
      A.σ5, curve_σσ]
  rcases A.eq_or_eq_of_curves (Ne.symm hne) hx hy hy' (A.crossingOf_α_ne d).symm with e | e
  · exact A.crossingOf_α_ne _ (by rw [e, crossingOf_σσ])
  · exact A.crossingOf_α_σσ_ne hn d e

/-- The darts at the crossing of `d`. -/
theorem mem_darts_crossingOf {d e : D} :
    e ∈ (A.crossingOf d).darts ↔ e ∈ [d, A.σ d, A.σ (A.σ d), A.σ (A.σ (A.σ d))] := by
  rw [Orbit.mem_darts, ← crossingOf, eq_comm, crossingOf_eq_iff]

/-- A corner of a digon has a dart in the digon. -/
theorem exists_dart_of_mem_corners {f : A.Cell} {x : A.Crossing} (hx : x ∈ Cell.corners A f) :
    ∃ d, A.cellOf d = f ∧ A.crossingOf d = x := by
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  exact ⟨d, Orbit.mem_darts.1 hd, rfl⟩

/-- **Digon lemma**, first part: a crossing is a corner of at most one digon (`n ≥ 4`). -/
theorem digon_eq_of_mem_corners (hn : 4 ≤ n) {f g : A.Cell} (hf : A.IsDigon f)
    (hg : A.IsDigon g) {x : A.Crossing} (hxf : x ∈ Cell.corners A f)
    (hxg : x ∈ Cell.corners A g) : f = g := by
  obtain ⟨d, rfl, rfl⟩ := A.exists_dart_of_mem_corners hxf
  obtain ⟨e, rfl, he⟩ := A.exists_dart_of_mem_corners hxg
  by_cases hde : d = e
  · rw [hde]
  rw [crossingOf_eq_iff] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · exact absurd he hde
  -- `he` puts `d` among the darts `e, σ e, σ² e, σ³ e` at `x`
  exfalso
  rcases he with rfl | rfl | rfl
  · rw [cellOf_σ] at hf; exact A.not_digon_α_of_digon (by omega) hg hf
  · exact A.not_digon_σσ_of_digon (by omega) hg hf
  · -- `e = σ (σ³ e)`, so `g` is the cell on the other side of a side of `f`
    rw [← A.σ_σ_σ_σ e, cellOf_σ] at hg
    exact A.not_digon_α_of_digon (by omega) hf hg

/-- **Digon lemma**, second part: a corner of a digon is incident to at most one triangle (only
the cell opposite to the digon can be a triangle). -/
theorem t_le_one_of_digon {f : A.Cell} (hf : A.IsDigon f) {x : A.Crossing}
    (hx : x ∈ Cell.corners A f) : A.t x ≤ 1 := by
  obtain ⟨d, rfl, rfl⟩ := A.exists_dart_of_mem_corners hx
  rw [t_eq_tAngles, tAngles]
  refine (card_le_card (t := {A.σ (A.σ d)}) ?_).trans (card_singleton _).le
  intro e he
  rw [mem_filter, mem_darts_crossingOf] at he
  obtain ⟨he, ht⟩ := he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rw [mem_singleton]
  rcases he with rfl | rfl | rfl | rfl
  · exact absurd (hf.symm.trans ht) (by norm_num)
  · rw [cellOf_σ] at ht; exact absurd ht (A.not_triangle_α_of_digon hf)
  · rfl
  · rw [← φ_eq_of_digon A hf] at ht
    exact absurd ht (A.not_triangle_α_of_digon (by rw [cellOf_φ]; exact hf))

/-- **Digon lemma**, consequence: `def ≥ 2 p_2` (`n ≥ 4`). The `2 p_2` corners of digons are
pairwise distinct and each contributes `2 - t x ≥ 1` to the deficiency. -/
theorem two_p2_le_deficiency (hn : 4 ≤ n) : 2 * A.p 2 ≤ A.deficiency := by
  set Y := (univ.filter (A.IsKCell 2)).biUnion (Cell.corners A) with hY
  have hdisj : ((univ.filter (A.IsKCell 2) : Finset A.Cell) : Set A.Cell).PairwiseDisjoint
      (Cell.corners A) := by
    intro f hf g hg hfg
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf hg
    exact disjoint_left.2 fun x hxf hxg => hfg (A.digon_eq_of_mem_corners hn hf hg hxf hxg)
  have hcard : Y.card = 2 * A.p 2 := by
    rw [hY, card_biUnion hdisj, p, mul_comm, ← smul_eq_mul, ← sum_const]
    exact sum_congr rfl fun f hf => Digon.card_corners (mem_filter.1 hf).2
  have hsub : Y ⊆ univ.filter (fun x => A.t x ≤ 1) := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := mem_biUnion.1 hx
    exact mem_filter.2 ⟨mem_univ _, A.t_le_one_of_digon (mem_filter.1 hf).2 hxf⟩
  rw [← hcard, card_eq_sum_ones, deficiency]
  calc ∑ x ∈ Y, 1 ≤ ∑ x ∈ Y, (2 - A.t x) :=
        sum_le_sum fun x hx => by have := (mem_filter.1 (hsub hx)).2; omega
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _

end Pca.Arrangement
