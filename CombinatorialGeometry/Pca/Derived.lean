/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Milestone 1: derived facts

Proved for every arrangement `A : Arrangement n D` (see `doc/pca/pca.md`):

* `Arrangement.connected`: the map is connected (`σ` and `α` generate a transitive action),
* `Arrangement.card_crossingsOn`: every pseudocircle carries `2(n-1)` crossings,
* `Arrangement.card_segmentsOn`: every pseudocircle has `2(n-1)` segments,
* `Arrangement.card_X`: `|X| = n(n-1)`,
* `Arrangement.card_darts`: `|D| = 4|X|`,
* `Arrangement.card_segments`: `#segments = 2|X|`,
* `Arrangement.card_cells`: `#cells = |X| + 2`.

Also: `Arrangement.nbrs`, the four neighbours of a crossing with multiplicity.
-/
import Pca.Counting
import Mathlib.Combinatorics.Enumerative.DoubleCounting

open Equiv Finset

namespace Pca

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## General facts on orbits -/

theorem period_eq_minimalPeriod (f : Perm D) (d : D) :
    period f d = Function.minimalPeriod f d := by
  have hmem : d ∈ Function.periodicPts f := ⟨period f d, period_pos f d, iterate_period f d⟩
  apply le_antisymm
  · exact Nat.find_min' _
      ⟨Function.minimalPeriod_pos_of_mem_periodicPts hmem, Function.iterate_minimalPeriod⟩
  · exact Function.IsPeriodicPt.minimalPeriod_le (period_pos f d) (iterate_period f d)

theorem orbitList_nodup (f : Perm D) (d : D) : (orbitList f d).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj h
  rw [List.mem_range, period_eq_minimalPeriod] at hi hj
  exact Function.iterate_injOn_Iio_minimalPeriod hi hj h

omit [Fintype D] in
theorem card_filter_toFinset {l : List D} (hl : l.Nodup) (P : D → Prop) [DecidablePred P] :
    (l.toFinset.filter P).card = (l.filter (fun e => decide (P e))).length := by
  rw [← List.toFinset_card_of_nodup (hl.filter _)]
  congr 1
  ext e
  simp

/-- An orbit has as many darts as the period of any of its darts. -/
theorem card_orbitFinset (f : Perm D) (d : D) : (orbitFinset f d).card = period f d := by
  rw [orbitFinset, List.toFinset_card_of_nodup (orbitList_nodup f d), orbitList,
    List.length_map, List.length_range]

theorem Orbit.darts_mk (f : Perm D) (d : D) : (Orbit.mk f d).darts = orbitFinset f d := rfl

omit [Fintype D] [DecidableEq D] in
theorem Orbit.mk_eq_mk {f : Perm D} {a b : D} : Orbit.mk f a = Orbit.mk f b ↔ f.SameCycle a b :=
  Quotient.eq

omit [Fintype D] [DecidableEq D] in
theorem Orbit.exists_mk {f : Perm D} (o : Orbit f) : ∃ d, Orbit.mk f d = o :=
  Quotient.exists_rep o

/-- The darts of the orbit `o` are exactly the darts whose orbit is `o`. -/
theorem Orbit.mem_darts {f : Perm D} {o : Orbit f} {d : D} : d ∈ o.darts ↔ Orbit.mk f d = o := by
  obtain ⟨a, rfl⟩ := o.exists_mk
  rw [darts_mk, mem_orbitFinset, mk_eq_mk]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Counting darts with a property orbit by orbit. -/
theorem card_filter_eq_sum_orbits (f : Perm D) (P : D → Prop) [DecidablePred P] :
    (univ.filter P).card = ∑ o : Orbit f, (o.darts.filter P).card := by
  rw [card_eq_sum_card_fiberwise (f := Orbit.mk f) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun o _ => ?_
  congr 1
  ext d
  simp only [mem_filter, mem_univ, true_and, Orbit.mem_darts]
  exact and_comm

/-- The number of darts is the sum of the orbit sizes. -/
theorem card_eq_sum_size (f : Perm D) : Fintype.card D = ∑ o : Orbit f, o.size := by
  have h := card_filter_eq_sum_orbits f (fun _ => True)
  simpa [Orbit.size] using h

/-! ## Crossings and segments -/

namespace Arrangement

variable {n : ℕ} (A : Arrangement n D)

theorem period_σ (d : D) : period A.σ d = 4 := by
  rw [← card_orbitFinset]; exact A.isArrangement.card_crossing d

theorem σ_σ_σ_σ (d : D) : A.σ (A.σ (A.σ (A.σ d))) = d := by
  have h := iterate_period A.σ d
  rw [A.period_σ] at h
  simpa using h

theorem orbitList_σ (d : D) :
    orbitList A.σ d = [d, A.σ d, A.σ (A.σ d), A.σ (A.σ (A.σ d))] := by
  simp [orbitList, A.period_σ, List.range_succ]

theorem period_α (d : D) : period A.α d = 2 := by
  apply le_antisymm
  · exact Nat.find_min' _ ⟨by norm_num, A.isArrangement.α_α d⟩
  · by_contra h
    have h1 : period A.α d = 1 := by have := period_pos A.α d; omega
    have := iterate_period A.α d
    rw [h1] at this
    exact A.isArrangement.α_ne d this

theorem orbitList_α (d : D) : orbitList A.α d = [d, A.α d] := by
  simp [orbitList, A.period_α, List.range_succ]

theorem curve_σσσ (d : D) : A.curve (A.σ (A.σ (A.σ d))) = A.curve (A.σ d) :=
  A.isArrangement.curve_σσ (A.σ d)

/-- The curves through the crossing of `d` are the curves of `d` and `σ d`. -/
theorem curves_crossingOf (d : D) :
    Crossing.curves A (A.crossingOf d) = {A.curve d, A.curve (A.σ d)} := by
  simp only [Crossing.curves, crossingCurves, crossingOf, Orbit.darts_mk, orbitFinset,
    orbitList_σ]
  ext c
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, mem_image, mem_insert,
    mem_singleton]
  constructor
  · rintro ⟨e, he, rfl⟩
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl (A.isArrangement.curve_σσ _)
    · exact Or.inr (A.curve_σσσ _)
  · rintro (rfl | rfl)
    · exact ⟨d, Or.inl rfl, rfl⟩
    · exact ⟨A.σ d, Or.inr (Or.inl rfl), rfl⟩

/-- Exactly two curves pass through every crossing. -/
theorem card_curves (x : A.Crossing) : (Crossing.curves A x).card = 2 := by
  obtain ⟨d, rfl⟩ := x.exists_mk
  rw [← crossingOf, curves_crossingOf]
  exact card_pair (A.isArrangement.curve_σ d).symm

/-- A crossing has exactly two darts on each of its curves, and none on other curves. -/
theorem card_darts_filter_curve (x : A.Crossing) (C : Fin n) :
    (x.darts.filter (fun d => A.curve d = C)).card =
      if C ∈ Crossing.curves A x then 2 else 0 := by
  obtain ⟨d, rfl⟩ := x.exists_mk
  have hnd := orbitList_nodup A.σ d
  rw [← crossingOf, curves_crossingOf, crossingOf, Orbit.darts_mk, orbitFinset,
    card_filter_toFinset hnd, orbitList_σ]
  have h2 := A.isArrangement.curve_σσ d
  have h3 := A.curve_σσσ d
  have hne := A.isArrangement.curve_σ d
  by_cases ha : A.curve d = C
  · subst ha; simp [h2, h3, hne, Ne.symm hne]
  · by_cases hb : A.curve (A.σ d) = C
    · subst hb; simp [h2, h3, ha, hne]
    · simp [h2, h3, ha, hb, Ne.symm ha, Ne.symm hb]

/-- The darts of a segment are `d` and `α d`. -/
theorem curves_segmentOf (d : D) : Segment.curves A (A.segmentOf d) = {A.curve d} := by
  simp [Segment.curves, segmentOf, Orbit.darts_mk, orbitFinset, orbitList_α,
    A.isArrangement.curve_α]

/-- A segment has exactly two darts on its curve, and none on other curves. -/
theorem card_segment_darts_filter_curve (s : A.Segment) (C : Fin n) :
    (s.darts.filter (fun d => A.curve d = C)).card =
      if C ∈ Segment.curves A s then 2 else 0 := by
  obtain ⟨d, rfl⟩ := s.exists_mk
  have hnd := orbitList_nodup A.α d
  rw [← segmentOf, curves_segmentOf, segmentOf, Orbit.darts_mk, orbitFinset,
    card_filter_toFinset hnd, orbitList_α]
  have h1 := A.isArrangement.curve_α d
  by_cases ha : A.curve d = C
  · subst ha; simp [h1]
  · simp [h1, ha, Ne.symm ha]

/-- The number of darts on `C` is twice the number of crossings on `C`. -/
theorem card_darts_on_eq_crossings (C : Fin n) :
    (univ.filter (fun d => A.curve d = C)).card = 2 * (A.crossingsOn C).card := by
  rw [card_filter_eq_sum_orbits A.σ, crossingsOn, card_filter, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [card_darts_filter_curve]
  split_ifs <;> rfl

/-- The number of darts on `C` is twice the number of segments on `C`. -/
theorem card_darts_on_eq_segments (C : Fin n) :
    (univ.filter (fun d => A.curve d = C)).card = 2 * (A.segmentsOn C).card := by
  rw [card_filter_eq_sum_orbits A.α, segmentsOn, card_filter, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [card_segment_darts_filter_curve]
  split_ifs <;> rfl

/-! ## Neighbours with multiplicity -/

/-- The four neighbours of a crossing `x`, with multiplicity: the multiset of the crossings at
the other ends of the four darts at `x`. (`Neighbors` is the relation and forgets
multiplicity.) -/
def nbrs (x : A.Crossing) : Multiset A.Crossing := x.darts.val.map (fun d => A.crossingOf (A.α d))

theorem card_nbrs (x : A.Crossing) : Multiset.card (A.nbrs x) = 4 := by
  obtain ⟨d, rfl⟩ := x.exists_mk
  rw [nbrs, Multiset.card_map, ← Finset.card_def, Orbit.darts_mk]
  exact A.isArrangement.card_crossing d

theorem mem_nbrs {x y : A.Crossing} : y ∈ A.nbrs x ↔ A.Neighbors x y := by
  simp [nbrs, Neighbors]

/-! ## Milestone 1 -/

/-- Axiom 6 in terms of `Crossing.curves`. -/
theorem card_curves_eq_pair (c c' : Fin n) (h : c ≠ c') :
    (univ.filter (fun x : A.Crossing => Crossing.curves A x = {c, c'})).card = 2 :=
  A.isArrangement.intersecting c c' h

/-- Every pseudocircle carries exactly `2(n-1)` crossings. -/
theorem card_crossingsOn (C : Fin n) : (A.crossingsOn C).card = 2 * (n - 1) := by
  have hU : A.crossingsOn C = (univ.erase C).biUnion
      (fun c' => univ.filter (fun x : A.Crossing => Crossing.curves A x = {C, c'})) := by
    ext x
    obtain ⟨d, rfl⟩ := x.exists_mk
    have hne := A.isArrangement.curve_σ d
    simp only [crossingsOn, mem_filter, mem_univ, true_and, and_true, mem_biUnion, mem_erase,
      ne_eq]
    rw [← crossingOf, curves_crossingOf]
    constructor
    · intro h
      rcases mem_insert.1 h with rfl | h
      · exact ⟨A.curve (A.σ d), hne, rfl⟩
      · rw [mem_singleton] at h
        subst h
        exact ⟨A.curve d, fun h' => hne h'.symm, pair_comm _ _⟩
    · rintro ⟨c', -, h⟩
      rw [h]; exact mem_insert_self _ _
  have hdisj : (↑(univ.erase C) : Set (Fin n)).PairwiseDisjoint
      (fun c' => univ.filter (fun x : A.Crossing => Crossing.curves A x = {C, c'})) := by
    intro a ha b hb hab
    simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff,
      true_and] at ha hb
    refine disjoint_left.2 fun x hxa hxb => hab ?_
    simp only [mem_filter, mem_univ, true_and] at hxa hxb
    have hmem : a ∈ ({C, b} : Finset (Fin n)) := hxb ▸ hxa ▸ mem_insert_of_mem (mem_singleton_self a)
    rcases mem_insert.1 hmem with h | h
    · exact absurd h ha
    · exact mem_singleton.1 h
  rw [hU, card_biUnion hdisj,
    sum_congr rfl fun c' hc' => A.card_curves_eq_pair C c' (ne_of_mem_erase hc').symm,
    sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin, smul_eq_mul,
    mul_comm]

/-- Every pseudocircle has exactly `4(n-1)` darts. -/
theorem card_darts_on (C : Fin n) :
    (univ.filter (fun d => A.curve d = C)).card = 4 * (n - 1) := by
  rw [card_darts_on_eq_crossings, card_crossingsOn]; ring

/-- Every pseudocircle has exactly `2(n-1)` segments. -/
theorem card_segmentsOn (C : Fin n) : (A.segmentsOn C).card = 2 * (n - 1) := by
  have h := A.card_darts_on_eq_segments C
  rw [card_darts_on] at h
  omega

/-- `|X| = n(n-1)`: double counting of the pairs (pseudocircle, crossing on it). -/
theorem card_X : A.X.card = n * (n - 1) := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := (univ : Finset (Fin n)))
    (t := (univ : Finset A.Crossing)) (fun C x => C ∈ Crossing.curves A x)
  simp only [bipartiteAbove, bipartiteBelow] at h
  have h1 : ∀ C : Fin n, (univ.filter (fun x : A.Crossing => C ∈ Crossing.curves A x)).card =
      2 * (n - 1) := A.card_crossingsOn
  have h2 : ∀ x : A.Crossing, (univ.filter (fun C : Fin n => C ∈ Crossing.curves A x)).card =
      2 := fun x => by simpa using A.card_curves x
  rw [sum_congr rfl fun C _ => h1 C, sum_congr rfl fun x _ => h2 x, sum_const, sum_const,
    card_univ, card_univ, Fintype.card_fin, smul_eq_mul, smul_eq_mul] at h
  have h3 : 2 * A.X.card = 2 * (n * (n - 1)) := by
    rw [X, card_univ, mul_comm, ← h]; ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h3

/-- `|D| = 4|X|`: every crossing has four darts. -/
theorem card_darts : Fintype.card D = 4 * A.X.card := by
  rw [card_eq_sum_size A.σ, X, card_univ, ← Finset.card_univ, mul_comm, ← smul_eq_mul,
    ← sum_const]
  refine sum_congr rfl fun x _ => ?_
  obtain ⟨d, rfl⟩ := x.exists_mk
  exact A.isArrangement.card_crossing d

/-- `|D| = 2 · #segments`: every segment has two darts. -/
theorem card_darts_eq_segments : Fintype.card D = 2 * Fintype.card A.Segment := by
  rw [card_eq_sum_size A.α, ← Finset.card_univ, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun s _ => ?_
  obtain ⟨d, rfl⟩ := s.exists_mk
  rw [Orbit.size, Orbit.darts_mk, card_orbitFinset, period_α]

/-- `#segments = 2|X|`. -/
theorem card_segments : Fintype.card A.Segment = 2 * A.X.card := by
  have h1 := A.card_darts
  have h2 := A.card_darts_eq_segments
  omega

/-- `#cells = |X| + 2`, from the Euler axiom. -/
theorem card_cells : Fintype.card A.Cell = A.X.card + 2 := by
  have he := A.isArrangement.euler
  have hs := A.card_segments
  have hx : Fintype.card A.Crossing = A.X.card := by rw [X, card_univ]
  change (Fintype.card A.Crossing : ℤ) - Fintype.card A.Segment + Fintype.card A.Cell = 2 at he
  omega

/-! ## Connectivity -/

/-- One step of the map: `b = σ a` or `b = α a`. -/
def Step (a b : D) : Prop := b = A.σ a ∨ b = A.α a

theorem eqvGen_pow (f : Perm D) (hf : ∀ y, Relation.EqvGen A.Step y (f y)) (d : D) (i : ℕ) :
    Relation.EqvGen A.Step d ((f ^ i) d) := by
  induction i with
  | zero => exact .refl _
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply]
    exact ih.trans _ _ _ (hf _)

theorem eqvGen_σ (d : D) : Relation.EqvGen A.Step d (A.σ d) := .rel _ _ (Or.inl rfl)

theorem eqvGen_α (d : D) : Relation.EqvGen A.Step d (A.α d) := .rel _ _ (Or.inr rfl)

theorem eqvGen_of_sameCycle {f : Perm D} (hf : ∀ y, Relation.EqvGen A.Step y (f y)) {d e : D}
    (h : f.SameCycle d e) : Relation.EqvGen A.Step d e := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  exact A.eqvGen_pow f hf d i

theorem eqvGen_straight (y : D) : Relation.EqvGen A.Step y (A.straight y) :=
  (A.eqvGen_α y).trans _ _ _ ((A.eqvGen_σ _).trans _ _ _ (A.eqvGen_σ _))

/-- Two darts on the same curve are connected. -/
theorem eqvGen_of_curve_eq {d e : D} (h : A.curve d = A.curve e) : Relation.EqvGen A.Step d e := by
  rcases A.isArrangement.straight d e h with h | h
  · exact A.eqvGen_of_sameCycle A.eqvGen_straight h
  · exact (A.eqvGen_of_sameCycle A.eqvGen_straight h).trans _ _ _
      ((A.eqvGen_σ e).trans _ _ _ (A.eqvGen_σ _)).symm

/-- **Connectivity**: any two darts are related by the equivalence relation generated by `σ` and
`α`. It follows from axioms 5 (a curve is one straight walk) and 6 (two curves cross). -/
theorem connected (d e : D) : Relation.EqvGen A.Step d e := by
  by_cases h : A.curve d = A.curve e
  · exact A.eqvGen_of_curve_eq h
  · have h2 := A.isArrangement.intersecting _ _ h
    obtain ⟨x, hx⟩ : (univ.filter (fun x : A.Crossing =>
        crossingCurves A.σ A.curve x = {A.curve d, A.curve e})).Nonempty := by
      rw [← card_pos, h2]; norm_num
    simp only [mem_filter, mem_univ, true_and] at hx
    obtain ⟨a, rfl⟩ := x.exists_mk
    have hd : A.curve d ∈ crossingCurves A.σ A.curve (Orbit.mk A.σ a) := by
      rw [hx]; exact mem_insert_self _ _
    have he : A.curve e ∈ crossingCurves A.σ A.curve (Orbit.mk A.σ a) := by
      rw [hx]; exact mem_insert_of_mem (mem_singleton_self _)
    obtain ⟨b, hb, hbd⟩ := mem_image.1 hd
    obtain ⟨c, hc, hce⟩ := mem_image.1 he
    rw [Orbit.darts_mk, mem_orbitFinset] at hb hc
    exact (A.eqvGen_of_curve_eq hbd.symm).trans _ _ _
      ((A.eqvGen_of_sameCycle A.eqvGen_σ (hb.symm.trans hc)).trans _ _ _ (A.eqvGen_of_curve_eq hce))

/-- **Connectivity**, group form: the subgroup generated by `σ` and `α` acts transitively on
the darts. -/
theorem connected_closure (d e : D) :
    ∃ g ∈ Subgroup.closure ({A.σ, A.α} : Set (Perm D)), g d = e := by
  induction A.connected d e with
  | rel a b h =>
    rcases h with rfl | rfl
    · exact ⟨A.σ, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
    · exact ⟨A.α, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
  | refl a => exact ⟨1, Subgroup.one_mem _, rfl⟩
  | symm a b _ ih =>
    obtain ⟨g, hg, rfl⟩ := ih
    exact ⟨g⁻¹, Subgroup.inv_mem _ hg, by simp⟩
  | trans a b c _ _ ih1 ih2 =>
    obtain ⟨g, hg, rfl⟩ := ih1
    obtain ⟨h, hh, rfl⟩ := ih2
    exact ⟨h * g, Subgroup.mul_mem _ hh hg, rfl⟩

end Arrangement

end Pca
