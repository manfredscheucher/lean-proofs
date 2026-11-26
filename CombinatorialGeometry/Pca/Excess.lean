/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Milestone 2: elementary facts on triangles and digons, and the counting identities

Proved for every arrangement `A : Arrangement n D` (see `doc/pca/pca.md`, Step 1 of
the (unpublished) notes on the maximum number of triangles).

Elementary facts (no loops, so a 2- or 3-cell does not visit a crossing twice):

* `Arrangement.crossingOf_α_ne`: a segment joins two distinct crossings,
* `Arrangement.Triangle.card_corners`, `.card_sides`, `.card_curves`, `.cellOf_α_ne`,
* `Arrangement.Digon.card_corners`, `.card_sides`, `.card_curves`, `.curves_corner`,
  `.cellOf_α_ne`,
* `Arrangement.t_eq_tAngles`, `Arrangement.t_eq_tCorners`.

Counting identities:

* `Arrangement.three_p3_eq_sum_t`: `3 p_3 = ∑_x t(x)`,
* `Arrangement.excess_eq_sum_t`: `e = ∑_x (t(x) - 2)`,
* `Arrangement.excess_eq_X'_sub_deficiency`: `e = |X'| - def`, assuming `t(x) ≤ 3`,
* `Arrangement.excess_eq_diamond_sub_trigophobic`: `e = δ - φ`,
* `Arrangement.sum_tC`, `Arrangement.sum_t_crossingsOn`, `Arrangement.tC_sub_eq`,
  `Arrangement.excess_eq_sum_tC`, `Arrangement.excess_eq_sum_diamondOn`: the count by
  pseudocircles,
* `Arrangement.excess_modEq`: `e ≡ n(n-1) (mod 3)`.
-/
import Pca.Derived
import Mathlib.Tactic.IntervalCases

open Equiv Finset

namespace Pca

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Summing a dart count over a set `S` of orbits: the darts `d` with `P d` whose orbit lies
in `S`. -/
theorem sum_card_filter_orbits (f : Perm D) (S : Finset (Orbit f)) (P : D → Prop)
    [DecidablePred P] :
    ∑ o ∈ S, (o.darts.filter P).card = (univ.filter (fun d => Orbit.mk f d ∈ S ∧ P d)).card := by
  rw [card_filter_eq_sum_orbits f, ← univ_inter S, ← sum_ite_mem]
  refine sum_congr rfl fun o _ => ?_
  split_ifs with h
  · congr 1
    refine filter_congr fun d hd => ?_
    rw [Orbit.mem_darts.1 hd]
    simp [h]
  · symm
    rw [card_eq_zero, filter_eq_empty_iff]
    intro d hd
    rw [Orbit.mem_darts.1 hd]
    simp [h]

namespace Arrangement

variable {n : ℕ} (A : Arrangement n D)

/-! ## Basic rewriting lemmas -/

theorem φ_apply (d : D) : A.φ d = A.σ (A.α d) := rfl

theorem σ_ne (d : D) : A.σ d ≠ d := fun h => A.isArrangement.curve_σ d (by rw [h])

theorem crossingOf_eq_iff {a b : D} :
    A.crossingOf a = A.crossingOf b ↔ b ∈ [a, A.σ a, A.σ (A.σ a), A.σ (A.σ (A.σ a))] := by
  rw [crossingOf, crossingOf, Orbit.mk_eq_mk, ← mem_orbitList, orbitList_σ]

theorem crossingOf_σ (d : D) : A.crossingOf (A.σ d) = A.crossingOf d := by
  rw [crossingOf, crossingOf, Orbit.mk_eq_mk]
  exact Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl _ _)

theorem crossingOf_φ (d : D) : A.crossingOf (A.φ d) = A.crossingOf (A.α d) := A.crossingOf_σ _

theorem segmentOf_eq_iff {a b : D} : A.segmentOf a = A.segmentOf b ↔ b ∈ [a, A.α a] := by
  rw [segmentOf, segmentOf, Orbit.mk_eq_mk, ← mem_orbitList, orbitList_α]

theorem darts_segmentOf (d : D) : (A.segmentOf d).darts = {d, A.α d} := by
  simp [segmentOf, Orbit.darts_mk, orbitFinset, orbitList_α]

theorem cellOf_eq_iff {a b : D} : A.cellOf a = A.cellOf b ↔ A.φ.SameCycle a b :=
  Orbit.mk_eq_mk

theorem cellOf_φ (d : D) : A.cellOf (A.φ d) = A.cellOf d := by
  rw [cellOf_eq_iff]
  exact Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl _ _)

theorem mem_darts_cellOf {d e : D} : e ∈ (A.cellOf d).darts ↔ A.φ.SameCycle d e := by
  rw [cellOf, Orbit.darts_mk, mem_orbitFinset]

theorem mem_darts_cellOf_self (d : D) : d ∈ (A.cellOf d).darts :=
  A.mem_darts_cellOf.2 (Perm.SameCycle.refl _ _)

theorem size_cellOf (d : D) : (A.cellOf d).size = period A.φ d := by
  rw [Orbit.size, cellOf, Orbit.darts_mk, card_orbitFinset]

theorem curve_φ_ne (d : D) : A.curve (A.φ d) ≠ A.curve d := by
  rw [φ_apply, ← A.isArrangement.curve_α d]
  exact A.isArrangement.curve_σ _

theorem curve_σ_φ (d : D) : A.curve (A.σ (A.φ d)) = A.curve d := by
  rw [φ_apply, A.isArrangement.curve_σσ, A.isArrangement.curve_α]

/-- The curves through the crossing of `φ d` are the curves of `d` and `φ d`. -/
theorem curves_crossingOf_φ (d : D) :
    Crossing.curves A (A.crossingOf (A.φ d)) = {A.curve d, A.curve (A.φ d)} := by
  rw [crossingOf_φ, curves_crossingOf, A.isArrangement.curve_α, φ_apply]

/-! ## No loops

A segment joins two distinct crossings. If `α d = σ² d`, then `straight d = d`, so by axiom 5
the curve of `d` has only the two darts `d`, `σ² d`; but every curve has `4(n-1) ≥ 4` darts. -/

theorem α_ne_σσ (d : D) : A.α d ≠ A.σ (A.σ d) := by
  intro h
  have hs : straightPerm A.σ A.α d = d := by
    show A.σ (A.σ (A.α d)) = d
    rw [h, A.σ_σ_σ_σ]
  have key : ∀ e, (straightPerm A.σ A.α).SameCycle d e → e = d := by
    intro e he
    obtain ⟨i, rfl⟩ := he.exists_nat_pow_eq
    exact Perm.pow_apply_eq_self_of_apply_eq_self hs i
  have hsub : univ.filter (fun e => A.curve e = A.curve d) ⊆ {d, A.σ (A.σ d)} := by
    intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    rcases A.isArrangement.straight d e he.symm with h1 | h1
    · simp [key e h1]
    · have h2 := key _ h1
      have : e = A.σ (A.σ d) := by rw [← h2, A.σ_σ_σ_σ]
      simp [this]
  have hc := card_le_card hsub
  have hpos : 0 < (univ.filter (fun e => A.curve e = A.curve d)).card :=
    card_pos.2 ⟨d, by simp⟩
  have h2 : ({d, A.σ (A.σ d)} : Finset D).card ≤ 2 := card_le_two
  rw [A.card_darts_on] at hc hpos
  omega

/-- **No loops**: the two ends of a segment are distinct crossings. -/
theorem crossingOf_α_ne (d : D) : A.crossingOf (A.α d) ≠ A.crossingOf d := by
  intro h
  rw [eq_comm, crossingOf_eq_iff] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h
  · exact A.isArrangement.α_ne d h
  · have := A.isArrangement.curve_σ d
    rw [← h, A.isArrangement.curve_α] at this
    exact this rfl
  · exact A.α_ne_σσ d h
  · have := A.isArrangement.curve_σ d
    rw [← A.curve_σσσ d, ← h, A.isArrangement.curve_α] at this
    exact this rfl

/-- Consecutive corners of a cell are distinct. -/
theorem crossingOf_φ_ne (d : D) : A.crossingOf (A.φ d) ≠ A.crossingOf d := by
  rw [crossingOf_φ]; exact A.crossingOf_α_ne d

/-! ## Cells with at most three darts -/

/-- In a cell with at most three darts, a function that differs on consecutive darts is
injective on the darts of the cell. -/
theorem injOn_cell {β : Type*} (g : D → β) (hg : ∀ e, g (A.φ e) ≠ g e) {a : D}
    (hp : period A.φ a ≤ 3) : Set.InjOn g ((A.cellOf a).darts : Set D) := by
  intro b hb c hc h
  rw [mem_coe, mem_darts_cellOf, ← mem_orbitList] at hb hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hc
  rw [List.mem_range] at hi hj
  have hstep : ∀ k, g ((A.φ^[k + 1]) a) ≠ g ((A.φ^[k]) a) := fun k => by
    rw [Function.iterate_succ_apply']; exact hg _
  have hper := iterate_period A.φ a
  have hlt : i < 3 ∧ j < 3 := ⟨by omega, by omega⟩
  have h3 : 2 < period A.φ a → g ((A.φ^[0]) a) ≠ g ((A.φ^[2]) a) := fun h2 => by
    have hp3 : period A.φ a = 3 := by omega
    rw [hp3] at hper
    have := hstep 2
    rw [hper] at this
    exact this
  rcases hlt with ⟨hi3, hj3⟩
  interval_cases i <;> interval_cases j
  · rfl
  · exact absurd h.symm (hstep 0)
  · exact absurd h (h3 (by omega))
  · exact absurd h (hstep 0)
  · rfl
  · exact absurd h.symm (hstep 1)
  · exact absurd h.symm (h3 (by omega))
  · exact absurd h (hstep 1)
  · rfl

/-- In a cell with at most three darts, the darts lie at distinct crossings. -/
theorem injOn_crossingOf {a : D} (hp : period A.φ a ≤ 3) :
    Set.InjOn A.crossingOf ((A.cellOf a).darts : Set D) :=
  A.injOn_cell _ A.crossingOf_φ_ne hp

/-- In a cell with at most three darts, the darts lie on distinct curves. -/
theorem injOn_curve {a : D} (hp : period A.φ a ≤ 3) :
    Set.InjOn A.curve ((A.cellOf a).darts : Set D) :=
  A.injOn_cell _ A.curve_φ_ne hp

/-- In a cell with at most three darts, the reverse of a dart is not in the cell. -/
theorem α_not_mem {a b : D} (hp : period A.φ a ≤ 3) (hb : b ∈ (A.cellOf a).darts) :
    A.α b ∉ (A.cellOf a).darts := by
  intro h
  have hφ : A.φ b ∈ (A.cellOf a).darts :=
    A.mem_darts_cellOf.2 (Perm.sameCycle_apply_right.2 (A.mem_darts_cellOf.1 hb))
  have := A.injOn_crossingOf hp h hφ (A.crossingOf_φ b).symm
  exact A.σ_ne (A.α b) (by rw [← φ_apply, ← this])

/-- In a cell with at most three darts, the cells on the two sides of a dart are distinct. -/
theorem cellOf_α_ne_of_period {d : D} (hp : period A.φ d ≤ 3) :
    A.cellOf (A.α d) ≠ A.cellOf d := fun h =>
  A.α_not_mem hp (A.mem_darts_cellOf_self d) (Orbit.mem_darts.2 h)

/-- In a cell with at most three darts, the darts lie on distinct segments. -/
theorem injOn_segmentOf {a : D} (hp : period A.φ a ≤ 3) :
    Set.InjOn A.segmentOf ((A.cellOf a).darts : Set D) := by
  intro b hb c hc h
  rw [segmentOf_eq_iff] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · exact h.symm
  · exact absurd (h ▸ hc) (A.α_not_mem hp hb)

theorem card_corners_cellOf {a : D} (hp : period A.φ a ≤ 3) :
    (Cell.corners A (A.cellOf a)).card = period A.φ a := by
  rw [Cell.corners, card_image_of_injOn (A.injOn_crossingOf hp), ← Orbit.size, size_cellOf]

theorem card_sides_cellOf {a : D} (hp : period A.φ a ≤ 3) :
    (Cell.sides A (A.cellOf a)).card = period A.φ a := by
  rw [Cell.sides, card_image_of_injOn (A.injOn_segmentOf hp), ← Orbit.size, size_cellOf]

theorem card_curves_cellOf {a : D} (hp : period A.φ a ≤ 3) :
    ((A.cellOf a).darts.image A.curve).card = period A.φ a := by
  rw [card_image_of_injOn (A.injOn_curve hp), ← Orbit.size, size_cellOf]

theorem exists_cellOf (f : A.Cell) : ∃ a, A.cellOf a = f := f.exists_mk

theorem period_of_size {a : D} {k : ℕ} (h : (A.cellOf a).size = k) : period A.φ a = k := by
  rw [← size_cellOf, h]

/-! ## Triangles -/

namespace Triangle

variable {A}

/-- A triangle has three distinct corners. -/
theorem card_corners {f : A.Cell} (hf : A.IsTriangle f) : (Cell.corners A f).card = 3 := by
  obtain ⟨a, rfl⟩ := A.exists_cellOf f
  have hp := A.period_of_size hf
  rw [A.card_corners_cellOf (by omega), hp]

/-- A triangle has three distinct sides. -/
theorem card_sides {f : A.Cell} (hf : A.IsTriangle f) : (Cell.sides A f).card = 3 := by
  obtain ⟨a, rfl⟩ := A.exists_cellOf f
  have hp := A.period_of_size hf
  rw [A.card_sides_cellOf (by omega), hp]

/-- The three sides of a triangle lie on three distinct pseudocircles (a dart of a cell runs
along one of its sides). -/
theorem card_curves {f : A.Cell} (hf : A.IsTriangle f) : (f.darts.image A.curve).card = 3 := by
  obtain ⟨a, rfl⟩ := A.exists_cellOf f
  have hp := A.period_of_size hf
  rw [A.card_curves_cellOf (by omega), hp]

/-- The darts of a triangle lie on distinct pseudocircles. -/
theorem injOn_curve {f : A.Cell} (hf : A.IsTriangle f) : Set.InjOn A.curve (f.darts : Set D) := by
  obtain ⟨a, rfl⟩ := A.exists_cellOf f
  exact A.injOn_curve (by have := A.period_of_size hf; omega)

/-- The darts of a triangle lie at distinct crossings. -/
theorem injOn_crossingOf {f : A.Cell} (hf : A.IsTriangle f) :
    Set.InjOn A.crossingOf (f.darts : Set D) := by
  obtain ⟨a, rfl⟩ := A.exists_cellOf f
  exact A.injOn_crossingOf (by have := A.period_of_size hf; omega)

/-- The two cells at a side of a triangle are distinct. -/
theorem cellOf_α_ne {d : D} (hf : A.IsTriangle (A.cellOf d)) :
    A.cellOf (A.α d) ≠ A.cellOf d :=
  A.cellOf_α_ne_of_period (by have := A.period_of_size hf; omega)

end Triangle

/-! ## Digons -/

namespace Digon

variable {A}

/-- A digon has two distinct corners. -/
theorem card_corners {f : A.Cell} (hf : A.IsDigon f) : (Cell.corners A f).card = 2 := by
  obtain ⟨a, rfl⟩ := A.exists_cellOf f
  have hp := A.period_of_size hf
  rw [A.card_corners_cellOf (by omega), hp]

/-- A digon has two distinct sides. -/
theorem card_sides {f : A.Cell} (hf : A.IsDigon f) : (Cell.sides A f).card = 2 := by
  obtain ⟨a, rfl⟩ := A.exists_cellOf f
  have hp := A.period_of_size hf
  rw [A.card_sides_cellOf (by omega), hp]

/-- The two sides of a digon lie on two distinct pseudocircles. -/
theorem card_curves {f : A.Cell} (hf : A.IsDigon f) : (f.darts.image A.curve).card = 2 := by
  obtain ⟨a, rfl⟩ := A.exists_cellOf f
  have hp := A.period_of_size hf
  rw [A.card_curves_cellOf (by omega), hp]

/-- Both corners of a digon lie on the same two pseudocircles, the curves of its two sides. -/
theorem curves_corner {f : A.Cell} (hf : A.IsDigon f) {x : A.Crossing}
    (hx : x ∈ Cell.corners A f) : Crossing.curves A x = f.darts.image A.curve := by
  obtain ⟨a, rfl⟩ := A.exists_cellOf f
  have hp := A.period_of_size hf
  have hl : orbitList A.φ a = [a, A.φ a] := by simp [orbitList, hp, List.range_succ]
  have hφφ : A.φ (A.φ a) = a := by
    have := iterate_period A.φ a
    rw [hp] at this
    simpa using this
  have hd : (A.cellOf a).darts = {a, A.φ a} := by
    rw [cellOf, Orbit.darts_mk, orbitFinset, hl]; simp
  rw [Cell.corners, hd] at hx
  rw [hd, image_insert, image_singleton]
  simp only [image_insert, image_singleton, mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · conv_lhs => rw [← hφφ]
    rw [curves_crossingOf_φ, hφφ, pair_comm]
  · rw [curves_crossingOf_φ]

/-- The two cells at a side of a digon are distinct. -/
theorem cellOf_α_ne {d : D} (hf : A.IsDigon (A.cellOf d)) :
    A.cellOf (A.α d) ≠ A.cellOf d :=
  A.cellOf_α_ne_of_period (by have := A.period_of_size hf; omega)

end Digon

/-- A segment that is a side of a triangle or a digon lies on two distinct cells. -/
theorem card_segment_cells {s : A.Segment}
    (h : ∃ f ∈ Segment.cells A s, A.IsTriangle f ∨ A.IsDigon f) :
    (Segment.cells A s).card = 2 := by
  obtain ⟨d, rfl⟩ := s.exists_mk
  have hcells : Segment.cells A (Orbit.mk A.α d) = {A.cellOf d, A.cellOf (A.α d)} := by
    rw [Segment.cells, ← segmentOf, darts_segmentOf, image_insert, image_singleton]
  rw [hcells] at h ⊢
  have hne : ∀ e, (A.IsTriangle (A.cellOf e) ∨ A.IsDigon (A.cellOf e)) →
      A.cellOf (A.α e) ≠ A.cellOf e := fun e he =>
    he.elim Triangle.cellOf_α_ne Digon.cellOf_α_ne
  simp only [mem_insert, mem_singleton] at h
  obtain ⟨f, hf | hf, hft⟩ := h
  · subst hf; exact card_pair (hne d hft).symm
  · subst hf
    have := hne (A.α d) hft
    rw [A.isArrangement.α_α] at this
    exact card_pair this

/-! ## Triangles at a crossing -/

/-- A triangle has at most one dart at each crossing, so `t x` (distinct triangles) equals
`tAngles x` (angles in triangles). -/
theorem t_eq_tAngles (x : A.Crossing) : A.t x = A.tAngles x := by
  rw [t, tAngles]
  refine card_image_of_injOn fun a ha b hb h => ?_
  simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
  have hpa := A.period_of_size ha.2
  have hb' : b ∈ (A.cellOf a).darts := Orbit.mem_darts.2 h.symm
  refine A.injOn_crossingOf (by omega) (A.mem_darts_cellOf_self a) hb' ?_
  rw [crossingOf, crossingOf, Orbit.mem_darts.1 ha.1, Orbit.mem_darts.1 hb.1]

/-- `t x` counted via `Cell.corners`. -/
theorem t_eq_tCorners (x : A.Crossing) : A.t x = A.tCorners x := by
  rw [t, tCorners, triangles, filter_filter]
  congr 1
  ext f
  simp only [mem_image, mem_filter, mem_univ, true_and, Cell.corners]
  constructor
  · rintro ⟨d, ⟨hdx, hd⟩, rfl⟩
    exact ⟨hd, d, A.mem_darts_cellOf_self d, Orbit.mem_darts.1 hdx⟩
  · rintro ⟨hf, d, hdf, hdx⟩
    have hc : A.cellOf d = f := Orbit.mem_darts.1 hdf
    exact ⟨d, ⟨Orbit.mem_darts.2 hdx, hc ▸ hf⟩, hc⟩

/-! ## Counting darts in triangles -/

/-- The predicate "the cell of `d` is a triangle". -/
abbrev InTriangle (d : D) : Prop := A.IsTriangle (A.cellOf d)

theorem card_filter_cell (f : A.Cell) (Q : A.Cell → Prop) [DecidablePred Q] :
    (f.darts.filter (fun d => Q (A.cellOf d))).card = if Q f then f.size else 0 := by
  have hf : ∀ d ∈ f.darts, A.cellOf d = f := fun d hd => Orbit.mem_darts.1 hd
  split_ifs with h
  · rw [filter_true_of_mem fun d hd => by rw [hf d hd]; exact h]; rfl
  · rw [filter_false_of_mem fun d hd => by rw [hf d hd]; exact h, card_empty]

/-- The darts in triangles: three per triangle. -/
theorem card_darts_inTriangle : (univ.filter A.InTriangle).card = 3 * A.p 3 := by
  rw [card_filter_eq_sum_orbits A.φ,
    sum_congr rfl fun f _ => A.card_filter_cell f A.IsTriangle, ← sum_filter,
    sum_congr rfl fun f hf => ((mem_filter.1 hf).2 : f.size = 3), sum_const, smul_eq_mul, mul_comm]
  rfl

/-! ## Step 1 of the notes: the excess -/

/-- `3 p_3 = ∑_x t(x)`. -/
theorem three_p3_eq_sum_t : 3 * A.p 3 = ∑ x, A.t x := by
  rw [← card_darts_inTriangle, card_filter_eq_sum_orbits A.σ]
  exact sum_congr rfl fun x _ => (A.t_eq_tAngles x).symm

/-- `e = ∑_x (t(x) - 2)`. -/
theorem excess_eq_sum_t : A.excess = ∑ x, ((A.t x : ℤ) - 2) := by
  have h := A.three_p3_eq_sum_t
  rw [excess, X, sum_sub_distrib, sum_const, card_univ, ← Nat.cast_sum, ← h]
  push_cast
  ring

/-- `e = |X'| - def`, assuming `t(x) ≤ 3` for all crossings (the fan lemma, milestone 4, for
`n ≥ 4`; false for the Krupp arrangement, `n = 3`). -/
theorem excess_eq_X'_sub_deficiency (h : ∀ x, A.t x ≤ 3) :
    A.excess = (A.X'.card : ℤ) - A.deficiency := by
  rw [excess_eq_sum_t, X', deficiency, card_filter, sum_filter]
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  have := h x
  interval_cases (A.t x) <;> simp

/-! ### By segments -/

/-- The number of triangles at a segment equals the number of its darts whose cell is a
triangle (the two cells at a side of a triangle are distinct). -/
theorem card_triangles_at (s : A.Segment) :
    ((Segment.cells A s).filter A.IsTriangle).card = (s.darts.filter A.InTriangle).card := by
  rw [Segment.cells, filter_image]
  refine card_image_of_injOn fun a ha b hb h => ?_
  simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
  have hab : A.segmentOf a = A.segmentOf b := by
    rw [segmentOf, segmentOf, Orbit.mem_darts.1 ha.1, Orbit.mem_darts.1 hb.1]
  rw [segmentOf_eq_iff] at hab
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with hab | hab
  · exact hab.symm
  · exact absurd (hab ▸ h).symm (Triangle.cellOf_α_ne ha.2)

/-- The dart count at a segment: `2` for a diamond, `0` for a trigophobic segment, `1`
otherwise. -/
theorem card_inTriangle_segment (s : A.Segment) :
    (s.darts.filter A.InTriangle).card + (if A.IsTrigophobic s then 1 else 0) =
      1 + (if A.IsDiamond s then 1 else 0) := by
  obtain ⟨d, rfl⟩ := s.exists_mk
  have hne : d ≠ A.α d := (A.isArrangement.α_ne d).symm
  have hd := A.darts_segmentOf d
  simp only [segmentOf] at hd
  simp only [IsDiamond, IsTrigophobic, hd, mem_insert, mem_singleton, forall_eq_or_imp,
    forall_eq]
  by_cases h1 : A.InTriangle d <;> by_cases h2 : A.InTriangle (A.α d) <;>
    simp [filter_insert, filter_singleton, h1, h2, hne]

/-- A segment is a side of at most two triangles. -/
theorem card_triangles_at_le (s : A.Segment) :
    ((Segment.cells A s).filter A.IsTriangle).card ≤ 2 := by
  rw [card_triangles_at]
  have := A.card_inTriangle_segment s
  split_ifs at this <;> omega

theorem card_darts_segment (s : A.Segment) : s.darts.card = 2 := by
  obtain ⟨d, rfl⟩ := s.exists_mk
  have hd := A.darts_segmentOf d
  simp only [segmentOf] at hd
  rw [hd, card_pair (A.isArrangement.α_ne d).symm]

/-- A diamond segment is a side of two triangles. -/
theorem isDiamond_iff (s : A.Segment) :
    A.IsDiamond s ↔ ((Segment.cells A s).filter A.IsTriangle).card = 2 := by
  rw [card_triangles_at, ← A.card_darts_segment s, card_filter_eq_iff]
  rfl

/-- A trigophobic segment is a side of no triangle. -/
theorem isTrigophobic_iff (s : A.Segment) :
    A.IsTrigophobic s ↔ ((Segment.cells A s).filter A.IsTriangle).card = 0 := by
  rw [card_triangles_at, card_eq_zero, filter_eq_empty_iff]
  rfl

/-- Summing the number of triangles over all segments counts every triangle three times. -/
theorem sum_triangles_at : ∑ s : A.Segment, ((Segment.cells A s).filter A.IsTriangle).card =
    3 * A.p 3 := by
  rw [← card_darts_inTriangle, card_filter_eq_sum_orbits A.α]
  exact sum_congr rfl fun s _ => A.card_triangles_at s

/-- `e = δ - φ` (diamond segments minus trigophobic segments). -/
theorem excess_eq_diamond_sub_trigophobic :
    A.excess = (A.numDiamond : ℤ) - A.numTrigophobic := by
  have h := sum_congr rfl fun s (_ : s ∈ (univ : Finset A.Segment)) =>
    A.card_inTriangle_segment s
  have e1 : A.numDiamond = ∑ s, if A.IsDiamond s then 1 else 0 := card_filter _ _
  have e2 : A.numTrigophobic = ∑ s, if A.IsTrigophobic s then 1 else 0 := card_filter _ _
  rw [sum_add_distrib, sum_add_distrib, ← e1, ← e2,
    ← card_filter_eq_sum_orbits A.α, card_darts_inTriangle, sum_const, card_univ,
    card_segments, smul_eq_mul, mul_one] at h
  rw [excess]
  omega

/-! ### By pseudocircles -/

/-- `t_C` is the number of darts on `C` in triangles (a triangle has its three sides on three
distinct pseudocircles, so at most one dart on `C`). -/
theorem tC_eq_card_darts (C : Fin n) :
    A.tC C = (univ.filter (fun d => A.curve d = C ∧ A.InTriangle d)).card := by
  rw [card_filter_eq_sum_orbits A.φ, tC, triangles, filter_filter, card_filter]
  refine sum_congr rfl fun f _ => ?_
  symm
  have hf : ∀ d ∈ f.darts, A.cellOf d = f := fun d hd => Orbit.mem_darts.1 hd
  by_cases ht : A.IsTriangle f
  · rw [filter_congr (q := fun d => A.curve d = C) fun d hd => by simp [InTriangle, hf d hd, ht]]
    by_cases hC : ∃ d ∈ f.darts, A.curve d = C
    · rw [if_pos ⟨ht, hC⟩]
      obtain ⟨d, hd, hdC⟩ := hC
      refine le_antisymm (card_le_one.2 fun a ha b hb => ?_) (card_pos.2 ⟨d, by simp [hd, hdC]⟩)
      simp only [mem_filter] at ha hb
      exact Triangle.injOn_curve ht ha.1 hb.1 (ha.2.trans hb.2.symm)
    · rw [if_neg fun h => hC h.2, card_eq_zero, filter_eq_empty_iff]
      exact fun d hd hdC => hC ⟨d, hd, hdC⟩
  · rw [if_neg fun h => ht h.1, card_eq_zero, filter_eq_empty_iff]
    intro d hd h
    exact ht (hf d hd ▸ h.2)

/-- `∑_C t_C = 3 p_3`. -/
theorem sum_tC : ∑ C : Fin n, A.tC C = 3 * A.p 3 := by
  rw [← card_darts_inTriangle,
    card_eq_sum_card_fiberwise (f := A.curve) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun C _ => ?_
  rw [tC_eq_card_darts, filter_filter]
  congr 1
  ext d
  simp [and_comm]

/-- `∑_{x on C} t(x) = 2 t_C`: a triangle with a side on `C` has exactly two corners on `C`. -/
theorem sum_t_crossingsOn (C : Fin n) : ∑ x ∈ A.crossingsOn C, A.t x = 2 * A.tC C := by
  have ht : ∀ x, A.t x = (x.darts.filter A.InTriangle).card := A.t_eq_tAngles
  rw [sum_congr rfl fun x _ => ht x, sum_card_filter_orbits]
  have hiff : ∀ d, (Orbit.mk A.σ d ∈ A.crossingsOn C ∧ A.InTriangle d) ↔
      ((A.curve d = C ∧ A.InTriangle d) ∨ (A.curve (A.σ d) = C ∧ A.InTriangle d)) := by
    intro d
    simp only [crossingsOn, mem_filter, mem_univ, true_and]
    rw [← crossingOf, curves_crossingOf, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h | h, ht⟩
      · exact Or.inl ⟨h.symm, ht⟩
      · exact Or.inr ⟨h.symm, ht⟩
    · rintro (⟨h, ht⟩ | ⟨h, ht⟩)
      · exact ⟨Or.inl h.symm, ht⟩
      · exact ⟨Or.inr h.symm, ht⟩
  rw [filter_congr fun d _ => hiff d, filter_or, card_union_of_disjoint]
  · -- the second set is the image of the first under `φ`
    have h2 : (univ.filter (fun d => A.curve (A.σ d) = C ∧ A.InTriangle d)).card =
        (univ.filter (fun d => A.curve d = C ∧ A.InTriangle d)).card := by
      refine card_nbij' A.φ.symm A.φ ?_ ?_ ?_ ?_
      · intro d hd
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hd ⊢
        refine ⟨?_, ?_⟩
        · rw [← A.curve_σ_φ, Equiv.apply_symm_apply]; exact hd.1
        · rw [InTriangle, ← A.cellOf_φ, Equiv.apply_symm_apply]; exact hd.2
      · intro d hd
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hd ⊢
        exact ⟨by rw [A.curve_σ_φ]; exact hd.1, by rw [InTriangle, A.cellOf_φ]; exact hd.2⟩
      · intro d _; simp
      · intro d _; simp
    rw [h2, tC_eq_card_darts]
    ring
  · rw [disjoint_filter]
    rintro d - ⟨h1, -⟩ ⟨h2, -⟩
    exact A.isArrangement.curve_σ d (h2.trans h1.symm)

/-- Per pseudocircle: `t_C - 2(n-1) = δ_C - φ_C`. -/
theorem tC_sub_eq (C : Fin n) :
    (A.tC C : ℤ) - 2 * (n - 1 : ℕ) = (A.numDiamondOn C : ℤ) - A.numTrigophobicOn C := by
  have h := sum_congr rfl fun s (_ : s ∈ A.segmentsOn C) => A.card_inTriangle_segment s
  have e1 : A.numDiamondOn C = ∑ s ∈ A.segmentsOn C, if A.IsDiamond s then 1 else 0 :=
    card_filter _ _
  have e2 : A.numTrigophobicOn C = ∑ s ∈ A.segmentsOn C, if A.IsTrigophobic s then 1 else 0 :=
    card_filter _ _
  rw [sum_add_distrib, sum_add_distrib, ← e1, ← e2,
    sum_card_filter_orbits, sum_const, card_segmentsOn, smul_eq_mul, mul_one] at h
  have hC : (univ.filter (fun d => Orbit.mk A.α d ∈ A.segmentsOn C ∧ A.InTriangle d)) =
      univ.filter (fun d => A.curve d = C ∧ A.InTriangle d) := by
    refine filter_congr fun d _ => ?_
    simp only [segmentsOn, mem_filter, mem_univ, true_and]
    rw [← segmentOf, curves_segmentOf, mem_singleton, eq_comm]
  rw [hC, ← tC_eq_card_darts] at h
  omega

/-- `e = ∑_C (t_C - 2(n-1))`. -/
theorem excess_eq_sum_tC : A.excess = ∑ C : Fin n, ((A.tC C : ℤ) - 2 * (n - 1 : ℕ)) := by
  rw [sum_sub_distrib, ← Nat.cast_sum, sum_tC, sum_const, card_univ, Fintype.card_fin, excess,
    card_X]
  push_cast
  ring

/-- `e = ∑_C (δ_C - φ_C)`. -/
theorem excess_eq_sum_diamondOn :
    A.excess = ∑ C : Fin n, ((A.numDiamondOn C : ℤ) - A.numTrigophobicOn C) := by
  rw [excess_eq_sum_tC]
  exact sum_congr rfl fun C _ => A.tC_sub_eq C

/-! ### Modulo 3 -/

/-- `e ≡ n(n-1) (mod 3)`. -/
theorem excess_modEq : A.excess ≡ ((n * (n - 1) : ℕ) : ℤ) [ZMOD 3] := by
  rw [excess, card_X, Int.modEq_iff_dvd]
  exact ⟨((n * (n - 1) : ℕ) : ℤ) - A.p 3, by ring⟩

/-- `e ≡ n(n-1) (mod 3)`, as remainders. -/
theorem excess_emod_three : A.excess % 3 = ((n * (n - 1) : ℕ) : ℤ) % 3 := A.excess_modEq

end Arrangement

end Pca
