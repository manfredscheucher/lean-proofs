/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): consequences of `C`, `C'` being parallel (for `Mimic.lean`)

With the digon `D ⊂ ext C ∩ int C'` (sides on `C` and `C'`):

* `par_corner` (FROS: `ext C ∩ int C'` is the digon): a cell outside `C` and inside `C'` is the
  digon, so its corners are on `C` and on `C'`.
* `par_inside_C`: a crossing of `C'` (not on `C`) lies inside `C` (`C' ∩ ext C` is the side of the
  digon).
* `par_outside_C'`: a crossing of `C` (not on `C'`) lies outside `C'`.
* `walk_between`: walking along a curve `c` from a segment whose two ends are crossings with `e`,
  the rest of `c` is on the other side of `e` (the two crossings of `c` with `e` are the ends of
  this segment).
-/
import Pca.FlipGraph.Lens
import Pca.FlipGraph.Delete

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement

/-- `C` and `C'` are **parallel** with the digon `D ⊂ ext C ∩ int C'` (FROS). -/
def Marked.Par (M : Marked n D) (C C' : Fin n) : Prop :=
  C ≠ C' ∧
    (∃ a, M.A.IsDigon (M.A.cellOf a) ∧ M.A.curve a = C ∧ M.A.curve (M.A.φ a) = C' ∧
      ¬ M.Inside C (M.A.cellOf a) ∧ M.Inside C' (M.A.cellOf a)) ∧
    ∀ x : M.A.Crossing, C ∉ Arrangement.Crossing.curves M.A x → C' ∉ Arrangement.Crossing.curves M.A x →
      ¬ (M.CrossInside C x ∧ ¬ M.CrossInside C' x)


/-- The corners of a digon are crossings of its two curves. -/
theorem digon_corner (A : Arrangement n D) {a : D} (hD : A.IsDigon (A.cellOf a)) {v : D}
    (hv : A.cellOf v = A.cellOf a) :
    A.curve a ∈ Crossing.curves A (A.crossingOf v) ∧
      A.curve (A.φ a) ∈ Crossing.curves A (A.crossingOf v) := by
  have hφφ : A.φ (A.φ a) = a := A.φ_φ_of_digon hD
  have hs : A.φ.SameCycle a v := A.mem_darts_cellOf.1 (hv ▸ A.mem_darts_cellOf_self v)
  rcases two_cycle hφφ hs with rfl | rfl
  · refine ⟨A.mem_curves_crossingOf _, ?_⟩
    have h := A.mem_curves_end (A.φ v)
    rwa [← A.crossingOf_σ, ← A.φ_apply, hφφ] at h
  · refine ⟨?_, A.mem_curves_crossingOf _⟩
    have h := A.mem_curves_end a
    rwa [← A.crossingOf_σ, ← A.φ_apply] at h

/-- A dart at the crossing of `v` on a curve `E` of that crossing. -/
theorem _root_.Pca.Arrangement.exists_dart_on_crossing (A : Arrangement n D) {v : D} {E : Fin n}
    (h : E ∈ Crossing.curves A (A.crossingOf v)) :
    ∃ t, A.crossingOf t = A.crossingOf v ∧ A.curve t = E := by
  rw [A.curves_crossingOf, mem_insert, mem_singleton] at h
  rcases h with h | h
  · exact ⟨v, rfl, h.symm⟩
  · exact ⟨A.σ v, A.crossingOf_σ v, h.symm⟩

namespace Marked

variable (M : Marked n D)

/-- The two cells at a crossing on both sides of a dart `t` of `E` (`cellOf t`, `cellOf (σ t)`)
are on different sides of `E`. -/
theorem inside_σ_of_curve {E : Fin n} {t : D} (ht : M.A.curve t = E) :
    M.Inside E (M.A.cellOf (M.A.σ t)) ↔ ¬ M.Inside E (M.A.cellOf t) := by
  rw [M.A.cellOf_σ, M.inside_α E t]; simp [ht]

/-- The cells at a crossing not on `E` all have the interior status of `E` of one of them. -/
theorem inside_at_crossing {E : Fin n} {v t : D} (hx : E ∉ Crossing.curves M.A (M.A.crossingOf v))
    (ht : M.A.crossingOf t = M.A.crossingOf v) :
    M.Inside E (M.A.cellOf t) ↔ M.Inside E (M.A.cellOf v) := by
  rw [← M.crossInside_iff hx, ← ht, M.crossInside_iff (by rw [ht]; exact hx)]

/-- **`ext C ∩ int C'` is the digon**: a cell outside `C` and inside `C'` is the digon of `Par`,
so its corners are crossings of `C` and `C'`. -/
theorem par_corner {C C' : Fin n} (hpar : M.Par C C') {w : D} (h1 : ¬ M.Inside C (M.A.cellOf w))
    (h2 : M.Inside C' (M.A.cellOf w)) :
    C ∈ Crossing.curves M.A (M.A.crossingOf w) ∧ C' ∈ Crossing.curves M.A (M.A.crossingOf w) := by
  obtain ⟨-, ⟨a, hD, rfl, rfl, hout, hin⟩, -⟩ := hpar
  obtain ⟨s, hs⟩ := M.A.exists_isSide (M.A.curve a)
  obtain ⟨s', hs'⟩ := M.A.exists_isSide (M.A.curve (M.A.φ a))
  have key : ∀ u v t : ZMod 2, u ≠ t → v ≠ t → u = v := by decide
  have key2 : ∀ u t : ZMod 2, ¬ u ≠ t → u = t := fun u t h => not_not.1 h
  have hf : s (M.A.cellOf w) = s (M.A.cellOf a) := by
    rw [key2 (s (M.A.cellOf w)) (s M.z) (by rw [← M.inside_iff hs]; exact h1),
      key2 (s (M.A.cellOf a)) (s M.z) (by rw [← M.inside_iff hs]; exact hout)]
  have hf' : s' (M.A.cellOf w) = s' (M.A.cellOf a) :=
    key _ _ _ ((M.inside_iff hs' _).1 h2) ((M.inside_iff hs' _).1 hin)
  exact digon_corner M.A hD (digon_region hD hs hs' hf hf')

/-- **Crossings of `C'` are inside `C`** (if not on `C`). -/
theorem par_inside_C {C C' : Fin n} (hpar : M.Par C C') {v : D}
    (h1 : C' ∈ Crossing.curves M.A (M.A.crossingOf v)) (h2 : C ∉ Crossing.curves M.A (M.A.crossingOf v)) :
    M.Inside C (M.A.cellOf v) := by
  by_contra hv
  obtain ⟨t, htv, htC⟩ := M.A.exists_dart_on_crossing h1
  have hσ : M.A.crossingOf (M.A.σ t) = M.A.crossingOf v := (M.A.crossingOf_σ t).trans htv
  have ht : ¬ M.Inside C (M.A.cellOf t) := by rw [M.inside_at_crossing h2 htv]; exact hv
  have ht' : ¬ M.Inside C (M.A.cellOf (M.A.σ t)) := by rw [M.inside_at_crossing h2 hσ]; exact hv
  by_cases hin : M.Inside C' (M.A.cellOf t)
  · exact h2 (htv ▸ (M.par_corner hpar ht hin).1)
  · have := (M.par_corner hpar ht' ((M.inside_σ_of_curve htC).2 hin)).1
    exact h2 (hσ ▸ this)

/-- **Crossings of `C` are outside `C'`** (if not on `C'`). -/
theorem par_outside_C' {C C' : Fin n} (hpar : M.Par C C') {v : D}
    (h1 : C ∈ Crossing.curves M.A (M.A.crossingOf v)) (h2 : C' ∉ Crossing.curves M.A (M.A.crossingOf v)) :
    ¬ M.Inside C' (M.A.cellOf v) := by
  intro hv
  obtain ⟨t, htv, htC⟩ := M.A.exists_dart_on_crossing h1
  have hσ : M.A.crossingOf (M.A.σ t) = M.A.crossingOf v := (M.A.crossingOf_σ t).trans htv
  have ht : M.Inside C' (M.A.cellOf t) := by rw [M.inside_at_crossing h2 htv]; exact hv
  have ht' : M.Inside C' (M.A.cellOf (M.A.σ t)) := by rw [M.inside_at_crossing h2 hσ]; exact hv
  by_cases hin : M.Inside C (M.A.cellOf t)
  · exact h2 (hσ ▸ (M.par_corner hpar (by rw [M.inside_σ_of_curve htC]; exact not_not.2 hin) ht').2)
  · exact h2 (htv ▸ (M.par_corner hpar hin ht).2)

/-- End form of `par_inside_C`: a segment of `c ≠ C` ending at a crossing with `C'` (not on `C`)
is inside `C`. -/
theorem par_inside_C_end {C C' : Fin n} (hpar : M.Par C C') {u : D} (hu : M.A.curve u ≠ C)
    (h1 : C' ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α u)))
    (h2 : C ∉ Crossing.curves M.A (M.A.crossingOf (M.A.α u))) :
    M.Inside C (M.A.cellOf u) := by
  have := M.par_inside_C hpar h1 h2
  rw [M.inside_α C u] at this; simpa [hu] using this

/-- End form of `par_outside_C'`. -/
theorem par_outside_C'_end {C C' : Fin n} (hpar : M.Par C C') {u : D} (hu : M.A.curve u ≠ C')
    (h1 : C ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α u)))
    (h2 : C' ∉ Crossing.curves M.A (M.A.crossingOf (M.A.α u))) :
    ¬ M.Inside C' (M.A.cellOf u) := by
  have := M.par_outside_C' hpar h1 h2
  rw [M.inside_α C' u] at this; simpa [hu] using this

/-- **Walking along `c` from a segment with both ends on `e`**: the walk meets `e` exactly at the
two ends of the segment (positions `0` and `period - 1`). -/
theorem walk_flips {e : Fin n} {y : D} (hy : M.A.curve y ≠ e)
    (hs : e ∈ Crossing.curves M.A (M.A.crossingOf y))
    (he : e ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α y))) :
    2 ≤ period M.A.straight y ∧ Walk.flipsOn M.A e y = {0, period M.A.straight y - 1} := by
  have hc := Walk.card_flipsOn M.A hy
  have hp0 := period_pos M.A.straight y
  have h0 : M.A.curve (M.A.σ (M.A.α y)) = e := (M.A.mem_curves_end_iff hy).1 he
  have hp1 : (M.A.straight ^ (period M.A.straight y - 1)) y = M.A.α (M.A.σ (M.A.σ y)) := by
    rw [← M.A.straight_symm_apply]
    apply (Equiv.eq_symm_apply _).2
    have := Walk.pow_period_apply M.A y
    rwa [show period M.A.straight y = period M.A.straight y - 1 + 1 by omega, pow_succ',
      Perm.mul_apply] at this
  have h1 : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ (period M.A.straight y - 1)) y))) = e := by
    rw [hp1, M.A.α_α, M.A.curve_σσσ]
    rw [M.A.curves_crossingOf, mem_insert, mem_singleton] at hs
    rcases hs with h | h
    · exact absurd h.symm hy
    · exact h.symm
  have hp : 2 ≤ period M.A.straight y := by
    by_contra h
    have : (Walk.flipsOn M.A e y).card ≤ 1 := by
      unfold Walk.flipsOn
      refine (card_filter_le _ _).trans ?_
      rw [card_range]; omega
    omega
  refine ⟨hp, (eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro i hi
    rw [mem_insert, mem_singleton] at hi
    rw [Walk.mem_flipsOn]
    rcases hi with rfl | rfl
    · exact ⟨hp0, by rw [pow_zero]; exact h0⟩
    · exact ⟨by omega, h1⟩
  · rw [hc, card_pair (by omega)]

/-- With `walk_flips`: all segments of `c` other than the one of `y` are on the other side of
`e`. -/
theorem walk_status {e : Fin n} {y : D} (hy : M.A.curve y ≠ e)
    (hs : e ∈ Crossing.curves M.A (M.A.crossingOf y))
    (he : e ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α y))) :
    ∀ i, 1 ≤ i → i < period M.A.straight y →
      (M.Inside e (M.A.cellOf ((M.A.straight ^ i) y)) ↔ ¬ M.Inside e (M.A.cellOf y)) := by
  obtain ⟨hp, hf⟩ := M.walk_flips hy hs he
  intro i hi hip
  induction i, hi using Nat.le_induction with
  | base =>
    rw [pow_one, M.inside_straight, (M.A.mem_curves_end_iff hy).1 he]; simp
  | succ i hi ih =>
    have hni : i ∉ Walk.flipsOn M.A e y := by
      rw [hf, mem_insert, mem_singleton]; omega
    rw [Walk.mem_flipsOn] at hni
    have hne : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y))) ≠ e :=
      fun h => hni ⟨by omega, h⟩
    rw [pow_succ', Perm.mul_apply, M.inside_straight, ih (by omega)]
    simp [hne]

/-- **A segment of `c ∉ {C, C'}` between two consecutive crossings with `C'` is outside `C'`**
(otherwise the rest of `c` is inside `C'`, also at the crossings of `c` with `C`). -/
theorem par_two_C' {C C' : Fin n} (hpar : M.Par C C') {y : D} (hyC : M.A.curve y ≠ C)
    (hyC' : M.A.curve y ≠ C') (h0 : M.A.curve (M.A.σ (M.A.α y)) = C')
    (h1 : M.A.curve (M.A.σ (M.A.α (M.A.straight y))) = C') :
    ¬ M.Inside C' (M.A.cellOf y) := by
  intro hin
  have hc := Walk.card_flipsOn M.A hyC'
  have hp : 2 ≤ period M.A.straight y := by
    by_contra h
    have : (Walk.flipsOn M.A C' y).card ≤ 1 := by
      unfold Walk.flipsOn; refine (card_filter_le _ _).trans ?_; rw [card_range]; omega
    omega
  have hf : Walk.flipsOn M.A C' y = {0, 1} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro i hi
      rw [mem_insert, mem_singleton] at hi
      rw [Walk.mem_flipsOn]
      rcases hi with rfl | rfl
      · exact ⟨by omega, by rw [pow_zero]; exact h0⟩
      · exact ⟨by omega, by rw [pow_one]; exact h1⟩
    · rw [hc, card_pair (by omega)]
  have hcC := Walk.card_flipsOn M.A hyC
  obtain ⟨j, hj⟩ := card_pos.1 (by omega : 0 < (Walk.flipsOn M.A C y).card)
  rw [Walk.mem_flipsOn] at hj
  have hj2 : 2 ≤ j := by
    by_contra h
    interval_cases j
    · rw [pow_zero, Perm.one_apply, h0] at hj; exact hpar.1 hj.2.symm
    · rw [pow_one, h1] at hj; exact hpar.1 hj.2.symm
  have hst : ∀ i, 2 ≤ i → i < period M.A.straight y →
      M.Inside C' (M.A.cellOf ((M.A.straight ^ i) y)) := by
    intro i hi hip
    induction i, hi using Nat.le_induction with
    | base =>
      rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ', Perm.mul_apply, pow_one, M.inside_straight,
        M.inside_straight, h0, h1]
      simp [hin]
    | succ i hi ih =>
      have hni : i ∉ Walk.flipsOn M.A C' y := by rw [hf, mem_insert, mem_singleton]; omega
      rw [Walk.mem_flipsOn] at hni
      have hne : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) y))) ≠ C' :=
        fun h => hni ⟨by omega, h⟩
      rw [pow_succ', Perm.mul_apply, M.inside_straight]
      simp [hne, ih (by omega)]
  have hcu : M.A.curve ((M.A.straight ^ j) y) = M.A.curve y := Walk.curve_pow M.A y j
  refine M.par_outside_C'_end hpar (by rw [hcu]; exact hyC') ?_ ?_ (hst j hj2 hj.1)
  · rw [M.A.mem_curves_end_iff (by rw [hcu]; exact hyC)]; exact hj.2
  · rw [M.A.mem_curves_end_iff (by rw [hcu]; exact hyC'), hj.2]; exact hpar.1

end Marked

/-- **A side of `M − C'` on a curve `≠ C` whose two ends are not on `C` is not crossed by `C'`**
(`α` of the deletion is `α` of `M`): a crossing with `C'` on it would put the side inside `C`, so
its ends inside `C'` (`Par`), and then `C'` would cross it once (end outside `C'`) or twice
(`par_two_C'`). -/
theorem par_no_cross {m : ℕ} {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} (hK : ∀ d, K d ↔ Keep M.A C' d) (hpar : M.Par C C') (b : {d // K d})
    (hbC : M.A.curve b.val ≠ C) (hs : C ∉ Crossing.curves M.A (M.A.crossingOf b.val))
    (he : C ∉ Crossing.curves M.A (M.A.crossingOf ((M.A.deleteOn C' hm K hK).α b).val)) :
    ((M.A.deleteOn C' hm K hK).α b).val = M.A.α b.val := by
  obtain ⟨k, hlt, hk, heq⟩ := deleteOn_α M.A C' hm K hK b
  have hb := (hK _).1 b.2
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [heq, pow_zero, Perm.one_apply]
  exfalso
  have h0 := hlt 0 hk0
  rw [pow_zero, Perm.one_apply] at h0
  have h0' : M.A.curve (M.A.σ (M.A.α b.val)) = C' := (M.A.mem_curves_end_iff hb.1).1 h0
  have hX0 : C ∉ Crossing.curves M.A (M.A.crossingOf (M.A.α b.val)) := by
    rw [M.A.curves_crossingOf, M.A.curve_α, h0']
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hbC, hpar.1⟩
  have hinC := M.par_inside_C_end hpar hbC h0 hX0
  have hinC' : M.Inside C' (M.A.cellOf b.val) := by
    by_contra h
    exact hpar.2.2 _ hs hb.2 (by rw [M.crossInside_iff hs, M.crossInside_iff hb.2]; exact ⟨hinC, h⟩)
  have hcs : M.A.curve (M.A.straight b.val) = M.A.curve b.val := by
    simpa using Walk.curve_pow M.A b.val 1
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · obtain rfl : k = 1 := by omega
    rw [heq, pow_one] at he
    rw [pow_one] at hk
    apply hpar.2.2 _ he hk
    rw [M.crossInside_iff he, M.crossInside_iff hk, M.inside_α, M.inside_α, M.inside_straight,
      M.inside_straight, h0']
    simp [hinC, hinC', hcs, hbC, hb.1, Ne.symm hpar.1]
  · have h1 := hlt 1 (by omega)
    rw [pow_one] at h1
    have h1' : M.A.curve (M.A.σ (M.A.α (M.A.straight b.val))) = C' :=
      (M.A.mem_curves_end_iff (by rw [hcs]; exact hb.1)).1 h1
    exact M.par_two_C' hpar hbC hb.1 h0' h1' hinC'


/-- The curve of `σ b` is the curve of the side before `b` in its cell. -/
theorem _root_.Pca.Arrangement.curve_φ_symm (A : Arrangement n D) (b : D) :
    A.curve (A.φ.symm b) = A.curve (A.σ b) := by
  have h1 : A.σ (A.α (A.φ.symm b)) = b := by rw [← A.φ_apply]; exact A.φ.apply_symm_apply b
  have h2 : A.α (A.φ.symm b) = A.σ (A.σ (A.σ b)) := by
    apply A.σ.injective; rw [h1, A.σ_σ_σ_σ]
  rw [← A.curve_α, h2, A.curve_σσσ]

/-- **First case of the mimicking**: a cell of `M − C'` without a side on `C` has no corner on
`C`, and its sides are not crossed by `C'` (`par_no_cross`). -/
theorem noC_no_cross {m : ℕ} {C C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {M : Marked (m + 1) D} (hK : ∀ d, K d ↔ Keep M.A C' d) (hpar : M.Par C C') {d : {d // K d}}
    (hC : ∀ b, (M.A.deleteOn C' hm K hK).cellOf b = (M.A.deleteOn C' hm K hK).cellOf d →
      M.A.curve b.val ≠ C) (b : {d // K d})
    (hb : (M.A.deleteOn C' hm K hK).cellOf b = (M.A.deleteOn C' hm K hK).cellOf d) :
    C ∉ Crossing.curves M.A (M.A.crossingOf b.val) ∧
      ((M.A.deleteOn C' hm K hK).α b).val = M.A.α b.val := by
  set δ := M.A.deleteOn C' hm K hK
  have hs : ∀ b, δ.cellOf b = δ.cellOf d → C ∉ Crossing.curves M.A (M.A.crossingOf b.val) := by
    intro b hb
    have hx : δ.cellOf (δ.φ.symm b) = δ.cellOf d := by
      rw [← hb, ← δ.cellOf_φ, δ.φ.apply_symm_apply]
    have h1 : M.A.curve (M.A.σ b.val) ≠ C := by
      rw [show M.A.σ b.val = (δ.σ b).val from rfl, ← deleteOn_curve M.A C' hm K hK (δ.σ b),
        ← δ.curve_φ_symm, deleteOn_curve]
      exact hC _ hx
    rw [M.A.curves_crossingOf]; simp only [mem_insert, mem_singleton, not_or]
    exact ⟨Ne.symm (hC b hb), Ne.symm h1⟩
  refine ⟨hs b hb, par_no_cross hK hpar b (hC b hb) (hs b hb) ?_⟩
  have hφ : δ.cellOf (δ.φ b) = δ.cellOf d := by rw [δ.cellOf_φ, hb]
  have := hs _ hφ
  rwa [show (δ.φ b).val = M.A.σ (δ.α b).val from rfl, M.A.crossingOf_σ] at this

/-- A triangle of `M − C'` whose sides are not crossed by `C'` is a triangle of `M` with the same
darts (all kept). -/
theorem tri_of_del {m : ℕ} {C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop} [DecidablePred K]
    {A : Arrangement (m + 1) D} (hK : ∀ d, K d ↔ Keep A C' d) {d : {d // K d}}
    (hT : (A.deleteOn C' hm K hK).IsTriangle ((A.deleteOn C' hm K hK).cellOf d))
    (hα : ∀ b, (A.deleteOn C' hm K hK).cellOf b = (A.deleteOn C' hm K hK).cellOf d →
      ((A.deleteOn C' hm K hK).α b).val = A.α b.val) :
    A.IsTriangle (A.cellOf d.val) ∧ ∀ y, A.cellOf y = A.cellOf d.val → K y := by
  set δ := A.deleteOn C' hm K hK
  have hφ : ∀ b, δ.cellOf b = δ.cellOf d → (δ.φ b).val = A.φ b.val := fun b hb => by
    show A.σ (δ.α b).val = A.σ (A.α b.val); rw [hα b hb]
  have c1 : δ.cellOf (δ.φ d) = δ.cellOf d := δ.cellOf_φ d
  have c2 : δ.cellOf (δ.φ (δ.φ d)) = δ.cellOf d := by rw [δ.cellOf_φ, δ.cellOf_φ]
  have e1 := hφ d rfl
  have e2 := hφ _ c1
  have e3 := hφ _ c2
  have h3 : δ.φ (δ.φ (δ.φ d)) = d := Arrangement.tri_φφφ hT
  have hA3 : A.φ (A.φ (A.φ d.val)) = d.val := by rw [← e1, ← e2, ← e3, h3]
  have horb : orbitFinset A.φ d.val = {d.val, (δ.φ d).val, (δ.φ (δ.φ d)).val} := by
    rw [orbitFinset_three hA3, ← e1, ← e2]
  obtain ⟨n1, n2, n3⟩ := Arrangement.tri_darts_ne hT
  refine ⟨?_, fun y hy => ?_⟩
  · show (orbitFinset A.φ d.val).card = 3
    rw [horb]
    exact card_eq_three.2 ⟨_, _, _, fun h => n1 (Subtype.ext h), fun h => n2 (Subtype.ext h),
      fun h => n3 (Subtype.ext h), rfl⟩
  · have : y ∈ orbitFinset A.φ d.val :=
      mem_orbitFinset.2 (A.mem_darts_cellOf.1 (hy ▸ A.mem_darts_cellOf_self y))
    rw [horb, mem_insert, mem_insert, mem_singleton] at this
    rcases this with rfl | rfl | rfl
    · exact d.2
    · exact (δ.φ d).2
    · exact (δ.φ (δ.φ d)).2

end Pca.FlipGraph
