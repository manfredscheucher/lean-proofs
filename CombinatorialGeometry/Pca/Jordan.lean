/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# A combinatorial Jordan curve theorem for the pseudocircles

For every pseudocircle `C` of an arrangement there is a **side function** `s : Cell → ZMod 2`
that changes exactly across the segments of `C`: for every dart `y`,
`s (cellOf y) + s (cellOf (α y)) = [curve y = C]` (`exists_side`).

Proof (linear algebra over `𝔽₂`, using Euler and connectivity): consider the boundary maps
`L : 𝔽₂^cells → 𝔽₂^segments` (a segment gets the sum over its two sides) and
`B : 𝔽₂^segments → 𝔽₂^crossings` (a crossing gets the sum over its four darts). Then
`B ∘ L = 0`, `ker L` consists of the constants (connectivity), and `range B` contains all vectors
with sum `0` (connectivity), so `dim range L ≥ #cells - 1 = #segments - #crossings + 1 ≥ dim ker B`
by Euler. Hence `range L = ker B`. The indicator of the segments of `C` lies in `ker B` (a crossing
has `0` or `2` darts on `C`), so it is `L s` for some `s`.

Consequences (genus-0 facts used for the flip, `Pca/Flip.lean`):

* `Arrangement.cellOf_α_ne'`: the two cells at any segment are distinct (no "bridges"),
* `Arrangement.cellOf_σσ_ne`: opposite cells at a crossing are distinct,
* `Arrangement.side_σσ`: the side changes around a crossing as expected.
-/
import Pca.Digon
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod

open Equiv Finset Module

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide

theorem zmod2_eq_add_of_add_eq {a b c : ZMod 2} (h : a + b = c) : b = a + c := by
  subst h; rw [← add_assoc, zmod2_add_self, zero_add]

theorem zmod2_trans (p q r : ZMod 2) : p + r = p + q + (q + r) := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;> decide

theorem zmod2_cycle (a b c e : ZMod 2) : a + b + (b + c) + (c + e) + (e + a) = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;> decide

/-! ## The boundary maps -/

/-- `L`: a function on cells gives on each segment the sum over the two cells at it. -/
def cellBdry : (A.Cell → ZMod 2) →ₗ[ZMod 2] (A.Segment → ZMod 2) where
  toFun g s := ∑ y ∈ s.darts, g (A.cellOf y)
  map_add' g h := by funext s; simp [sum_add_distrib]
  map_smul' c g := by funext s; simp [mul_sum]

/-- `B`: a function on segments gives on each crossing the sum over its four darts. -/
def segBdry : (A.Segment → ZMod 2) →ₗ[ZMod 2] (A.Crossing → ZMod 2) where
  toFun h x := ∑ y ∈ x.darts, h (A.segmentOf y)
  map_add' g h := by funext s; simp [sum_add_distrib]
  map_smul' c g := by funext s; simp [mul_sum]

/-- The sum of all entries. -/
def sumAll : (A.Crossing → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ x, v x
  map_add' v w := by simp [sum_add_distrib]
  map_smul' c v := by simp [mul_sum]

theorem cellBdry_segmentOf (g : A.Cell → ZMod 2) (y : D) :
    A.cellBdry g (A.segmentOf y) = g (A.cellOf y) + g (A.cellOf (A.α y)) := by
  show ∑ z ∈ (A.segmentOf y).darts, g (A.cellOf z) = _
  rw [darts_segmentOf, sum_pair (A.isArrangement.α_ne y).symm]

theorem sum_darts_crossingOf {M : Type*} [AddCommMonoid M] (F : D → M) (y : D) :
    ∑ z ∈ (A.crossingOf y).darts, F z =
      F y + F (A.σ y) + F (A.σ (A.σ y)) + F (A.σ (A.σ (A.σ y))) := by
  rw [crossingOf, Orbit.darts_mk, orbitFinset, List.sum_toFinset _ (orbitList_nodup _ _),
    orbitList_σ]
  simp [add_assoc]

theorem segBdry_crossingOf (h : A.Segment → ZMod 2) (y : D) :
    A.segBdry h (A.crossingOf y) =
      h (A.segmentOf y) + h (A.segmentOf (A.σ y)) + h (A.segmentOf (A.σ (A.σ y))) +
        h (A.segmentOf (A.σ (A.σ (A.σ y)))) :=
  A.sum_darts_crossingOf (fun z => h (A.segmentOf z)) y

/-- `B ∘ L = 0`. -/
theorem segBdry_cellBdry (g : A.Cell → ZMod 2) : A.segBdry (A.cellBdry g) = 0 := by
  funext x
  obtain ⟨y, rfl⟩ := x.exists_mk
  change A.segBdry (A.cellBdry g) (A.crossingOf y) = 0
  rw [segBdry_crossingOf, cellBdry_segmentOf, cellBdry_segmentOf, cellBdry_segmentOf,
    cellBdry_segmentOf, ← cellOf_σ, ← cellOf_σ, ← cellOf_σ, ← cellOf_σ, A.σ_σ_σ_σ]
  exact zmod2_cycle _ _ _ _

/-- A function on darts that is invariant under `σ` and `α` is constant (connectivity). -/
theorem const_of_invariant {β : Type*} (G : D → β) (hσ : ∀ y, G (A.σ y) = G y)
    (hα : ∀ y, G (A.α y) = G y) (y z : D) : G y = G z := by
  induction A.connected y z with
  | rel a b h => rcases h with rfl | rfl
                 · exact (hσ a).symm
                 · exact (hα a).symm
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- `ker L` consists of constant functions. -/
theorem ker_cellBdry_le : LinearMap.ker A.cellBdry ≤ ZMod 2 ∙ (fun _ => 1) := by
  intro g hg
  rw [LinearMap.mem_ker] at hg
  have h : ∀ y, g (A.cellOf (A.α y)) = g (A.cellOf y) := fun y => by
    have := congrFun hg (A.segmentOf y)
    rw [cellBdry_segmentOf, Pi.zero_apply] at this
    rw [zmod2_eq_add_of_add_eq this, add_zero]
  rcases isEmpty_or_nonempty D with hD | ⟨⟨y0⟩⟩
  · have : g = 0 := funext fun f => by obtain ⟨y, -⟩ := f.exists_mk; exact (IsEmpty.false y).elim
    rw [this]; exact Submodule.zero_mem _
  · rw [Submodule.mem_span_singleton]
    refine ⟨g (A.cellOf y0), funext fun f => ?_⟩
    obtain ⟨y, rfl⟩ := f.exists_mk
    have := A.const_of_invariant (fun z => g (A.cellOf z))
      (fun z => by rw [cellOf_σ, h]) h y0 y
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    exact this

theorem finrank_ker_cellBdry_le : finrank (ZMod 2) (LinearMap.ker A.cellBdry) ≤ 1 := by
  refine (Submodule.finrank_mono A.ker_cellBdry_le).trans ?_
  refine (finrank_span_le_card ({fun _ => 1} : Set (A.Cell → ZMod 2))).trans ?_
  simp

/-- `B` of a single segment is the sum of its two end crossings. -/
theorem segBdry_single (y : D) :
    A.segBdry (Pi.single (A.segmentOf y) 1) =
      Pi.single (A.crossingOf y) 1 + Pi.single (A.crossingOf (A.α y)) 1 := by
  funext x
  have hne : y ≠ A.α y := (A.isArrangement.α_ne y).symm
  change ∑ z ∈ x.darts, (Pi.single (A.segmentOf y) 1 : A.Segment → ZMod 2) (A.segmentOf z) = _
  have hz : ∀ z, (Pi.single (A.segmentOf y) 1 : A.Segment → ZMod 2) (A.segmentOf z) =
      (if z = y then 1 else 0) + (if z = A.α y then 1 else 0) := by
    intro z
    have hs : A.segmentOf z = A.segmentOf y ↔ z = y ∨ z = A.α y := by
      rw [eq_comm, segmentOf_eq_iff]; simp
    simp only [Pi.single_apply, hs]
    by_cases h1 : z = y
    · subst h1; simp [hne]
    · by_cases h2 : z = A.α y <;> simp [h1, h2, Ne.symm hne]
  rw [sum_congr rfl fun z _ => hz z, sum_add_distrib, sum_ite_eq', sum_ite_eq',
    Pi.add_apply, Pi.single_apply, Pi.single_apply]
  congr 1
  · by_cases h : x = A.crossingOf y
    · rw [if_pos h, if_pos (Orbit.mem_darts.2 h.symm)]
    · rw [if_neg h, if_neg (fun hm => h (Orbit.mem_darts.1 hm).symm)]
  · by_cases h : x = A.crossingOf (A.α y)
    · rw [if_pos h, if_pos (Orbit.mem_darts.2 h.symm)]
    · rw [if_neg h, if_neg (fun hm => h (Orbit.mem_darts.1 hm).symm)]

/-- Any two crossings: the sum of their indicators lies in `range B` (connectivity). -/
theorem single_add_single_mem (y z : D) :
    Pi.single (A.crossingOf y) (1 : ZMod 2) + Pi.single (A.crossingOf z) 1 ∈
      LinearMap.range A.segBdry := by
  induction A.connected y z with
  | rel a b h =>
    rcases h with rfl | rfl
    · rw [crossingOf_σ, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
      exact Submodule.zero_mem _
    · exact ⟨_, A.segBdry_single a⟩
  | refl a =>
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact Submodule.zero_mem _
  | symm a b _ ih => rw [add_comm]; exact ih
  | trans a b c _ _ ih1 ih2 =>
    have := Submodule.add_mem _ ih1 ih2
    convert this using 1
    funext x
    simp only [Pi.add_apply]
    exact zmod2_trans _ _ _

/-- `range B` contains every vector with sum `0`. -/
theorem ker_sumAll_le : LinearMap.ker A.sumAll ≤ LinearMap.range A.segBdry := by
  intro v hv
  rw [LinearMap.mem_ker] at hv
  change ∑ x, v x = 0 at hv
  rcases isEmpty_or_nonempty D with hD | ⟨⟨y0⟩⟩
  · have : v = 0 := funext fun x => by obtain ⟨y, -⟩ := x.exists_mk; exact (IsEmpty.false y).elim
    rw [this]; exact Submodule.zero_mem _
  have hv' : v = ∑ x, v x • (Pi.single x (1 : ZMod 2) + Pi.single (A.crossingOf y0) 1) := by
    rw [sum_congr rfl fun x _ => smul_add (v x) _ _, sum_add_distrib, ← sum_smul, hv, zero_smul,
      add_zero]
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv']
  refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
  obtain ⟨y, rfl⟩ := x.exists_mk
  exact A.single_add_single_mem y y0

theorem card_le_finrank_range_segBdry :
    Fintype.card A.Crossing ≤ finrank (ZMod 2) (LinearMap.range A.segBdry) + 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker A.sumAll
  have h2 : finrank (ZMod 2) (LinearMap.range A.sumAll) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range A.sumAll)
    rwa [finrank_self] at this
  have h3 := Submodule.finrank_mono A.ker_sumAll_le
  rw [finrank_fintype_fun_eq_card] at h1
  omega

/-- The indicator of the segments of the curve `C`. -/
def curveInd (C : Fin n) : A.Segment → ZMod 2 :=
  fun s => if C ∈ Segment.curves A s then 1 else 0

theorem curveInd_segmentOf (C : Fin n) (y : D) :
    A.curveInd C (A.segmentOf y) = if A.curve y = C then 1 else 0 := by
  rw [curveInd, curves_segmentOf]
  simp [eq_comm]

theorem curveInd_mem_ker (C : Fin n) : A.curveInd C ∈ LinearMap.ker A.segBdry := by
  rw [LinearMap.mem_ker]
  funext x
  have h := A.card_darts_filter_curve x C
  change ∑ z ∈ x.darts, A.curveInd C (A.segmentOf z) = 0
  rw [sum_congr rfl fun z _ => A.curveInd_segmentOf C z, ← sum_filter, sum_const, h]
  split_ifs <;> rfl

/-- **Combinatorial Jordan curve theorem**: for every pseudocircle `C` there is a side
function on the cells that changes exactly across the segments of `C`. -/
theorem exists_side (C : Fin n) : ∃ s : A.Cell → ZMod 2,
    ∀ y, s (A.cellOf y) + s (A.cellOf (A.α y)) = if A.curve y = C then 1 else 0 := by
  have hle : LinearMap.range A.cellBdry ≤ LinearMap.ker A.segBdry := by
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]; exact A.segBdry_cellBdry g
  have hL := LinearMap.finrank_range_add_finrank_ker A.cellBdry
  have hB := LinearMap.finrank_range_add_finrank_ker A.segBdry
  rw [finrank_fintype_fun_eq_card] at hL hB
  have hk := A.finrank_ker_cellBdry_le
  have hr := A.card_le_finrank_range_segBdry
  have he := A.isArrangement.euler
  change (Fintype.card A.Crossing : ℤ) - Fintype.card A.Segment + Fintype.card A.Cell = 2 at he
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  obtain ⟨s, hs⟩ : A.curveInd C ∈ LinearMap.range A.cellBdry := heq ▸ A.curveInd_mem_ker C
  refine ⟨s, fun y => ?_⟩
  rw [← cellBdry_segmentOf, hs, curveInd_segmentOf]

/-! ## Consequences -/

theorem side_σ {s : A.Cell → ZMod 2} {C : Fin n}
    (hs : ∀ y, s (A.cellOf y) + s (A.cellOf (A.α y)) = if A.curve y = C then 1 else 0) (y : D) :
    s (A.cellOf (A.σ y)) = s (A.cellOf y) + if A.curve y = C then 1 else 0 := by
  rw [cellOf_σ]; exact zmod2_eq_add_of_add_eq (hs y)

theorem side_σσ {s : A.Cell → ZMod 2} {C : Fin n}
    (hs : ∀ y, s (A.cellOf y) + s (A.cellOf (A.α y)) = if A.curve y = C then 1 else 0) (y : D) :
    s (A.cellOf (A.σ (A.σ y))) = s (A.cellOf y) + (if A.curve y = C then 1 else 0) +
      (if A.curve (A.σ y) = C then 1 else 0) := by
  rw [A.side_σ hs, A.side_σ hs]

/-- **No bridges**: the two cells at any segment are distinct. -/
theorem cellOf_α_ne' (y : D) : A.cellOf (A.α y) ≠ A.cellOf y := by
  obtain ⟨s, hs⟩ := A.exists_side (A.curve y)
  intro h
  have := hs y
  rw [h, zmod2_add_self, if_pos rfl] at this
  exact absurd this (by decide)

/-- Opposite cells at a crossing are distinct. -/
theorem cellOf_σσ_ne (y : D) : A.cellOf (A.σ (A.σ y)) ≠ A.cellOf y := by
  obtain ⟨s, hs⟩ := A.exists_side (A.curve y)
  intro h
  have := A.side_σσ hs y
  rw [h, if_pos rfl, if_neg (A.isArrangement.curve_σ y), add_zero] at this
  have h2 := congrArg (· + s (A.cellOf y)) this
  simp only [zmod2_add_self, add_right_comm _ (1 : ZMod 2), zero_add] at h2
  exact absurd h2 (by decide)

end Pca.Arrangement
