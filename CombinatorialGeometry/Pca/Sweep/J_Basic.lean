/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package J, helpers: basic rewriting lemmas and the `𝔽₂` boundary maps for `SConf`

Port of the parts of `Pca/Digon.lean`, `Pca/Excess.lean`, `Pca/Derived.lean` and
`Pca/Jordan.lean` that only use axioms 1-5, connectivity and Euler, stated for a sweep
configuration (`Pca/Sweep/Conf.lean`). Main result: `j_range_eq_ker`, every cycle of the
segments (an element of `ker B`) is a coboundary of the cells (`range L`).
-/
import Pca.Sweep.Basic
import Pca.Derived
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod

open Equiv Finset Module

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

theorem j_zmod2_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide

theorem j_zmod2_eq_add_of_add_eq {a b c : ZMod 2} (h : a + b = c) : b = a + c := by
  subst h; rw [← add_assoc, j_zmod2_add_self, zero_add]

/-! ## Rewriting lemmas -/

theorem j_straight_apply (d : D) : Γ.straight d = Γ.σ (Γ.σ (Γ.α d)) := rfl

theorem j_φ_apply (d : D) : Γ.φ d = Γ.σ (Γ.α d) := rfl

theorem j_α_α (d : D) : Γ.α (Γ.α d) = d := Γ.isSConf.α_α d

theorem j_curve_α (d : D) : Γ.curve (Γ.α d) = Γ.curve d := Γ.isSConf.curve_α d

theorem j_curve_σσ (d : D) : Γ.curve (Γ.σ (Γ.σ d)) = Γ.curve d := Γ.isSConf.curve_σσ d

theorem j_curve_straight (d : D) : Γ.curve (Γ.straight d) = Γ.curve d := by
  rw [j_straight_apply, j_curve_σσ, j_curve_α]

theorem j_period_σ (d : D) : period Γ.σ d = 4 := by
  rw [← card_orbitFinset]; exact Γ.isSConf.card_crossing d

theorem j_σ4 (d : D) : Γ.σ (Γ.σ (Γ.σ (Γ.σ d))) = d := by
  have h := iterate_period Γ.σ d
  rw [Γ.j_period_σ] at h
  simpa using h

theorem j_orbitList_σ (d : D) :
    orbitList Γ.σ d = [d, Γ.σ d, Γ.σ (Γ.σ d), Γ.σ (Γ.σ (Γ.σ d))] := by
  simp [orbitList, Γ.j_period_σ, List.range_succ]

theorem j_σσ_ne (d : D) : Γ.σ (Γ.σ d) ≠ d := by
  have h := orbitList_nodup Γ.σ d
  rw [j_orbitList_σ] at h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact fun e => h.1.2.1 e.symm

theorem j_period_α (d : D) : period Γ.α d = 2 := by
  apply le_antisymm
  · exact Nat.find_min' _ ⟨by norm_num, Γ.isSConf.α_α d⟩
  · by_contra h
    have h1 : period Γ.α d = 1 := by have := period_pos Γ.α d; omega
    have := iterate_period Γ.α d
    rw [h1] at this
    exact Γ.isSConf.α_ne d this

theorem j_orbitList_α (d : D) : orbitList Γ.α d = [d, Γ.α d] := by
  simp [orbitList, Γ.j_period_α, List.range_succ]

theorem j_segmentOf_eq_iff {a b : D} : Γ.segmentOf a = Γ.segmentOf b ↔ b ∈ [a, Γ.α a] := by
  rw [segmentOf, segmentOf, Orbit.mk_eq_mk, ← mem_orbitList, j_orbitList_α]

theorem j_darts_segmentOf (d : D) : (Γ.segmentOf d).darts = {d, Γ.α d} := by
  simp [segmentOf, Orbit.darts_mk, orbitFinset, j_orbitList_α]

theorem j_segmentOf_α (d : D) : Γ.segmentOf (Γ.α d) = Γ.segmentOf d := by
  rw [j_segmentOf_eq_iff]; simp [j_α_α]

theorem j_crossingOf_σ (d : D) : Γ.crossingOf (Γ.σ d) = Γ.crossingOf d := by
  rw [crossingOf, crossingOf, Orbit.mk_eq_mk]
  exact Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl _ _)

theorem j_cellOf_φ (d : D) : Γ.cellOf (Γ.φ d) = Γ.cellOf d := by
  rw [cellOf, cellOf, Orbit.mk_eq_mk]
  exact Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl _ _)

/-- The cell to the left of `d` is the cell of `σ d`. -/
theorem j_cellOf_σ (d : D) : Γ.cellOf (Γ.σ d) = Γ.cellOf (Γ.α d) := by
  conv_rhs => rw [← j_cellOf_φ, j_φ_apply, j_α_α]

/-- The curves through the crossing of `d` are the curves of `d` and `σ d`. -/
theorem j_curves_crossingOf (d : D) :
    Γ.curves (Γ.crossingOf d) = {Γ.curve d, Γ.curve (Γ.σ d)} := by
  simp only [curves, crossingCurves, crossingOf, Orbit.darts_mk, orbitFinset, j_orbitList_σ]
  ext c
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, mem_image, mem_insert,
    mem_singleton]
  constructor
  · rintro ⟨e, he, rfl⟩
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl (Γ.j_curve_σσ _)
    · exact Or.inr (Γ.j_curve_σσ _)
  · rintro (rfl | rfl)
    · exact ⟨d, Or.inl rfl, rfl⟩
    · exact ⟨Γ.σ d, Or.inr (Or.inl rfl), rfl⟩

theorem j_sum_darts_crossingOf {M : Type*} [AddCommMonoid M] (F : D → M) (y : D) :
    ∑ z ∈ (Γ.crossingOf y).darts, F z =
      F y + F (Γ.σ y) + F (Γ.σ (Γ.σ y)) + F (Γ.σ (Γ.σ (Γ.σ y))) := by
  rw [crossingOf, Orbit.darts_mk, orbitFinset, List.sum_toFinset _ (orbitList_nodup _ _),
    j_orbitList_σ]
  simp [add_assoc]

/-! ## The boundary maps (as in `Pca/Jordan.lean`) -/

/-- `L`: a function on cells gives on each segment the sum over the two cells at it. -/
def jCellBdry : (Γ.Cell → ZMod 2) →ₗ[ZMod 2] (Γ.Segment → ZMod 2) where
  toFun g s := ∑ y ∈ s.darts, g (Γ.cellOf y)
  map_add' g h := by funext s; simp [sum_add_distrib]
  map_smul' c g := by funext s; simp [mul_sum]

/-- `B`: a function on segments gives on each crossing the sum over its four darts. -/
def jSegBdry : (Γ.Segment → ZMod 2) →ₗ[ZMod 2] (Γ.Crossing → ZMod 2) where
  toFun h x := ∑ y ∈ x.darts, h (Γ.segmentOf y)
  map_add' g h := by funext s; simp [sum_add_distrib]
  map_smul' c g := by funext s; simp [mul_sum]

/-- The sum of all entries. -/
def jSumAll : (Γ.Crossing → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ x, v x
  map_add' v w := by simp [sum_add_distrib]
  map_smul' c v := by simp [mul_sum]

theorem j_cellBdry_segmentOf (g : Γ.Cell → ZMod 2) (y : D) :
    Γ.jCellBdry g (Γ.segmentOf y) = g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) := by
  show ∑ z ∈ (Γ.segmentOf y).darts, g (Γ.cellOf z) = _
  rw [j_darts_segmentOf, sum_pair (Γ.isSConf.α_ne y).symm]

theorem j_segBdry_crossingOf (h : Γ.Segment → ZMod 2) (y : D) :
    Γ.jSegBdry h (Γ.crossingOf y) =
      h (Γ.segmentOf y) + h (Γ.segmentOf (Γ.σ y)) + h (Γ.segmentOf (Γ.σ (Γ.σ y))) +
        h (Γ.segmentOf (Γ.σ (Γ.σ (Γ.σ y)))) :=
  Γ.j_sum_darts_crossingOf (fun z => h (Γ.segmentOf z)) y

theorem j_zmod2_cycle (a b c e : ZMod 2) : a + b + (b + c) + (c + e) + (e + a) = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;> decide

theorem j_zmod2_trans (p q r : ZMod 2) : p + r = p + q + (q + r) := by
  fin_cases p <;> fin_cases q <;> fin_cases r <;> decide

/-- `B ∘ L = 0`. -/
theorem j_segBdry_cellBdry (g : Γ.Cell → ZMod 2) : Γ.jSegBdry (Γ.jCellBdry g) = 0 := by
  funext x
  obtain ⟨y, rfl⟩ := x.exists_mk
  change Γ.jSegBdry (Γ.jCellBdry g) (Γ.crossingOf y) = 0
  rw [j_segBdry_crossingOf, j_cellBdry_segmentOf, j_cellBdry_segmentOf, j_cellBdry_segmentOf,
    j_cellBdry_segmentOf, ← j_cellOf_σ, ← j_cellOf_σ, ← j_cellOf_σ, ← j_cellOf_σ, Γ.j_σ4]
  exact j_zmod2_cycle _ _ _ _

theorem j_eqvGen_rec {P : D → D → Prop} (hσ : ∀ a, P a (Γ.σ a)) (hα : ∀ a, P a (Γ.α a))
    (hrefl : ∀ a, P a a) (hsymm : ∀ a b, P a b → P b a)
    (htrans : ∀ a b c, P a b → P b c → P a c) (y z : D) : P y z := by
  induction Γ.isSConf.connected y z with
  | rel a b h => rcases h with rfl | rfl
                 · exact hσ a
                 · exact hα a
  | refl => exact hrefl _
  | symm _ _ _ ih => exact hsymm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact htrans _ _ _ ih1 ih2

/-- `ker L` consists of constant functions. -/
theorem j_ker_cellBdry_le : LinearMap.ker Γ.jCellBdry ≤ ZMod 2 ∙ (fun _ => 1) := by
  intro g hg
  rw [LinearMap.mem_ker] at hg
  have h : ∀ y, g (Γ.cellOf (Γ.α y)) = g (Γ.cellOf y) := fun y => by
    have := congrFun hg (Γ.segmentOf y)
    rw [j_cellBdry_segmentOf, Pi.zero_apply] at this
    rw [j_zmod2_eq_add_of_add_eq this, add_zero]
  rcases isEmpty_or_nonempty D with hD | ⟨⟨y0⟩⟩
  · have : g = 0 := funext fun f => by obtain ⟨y, -⟩ := f.exists_mk; exact (IsEmpty.false y).elim
    rw [this]; exact Submodule.zero_mem _
  · rw [Submodule.mem_span_singleton]
    refine ⟨g (Γ.cellOf y0), funext fun f => ?_⟩
    obtain ⟨y, rfl⟩ := f.exists_mk
    have := Γ.j_eqvGen_rec (P := fun a b => g (Γ.cellOf a) = g (Γ.cellOf b))
      (fun a => by rw [j_cellOf_σ, h]) (fun a => (h a).symm) (fun _ => rfl)
      (fun _ _ h => h.symm) (fun _ _ _ h1 h2 => h1.trans h2) y0 y
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    exact this

theorem j_finrank_ker_cellBdry_le : finrank (ZMod 2) (LinearMap.ker Γ.jCellBdry) ≤ 1 := by
  refine (Submodule.finrank_mono Γ.j_ker_cellBdry_le).trans ?_
  refine (finrank_span_le_card ({fun _ => 1} : Set (Γ.Cell → ZMod 2))).trans ?_
  simp

/-- `B` of a single segment is the sum of its two end crossings. -/
theorem j_segBdry_single (y : D) :
    Γ.jSegBdry (Pi.single (Γ.segmentOf y) 1) =
      Pi.single (Γ.crossingOf y) 1 + Pi.single (Γ.crossingOf (Γ.α y)) 1 := by
  funext x
  have hne : y ≠ Γ.α y := (Γ.isSConf.α_ne y).symm
  change ∑ z ∈ x.darts, (Pi.single (Γ.segmentOf y) 1 : Γ.Segment → ZMod 2) (Γ.segmentOf z) = _
  have hz : ∀ z, (Pi.single (Γ.segmentOf y) 1 : Γ.Segment → ZMod 2) (Γ.segmentOf z) =
      (if z = y then 1 else 0) + (if z = Γ.α y then 1 else 0) := by
    intro z
    have hs : Γ.segmentOf z = Γ.segmentOf y ↔ z = y ∨ z = Γ.α y := by
      rw [eq_comm, j_segmentOf_eq_iff]; simp
    simp only [Pi.single_apply, hs]
    by_cases h1 : z = y
    · subst h1; simp [hne]
    · by_cases h2 : z = Γ.α y <;> simp [h1, h2, Ne.symm hne]
  rw [sum_congr rfl fun z _ => hz z, sum_add_distrib, sum_ite_eq', sum_ite_eq',
    Pi.add_apply, Pi.single_apply, Pi.single_apply]
  congr 1
  · by_cases h : x = Γ.crossingOf y
    · rw [if_pos h, if_pos (Orbit.mem_darts.2 h.symm)]
    · rw [if_neg h, if_neg (fun hm => h (Orbit.mem_darts.1 hm).symm)]
  · by_cases h : x = Γ.crossingOf (Γ.α y)
    · rw [if_pos h, if_pos (Orbit.mem_darts.2 h.symm)]
    · rw [if_neg h, if_neg (fun hm => h (Orbit.mem_darts.1 hm).symm)]

/-- Any two crossings: the sum of their indicators lies in `range B` (connectivity). -/
theorem j_single_add_single_mem (y z : D) :
    Pi.single (Γ.crossingOf y) (1 : ZMod 2) + Pi.single (Γ.crossingOf z) 1 ∈
      LinearMap.range Γ.jSegBdry := by
  have h0 : ∀ a : D, Pi.single (Γ.crossingOf a) (1 : ZMod 2) + Pi.single (Γ.crossingOf a) 1 ∈
      LinearMap.range Γ.jSegBdry := fun a => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact Submodule.zero_mem _
  refine Γ.j_eqvGen_rec (P := fun a b => Pi.single (Γ.crossingOf a) (1 : ZMod 2) +
      Pi.single (Γ.crossingOf b) 1 ∈ LinearMap.range Γ.jSegBdry) (fun a => ?_) (fun a => ?_) h0
    (fun a b h => ?_) (fun a b c h1 h2 => ?_) y z
  · rw [j_crossingOf_σ]; exact h0 a
  · exact ⟨_, Γ.j_segBdry_single a⟩
  · rw [add_comm]; exact h
  · have := Submodule.add_mem _ h1 h2
    convert this using 1
    funext x
    simp only [Pi.add_apply]
    exact j_zmod2_trans _ _ _

/-- `range B` contains every vector with sum `0`. -/
theorem j_ker_sumAll_le : LinearMap.ker Γ.jSumAll ≤ LinearMap.range Γ.jSegBdry := by
  intro v hv
  rw [LinearMap.mem_ker] at hv
  change ∑ x, v x = 0 at hv
  rcases isEmpty_or_nonempty D with hD | ⟨⟨y0⟩⟩
  · have : v = 0 := funext fun x => by obtain ⟨y, -⟩ := x.exists_mk; exact (IsEmpty.false y).elim
    rw [this]; exact Submodule.zero_mem _
  have hv' : v = ∑ x, v x • (Pi.single x (1 : ZMod 2) + Pi.single (Γ.crossingOf y0) 1) := by
    rw [sum_congr rfl fun x _ => smul_add (v x) _ _, sum_add_distrib, ← sum_smul, hv, zero_smul,
      add_zero]
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv']
  refine Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ ?_
  obtain ⟨y, rfl⟩ := x.exists_mk
  exact Γ.j_single_add_single_mem y y0

theorem j_card_le_finrank_range_segBdry :
    Fintype.card Γ.Crossing ≤ finrank (ZMod 2) (LinearMap.range Γ.jSegBdry) + 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker Γ.jSumAll
  have h2 : finrank (ZMod 2) (LinearMap.range Γ.jSumAll) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range Γ.jSumAll)
    rwa [finrank_self] at this
  have h3 := Submodule.finrank_mono Γ.j_ker_sumAll_le
  rw [finrank_fintype_fun_eq_card] at h1
  omega

/-- **`range L = ker B`** (Euler and connectivity): every cycle of segments is a cut. -/
theorem j_mem_range_of_mem_ker (h : Γ.Segment → ZMod 2) (hh : Γ.jSegBdry h = 0) :
    ∃ g, Γ.jCellBdry g = h := by
  rcases isEmpty_or_nonempty D with hD | hne
  · refine ⟨0, funext fun s => ?_⟩
    obtain ⟨y, -⟩ := s.exists_mk; exact (IsEmpty.false y).elim
  have hle : LinearMap.range Γ.jCellBdry ≤ LinearMap.ker Γ.jSegBdry := by
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]; exact Γ.j_segBdry_cellBdry g
  have hL := LinearMap.finrank_range_add_finrank_ker Γ.jCellBdry
  have hB := LinearMap.finrank_range_add_finrank_ker Γ.jSegBdry
  rw [finrank_fintype_fun_eq_card] at hL hB
  have hk := Γ.j_finrank_ker_cellBdry_le
  have hr := Γ.j_card_le_finrank_range_segBdry
  have he := Γ.isSConf.euler hne
  change (Fintype.card Γ.Crossing : ℤ) - Fintype.card Γ.Segment + Fintype.card Γ.Cell = 2 at he
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hmem : h ∈ LinearMap.ker Γ.jSegBdry := hh
  rw [← heq] at hmem
  exact hmem

end SConf

end Pca.Sweep
