/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package U, helpers: two-intersection, connectivity and the side function of the untangling

* two-intersection: exchanging the `j`-th crossings of the two legs (`uπ`) maps the pairs of
  curves of the untangled configuration to those of `Γ`;
* connectivity: every changed dart is reached from `σ d`;
* the side function: the darts of `v` (now the new crossing below `S`) get side `0`.
-/
import Pca.Sweep.U_Conf

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {d a : D} {k : ℕ} {γ : Fin n}

variable (Γ) in
/-- The `j`-th crossing of the leg from `i`. -/
def uF1 (d : D) (j : ℕ) : Γ.Crossing := Γ.crossingOf ((Γ.straight ^ j) (Γ.ub1 d))

variable (Γ) in
/-- The `j`-th crossing of the leg from `i + 1`. -/
def uF2 (d : D) (j : ℕ) : Γ.Crossing := Γ.crossingOf ((Γ.straight ^ j) (Γ.ub2 d))

variable (Γ) in
/-- Exchange the crossings of the two legs. -/
noncomputable def uπ (d : D) (k : ℕ) (x : Γ.Crossing) : Γ.Crossing :=
  if h : ∃ j, j < k ∧ Γ.uF1 d j = x then Γ.uF2 d (Classical.choose h)
  else if h' : ∃ j, j < k ∧ Γ.uF2 d j = x then Γ.uF1 d (Classical.choose h') else x

section Hyp

variable (H : Γ.UHyp d a k γ)
include H

theorem UHyp.uπ_f1 {j : ℕ} (hj : j < k) : Γ.uπ d k (Γ.uF1 d j) = Γ.uF2 d j := by
  have h : ∃ i, i < k ∧ Γ.uF1 d i = Γ.uF1 d j := ⟨j, hj, rfl⟩
  rw [uπ, dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  rw [H.f1_inj h1 hj h2]

theorem UHyp.uπ_f2 {j : ℕ} (hj : j < k) : Γ.uπ d k (Γ.uF2 d j) = Γ.uF1 d j := by
  have h0 : ¬ ∃ i, i < k ∧ Γ.uF1 d i = Γ.uF2 d j := by
    rintro ⟨i, hi, he⟩; exact H.f1_ne_f2 hi hj he
  have h : ∃ i, i < k ∧ Γ.uF2 d i = Γ.uF2 d j := ⟨j, hj, rfl⟩
  rw [uπ, dif_neg h0, dif_pos h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  rw [H.f2_inj h1 hj h2]

theorem UHyp.uπ_other {x : Γ.Crossing} (h1 : x ∉ Γ.uC1 d k) (h2 : x ∉ Γ.uC2 d k) :
    Γ.uπ d k x = x := by
  have h1' : ¬ ∃ i, i < k ∧ Γ.uF1 d i = x := by
    rintro ⟨i, hi, rfl⟩; exact h1 (mem_image.2 ⟨i, mem_range.2 hi, rfl⟩)
  have h2' : ¬ ∃ i, i < k ∧ Γ.uF2 d i = x := by
    rintro ⟨i, hi, rfl⟩; exact h2 (mem_image.2 ⟨i, mem_range.2 hi, rfl⟩)
  rw [uπ, dif_neg h1', dif_neg h2']

theorem UHyp.uπ_invol : Function.Involutive (Γ.uπ d k) := by
  intro x
  by_cases h1 : x ∈ Γ.uC1 d k
  · obtain ⟨j, hj, rfl⟩ := mem_image.1 h1
    rw [mem_range] at hj
    exact (congrArg _ (H.uπ_f1 hj)).trans (H.uπ_f2 hj)
  by_cases h2 : x ∈ Γ.uC2 d k
  · obtain ⟨j, hj, rfl⟩ := mem_image.1 h2
    rw [mem_range] at hj
    exact (congrArg _ (H.uπ_f2 hj)).trans (H.uπ_f1 hj)
  rw [H.uπ_other h1 h2, H.uπ_other h1 h2]

/-- The curves at a crossing, for the new labels. -/
theorem UHyp.uCurves_mk (y : D) :
    crossingCurves Γ.σ (Γ.uCurve d k) (Γ.crossingOf y) =
      {Γ.uCurve d k y, Γ.uCurve d k (Γ.σ y)} := by
  simp only [crossingCurves, crossingOf, Orbit.darts_mk, orbitFinset, Γ.j_orbitList_σ]
  ext c
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, mem_image, mem_insert,
    mem_singleton]
  constructor
  · rintro ⟨e, he, rfl⟩
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl (H.uCurve_σσ _)
    · exact Or.inr (H.uCurve_σσ _)
  · rintro (rfl | rfl)
    · exact ⟨y, Or.inl rfl, rfl⟩
    · exact ⟨Γ.σ y, Or.inr (Or.inl rfl), rfl⟩

theorem UHyp.uCurves_π (x : Γ.Crossing) :
    crossingCurves Γ.σ (Γ.uCurve d k) x = Γ.curves (Γ.uπ d k x) := by
  by_cases h1 : x ∈ Γ.uC1 d k
  · obtain ⟨j, hj, rfl⟩ := mem_image.1 h1
    rw [mem_range] at hj
    rw [show Γ.crossingOf ((Γ.straight ^ j) (Γ.ub1 d)) = Γ.uF1 d j from rfl, H.uπ_f1 hj, uF2,
      H.curves2 hj, uF1, H.uCurves_mk]
    have hc1 : Γ.crossingOf ((Γ.straight ^ j) (Γ.ub1 d)) ∈ Γ.uC1 d k := h1
    have hc1' : Γ.crossingOf (Γ.σ ((Γ.straight ^ j) (Γ.ub1 d))) ∈ Γ.uC1 d k := by
      rw [j_crossingOf_σ]; exact h1
    rw [H.uCurve_C1 hc1, H.uCurve_C1 hc1', if_pos (u_curve_pow _ _ _), H.oth1 hj,
      if_neg (H.oth_ne1 j)]
  by_cases h2 : x ∈ Γ.uC2 d k
  · obtain ⟨j, hj, rfl⟩ := mem_image.1 h2
    rw [mem_range] at hj
    rw [show Γ.crossingOf ((Γ.straight ^ j) (Γ.ub2 d)) = Γ.uF2 d j from rfl, H.uπ_f2 hj, uF1,
      H.curves1 hj, uF2, H.uCurves_mk]
    have hc2 : Γ.crossingOf ((Γ.straight ^ j) (Γ.ub2 d)) ∈ Γ.uC2 d k := h2
    have hc2' : Γ.crossingOf (Γ.σ ((Γ.straight ^ j) (Γ.ub2 d))) ∈ Γ.uC2 d k := by
      rw [j_crossingOf_σ]; exact h2
    rw [H.uCurve_C2 hc2, H.uCurve_C2 hc2', if_pos (u_curve_pow _ _ _), H.oth2 hj,
      if_neg (H.oth_ne2 j)]
  rw [H.uπ_other h1 h2]
  obtain ⟨y, rfl⟩ := x.exists_mk
  change crossingCurves Γ.σ (Γ.uCurve d k) (Γ.crossingOf y) = Γ.curves (Γ.crossingOf y)
  have h1' : Γ.crossingOf (Γ.σ y) ∉ Γ.uC1 d k := by rw [j_crossingOf_σ]; exact h1
  have h2' : Γ.crossingOf (Γ.σ y) ∉ Γ.uC2 d k := by rw [j_crossingOf_σ]; exact h2
  rw [H.uCurves_mk, j_curves_crossingOf, H.uCurve_C0 h1 h2, H.uCurve_C0 h1' h2']

/-- Two-intersection property of the untangled configuration. -/
theorem UHyp.two_int (c c' : Fin n) (hcc : c ≠ c') :
    (univ.filter (fun x : Orbit Γ.σ => crossingCurves Γ.σ (Γ.uCurve d k) x = {c, c'})).card ≤ 2 := by
  have h := Γ.isSConf.two_int c c' hcc
  refine le_trans (le_of_eq ?_) h
  refine card_bij (fun x _ => Γ.uπ d k x) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    have := H.uCurves_π x; rw [hx] at this; exact this.symm
  · intro x _ y _ hxy
    exact H.uπ_invol.injective hxy
  · intro y hy
    refine ⟨Γ.uπ d k y, ?_, H.uπ_invol y⟩
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    have := H.uCurves_π (Γ.uπ d k y); rw [H.uπ_invol] at this; rw [this]; exact hy

/-! ### Connectivity -/

theorem UHyp.eqv_st (x : D) :
    Relation.EqvGen (StepRel Γ.σ H.α') x (H.st x) := by
  have h1 : Relation.EqvGen (StepRel Γ.σ H.α') x (H.α' x) := .rel _ _ (Or.inr rfl)
  have h2 : Relation.EqvGen (StepRel Γ.σ H.α') (H.α' x) (Γ.σ (H.α' x)) := .rel _ _ (Or.inl rfl)
  have h3 : Relation.EqvGen (StepRel Γ.σ H.α') (Γ.σ (H.α' x)) (Γ.σ (Γ.σ (H.α' x))) :=
    .rel _ _ (Or.inl rfl)
  exact h1.trans _ _ _ (h2.trans _ _ _ h3)

theorem UHyp.eqv_pow (x : D) (j : ℕ) :
    Relation.EqvGen (StepRel Γ.σ H.α') x ((H.st ^ j) x) := by
  induction j with
  | zero => exact .refl _
  | succ j ih => rw [u_pow_succ]; exact ih.trans _ _ _ (H.eqv_st _)

theorem UHyp.eqv_uM (i : Fin 12) :
    Relation.EqvGen (StepRel Γ.σ H.α') (Γ.ub1 d) (Γ.uM d a i) := by
  have σs : ∀ x, Relation.EqvGen (StepRel Γ.σ H.α') x (Γ.σ x) := fun x => .rel _ _ (Or.inl rfl)
  have αs : ∀ x, Relation.EqvGen (StepRel Γ.σ H.α') x (H.α' x) := fun x => .rel _ _ (Or.inr rfl)
  have e8 : Relation.EqvGen (StepRel Γ.σ H.α') (Γ.ub1 d) (Γ.uM d a 8) :=
    (σs _).trans _ _ _ (σs _)
  have e0 : Relation.EqvGen (StepRel Γ.σ H.α') (Γ.ub1 d) (Γ.uM d a 0) := by
    have := αs (Γ.uM d a 8); rw [H.α'_uM] at this; exact e8.trans _ _ _ this
  have e1 := e0.trans _ _ _ (σs _)
  have e2 := e1.trans _ _ _ (σs _)
  have e3 := e2.trans _ _ _ (σs _)
  have hα : ∀ i j, uPI i = j → Relation.EqvGen (StepRel Γ.σ H.α') (Γ.ub1 d) (Γ.uM d a i) →
      Relation.EqvGen (StepRel Γ.σ H.α') (Γ.ub1 d) (Γ.uM d a j) := by
    intro i j hij hi
    have := αs (Γ.uM d a i); rw [H.α'_uM, hij] at this; exact hi.trans _ _ _ this
  have e9 := hα 1 9 rfl e1
  have e10 := hα 3 10 rfl e3
  have e11 := hα 2 11 rfl e2
  have hk := H.k_pos
  have e7 : Relation.EqvGen (StepRel Γ.σ H.α') (Γ.ub1 d) (Γ.uM d a 7) := by
    have := H.eqv_pow (Γ.ub1 d) (k - 1)
    rwa [H.leg1_st le_rfl, ← H.pos7] at this
  have e4 : Relation.EqvGen (StepRel Γ.σ H.α') (Γ.ub1 d) (Γ.uM d a 4) := by
    have hb : Relation.EqvGen (StepRel Γ.σ H.α') (Γ.ub1 d) (Γ.ub2 d) :=
      e10.trans _ _ _ ((σs _).trans _ _ _ (σs _))
    have := H.eqv_pow (Γ.ub2 d) (k - 1)
    rw [H.leg2_st le_rfl, ← H.pos4] at this
    exact hb.trans _ _ _ this
  have e5 := hα 4 5 rfl e4
  have e6 := hα 7 6 rfl e7
  fin_cases i
  exacts [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]

theorem UHyp.connected (x y : D) : Relation.EqvGen (StepRel Γ.σ H.α') x y := by
  refine Γ.j_eqvGen_rec (P := fun x y => Relation.EqvGen (StepRel Γ.σ H.α') x y)
    (fun x => .rel _ _ (Or.inl rfl)) (fun x => ?_) (fun x => .refl _) (fun _ _ h => h.symm _ _)
    (fun _ _ _ h1 h2 => h1.trans _ _ _ h2) x y
  by_cases hx : ∃ i, Γ.uM d a i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [H.α_uM]
    exact ((H.eqv_uM i).symm _ _).trans _ _ _ (H.eqv_uM _)
  · push Not at hx
    rw [← H.α'_of hx]
    exact .rel _ _ (Or.inr rfl)

end Hyp

end SConf

end Pca.Sweep
