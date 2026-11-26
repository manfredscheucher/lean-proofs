/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package U, helpers: the axioms of the untangled configuration (labels, curves)

With the new edge involution `α'` (`UHyp.α'`) and the new labels `uCurve`: the label axioms,
the straight walks of the two new curves (`doc/pca/sweep.md`: the walk of the curve labelled
`γ2` is the leg from `i`, then `γ2` from beyond `v` to the dart before `i + 1` below, then the new
crossing; likewise for `γ1`), and the two-intersection property (the crossings of the two legs
exchange their pairs of curves).
-/
import Pca.Sweep.U_Build

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u v

/-- Conjugation by an involution that reverses `s` maps cycles of `s` to cycles of `s`. -/
theorem u_sameCycle_conj {X : Type v} {s t : Perm X} (htt : ∀ x, t (t x) = x)
    (hc : ∀ x, t (s (t x)) = s⁻¹ x) {x y : X} (h : s.SameCycle x y) :
    s.SameCycle (t x) (t y) := by
  obtain ⟨i, rfl⟩ := h
  have key : ∀ i : ℤ, ∀ z, t ((s ^ i) z) = (s ^ (-i)) (t z) := by
    intro i z
    have h1 : (t * s * t) = s⁻¹ := by
      ext z; simp only [Perm.mul_apply]; rw [hc]
    have h2 : (t * s * t) ^ i = t * s ^ i * t := by
      have ht : t⁻¹ = t := by ext z; rw [Perm.inv_eq_iff_eq, htt]
      have := conj_zpow (a := t) (b := s) (i := i)
      rw [ht] at this; exact this
    rw [h1, inv_zpow'] at h2
    have := congrArg (fun p : Perm X => p (t z)) h2
    simp only [Perm.mul_apply, htt] at this
    exact this.symm
  exact ⟨-i, by rw [key]⟩

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {d a : D} {k : ℕ} {γ : Fin n}

/-- The new edge involution. -/
noncomputable def UHyp.α' (H : Γ.UHyp d a k γ) : Perm D :=
  Function.Involutive.toPerm _ H.uαf_invol

/-- The new straight walk. -/
noncomputable def UHyp.st (H : Γ.UHyp d a k γ) : Perm D := straightPerm Γ.σ H.α'

section Hyp

variable (H : Γ.UHyp d a k γ)
include H

theorem UHyp.α'_apply (x : D) : H.α' x = Γ.uαf d a x := rfl

theorem UHyp.α'_uM (i : Fin 12) : H.α' (Γ.uM d a i) = Γ.uM d a (uPI i) := H.uαf_uM i

theorem UHyp.α'_of {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) : H.α' x = Γ.α x := H.uαf_of hx

theorem UHyp.st_apply (x : D) : H.st x = Γ.σ (Γ.σ (H.α' x)) := rfl

theorem UHyp.st_of {x : D} (hx : ∀ i, Γ.uM d a i ≠ x) : H.st x = Γ.straight x := by
  rw [H.st_apply, H.α'_of hx]; rfl

/-- The changed darts on the walks of `γ1` and `γ2`. -/
theorem UHyp.notM1 {i : ℕ} (hi : i < period Γ.straight (Γ.ub1 d)) (h1 : i ≠ k) (h2 : i + 1 ≠ k)
    (h3 : i + 1 ≠ period Γ.straight (Γ.ub1 d)) :
    ∀ m, Γ.uM d a m ≠ (Γ.straight ^ i) (Γ.ub1 d) := by
  intro m hm
  rcases H.fwd1 hi hm with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega

theorem UHyp.notM2 {i : ℕ} (hi : i < period Γ.straight (Γ.ub2 d)) (h1 : i ≠ k) (h2 : i + 1 ≠ k)
    (h3 : i + 1 ≠ period Γ.straight (Γ.ub2 d)) :
    ∀ m, Γ.uM d a m ≠ (Γ.straight ^ i) (Γ.ub2 d) := by
  intro m hm
  rcases H.fwd2 hi hm with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega

theorem UHyp.st_eq_of_notM {M : D → Prop} (hM : M = fun x => ∃ i, Γ.uM d a i = x) :
    ∀ x, ¬ M x → H.st x = Γ.straight x := by
  intro x hx
  subst hM
  push Not at hx
  exact H.st_of hx

/-- The walk along the first `k - 1` steps of a leg is unchanged. -/
theorem UHyp.leg1_st {j : ℕ} (hj : j ≤ k - 1) :
    (H.st ^ j) (Γ.ub1 d) = (Γ.straight ^ j) (Γ.ub1 d) := by
  have hP := H.kP1
  refine u_pow_eq_of_avoid (M := fun x => ∃ i, Γ.uM d a i = x) (H.st_eq_of_notM rfl) _ j ?_
  intro i hi ⟨m, hm⟩
  exact H.notM1 (by omega) (by omega) (by omega) (by omega) m hm

theorem UHyp.leg2_st {j : ℕ} (hj : j ≤ k - 1) :
    (H.st ^ j) (Γ.ub2 d) = (Γ.straight ^ j) (Γ.ub2 d) := by
  have hP := H.kP2
  refine u_pow_eq_of_avoid (M := fun x => ∃ i, Γ.uM d a i = x) (H.st_eq_of_notM rfl) _ j ?_
  intro i hi ⟨m, hm⟩
  exact H.notM2 (by omega) (by omega) (by omega) (by omega) m hm

/-- After the leg from `i`, the new walk continues on `γ2` beyond `v`. -/
theorem UHyp.leg1_turn : (H.st ^ k) (Γ.ub1 d) = (Γ.straight ^ (k + 1)) (Γ.ub2 d) := by
  have hk := H.k_pos
  rw [show (H.st ^ k) (Γ.ub1 d) = H.st ((H.st ^ (k - 1)) (Γ.ub1 d)) by
      rw [← u_pow_succ, Nat.sub_add_cancel hk], H.leg1_st le_rfl, ← H.pos7,
    show Γ.α (Γ.σ (Γ.σ (Γ.σ a))) = Γ.uM d a 7 from rfl, H.st_apply, H.α'_uM]
  show Γ.σ (Γ.σ (Γ.α (Γ.σ (Γ.σ a)))) = _
  rw [H.pos6, Γ.j_σ4]

theorem UHyp.leg2_turn : (H.st ^ k) (Γ.ub2 d) = (Γ.straight ^ (k + 1)) (Γ.ub1 d) := by
  have hk := H.k_pos
  rw [show (H.st ^ k) (Γ.ub2 d) = H.st ((H.st ^ (k - 1)) (Γ.ub2 d)) by
      rw [← u_pow_succ, Nat.sub_add_cancel hk], H.leg2_st le_rfl, ← H.pos4,
    show Γ.α a = Γ.uM d a 4 from rfl, H.st_apply, H.α'_uM]
  show Γ.σ (Γ.σ (Γ.α (Γ.σ a))) = _
  rw [H.pos5, Γ.j_σ4]

theorem UHyp.tail2_st {m : ℕ} (hm1 : k + 1 ≤ m) (hm2 : m < period Γ.straight (Γ.ub2 d)) :
    (H.st ^ (m - (k + 1))) ((Γ.straight ^ (k + 1)) (Γ.ub2 d)) = (Γ.straight ^ m) (Γ.ub2 d) := by
  rw [u_pow_eq_of_avoid (M := fun x => ∃ i, Γ.uM d a i = x) (H.st_eq_of_notM rfl) _ _ ?_,
    ← u_pow_add, Nat.sub_add_cancel hm1]
  intro i hi ⟨j, hj⟩
  rw [← u_pow_add] at hj
  exact H.notM2 (by omega) (by omega) (by omega) (by omega) j hj

theorem UHyp.tail1_st {m : ℕ} (hm1 : k + 1 ≤ m) (hm2 : m < period Γ.straight (Γ.ub1 d)) :
    (H.st ^ (m - (k + 1))) ((Γ.straight ^ (k + 1)) (Γ.ub1 d)) = (Γ.straight ^ m) (Γ.ub1 d) := by
  rw [u_pow_eq_of_avoid (M := fun x => ∃ i, Γ.uM d a i = x) (H.st_eq_of_notM rfl) _ _ ?_,
    ← u_pow_add, Nat.sub_add_cancel hm1]
  intro i hi ⟨j, hj⟩
  rw [← u_pow_add] at hj
  exact H.notM1 (by omega) (by omega) (by omega) (by omega) j hj

theorem UHyp.st_uM0 : H.st (Γ.uM d a 0) = Γ.ub1 d := by
  rw [H.st_apply, H.α'_uM]
  show Γ.σ (Γ.σ (Γ.σ (Γ.σ (Γ.σ d)))) = Γ.σ d
  rw [Γ.j_σ4]

theorem UHyp.st_uM3 : H.st (Γ.uM d a 3) = Γ.ub2 d := by
  rw [H.st_apply, H.α'_uM]; rfl

/-- `σ²` reverses the new walks. -/
theorem UHyp.st_conj (x : D) : Γ.σ (Γ.σ (H.st (Γ.σ (Γ.σ x)))) = H.st⁻¹ x := by
  rw [eq_comm, Perm.inv_eq_iff_eq, H.st_apply, H.st_apply, Γ.j_σ4, H.α'_apply, H.α'_apply,
    H.uαf_invol, Γ.j_σ4]

theorem UHyp.sc_σσ {x y : D} (h : H.st.SameCycle x y) :
    H.st.SameCycle (Γ.σ (Γ.σ x)) (Γ.σ (Γ.σ y)) :=
  u_sameCycle_conj (t := Γ.σ * Γ.σ) (fun x => Γ.j_σ4 x) (fun x => H.st_conj x) h

/-! ### The labels -/

theorem UHyp.uCurve_ne_S_iff (x : D) : Γ.uCurve d k x = Γ.S ↔ Γ.curve x = Γ.S := by
  unfold uCurve
  split_ifs with h1 h2
  · exact ⟨fun h => absurd h H.c2S, fun h => absurd (h1.2.symm.trans h) H.c1S⟩
  · exact ⟨fun h => absurd h H.c1S, fun h => absurd (h2.2.symm.trans h) H.c2S⟩
  · exact Iff.rfl

theorem UHyp.uCurve_α (x : D) : Γ.uCurve d k (H.α' x) = Γ.uCurve d k x := by
  by_cases hx : ∃ i, Γ.uM d a i = x
  · obtain ⟨i, rfl⟩ := hx
    rw [H.α'_uM, H.uCurve_uM, H.uCurve_uM, uKI'_uPI]
  · push Not at hx
    rw [H.α'_of hx]
    simp only [uCurve, H.uR1_α_iff hx, H.uR2_α_iff hx, j_curve_α]

theorem UHyp.C1_curve {x : D} (h : Γ.crossingOf x ∈ Γ.uC1 d k) :
    Γ.curve x ≠ Γ.curve (Γ.ub2 d) := by
  obtain ⟨j, hj, hx⟩ := mem_image.1 h
  rw [mem_range] at hj
  intro hc
  have hm : Γ.curve x ∈ Γ.curves (Γ.crossingOf x) := by
    rw [j_curves_crossingOf]; exact mem_insert_self _ _
  rw [← hx, H.curves1 hj, hc, mem_insert, mem_singleton] at hm
  rcases hm with hm | hm
  · exact H.c12 hm.symm
  · exact H.oth_ne2 j hm.symm

theorem UHyp.C2_curve {x : D} (h : Γ.crossingOf x ∈ Γ.uC2 d k) :
    Γ.curve x ≠ Γ.curve (Γ.ub1 d) := by
  obtain ⟨j, hj, hx⟩ := mem_image.1 h
  rw [mem_range] at hj
  intro hc
  have hm : Γ.curve x ∈ Γ.curves (Γ.crossingOf x) := by
    rw [j_curves_crossingOf]; exact mem_insert_self _ _
  rw [← hx, H.curves2 hj, hc, mem_insert, mem_singleton] at hm
  rcases hm with hm | hm
  · exact H.c12 hm
  · exact H.oth_ne1 j hm.symm

theorem UHyp.C12 {x : Γ.Crossing} (h1 : x ∈ Γ.uC1 d k) : x ∉ Γ.uC2 d k := by
  intro h2
  obtain ⟨i, hi, rfl⟩ := mem_image.1 h1
  obtain ⟨j, hj, hx⟩ := mem_image.1 h2
  rw [mem_range] at hi hj
  exact H.f1_ne_f2 hi hj hx.symm

/-- On the crossings of the leg from `i`, the new label. -/
theorem UHyp.uCurve_C1 {x : D} (h : Γ.crossingOf x ∈ Γ.uC1 d k) :
    Γ.uCurve d k x = if Γ.curve x = Γ.curve (Γ.ub1 d) then Γ.curve (Γ.ub2 d) else Γ.curve x := by
  unfold uCurve uR1 uR2
  simp only [h, true_and, H.C12 h, false_and, if_false]

theorem UHyp.uCurve_C2 {x : D} (h : Γ.crossingOf x ∈ Γ.uC2 d k) :
    Γ.uCurve d k x = if Γ.curve x = Γ.curve (Γ.ub2 d) then Γ.curve (Γ.ub1 d) else Γ.curve x := by
  have h1 : Γ.crossingOf x ∉ Γ.uC1 d k := fun h1 => H.C12 h1 h
  unfold uCurve uR1 uR2
  simp only [h1, false_and, if_false, h, true_and]

theorem UHyp.uCurve_C0 {x : D} (h1 : Γ.crossingOf x ∉ Γ.uC1 d k)
    (h2 : Γ.crossingOf x ∉ Γ.uC2 d k) : Γ.uCurve d k x = Γ.curve x := by
  unfold uCurve uR1 uR2
  simp only [h1, false_and, if_false, h2]

theorem UHyp.uCurve_σσ (x : D) : Γ.uCurve d k (Γ.σ (Γ.σ x)) = Γ.uCurve d k x := by
  simp only [uCurve, uR1, uR2, j_crossingOf_σ, j_curve_σσ]

theorem UHyp.uCurve_σ (x : D) : Γ.uCurve d k (Γ.σ x) ≠ Γ.uCurve d k x := by
  have hne := Γ.isSConf.curve_σ x
  have hcx : Γ.crossingOf (Γ.σ x) = Γ.crossingOf x := j_crossingOf_σ _ _
  by_cases h1 : Γ.crossingOf x ∈ Γ.uC1 d k
  · have h1' : Γ.crossingOf (Γ.σ x) ∈ Γ.uC1 d k := hcx ▸ h1
    rw [H.uCurve_C1 h1, H.uCurve_C1 h1']
    have n1 := H.C1_curve h1
    have n1' := H.C1_curve h1'
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) hne
    · exact n1.symm
    · exact n1'
    · exact hne
  by_cases h2 : Γ.crossingOf x ∈ Γ.uC2 d k
  · have h2' : Γ.crossingOf (Γ.σ x) ∈ Γ.uC2 d k := hcx ▸ h2
    rw [H.uCurve_C2 h2, H.uCurve_C2 h2']
    have n1 := H.C2_curve h2
    have n1' := H.C2_curve h2'
    split_ifs with ha hb hb
    · exact absurd (ha.trans hb.symm) hne
    · exact n1.symm
    · exact n1'
    · exact hne
  rw [H.uCurve_C0 h1 h2, H.uCurve_C0 (hcx ▸ h1) (hcx ▸ h2)]
  exact hne

/-! ### The straight walks of the new curves -/

/-- The walk of the new curve labelled `γ2` (from `σ d`) reaches every dart of old `γ2` beyond
`v`. -/
theorem UHyp.reach1 {z : D} (hz : Γ.straight.SameCycle (Γ.ub2 d) z) (hR : ¬ Γ.uR2 d k z) :
    H.st.SameCycle (Γ.ub1 d) z ∨ H.st.SameCycle (Γ.ub1 d) (Γ.σ (Γ.σ z)) := by
  obtain ⟨m, hm, rfl⟩ := u_exists_idx hz
  rcases Nat.lt_or_ge m k with h1 | h1
  · exact absurd (H.uR2_iff.2 ⟨m, h1, Or.inl rfl⟩) hR
  rcases Nat.eq_or_lt_of_le h1 with h2 | h2
  · subst h2
    right
    rw [H.leg2, Γ.j_σ4]
    have e : H.st a = Γ.ub1 d := H.st_uM0
    rw [← e]; exact (u_sameCycle_apply _ _).symm
  · left
    rw [← H.tail2_st (by omega) hm, ← H.leg1_turn, ← u_pow_add]
    exact u_sameCycle_pow _ _ _

theorem UHyp.reach2 {z : D} (hz : Γ.straight.SameCycle (Γ.ub1 d) z) (hR : ¬ Γ.uR1 d k z) :
    H.st.SameCycle (Γ.ub2 d) z ∨ H.st.SameCycle (Γ.ub2 d) (Γ.σ (Γ.σ z)) := by
  obtain ⟨m, hm, rfl⟩ := u_exists_idx hz
  rcases Nat.lt_or_ge m k with h1 | h1
  · exact absurd (H.uR1_iff.2 ⟨m, h1, Or.inl rfl⟩) hR
  rcases Nat.eq_or_lt_of_le h1 with h2 | h2
  · subst h2
    right
    rw [H.leg1]
    have e : H.st (Γ.σ (Γ.σ (Γ.σ a))) = Γ.ub2 d := H.st_uM3
    rw [← e]; exact (u_sameCycle_apply _ _).symm
  · left
    rw [← H.tail1_st (by omega) hm, ← H.leg2_turn, ← u_pow_add]
    exact u_sameCycle_pow _ _ _

theorem UHyp.uR2_σσ {z : D} : Γ.uR2 d k (Γ.σ (Γ.σ z)) ↔ Γ.uR2 d k z := by
  unfold uR2; rw [j_crossingOf_σ, j_crossingOf_σ, j_curve_σσ]

theorem UHyp.uR1_σσ {z : D} : Γ.uR1 d k (Γ.σ (Γ.σ z)) ↔ Γ.uR1 d k z := by
  unfold uR1; rw [j_crossingOf_σ, j_crossingOf_σ, j_curve_σσ]

/-- Every dart labelled `γ2` lies on the walk from `σ d` (in one of its two directions). -/
theorem UHyp.base2 {y : D} (hy : Γ.uCurve d k y = Γ.curve (Γ.ub2 d)) :
    H.st.SameCycle (Γ.ub1 d) y ∨ H.st.SameCycle (Γ.ub1 d) (Γ.σ (Γ.σ y)) := by
  by_cases h1 : Γ.uR1 d k y
  · obtain ⟨j, hj, rfl | rfl⟩ := H.uR1_iff.1 h1
    · left; rw [← H.leg1_st (by omega)]; exact u_sameCycle_pow _ _ _
    · right; rw [Γ.j_σ4, ← H.leg1_st (by omega)]; exact u_sameCycle_pow _ _ _
  have h2 : ¬ Γ.uR2 d k y := fun h2 => by
    unfold uCurve at hy; rw [if_neg h1, if_pos h2] at hy; exact H.c12 hy
  have hc : Γ.curve y = Γ.curve (Γ.ub2 d) := by
    unfold uCurve at hy; rwa [if_neg h1, if_neg h2] at hy
  rcases Γ.isSConf.straight (Γ.ub2 d) y hc.symm with h | h
  · exact H.reach1 h h2
  · rcases H.reach1 h (by rwa [H.uR2_σσ]) with h' | h'
    · exact Or.inr h'
    · rw [Γ.j_σ4] at h'; exact Or.inl h'

theorem UHyp.base1 {y : D} (hy : Γ.uCurve d k y = Γ.curve (Γ.ub1 d)) :
    H.st.SameCycle (Γ.ub2 d) y ∨ H.st.SameCycle (Γ.ub2 d) (Γ.σ (Γ.σ y)) := by
  by_cases h2 : Γ.uR2 d k y
  · obtain ⟨j, hj, rfl | rfl⟩ := H.uR2_iff.1 h2
    · left; rw [← H.leg2_st (by omega)]; exact u_sameCycle_pow _ _ _
    · right; rw [Γ.j_σ4, ← H.leg2_st (by omega)]; exact u_sameCycle_pow _ _ _
  have h1 : ¬ Γ.uR1 d k y := fun h1 => by
    unfold uCurve at hy; rw [if_pos h1] at hy; exact H.c12 hy.symm
  have hc : Γ.curve y = Γ.curve (Γ.ub1 d) := by
    unfold uCurve at hy; rwa [if_neg h1, if_neg h2] at hy
  rcases Γ.isSConf.straight (Γ.ub1 d) y hc.symm with h | h
  · exact H.reach2 h h1
  · rcases H.reach2 h (by rwa [H.uR1_σσ]) with h' | h'
    · exact Or.inr h'
    · rw [Γ.j_σ4] at h'; exact Or.inl h'

/-- Darts of other curves: their walks do not change. -/
theorem UHyp.other_sc {y z : D} (hy1 : Γ.curve y ≠ Γ.curve (Γ.ub1 d))
    (hy2 : Γ.curve y ≠ Γ.curve (Γ.ub2 d)) (h : Γ.straight.SameCycle y z) : H.st.SameCycle y z := by
  obtain ⟨m, rfl⟩ := h.exists_nat_pow_eq
  rw [← u_pow_eq_of_avoid (M := fun x => ∃ i, Γ.uM d a i = x) (H.st_eq_of_notM rfl) y m ?_]
  · exact u_sameCycle_pow _ _ _
  intro i _ ⟨j, hj⟩
  have hc := congrArg Γ.curve hj
  rw [H.c_uM, u_curve_pow] at hc
  split_ifs at hc
  · exact hy2 hc.symm
  · exact hy1 hc.symm

theorem UHyp.combine {b x y : D}
    (hx : H.st.SameCycle b x ∨ H.st.SameCycle b (Γ.σ (Γ.σ x)))
    (hy : H.st.SameCycle b y ∨ H.st.SameCycle b (Γ.σ (Γ.σ y))) :
    H.st.SameCycle x y ∨ H.st.SameCycle x (Γ.σ (Γ.σ y)) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (hx.symm.trans hy)
  · exact Or.inr (hx.symm.trans hy)
  · right
    have := H.sc_σσ (hx.symm.trans hy)
    rwa [Γ.j_σ4] at this
  · left
    have := H.sc_σσ (hx.symm.trans hy)
    rwa [Γ.j_σ4, Γ.j_σ4] at this

/-- The axiom `straight` of the untangled configuration. -/
theorem UHyp.straight_ax (x y : D) (h : Γ.uCurve d k x = Γ.uCurve d k y) :
    H.st.SameCycle x y ∨ H.st.SameCycle x (Γ.σ (Γ.σ y)) := by
  by_cases h2 : Γ.uCurve d k x = Γ.curve (Γ.ub2 d)
  · exact H.combine (H.base2 h2) (H.base2 (h ▸ h2))
  by_cases h1 : Γ.uCurve d k x = Γ.curve (Γ.ub1 d)
  · exact H.combine (H.base1 h1) (H.base1 (h ▸ h1))
  have hx : Γ.uCurve d k x = Γ.curve x := by
    unfold uCurve at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ <;> simp_all
  have hy : Γ.uCurve d k y = Γ.curve y := by
    rw [h] at h1 h2
    unfold uCurve at h1 h2 ⊢
    split_ifs at h1 h2 ⊢ <;> simp_all
  rw [hx] at h1 h2 h
  rw [hy] at h
  rcases Γ.isSConf.straight x y h with h' | h'
  · exact Or.inl (H.other_sc h1 h2 h')
  · exact Or.inr (H.other_sc h1 h2 h')

end Hyp

end SConf

end Pca.Sweep
