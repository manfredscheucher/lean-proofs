/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package M, helpers: a triangle with a side on the sweeping curve

The local facts on a triangle `T` that the flip needs (the `SConf` versions of the triangle
facts N1-N3, O1, O2 of `Pca/Flip.lean`). In `Pca/Flip.lean` they come from the arrangement
axioms (intersecting: a curve has `2(n-1) ≥ 4` crossings). In a sweep configuration a curve
may have only two crossings, so O1/O2 need an argument: they reduce to "the straight walk of a
side of `T` does not close after two steps" (`m_tri_straight_straight_ne`), which follows from
the side function of `S` (a parity argument: walking along a curve, the side changes exactly at
the crossings with `S`; it uses that `T` has a side on `S`).
-/
import Pca.Sweep.M_Basic

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable (Γ : SConf n D)

/-! ## Straight walks never come back reversed -/

theorem m_α_mul_straight : Γ.α * Γ.straight * Γ.α⁻¹ = Γ.straight⁻¹ := by
  have hα : Γ.α⁻¹ = Γ.α := by
    ext y; rw [Perm.inv_eq_iff_eq, m_α_α]
  ext y
  rw [hα, Perm.mul_apply, Perm.mul_apply, Perm.inv_def, m_straight_symm_apply, m_straight_apply,
    m_α_α]

/-- The straight walk of `y` never contains the reverse dart `α y`. -/
theorem m_not_sameCycle_α (y : D) : ¬ Γ.straight.SameCycle y (Γ.α y) := by
  rintro ⟨m, hm⟩
  have key : ∀ k : ℤ, Γ.α ((Γ.straight ^ k) y) = (Γ.straight ^ (m - k)) y := by
    intro k
    have h1 : Γ.α * Γ.straight ^ k * Γ.α⁻¹ = Γ.straight ^ (-k) := by
      rw [← conj_zpow, m_α_mul_straight, inv_zpow, zpow_neg]
    have h2 : Γ.α ((Γ.straight ^ k) y) = (Γ.straight ^ (-k)) (Γ.α y) := by
      rw [← h1]; simp [Perm.mul_apply]
    rw [h2, ← hm, ← Perm.mul_apply, ← zpow_add, neg_add_eq_sub]
  rcases Int.even_or_odd' m with ⟨j, hj | hj⟩
  · have := key j
    rw [show m - j = j by omega] at this
    exact Γ.m_α_ne _ this
  · have := key j
    rw [show m - j = 1 + j by omega, zpow_one_add, Perm.mul_apply] at this
    exact Γ.m_σσ_ne (Γ.α ((Γ.straight ^ j) y)) (by rw [← m_straight_apply]; exact this.symm)

/-! ## Triangles -/

/-- `T = cellOf t` is a triangle with the side `t` on `S`. -/
structure MTri (t : D) : Prop where
  size : (Γ.cellOf t).size = 3
  curve_t : Γ.curve t = Γ.S

/-- `y` is at a corner of the cell of `t`. -/
def MCorner (t y : D) : Prop := ∃ e, Γ.cellOf e = Γ.cellOf t ∧ Γ.crossingOf e = Γ.crossingOf y

variable {Γ} {t : D} (hT : Γ.MTri t)
include hT

section Tri

variable {b : D} (hb : Γ.cellOf b = Γ.cellOf t)
include hb

theorem m_tri_period : period Γ.φ b = 3 := by
  rw [← m_size_cellOf, hb, hT.size]

theorem m_tri_φφφ : Γ.φ (Γ.φ (Γ.φ b)) = b := by
  have := iterate_period Γ.φ b
  rw [m_tri_period hT hb] at this
  simpa using this

theorem m_tri_orbitList : orbitList Γ.φ b = [b, Γ.φ b, Γ.φ (Γ.φ b)] := by
  simp [orbitList, m_tri_period hT hb, List.range_succ]

theorem m_tri_mem_iff {e : D} :
    Γ.cellOf e = Γ.cellOf t ↔ e = b ∨ e = Γ.φ b ∨ e = Γ.φ (Γ.φ b) := by
  rw [← hb, m_cellOf_eq_iff, Perm.sameCycle_comm, ← mem_orbitList,
    m_tri_orbitList hT hb]
  simp

theorem m_tri_darts_ne : b ≠ Γ.φ b ∧ b ≠ Γ.φ (Γ.φ b) ∧ Γ.φ b ≠ Γ.φ (Γ.φ b) := by
  have h := orbitList_nodup Γ.φ b
  rw [m_tri_orbitList hT hb] at h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact ⟨h.1.1, h.1.2, h.2.1⟩

omit hT in
theorem m_tri_φ : Γ.cellOf (Γ.φ b) = Γ.cellOf t := by rw [m_cellOf_φ, hb]

omit hT in
theorem m_tri_φφ : Γ.cellOf (Γ.φ (Γ.φ b)) = Γ.cellOf t := by rw [m_cellOf_φ, m_cellOf_φ, hb]

theorem m_tri_σσσ : Γ.σ (Γ.σ (Γ.σ b)) = Γ.α (Γ.φ (Γ.φ b)) := by
  have h := m_tri_φφφ hT hb
  rw [Γ.m_φ_apply (Γ.φ (Γ.φ b))] at h
  exact (Γ.m_eq_σσσ_of_σ_eq h).symm

theorem m_tri_σ : Γ.σ b = Γ.straight (Γ.φ (Γ.φ b)) := by
  rw [m_straight_apply, ← m_tri_σσσ hT hb, Γ.m_σ4]

/-- N1: the reverse of a side of `T` is not in `T`. -/
theorem m_tri_α_ne : Γ.cellOf (Γ.α b) ≠ Γ.cellOf t := by
  intro h
  rcases (m_tri_mem_iff hT hb).1 h with h | h | h
  · exact Γ.m_α_ne b h
  · rw [m_φ_apply] at h; exact Γ.m_σ_ne _ h.symm
  · have h2 : Γ.φ (Γ.α b) = b := by rw [h, m_tri_φφφ hT hb]
    rw [m_φ_α] at h2
    exact Γ.m_σ_ne b h2

end Tri

theorem m_tri_crossing_φ_ne {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    Γ.crossingOf (Γ.φ b) ≠ Γ.crossingOf b := by
  intro h
  rw [m_crossingOf_φ] at h
  rcases Γ.m_eq_or_eq_σσ h.symm (Γ.m_curve_α b).symm with h1 | h1
  · exact Γ.m_α_ne b h1
  · -- `α b = σ² b`: then `φ b = σ³ b = α (φ² b)` lies in `T`
    have h2 : Γ.φ b = Γ.α (Γ.φ (Γ.φ b)) := by
      show Γ.σ (Γ.α b) = _
      rw [h1, m_tri_σσσ hT hb]
    exact m_tri_α_ne hT (m_tri_φφ hb) (by rw [← h2, m_tri_φ hb])

theorem m_tri_crossing_φφ_ne {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    Γ.crossingOf (Γ.φ (Γ.φ b)) ≠ Γ.crossingOf b := by
  intro h
  have := m_tri_crossing_φ_ne hT (m_tri_φφ hb)
  rw [m_tri_φφφ hT hb] at this
  exact this h.symm

theorem m_tri_crossing_φ_φφ_ne {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    Γ.crossingOf (Γ.φ (Γ.φ b)) ≠ Γ.crossingOf (Γ.φ b) :=
  m_tri_crossing_φ_ne hT (m_tri_φ hb)

/-- The darts of `T` lie at three distinct crossings. -/
theorem m_tri_injOn_crossing {b e : D} (hb : Γ.cellOf b = Γ.cellOf t)
    (he : Γ.cellOf e = Γ.cellOf t) (h : Γ.crossingOf e = Γ.crossingOf b) : e = b := by
  rcases (m_tri_mem_iff hT hb).1 he with rfl | rfl | rfl
  · rfl
  · exact absurd h (m_tri_crossing_φ_ne hT hb)
  · exact absurd h (m_tri_crossing_φφ_ne hT hb)

theorem m_tri_curve_φφ_ne {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    Γ.curve (Γ.φ (Γ.φ b)) ≠ Γ.curve b := by
  intro h
  have := Γ.m_curve_φ_ne (Γ.φ (Γ.φ b))
  rw [m_tri_φφφ hT hb] at this
  exact this h.symm

/-- The darts of `T` lie on three distinct curves. -/
theorem m_tri_injOn_curve {b e : D} (hb : Γ.cellOf b = Γ.cellOf t)
    (he : Γ.cellOf e = Γ.cellOf t) (h : Γ.curve e = Γ.curve b) : e = b := by
  rcases (m_tri_mem_iff hT hb).1 he with rfl | rfl | rfl
  · rfl
  · exact absurd h (Γ.m_curve_φ_ne b)
  · exact absurd h (m_tri_curve_φφ_ne hT hb)

/-- N3: the opposite dart `σ² b` at a corner is not in `T`. -/
theorem m_tri_σσ_ne {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    Γ.cellOf (Γ.σ (Γ.σ b)) ≠ Γ.cellOf t := fun h =>
  Γ.m_σσ_ne b (m_tri_injOn_crossing hT hb h (Γ.m_crossingOf_σσ b))

/-- N2: `straight b` is not in `T`. -/
theorem m_tri_straight_ne {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    Γ.cellOf (Γ.straight b) ≠ Γ.cellOf t := by
  intro h
  have h1 := m_tri_injOn_crossing hT (m_tri_φ hb) h
    (by rw [m_crossingOf_straight, m_crossingOf_φ])
  have hc := Γ.m_curve_φ_ne b
  rw [← h1, m_curve_straight] at hc
  exact hc rfl

/-- The curve of `b` does not pass the corner of `T` opposite to the side `b`. -/
theorem m_tri_curve_ne_at_φφ {b z : D} (hb : Γ.cellOf b = Γ.cellOf t)
    (hz : Γ.crossingOf z = Γ.crossingOf (Γ.φ (Γ.φ b))) : Γ.curve z ≠ Γ.curve b := by
  have hσ : Γ.curve (Γ.σ (Γ.φ (Γ.φ b))) = Γ.curve (Γ.φ b) := by
    rw [m_tri_σ hT (m_tri_φφ hb), m_curve_straight, m_tri_φφφ hT (m_tri_φ hb)]
  have h0 := (Γ.m_crossingOf_eq_iff).1 hz.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
  have h1 := m_tri_curve_φφ_ne hT hb
  have h2 := Γ.m_curve_φ_ne b
  rcases h0 with rfl | rfl | rfl | rfl
  · exact h1
  · rw [hσ]; exact h2
  · rw [m_curve_σσ]; exact h1
  · rw [m_curve_σσσ, hσ]; exact h2

/-- Exactly one side of `T` lies on `S` (the side `t`). -/
theorem m_tri_mS {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    Γ.mS b + Γ.mS (Γ.φ b) + Γ.mS (Γ.φ (Γ.φ b)) = 1 := by
  have ht := hT.curve_t
  have h1 : ∀ e, Γ.cellOf e = Γ.cellOf t → e ≠ t → Γ.mS e = 0 := by
    intro e he hne
    rw [mS, if_neg]
    intro h
    exact hne (m_tri_injOn_curve hT rfl he (h.trans ht.symm))
  have hne := m_tri_darts_ne hT hb
  rcases (m_tri_mem_iff hT hb).1 (rfl : Γ.cellOf t = Γ.cellOf t) with h | h | h
  · rw [h1 _ (m_tri_φ hb) (by rw [h]; exact Ne.symm hne.1),
      h1 _ (m_tri_φφ hb) (by rw [h]; exact Ne.symm hne.2.1), mS, if_pos (h ▸ ht)]
    decide
  · rw [h1 _ hb (by rw [h]; exact hne.1),
      h1 _ (m_tri_φφ hb) (by rw [h]; exact Ne.symm hne.2.2), mS, if_pos (h ▸ ht)]
    decide
  · rw [h1 _ hb (by rw [h]; exact hne.2.1),
      h1 _ (m_tri_φ hb) (by rw [h]; exact hne.2.2), mS, if_pos (h ▸ ht)]
    decide

/-! ## Parity: the straight walk of a side of `T` does not close after two steps -/

omit hT in
theorem m_iterate_ne_of_lt {f : Perm D} {y : D} {m : ℕ} (h0 : 0 < m) (hm : m < period f y) :
    (f^[m]) y ≠ y := fun h => Nat.find_min _ hm ⟨h0, h⟩

omit hT in
/-- Two steps on a straight walk of period two stay in `{b, straight b}`. -/
theorem m_sameCycle_of_period_two {b w : D} (h2 : Γ.straight (Γ.straight b) = b)
    (h : Γ.straight.SameCycle b w) : w = b ∨ w = Γ.straight b := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    rw [pow_succ', Perm.mul_apply]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl h2

/-- **Parity.** The straight walk of a side `b` of `T` does not close after two steps (else the
curve of `b`, or for `b` on `S` the curve of `φ b`, would cross `S` an odd number of times). -/
theorem m_tri_straight_straight_ne {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    Γ.straight (Γ.straight b) ≠ b := by
  intro h2
  have hαs : Γ.α (Γ.straight b) = Γ.σ (Γ.σ b) := by
    calc Γ.α (Γ.straight b) = Γ.σ (Γ.σ (Γ.σ (Γ.σ (Γ.α (Γ.straight b))))) := (Γ.m_σ4 _).symm
      _ = Γ.σ (Γ.σ b) := by rw [← m_straight_apply, h2]
  have hx1 : ∀ x : ZMod 2, x ≠ x + 1 := by decide
  by_cases hc : Γ.curve b = Γ.S
  · -- `b` is the side on `S`: then `S` has only the crossings at the ends of `b`, and the curve
    -- of `φ b` crosses `S` exactly once
    set y := Γ.φ b with hy
    have hA : ∀ e, Γ.curve e = Γ.S →
        Γ.crossingOf e = Γ.crossingOf b ∨ Γ.crossingOf e = Γ.crossingOf (Γ.α b) := by
      intro e he
      rcases Γ.isSConf.straight b e (hc.trans he.symm) with h | h
      · rcases m_sameCycle_of_period_two h2 h with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Γ.m_crossingOf_straight b)
      · rcases m_sameCycle_of_period_two h2 h with h' | h'
        · left; rw [← Γ.m_crossingOf_σσ e, h']
        · right; rw [← Γ.m_crossingOf_σσ e, h', m_crossingOf_straight]
    have hcy : Γ.curve y ≠ Γ.curve b := Γ.m_curve_φ_ne b
    have hcσ : Γ.curve (Γ.σ b) = Γ.curve (Γ.φ (Γ.φ b)) := by
      rw [m_tri_σ hT hb, m_curve_straight]
    have hcyσ : Γ.curve y ≠ Γ.curve (Γ.σ b) := by
      rw [hcσ]; exact fun h => Γ.m_curve_φ_ne (Γ.φ b) h.symm
    have hB : ∀ z, Γ.curve z = Γ.curve y → Γ.mS (Γ.σ (Γ.α z)) = 1 →
        Γ.α z = Γ.σ (Γ.α b) ∨ Γ.α z = Γ.σ (Γ.σ (Γ.σ (Γ.α b))) := by
      intro z hz hS
      have hS' : Γ.curve (Γ.σ (Γ.α z)) = Γ.S := by
        by_contra h; rw [mS, if_neg h] at hS; exact zero_ne_one hS
      have hzc : Γ.curve (Γ.α z) = Γ.curve y := by rw [m_curve_α, hz]
      rcases hA _ hS' with h | h <;> rw [m_crossingOf_σ] at h
      · exfalso
        have h0 := (Γ.m_crossingOf_eq_iff).1 h.symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
        rcases h0 with h0 | h0 | h0 | h0 <;> rw [h0] at hzc
        · exact hcy hzc.symm
        · exact hcyσ hzc.symm
        · rw [m_curve_σσ] at hzc; exact hcy hzc.symm
        · rw [m_curve_σσσ] at hzc; exact hcyσ hzc.symm
      · have h0 := (Γ.m_crossingOf_eq_iff).1 h.symm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
        rcases h0 with h0 | h0 | h0 | h0
        · rw [h0, m_curve_α] at hzc; exact absurd hzc.symm hcy
        · exact Or.inl h0
        · rw [h0, m_curve_σσ, m_curve_α] at hzc; exact absurd hzc.symm hcy
        · exact Or.inr h0
    set z0 := Γ.α (Γ.σ (Γ.σ (Γ.σ (Γ.α b)))) with hz0
    have hsz0 : Γ.straight z0 = y := by
      rw [hz0, m_straight_apply, m_α_α, Γ.m_σ4]; rfl
    have hC := Γ.m_not_sameCycle_α y
    set p := period Γ.straight y with hp
    have hp0 := period_pos Γ.straight y
    have hstep : ∀ k, k + 1 < p → Γ.mS (Γ.σ (Γ.α ((Γ.straight^[k]) y))) = 0 := by
      intro k hk
      by_contra hne
      have hS : Γ.mS (Γ.σ (Γ.α ((Γ.straight^[k]) y))) = 1 := by
        revert hne; generalize Γ.mS _ = x; revert x; decide
      have hcur : Γ.curve ((Γ.straight^[k]) y) = Γ.curve y := by
        clear hS hk hne
        induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply', m_curve_straight, ih]
      rcases hB _ hcur hS with h | h
      · apply hC
        have : (Γ.straight^[k]) y = Γ.α y := by
          rw [← Γ.m_α_α ((Γ.straight^[k]) y), h]; rfl
        rw [← this, ← Perm.coe_pow]
        exact Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)
      · have : (Γ.straight^[k]) y = z0 := by rw [hz0, ← h, m_α_α]
        have h1 := m_iterate_ne_of_lt (f := Γ.straight) (y := y) (m := k + 1) (by omega) hk
        rw [Function.iterate_succ_apply', this, hsz0] at h1
        exact h1 rfl
    have hconst : ∀ k, k + 1 ≤ p → Γ.mSide ((Γ.straight^[k]) y) = Γ.mSide y := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        rw [Function.iterate_succ_apply', m_side_straight, hstep k (by omega), add_zero,
          ih (by omega)]
    have hlast : (Γ.straight^[p - 1]) y = z0 := by
      apply Γ.straight.injective
      rw [hsz0, ← Function.iterate_succ_apply' (f := Γ.straight), Nat.succ_eq_add_one,
        Nat.sub_add_cancel hp0]
      exact iterate_period Γ.straight y
    have hfin := iterate_period Γ.straight y
    rw [← hp, show p = (p - 1) + 1 by omega, Function.iterate_succ_apply', hlast] at hfin
    have hS1 : Γ.mS (Γ.σ (Γ.α z0)) = 1 := by
      rw [hz0, m_α_α, Γ.m_σ4, m_mS_α, mS, if_pos hc]
    have := hconst (p - 1) (by omega)
    rw [hlast] at this
    have h3 := Γ.m_side_straight z0
    rw [hsz0, hS1, this] at h3
    exact hx1 _ h3
  · have hS := m_tri_mS hT hb
    rw [mS, if_neg hc, zero_add] at hS
    have h3 := Γ.m_side_straight (Γ.straight b)
    rw [h2, Γ.m_side_straight b, hαs] at h3
    have e1 : Γ.mS (Γ.σ (Γ.α b)) = Γ.mS (Γ.φ b) := rfl
    have e2 : Γ.mS (Γ.σ (Γ.σ (Γ.σ b))) = Γ.mS (Γ.φ (Γ.φ b)) := by
      rw [m_tri_σσσ hT hb, m_mS_α]
    rw [e1, e2, add_assoc, hS] at h3
    exact hx1 _ h3

/-! ## Corners of `T` -/

omit hT in
theorem m_isCorner_of_mem {y : D} (hy : Γ.cellOf y = Γ.cellOf t) : Γ.MCorner t y :=
  ⟨y, hy, rfl⟩

omit hT in
theorem m_isCorner_α_of_mem {y : D} (hy : Γ.cellOf y = Γ.cellOf t) : Γ.MCorner t (Γ.α y) :=
  ⟨Γ.φ y, m_tri_φ hy, Γ.m_crossingOf_φ y⟩

omit hT in
theorem m_isCorner_σσ {y : D} : Γ.MCorner t (Γ.σ (Γ.σ y)) ↔ Γ.MCorner t y := by
  rw [MCorner, MCorner, m_crossingOf_σσ]

omit hT in
theorem m_isCorner_φ {y : D} : Γ.MCorner t (Γ.φ y) ↔ Γ.MCorner t (Γ.α y) := by
  rw [MCorner, MCorner, m_crossingOf_φ]

omit hT in
theorem m_not_mem_of_not_corner {y : D} (hy : ¬ Γ.MCorner t y) : Γ.cellOf y ≠ Γ.cellOf t :=
  fun h => hy (m_isCorner_of_mem h)

/-- Every dart at a corner of `T` is `b`, `α b`, `straight b` or `σ² b` for a dart `b` of `T`. -/
theorem m_corner_cases {y : D} (hy : Γ.MCorner t y) :
    ∃ b, Γ.cellOf b = Γ.cellOf t ∧
      (y = b ∨ y = Γ.α b ∨ y = Γ.straight b ∨ y = Γ.σ (Γ.σ b)) := by
  obtain ⟨c, hc, hcy⟩ := hy
  have hφφ := m_tri_φφ hc
  have h0 := (Γ.m_crossingOf_eq_iff).1 hcy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
  rcases h0 with h | h | h | h
  · exact ⟨c, hc, Or.inl h⟩
  · exact ⟨_, hφφ, Or.inr (Or.inr (Or.inl (h.trans (m_tri_σ hT hc))))⟩
  · exact ⟨c, hc, Or.inr (Or.inr (Or.inr h))⟩
  · exact ⟨_, hφφ, Or.inr (Or.inl (h.trans (m_tri_σσσ hT hc)))⟩

/-- O1: the far end of `straight b` is not a corner of `T`. -/
theorem m_not_corner_end_straight {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    ¬ Γ.MCorner t (Γ.α (Γ.straight b)) := by
  rintro ⟨e, he, hx⟩
  have hcur : Γ.curve (Γ.α (Γ.straight b)) = Γ.curve b := by rw [m_curve_α, m_curve_straight]
  rcases (m_tri_mem_iff hT hb).1 he with rfl | rfl | rfl
  · rcases Γ.m_eq_or_eq_σσ hx hcur.symm with h | h
    · have h' : Γ.straight e = Γ.α e := by have := congrArg Γ.α h; rwa [m_α_α] at this
      exact Γ.m_σσ_ne (Γ.α e) (by rw [← m_straight_apply, h'])
    · have h' : Γ.straight (Γ.straight e) = e := by
        rw [Γ.m_straight_apply (Γ.straight e), h, Γ.m_σ4]
      exact m_tri_straight_straight_ne hT hb h'
  · rw [m_crossingOf_φ, ← m_crossingOf_straight] at hx
    rcases Γ.m_eq_or_eq_σσ hx (Γ.m_curve_α _).symm with h | h
    · exact Γ.m_α_ne _ h
    · have h1 : Γ.straight (Γ.straight b) = Γ.straight b := by
        rw [Γ.m_straight_apply (Γ.straight b), h, Γ.m_σ4]
      have h2 : Γ.straight b = b := Γ.straight.injective h1
      exact m_tri_straight_ne hT hb (by rw [h2, hb])
  · exact m_tri_curve_ne_at_φφ hT hb hx.symm hcur

/-- O2: the far end of `σ² b` is not a corner of `T`. -/
theorem m_not_corner_end_σσ {b : D} (hb : Γ.cellOf b = Γ.cellOf t) :
    ¬ Γ.MCorner t (Γ.α (Γ.σ (Γ.σ b))) := by
  rintro ⟨e, he, hx⟩
  have hcur : Γ.curve (Γ.α (Γ.σ (Γ.σ b))) = Γ.curve b := by rw [m_curve_α, m_curve_σσ]
  rcases (m_tri_mem_iff hT hb).1 he with rfl | rfl | rfl
  · rcases Γ.m_eq_or_eq_σσ hx hcur.symm with h | h
    · have h' : Γ.σ (Γ.σ e) = Γ.α e := by have := congrArg Γ.α h; rwa [m_α_α] at this
      have h1 : Γ.straight e = e := by
        rw [m_straight_apply, ← h', Γ.m_σ4]
      exact m_tri_straight_ne hT hb (by rw [h1, hb])
    · exact Γ.m_α_ne _ h
  · rw [m_crossingOf_φ] at hx
    rcases Γ.m_eq_or_eq_σσ hx (by rw [hcur, m_curve_α]) with h | h
    · have := Γ.isSConf.α_α (Γ.σ (Γ.σ b))
      rw [h, m_α_α] at this
      exact Γ.m_σσ_ne b this.symm
    · have h1 : Γ.straight (Γ.straight b) = b := by
        rw [Γ.m_straight_apply (Γ.straight b), Γ.m_straight_apply b, ← h, m_α_α, Γ.m_σ4]
      exact m_tri_straight_straight_ne hT hb h1
  · exact m_tri_curve_ne_at_φφ hT hb hx.symm hcur

end SConf

end Pca.Sweep
