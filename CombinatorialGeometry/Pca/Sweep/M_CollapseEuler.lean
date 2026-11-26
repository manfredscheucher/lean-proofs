/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package M, helpers: Euler, side function and connectivity of the collapsed map

* connectivity: the hypothesis `hconn` (the kept darts are connected by `σ` and joined
  segments, `MStep`) is exactly connectivity of the collapsed map (`m_conn_transport`);
* Euler: `V' = V - 2`, `E' = E - 4` (counting darts), `F' ≥ F - 2` (every old cell except the
  digon and the cell below `S` right of the digon has a kept dart in a new cell, `mGc`), and
  `V' - E' + F' ≤ 2` for every connected map (`Pca.MapFacts.euler_le_two`); so `V' - E' + F' = 2`;
* the side function: the side of the old cell (well defined: the two cells below `S` beside the
  digon that merge have the same side, `m_side_p₁_q₂`).
-/
import Pca.Sweep.M_CollapseConf

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {d : D}

/-- One step of the collapsed map, in terms of `Γ`: `σ`, or a joined segment (go straight
through deleted crossings). -/
def MStep (Γ : SConf n D) (d a b : D) : Prop :=
  Γ.mKept d a ∧ Γ.mKept d b ∧ (b = Γ.σ a ∨
    ∃ k, (∀ i < k, ¬ Γ.mKept d (Γ.α ((Γ.straight ^ i) a))) ∧ b = Γ.α ((Γ.straight ^ k) a))

variable (h : Γ.EmptyHumpAt d) (hS : ∃ e, Γ.curve e = Γ.S ∧ Γ.mKept d e)
  (hc : ∃ e, Γ.curve e = Γ.curve (Γ.σ d) ∧ Γ.mKept d e)
include h hS hc

/-! ## The joined segments -/

/-- At an outer dart, the joined segment has three pieces. -/
theorem m_outer_step {y : D} (hy : y = Γ.mp₁ d ∨ y = Γ.mq₁ d ∨ y = Γ.mp₂ d ∨ y = Γ.mq₂ d) :
    ¬ Γ.mKept d (Γ.α y) ∧ ¬ Γ.mKept d (Γ.α (Γ.straight y)) ∧
      Γ.α (Γ.straight (Γ.straight y)) = Γ.mαc d y := by
  refine ⟨m_nk_α_outer h hy, ?_, ?_⟩
  · rcases hy with rfl | rfl | rfl | rfl
    · rw [m_s_p₁]; exact m_nk_αd h
    · rw [m_s_q₁, m_α_α]; exact m_nk_d h
    · rw [m_s_p₂, m_dig_ασ h]; exact m_nk_σσσαd h
    · rw [m_s_q₂, ← m_dig_ασ h, m_α_α]; exact m_nk_σd h
  · rcases hy with rfl | rfl | rfl | rfl
    · rw [m_s_p₁, m_αs_d, m_αc_p₁ h hS hc]
    · rw [m_s_q₁, m_αs_αd, m_αc_q₁ h]
    · rw [m_s_p₂, m_αs_σd h, m_αc_p₂ h]
    · rw [m_s_q₂, m_αs_σσσαd h, m_αc_q₂ h]

/-- The new edge involution is the joined segment (`k = 0` or `k = 2` pieces skipped). -/
theorem m_αc_eq_join (y : D) (hy : Γ.mKept d y) : ∃ k, (∀ i < k,
    ¬ Γ.mKept d (Γ.α ((Γ.straight ^ i) y))) ∧ Γ.mαc d y = Γ.α ((Γ.straight ^ k) y) := by
  rcases m_kept_cases h hS hc hy with ⟨-, -, -, -, -, he⟩ | e | e | e | e
  · exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), by rw [he, pow_zero]; rfl⟩
  all_goals
    have ho := m_outer_step h hS hc (y := y) (by simp only [e, true_or, or_true])
    refine ⟨2, fun i hi => ?_, ?_⟩
    · interval_cases i
      · rw [pow_zero]; exact ho.1
      · rw [pow_one]; exact ho.2.1
    · rw [← ho.2.2, pow_two, Perm.mul_apply]

theorem m_step_of_MStep {a b : D} (hab : Γ.MStep d a b) :
    StepRel mσc (mαcP h hS hc) ⟨a, hab.1⟩ ⟨b, hab.2.1⟩ := by
  obtain ⟨ha, hb, h1 | ⟨k, hk, hbk⟩⟩ := hab
  · exact Or.inl (Subtype.ext h1)
  · right
    apply Subtype.ext
    show b = Γ.mαc d a
    rcases m_kept_cases h hS hc ha with ⟨-, -, -, -, hk', he⟩ | e | e | e | e
    · rw [he]
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · rw [hbk, pow_zero]; rfl
      · exact absurd (by simpa using hk 0 hpos) (not_not.2 hk')
    all_goals
      have ho := m_outer_step h hS hc (y := a) (by simp only [e, true_or, or_true])
      rw [← ho.2.2]
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ 2 < k by omega) with rfl | rfl | rfl | hk2
      · rw [pow_zero] at hbk; rw [hbk] at hb; exact absurd hb ho.1
      · rw [pow_one] at hbk; rw [hbk] at hb; exact absurd hb ho.2.1
      · rw [hbk, pow_two, Perm.mul_apply]
      · exfalso
        have := hk 2 hk2
        rw [pow_two, Perm.mul_apply, ho.2.2] at this
        exact this (m_kept_αc h hS hc ha)

/-- Connectivity of the collapsed map from connectivity of the kept darts in `Γ`. -/
theorem m_conn_transport (a b : D) (hab : Relation.EqvGen (Γ.MStep d) a b) :
    (a = b ∨ (Γ.mKept d a ∧ Γ.mKept d b)) ∧ ∀ ha hb,
      Relation.EqvGen (StepRel mσc (mαcP h hS hc)) ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction hab with
  | rel x y hxy =>
    exact ⟨Or.inr ⟨hxy.1, hxy.2.1⟩, fun _ _ => .rel _ _ (m_step_of_MStep h hS hc hxy)⟩
  | refl x => exact ⟨Or.inl rfl, fun _ _ => .refl _⟩
  | symm x y _ ih =>
    refine ⟨?_, fun hx hy => (ih.2 hy hx).symm⟩
    rcases ih.1 with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr ⟨h1.2, h1.1⟩
  | trans x y z _ _ ih1 ih2 =>
    refine ⟨?_, fun hx hz => ?_⟩
    · rcases ih1.1 with rfl | h1
      · exact ih2.1
      · rcases ih2.1 with rfl | h2
        · exact Or.inr h1
        · exact Or.inr ⟨h1.1, h2.2⟩
    · have hy : Γ.mKept d y := by
        rcases ih1.1 with rfl | h1
        · exact hx
        · exact h1.2
      exact (ih1.2 hx hy).trans _ _ _ (ih2.2 hy hz)

/-! ## Cells -/

omit hS hc in
theorem m_c_q₂ : Γ.cellOf (Γ.mq₂ d) = Γ.cellOf (Γ.σ (Γ.σ (Γ.α d))) :=
  (Γ.m_cellOf_σ (Γ.σ (Γ.α d))).symm
omit hS hc in
theorem m_c_q₁ : Γ.cellOf (Γ.mq₁ d) = Γ.cellOf (Γ.σ (Γ.σ d)) := by
  rw [mq₁, ← m_cellOf_σ, ← m_dig_ασ h, ← m_cellOf_σ]
omit hS hc in
theorem m_c_p₂ : Γ.cellOf (Γ.mp₂ d) = Γ.cellOf d := by
  rw [mp₂, ← m_cellOf_σ, Γ.m_σ4]
omit hS hc in
theorem m_c_σσσd : Γ.cellOf (Γ.σ (Γ.σ (Γ.σ d))) = Γ.cellOf (Γ.mp₁ d) := Γ.m_cellOf_σ _
omit hS hc in
theorem m_c_σq₁ : Γ.cellOf (Γ.σ (Γ.mq₁ d)) = Γ.cellOf (Γ.mq₂ d) := by
  rw [m_cellOf_σ, mq₁, m_α_α, m_c_q₂ h]
omit hS hc in
theorem m_c_σp₁ : Γ.cellOf (Γ.σ (Γ.mp₁ d)) = Γ.cellOf (Γ.mq₁ d) := by
  rw [m_cellOf_σ, mp₁, m_α_α, m_c_q₁ h]
omit hS hc in
theorem m_c_σq₂ : Γ.cellOf (Γ.σ (Γ.mq₂ d)) = Γ.cellOf (Γ.mp₂ d) := by
  rw [m_cellOf_σ, mq₂, m_α_α, m_cellOf_σ, m_α_α, m_c_p₂ h]
omit hS hc in
theorem m_c_σp₂ : Γ.cellOf (Γ.σ (Γ.mp₂ d)) = Γ.cellOf (Γ.mp₁ d) := by
  rw [m_cellOf_σ, mp₂, m_α_α, m_c_σσσd h]

omit hS hc in
/-- The cells at the corners. -/
theorem m_cell_corner {z : D} (hz : ¬ Γ.mKept d z) :
    Γ.cellOf z = Γ.cellOf d ∨ Γ.cellOf z = Γ.cellOf (Γ.α d) ∨
    Γ.cellOf z = Γ.cellOf (Γ.mq₁ d) ∨ Γ.cellOf z = Γ.cellOf (Γ.mp₁ d) ∨
    Γ.cellOf z = Γ.cellOf (Γ.mq₂ d) := by
  rcases (m_not_kept_iff (Γ := Γ) (d := d)).1 hz with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (Γ.m_cellOf_σ d))
  · exact Or.inr (Or.inr (Or.inl (m_c_q₁ h).symm))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (m_c_σσσd h))))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (by rw [m_cellOf_σ, m_α_α])
  · exact Or.inr (Or.inr (Or.inr (Or.inr (m_c_q₂ h).symm)))
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [m_cellOf_σ]; rfl

omit hS hc in
/-- The old cell of a new dart, with the cell below `S` right of the digon merged into the one
left of it. -/
def mgc (Γ : SConf n D) (d z : D) : Γ.Cell :=
  if Γ.cellOf z = Γ.cellOf (Γ.mq₂ d) then Γ.cellOf (Γ.mp₁ d) else Γ.cellOf z

theorem m_mgc_step (y : Γ.MK d) :
    Γ.mgc d (((mσc * mαcP h hS hc : Perm (Γ.MK d))) y).1 = Γ.mgc d y.1 := by
  show Γ.mgc d (Γ.σ (Γ.mαc d y.1)) = Γ.mgc d y.1
  rcases m_kept_cases h hS hc y.2 with ⟨-, -, -, -, -, he⟩ | e | e | e | e
  · rw [he, ← m_φ_apply, mgc, mgc, m_cellOf_φ]
  · rw [e, m_αc_p₁ h hS hc, mgc, mgc, m_c_σq₁ h, if_pos rfl]; split_ifs <;> rfl
  · rw [e, m_αc_q₁ h, mgc, mgc, m_c_σp₁ h]
  · rw [e, m_αc_p₂ h, mgc, mgc, m_c_σq₂ h]
  · rw [e, m_αc_q₂ h, mgc, mgc, m_c_σp₂ h, if_pos rfl]; split_ifs <;> rfl

/-- The old cell (with the merge) of a new cell. -/
def mGc : Orbit (mσc * mαcP h hS hc) → Γ.Cell :=
  Quotient.lift (fun y => Γ.mgc d y.1) (fun a b hab => by
    obtain ⟨i, rfl⟩ := (hab : (mσc * mαcP h hS hc).SameCycle a b).exists_nat_pow_eq
    clear hab
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Perm.mul_apply, m_mgc_step h hS hc, ih])

theorem m_card_cells : Fintype.card Γ.Cell ≤ Fintype.card (Orbit (mσc * mαcP h hS hc)) + 2 := by
  have hsub : ((univ : Finset Γ.Cell).erase (Γ.cellOf (Γ.α d))).erase (Γ.cellOf (Γ.mq₂ d)) ⊆
      univ.image (mGc h hS hc) := by
    intro C hC
    simp only [mem_erase, mem_univ, and_true] at hC
    obtain ⟨hR, hD⟩ := hC
    rw [mem_image]
    have hpre : ∀ z (hz : Γ.mKept d z), Γ.cellOf z = C →
        ∃ a ∈ univ, mGc h hS hc a = C := by
      intro z hz hzC
      refine ⟨Orbit.mk _ ⟨z, hz⟩, mem_univ _, ?_⟩
      show Γ.mgc d z = C
      rw [mgc, if_neg (by rw [hzC]; exact hR), hzC]
    obtain ⟨z, rfl⟩ := C.exists_mk
    change Γ.cellOf z ≠ _ at hR hD
    change ∃ a ∈ univ, mGc h hS hc a = Γ.cellOf z
    by_cases hz : Γ.mKept d z
    · exact hpre z hz rfl
    rcases m_cell_corner h hz with e | e | e | e | e
    · exact hpre _ (m_kept_p₂ h hc) ((m_c_p₂ h).trans e.symm)
    · exact absurd e hD
    · exact hpre _ (m_kept_q₁ h hS) e.symm
    · exact hpre _ (m_kept_p₁ h hS) e.symm
    · exact absurd e hR
  have h1 := card_le_card hsub
  have h2 := card_image_le (s := (univ : Finset (Orbit (mσc * mαcP h hS hc)))) (f := mGc h hS hc)
  have h3 := pred_card_le_card_erase (s := (univ : Finset Γ.Cell).erase (Γ.cellOf (Γ.α d)))
    (a := Γ.cellOf (Γ.mq₂ d))
  have h4 := pred_card_le_card_erase (s := (univ : Finset Γ.Cell)) (a := Γ.cellOf (Γ.α d))
  rw [card_univ] at h2 h4
  omega

/-! ## Counting darts -/

omit hS hc in
theorem m_card_D : Fintype.card (Γ.MK d) + 8 = Fintype.card D := by
  rw [Fintype.card_subtype, ← card_univ, ← card_filter_add_card_filter_not (s := univ) (Γ.mKept d)]
  congr 1
  have hset : univ.filter (fun y => ¬ Γ.mKept d y) = orbitFinset Γ.σ d ∪ orbitFinset Γ.σ (Γ.α d) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_orbitFinset, mKept, not_and_or,
      not_not]
    rw [← Orbit.mk_eq_mk, ← Orbit.mk_eq_mk]
    exact ⟨fun h' => h'.imp Eq.symm Eq.symm, fun h' => h'.imp Eq.symm Eq.symm⟩
  rw [hset, card_union_of_disjoint, Γ.isSConf.card_crossing, Γ.isSConf.card_crossing]
  rw [disjoint_left]
  intro y h1 h2
  rw [mem_orbitFinset] at h1 h2
  exact m_dig_cross_ne h (Orbit.mk_eq_mk.2 (h1.trans h2.symm))

theorem m_card_four {X : Type u} [Fintype X] [DecidableEq X] (f : Perm X)
    (hf : ∀ y, (orbitFinset f y).card = 4) : Fintype.card X = 4 * Fintype.card (Orbit f) := by
  rw [card_eq_sum_size f]
  have : ∀ o : Orbit f, o.size = 4 := by
    intro o
    obtain ⟨y, rfl⟩ := o.exists_mk
    exact hf y
  rw [sum_congr rfl fun o _ => this o, sum_const, card_univ, smul_eq_mul, mul_comm]

/-! ## The side function -/

omit hS hc in
theorem m_side_p₁_q₂ : Γ.mSide (Γ.mp₁ d) = Γ.mSide (Γ.mq₂ d) := by
  have hd : Γ.mS d = 1 := by rw [mS, if_pos (m_dig_curve_d h)]
  have hαd : Γ.mS (Γ.α d) = 1 := by rw [m_mS_α, hd]
  have hσd : Γ.mS (Γ.σ d) = 0 := by rw [mS, if_neg (m_dig_curve_γ_ne h)]
  have hσσd : Γ.mS (Γ.σ (Γ.σ d)) = 1 := by rw [m_mS_σσ, hd]
  have hσαd : Γ.mS (Γ.σ (Γ.α d)) = 0 := by
    rw [mS, if_neg]; intro h'
    exact Γ.m_curve_σ (Γ.α d) (h'.trans (by rw [m_curve_α, m_dig_curve_d h]))
  have hside := Γ.m_isSide d
  rw [hd] at hside
  rw [mp₁, mq₂, m_side_α, m_side_σ, m_side_σ, hd, hσd, hσσd, m_side_α, m_side_σ, hαd, hσαd,
    m_side_α, hd]
  revert hside
  generalize Γ.mSide d = x
  generalize Γ.mSide (Γ.α d) = y
  revert x y; decide

/-- The side function of the collapsed map: the side of the old cell. -/
def mSideC : Orbit (mσc * mαcP h hS hc) → ZMod 2 :=
  Quotient.lift (fun y => Γ.mSide y.1) (fun a b hab => by
    obtain ⟨i, rfl⟩ := (hab : (mσc * mαcP h hS hc).SameCycle a b).exists_nat_pow_eq
    clear hab
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [ih, pow_succ', Perm.mul_apply]
      generalize ((mσc * mαcP h hS hc : Perm (Γ.MK d)) ^ i) a = y
      show Γ.mSide y.1 = Γ.mSide (Γ.σ (Γ.mαc d y.1))
      symm
      rcases m_kept_cases h hS hc y.2 with ⟨-, -, -, -, -, he⟩ | e | e | e | e
      · rw [he, ← m_φ_apply, m_side_φ]
      · rw [e, m_αc_p₁ h hS hc, mSide, m_c_σq₁ h, ← mSide, m_side_p₁_q₂ h]
      · rw [e, m_αc_q₁ h, mSide, m_c_σp₁ h]; rfl
      · rw [e, m_αc_p₂ h, mSide, m_c_σq₂ h]; rfl
      · rw [e, m_αc_q₂ h, mSide, m_c_σp₂ h, ← mSide, m_side_p₁_q₂ h])

theorem m_isSideC (y : Γ.MK d) :
    mSideC h hS hc (Orbit.mk _ y) + mSideC h hS hc (Orbit.mk _ (mαcP h hS hc y)) =
      if Γ.curve y.1 = Γ.S then 1 else 0 := by
  show Γ.mSide y.1 + Γ.mSide (Γ.mαc d y.1) = Γ.mS y.1
  rcases m_kept_cases h hS hc y.2 with ⟨-, -, -, -, -, he⟩ | e | e | e | e
  · rw [he]; exact Γ.m_isSide _
  · have e1 : Γ.mSide (Γ.mq₁ d) = Γ.mSide (Γ.α (Γ.mp₁ d)) := by
      unfold mSide; rw [m_c_q₁ h, mp₁, m_α_α]
    rw [e, m_αc_p₁ h hS hc, e1]; exact Γ.m_isSide _
  · have e1 : Γ.mSide (Γ.mq₁ d) = Γ.mSide (Γ.α (Γ.mp₁ d)) := by
      unfold mSide; rw [m_c_q₁ h, mp₁, m_α_α]
    rw [e, m_αc_q₁ h, e1, add_comm, Γ.m_isSide, mS, mS, m_curve_p₁ h, m_curve_q₁ h]
  · have e1 : Γ.mSide (Γ.mq₂ d) = Γ.mSide (Γ.α (Γ.mp₂ d)) := by
      rw [← m_side_p₁_q₂ h]; unfold mSide; rw [mp₂, m_α_α, m_c_σσσd h]
    rw [e, m_αc_p₂ h, e1]; exact Γ.m_isSide _
  · have e1 : Γ.mSide (Γ.mp₂ d) = Γ.mSide (Γ.α (Γ.mq₂ d)) := by
      unfold mSide; rw [m_c_p₂ h, mq₂, m_α_α, m_cellOf_σ, m_α_α]
    rw [e, m_αc_q₂ h, e1]; exact Γ.m_isSide _

end SConf

end Pca.Sweep
