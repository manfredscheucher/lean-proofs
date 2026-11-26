/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package M, helpers: the ∞-arc after the collapse, and the collapsed sweep configuration

The ∞-arc keeps its length. If it starts with the segment of `S` after the digon
(`straight d`, which disappears), it starts with the joined segment `p₁` instead (the joined
segment of `S` contains the old first segment); otherwise it keeps its start. `mCollapse` is the
collapsed sweep configuration.
-/
import Pca.Sweep.M_CollapseEuler

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {d : D}

variable (h : Γ.EmptyHumpAt d) (hS : ∃ e, Γ.curve e = Γ.S ∧ Γ.mKept d e)
  (hc : ∃ e, Γ.curve e = Γ.curve (Γ.σ d) ∧ Γ.mKept d e)
include h

/-! ## Arc darts -/

theorem m_side_αd' : Γ.mSide (Γ.α d) = 1 := h.1.1.2

theorem m_side_d' : Γ.mSide d = 0 := by
  have h1 := Γ.m_isSide d
  rw [m_side_αd' h, mS, if_pos (m_dig_curve_d h)] at h1
  revert h1; generalize Γ.mSide d = x; revert x; decide

theorem m_mS_σd : Γ.mS (Γ.σ d) = 0 := by rw [mS, if_neg (m_dig_curve_γ_ne h)]

theorem m_mS_d : Γ.mS d = 1 := by rw [mS, if_pos (m_dig_curve_d h)]

theorem m_side_σσd : Γ.mSide (Γ.σ (Γ.σ d)) = 1 := by
  rw [m_side_σ, m_side_σ, m_side_d' h, m_mS_d h, m_mS_σd h]; decide

theorem m_arc_sweep {w : D} (hw : w ∈ Γ.infArc) : Γ.curve w = Γ.S ∧ Γ.mSide (Γ.α w) = 1 :=
  Γ.infArc_sweep w hw

theorem m_arc_ne_d {w : D} (hw : w ∈ Γ.infArc) : w ≠ d := fun e => h.1.2 (e ▸ hw)

theorem m_arc_ne_outer {w : D} (hw : w ∈ Γ.infArc) :
    w ≠ Γ.mq₁ d ∧ w ≠ Γ.mp₂ d ∧ w ≠ Γ.mq₂ d := by
  obtain ⟨hwS, hwU⟩ := m_arc_sweep h hw
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rw [e, mq₁, m_α_α, m_side_σ, m_side_σ, m_side_αd' h, m_mS_α, m_mS_d h, mS,
      if_neg (fun h' => Γ.m_curve_σ (Γ.α d) (h'.trans (by rw [m_curve_α, m_dig_curve_d h])))]
      at hwU
    exact absurd hwU (by decide)
  · rw [e, m_curve_p₂] at hwS; exact m_dig_curve_γ_ne h hwS
  · rw [e, m_curve_q₂ h] at hwS; exact m_dig_curve_γ_ne h hwS

/-- An arc dart other than `straight d` is kept. -/
theorem m_arc_kept {w : D} (hw : w ∈ Γ.infArc) (hne : w ≠ Γ.straight d) : Γ.mKept d w := by
  obtain ⟨hwS, hwU⟩ := m_arc_sweep h hw
  have hγ := m_dig_curve_γ_ne h
  by_contra hk
  rcases (m_not_kept_iff (Γ := Γ) (d := d)).1 hk with (e | e | e | e) | (e | e | e | e) <;>
    subst e
  · exact m_arc_ne_d h hw rfl
  · exact hγ hwS
  · rw [m_side_α, m_side_σσd h, m_mS_σσ, m_mS_d h] at hwU
    exact absurd hwU (by decide)
  · rw [m_curve_σσσ] at hwS; exact hγ hwS
  · rw [m_α_α, m_side_d' h] at hwU; exact absurd hwU (by decide)
  · exact hγ (by rw [← m_straight_σd h, m_curve_straight] at hwS; exact hwS)
  · exact hne rfl
  · exact hγ (by rw [← m_dig_ασ h, m_curve_α] at hwS; exact hwS)

theorem m_arc_mem {z0 : D} (hz0 : Γ.infStart = some z0) {j : ℕ} (hj : j ≤ Γ.infLen) :
    (Γ.straight ^ j) z0 ∈ Γ.infArc := by
  unfold infArc
  rw [hz0]
  simp only [arcOf, Option.elim_some, mem_image, mem_range]
  exact ⟨j, by omega, rfl⟩

/-- If the arc contains `straight d`, it starts there. -/
theorem m_arc_start {z0 : D} (hz0 : Γ.infStart = some z0) (hs : Γ.straight d ∈ Γ.infArc) :
    z0 = Γ.straight d := by
  unfold infArc at hs
  rw [hz0] at hs
  simp only [arcOf, Option.elim_some, mem_image, mem_range] at hs
  obtain ⟨j, hj, hjz⟩ := hs
  change (Γ.straight ^ j) z0 = _ at hjz
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · exact hjz
  · exfalso
    have : (Γ.straight ^ (j - 1)) z0 = d := by
      apply Γ.straight.injective
      rw [← Perm.mul_apply, ← pow_succ', Nat.sub_add_cancel hpos, hjz]
    exact h.1.2 (this ▸ m_arc_mem h hz0 (by omega))

include hS hc

/-- On an arc dart other than `p₁` the new straight walk is the old one. -/
theorem m_msc_arc (y : Γ.MK d) (hy : y.1 ∈ Γ.infArc) (hp : y.1 ≠ Γ.mp₁ d) :
    (msc h hS hc y).1 = Γ.straight y.1 := by
  obtain ⟨h2, h3, h4⟩ := m_arc_ne_outer h hy
  rw [msc_val, m_αc_other h hp h2 h3 h4]; rfl

/-! ## The new start of the arc -/

/-- The kept dart `z`, if it is kept. -/
def mfk (Γ : SConf n D) (d z : D) : Option (Γ.MK d) :=
  if hk : Γ.mKept d z then some ⟨z, hk⟩ else none

/-- The start of the ∞-arc after the collapse. -/
def mStartC : Option (Γ.MK d) :=
  if Γ.straight d ∈ Γ.infArc then some ⟨Γ.mp₁ d, m_kept_p₁ h hS⟩ else Γ.infStart.bind (Γ.mfk d)

/-- The walk along the new arc: every dart is an old arc dart or `p₁`; it does not close up
before `infLen` steps. -/
theorem m_arc_walk {z' : Γ.MK d} (hz' : z' ∈ mStartC h hS) :
    (∀ i ≤ Γ.infLen, ((msc h hS hc ^ i) z').1 ∈ Γ.infArc ∨ ((msc h hS hc ^ i) z').1 = Γ.mp₁ d) ∧
      Γ.infLen ≤ period (msc h hS hc) z' := by
  obtain ⟨z0, hz0⟩ : ∃ z0, Γ.infStart = some z0 :=
    Option.isSome_iff_exists.1 (Γ.infStart_isSome ⟨d⟩)
  have hper := iterate_period (msc h hS hc) z'
  have hp0 := period_pos (msc h hS hc) z'
  set P := period (msc h hS hc) z' with hP
  unfold mStartC at hz'
  split_ifs at hz' with hs
  · -- the arc starts with `straight d`; the new arc starts with `p₁`
    obtain rfl := Option.some_injective _ hz'
    have hz0s := m_arc_start h hz0 hs
    subst hz0s
    have key : ∀ i, 1 ≤ i → i ≤ Γ.infLen →
        ((msc h hS hc ^ i) ⟨Γ.mp₁ d, m_kept_p₁ h hS⟩).1 = (Γ.straight ^ i) (Γ.straight d) := by
      intro i hi1 hi2
      induction i with
      | zero => omega
      | succ i ih =>
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · rw [zero_add, pow_one, msc_val, m_αc_p₁ h hS hc, pow_one]; rfl
        · rw [pow_succ', Perm.mul_apply, m_msc_arc h hS hc _ ?_ ?_, ih hpos (by omega), pow_succ',
            Perm.mul_apply]
          · rw [ih hpos (by omega)]; exact m_arc_mem h hz0 (by omega)
          · rw [ih hpos (by omega)]
            intro e
            have : (Γ.straight ^ (i + 1)) (Γ.straight d) = d := by
              rw [pow_succ', Perm.mul_apply, e, m_s_p₁]
            exact h.1.2 (this ▸ m_arc_mem h hz0 (by omega))
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact Or.inr rfl
      · rw [key i hpos hi]; exact Or.inl (m_arc_mem h hz0 hi)
    · by_contra hlt
      push Not at hlt
      have e := key _ hp0 hlt.le
      rw [Perm.coe_pow] at e
      rw [hper] at e
      have : (Γ.straight ^ (P + 1)) (Γ.straight d) = d := by
        rw [pow_succ', Perm.mul_apply, ← e, m_s_p₁]
      exact h.1.2 (this ▸ m_arc_mem h hz0 (by omega))
  · -- the start is kept
    rw [hz0] at hz'
    simp only [Option.bind_some, mfk] at hz'
    split_ifs at hz' with hk
    pick_goal 2
    · simp at hz'
    obtain rfl := Option.some_injective _ hz'
    have key : ∀ i ≤ Γ.infLen,
        ((msc h hS hc ^ i) ⟨z0, hk⟩).1 = (Γ.straight ^ i) z0 := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [pow_succ', Perm.mul_apply, m_msc_arc h hS hc _ ?_ ?_, ih (by omega), pow_succ',
          Perm.mul_apply]
        · rw [ih (by omega)]; exact m_arc_mem h hz0 (by omega)
        · rw [ih (by omega)]
          intro e
          have : (Γ.straight ^ (i + 1)) z0 = d := by
            rw [pow_succ', Perm.mul_apply, e, m_s_p₁]
          exact h.1.2 (this ▸ m_arc_mem h hz0 hi)
    refine ⟨fun i hi => Or.inl (by rw [key i hi]; exact m_arc_mem h hz0 hi), ?_⟩
    by_contra hlt
    push Not at hlt
    have e := key _ hlt.le
    rw [Perm.coe_pow, hper, Perm.coe_pow] at e
    have hle : Γ.infLen ≤ period Γ.straight z0 := Γ.infLen_le z0 hz0
    exact m_iterate_ne_of_lt hp0 (by omega) e.symm

/-! ## The collapsed sweep configuration -/

theorem m_αcP_α_α (y : Γ.MK d) : mαcP h hS hc (mαcP h hS hc y) = y :=
  Subtype.ext (m_αc_αc h hS hc y.2)

theorem m_αcP_ne (y : Γ.MK d) : mαcP h hS hc y ≠ y := by
  intro he
  have := congrArg Subtype.val he
  rw [mαcP_val] at this
  rcases m_kept_cases h hS hc y.2 with ⟨-, -, -, -, -, he'⟩ | e | e | e | e
  · rw [he'] at this; exact Γ.m_α_ne _ this
  · rw [e, m_αc_p₁ h hS hc] at this; exact m_p₁_ne_q₁ this.symm
  · rw [e, m_αc_q₁ h] at this; exact m_p₁_ne_q₁ this
  · rw [e, m_αc_p₂ h] at this; exact m_p₂_ne_q₂ h this.symm
  · rw [e, m_αc_q₂ h] at this; exact m_p₂_ne_q₂ h this

variable (hconn : ∀ a b, Γ.mKept d a → Γ.mKept d b → Relation.EqvGen (Γ.MStep d) a b)
include hconn

theorem m_collapse_connected (a b : Γ.MK d) :
    Relation.EqvGen (StepRel mσc (mαcP h hS hc)) a b :=
  (m_conn_transport h hS hc a.1 b.1 (hconn a.1 b.1 a.2 b.2)).2 a.2 b.2

theorem m_collapse_euler :
    (Fintype.card (Orbit (mσc (Γ := Γ) (d := d))) : ℤ) - Fintype.card (Orbit (mαcP h hS hc)) +
      Fintype.card (Orbit (mσc * mαcP h hS hc)) = 2 := by
  have hV := m_card_four h hS hc Γ.σ Γ.isSConf.card_crossing
  have hV' := m_card_four h hS hc (mσc (Γ := Γ) (d := d)) (fun y => by
    rw [← card_map ⟨Subtype.val, Subtype.val_injective⟩, m_map_orbit_σ h y]
    exact Γ.isSConf.card_crossing y.1)
  have hE := MapFacts.card_eq_two_mul_card_orbit Γ.α Γ.isSConf.α_α Γ.isSConf.α_ne
  have hE' := MapFacts.card_eq_two_mul_card_orbit (mαcP h hS hc) (m_αcP_α_α h hS hc)
    (m_αcP_ne h hS hc)
  have hD := m_card_D h
  have hF := m_card_cells h hS hc
  have heu := Γ.isSConf.euler ⟨d⟩
  have hle := MapFacts.euler_le_two (σ := mσc (Γ := Γ) (d := d)) (α := mαcP h hS hc)
    (m_αcP_α_α h hS hc) (m_αcP_ne h hS hc) (m_collapse_connected h hS hc hconn)
  change (Fintype.card (Orbit Γ.σ) : ℤ) - Fintype.card (Orbit Γ.α) +
    Fintype.card (Orbit Γ.φ) = 2 at heu
  change Fintype.card (Orbit Γ.φ) ≤ _ at hF
  omega

/-- **The collapsed sweep configuration.** -/
def mCollapse : SConf n (Γ.MK d) where
  σ := mσc
  α := mαcP h hS hc
  curve z := Γ.curve z.1
  S := Γ.S
  isSConf := m_collapse_isSConf h hS hc (m_collapse_connected h hS hc hconn)
    (fun _ => m_collapse_euler h hS hc hconn)
  side := mSideC h hS hc
  isSide := m_isSideC h hS hc
  infStart := mStartC h hS
  infLen := Γ.infLen
  infStart_isSome _ := by
    unfold mStartC
    split_ifs with hs
    · rfl
    · obtain ⟨z0, hz0⟩ : ∃ z0, Γ.infStart = some z0 :=
        Option.isSome_iff_exists.1 (Γ.infStart_isSome ⟨d⟩)
      have hne : z0 ≠ Γ.straight d := fun e => hs (e ▸ m_arc_mem h hz0 (Nat.zero_le _))
      rw [hz0]
      have hk : Γ.mKept d z0 := m_arc_kept h (m_arc_mem h hz0 (Nat.zero_le _)) hne
      rw [Option.bind_some, mfk, dif_pos hk]
      rfl
  infLen_le z' hz' := (m_arc_walk h hS hc hz').2
  infArc_sweep a' ha' := by
    obtain ⟨z', hz', ha''⟩ : ∃ z', mStartC h hS = some z' ∧
        a' ∈ (range (Γ.infLen + 1)).image (fun i => (msc h hS hc ^ i) z') := by
      revert ha'
      cases mStartC h hS with
      | none => intro ha'; simp [arcOf] at ha'
      | some z' => intro ha'; exact ⟨z', rfl, ha'⟩
    obtain ⟨i, hi, rfl⟩ := mem_image.1 ha''
    have hw := (m_arc_walk h hS hc hz').1 i (by rw [mem_range] at hi; omega)
    set w := (msc h hS hc ^ i) z' with hwdef
    show Γ.curve w.1 = Γ.S ∧ Γ.mSide (Γ.mαc d w.1) = 1
    by_cases hp : w.1 = Γ.mp₁ d
    · rw [hp, m_αc_p₁ h hS hc, m_curve_p₁ h]
      refine ⟨rfl, ?_⟩
      unfold mSide; rw [m_c_q₁ h]; exact m_side_σσd h
    · rcases hw with hw | hw
      · obtain ⟨h2, h3, h4⟩ := m_arc_ne_outer h hw
        rw [m_αc_other h hp h2 h3 h4]
        exact m_arc_sweep h hw
      · exact absurd hw hp

theorem m_collapse_α_join (y : Γ.MK d) : ∃ k, (∀ i < k,
    ¬ Γ.mKept d (Γ.α ((Γ.straight ^ i) y.1))) ∧
      ((mCollapse h hS hc hconn).α y).1 = Γ.α ((Γ.straight ^ k) y.1) :=
  m_αc_eq_join h hS hc y.1 y.2

end SConf

end Pca.Sweep
