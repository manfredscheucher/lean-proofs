/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package M, helpers: the collapsed map

The map after the digon collapse at `d` (`Pca/Sweep/M_Collapse.lean`): darts the kept darts
(`MK = {y // mKept d y}`), `σ` restricted (`mσc`), `α'` pairing the outer darts (`mαcP`). Its
straight walk is the first return of the old straight walk to the kept darts (`m_isFR`), its
crossings are the kept crossings.
-/
import Pca.Sweep.M_Collapse
import Pca.Great.Map_Euler

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {d : D}

/-- The kept darts. -/
abbrev MK (Γ : SConf n D) (d : D) := {y // Γ.mKept d y}

section Walk

variable (h : Γ.EmptyHumpAt d)
include h

omit h in
theorem m_s_p₁ : Γ.straight (Γ.mp₁ d) = d := by rw [mp₁, m_straight_apply, m_α_α, Γ.m_σ4]
omit h in
theorem m_s_q₁ : Γ.straight (Γ.mq₁ d) = Γ.α d := by rw [mq₁, m_straight_apply, m_α_α, Γ.m_σ4]
omit h in
theorem m_s_p₂ : Γ.straight (Γ.mp₂ d) = Γ.σ d := by rw [mp₂, m_straight_apply, m_α_α, Γ.m_σ4]
omit h in
theorem m_s_q₂ : Γ.straight (Γ.mq₂ d) = Γ.σ (Γ.σ (Γ.σ (Γ.α d))) := by
  rw [mq₂, m_straight_apply, m_α_α]
theorem m_s_σσσα : Γ.straight (Γ.σ (Γ.σ (Γ.σ (Γ.α d)))) = Γ.σ (Γ.σ (Γ.σ d)) := by
  rw [← m_dig_ασ h, m_straight_apply, m_α_α]

omit h in
theorem m_αs_d : Γ.α (Γ.straight d) = Γ.mq₁ d := rfl
omit h in
theorem m_αs_αd : Γ.α (Γ.straight (Γ.α d)) = Γ.mp₁ d := by rw [m_straight_α]; rfl
theorem m_αs_σd : Γ.α (Γ.straight (Γ.σ d)) = Γ.mq₂ d := by rw [m_straight_σd h]; rfl
theorem m_αs_σσσαd : Γ.α (Γ.straight (Γ.σ (Γ.σ (Γ.σ (Γ.α d))))) = Γ.mp₂ d := by
  rw [m_s_σσσα h]; rfl

/-- Corner darts are not kept. -/
theorem m_nk_d : ¬ Γ.mKept d d := fun hk => hk.1 rfl
theorem m_nk_αd : ¬ Γ.mKept d (Γ.α d) := fun hk => hk.2 rfl
theorem m_nk_σd : ¬ Γ.mKept d (Γ.σ d) := fun hk => hk.1 (Γ.m_crossingOf_σ d)
theorem m_nk_σσd : ¬ Γ.mKept d (Γ.σ (Γ.σ d)) := fun hk => hk.1 (Γ.m_crossingOf_σσ d)
theorem m_nk_σσσd : ¬ Γ.mKept d (Γ.σ (Γ.σ (Γ.σ d))) := fun hk => hk.1 (Γ.m_crossingOf_σσσ d)
theorem m_nk_σαd : ¬ Γ.mKept d (Γ.σ (Γ.α d)) := fun hk => hk.2 (Γ.m_crossingOf_σ _)
theorem m_nk_σσαd : ¬ Γ.mKept d (Γ.σ (Γ.σ (Γ.α d))) := fun hk => hk.2 (Γ.m_crossingOf_σσ _)
theorem m_nk_σσσαd : ¬ Γ.mKept d (Γ.σ (Γ.σ (Γ.σ (Γ.α d)))) :=
  fun hk => hk.2 (Γ.m_crossingOf_σσσ _)

/-- The reverse of an outer dart is not kept. -/
theorem m_nk_α_outer {y : D} (hy : y = Γ.mp₁ d ∨ y = Γ.mq₁ d ∨ y = Γ.mp₂ d ∨ y = Γ.mq₂ d) :
    ¬ Γ.mKept d (Γ.α y) := by
  rcases hy with rfl | rfl | rfl | rfl <;> simp only [mp₁, mq₁, mp₂, mq₂, m_α_α]
  · exact m_nk_σσd h
  · exact m_nk_σσαd h
  · exact m_nk_σσσd h
  · exact m_nk_σαd h

end Walk

section Map

variable (h : Γ.EmptyHumpAt d) (hS : ∃ e, Γ.curve e = Γ.S ∧ Γ.mKept d e)
  (hc : ∃ e, Γ.curve e = Γ.curve (Γ.σ d) ∧ Γ.mKept d e)
include h hS hc

theorem m_outer_kept {y : D} (hy : y = Γ.mp₁ d ∨ y = Γ.mq₁ d ∨ y = Γ.mp₂ d ∨ y = Γ.mq₂ d) :
    Γ.mKept d y := by
  rcases hy with rfl | rfl | rfl | rfl
  · exact m_kept_p₁ h hS
  · exact m_kept_q₁ h hS
  · exact m_kept_p₂ h hc
  · exact m_kept_q₂ h hc

theorem m_αc_p₁ : Γ.mαc d (Γ.mp₁ d) = Γ.mq₁ d := by rw [mαc, if_pos rfl]
omit hS hc in
theorem m_αc_q₁ : Γ.mαc d (Γ.mq₁ d) = Γ.mp₁ d := by
  rw [mαc, if_neg (m_p₁_ne_q₁ (Γ := Γ) (d := d)).symm, if_pos rfl]
omit hS hc in
theorem m_αc_p₂ : Γ.mαc d (Γ.mp₂ d) = Γ.mq₂ d := by
  rw [mαc, if_neg (m_p₁_ne_p₂ h).symm, if_neg (m_q₁_ne_p₂ h).symm, if_pos rfl]
omit hS hc in
theorem m_αc_q₂ : Γ.mαc d (Γ.mq₂ d) = Γ.mp₂ d := by
  rw [mαc, if_neg (m_p₁_ne_q₂ h).symm, if_neg (m_q₁_ne_q₂ h).symm,
    if_neg (m_p₂_ne_q₂ h).symm, if_pos rfl]
omit hS hc in
theorem m_αc_other {y : D} (h1 : y ≠ Γ.mp₁ d) (h2 : y ≠ Γ.mq₁ d) (h3 : y ≠ Γ.mp₂ d)
    (h4 : y ≠ Γ.mq₂ d) : Γ.mαc d y = Γ.α y := by
  rw [mαc, if_neg h1, if_neg h2, if_neg h3, if_neg h4]

/-- The four cases of a kept dart. -/
theorem m_kept_cases {y : D} (hy : Γ.mKept d y) :
    (y ≠ Γ.mp₁ d ∧ y ≠ Γ.mq₁ d ∧ y ≠ Γ.mp₂ d ∧ y ≠ Γ.mq₂ d ∧ Γ.mKept d (Γ.α y) ∧
      Γ.mαc d y = Γ.α y) ∨
    y = Γ.mp₁ d ∨ y = Γ.mq₁ d ∨ y = Γ.mp₂ d ∨ y = Γ.mq₂ d := by
  by_cases h1 : y = Γ.mp₁ d
  · exact Or.inr (Or.inl h1)
  by_cases h2 : y = Γ.mq₁ d
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases h3 : y = Γ.mp₂ d
  · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  by_cases h4 : y = Γ.mq₂ d
  · exact Or.inr (Or.inr (Or.inr (Or.inr h4)))
  exact Or.inl ⟨h1, h2, h3, h4, m_kept_α h hy h1 h2 h3 h4, m_αc_other h h1 h2 h3 h4⟩

theorem m_kept_αc {y : D} (hy : Γ.mKept d y) : Γ.mKept d (Γ.mαc d y) := by
  rcases m_kept_cases h hS hc hy with ⟨-, -, -, -, hk, he⟩ | rfl | rfl | rfl | rfl
  · rw [he]; exact hk
  · rw [m_αc_p₁ h hS hc]; exact m_kept_q₁ h hS
  · rw [m_αc_q₁ h]; exact m_kept_p₁ h hS
  · rw [m_αc_p₂ h]; exact m_kept_q₂ h hc
  · rw [m_αc_q₂ h]; exact m_kept_p₂ h hc

theorem m_αc_αc {y : D} (hy : Γ.mKept d y) : Γ.mαc d (Γ.mαc d y) = y := by
  rcases m_kept_cases h hS hc hy with ⟨h1, h2, h3, h4, hk, he⟩ | rfl | rfl | rfl | rfl
  · rw [he]
    have hyy : Γ.mKept d (Γ.α (Γ.α y)) := by rw [m_α_α]; exact hy
    rcases m_kept_cases h hS hc hk with ⟨-, -, -, -, -, he'⟩ | e | e | e | e
    · rw [he', m_α_α]
    all_goals exact absurd hyy (m_nk_α_outer h (by rw [e]; simp))
  · rw [m_αc_p₁ h hS hc, m_αc_q₁ h]
  · rw [m_αc_q₁ h, m_αc_p₁ h hS hc]
  · rw [m_αc_p₂ h, m_αc_q₂ h]
  · rw [m_αc_q₂ h, m_αc_p₂ h]

/-- The rotation on the kept darts. -/
def mσc : Perm (Γ.MK d) := Γ.σ.subtypePerm (fun _ => m_kept_σ)

/-- The edge involution on the kept darts. -/
def mαcP : Perm (Γ.MK d) :=
  Function.Involutive.toPerm (fun y => ⟨Γ.mαc d y.1, m_kept_αc h hS hc y.2⟩)
    (fun y => Subtype.ext (m_αc_αc h hS hc y.2))

theorem mσc_val (y : Γ.MK d) : ((mσc (Γ := Γ) (d := d)) y).1 = Γ.σ y.1 := rfl

theorem mαcP_val (y : Γ.MK d) : (mαcP h hS hc y).1 = Γ.mαc d y.1 := rfl

end Map

section Axioms

variable (h : Γ.EmptyHumpAt d) (hS : ∃ e, Γ.curve e = Γ.S ∧ Γ.mKept d e)
  (hc : ∃ e, Γ.curve e = Γ.curve (Γ.σ d) ∧ Γ.mKept d e)
include h hS hc

/-- The straight walk of the collapsed map. -/
abbrev msc : Perm (Γ.MK d) := straightPerm mσc (mαcP h hS hc)

theorem msc_val (y : Γ.MK d) : (msc h hS hc y).1 = Γ.σ (Γ.σ (Γ.mαc d y.1)) := rfl

omit h hS hc in
theorem m_pow3 (y : D) :
    (Γ.straight ^ 3) y = Γ.straight (Γ.straight (Γ.straight y)) := by
  simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply]

/-- The straight walk of the collapsed map is the first return of the old one. -/
theorem m_isFR : MapFacts.IsFR Γ.straight (msc h hS hc) Subtype.val (Γ.mKept d) := by
  intro y
  rcases m_kept_cases h hS hc y.2 with ⟨-, -, -, -, -, he⟩ | e | e | e | e
  · refine ⟨1, one_pos, ?_, fun j hj0 hj => absurd hj (by omega)⟩
    rw [msc_val, he, pow_one]; rfl
  all_goals refine ⟨3, by norm_num, ?_, fun j hj0 hj => ?_⟩
  · rw [msc_val, e, m_αc_p₁ h hS hc, m_pow3, m_s_p₁]; rfl
  · interval_cases j
    · rw [pow_one, e, m_s_p₁]; exact m_nk_d h
    · rw [pow_two, Perm.mul_apply, e, m_s_p₁]; exact m_nk_σσαd h
  · rw [msc_val, e, m_αc_q₁ h, m_pow3, m_s_q₁, m_straight_α]; rfl
  · interval_cases j
    · rw [pow_one, e, m_s_q₁]; exact m_nk_αd h
    · rw [pow_two, Perm.mul_apply, e, m_s_q₁, m_straight_α]; exact m_nk_σσd h
  · rw [msc_val, e, m_αc_p₂ h, m_pow3, m_s_p₂, m_straight_σd h]; rfl
  · interval_cases j
    · rw [pow_one, e, m_s_p₂]; exact m_nk_σd h
    · rw [pow_two, Perm.mul_apply, e, m_s_p₂, m_straight_σd h]; exact m_nk_σαd h
  · rw [msc_val, e, m_αc_q₂ h, m_pow3, m_s_q₂, m_s_σσσα h]; rfl
  · interval_cases j
    · rw [pow_one, e, m_s_q₂]; exact m_nk_σσσαd h
    · rw [pow_two, Perm.mul_apply, e, m_s_q₂, m_s_σσσα h]; exact m_nk_σσσd h

omit hS hc in
theorem m_kept_of_sameCycle {y z : D} (hy : Γ.mKept d y) (hz : Γ.σ.SameCycle y z) :
    Γ.mKept d z := by
  have : Γ.crossingOf z = Γ.crossingOf y := Orbit.mk_eq_mk.2 hz.symm
  rw [mKept, this]; exact hy

omit hS hc in
theorem m_map_orbit_σ (y : Γ.MK d) :
    (orbitFinset mσc y).map ⟨Subtype.val, Subtype.val_injective⟩ = orbitFinset Γ.σ y.1 := by
  ext z
  simp only [mem_map, mem_orbitFinset, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact Perm.sameCycle_subtypePerm.1 hw
  · intro hz
    exact ⟨⟨z, m_kept_of_sameCycle h y.2 hz⟩, Perm.sameCycle_subtypePerm.2 hz, rfl⟩

omit hS hc in
theorem m_curves_orbit (y : Γ.MK d) :
    (orbitFinset mσc y).image (fun z => Γ.curve z.1) = (orbitFinset Γ.σ y.1).image Γ.curve := by
  rw [← m_map_orbit_σ h y, map_eq_image, image_image]; rfl

theorem m_collapse_isSConf
    (hconn : ∀ a b : Γ.MK d, Relation.EqvGen (StepRel mσc (mαcP h hS hc)) a b)
    (heuler : Nonempty (Γ.MK d) → (Fintype.card (Orbit (mσc (Γ := Γ) (d := d))) : ℤ) -
      Fintype.card (Orbit (mαcP h hS hc)) + Fintype.card (Orbit (mσc * mαcP h hS hc)) = 2) :
    IsSConf n mσc (mαcP h hS hc) (fun z => Γ.curve z.1) Γ.S where
  card_crossing y := by
    rw [← card_map ⟨Subtype.val, Subtype.val_injective⟩, m_map_orbit_σ h y]
    exact Γ.isSConf.card_crossing y.1
  α_ne y he := by
    have := congrArg Subtype.val he
    rw [mαcP_val] at this
    rcases m_kept_cases h hS hc y.2 with ⟨-, -, -, -, -, he'⟩ | e | e | e | e
    · rw [he'] at this; exact Γ.m_α_ne _ this
    · rw [e, m_αc_p₁ h hS hc] at this; exact m_p₁_ne_q₁ this.symm
    · rw [e, m_αc_q₁ h] at this; exact m_p₁_ne_q₁ this
    · rw [e, m_αc_p₂ h] at this; exact m_p₂_ne_q₂ h this.symm
    · rw [e, m_αc_q₂ h] at this; exact m_p₂_ne_q₂ h this
  α_α y := Subtype.ext (m_αc_αc h hS hc y.2)
  curve_α y := by
    show Γ.curve (Γ.mαc d y.1) = Γ.curve y.1
    rcases m_kept_cases h hS hc y.2 with ⟨-, -, -, -, -, he'⟩ | e | e | e | e
    · rw [he', m_curve_α]
    · rw [e, m_αc_p₁ h hS hc, m_curve_p₁ h, m_curve_q₁ h]
    · rw [e, m_αc_q₁ h, m_curve_p₁ h, m_curve_q₁ h]
    · rw [e, m_αc_p₂ h, m_curve_p₂, m_curve_q₂ h]
    · rw [e, m_αc_q₂ h, m_curve_p₂, m_curve_q₂ h]
  curve_σ y := Γ.isSConf.curve_σ y.1
  curve_σσ y := Γ.isSConf.curve_σσ y.1
  straight y z hyz := by
    have hFR := m_isFR h hS hc
    have hr : ∀ x, Γ.mKept d x → ∃ x' : Γ.MK d, x'.1 = x := fun x hx => ⟨⟨x, hx⟩, rfl⟩
    have key := fun a b => MapFacts.IsFR.sameCycle_iff (a := a) (b := b) Subtype.val_injective
      (fun x' : Γ.MK d => x'.2) hr hFR
    rcases Γ.isSConf.straight y.1 z.1 hyz with h1 | h1
    · exact Or.inl ((key y z).2 h1)
    · exact Or.inr ((key y (mσc (mσc z))).2 h1)
  two_int c c' hcc := by
    let cm : Orbit (mσc (Γ := Γ) (d := d)) → Orbit Γ.σ := fun o =>
      Quotient.liftOn o (fun y => Orbit.mk Γ.σ y.1)
        (fun a b hab => Orbit.mk_eq_mk.2 (Perm.sameCycle_subtypePerm.1 hab))
    have hcm : ∀ y : Γ.MK d, cm (Orbit.mk _ y) = Orbit.mk Γ.σ y.1 := fun _ => rfl
    have hcur : ∀ o, crossingCurves mσc (fun z => Γ.curve z.1) o = crossingCurves Γ.σ Γ.curve (cm o) := by
      intro o
      obtain ⟨y, rfl⟩ := o.exists_mk
      rw [hcm]
      exact m_curves_orbit h y
    refine le_trans ?_ (Γ.isSConf.two_int c c' hcc)
    refine card_le_card_of_injOn cm ?_ ?_
    · intro o ho
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at ho ⊢
      rw [← hcur]; exact ho
    · intro a _ b _ hab
      obtain ⟨y, rfl⟩ := a.exists_mk
      obtain ⟨z, rfl⟩ := b.exists_mk
      rw [hcm, hcm] at hab
      exact Orbit.mk_eq_mk.2 (Perm.sameCycle_subtypePerm.2 (Orbit.mk_eq_mk.1 hab))
  connected := hconn
  euler := heuler
  S_mem _ := by
    obtain ⟨e, he, hk⟩ := hS
    exact ⟨⟨e, hk⟩, he⟩

end Axioms

end SConf

end Pca.Sweep
