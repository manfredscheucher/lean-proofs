/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package R (removal), the construction

Helper file for `Pca/Sweep/Removal.lean`: the removal of `R` on the subtype of surviving darts.

* `rσ`: `σ` restricted; `rα`: the reverse dart of the joined segment (`rHit`);
* `straight` of the result is the first return of `straight` (`r_isFR_straight`);
* connectivity: a kept step is a step of the result, and the darts of `S` are connected along
  `straight`;
* Euler (`r_euler`): every cycle of segments of the result lifts to a cycle of `Γ` (pieces of the
  joined segments), which is a cut by Jordan (`j_mem_range_of_mem_ker`); the cut descends because
  it does not change across removed segments. Then `r_euler_of_cut`.
-/
import Pca.Sweep.R_Basic

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}


/-- A function constant along `f` is constant on its cycles. -/
theorem r_eq_of_sameCycle {X : Type*} [Finite X] {β : Type*} {f : Perm X} (g : X → β)
    (hg : ∀ x, g (f x) = g x) {a b : X} (h : f.SameCycle a b) : g a = g b := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction i with
  | zero => rfl
  | succ i ih => rw [pow_succ', Perm.mul_apply, hg, ih]

theorem r_eqvGen_of_sameCycle {X : Type*} [Finite X] {r : X → X → Prop} {f : Perm X}
    (hf : ∀ y, Relation.EqvGen r y (f y)) {a b : X} (h : f.SameCycle a b) :
    Relation.EqvGen r a b := by
  obtain ⟨i, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction i with
  | zero => exact .refl _
  | succ i ih => rw [pow_succ', Perm.mul_apply]; exact ih.trans _ _ _ (hf _)

namespace SConf

variable {Γ : SConf n D} {R : Finset (Fin n)}

variable (Γ R) in
/-- The surviving darts. -/
abbrev RD := {d // Γ.Keep R d}

noncomputable instance : Fintype (Γ.RD R) := Fintype.ofFinite _

variable (Γ R) in
noncomputable def rσ : Perm (Γ.RD R) := Γ.σ.subtypePerm fun d => r_keep_σ_iff d

variable (Γ R) in
noncomputable def rα : Perm (Γ.RD R) :=
  Function.Involutive.toPerm (fun d => ⟨Γ.rHit R d.1, r_keep_hit d.2⟩)
    (fun d => Subtype.ext (r_hit_hit d.2.1))

theorem r_rσ_val (d : Γ.RD R) : (Γ.rσ R d).1 = Γ.σ d.1 := rfl

theorem r_rα_val (d : Γ.RD R) : (Γ.rα R d).1 = Γ.rHit R d.1 := rfl

theorem r_rα_α (d : Γ.RD R) : Γ.rα R (Γ.rα R d) = d := Subtype.ext (r_hit_hit d.2.1)

theorem r_rα_ne (d : Γ.RD R) : Γ.rα R d ≠ d := fun h => r_hit_ne d.2.1 (congrArg Subtype.val h)

theorem r_straight_val (d : Γ.RD R) :
    (straightPerm (Γ.rσ R) (Γ.rα R) d).1 = (Γ.straight ^ (Γ.rJ R d.1 + 1)) d.1 :=
  r_σσ_hit d.2.1

theorem r_isFR_σ : MapFacts.IsFR Γ.σ (Γ.rσ R) Subtype.val (Γ.Keep R) := fun x =>
  ⟨1, one_pos, by rw [pow_one]; rfl, fun j h0 h1 => by omega⟩

theorem r_isFR_straight :
    MapFacts.IsFR Γ.straight (straightPerm (Γ.rσ R) (Γ.rα R)) Subtype.val (Γ.Keep R) := fun x =>
  ⟨Γ.rJ R x.1 + 1, by omega, r_straight_val x, fun j h0 h1 hk =>
    r_notK_pow x.2.1 h0 (by omega) hk.1⟩

theorem r_hinj : Function.Injective (Subtype.val : Γ.RD R → D) := Subtype.val_injective
theorem r_hK : ∀ x : Γ.RD R, Γ.Keep R x.1 := fun x => x.2
theorem r_hr : ∀ x, Γ.Keep R x → ∃ x' : Γ.RD R, x'.1 = x := fun x hx => ⟨⟨x, hx⟩, rfl⟩

theorem r_keep_of_sameCycle_σ {a b : D} (ha : Γ.Keep R a) (h : Γ.σ.SameCycle a b) :
    Γ.Keep R b := by
  have := r_eq_of_sameCycle (fun d => Γ.Keep R d) (fun d => propext (r_keep_σ_iff d)) h
  exact this ▸ ha

open Classical in
theorem r_map_orbitFinset_σ (d : Γ.RD R) :
    (orbitFinset (Γ.rσ R) d).map ⟨Subtype.val, r_hinj⟩ = orbitFinset Γ.σ d.1 := by
  rw [r_isFR_σ.map_orbitFinset r_hinj r_hK r_hr, filter_eq_self]
  intro z hz
  exact r_keep_of_sameCycle_σ d.2 (mem_orbitFinset.1 hz)

theorem r_sum_orbitFinset_σ {M : Type*} [AddCommMonoid M] (F : D → M) (d : Γ.RD R) :
    ∑ z ∈ orbitFinset (Γ.rσ R) d, F z.1 = ∑ z ∈ orbitFinset Γ.σ d.1, F z := by
  rw [← r_map_orbitFinset_σ d, sum_map]; rfl

/-! ## The side function -/

theorem r_cell_hit {M : Type*} (r : Γ.Cell → M)
    (hr : ∀ w, Γ.curve w ∈ R → r (Γ.cellOf (Γ.α w)) = r (Γ.cellOf w)) {k : D}
    (hk : Γ.rK R k) : r (Γ.cellOf (Γ.σ (Γ.rHit R k))) = r (Γ.cellOf k) := by
  rw [r_hit_eq hk, ← j_φ_apply, j_cellOf_φ]
  exact r_cell_pow r hr hk le_rfl

/-- A function on cells of `Γ`, constant across removed segments, as a function on the cells of
the result. -/
noncomputable def rCellFun {M : Type*} (r : Γ.Cell → M)
    (hr : ∀ w, Γ.curve w ∈ R → r (Γ.cellOf (Γ.α w)) = r (Γ.cellOf w)) :
    Orbit (Γ.rσ R * Γ.rα R) → M :=
  Quotient.lift (fun d => r (Γ.cellOf d.1)) fun _ _ h =>
    r_eq_of_sameCycle (fun d : Γ.RD R => r (Γ.cellOf d.1)) (fun d => r_cell_hit r hr d.2.1) h

theorem r_cellFun_mk {M : Type*} (r : Γ.Cell → M)
    (hr : ∀ w, Γ.curve w ∈ R → r (Γ.cellOf (Γ.α w)) = r (Γ.cellOf w)) (d : Γ.RD R) :
    rCellFun r hr (Orbit.mk _ d) = r (Γ.cellOf d.1) := rfl

theorem r_cellFun_add {r : Γ.Cell → ZMod 2}
    (hr : ∀ w, Γ.curve w ∈ R → r (Γ.cellOf (Γ.α w)) = r (Γ.cellOf w)) (d : Γ.RD R) :
    rCellFun r hr (Orbit.mk _ d) + rCellFun r hr (Orbit.mk _ (Γ.rα R d)) =
      r (Γ.cellOf ((Γ.straight ^ Γ.rJ R d.1) d.1)) +
        r (Γ.cellOf (Γ.α ((Γ.straight ^ Γ.rJ R d.1) d.1))) := by
  rw [r_cellFun_mk, r_cellFun_mk, r_rα_val, r_hit_eq d.2.1, r_cell_pow r hr d.2.1 le_rfl]

/-! ## Crossings -/

theorem r_crossingCurves (d : Γ.RD R) :
    crossingCurves (Γ.rσ R) (fun d => Γ.curve d.1) (Orbit.mk _ d) =
      Γ.curves (Γ.crossingOf d.1) := by
  show (orbitFinset (Γ.rσ R) d).image (fun d => Γ.curve d.1) = (orbitFinset Γ.σ d.1).image Γ.curve
  rw [← r_map_orbitFinset_σ d, map_eq_image, image_image]
  rfl

/-- Crossings of the result as crossings of `Γ`. -/
noncomputable def rCr : Orbit (Γ.rσ R) → Γ.Crossing :=
  Quotient.map' Subtype.val fun _ _ h => (r_isFR_σ.sameCycle_iff r_hinj r_hK r_hr).1 h

theorem r_rCr_mk (d : Γ.RD R) : rCr (Orbit.mk _ d) = Γ.crossingOf d.1 := rfl

theorem r_rCr_inj : Function.Injective (rCr (Γ := Γ) (R := R)) := by
  intro o1 o2 he
  obtain ⟨a, rfl⟩ := o1.exists_mk
  obtain ⟨b, rfl⟩ := o2.exists_mk
  rw [r_rCr_mk, r_rCr_mk] at he
  unfold crossingOf at he
  rw [Orbit.mk_eq_mk] at he
  exact Orbit.mk_eq_mk.2 ((r_isFR_σ.sameCycle_iff r_hinj r_hK r_hr).2 he)

/-! ## Connectivity -/

theorem r_stepRel_of_eqvGen {a b : D} (h : Relation.EqvGen (Γ.KeptStep R) a b)
    (ha : Γ.Keep R a) (hb : Γ.Keep R b) :
    Relation.EqvGen (StepRel (Γ.rσ R) (Γ.rα R)) ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | rel a b h =>
    refine .rel _ _ ?_
    rcases r_keptStep_cases ha.1 h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  | refl => exact .refl _
  | symm a b _ ih => exact (ih hb ha).symm
  | trans a b c h1 _ ih1 ih2 =>
    have hb' := r_keep_of_eqvGen ha h1
    exact (ih1 ha hb').trans _ _ _ (ih2 hb' hb)

theorem r_straight' (d e : Γ.RD R) (h : Γ.curve d.1 = Γ.curve e.1) :
    (straightPerm (Γ.rσ R) (Γ.rα R)).SameCycle d e ∨
      (straightPerm (Γ.rσ R) (Γ.rα R)).SameCycle d (Γ.rσ R (Γ.rσ R e)) := by
  rcases Γ.isSConf.straight d.1 e.1 h with h1 | h1
  · exact Or.inl ((r_isFR_straight.sameCycle_iff r_hinj r_hK r_hr).2 h1)
  · exact Or.inr ((r_isFR_straight.sameCycle_iff r_hinj r_hK r_hr).2 h1)

theorem r_connected (a b : Γ.RD R) : Relation.EqvGen (StepRel (Γ.rσ R) (Γ.rα R)) a b := by
  have hS : ∀ x y : Γ.RD R, Γ.curve x.1 = Γ.S → Γ.curve y.1 = Γ.S →
      Relation.EqvGen (StepRel (Γ.rσ R) (Γ.rα R)) x y := by
    intro x y hx hy
    have s1 : ∀ z, Relation.EqvGen (StepRel (Γ.rσ R) (Γ.rα R)) z (Γ.rα R z) :=
      fun z => .rel _ _ (Or.inr rfl)
    have s2 : ∀ z, Relation.EqvGen (StepRel (Γ.rσ R) (Γ.rα R)) z (Γ.rσ R z) :=
      fun z => .rel _ _ (Or.inl rfl)
    have hst : ∀ z, Relation.EqvGen (StepRel (Γ.rσ R) (Γ.rα R)) z
        (straightPerm (Γ.rσ R) (Γ.rα R) z) := fun z =>
      ((s1 z).trans _ _ _ (s2 _)).trans _ _ _ (s2 _)
    rcases r_straight' x y (hx.trans hy.symm) with h | h
    · exact r_eqvGen_of_sameCycle hst h
    · refine (r_eqvGen_of_sameCycle hst h).trans _ _ _ ?_
      exact ((s2 y).trans _ _ _ (s2 _)).symm
  obtain ⟨e, he, hae⟩ := a.2.2
  obtain ⟨f, hf, hbf⟩ := b.2.2
  have hke := r_keep_of_eqvGen a.2 hae
  have hkf := r_keep_of_eqvGen b.2 hbf
  exact ((r_stepRel_of_eqvGen hae a.2 hke).trans _ _ _ (hS ⟨e, hke⟩ ⟨f, hkf⟩ he hf)).trans _ _ _
    (r_stepRel_of_eqvGen hbf b.2 hkf).symm

/-! ## Euler -/

section Euler

variable (h : Orbit (Γ.rα R) → ZMod 2)

/-- `z` is a piece of a joined segment with value `1`. -/
def rPc (z : D) : Prop :=
  ∃ d : Γ.RD R, ∃ i ≤ Γ.rJ R d.1, (Γ.straight ^ i) d.1 = z ∧ h (Orbit.mk _ d) = 1

theorem r_mk_rα (d : Γ.RD R) : Orbit.mk (Γ.rα R) (Γ.rα R d) = Orbit.mk (Γ.rα R) d := by
  rw [Orbit.mk_eq_mk]; exact (MapFacts.sameCycle_of_pow _ d 1).symm

theorem r_Pc_α {z : D} (hz : rPc h z) : rPc h (Γ.α z) := by
  obtain ⟨d, i, hi, rfl, hv⟩ := hz
  refine ⟨Γ.rα R d, Γ.rJ R d.1 - i, by rw [r_rα_val, r_J_hit d.2.1]; omega, ?_, by
    rw [r_mk_rα]; exact hv⟩
  have := r_rev (k := Γ.rHit R d.1) (r_K_hit d.2.1) (i := i) (by rw [r_J_hit d.2.1]; exact hi)
  rw [r_hit_hit d.2.1, r_J_hit d.2.1] at this
  rw [r_rα_val, ← this]

theorem r_Pc_α_iff (z : D) : rPc h (Γ.α z) ↔ rPc h z :=
  ⟨fun hz => by have := r_Pc_α h hz; rwa [j_α_α] at this, r_Pc_α h⟩

/-- The owner of a piece is unique. -/
theorem r_Pc_owner {d : Γ.RD R} {i : ℕ} (hi : i ≤ Γ.rJ R d.1) :
    rPc h ((Γ.straight ^ i) d.1) ↔ h (Orbit.mk _ d) = 1 := by
  constructor
  · rintro ⟨d', i', hi', he, hv⟩
    have := r_piece_unique d'.2.1 d.2.1 hi' hi he
    rwa [Subtype.ext this] at hv
  · intro hv; exact ⟨d, i, hi, rfl, hv⟩

theorem r_Pc_curve {w : D} (hw : Γ.curve w ∈ R) : ¬ rPc h w := by
  rintro ⟨d, i, -, rfl, -⟩
  rw [r_curve_pow] at hw
  exact Γ.r_curve_not_mem R d.2.1 hw

open Classical in
noncomputable def rF (z : D) : ZMod 2 := if rPc h z then 1 else 0

theorem r_zmod2_ite (a : ZMod 2) : (if a = 1 then (1 : ZMod 2) else 0) = a := by
  revert a; decide

theorem r_Pc_σσ {z : D} (hz : ¬ Γ.rK R z) (hp : rPc h z) : rPc h (Γ.σ (Γ.σ z)) := by
  obtain ⟨d, i, hi, rfl, hv⟩ := hp
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact absurd d.2.1 hz
  obtain ⟨s, rfl⟩ : ∃ s, i = s + 1 := ⟨i - 1, by omega⟩
  have he : Γ.σ (Γ.σ ((Γ.straight ^ (s + 1)) d.1)) = Γ.α ((Γ.straight ^ s) d.1) := by
    rw [r_pow_succ, j_straight_apply, Γ.j_σ4]
  rw [he]
  exact r_Pc_α h ⟨d, s, by omega, rfl, hv⟩

open Classical in
theorem r_segBdry_lift (hh : MapFacts.segBdry (Γ.rσ R) (Γ.rα R) h = 0) :
    Γ.jSegBdry (Quotient.lift (rF h) fun a b hab => by
      obtain ⟨i, rfl⟩ := hab.exists_nat_pow_eq
      clear hab
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [ih, pow_succ', Perm.mul_apply]
        unfold rF
        rw [if_congr (r_Pc_α_iff h _) rfl rfl]) = 0 := by
  classical
  funext x
  obtain ⟨y, rfl⟩ := x.exists_mk
  change ∑ z ∈ orbitFinset Γ.σ y, rF h z = 0
  by_cases hK : Γ.rK R y
  · by_cases hk : Γ.Keep R y
    · rw [← r_sum_orbitFinset_σ (fun z => rF h z) ⟨y, hk⟩]
      have h0 := congrFun hh (Orbit.mk _ ⟨y, hk⟩)
      change ∑ z ∈ orbitFinset (Γ.rσ R) ⟨y, hk⟩, h (Orbit.mk (Γ.rα R) z) = 0 at h0
      rw [← h0]
      refine sum_congr rfl fun z _ => ?_
      unfold rF
      have := r_Pc_owner h (d := z) (i := 0) (Nat.zero_le _)
      rw [pow_zero, Perm.one_apply] at this
      rw [if_congr this rfl rfl, r_zmod2_ite]
    · refine sum_eq_zero fun z hz => ?_
      have hzK : Γ.rK R z := by
        unfold rK; rw [crossingOf, ← (Orbit.mk_eq_mk.2 (mem_orbitFinset.1 hz))]; exact hK
      have hzk : ¬ Γ.Keep R z := fun h' =>
        hk (r_keep_of_sameCycle_σ h' (mem_orbitFinset.1 hz).symm)
      unfold rF
      rw [if_neg]
      rintro ⟨d, i, hi, rfl, -⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact hzk d.2
      · exact r_notK_pow d.2.1 hi0 hi hzK
  · rw [show orbitFinset Γ.σ y = (Γ.crossingOf y).darts from rfl, j_sum_darts_crossingOf]
    have hK1 : ¬ Γ.rK R (Γ.σ y) := by rwa [r_rK_σ]
    have e1 : rF h (Γ.σ (Γ.σ y)) = rF h y := by
      unfold rF
      refine if_congr ⟨fun hp => ?_, r_Pc_σσ h hK⟩ rfl rfl
      have := r_Pc_σσ h (by rwa [r_rK_σσ]) hp
      rwa [Γ.j_σ4] at this
    have e2 : rF h (Γ.σ (Γ.σ (Γ.σ y))) = rF h (Γ.σ y) := by
      unfold rF
      refine if_congr ⟨fun hp => ?_, r_Pc_σσ h hK1⟩ rfl rfl
      have := r_Pc_σσ h (by rwa [r_rK_σσ]) hp
      rwa [Γ.j_σ4] at this
    rw [e1, e2]
    generalize rF h y = a
    generalize rF h (Γ.σ y) = b
    fin_cases a <;> fin_cases b <;> decide

theorem r_cut (hh : MapFacts.segBdry (Γ.rσ R) (Γ.rα R) h = 0) :
    ∃ g, MapFacts.cellBdry (Γ.rσ R) (Γ.rα R) g = h := by
  classical
  obtain ⟨g, hg⟩ := Γ.j_mem_range_of_mem_ker _ (r_segBdry_lift h hh)
  have hgy : ∀ y, g (Γ.cellOf y) + g (Γ.cellOf (Γ.α y)) = rF h y := fun y => by
    rw [← j_cellBdry_segmentOf, hg]; rfl
  have hr : ∀ w, Γ.curve w ∈ R → g (Γ.cellOf (Γ.α w)) = g (Γ.cellOf w) := by
    intro w hw
    have := hgy w
    unfold rF at this
    rw [if_neg (r_Pc_curve h hw)] at this
    rw [j_zmod2_eq_add_of_add_eq this, add_zero]
  refine ⟨rCellFun g hr, funext fun s => ?_⟩
  obtain ⟨d, rfl⟩ := s.exists_mk
  rw [MapFacts.cellBdry_mk r_rα_α r_rα_ne r_connected, r_cellFun_add, hgy]
  unfold rF
  rw [if_congr (r_Pc_owner h le_rfl) rfl rfl, r_zmod2_ite]

end Euler

theorem r_euler [Nonempty (Γ.RD R)] :
    (Fintype.card (Orbit (Γ.rσ R)) : ℤ) - Fintype.card (Orbit (Γ.rα R)) +
      Fintype.card (Orbit (Γ.rσ R * Γ.rα R)) = 2 :=
  r_euler_of_cut r_rα_α r_rα_ne r_connected fun h hh => r_cut h hh

end SConf

end Pca.Sweep
