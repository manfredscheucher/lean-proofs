/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package R (removal), the ∞-arc of the result

Helper file for `Pca/Sweep/Removal.lean`. For a nonempty result: the start of the new ∞-arc is the
owner `rOwn` of the old start `rZ` (the joined segment containing it, `rZ = straight^rM rOwn`), and
the new number of inner crossings `rL` is the number of kept crossings among the old inner
crossings. Then the inner crossings of the new arc are the kept inner crossings of the old one
(`r_infVertex`), and `rL` is at most the period (`r_rL_le`).
-/
import Pca.Sweep.R_Build

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}


theorem r_period_le {X : Type*} [Fintype X] [DecidableEq X] {f : Perm X} {x : X} {k : ℕ}
    (hk : 0 < k) (h : (f ^ k) x = x) : period f x ≤ k :=
  Nat.find_min' _ ⟨hk, by rwa [← MapFacts.pow_apply_eq_iterate]⟩

theorem r_pow_period {X : Type*} [Fintype X] [DecidableEq X] (f : Perm X) (x : X) :
    (f ^ period f x) x = x := by
  rw [MapFacts.pow_apply_eq_iterate]; exact iterate_period f x

theorem r_period_pow_le {X : Type*} [Fintype X] [DecidableEq X] (f : Perm X) (x : X) (m : ℕ) :
    period f ((f ^ m) x) ≤ period f x := by
  refine r_period_le (period_pos f x) ?_
  rw [← Perm.mul_apply, ← pow_add, add_comm, pow_add, Perm.mul_apply, r_pow_period]

theorem r_inv_apply {X : Type*} (f : Perm X) (x : X) : f⁻¹ (f x) = x := by
  rw [Perm.inv_def]; exact f.symm_apply_apply x

theorem r_apply_inv {X : Type*} (f : Perm X) (x : X) : f (f⁻¹ x) = x := by
  rw [Perm.inv_def]; exact f.apply_symm_apply x

namespace SConf

variable {Γ : SConf n D} {R : Finset (Fin n)}

/-- The owner of a dart of `S`: the joined segment containing it. -/
theorem r_owner [Nonempty (Γ.RD R)] {z : D} (hz : Γ.curve z = Γ.S) :
    ∃ (o : Γ.RD R) (m : ℕ), m ≤ Γ.rJ R o.1 ∧ (Γ.straight ^ m) o.1 = z := by
  classical
  obtain ⟨d0⟩ := ‹Nonempty (Γ.RD R)›
  obtain ⟨e, he, hde⟩ := d0.2.2
  have hke := r_keep_of_eqvGen d0.2 hde
  have hw : ∃ w, Γ.rK R w ∧ Γ.straight.SameCycle w z := by
    rcases Γ.isSConf.straight z e (hz.trans he.symm) with h | h
    · exact ⟨e, hke.1, h.symm⟩
    · exact ⟨_, (Γ.r_rK_σσ R e).2 hke.1, h.symm⟩
  obtain ⟨w, hwK, hwz⟩ := hw
  have hex : ∃ m, Γ.rK R ((Γ.straight ^ m)⁻¹ z) := by
    obtain ⟨m, hm⟩ := hwz.exists_nat_pow_eq
    exact ⟨m, by rw [← hm, r_inv_apply]; exact hwK⟩
  set m := Nat.find hex
  set o := (Γ.straight ^ m)⁻¹ z
  have hoz : (Γ.straight ^ m) o = z := r_apply_inv _ _
  have hoS : Γ.curve o = Γ.S := by rw [← hz, ← hoz, r_curve_pow]
  have ho : Γ.Keep R o := r_keep_S hoS (Nat.find_spec hex)
  refine ⟨⟨o, ho⟩, m, ?_, hoz⟩
  show m ≤ Γ.rJ R o
  by_contra hlt
  push Not at hlt
  have h1 := r_K_end ho.1
  rw [← r_rK_straight, ← r_pow_succ] at h1
  have h2 : (Γ.straight ^ (m - (Γ.rJ R o + 1)))⁻¹ z = (Γ.straight ^ (Γ.rJ R o + 1)) o := by
    rw [← hoz, MapFacts.pow_inv_pow_apply _ (by omega), show m - (m - (Γ.rJ R o + 1)) =
      Γ.rJ R o + 1 by omega]
  exact Nat.find_min hex (show m - (Γ.rJ R o + 1) < m by omega) (h2 ▸ h1)

theorem r_D_nonempty (Γ : SConf n D) (R : Finset (Fin n)) [h : Nonempty (Γ.RD R)] :
    Nonempty D := ⟨h.some.1⟩

/-- The start of the ∞-arc of `Γ`. -/
noncomputable def rZ (Γ : SConf n D) (R : Finset (Fin n)) [Nonempty (Γ.RD R)] : D := Γ.infStart.get (Γ.infStart_isSome (r_D_nonempty Γ R))

variable [Nonempty (Γ.RD R)]

theorem r_rZ_eq : Γ.infStart = some (Γ.rZ R) := (Option.some_get _).symm

theorem r_rZ_mem_arc : Γ.rZ R ∈ Γ.infArc := by
  unfold infArc arcOf
  rw [(r_rZ_eq (Γ := Γ) (R := R))]
  exact mem_image.2 ⟨0, mem_range.2 (Nat.succ_pos _), rfl⟩

theorem r_rZ_sweep : Γ.curve (Γ.rZ R) = Γ.S ∧ Γ.side (Γ.cellOf (Γ.α (Γ.rZ R))) = 1 :=
  Γ.infArc_sweep _ (r_rZ_mem_arc (Γ := Γ) (R := R))

noncomputable def rOwn (Γ : SConf n D) (R : Finset (Fin n)) [Nonempty (Γ.RD R)] : Γ.RD R := Classical.choose (r_owner (R := R) (r_rZ_sweep (Γ := Γ) (R := R)).1)

noncomputable def rM (Γ : SConf n D) (R : Finset (Fin n)) [Nonempty (Γ.RD R)] : ℕ := Classical.choose (Classical.choose_spec (r_owner (R := R) (r_rZ_sweep (Γ := Γ) (R := R)).1))

theorem r_rM_le : Γ.rM R ≤ Γ.rJ R (Γ.rOwn R).1 :=
  (Classical.choose_spec (Classical.choose_spec (r_owner (R := R) (r_rZ_sweep (Γ := Γ) (R := R)).1))).1

theorem r_rM_eq : (Γ.straight ^ Γ.rM R) (Γ.rOwn R).1 = Γ.rZ R :=
  (Classical.choose_spec (Classical.choose_spec (r_owner (R := R) (r_rZ_sweep (Γ := Γ) (R := R)).1))).2

open Classical in
/-- The number of kept crossings among the inner crossings of the old arc. -/
noncomputable def rL (Γ : SConf n D) (R : Finset (Fin n)) [Nonempty (Γ.RD R)] : ℕ :=
  ((range (Γ.rM R + Γ.infLen)).filter
    (fun t => Γ.Keep R ((Γ.straight ^ (t + 1)) (Γ.rOwn R).1))).card

theorem r_piece_own : Γ.Piece R (Γ.rOwn R).1 (Γ.rZ R) :=
  (Γ.r_piece_iff R).2 ⟨Γ.rM R, fun _ hi => r_notK_lt (Γ.rOwn R).2.1 (by
    have := (r_rM_le (Γ := Γ) (R := R)); omega), (r_rM_eq (Γ := Γ) (R := R))⟩

theorem r_own_S : Γ.curve (Γ.rOwn R).1 = Γ.S := by
  rw [← (r_rZ_sweep (Γ := Γ) (R := R)).1, ← (r_rM_eq (Γ := Γ) (R := R)), r_curve_pow]

theorem r_tau_one : Γ.rM R < r_isFR_straight.tau (Γ.rOwn R) 1 := by
  by_contra hle
  push Not at hle
  have h0 := r_isFR_straight.tau_lt_succ (Γ.rOwn R) 0
  have hk := r_hK ((straightPerm (Γ.rσ R) (Γ.rα R) ^ 1) (Γ.rOwn R))
  rw [r_isFR_straight.pow_apply] at hk
  exact r_notK_pow (Γ.rOwn R).2.1 (by simpa [MapFacts.IsFR.tau] using h0)
    (le_trans hle (r_rM_le (Γ := Γ) (R := R))) hk.1

theorem r_tau_le (j : ℕ) :
    r_isFR_straight.tau (Γ.rOwn R) j ≤ Γ.rM R + Γ.infLen ↔ j ≤ Γ.rL R := by
  classical
  unfold rL
  convert r_tau_le_iff r_isFR_straight r_hK (Γ.rOwn R) (Γ.rM R + Γ.infLen) j

/-- The crossing at the end of `α' (straight'^i own)`. -/
theorem r_rCr_α_pow (i : ℕ) :
    rCr (Orbit.mk (Γ.rσ R) (Γ.rα R ((straightPerm (Γ.rσ R) (Γ.rα R) ^ i) (Γ.rOwn R)))) =
      Γ.crossingOf ((Γ.straight ^ r_isFR_straight.tau (Γ.rOwn R) (i + 1)) (Γ.rOwn R).1) := by
  rw [← r_isFR_straight.pow_apply, pow_succ', Perm.mul_apply, r_rCr_mk, r_rα_val]
  rw [show (straightPerm (Γ.rσ R) (Γ.rα R)) ((straightPerm (Γ.rσ R) (Γ.rα R) ^ i) (Γ.rOwn R)) =
    Γ.rσ R (Γ.rσ R (Γ.rα R ((straightPerm (Γ.rσ R) (Γ.rα R) ^ i) (Γ.rOwn R)))) from rfl,
    r_rσ_val, r_rσ_val, r_rα_val, r_crossingOf_σσ]

theorem r_infVertex (d : Γ.RD R) :
    (∃ i < Γ.rL R, rCr (Orbit.mk (Γ.rσ R)
        (Γ.rα R ((straightPerm (Γ.rσ R) (Γ.rα R) ^ i) (Γ.rOwn R)))) = Γ.crossingOf d.1) ↔
      Γ.IsInfVertex (Γ.crossingOf d.1) := by
  have hz := (r_rM_eq (Γ := Γ) (R := R))
  constructor
  · rintro ⟨i, hi, he⟩
    rw [r_rCr_α_pow] at he
    have h1 := (r_tau_le (Γ := Γ) (R := R) (i + 1)).2 (by omega)
    have h2 : r_isFR_straight.tau (Γ.rOwn R) 1 ≤ r_isFR_straight.tau (Γ.rOwn R) (i + 1) :=
      (r_isFR_straight.tau_strictMono _).monotone (by omega)
    have h3 := r_tau_one (Γ := Γ) (R := R)
    obtain ⟨i0, hi0⟩ : ∃ i0, r_isFR_straight.tau (Γ.rOwn R) (i + 1) = Γ.rM R + i0 + 1 :=
      ⟨r_isFR_straight.tau (Γ.rOwn R) (i + 1) - (Γ.rM R + 1), by omega⟩
    refine ⟨Γ.rZ R, (r_rZ_eq (Γ := Γ) (R := R)), i0, by omega, ?_⟩
    rw [← he, hi0, ← r_crossingOf_straight, ← r_pow_succ, ← hz, ← Perm.mul_apply, ← pow_add]
    congr 3; omega
  · rintro ⟨z0, hz0, i0, hi0, he⟩
    rw [(r_rZ_eq (Γ := Γ) (R := R)), Option.mem_def, Option.some_inj] at hz0
    subst hz0
    set t := Γ.rM R + i0 + 1
    have hst : (Γ.straight ^ t) (Γ.rOwn R).1 = (Γ.straight ^ (i0 + 1)) (Γ.rZ R) := by
      rw [← hz, ← Perm.mul_apply, ← pow_add]; congr 2; omega
    have hcr : Γ.crossingOf ((Γ.straight ^ t) (Γ.rOwn R).1) = Γ.crossingOf d.1 := by
      rw [hst, r_pow_succ, r_crossingOf_straight, he]
    have hK : Γ.rK R ((Γ.straight ^ t) (Γ.rOwn R).1) := by
      unfold rK; rw [hcr]; exact d.2.1
    obtain ⟨j, hj⟩ := r_isFR_straight.mem_of_mem r_hK (Γ.rOwn R) t (r_keep_pow (Γ.rOwn R).2 hK)
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · simp [MapFacts.IsFR.tau] at hj
      · exact h
    have hjL := (r_tau_le (Γ := Γ) (R := R) j).1 (by omega)
    refine ⟨j - 1, by omega, ?_⟩
    rw [r_rCr_α_pow, Nat.sub_add_cancel hj0, hj, hcr]

theorem r_rL_le : Γ.rL R ≤ period (straightPerm (Γ.rσ R) (Γ.rα R)) (Γ.rOwn R) := by
  set P' := period (straightPerm (Γ.rσ R) (Γ.rα R)) (Γ.rOwn R)
  by_contra hlt
  push Not at hlt
  have h1 := (r_tau_le (Γ := Γ) (R := R) (P' + 1)).2 (by omega)
  have hP : (straightPerm (Γ.rσ R) (Γ.rα R) ^ P') (Γ.rOwn R) = Γ.rOwn R := r_pow_period _ _
  have h2 : r_isFR_straight.tau (Γ.rOwn R) (P' + 1) =
      r_isFR_straight.tau (Γ.rOwn R) P' + r_isFR_straight.tau (Γ.rOwn R) 1 := by
    show _ + r_isFR_straight.time _ = _
    rw [hP]; simp [MapFacts.IsFR.tau]
  have h3 : period Γ.straight (Γ.rOwn R).1 ≤ r_isFR_straight.tau (Γ.rOwn R) P' := by
    refine r_period_le ?_ ?_
    · have := r_isFR_straight.tau_strictMono (Γ.rOwn R)
        (period_pos (straightPerm (Γ.rσ R) (Γ.rα R)) (Γ.rOwn R))
      simpa [MapFacts.IsFR.tau] using this
    · rw [← r_isFR_straight.pow_apply, hP]
  have h4 := r_period_pow_le Γ.straight (Γ.rOwn R).1 (Γ.rM R)
  rw [(r_rM_eq (Γ := Γ) (R := R))] at h4
  have h5 := Γ.infLen_le _ (r_rZ_eq (Γ := Γ) (R := R))
  have h6 := r_tau_one (Γ := Γ) (R := R)
  change Γ.infLen ≤ period Γ.straight (Γ.rZ R) at h5
  omega

theorem r_arc_sweep (i : ℕ) :
    Γ.curve ((straightPerm (Γ.rσ R) (Γ.rα R) ^ i) (Γ.rOwn R)).1 = Γ.S ∧
      Γ.side (Γ.cellOf (Γ.rHit R ((straightPerm (Γ.rσ R) (Γ.rα R) ^ i) (Γ.rOwn R)).1)) = 1 := by
  rw [r_isFR_straight.pow_apply]
  set k := (Γ.straight ^ r_isFR_straight.tau (Γ.rOwn R) i) (Γ.rOwn R).1
  have hkK : Γ.rK R k := by
    have := (r_hK ((straightPerm (Γ.rσ R) (Γ.rα R) ^ i) (Γ.rOwn R))).1
    rwa [r_isFR_straight.pow_apply] at this
  refine ⟨by rw [r_curve_pow]; exact (r_own_S (Γ := Γ) (R := R)), ?_⟩
  rw [r_hit_eq hkK, r_sweep_pow (by rw [r_curve_pow]; exact (r_own_S (Γ := Γ) (R := R))), r_sweep_pow (r_own_S (Γ := Γ) (R := R)),
    ← (r_rZ_sweep (Γ := Γ) (R := R)).2, ← (r_rM_eq (Γ := Γ) (R := R)), r_sweep_pow (r_own_S (Γ := Γ) (R := R))]

end SConf

end Pca.Sweep
