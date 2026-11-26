/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# SH Lemma 3.5 in graph language: the lower side does not matter (package L)

"LEMMA 3.5. We can choose a minimum counterexample such that all of the curves of `Γ` are rays
to infinity below the sweep `c`. PROOF. Map the bi-infinite sweeping curve `c` to a line `c'` by a
continuous mapping of the plane onto itself, cut all curves below `c'` and extend them
perpendicularly to infinity, then apply the inverse mapping. When this procedure is applied to a
minimum counterexample, neither the arrangement above the sweep nor the size is affected. Thus, it
remains a minimum counterexample." (SH p. 318)

On the sphere nothing can be sent to infinity below `S`; the translation is: everything SH look at
(stuck, progress, finished, size) depends only on the **upper side** of `S`, i.e. on the cells
above `S` with their darts, `φ`, `α` on curve darts, the labels and the ∞-arc. `UpperIso Γ Γ'` says
that `Γ` and `Γ'` have the same upper side (`f` maps the darts whose cell is above `S`). The lower
side is only needed to make the object a sphere map; constructions that change the upper side
(untangling, Lemma 3.9; the surgery, Lemma 3.11) choose a new lower side. Its existence is SH's
chord argument of Lemma 3.12 (p. 326): two arcs with interleaved ends cross an odd number of times
above `S`, so closing every upper arc by a chord below `S` keeps the two-intersection property.
-/
import Pca.Sweep.Jordan
import Pca.Sweep.LD_Basic

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

/-- `Γ` and `Γ'` have isomorphic upper sides: `f` maps the darts of the cells above `S`
bijectively onto those of `Γ'`, commuting with `φ`, with `α` on curve darts, with the labels (up to
the injective relabelling `lab`, `lab S = S'`) and with the ∞-arc (its darts, its start and its
number of inner crossings). -/
structure UpperIso {n' : ℕ} {D' : Type u} [Fintype D'] [DecidableEq D'] (Γ : SConf n D)
    (Γ' : SConf n' D') where
  f : D → D'
  lab : Fin n → Fin n'
  lab_inj : Function.Injective lab
  lab_S : lab Γ.S = Γ'.S
  up : ∀ d, Γ.Up (Γ.cellOf d) → Γ'.Up (Γ'.cellOf (f d))
  inj : ∀ d e, Γ.Up (Γ.cellOf d) → Γ.Up (Γ.cellOf e) → f d = f e → d = e
  surj : ∀ d', Γ'.Up (Γ'.cellOf d') → ∃ d, Γ.Up (Γ.cellOf d) ∧ f d = d'
  φ : ∀ d, Γ.Up (Γ.cellOf d) → f (Γ.φ d) = Γ'.φ (f d)
  α : ∀ d, Γ.Up (Γ.cellOf d) → Γ.curve d ≠ Γ.S → f (Γ.α d) = Γ'.α (f d)
  curve : ∀ d, Γ.Up (Γ.cellOf d) → Γ'.curve (f d) = lab (Γ.curve d)
  infArc : ∀ d, Γ.Up (Γ.cellOf d) → Γ.curve d = Γ.S →
    (Γ.α d ∈ Γ.infArc ↔ Γ'.α (f d) ∈ Γ'.infArc)
  infStart : ∀ d, Γ.Up (Γ.cellOf d) → Γ.curve d = Γ.S →
    (Γ.infStart = some (Γ.α d) ↔ Γ'.infStart = some (Γ'.α (f d)))
  infLen : Γ'.infLen = Γ.infLen

variable {Γ : SConf n D} {n' : ℕ} {D' : Type u} [Fintype D'] [DecidableEq D'] {Γ' : SConf n' D'}

namespace UpperIso

variable (e : UpperIso Γ Γ')

/-! ### Transfer of the local structure (package L helpers) -/

private theorem ld_curve_S {d : D} (hd : Γ.Up (Γ.cellOf d)) :
    Γ'.curve (e.f d) = Γ'.S ↔ Γ.curve d = Γ.S := by
  rw [e.curve d hd, ← e.lab_S]; exact e.lab_inj.eq_iff

private theorem ld_φinv {d : D} (hd : Γ.Up (Γ.cellOf d)) : e.f (Γ.φ⁻¹ d) = Γ'.φ⁻¹ (e.f d) := by
  have hu : Γ.Up (Γ.cellOf (Γ.φ⁻¹ d)) := by rw [Γ.ld_cellOf_φinv]; exact hd
  have h := e.φ _ hu
  rw [ld_perm_apply_inv] at h
  rw [h]
  exact (Perm.inv_eq_iff_eq.2 rfl).symm

private theorem ld_pow {d : D} (hd : Γ.Up (Γ.cellOf d)) (k : ℕ) :
    e.f ((Γ.φ ^ k) d) = (Γ'.φ ^ k) (e.f d) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, pow_succ', Perm.mul_apply,
      e.φ _ (by rw [Γ.ld_cellOf_pow]; exact hd), ih]

private theorem ld_sameCycle {b c : D} (hb : Γ.Up (Γ.cellOf b)) (hc : Γ.Up (Γ.cellOf c)) :
    Γ'.φ.SameCycle (e.f b) (e.f c) ↔ Γ.φ.SameCycle b c := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [← e.ld_pow hb] at hk
    have := e.inj _ _ (by rw [Γ.ld_cellOf_pow]; exact hb) hc hk
    rw [← this]
    exact Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [← hk, e.ld_pow hb]
    exact Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)

private theorem ld_mem_cell {b c : D} (hb : Γ.Up (Γ.cellOf b)) (hc : Γ.Up (Γ.cellOf c)) :
    e.f c ∈ (Γ'.cellOf (e.f b)).darts ↔ c ∈ (Γ.cellOf b).darts := by
  simp only [cellOf, Orbit.darts_mk, mem_orbitFinset]
  exact e.ld_sameCycle hb hc

private theorem ld_up_of_mem {b c : D} (hb : Γ.Up (Γ.cellOf b)) (hc : c ∈ (Γ.cellOf b).darts) :
    Γ.Up (Γ.cellOf c) := by
  have : Γ.cellOf c = Γ.cellOf b := Orbit.mem_darts.1 hc
  unfold Up; rw [this]; exact hb

private theorem ld_size {b : D} (hb : Γ.Up (Γ.cellOf b)) :
    (Γ'.cellOf (e.f b)).size = (Γ.cellOf b).size := by
  unfold Orbit.size
  have him : (Γ'.cellOf (e.f b)).darts = (Γ.cellOf b).darts.image e.f := by
    ext c'
    rw [mem_image]
    constructor
    · intro hc'
      obtain ⟨c, hc, rfl⟩ := e.surj c' (ld_up_of_mem (e.up b hb) hc')
      exact ⟨c, (e.ld_mem_cell hb hc).1 hc', rfl⟩
    · rintro ⟨c, hc', rfl⟩
      exact (e.ld_mem_cell hb (ld_up_of_mem hb hc')).2 hc'
  rw [him, card_image_of_injOn]
  intro x hx y hy h
  exact e.inj _ _ (ld_up_of_mem hb hx) (ld_up_of_mem hb hy) h

private theorem ld_σ {d : D} (hd : Γ.Up (Γ.cellOf d)) (hc : Γ.curve d ≠ Γ.S) :
    e.f (Γ.σ d) = Γ'.σ (e.f d) := by
  have hα : Γ.Up (Γ.cellOf (Γ.α d)) := (Γ.ld_up_α_iff hc).2 hd
  have h1 := e.φ _ hα
  rw [e.α d hd hc] at h1
  simpa only [j_φ_apply, j_α_α] using h1

private theorem ld_σinv {b : D} (hb : Γ.Up (Γ.cellOf b)) (hS : Γ.curve b = Γ.S) :
    e.f (Γ.σ⁻¹ b) = Γ'.σ⁻¹ (e.f b) := by
  have h := e.ld_σ (Γ.ld_up_σinv hS hb) (Γ.ld_curve_σinv_ne hS)
  rw [ld_σ_σinv] at h
  rw [h]
  exact (Perm.inv_eq_iff_eq.2 rfl).symm

private theorem ld_next_eq {n₀ : ℕ} {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] (Δ : SConf n₀ D₀)
    (b : D₀) : Δ.α (Δ.straight (Δ.α b)) = Δ.φ⁻¹ (Δ.σ⁻¹ b) := by
  rw [ld_φinv_apply, j_straight_apply, j_α_α, Δ.ld_σinv_eq (Δ.σ⁻¹ b), ld_σ_σinv]

/-- The step along `S` above the sweep commutes with `f`. -/
private theorem ld_next {b : D} (hb : Γ.Up (Γ.cellOf b)) (hS : Γ.curve b = Γ.S) :
    e.f (Γ.α (Γ.straight (Γ.α b))) = Γ'.α (Γ'.straight (Γ'.α (e.f b))) ∧
      Γ.Up (Γ.cellOf (Γ.α (Γ.straight (Γ.α b)))) ∧ Γ.curve (Γ.α (Γ.straight (Γ.α b))) = Γ.S := by
  have hu := Γ.ld_up_σinv hS hb
  refine ⟨?_, ?_, ?_⟩
  · rw [ld_next_eq, ld_next_eq, e.ld_φinv hu, e.ld_σinv hb hS]
  · rw [ld_next_eq, Γ.ld_cellOf_φinv]; exact hu
  · rw [j_curve_α, j_curve_straight, j_curve_α]; exact hS

private theorem ld_arcPow {b : D} (hb : Γ.Up (Γ.cellOf b)) (hS : Γ.curve b = Γ.S) (i : ℕ) :
    e.f (Γ.α ((Γ.straight ^ i) (Γ.α b))) = Γ'.α ((Γ'.straight ^ i) (Γ'.α (e.f b))) ∧
      Γ.Up (Γ.cellOf (Γ.α ((Γ.straight ^ i) (Γ.α b)))) ∧
      Γ.curve (Γ.α ((Γ.straight ^ i) (Γ.α b))) = Γ.S := by
  induction i with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> simp only [pow_zero, Perm.one_apply, j_α_α] <;> assumption
  | succ i ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have key : ∀ {n₀ : ℕ} {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] (Δ : SConf n₀ D₀) (x : D₀),
        Δ.α ((Δ.straight ^ (i + 1)) x) = Δ.α (Δ.straight (Δ.α (Δ.α ((Δ.straight ^ i) x)))) := by
      intro n₀ D₀ _ _ Δ x
      rw [j_α_α, pow_succ', Perm.mul_apply]
    obtain ⟨g1, g2, g3⟩ := e.ld_next h2 h3
    rw [key Γ, key Γ', ← h1]
    exact ⟨g1, g2, g3⟩

private theorem ld_arc0 {z : D} (hz : z ∈ Γ.infStart) :
    Γ.curve (Γ.α z) = Γ.S ∧ Γ.Up (Γ.cellOf (Γ.α z)) := by
  have h := Γ.ld_arc hz (Nat.zero_le Γ.infLen)
  simpa only [pow_zero, Perm.one_apply] using h

private theorem ld_infStart : Γ'.infStart = Γ.infStart.map (fun z => Γ'.α (e.f (Γ.α z))) := by
  cases hz : Γ.infStart with
  | some z =>
    have h0 := ld_arc0 (Γ := Γ) (Option.mem_def.2 hz)
    have := (e.infStart _ h0.2 h0.1).1 (by rw [hz, j_α_α])
    rw [this]; rfl
  | none =>
    cases hz' : Γ'.infStart with
    | none => rfl
    | some z' =>
      have h0 := ld_arc0 (Γ := Γ') (Option.mem_def.2 hz')
      obtain ⟨d, hd, hfd⟩ := e.surj _ h0.2
      have hdS : Γ.curve d = Γ.S := (e.ld_curve_S hd).1 (hfd ▸ h0.1)
      have := (e.infStart d hd hdS).2 (by rw [hz', hfd, j_α_α])
      rw [hz] at this
      cases this

private theorem ld_infB {b : D} (hb : Γ.Up (Γ.cellOf b)) (hS : Γ.curve b = Γ.S) :
    Γ'.ldInfB (e.f b) ↔ Γ.ldInfB b := by
  unfold ldInfB
  rw [e.ld_infStart, e.infLen]
  constructor
  · rintro ⟨z', hz', i, hi, h⟩
    obtain ⟨z, hz, rfl⟩ := Option.mem_map.1 hz'
    have hA := Γ.ld_arc hz hi.le
    have h0 := ld_arc0 hz
    obtain ⟨h1, -, -⟩ := e.ld_arcPow h0.2 h0.1 i
    rw [j_α_α] at h1
    exact ⟨z, hz, i, hi, e.inj _ _ hA.2 hb (by rw [h1, h])⟩
  · rintro ⟨z, hz, i, hi, rfl⟩
    have h0 := ld_arc0 hz
    obtain ⟨h1, -, -⟩ := e.ld_arcPow h0.2 h0.1 i
    rw [j_α_α] at h1
    exact ⟨_, Option.mem_map_of_mem _ hz, i, hi, h1.symm⟩

private theorem ld_finV {b : D} (hb : Γ.Up (Γ.cellOf b)) (hS : Γ.curve b = Γ.S) :
    Γ'.IsFinVertex (Γ'.crossingOf (e.f b)) ↔ Γ.IsFinVertex (Γ.crossingOf b) := by
  rw [Γ'.ld_finVertex_iff ((e.ld_curve_S hb).2 hS) (e.up b hb), Γ.ld_finVertex_iff hS hb,
    e.ld_infB hb hS]

private theorem ld_onCurve {b : D} (hb : Γ.Up (Γ.cellOf b)) (hS : Γ.curve b = Γ.S) (γ : Fin n) :
    Γ'.OnCurve (e.lab γ) (Γ'.crossingOf (e.f b)) ↔ Γ.OnCurve γ (Γ.crossingOf b) := by
  rw [Γ'.ld_onCurve_S ((e.ld_curve_S hb).2 hS), Γ.ld_onCurve_S hS, ← e.ld_σinv hb hS,
    e.curve _ (Γ.ld_up_σinv hS hb), ← e.lab_S, e.lab_inj.eq_iff, e.lab_inj.eq_iff]

/-! ### Generic transfer of statements about darts above `S` -/

private theorem ld_exists (P : D → Prop) (P' : D' → Prop)
    (h : ∀ d, Γ.Up (Γ.cellOf d) → (P' (e.f d) ↔ P d)) :
    (∃ d', Γ'.Up (Γ'.cellOf d') ∧ P' d') ↔ ∃ d, Γ.Up (Γ.cellOf d) ∧ P d := by
  constructor
  · rintro ⟨d', hu', hp'⟩
    obtain ⟨d, hd, rfl⟩ := e.surj d' hu'
    exact ⟨d, hd, (h d hd).1 hp'⟩
  · rintro ⟨d, hd, hp⟩
    exact ⟨e.f d, e.up d hd, (h d hd).2 hp⟩

private theorem ld_card (P : D → Prop) (P' : D' → Prop) [DecidablePred P] [DecidablePred P']
    (h : ∀ d, Γ.Up (Γ.cellOf d) → (P' (e.f d) ↔ P d)) :
    (univ.filter (fun d' => Γ'.Up (Γ'.cellOf d') ∧ P' d')).card =
      (univ.filter (fun d => Γ.Up (Γ.cellOf d) ∧ P d)).card := by
  symm
  refine card_bij (fun d _ => e.f d) ?_ ?_ ?_
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    exact ⟨e.up d hd.1, (h d hd.1).2 hd.2⟩
  · intro a ha b hb hab
    simp only [mem_filter, mem_univ, true_and] at ha hb
    exact e.inj a b ha.1 hb.1 hab
  · intro d' hd'
    simp only [mem_filter, mem_univ, true_and] at hd'
    obtain ⟨d, hd, rfl⟩ := e.surj d' hd'.1
    exact ⟨d, by simp only [mem_filter, mem_univ, true_and]; exact ⟨hd, (h d hd).1 hd'.2⟩, rfl⟩

/-! ### The notions of SH section 2 -/

private theorem ld_hitsP (γ : Fin n) (d : D) (hd : Γ.Up (Γ.cellOf d)) :
    (Γ'.curve (e.f d) = Γ'.S ∧ Γ'.IsFinVertex (Γ'.crossingOf (e.f d)) ∧
      Γ'.OnCurve (e.lab γ) (Γ'.crossingOf (e.f d))) ↔
    (Γ.curve d = Γ.S ∧ Γ.IsFinVertex (Γ.crossingOf d) ∧ Γ.OnCurve γ (Γ.crossingOf d)) := by
  constructor
  · rintro ⟨hS', hF, hO⟩
    have hS := (e.ld_curve_S hd).1 hS'
    exact ⟨hS, (e.ld_finV hd hS).1 hF, (e.ld_onCurve hd hS γ).1 hO⟩
  · rintro ⟨hS, hF, hO⟩
    exact ⟨(e.ld_curve_S hd).2 hS, (e.ld_finV hd hS).2 hF, (e.ld_onCurve hd hS γ).2 hO⟩

private theorem ld_hits (γ : Fin n) : Γ'.numSweepHits (e.lab γ) = Γ.numSweepHits γ := by
  classical
  unfold numSweepHits
  rw [Γ'.ld_card_onSweep' _ (fun x hx => hx.1.1), Γ.ld_card_onSweep' _ (fun x hx => hx.1.1)]
  exact e.ld_card _ _ (e.ld_hitsP γ)

private theorem ld_meets (γ : Fin n) : Γ'.MeetsSweep (e.lab γ) ↔ Γ.MeetsSweep γ := by
  rw [Γ'.ld_meetsSweep_iff, Γ.ld_meetsSweep_iff]
  exact e.ld_exists _ _ (e.ld_hitsP γ)

private theorem ld_ray (γ : Fin n) : Γ'.IsRay (e.lab γ) ↔ Γ.IsRay γ := by
  unfold IsRay
  rw [e.ld_hits, Γ'.ld_infOn_iff, Γ.ld_infOn_iff]
  refine and_congr_right fun _ => e.ld_exists _ _ fun d hd => ?_
  constructor
  · rintro ⟨hS', hI, hO⟩
    have hS := (e.ld_curve_S hd).1 hS'
    exact ⟨hS, (e.ld_infB hd hS).1 hI, (e.ld_onCurve hd hS γ).1 hO⟩
  · rintro ⟨hS, hI, hO⟩
    exact ⟨(e.ld_curve_S hd).2 hS, (e.ld_infB hd hS).2 hI, (e.ld_onCurve hd hS γ).2 hO⟩

private theorem ld_present (γ : Fin n) : Γ'.Present (e.lab γ) ↔ Γ.Present γ := by
  rw [Γ'.ld_present_iff, Γ.ld_present_iff, ← e.lab_S, e.lab_inj.ne_iff]
  refine and_congr_right fun _ => e.ld_exists _ _ fun d hd => ?_
  rw [e.curve d hd, e.lab_inj.eq_iff, e.lab_inj.ne_iff]

private theorem ld_present_lab {γ' : Fin n'} (h : Γ'.Present γ') : ∃ γ, e.lab γ = γ' := by
  obtain ⟨-, d', rfl, -, hu'⟩ := h
  obtain ⟨d, hd, rfl⟩ := e.surj d' hu'
  exact ⟨Γ.curve d, (e.curve d hd).symm⟩

include e in
private theorem ld_terminal : Γ'.Terminal ↔ Γ.Terminal := by
  unfold Terminal
  rw [Γ'.ld_noAbove_iff, Γ.ld_noAbove_iff]
  refine and_congr ?_ ?_
  · refine not_congr (e.ld_exists _ _ fun d hd => ?_)
    rw [← e.lab_S, e.curve d hd, e.lab_inj.ne_iff]
    refine and_congr_right fun hc => ?_
    rw [← e.ld_σ hd hc, e.curve _ ((Γ.ld_up_σ_iff hc).2 hd), e.lab_inj.ne_iff]
  · constructor
    · intro h γ hP
      exact (e.ld_ray γ).1 (h _ ((e.ld_present γ).2 hP))
    · intro h γ' hP'
      obtain ⟨γ, rfl⟩ := e.ld_present_lab hP'
      exact (e.ld_ray γ).2 (h γ ((e.ld_present γ).1 hP'))

include e in
private theorem ld_emptyCell (k : ℕ) :
    (∃ d, Γ'.IsFinSeg d ∧ (Γ'.upperCell d).size = k) ↔
      ∃ d, Γ.IsFinSeg d ∧ (Γ.upperCell d).size = k := by
  rw [Γ'.ld_emptyCell_iff, Γ.ld_emptyCell_iff]
  refine e.ld_exists _ _ fun d hd => ?_
  constructor
  · rintro ⟨hS', hA, hk⟩
    have hS := (e.ld_curve_S hd).1 hS'
    exact ⟨hS, fun h => hA ((e.infArc d hd hS).1 h), by rw [← e.ld_size hd]; exact hk⟩
  · rintro ⟨hS, hA, hk⟩
    exact ⟨(e.ld_curve_S hd).2 hS, fun h => hA ((e.infArc d hd hS).2 h),
      by rw [e.ld_size hd]; exact hk⟩

include e in
private theorem ld_canTakeLoop : Γ'.CanTakeLoop ↔ Γ.CanTakeLoop := by
  rw [Γ'.ld_canTakeLoop_iff, Γ.ld_canTakeLoop_iff]
  refine e.ld_exists _ _ fun b hb => ?_
  rw [e.ld_curve_S hb]
  refine and_congr_right fun _ => e.ld_exists _ _ fun c hc => ?_
  rw [e.ld_mem_cell hb hc, e.curve c hc, ← e.lab_S, e.lab_inj.ne_iff, e.ld_meets]

include e in
private theorem ld_progress : Γ'.Progress ↔ Γ.Progress := by
  unfold Progress EmptyHumpAt EmptyTriAt
  rw [e.ld_emptyCell 2, e.ld_emptyCell 3, e.ld_canTakeLoop]

end UpperIso

/-- **SH Lemma 3.5** (graph form): stuck, the size and the operations depend only on the upper
side. -/
theorem UpperIso.stuck_iff (e : UpperIso Γ Γ') : Γ'.Stuck ↔ Γ.Stuck := by
  unfold Stuck
  rw [e.ld_terminal, e.ld_progress]

theorem UpperIso.numVertices_eq (e : UpperIso Γ Γ') : Γ'.numVertices = Γ.numVertices := by
  classical
  have h' := Γ'.ld_numVertices
  have h := Γ.ld_numVertices
  have c1 := e.ld_card (fun d => Γ.curve d = Γ.S ∧ Γ.IsFinVertex (Γ.crossingOf d))
    (fun d' => Γ'.curve d' = Γ'.S ∧ Γ'.IsFinVertex (Γ'.crossingOf d')) fun d hd => by
      constructor
      · rintro ⟨hS', hF⟩
        have hS := (e.ld_curve_S hd).1 hS'
        exact ⟨hS, (e.ld_finV hd hS).1 hF⟩
      · rintro ⟨hS, hF⟩
        exact ⟨(e.ld_curve_S hd).2 hS, (e.ld_finV hd hS).2 hF⟩
  have c2 := e.ld_card (fun d => Γ.curve d ≠ Γ.S ∧ Γ.curve (Γ.σ d) ≠ Γ.S)
    (fun d' => Γ'.curve d' ≠ Γ'.S ∧ Γ'.curve (Γ'.σ d') ≠ Γ'.S) fun d hd => by
      rw [← e.lab_S, e.curve d hd, e.lab_inj.ne_iff]
      refine and_congr_right fun hc => ?_
      rw [← e.ld_σ hd hc, e.curve _ ((Γ.ld_up_σ_iff hc).2 hd), e.lab_inj.ne_iff]
  rw [c1, c2, ← h] at h'
  omega

theorem UpperIso.numCurves_eq (e : UpperIso Γ Γ') : Γ'.numCurves = Γ.numCurves := by
  classical
  unfold numCurves
  have him : univ.filter Γ'.Present = (univ.filter Γ.Present).image e.lab := by
    ext γ'
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hP'
      obtain ⟨γ, rfl⟩ := e.ld_present_lab hP'
      exact ⟨γ, (e.ld_present γ).1 hP', rfl⟩
    · rintro ⟨γ, hP, rfl⟩
      exact (e.ld_present γ).2 hP
  rw [him, card_image_of_injective _ e.lab_inj]


end SConf

end Pca.Sweep
