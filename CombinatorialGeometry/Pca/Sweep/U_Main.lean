/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package U, helpers: the untangled configuration and its upper side

`UHyp.conf`: the sweep configuration after untangling (same darts, `σ`, `S`, ∞-arc; new `α'`,
labels, side function). Its upper side compared with `Γ`: the sweep darts, finite edges, vertices
on the sweep, the ∞-arc and the present curves are the same; the vertices above the sweep are
those of `Γ` except `v`.
-/
import Pca.Sweep.U_Psi

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {d a : D} {k : ℕ} {γ : Fin n}

section Hyp

variable (H : Γ.UHyp d a k γ)
include H

theorem UHyp.notM_S {z : D} (hz : Γ.curve z = Γ.S) : ∀ i, Γ.uM d a i ≠ z := by
  intro i h
  rw [← h, H.c_uM] at hz
  split_ifs at hz
  · exact H.c2S hz
  · exact H.c1S hz

theorem UHyp.notv_S {z : D} (hz : Γ.curve z = Γ.S) : Γ.crossingOf z ≠ Γ.crossingOf a := by
  intro h
  rcases H.v_iff.1 h with h' | h' | h' | h' <;> exact H.notM_S hz _ h'.symm

theorem UHyp.st_pow_S {z : D} (hz : Γ.curve z = Γ.S) (i : ℕ) :
    (H.st ^ i) z = (Γ.straight ^ i) z :=
  u_pow_eq_of_avoid (M := fun x => ∃ i, Γ.uM d a i = x) (H.st_eq_of_notM rfl) z i
    fun j _ ⟨m, hm⟩ => H.notM_S (by rw [u_curve_pow]; exact hz) m hm

theorem UHyp.period_S {z : D} (hz : Γ.curve z = Γ.S) :
    period H.st z = period Γ.straight z := by
  apply le_antisymm
  · exact u_period_le (period_pos _ _) (by rw [H.st_pow_S hz, u_pow_period])
  · exact u_period_le (period_pos _ _) (by rw [← H.st_pow_S hz, u_pow_period])

theorem UHyp.start_S {z : D} (hz : z ∈ Γ.infStart) : Γ.curve z = Γ.S := by
  have := Γ.infArc_sweep z (by
    unfold arcOf; rw [Option.mem_def.1 hz]
    exact mem_image.2 ⟨0, mem_range.2 (Nat.succ_pos _), rfl⟩)
  exact this.1

theorem UHyp.arcOf_eq : arcOf Γ.σ H.α' Γ.infStart Γ.infLen = arcOf Γ.σ Γ.α Γ.infStart Γ.infLen := by
  unfold arcOf
  cases hz : Γ.infStart with
  | none => rfl
  | some z =>
    have hS := H.start_S (Option.mem_def.2 hz)
    simp only [Option.elim]
    exact image_congr fun i _ => H.st_pow_S hS i

theorem UHyp.α'_S {z : D} (hz : Γ.curve z = Γ.S) : H.α' z = Γ.α z := H.α'_of (H.notM_S hz)

/-- The untangled configuration. -/
noncomputable def UHyp.conf : SConf n D where
  σ := Γ.σ
  α := H.α'
  curve := Γ.uCurve d k
  S := Γ.S
  isSConf :=
    { card_crossing := Γ.isSConf.card_crossing
      α_ne := H.uαf_ne
      α_α := H.uαf_invol
      curve_α := H.uCurve_α
      curve_σ := H.uCurve_σ
      curve_σσ := H.uCurve_σσ
      straight := H.straight_ax
      two_int := H.two_int
      connected := H.connected
      euler := H.euler
      S_mem := fun _ => ⟨d, (H.uCurve_ne_S_iff d).2 H.c_d⟩ }
  side := H.side'
  isSide := H.isSide'
  infStart := Γ.infStart
  infLen := Γ.infLen
  infStart_isSome := Γ.infStart_isSome
  infLen_le := fun z hz => by
    have h := Γ.infLen_le z hz
    change Γ.infLen ≤ period H.st z
    rw [H.period_S (H.start_S hz)]; exact h
  infArc_sweep := fun z hz => by
    change z ∈ arcOf Γ.σ H.α' Γ.infStart Γ.infLen at hz
    rw [H.arcOf_eq] at hz
    obtain ⟨h1, h2⟩ := Γ.infArc_sweep z hz
    refine ⟨(H.uCurve_ne_S_iff z).2 h1, ?_⟩
    change Γ.uSideD a (H.α' z) = 1
    rw [H.α'_S h1]
    unfold uSideD
    rw [if_neg (H.notv_S (by rw [j_curve_α]; exact h1))]
    exact h2

/-! ### The upper side of the untangled configuration -/

theorem UHyp.conf_curve_S (x : D) : H.conf.curve x = H.conf.S ↔ Γ.curve x = Γ.S :=
  H.uCurve_ne_S_iff x

theorem UHyp.conf_up (x : D) : H.conf.Up (H.conf.cellOf x) ↔ Γ.uSideD a x = 1 := Iff.rfl

theorem UHyp.uSideD_nv {x : D} (hv : Γ.crossingOf x ≠ Γ.crossingOf a) :
    Γ.uSideD a x = Γ.side (Γ.cellOf x) := by
  unfold uSideD; rw [if_neg hv]

theorem UHyp.uSideD_v {x : D} (hv : Γ.crossingOf x = Γ.crossingOf a) : Γ.uSideD a x = 0 := by
  unfold uSideD; rw [if_pos hv]

theorem UHyp.conf_sweep (e : D) : H.conf.IsSweepDart e ↔ Γ.IsSweepDart e := by
  unfold IsSweepDart
  rw [H.conf_curve_S]
  refine and_congr_right fun hS => ?_
  change Γ.uSideD a (H.α' e) = 1 ↔ _
  rw [H.α'_S hS, H.uSideD_nv (H.notv_S (by rw [j_curve_α]; exact hS))]
  rfl

theorem UHyp.conf_infArc : H.conf.infArc = Γ.infArc := H.arcOf_eq

theorem UHyp.conf_finSeg (e : D) : H.conf.IsFinSeg e ↔ Γ.IsFinSeg e := by
  unfold IsFinSeg; rw [H.conf_sweep, H.conf_infArc]

theorem UHyp.conf_onSweep (x : Γ.Crossing) : H.conf.OnSweep x ↔ Γ.OnSweep x := by
  unfold OnSweep curves crossingCurves
  change Γ.S ∈ x.darts.image (Γ.uCurve d k) ↔ Γ.S ∈ x.darts.image Γ.curve
  simp only [mem_image]
  exact exists_congr fun e => and_congr_right fun _ => H.uCurve_ne_S_iff e

theorem UHyp.conf_infVertex (x : Γ.Crossing) : H.conf.IsInfVertex x ↔ Γ.IsInfVertex x := by
  unfold IsInfVertex
  change (∃ z ∈ Γ.infStart, ∃ i < Γ.infLen, Γ.crossingOf (H.α' ((H.st ^ i) z)) = x) ↔ _
  refine exists_congr fun z => ?_
  constructor
  · rintro ⟨hz, i, hi, h⟩
    have hS := H.start_S hz
    rw [H.st_pow_S hS, H.α'_S (by rw [u_curve_pow]; exact hS)] at h
    exact ⟨hz, i, hi, h⟩
  · rintro ⟨hz, i, hi, h⟩
    have hS := H.start_S hz
    refine ⟨hz, i, hi, ?_⟩
    rw [H.st_pow_S hS, H.α'_S (by rw [u_curve_pow]; exact hS)]
    exact h

theorem UHyp.conf_finVertex (x : Γ.Crossing) : H.conf.IsFinVertex x ↔ Γ.IsFinVertex x := by
  unfold IsFinVertex; rw [H.conf_onSweep, H.conf_infVertex]

theorem UHyp.conf_above (e : D) :
    H.conf.Above e ↔ Γ.Above e ∧ Γ.crossingOf e ≠ Γ.crossingOf a := by
  unfold Above
  rw [show (H.conf.curve e ≠ H.conf.S ↔ Γ.curve e ≠ Γ.S) from not_congr (H.conf_curve_S e),
    H.conf_up]
  by_cases hv : Γ.crossingOf e = Γ.crossingOf a
  · rw [H.uSideD_v hv]; simp [hv]
  · rw [H.uSideD_nv hv]; simp only [hv, ne_eq, not_false_eq_true, and_true]; rfl

theorem UHyp.v_onSweep : ¬ Γ.OnSweep (Γ.crossingOf a) := by
  unfold OnSweep; rw [H.curves_v, mem_insert, mem_singleton]
  rintro (h | h)
  · exact H.c2S h.symm
  · exact H.c1S h.symm

theorem UHyp.v_above : Γ.IsAboveVertex (Γ.crossingOf a) :=
  ⟨H.v_onSweep, a, by rw [crossingOf, Orbit.darts_mk]; exact mem_orbitFinset.2 (.refl _ _),
    by rw [H.c_a]; exact H.c2S, H.s_a⟩

theorem UHyp.conf_aboveVertex (x : Γ.Crossing) :
    H.conf.IsAboveVertex x ↔ Γ.IsAboveVertex x ∧ x ≠ Γ.crossingOf a := by
  unfold IsAboveVertex
  rw [H.conf_onSweep]
  constructor
  · rintro ⟨h1, e, he, hA⟩
    rw [H.conf_above] at hA
    have hx : Γ.crossingOf e = x := Orbit.mem_darts.1 he
    exact ⟨⟨h1, e, he, hA.1⟩, hx ▸ hA.2⟩
  · rintro ⟨⟨h1, e, he, hA⟩, hne⟩
    have hx : Γ.crossingOf e = x := Orbit.mem_darts.1 he
    exact ⟨h1, e, he, (H.conf_above e).2 ⟨hA, hx ▸ hne⟩⟩

open Classical in
theorem UHyp.conf_numVertices : H.conf.numVertices + 1 = Γ.numVertices := by
  unfold numVertices
  have hmem : Γ.crossingOf a ∈ univ.filter (fun x : Γ.Crossing =>
      Γ.IsFinVertex x ∨ Γ.IsAboveVertex x) := by
    simp only [mem_filter, mem_univ, true_and]; exact Or.inr H.v_above
  rw [← card_erase_add_one hmem]
  congr 1
  refine card_bij (fun x _ => x) ?_ (fun _ _ _ _ h => h) ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rcases hx with h | h
    · have h := (H.conf_finVertex x).1 h
      exact mem_erase.2 ⟨fun he => H.v_onSweep (he ▸ h.1), mem_filter.2 ⟨mem_univ _, Or.inl h⟩⟩
    · obtain ⟨h, hne⟩ := (H.conf_aboveVertex x).1 h
      exact mem_erase.2 ⟨hne, mem_filter.2 ⟨mem_univ _, Or.inr h⟩⟩
  · intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_erase] at hx
    refine ⟨x, ?_, rfl⟩
    rcases hx with ⟨hne, h | h⟩
    · exact mem_filter.2 ⟨mem_univ _, Or.inl ((H.conf_finVertex x).2 h)⟩
    · exact mem_filter.2 ⟨mem_univ _, Or.inr ((H.conf_aboveVertex x).2 ⟨h, hne⟩)⟩

theorem UHyp.uCurve_other {e : D} {c : Fin n} (h1 : c ≠ Γ.curve (Γ.ub1 d))
    (h2 : c ≠ Γ.curve (Γ.ub2 d)) : Γ.uCurve d k e = c ↔ Γ.curve e = c := by
  unfold uCurve
  split_ifs with r1 r2
  · exact ⟨fun h => absurd h.symm h2, fun h => absurd (r1.2.symm.trans h).symm h1⟩
  · exact ⟨fun h => absurd h.symm h1, fun h => absurd (r2.2.symm.trans h).symm h2⟩
  · exact Iff.rfl

theorem UHyp.above_ub1 : Γ.Above (Γ.ub1 d) ∧ Γ.crossingOf (Γ.ub1 d) ≠ Γ.crossingOf a :=
  ⟨⟨H.c1S, H.s_σd⟩, by have := H.f1_ne_v H.k_pos; rwa [pow_zero] at this⟩

theorem UHyp.above_ub2 : Γ.Above (Γ.ub2 d) ∧ Γ.crossingOf (Γ.ub2 d) ≠ Γ.crossingOf a :=
  ⟨⟨H.c2S, H.s_ub2⟩, by have := H.f2_ne_v H.k_pos; rwa [pow_zero] at this⟩

theorem UHyp.uCurve_ub1 : Γ.uCurve d k (Γ.ub1 d) = Γ.curve (Γ.ub2 d) := by
  have h : Γ.uR1 d k (Γ.ub1 d) := H.uR1_iff.2 ⟨0, H.k_pos, Or.inl (by simp)⟩
  unfold uCurve; rw [if_pos h]

theorem UHyp.uCurve_ub2 : Γ.uCurve d k (Γ.ub2 d) = Γ.curve (Γ.ub1 d) := by
  have h : Γ.uR2 d k (Γ.ub2 d) := H.uR2_iff.2 ⟨0, H.k_pos, Or.inl (by simp)⟩
  unfold uCurve; rw [if_neg (fun h1 => H.not_R1_R2 h1 h), if_pos h]

theorem UHyp.curve_at_v {e : D} (hv : Γ.crossingOf e = Γ.crossingOf a) :
    Γ.curve e = Γ.curve (Γ.ub2 d) ∨ Γ.curve e = Γ.curve (Γ.ub1 d) := by
  have hm : Γ.curve e ∈ Γ.curves (Γ.crossingOf e) := by
    rw [j_curves_crossingOf]; exact mem_insert_self _ _
  rw [hv, H.curves_v, mem_insert, mem_singleton] at hm
  exact hm

theorem UHyp.conf_present (c : Fin n) : H.conf.Present c ↔ Γ.Present c := by
  unfold Present
  change (c ≠ Γ.S ∧ ∃ e, Γ.uCurve d k e = c ∧ H.conf.Above e) ↔ _
  refine and_congr_right fun hcS => ?_
  by_cases h1 : c = Γ.curve (Γ.ub1 d)
  · subst h1
    exact ⟨fun _ => ⟨_, rfl, H.above_ub1.1⟩,
      fun _ => ⟨_, H.uCurve_ub2, (H.conf_above _).2 H.above_ub2⟩⟩
  by_cases h2 : c = Γ.curve (Γ.ub2 d)
  · subst h2
    exact ⟨fun _ => ⟨_, rfl, H.above_ub2.1⟩,
      fun _ => ⟨_, H.uCurve_ub1, (H.conf_above _).2 H.above_ub1⟩⟩
  refine exists_congr fun e => ?_
  rw [H.uCurve_other h1 h2, H.conf_above]
  constructor
  · rintro ⟨h, hA, -⟩; exact ⟨h, hA⟩
  · rintro ⟨h, hA⟩
    refine ⟨h, hA, fun hv => ?_⟩
    rcases H.curve_at_v hv with h' | h'
    · exact h2 (h.symm.trans h')
    · exact h1 (h.symm.trans h')

open Classical in
theorem UHyp.conf_numCurves : H.conf.numCurves = Γ.numCurves := by
  unfold numCurves
  refine card_bij (fun c _ => c) ?_ (fun _ _ _ _ h => h) ?_
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    exact (H.conf_present c).1 hc
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    exact ⟨c, mem_filter.2 ⟨mem_univ _, (H.conf_present c).2 hc⟩, rfl⟩

theorem UHyp.fin_uπ (hf1 : Γ.IsFinVertex (Γ.crossingOf d))
    (hf2 : Γ.IsFinVertex (Γ.crossingOf (Γ.α d))) {x : Γ.Crossing} (hx : Γ.IsFinVertex x) :
    Γ.IsFinVertex (Γ.uπ d k x) := by
  have j0 : ∀ j, j < k → (if j = 0 then Γ.S else γ) = Γ.S → j = 0 := by
    intro j _ h
    by_contra hj; rw [if_neg hj] at h; exact H.γ_S h
  by_cases h1 : x ∈ Γ.uC1 d k
  · obtain ⟨j, hj, rfl⟩ := mem_image.1 h1
    rw [mem_range] at hj
    have hS := hx.1
    unfold OnSweep at hS
    rw [H.curves1 hj, mem_insert, mem_singleton] at hS
    rcases hS with hS | hS
    · exact absurd hS.symm H.c1S
    have := j0 j hj hS.symm
    subst this
    rw [show Γ.crossingOf ((Γ.straight ^ 0) (Γ.ub1 d)) = Γ.uF1 d 0 from rfl, H.uπ_f1 hj]
    show Γ.IsFinVertex (Γ.crossingOf ((Γ.straight ^ 0) (Γ.ub2 d)))
    rw [pow_zero, Perm.one_apply]
    unfold ub2
    rw [j_crossingOf_σ, j_crossingOf_σ, j_crossingOf_σ]; exact hf2
  by_cases h2 : x ∈ Γ.uC2 d k
  · obtain ⟨j, hj, rfl⟩ := mem_image.1 h2
    rw [mem_range] at hj
    have hS := hx.1
    unfold OnSweep at hS
    rw [H.curves2 hj, mem_insert, mem_singleton] at hS
    rcases hS with hS | hS
    · exact absurd hS.symm H.c2S
    have := j0 j hj hS.symm
    subst this
    rw [show Γ.crossingOf ((Γ.straight ^ 0) (Γ.ub2 d)) = Γ.uF2 d 0 from rfl, H.uπ_f2 hj]
    show Γ.IsFinVertex (Γ.crossingOf ((Γ.straight ^ 0) (Γ.ub1 d)))
    rw [pow_zero, Perm.one_apply]
    unfold ub1
    rw [j_crossingOf_σ]; exact hf1
  rw [H.uπ_other h1 h2]; exact hx

theorem UHyp.conf_meets (hf1 : Γ.IsFinVertex (Γ.crossingOf d))
    (hf2 : Γ.IsFinVertex (Γ.crossingOf (Γ.α d))) (c : Fin n) :
    H.conf.MeetsSweep c ↔ Γ.MeetsSweep c := by
  unfold MeetsSweep OnCurve
  change (∃ x : Γ.Crossing, H.conf.IsFinVertex x ∧ c ∈ crossingCurves Γ.σ (Γ.uCurve d k) x) ↔ _
  constructor
  · rintro ⟨x, hx, hc⟩
    rw [H.uCurves_π] at hc
    exact ⟨_, H.fin_uπ hf1 hf2 ((H.conf_finVertex x).1 hx), hc⟩
  · rintro ⟨y, hy, hc⟩
    refine ⟨Γ.uπ d k y, (H.conf_finVertex _).2 (H.fin_uπ hf1 hf2 hy), ?_⟩
    rw [H.uCurves_π, H.uπ_invol]; exact hc

/-- SH: "`Γ'` is not finished": a crossing on the leg from `i` stays above the sweep. -/
theorem UHyp.conf_not_terminal (hk : 1 < k) : ¬ H.conf.Terminal := by
  intro hT
  have hne := H.f1_ne_v hk
  apply hT.1 (Γ.crossingOf ((Γ.straight ^ 1) (Γ.ub1 d)))
  refine (H.conf_aboveVertex _).2 ⟨⟨?_, (Γ.straight ^ 1) (Γ.ub1 d), ?_, ?_⟩, hne⟩
  · unfold OnSweep
    rw [H.curves1 hk, if_neg (by omega), mem_insert, mem_singleton]
    rintro (h | h)
    · exact H.c1S h.symm
    · exact H.γ_S h.symm
  · rw [crossingOf, Orbit.darts_mk]; exact mem_orbitFinset.2 (.refl _ _)
  · exact ⟨by rw [u_curve_pow]; exact H.c1S, H.s_leg1 hk.le⟩

/-- SH: no loop can be taken in `Γ'` (every present curve of `Γ` meets the sweep). -/
theorem UHyp.conf_not_loop (hf1 : Γ.IsFinVertex (Γ.crossingOf d))
    (hf2 : Γ.IsFinVertex (Γ.crossingOf (Γ.α d))) (hm : ∀ c, Γ.Present c → Γ.MeetsSweep c) :
    ¬ H.conf.CanTakeLoop := by
  rintro ⟨e, f, he, hf, hcS, hms⟩
  have hc : H.conf.cellOf f = H.conf.cellOf (H.conf.α e) := Orbit.mem_darts.1 hf
  have hA : H.conf.Above f := ⟨hcS, by unfold Up; rw [hc]; exact he.2⟩
  have hP : H.conf.Present (H.conf.curve f) := ⟨hcS, f, rfl, hA⟩
  exact hms ((H.conf_meets hf1 hf2 _).2 (hm _ ((H.conf_present _).1 hP)))

/-! ### The correspondence of the cells above the sweep -/

omit H in
/-- A dart of a cell. -/
noncomputable def UHyp.rep (_H : Γ.UHyp d a k γ) (f : Γ.Cell) : D :=
  Quotient.out (s := Perm.SameCycle.setoid Γ.φ) f

omit H in
theorem UHyp.rep_spec (H : Γ.UHyp d a k γ) (f : Γ.Cell) : Γ.cellOf (H.rep f) = f :=
  Quotient.out_eq (s := Perm.SameCycle.setoid Γ.φ) f

/-- Old cell ↦ new cell (`B` and `T` ↦ the merged cell). -/
noncomputable def UHyp.ψ (f : Γ.Cell) : Orbit H.ph :=
  if f = Γ.uCell d a 0 ∨ f = Γ.uCell d a 2 then Orbit.mk H.ph (Γ.uM d a 7)
  else if f = Γ.uCell d a 1 then Orbit.mk H.ph (Γ.uM d a 4)
  else if f = Γ.uCell d a 3 then Orbit.mk H.ph (Γ.uM d a 6)
  else Orbit.mk H.ph (H.rep f)

theorem UHyp.ψ_spec {x : D} (hu : Γ.side (Γ.cellOf x) = 1)
    (hv : Γ.crossingOf x ≠ Γ.crossingOf a) : H.ψ (Γ.cellOf x) = Orbit.mk H.ph x := by
  have hn : ∀ i : Fin 12, i.val < 4 → x ≠ Γ.uM d a i := fun i hi h =>
    hv (H.v_iff.2 (by subst h; fin_cases i <;> simp at hi ⊢))
  unfold UHyp.ψ
  by_cases h0 : Γ.cellOf x = Γ.uCell d a 0
  · rw [if_pos (Or.inl h0)]; exact Orbit.mk_eq_mk.2 (H.sc_B h0 (hn 0 (by decide)))
  by_cases h2 : Γ.cellOf x = Γ.uCell d a 2
  · rw [if_pos (Or.inr h2)]; exact Orbit.mk_eq_mk.2 (H.sc_T h2 (hn 2 (by decide)))
  rw [if_neg (by tauto)]
  by_cases h1 : Γ.cellOf x = Γ.uCell d a 1
  · rw [if_pos h1]; exact Orbit.mk_eq_mk.2 (H.sc_L h1 (hn 1 (by decide)))
  rw [if_neg h1]
  by_cases h3 : Γ.cellOf x = Γ.uCell d a 3
  · rw [if_pos h3]; exact Orbit.mk_eq_mk.2 (H.sc_R h3 (hn 3 (by decide)))
  rw [if_neg h3]
  have hout : Γ.φ.SameCycle x (H.rep (Γ.cellOf x)) := by
    rw [← Orbit.mk_eq_mk]; exact (H.rep_spec (Γ.cellOf x)).symm
  have ho := H.orbit_other hu (fun c hc => by
    fin_cases c <;> simp at hc <;> assumption)
  have : H.rep (Γ.cellOf x) ∈ orbitFinset H.ph x := by
    rw [ho]; exact mem_orbitFinset.2 hout
  exact (Orbit.mk_eq_mk.2 (mem_orbitFinset.1 this)).symm

theorem UHyp.exists_rep (f : Γ.Cell) : ∃ x, Γ.cellOf x = f ∧ Γ.crossingOf x ≠ Γ.crossingOf a := by
  have viaM : ∀ i : Fin 12, 4 ≤ i.val → Γ.cellOf (Γ.uM d a i) = f →
      ∃ x, Γ.cellOf x = f ∧ Γ.crossingOf x ≠ Γ.crossingOf a :=
    fun i hi h => ⟨_, h, H.notv_uM hi⟩
  by_cases h0 : f = Γ.uCell d a 0
  · exact viaM 7 (by decide) (by rw [h0, H.cell_uM]; rfl)
  by_cases h1 : f = Γ.uCell d a 1
  · exact viaM 4 (by decide) (by rw [h1, H.cell_uM]; rfl)
  by_cases h2 : f = Γ.uCell d a 2
  · exact viaM 5 (by decide) (by rw [h2, H.cell_uM]; rfl)
  by_cases h3 : f = Γ.uCell d a 3
  · exact viaM 6 (by decide) (by rw [h3, H.cell_uM]; rfl)
  obtain ⟨x, rfl⟩ := f.exists_mk
  refine ⟨x, rfl, fun hv => ?_⟩
  rcases H.v_iff.1 hv with h | h | h | h <;> rw [h] at h0 h1 h2 h3
  · exact h0 (H.cell_uM 0)
  · exact h1 (H.cell_uM 1)
  · exact h2 (H.cell_uM 2)
  · exact h3 (H.cell_uM 3)

theorem UHyp.size_merge : (H.ψ (Γ.cellOf a)).size + 2 =
    (Γ.cellOf a).size + (Γ.cellOf (Γ.σ (Γ.σ a))).size := by
  have hψ : H.ψ (Γ.cellOf a) = Orbit.mk H.ph (Γ.uM d a 7) := by
    unfold UHyp.ψ; exact if_pos (Or.inl rfl)
  rw [hψ]
  change (orbitFinset H.ph _).card + 2 = (orbitFinset Γ.φ a).card +
    (orbitFinset Γ.φ (Γ.σ (Γ.σ a))).card
  rw [H.orbit_merge, card_union_of_disjoint, card_erase_of_mem (mem_orbitFinset.2 (.refl _ _)),
    card_erase_of_mem (mem_orbitFinset.2 (.refl _ _))]
  · have p1 := card_pos.2 ⟨a, mem_orbitFinset.2 (Perm.SameCycle.refl Γ.φ a)⟩
    have p2 := card_pos.2 ⟨Γ.σ (Γ.σ a), mem_orbitFinset.2 (Perm.SameCycle.refl Γ.φ (Γ.σ (Γ.σ a)))⟩
    omega
  · rw [disjoint_left]
    intro y h1 h2
    have e1 := mem_orbitFinset.1 (mem_of_mem_erase h1)
    have e2 := mem_orbitFinset.1 (mem_of_mem_erase h2)
    exact H.uCell_ne (c := 0) (c' := 2) (by decide) (Orbit.mk_eq_mk.2 (e1.trans e2.symm))

theorem UHyp.size_L : (H.ψ (Γ.cellOf (Γ.σ a))).size + 1 = (Γ.cellOf (Γ.σ a)).size := by
  have hψ : H.ψ (Γ.cellOf (Γ.σ a)) = Orbit.mk H.ph (Γ.uM d a 4) := by
    have n0 : Γ.uCell d a 1 ≠ Γ.uCell d a 0 := H.uCell_ne (by decide)
    have n2 : Γ.uCell d a 1 ≠ Γ.uCell d a 2 := H.uCell_ne (by decide)
    unfold UHyp.ψ
    rw [if_neg (show ¬ (Γ.cellOf (Γ.σ a) = Γ.uCell d a 0 ∨ Γ.cellOf (Γ.σ a) = Γ.uCell d a 2)
      from not_or.2 ⟨n0, n2⟩)]
    exact if_pos rfl
  rw [hψ]
  change (orbitFinset H.ph _).card + 1 = (orbitFinset Γ.φ (Γ.σ a)).card
  rw [H.orbit_L, card_erase_of_mem (mem_orbitFinset.2 (.refl _ _))]
  have := card_pos.2 ⟨Γ.σ a, mem_orbitFinset.2 (Perm.SameCycle.refl Γ.φ (Γ.σ a))⟩
  omega

theorem UHyp.size_R : (H.ψ (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ a))))).size + 1 =
    (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ a)))).size := by
  have hψ : H.ψ (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ a)))) = Orbit.mk H.ph (Γ.uM d a 6) := by
    have n0 : Γ.uCell d a 3 ≠ Γ.uCell d a 0 := H.uCell_ne (by decide)
    have n2 : Γ.uCell d a 3 ≠ Γ.uCell d a 2 := H.uCell_ne (by decide)
    have n1 : Γ.uCell d a 3 ≠ Γ.uCell d a 1 := H.uCell_ne (by decide)
    unfold UHyp.ψ
    rw [if_neg (show ¬ (Γ.cellOf (Γ.σ (Γ.σ (Γ.σ a))) = Γ.uCell d a 0 ∨
      Γ.cellOf (Γ.σ (Γ.σ (Γ.σ a))) = Γ.uCell d a 2) from not_or.2 ⟨n0, n2⟩),
      if_neg (show Γ.cellOf (Γ.σ (Γ.σ (Γ.σ a))) ≠ Γ.uCell d a 1 from n1)]
    exact if_pos rfl
  rw [hψ]
  change (orbitFinset H.ph _).card + 1 = (orbitFinset Γ.φ (Γ.σ (Γ.σ (Γ.σ a)))).card
  rw [H.orbit_R, card_erase_of_mem (mem_orbitFinset.2 (.refl _ _))]
  have := card_pos.2 ⟨Γ.σ (Γ.σ (Γ.σ a)),
    mem_orbitFinset.2 (Perm.SameCycle.refl Γ.φ (Γ.σ (Γ.σ (Γ.σ a))))⟩
  omega

end Hyp

end SConf

end Pca.Sweep
