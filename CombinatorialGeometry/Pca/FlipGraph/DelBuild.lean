/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): the construction of the deletion `A − C'`

Helper file for `Delete.lean`.

* `Arrangement.transport`: an arrangement carried along a bijection of the dart types.
* `delKeep_iff`: in an arrangement (all curves pairwise intersecting) the darts that survive the
  removal of `C'` in the sense of the SH sweep (`Sweep.SConf.Keep`: kept crossing and connected to
  the sweep curve) are exactly the darts at crossings without `C'` (`FlipGraph.Keep`).
* `delArr`: the removal `Sweep.SConf.rConf` of `{C'}` from `sconfOf A S …` (any sweep curve
  `S ≠ C'`) as an arrangement of `m` curves, labels renumbered by `C'.succAbove`.
-/
import Pca.FlipGraph.Lemmas
import Pca.FlipGraph.SConfOf
import Pca.Sweep.R_Make

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.FlipGraph

universe u v

variable {n m : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-! ## Transport along a bijection of the darts -/

section Transport

variable {D' : Type v} [Fintype D'] [DecidableEq D'] (e : D' ≃ D)

theorem conj_apply (f : Perm D) (x : D') : e ((e.symm.permCongr f) x) = f (e x) := by
  simp [Equiv.permCongr_apply]

/-- Orbits of conjugate permutations. -/
def orbitCongr {f' : Perm D'} {f : Perm D} (h : ∀ x, e (f' x) = f (e x)) : Orbit f' ≃ Orbit f :=
  Quotient.congr e fun a b => (sameCycle_map_iff e h).symm

theorem orbitCongr_mk {f' : Perm D'} {f : Perm D} (h : ∀ x, e (f' x) = f (e x)) (x : D') :
    orbitCongr e h (Orbit.mk f' x) = Orbit.mk f (e x) := rfl

theorem orbitFinset_congr {f' : Perm D'} {f : Perm D} (h : ∀ x, e (f' x) = f (e x)) (x : D') :
    orbitFinset f (e x) = (orbitFinset f' x).map e.toEmbedding := by
  ext y
  obtain ⟨y, rfl⟩ := e.surjective y
  rw [mem_map_equiv, mem_orbitFinset, mem_orbitFinset, Equiv.symm_apply_apply,
    sameCycle_map_iff e h]

variable (A : Arrangement n D)

theorem transport_isArrangement :
    IsArrangement n (e.symm.permCongr A.σ) (e.symm.permCongr A.α) (fun x => A.curve (e x)) := by
  have hσ := conj_apply e A.σ
  have hα := conj_apply e A.α
  have hst : ∀ x, e (straightPerm (e.symm.permCongr A.σ) (e.symm.permCongr A.α) x) =
      straightPerm A.σ A.α (e x) := by
    intro x; simp only [straightPerm, Perm.mul_apply, hσ, hα]
  have hφ : ∀ x, e ((e.symm.permCongr A.σ * e.symm.permCongr A.α) x) = (A.σ * A.α) (e x) := by
    intro x; simp only [Perm.mul_apply, hσ, hα]
  have hcc : ∀ o : Orbit (e.symm.permCongr A.σ),
      crossingCurves (e.symm.permCongr A.σ) (fun x => A.curve (e x)) o =
        crossingCurves A.σ A.curve (orbitCongr e hσ o) := by
    intro o
    obtain ⟨x, rfl⟩ := Quotient.exists_rep o
    show (orbitFinset _ x).image _ = (orbitFinset A.σ (e x)).image A.curve
    rw [orbitFinset_congr e hσ, map_eq_image, image_image]
    rfl
  have H := A.isArrangement
  refine
    { card_crossing := fun x => ?_
      α_ne := fun x h => H.α_ne (e x) ?_
      α_α := fun x => by simp [Equiv.permCongr_apply, H.α_α]
      curve_α := fun x => by rw [hα]; exact H.curve_α _
      curve_σ := fun x => by rw [hσ]; exact H.curve_σ _
      curve_σσ := fun x => by rw [hσ, hσ]; exact H.curve_σσ _
      straight := fun x y hxy => ?_
      intersecting := fun c c' hcc' => ?_
      euler := ?_ }
  · rw [← H.card_crossing (e x), orbitFinset_congr e hσ, card_map]
  · rw [← hα, h]
  · rcases H.straight (e x) (e y) hxy with h1 | h1
    · exact Or.inl ((sameCycle_map_iff e hst).1 h1)
    · right
      rw [← hσ, ← hσ] at h1
      exact (sameCycle_map_iff e hst).1 h1
  · rw [← H.intersecting c c' hcc']
    refine card_equiv (orbitCongr e hσ) fun o => ?_
    simp only [mem_filter, mem_univ, true_and, hcc]
  · rw [← H.euler, Fintype.card_congr (orbitCongr e hσ), Fintype.card_congr (orbitCongr e hα),
      Fintype.card_congr (orbitCongr e hφ)]

/-- `A` carried along the dart bijection `e`. -/
def _root_.Pca.Arrangement.transport : Arrangement n D' where
  σ := e.symm.permCongr A.σ
  α := e.symm.permCongr A.α
  curve := fun x => A.curve (e x)
  isArrangement := transport_isArrangement e A

theorem transport_straight (x : D') :
    e ((A.transport e).straight x) = A.straight (e x) := by
  show e (straightPerm (e.symm.permCongr A.σ) (e.symm.permCongr A.α) x) = _
  simp only [straightPerm, Perm.mul_apply, conj_apply]
  rfl

end Transport

theorem _root_.Pca.Arrangement.α_eq_σσ_straight (A : Arrangement n D) (x : D) :
    A.α x = A.σ (A.σ (A.straight x)) := by
  rw [A.straight_apply, A.σ_σ_σ_σ]

/-- Arrangements with the same `σ`, `straight` and labels are equal (`α = σ² ∘ straight`). -/
theorem _root_.Pca.Arrangement.ext_straight {A B : Arrangement n D} (hσ : A.σ = B.σ)
    (hc : A.curve = B.curve) (hs : ∀ x, A.straight x = B.straight x) : A = B := by
  have hα : A.α = B.α := by
    ext x
    have h1 : A.σ (A.σ (A.straight x)) = A.α x := by
      rw [A.straight_apply, A.σ_σ_σ_σ]
    have h2 : B.σ (B.σ (B.straight x)) = B.α x := by
      rw [B.straight_apply, B.σ_σ_σ_σ]
    rw [← h1, ← h2, hs, hσ]
  cases A; cases B
  simp only at hσ hc hα
  subst hσ hc hα
  rfl

/-! ## Renumbering the curves -/

/-- The label of `c ≠ C'` after deleting `C'` (inverse of `C'.succAbove`). -/
noncomputable def predLabel (C' : Fin (m + 1)) (hm : 2 ≤ m) (c : Fin (m + 1)) : Fin m :=
  if h : c ≠ C' then (Fin.exists_succAbove_eq h).choose else ⟨0, by omega⟩

theorem succAbove_predLabel {C' : Fin (m + 1)} {hm : 2 ≤ m} {c : Fin (m + 1)} (h : c ≠ C') :
    C'.succAbove (predLabel C' hm c) = c := by
  rw [predLabel, dif_pos h]
  exact (Fin.exists_succAbove_eq h).choose_spec

theorem predLabel_succAbove {C' : Fin (m + 1)} {hm : 2 ≤ m} (c : Fin m) :
    predLabel C' hm (C'.succAbove c) = c :=
  Fin.succAbove_right_injective (succAbove_predLabel (Fin.succAbove_ne C' c))

theorem predLabel_inj {C' : Fin (m + 1)} {hm : 2 ≤ m} {a b : Fin (m + 1)} (ha : a ≠ C')
    (hb : b ≠ C') (h : predLabel C' hm a = predLabel C' hm b) : a = b := by
  rw [← succAbove_predLabel (hm := hm) ha, ← succAbove_predLabel (hm := hm) hb, h]

/-! ## The surviving darts -/

section Keep

/-- The darts kept when deleting the curve `C'`: not on `C'` and not at a crossing with `C'`. -/
def Keep (A : Arrangement n D) (C' : Fin n) (d : D) : Prop :=
  A.curve d ≠ C' ∧ C' ∉ Arrangement.Crossing.curves A (A.crossingOf d)

instance (A : Arrangement n D) (C' : Fin n) : DecidablePred (Keep A C') :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

variable (A : Arrangement n D)

theorem exists_dart_of_ne {c c' : Fin n} (h : c ≠ c') :
    ∃ d, A.curve d = c ∧ A.curve (A.σ d) = c' := by
  have h2 := A.isArrangement.intersecting c c' h
  obtain ⟨x, hx⟩ : (univ.filter (fun x : A.Crossing =>
      crossingCurves A.σ A.curve x = {c, c'})).Nonempty := card_pos.1 (by rw [h2]; omega)
  rw [mem_filter] at hx
  obtain ⟨d0, rfl⟩ := x.exists_mk
  have hmem : c ∈ crossingCurves A.σ A.curve (Orbit.mk A.σ d0) := by
    rw [hx.2]; exact mem_insert_self _ _
  obtain ⟨d, hd, hdc⟩ := mem_image.1 hmem
  refine ⟨d, hdc, ?_⟩
  have hσ : A.curve (A.σ d) ∈ crossingCurves A.σ A.curve (Orbit.mk A.σ d0) := by
    refine mem_image.2 ⟨A.σ d, ?_, rfl⟩
    exact mem_orbitFinset.2 ((mem_orbitFinset.1 hd).trans (Perm.SameCycle.refl _ _ |>.trans
      ⟨1, by simp⟩))
  rw [hx.2, mem_insert, mem_singleton] at hσ
  rcases hσ with h1 | h1
  · exact absurd (h1.trans hdc.symm) (A.isArrangement.curve_σ d)
  · exact h1

variable {A} {C' S : Fin n} {s : A.Cell → ZMod 2} {hs : A.IsSide S s} {b : ZMod 2} {y : D}
  {hy : A.curve y = S} {hyb : s (A.cellOf y) = b}

theorem del_rK_iff (d : D) : (sconfOf A S s hs b y hy hyb).rK {C'} d ↔
    C' ∉ Arrangement.Crossing.curves A (A.crossingOf d) := by
  unfold Sweep.SConf.rK Sweep.SConf.Deleted Sweep.SConf.OnCurve
  simp only [mem_singleton, exists_eq_left]
  rfl

theorem keep_iff_not_mem (d : D) :
    Keep A C' d ↔ C' ∉ Arrangement.Crossing.curves A (A.crossingOf d) := by
  refine ⟨And.right, fun h => ⟨fun hc => h ?_, h⟩⟩
  rw [A.curves_crossingOf, hc]
  exact mem_insert_self _ _

/-- In an arrangement the darts surviving the removal of `C'` (SH sense) are the kept darts. -/
theorem delKeep_iff (hS : S ≠ C') (d : D) :
    (sconfOf A S s hs b y hy hyb).Keep {C'} d ↔ Keep A C' d := by
  set Γ := sconfOf A S s hs b y hy hyb
  rw [keep_iff_not_mem]
  refine ⟨fun h => (del_rK_iff d).1 h.1, fun h => ?_⟩
  have hrK : Γ.rK {C'} d := (del_rK_iff d).2 h
  by_cases ha : A.curve d = S
  · exact Sweep.SConf.r_keep_S ha hrK
  obtain ⟨w, hw1, hw2⟩ := exists_dart_of_ne A ha
  have hcd : A.curve d ≠ C' := fun hc => h (by
    rw [A.curves_crossingOf, hc]
    exact mem_insert_self _ _)
  have hwK : Γ.rK {C'} w := by
    rw [del_rK_iff, A.curves_crossingOf, hw1,
      hw2, mem_insert, mem_singleton, not_or]
    exact ⟨Ne.symm hcd, Ne.symm hS⟩
  have hσw : Γ.Keep {C'} (A.σ w) :=
    Sweep.SConf.r_keep_S hw2 ((Sweep.SConf.r_rK_σ Γ {C'} w).2 hwK)
  have hw : Γ.Keep {C'} w := (Sweep.SConf.r_keep_σ_iff w).1 hσw
  rcases A.isArrangement.straight w d hw1 with h1 | h1
  · obtain ⟨t, ht⟩ := h1.exists_nat_pow_eq
    have := Sweep.SConf.r_keep_pow (t := t) hw (by
      show Γ.rK {C'} ((straightPerm A.σ A.α ^ t) w); rw [ht]; exact hrK)
    show Γ.Keep {C'} d
    rw [← ht]; exact this
  · obtain ⟨t, ht⟩ := h1.exists_nat_pow_eq
    have := Sweep.SConf.r_keep_pow (t := t) hw (by
      show Γ.rK {C'} ((straightPerm A.σ A.α ^ t) w)
      rw [ht]; exact (Sweep.SConf.r_rK_σσ Γ {C'} d).2 hrK)
    have h2 : Γ.Keep {C'} (A.σ (A.σ d)) := by
      show Γ.Keep {C'} (A.σ (A.σ d)); rw [← ht]; exact this
    exact (Sweep.SConf.r_keep_σ_iff d).1 ((Sweep.SConf.r_keep_σ_iff (A.σ d)).1 h2)

end Keep

/-! ## The removal as an arrangement of `m` curves -/

section DelArr

variable {A : Arrangement (m + 1) D} {C' S : Fin (m + 1)} {s : A.Cell → ZMod 2}
  {hs : A.IsSide S s} {b : ZMod 2} {y : D} {hy : A.curve y = S} {hyb : s (A.cellOf y) = b}

theorem image_predLabel_iff (hm : 2 ≤ m) {X : Finset (Fin (m + 1))} (hX : C' ∉ X) (c c' : Fin m) :
    X.image (predLabel C' hm) = {c, c'} ↔ X = {C'.succAbove c, C'.succAbove c'} := by
  constructor
  · intro h
    have : X = (X.image (predLabel C' hm)).image C'.succAbove := by
      rw [image_image]
      ext x
      constructor
      · intro hx
        exact mem_image.2 ⟨x, hx, succAbove_predLabel (fun h => hX (by rw [← h]; exact hx))⟩
      · intro hx
        obtain ⟨x', hx', rfl⟩ := mem_image.1 hx
        rw [Function.comp_apply, succAbove_predLabel (fun h => hX (by rw [← h]; exact hx'))]
        exact hx'
    rw [this, h, image_insert, image_singleton]
  · rintro rfl
    rw [image_insert, image_singleton, predLabel_succAbove, predLabel_succAbove]

theorem exists_third (hm : 2 ≤ m) (C' S : Fin (m + 1)) : ∃ c : Fin (m + 1), c ≠ S ∧ c ≠ C' := by
  have h01 : C'.succAbove ⟨0, by omega⟩ ≠ C'.succAbove ⟨1, by omega⟩ :=
    fun h => absurd (Fin.succAbove_right_injective h) (by simp [Fin.ext_iff])
  by_cases h0 : C'.succAbove ⟨0, by omega⟩ = S
  · exact ⟨_, fun h => h01 (h0.trans h.symm), Fin.succAbove_ne _ _⟩
  · exact ⟨_, h0, Fin.succAbove_ne _ _⟩

theorem delArr_isArrangement (hm : 2 ≤ m) (hS : S ≠ C') :
    IsArrangement m ((sconfOf A S s hs b y hy hyb).rσ {C'}) ((sconfOf A S s hs b y hy hyb).rα {C'})
      (fun d => predLabel C' hm (A.curve d.1)) := by
  set Γ := sconfOf A S s hs b y hy hyb
  have hS' : Γ.S ∉ ({C'} : Finset (Fin (m + 1))) := fun h => hS (mem_singleton.1 h)
  have H : Sweep.IsSConf (m + 1) (Γ.rσ {C'}) (Γ.rα {C'}) (fun d => Γ.curve d.1) Γ.S :=
    Sweep.SConf.r_isSConf
  have hc : ∀ d : Γ.RD {C'}, A.curve d.1 ≠ C' := fun d h =>
    Sweep.SConf.r_curve_not_mem Γ {C'} d.2.1 (mem_singleton.2 h)
  have hcK : ∀ d : Γ.RD {C'}, C' ∉ Arrangement.Crossing.curves A (A.crossingOf d.1) :=
    fun d => (del_rK_iff d.1).1 d.2.1
  obtain ⟨c3, hc3S, hc3C⟩ := exists_third hm C' S
  obtain ⟨w, hw1, hw2⟩ := exists_dart_of_ne A (Ne.symm hc3S)
  have hwK : Γ.Keep {C'} w := by
    rw [delKeep_iff hS, keep_iff_not_mem,
      A.curves_crossingOf, hw1, hw2,
      mem_insert, mem_singleton, not_or]
    exact ⟨Ne.symm hS, Ne.symm hc3C⟩
  refine
    { card_crossing := H.card_crossing
      α_ne := H.α_ne
      α_α := H.α_α
      curve_α := fun d => congrArg (predLabel C' hm) (H.curve_α d)
      curve_σ := fun d h => H.curve_σ d (predLabel_inj (hc _) (hc _) h)
      curve_σσ := fun d => congrArg (predLabel C' hm) (H.curve_σσ d)
      straight := fun d e h => H.straight d e (predLabel_inj (hc d) (hc e) h)
      intersecting := fun c c' hne => ?_
      euler := H.euler ⟨⟨w, hwK⟩⟩ }
  have hne' : C'.succAbove c ≠ C'.succAbove c' := fun h => hne (Fin.succAbove_right_injective h)
  rw [← A.isArrangement.intersecting _ _ hne']
  have himg : ∀ d : Γ.RD {C'}, crossingCurves (Γ.rσ {C'}) (fun d => predLabel C' hm (A.curve d.1))
      (Orbit.mk _ d) = (Arrangement.Crossing.curves A (A.crossingOf d.1)).image (predLabel C' hm) := by
    intro d
    rw [show Arrangement.Crossing.curves A (A.crossingOf d.1) = Γ.curves (Γ.crossingOf d.1) from rfl,
      ← Sweep.SConf.r_crossingCurves d]
    show (orbitFinset _ d).image _ = ((orbitFinset _ d).image _).image _
    rw [image_image]
    rfl
  refine card_bij (fun o _ => Sweep.SConf.rCr o) ?_ (fun a _ b _ h => Sweep.SConf.r_rCr_inj h) ?_
  · intro o ho
    obtain ⟨d, rfl⟩ := o.exists_mk
    simp only [mem_filter, mem_univ, true_and] at ho
    rw [Sweep.SConf.r_rCr_mk]
    rw [himg] at ho
    exact mem_filter.2 ⟨mem_univ _, (image_predLabel_iff hm (hcK d) c c').1 ho⟩
  · intro x hx
    obtain ⟨d0, rfl⟩ := x.exists_mk
    simp only [mem_filter, mem_univ, true_and] at hx
    have hx2 : Arrangement.Crossing.curves A (A.crossingOf d0) = {C'.succAbove c, C'.succAbove c'} :=
      hx
    have hC : C' ∉ Arrangement.Crossing.curves A (A.crossingOf d0) := by
      rw [hx2, mem_insert, mem_singleton, not_or]
      exact ⟨(Fin.succAbove_ne _ _).symm, (Fin.succAbove_ne _ _).symm⟩
    have hk : Γ.Keep {C'} d0 := by
      rw [delKeep_iff hS, keep_iff_not_mem]
      exact hC
    refine ⟨Orbit.mk _ ⟨d0, hk⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [himg]
    exact (image_predLabel_iff hm hC c c').2 hx2

/-- The removal of `C'` as an arrangement of `m` curves on the surviving darts. -/
noncomputable def delArr (hm : 2 ≤ m) (hS : S ≠ C') : Arrangement m ((sconfOf A S s hs b y hy hyb).RD {C'}) where
  σ := (sconfOf A S s hs b y hy hyb).rσ {C'}
  α := (sconfOf A S s hs b y hy hyb).rα {C'}
  curve := fun d => predLabel C' hm (A.curve d.1)
  isArrangement := delArr_isArrangement hm hS

end DelArr

end Pca.FlipGraph
