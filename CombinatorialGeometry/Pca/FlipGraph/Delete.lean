/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): deleting a curve (FROS `𝒜 − {C'}`)

FROS (proof of Theorem 3): "we introduce the notation `𝒜 − {C_1, …, C_k}` to denote the arrangement
that is obtained from `𝒜` by removing the pseudocircles". Graph language: delete every dart on `C'`
and every dart at a crossing with `C'`; `σ` is inherited; `α` goes straight through the deleted
crossings until it reaches a kept crossing (the pieces of a segment are joined); the curve labels
`≠ C'` are renumbered by `Fin.succAbove C'`.

The deletion is defined on the subtype of a predicate `K` equivalent to `Keep A C'`: arrangements
with the same crossings and curves (for example `A` and every flip of `A`) then have their
deletions on the same dart type, and flips commute with the deletion literally:

* `deleteOn_flip_of_side` (P1): flipping a triangle with a side on `C'` (`C'` moves over a crossing)
  does not change `A − C'`.
* `deleteOn_flip_of_no_corner` (P2): flipping a triangle without a corner on `C'` commutes with the
  deletion.
-/
import Pca.FlipGraph.DelBuild
import Pca.FlipGraph.DelFlip

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n m : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-! ## The construction (via the SH removal, `DelBuild.lean`)

Sweep curve `delS = C'.succAbove 0`, a side function of it and a dart on it chosen once; the
result does not depend on these choices (`σ` restricted, `α` = end of the joined segment). -/

theorem delS_ne (C' : Fin (m + 1)) (hm : 2 ≤ m) : C'.succAbove ⟨0, by omega⟩ ≠ C' :=
  Fin.succAbove_ne _ _

/-- The sweep configuration used to build `A − C'`. -/
noncomputable def delΓ (A : Arrangement (m + 1) D) (C' : Fin (m + 1)) (hm : 2 ≤ m) :
    Sweep.SConf (m + 1) D :=
  sconfOf A (C'.succAbove ⟨0, by omega⟩) (A.exists_isSide _).choose
    (A.exists_isSide _).choose_spec _ (exists_dart_of_ne A (delS_ne C' hm)).choose
    (exists_dart_of_ne A (delS_ne C' hm)).choose_spec.1 rfl

theorem delΓ_keep_iff (A : Arrangement (m + 1) D) (C' : Fin (m + 1)) (hm : 2 ≤ m) (d : D) :
    (delΓ A C' hm).Keep {C'} d ↔ Keep A C' d :=
  delKeep_iff (delS_ne C' hm) d

theorem delΓ_rK_iff (A : Arrangement (m + 1) D) (C' : Fin (m + 1)) (hm : 2 ≤ m) (d : D) :
    (delΓ A C' hm).rK {C'} d ↔ C' ∉ Arrangement.Crossing.curves A (A.crossingOf d) :=
  del_rK_iff d

/-- **The deletion of the curve `C'`** (FROS `𝒜 − {C'}`), on the darts satisfying `K ↔ Keep A C'`.
Needs at least two remaining curves (`2 ≤ m`; one curve without crossings is not an arrangement in
the model). -/
noncomputable def _root_.Pca.Arrangement.deleteOn (A : Arrangement (m + 1) D) (C' : Fin (m + 1)) (hm : 2 ≤ m)
    (K : D → Prop) [DecidablePred K] (hK : ∀ d, K d ↔ Keep A C' d) :
    Arrangement m {d // K d} :=
  (delArr (A := A) (C' := C') hm (delS_ne C' hm) (hyb := rfl)).transport
    (Equiv.subtypeEquivRight fun d => (hK d).trans (delΓ_keep_iff A C' hm d).symm)

section Spec

variable (A : Arrangement (m + 1) D) (C' : Fin (m + 1)) (hm : 2 ≤ m) (K : D → Prop)
  [DecidablePred K] (hK : ∀ d, K d ↔ Keep A C' d)

theorem deleteOn_σ (d : {d // K d}) : ((A.deleteOn C' hm K hK).σ d).val = A.σ d.val := rfl

theorem deleteOn_curve (d : {d // K d}) :
    C'.succAbove ((A.deleteOn C' hm K hK).curve d) = A.curve d.val :=
  succAbove_predLabel (hm := hm) ((hK _).1 d.2).1

/-- `α` of the deletion: walk straight from `d` through the deleted crossings (`k` of them) to the
next kept crossing. -/
theorem deleteOn_α (d : {d // K d}) :
    ∃ k, (∀ i < k, C' ∈ Arrangement.Crossing.curves A (A.crossingOf (A.α ((A.straight ^ i) d.val)))) ∧
      C' ∉ Arrangement.Crossing.curves A (A.crossingOf (A.α ((A.straight ^ k) d.val))) ∧
      ((A.deleteOn C' hm K hK).α d).val = A.α ((A.straight ^ k) d.val) := by
  have hk : (delΓ A C' hm).rK {C'} d.val := (delΓ_rK_iff A C' hm _).2 ((hK _).1 d.2).2
  refine ⟨(delΓ A C' hm).rJ {C'} d.val, fun i hi => ?_, ?_, Sweep.SConf.r_hit_eq hk⟩
  · have := Sweep.SConf.r_notK_lt hk hi
    rw [delΓ_rK_iff, not_not] at this
    exact this
  · exact (delΓ_rK_iff A C' hm _).1 (Sweep.SConf.r_K_end hk)

/-- A side function of a curve `c ≠ C'` induces a side function of the deletion. -/
theorem deleteOn_isSide {c : Fin m} {s : A.Cell → ZMod 2} (hs : A.IsSide (C'.succAbove c) s) :
    ∃ s', (A.deleteOn C' hm K hK).IsSide c s' ∧
      ∀ d : {d // K d}, s' ((A.deleteOn C' hm K hK).cellOf d) = s (A.cellOf d.val) := by
  set Γ := delΓ A C' hm
  set e := Equiv.subtypeEquivRight fun d => (hK d).trans (delΓ_keep_iff A C' hm d).symm
  have key0 : ∀ u v : ZMod 2, u + v = 0 → v = u := by decide
  have hr : ∀ w, Γ.curve w ∈ ({C'} : Finset (Fin (m + 1))) →
      s (Γ.cellOf (Γ.α w)) = s (Γ.cellOf w) := by
    intro w hw
    have h1 := hs w
    rw [if_neg (by rw [show A.curve w = C' from mem_singleton.1 hw]; exact (Fin.succAbove_ne C' c).symm)] at h1
    exact key0 _ _ h1
  have hφ : ∀ x, e (((A.deleteOn C' hm K hK).σ * (A.deleteOn C' hm K hK).α) x) =
      (Γ.rσ {C'} * Γ.rα {C'}) (e x) := fun x => by
    simp only [Perm.mul_apply]
    exact (conj_apply e _ _).trans (congrArg _ (conj_apply e _ _))
  refine ⟨fun f => Sweep.SConf.rCellFun (Γ := Γ) (fun f => s f) hr (orbitCongr e hφ f), fun d => ?_, fun d => rfl⟩
  show Sweep.SConf.rCellFun (Γ := Γ) (fun f => s f) hr (Orbit.mk _ (e d)) +
    Sweep.SConf.rCellFun (Γ := Γ) (fun f => s f) hr (Orbit.mk _ (e ((A.deleteOn C' hm K hK).α d))) = _
  rw [show e ((A.deleteOn C' hm K hK).α d) = Γ.rα {C'} (e d) from conj_apply e _ _,
    Sweep.SConf.r_cellFun_add hr]
  have hc := Sweep.SConf.r_curve_pow (Γ := Γ) (e d).1 (Γ.rJ {C'} (e d).1)
  refine (hs _).trans ?_
  rw [show A.curve _ = A.curve d.val from hc]
  have hd : A.curve d.val ≠ C' := ((hK _).1 d.2).1
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · show predLabel C' hm (A.curve d.val) = c
    rw [show A.curve d.val = C'.succAbove c from h]; exact predLabel_succAbove c
  · show A.curve d.val = C'.succAbove c
    rw [← show predLabel C' hm (A.curve d.val) = c from h]; exact (succAbove_predLabel hd).symm

/-- `straight` of the deletion is the first return of `straight` to the kept darts. -/
theorem deleteOn_first (d : {d // K d}) :
    IsFirst A.straight K d.val ((A.deleteOn C' hm K hK).straight d).val := by
  set e := Equiv.subtypeEquivRight fun d => (hK d).trans (delΓ_keep_iff A C' hm d).symm
  obtain ⟨k, hk0, hk, hlt⟩ := Sweep.SConf.r_isFR_straight (Γ := delΓ A C' hm) (R := {C'}) (e d)
  have h1 : ((A.deleteOn C' hm K hK).straight d).val =
      (straightPerm ((delΓ A C' hm).rσ {C'}) ((delΓ A C' hm).rα {C'}) (e d)).val :=
    congrArg Subtype.val (transport_straight e
      (delArr (A := A) (C' := C') hm (delS_ne C' hm) (hyb := rfl)) d)
  refine ⟨k, hk0, by rw [h1, hk]; rfl, ((A.deleteOn C' hm K hK).straight d).2,
    fun j h0 hj hKj => hlt j h0 hj ?_⟩
  exact (delΓ_keep_iff A C' hm _).2 ((hK _).1 hKj)

end Spec

theorem deleteOn_ext {A B : Arrangement (m + 1) D} {C' : Fin (m + 1)} {hm : 2 ≤ m}
    {K : D → Prop} [DecidablePred K] (hA : ∀ d, K d ↔ Keep A C' d) (hB : ∀ d, K d ↔ Keep B C' d)
    (hσ : B.σ = A.σ) (hc : B.curve = A.curve)
    (hs : ∀ x, ((B.deleteOn C' hm K hB).straight x).val = ((A.deleteOn C' hm K hA).straight x).val) :
    B.deleteOn C' hm K hB = A.deleteOn C' hm K hA := by
  refine Arrangement.ext_straight ?_ ?_ fun x => Subtype.ext (hs x)
  · ext x
    rw [deleteOn_σ, deleteOn_σ, hσ]
  · funext x
    apply Fin.succAbove_right_injective (p := C')
    rw [deleteOn_curve, deleteOn_curve, hc]

/-- **P1**: flipping a triangle with a side on `C'` does not change the deletion of `C'`. -/
theorem deleteOn_flip_of_side (A : Arrangement (m + 1) D) (C' : Fin (m + 1)) (hm : 2 ≤ m)
    (K : D → Prop) [DecidablePred K] (hK : ∀ d, K d ↔ Keep A C' d) {d : D}
    (hT : A.IsTriangle (A.cellOf d)) (hside : ∃ y ∈ (A.cellOf d).darts, A.curve y = C')
    (hK' : ∀ e, K e ↔ Keep (A.flip d hT) C' e) :
    (A.flip d hT).deleteOn C' hm K hK' = A.deleteOn C' hm K hK := by
  refine deleteOn_ext hK hK' rfl rfl fun x => ?_
  refine IsFirst.unique (deleteOn_first _ C' hm K hK' x) ?_
  refine isFirst_swap (Arrangement.straight_not_mem_sideDarts hT) (straight_straight_not_mem_sideDarts hT)
    (fun y => Arrangement.flip_straightPerm hT y) (fun u hu h => ?_) x.2 (deleteOn_first A C' hm K hK x)
  rcases side_pair_meets hT hside hu with h1 | h1
  · exact ((hK _).1 h.1).2 h1
  · exact ((hK _).1 h.2).2 h1

/-! ## P2 support: a triangle without corner on `C'` -/

theorem orbitFinset_three {X : Type*} [Fintype X] [DecidableEq X] {f : Perm X} {x : X}
    (h : f (f (f x)) = x) : orbitFinset f x = {x, f x, f (f x)} := by
  ext y
  rw [mem_orbitFinset]
  constructor
  · intro hs
    obtain ⟨i, hi⟩ := hs.exists_nat_pow_eq
    have hp : Function.IsPeriodicPt f 3 x := h
    have h3 : (f ^ (i % 3)) x = y := by
      rw [← hi, Perm.coe_pow, Perm.coe_pow, hp.iterate_mod_apply]
    have : i % 3 < 3 := Nat.mod_lt _ (by omega)
    simp only [mem_insert, mem_singleton]
    interval_cases (i % 3)
    · left; rw [← h3]; rfl
    · right; left; rw [← h3]; rfl
    · right; right; rw [← h3]; rfl
  · simp only [mem_insert, mem_singleton]
    rintro (rfl | rfl | rfl)
    · exact Perm.SameCycle.refl _ _
    · exact ⟨1, by simp⟩
    · exact ⟨2, by rw [zpow_ofNat, pow_two, Perm.mul_apply]⟩

section P2

variable {A : Arrangement (m + 1) D} {C' : Fin (m + 1)} {hm : 2 ≤ m} {K : D → Prop}
  [DecidablePred K] {hK : ∀ d, K d ↔ Keep A C' d}

theorem deleteOn_straight_val {z : {d // K d}} (h : K (A.straight z.val)) :
    ((A.deleteOn C' hm K hK).straight z).val = A.straight z.val :=
  IsFirst.unique (deleteOn_first A C' hm K hK z) (isFirst_one h)

theorem keep_crossing (hK : ∀ d, K d ↔ Keep A C' d) {y z : D} (hyz : A.crossingOf y = A.crossingOf z) (hz : K z) : K y := by
  rw [hK, keep_iff_not_mem, hyz, ← keep_iff_not_mem, ← hK]
  exact hz

theorem deleteOn_α_val {z : {d // K d}} (h : K (A.α z.val)) :
    ((A.deleteOn C' hm K hK).α z).val = A.α z.val := by
  have hs : K (A.straight z.val) := keep_crossing hK (A.crossingOf_straight _) h
  rw [Arrangement.α_eq_σσ_straight, deleteOn_σ, deleteOn_σ, deleteOn_straight_val hs,
    ← Arrangement.α_eq_σσ_straight]

theorem deleteOn_φ_val {z : {d // K d}} (h : K (A.α z.val)) :
    ((A.deleteOn C' hm K hK).φ z).val = A.φ z.val := by
  show ((A.deleteOn C' hm K hK).σ ((A.deleteOn C' hm K hK).α z)).val = A.σ (A.α z.val)
  rw [deleteOn_σ, deleteOn_α_val h]

end P2

/-- **P2**: flipping a triangle without a corner on `C'` commutes with the deletion of `C'`. -/
theorem deleteOn_flip_of_no_corner (A : Arrangement (m + 1) D) (C' : Fin (m + 1)) (hm : 2 ≤ m)
    (K : D → Prop) [DecidablePred K] (hK : ∀ d, K d ↔ Keep A C' d) {d : D}
    (hT : A.IsTriangle (A.cellOf d))
    (hcorner : ∀ y ∈ (A.cellOf d).darts, C' ∉ Arrangement.Crossing.curves A (A.crossingOf y))
    (hK' : ∀ e, K e ↔ Keep (A.flip d hT) C' e) :
    ∃ (hd : K d) (hT' : (A.deleteOn C' hm K hK).IsTriangle ((A.deleteOn C' hm K hK).cellOf ⟨d, hd⟩)),
      (A.flip d hT).deleteOn C' hm K hK' = (A.deleteOn C' hm K hK).flip ⟨d, hd⟩ hT' := by
  have hcK : ∀ z, A.IsCorner d z → K z := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := mem_image.1 hz
    exact keep_crossing hK hyz.symm ((hK y).2 ((keep_iff_not_mem y).2 (hcorner y hy)))
  have hb : ∀ b, A.cellOf b = A.cellOf d → K b ∧ K (A.α b) := fun b h =>
    ⟨hcK _ (Arrangement.isCorner_of_mem h), hcK _ (Arrangement.isCorner_α_of_mem h)⟩
  have hd : K d := (hb d rfl).1
  set δ := A.deleteOn C' hm K hK with hδ
  have c1 : A.cellOf (A.φ d) = A.cellOf d := A.cellOf_φ d
  have c2 : A.cellOf (A.φ (A.φ d)) = A.cellOf d := by rw [A.cellOf_φ, A.cellOf_φ]
  set d0 : {d // K d} := ⟨d, hd⟩
  set d1 : {d // K d} := ⟨A.φ d, (hb _ c1).1⟩
  set d2 : {d // K d} := ⟨A.φ (A.φ d), (hb _ c2).1⟩
  have hφ0 : δ.φ d0 = d1 := Subtype.ext (deleteOn_φ_val (hb d rfl).2)
  have hφ1 : δ.φ d1 = d2 := Subtype.ext (deleteOn_φ_val (hb _ c1).2)
  have hφ2 : δ.φ d2 = d0 :=
    Subtype.ext ((deleteOn_φ_val (hb _ c2).2).trans (Arrangement.tri_φφφ hT))
  have horb : orbitFinset δ.φ d0 = {d0, d1, d2} := by
    rw [orbitFinset_three (by rw [hφ0, hφ1, hφ2]), hφ0, hφ1]
  have horbA : orbitFinset A.φ d = {d, A.φ d, A.φ (A.φ d)} :=
    orbitFinset_three (Arrangement.tri_φφφ hT)
  have hmap : ({d0, d1, d2} : Finset {d // K d}).map ⟨Subtype.val, Subtype.val_injective⟩ =
      {d, A.φ d, A.φ (A.φ d)} := by
    simp [map_insert, d0, d1, d2]
  have hTδ : δ.IsTriangle (δ.cellOf d0) := by
    show (orbitFinset δ.φ d0).card = 3
    rw [horb, ← card_map ⟨Subtype.val, Subtype.val_injective⟩, hmap, ← horbA]
    exact hT
  refine ⟨hd, hTδ, ?_⟩
  have hcell : ∀ y : {d // K d}, δ.cellOf y = δ.cellOf d0 ↔ A.cellOf y.val = A.cellOf d := by
    intro y
    have e1 : δ.cellOf y = δ.cellOf d0 ↔ y ∈ orbitFinset δ.φ d0 := Orbit.mem_darts.symm
    have e2 : A.cellOf y.val = A.cellOf d ↔ y.val ∈ orbitFinset A.φ d := Orbit.mem_darts.symm
    rw [e1, e2, horb, horbA]
    simp only [mem_insert, mem_singleton, Subtype.ext_iff, d0, d1, d2]
  have hside : ∀ y, y ∈ δ.sideDarts d0 ↔ y.val ∈ A.sideDarts d := by
    intro y
    rw [Arrangement.mem_sideDarts, Arrangement.mem_sideDarts, hcell, hcell]
    refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · have h1 := deleteOn_α_val (hK := hK) (hm := hm) (z := δ.α y) (hb _ h).2
      rw [show δ.α (δ.α y) = y from δ.α_α y] at h1
      rw [h1, A.α_α]; exact h
    · rw [deleteOn_α_val (hb _ h).1]; exact h
  have hst : ∀ z : {d // K d}, z.val ∈ A.sideDarts d → (δ.straight z).val = A.straight z.val :=
    fun z hz => deleteOn_straight_val (hcK _ (corner_straight_of_mem_sideDarts hT hz))
  have hρ : ∀ y : {d // K d}, (Arrangement.flipρ hTδ y).val = Arrangement.flipρ hT y.val := by
    intro y
    rw [Arrangement.flipρ_apply, Arrangement.flipρ_apply]
    unfold swapAlong
    by_cases h1 : y.val ∈ A.sideDarts d
    · rw [if_pos ((hside y).2 h1), if_pos h1, hst y h1]
    rw [if_neg (fun h => h1 ((hside y).1 h)), if_neg h1]
    by_cases h2 : A.straight.symm y.val ∈ A.sideDarts d
    · have hz : K (A.straight.symm y.val) := hcK _ (corner_of_mem_sideDarts hT h2)
      have hzy : δ.straight.symm y = ⟨_, hz⟩ := by
        rw [Equiv.symm_apply_eq]
        exact Subtype.ext ((hst ⟨_, hz⟩ h2).trans (A.straight.apply_symm_apply _)).symm
      rw [if_pos h2, hzy, if_pos ((hside _).2 h2)]
    · rw [if_neg h2, if_neg]
      intro hw
      apply h2
      have h3 := hst _ ((hside _).1 hw)
      rw [δ.straight.apply_symm_apply] at h3
      rw [h3, A.straight.symm_apply_apply]
      exact (hside _).1 hw
  have hKρ : ∀ y, K (Arrangement.flipρ hT y) ↔ K y := by
    intro y
    rw [Arrangement.flipρ_apply]
    unfold swapAlong
    by_cases h1 : y ∈ A.sideDarts d
    · rw [if_pos h1]
      exact iff_of_true (hcK _ (corner_straight_of_mem_sideDarts hT h1))
        (hcK _ (corner_of_mem_sideDarts hT h1))
    rw [if_neg h1]
    by_cases h2 : A.straight.symm y ∈ A.sideDarts d
    · rw [if_pos h2]
      refine iff_of_true (hcK _ (corner_of_mem_sideDarts hT h2)) ?_
      have := hcK _ (corner_straight_of_mem_sideDarts hT h2)
      rwa [A.straight.apply_symm_apply] at this
    · rw [if_neg h2]
  refine Arrangement.ext_straight ?_ ?_ fun x => Subtype.ext ?_
  · ext x
    rw [deleteOn_σ]
    exact (deleteOn_σ A C' hm K hK x).symm
  · funext x
    apply Fin.succAbove_right_injective (p := C')
    rw [deleteOn_curve]
    exact (deleteOn_curve A C' hm K hK x).symm
  · rw [show (δ.flip d0 hTδ).straight x = Arrangement.flipρ hTδ (δ.straight (Arrangement.flipρ hTδ x))
      from Arrangement.flip_straightPerm hTδ x, hρ]
    refine IsFirst.unique (deleteOn_first _ C' hm K hK' x) ?_
    refine isFirst_conj (Arrangement.flipρ_flipρ hT) hKρ (fun y => Arrangement.flip_straightPerm hT y) ?_
    rw [← hρ]
    exact deleteOn_first A C' hm K hK _

/-- Flips do not change the kept darts. -/
theorem keep_flip_iff (A : Arrangement n D) (C' : Fin n) {d : D} (hT : A.IsTriangle (A.cellOf d))
    (y : D) : Keep (A.flip d hT) C' y ↔ Keep A C' y := Iff.rfl

end Pca.FlipGraph
