/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): the band end triangle next to the digon (for `mimic_move_digon`)

`C`, `C'` parallel with the digon `cellOf a` (`a` on `C`, outside `C`, inside `C'`). The dart
`g = σ² a` starts at the corner `Z₂` of the digon and runs along `C` away from it, with the band
`int C ∩ ext C'` on its right. The cell of `g` is the **band end triangle** `Δ = (Z₂, X₁, Y₁)`:
`u = φ g` is a single segment of a curve `c₁` from `X₁ ∈ C` to `Y₁ ∈ C'` (`Par`), and the dart
`v = φ u` on `C'` ends at `Z₂`, so `φ v = g` (`band_tri`).

The last step is a cut (`Chain.exists_norm` in the band lens `int C ∩ ext C'`): if `v` ended at a
crossing `W` of `C'` with a curve `c`, the chain `g + u + (C'-walk of v up to C)` is even, its
normalized cut has value `1` on the cell of `g`, hence on the cell of `w = φ v` (the dart of `c`
at `W`); the segment of `w` ends on `C` at a dart with value `0` (a crossing of `c` and `C` other
than the ends of `g`), on `C'` (then `c` would never reach `C` outside `C'`) or at a crossing of
two other curves in the band (`Par`). FROS: "the digon is transferred to a neighboring edge".
-/
import Pca.FlipGraph.MimicPar
import Pca.FlipGraph.Chain
import Pca.FlipGraph.Chord
import Pca.FlipGraph.ClaimA

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement

namespace Marked

variable (M : Marked n D)

/-- The interior status of the cell of `σ² y`. -/
theorem inside_σσ_iff (E : Fin n) (y : D) :
    M.Inside E (M.A.cellOf (M.A.σ (M.A.σ y))) ↔
      ((M.Inside E (M.A.cellOf y) ↔ M.A.curve y ≠ E) ↔ M.A.curve (M.A.σ y) ≠ E) := by
  rw [M.A.cellOf_σ, M.inside_α, M.A.cellOf_σ, M.inside_α]

/-- A cell outside `C` and inside `C'` is the digon (`digon_region`). -/
theorem par_digon_cell {C C' : Fin n} {a : D} (hD : M.A.IsDigon (M.A.cellOf a))
    (ha : M.A.curve a = C) (hφa : M.A.curve (M.A.φ a) = C') (hout : ¬ M.Inside C (M.A.cellOf a))
    (hin : M.Inside C' (M.A.cellOf a)) {w : D} (h1 : ¬ M.Inside C (M.A.cellOf w))
    (h2 : M.Inside C' (M.A.cellOf w)) : M.A.cellOf w = M.A.cellOf a := by
  subst ha; subst hφa
  obtain ⟨s, hs⟩ := M.A.exists_isSide (M.A.curve a)
  obtain ⟨s', hs'⟩ := M.A.exists_isSide (M.A.curve (M.A.φ a))
  have key : ∀ u v t : ZMod 2, u ≠ t → v ≠ t → u = v := by decide
  have key2 : ∀ u t : ZMod 2, ¬ u ≠ t → u = t := fun u t h => not_not.1 h
  refine digon_region hD hs hs' ?_ ?_
  · rw [key2 (s (M.A.cellOf w)) (s M.z) (by rw [← M.inside_iff hs]; exact h1),
      key2 (s (M.A.cellOf a)) (s M.z) (by rw [← M.inside_iff hs]; exact hout)]
  · exact key _ _ _ ((M.inside_iff hs' _).1 h2) ((M.inside_iff hs' _).1 hin)

/-- The darts of a digon cell. -/
theorem digon_darts {a y : D} (hD : M.A.IsDigon (M.A.cellOf a)) (hy : M.A.cellOf y = M.A.cellOf a) :
    y = a ∨ y = M.A.φ a :=
  two_cycle (M.A.φ_φ_of_digon hD) (M.A.mem_darts_cellOf.1 (hy ▸ M.A.mem_darts_cellOf_self y))

/-- A segment of `c ∉ {C, C'}` inside `C` with both ends on `C` is impossible (the rest of `c`
would be outside `C`, also at its crossings with `C'`). -/
theorem par_no_C_chord {C C' : Fin n} (hpar : M.Par C C') {y : D} (hyC : M.A.curve y ≠ C)
    (hyC' : M.A.curve y ≠ C') (hs : C ∈ Crossing.curves M.A (M.A.crossingOf y))
    (he : C ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α y))) (hin : M.Inside C (M.A.cellOf y)) :
    False := by
  have hst := M.walk_status hyC hs he
  have hc := Walk.card_flipsOn M.A hyC'
  obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < (Walk.flipsOn M.A C' y).card)
  rw [Walk.mem_flipsOn] at hi
  have hcu : M.A.curve ((M.A.straight ^ i) y) = M.A.curve y := Walk.curve_pow M.A y i
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, Perm.one_apply] at hi
    have h1 := (M.A.mem_curves_end_iff hyC).1 he
    exact hpar.1 (h1.symm.trans hi.2)
  have hout := (hst i (by omega) hi.1).1
  refine (hst i (by omega) hi.1).1 ?_ hin
  refine M.par_inside_C_end hpar (by rw [hcu]; exact hyC) ?_ ?_
  · rw [M.A.mem_curves_end_iff (by rw [hcu]; exact hyC'), hi.2]
  · rw [M.A.mem_curves_end_iff (by rw [hcu]; exact hyC), hi.2]; exact Ne.symm hpar.1

/-- A segment of `c ∉ {C, C'}` outside `C'` with both ends on `C'` is impossible (the rest of `c`
would be inside `C'`, also at its crossings with `C`). -/
theorem par_no_C'_chord {C C' : Fin n} (hpar : M.Par C C') {y : D} (hyC : M.A.curve y ≠ C)
    (hyC' : M.A.curve y ≠ C') (hs : C' ∈ Crossing.curves M.A (M.A.crossingOf y))
    (he : C' ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α y))) (hout : ¬ M.Inside C' (M.A.cellOf y)) :
    False := by
  have hst := M.walk_status hyC' hs he
  have hc := Walk.card_flipsOn M.A hyC
  obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < (Walk.flipsOn M.A C y).card)
  rw [Walk.mem_flipsOn] at hi
  have hcu : M.A.curve ((M.A.straight ^ i) y) = M.A.curve y := Walk.curve_pow M.A y i
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, Perm.one_apply] at hi
    have h1 := (M.A.mem_curves_end_iff hyC').1 he
    exact hpar.1 (hi.2.symm.trans h1)
  have hin := (hst i (by omega) hi.1).2 hout
  refine M.par_outside_C'_end hpar (by rw [hcu]; exact hyC') ?_ ?_ hin
  · rw [M.A.mem_curves_end_iff (by rw [hcu]; exact hyC), hi.2]
  · rw [M.A.mem_curves_end_iff (by rw [hcu]; exact hyC'), hi.2]; exact hpar.1

/-- The band cell of `g = σ² a`: inside `C`, outside `C'`. -/
theorem band_g {C C' : Fin n} (hCC : C ≠ C') {a : D} (hD : M.A.IsDigon (M.A.cellOf a))
    (ha : M.A.curve a = C) (hφa : M.A.curve (M.A.φ a) = C') (hout : ¬ M.Inside C (M.A.cellOf a))
    (hin : M.Inside C' (M.A.cellOf a)) :
    M.A.curve (M.A.σ a) = C' ∧ M.Inside C (M.A.cellOf (M.A.σ (M.A.σ a))) ∧
      ¬ M.Inside C' (M.A.cellOf (M.A.σ (M.A.σ a))) := by
  have hσa : M.A.curve (M.A.σ a) = C' := by
    have h := (digon_corner M.A hD rfl).2
    rw [hφa, M.A.curves_crossingOf, ha, mem_insert, mem_singleton] at h
    rcases h with h | h
    · exact absurd h.symm hCC
    · exact h.symm
  refine ⟨hσa, ?_, ?_⟩
  · rw [M.inside_σσ_iff, ha, hσa]; simp [hout, Ne.symm hCC]
  · rw [M.inside_σσ_iff, ha, hσa]; simp [hin, hCC]

/-- **The band end triangle**: with `g = σ² a`, `φ³ g = g`, the third side `φ² g` is on `C'`
and the end `X₁` of `g` is not on `C'`. -/
theorem band_tri {C C' : Fin n} (hn : 3 ≤ n) (hpar : M.Par C C') {a : D}
    (hD : M.A.IsDigon (M.A.cellOf a)) (ha : M.A.curve a = C) (hφa : M.A.curve (M.A.φ a) = C')
    (hout : ¬ M.Inside C (M.A.cellOf a)) (hin : M.Inside C' (M.A.cellOf a)) :
    M.A.φ (M.A.φ (M.A.φ (M.A.σ (M.A.σ a)))) = M.A.σ (M.A.σ a) ∧
      M.A.curve (M.A.φ (M.A.φ (M.A.σ (M.A.σ a)))) = C' ∧
      C' ∉ Crossing.curves M.A (M.A.crossingOf (M.A.α (M.A.σ (M.A.σ a)))) := by
  classical
  have hCC := hpar.1
  obtain ⟨hσa, hgC, hgC'⟩ := M.band_g hCC hD ha hφa hout hin
  set g := M.A.σ (M.A.σ a) with hgdef
  have cg : M.A.curve g = C := by rw [hgdef, M.A.curve_σσ, ha]
  -- `X₁`, the end of `g`, is not on `C'` (position `1` of the walk of `α a`)
  have hX₁ : C' ∉ Crossing.curves M.A (M.A.crossingOf (M.A.α g)) := by
    intro h
    have haC : M.A.curve (M.A.α a) ≠ C' := by rw [M.A.curve_α, ha]; exact hCC
    have hs : C' ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α a)) := by
      have := (digon_corner M.A hD (M.A.cellOf_φ a)).2
      rwa [hφa, M.A.φ_apply, M.A.crossingOf_σ] at this
    have he : C' ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α (M.A.α a))) := by
      rw [M.A.α_α]; have := (digon_corner M.A hD rfl).2; rwa [hφa] at this
    obtain ⟨hp2, hf⟩ := M.walk_flips haC hs he
    have hP := M.A.two_mul_le_period_straight (M.A.α a)
    have h1 : 1 ∈ Walk.flipsOn M.A C' (M.A.α a) := by
      rw [Walk.mem_flipsOn, pow_one, M.A.straight_α, ← hgdef]
      refine ⟨by omega, ?_⟩
      exact (M.A.mem_curves_end_iff (by rw [cg]; exact hCC)).1 h
    rw [hf, mem_insert, mem_singleton] at h1
    omega
  -- `u = φ g` on a curve `c₁ ∉ {C, C'}`, a single segment from `X₁` to `C'`
  set u := M.A.φ g with hudef
  have cuC : M.A.curve u ≠ C := by rw [hudef, ← cg]; exact M.A.curve_φ_ne g
  have cuC' : M.A.curve u ≠ C' := by
    intro h; apply hX₁; rw [← M.A.crossingOf_φ, ← h]; exact M.A.mem_curves_crossingOf u
  have hcu : M.A.cellOf u = M.A.cellOf g := M.A.cellOf_φ g
  have huC : M.Inside C (M.A.cellOf u) := by rw [hcu]; exact hgC
  have huC' : ¬ M.Inside C' (M.A.cellOf u) := by rw [hcu]; exact hgC'
  have hαuC : M.Inside C (M.A.cellOf (M.A.α u)) := by rw [M.inside_α]; simp [huC, cuC]
  have hαuC' : ¬ M.Inside C' (M.A.cellOf (M.A.α u)) := by rw [M.inside_α]; simp [huC', cuC']
  have hXu : C ∈ Crossing.curves M.A (M.A.crossingOf u) := by
    rw [hudef, M.A.crossingOf_φ, ← cg, ← M.A.curve_α]; exact M.A.mem_curves_crossingOf _
  have hY₁ : M.A.curve (M.A.σ (M.A.α u)) = C' := by
    by_contra hne
    by_cases hc : M.A.curve (M.A.σ (M.A.α u)) = C
    · exact M.par_no_C_chord hpar cuC cuC' hXu ((M.A.mem_curves_end_iff cuC).2 hc) huC
    · have h1 : C ∉ Crossing.curves M.A (M.A.crossingOf (M.A.α u)) := by
        rw [M.A.mem_curves_end_iff cuC]; exact hc
      have h2 : C' ∉ Crossing.curves M.A (M.A.crossingOf (M.A.α u)) := by
        rw [M.A.mem_curves_end_iff cuC']; exact hne
      apply hpar.2.2 _ h1 h2
      rw [M.crossInside_iff h1, M.crossInside_iff h2]
      exact ⟨hαuC, hαuC'⟩
  -- `v = φ u` on `C'`; its walk up to the first crossing with `C`
  set v := M.A.φ u with hvdef
  have cv : M.A.curve v = C' := hY₁
  have hcv : M.A.cellOf v = M.A.cellOf g := by rw [hvdef, M.A.cellOf_φ, hcu]
  have hvC : M.A.curve v ≠ C := by rw [cv]; exact Ne.symm hCC
  have hex : ∃ i, M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) v))) = C := by
    have hc := Walk.card_flipsOn M.A hvC
    obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < (Walk.flipsOn M.A C v).card)
    exact ⟨i, ((Walk.mem_flipsOn M.A).1 hi).2⟩
  set j := Nat.find hex with hjdef
  have hj : M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ j) v))) = C := Nat.find_spec hex
  have hjmin : ∀ i < j, M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ i) v))) ≠ C :=
    fun i hi => Nat.find_min hex hi
  have hband : ∀ i ≤ j, M.Inside C (M.A.cellOf ((M.A.straight ^ i) v)) ∧
      ¬ M.Inside C' (M.A.cellOf ((M.A.straight ^ i) v)) := by
    intro i hi
    refine ⟨?_, by rw [M.inside_pow_of_curve cv, hcv]; exact hgC'⟩
    induction i with
    | zero => rw [pow_zero, Perm.one_apply, hcv]; exact hgC
    | succ i ih =>
      rw [Walk.pow_succ_apply, M.inside_straight]
      simp [ih (by omega), hjmin i (by omega)]
  -- the dart after the walk is `g`
  set y := (M.A.straight ^ j) v with hydef
  have cy : M.A.curve y = C' := by rw [hydef, Walk.curve_pow, cv]
  have hφy : M.A.φ y = g := by
    set x := M.A.φ y with hxdef
    have cx : M.A.curve x = C := hj
    have hcx : M.A.cellOf x = M.A.cellOf y := M.A.cellOf_φ y
    have hσx : M.A.curve (M.A.σ x) = C' := by
      have h := M.A.mem_curves_crossingOf_σ x
      have h' : M.A.curve y ∈ Crossing.curves M.A (M.A.crossingOf x) := by
        rw [hxdef, M.A.crossingOf_φ, ← M.A.curve_α]; exact M.A.mem_curves_crossingOf _
      rw [M.A.curves_crossingOf, cy, cx, mem_insert, mem_singleton] at h'
      rcases h' with h' | h'
      · exact absurd h'.symm hCC
      · exact h'.symm
    have hb := hband j le_rfl
    rw [← hydef, ← hcx] at hb
    have hd1 : ¬ M.Inside C (M.A.cellOf (M.A.σ (M.A.σ x))) := by
      rw [M.inside_σσ_iff, cx, hσx]; simp [hb.1, Ne.symm hCC]
    have hd2 : M.Inside C' (M.A.cellOf (M.A.σ (M.A.σ x))) := by
      rw [M.inside_σσ_iff, cx, hσx]; simp [hb.2, hCC]
    have hcell := M.par_digon_cell hD ha hφa hout hin hd1 hd2
    rcases M.digon_darts hD hcell with h | h
    · rw [hgdef, ← h, M.A.σ_σ_σ_σ]
    · exfalso; have := congrArg M.A.curve h; rw [M.A.curve_σσ, cx, hφa] at this; exact hCC this
  refine ⟨?_, cv, hX₁⟩
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · rw [hydef, hj0, pow_zero, Perm.one_apply] at hφy; exact hφy
  exfalso
  -- the cut along `g + u + (walk of v)` in the band lens
  set Λ := M.twoLens (Ne.symm hCC) False True with hΛ
  have hQ : ∀ f, Λ.Q f ↔ M.Inside C f ∧ ¬ M.Inside C' f := by
    intro f; change M.TwoQ C' C False True f ↔ _; unfold TwoQ; tauto
  set c : M.A.Segment → ZMod 2 := Chain.δ (M.A.segmentOf g) + Chain.δ (M.A.segmentOf u) +
    Chain.walk v (j + 1) with hcdef
  have hcrv : M.A.crossingOf v = M.A.crossingOf (M.A.α u) := M.A.crossingOf_φ u
  have hcru : M.A.crossingOf u = M.A.crossingOf (M.A.α g) := M.A.crossingOf_φ g
  have hend : M.A.crossingOf ((M.A.straight ^ (j + 1)) v) = M.A.crossingOf g := by
    rw [← Chain.crossingOf_α_pow, ← hydef, ← M.A.crossingOf_φ, hφy]
  have hev : Chain.IsEven c := by
    intro x
    rw [hcdef, Chain.bd_add, Chain.bd_add, Chain.bd_δ, Chain.bd_δ, Chain.bd_walk, hcrv, hcru, hend]
    have key : ∀ p q r : ZMod 2, p + q + (q + r) + (r + p) = 0 := by decide
    exact key _ _ _
  have hval : ∀ s, c s ≠ 0 → s = M.A.segmentOf g ∨ s = M.A.segmentOf u ∨
      ∃ i < j + 1, s = M.A.segmentOf ((M.A.straight ^ i) v) := by
    intro s hs
    by_contra hno
    push Not at hno
    apply hs
    rw [hcdef, Pi.add_apply, Pi.add_apply, Chain.walk_apply]
    simp only [Chain.δ, if_neg hno.1, if_neg hno.2.1]
    rw [Finset.sum_eq_zero (fun i hi => if_neg (hno.2.2 i (mem_range.1 hi)))]
    simp
  have hQg : Λ.Q (M.A.cellOf g) := (hQ _).2 ⟨hgC, hgC'⟩
  have hsupp : Chain.Supp Λ c := by
    intro z hz
    have hQz : ∀ t, Λ.Q (M.A.cellOf t) → M.A.segmentOf z = M.A.segmentOf t →
        Λ.Q (M.A.cellOf z) ∨ Λ.Q (M.A.cellOf (M.A.α z)) := by
      intro t ht e
      rcases eq_or_eq_α_of_segmentOf e with rfl | rfl
      · exact Or.inl ht
      · right; rwa [M.A.α_α]
    rcases hval _ hz with h | h | ⟨i, hi, h⟩
    · exact hQz g hQg h
    · exact hQz u (by rw [hcu]; exact hQg) h
    · exact hQz _ ((hQ _).2 (hband i (by omega))) h
  obtain ⟨r, hr, hnorm⟩ := Chain.exists_norm Λ hev hsupp
  -- curves of the chain segments
  have hseg_curve : ∀ z t, M.A.segmentOf z = M.A.segmentOf t → M.A.curve z = M.A.curve t := by
    intro z t e
    rcases eq_or_eq_α_of_segmentOf e with rfl | rfl
    · rfl
    · exact M.A.curve_α t
  have hcz : ∀ z, M.A.curve z = C → c (M.A.segmentOf z) = if M.A.segmentOf z = M.A.segmentOf g
      then 1 else 0 := by
    intro z hz
    rw [hcdef, Pi.add_apply, Pi.add_apply, Chain.walk_apply]
    have h1 : M.A.segmentOf z ≠ M.A.segmentOf u := fun e => cuC (by rw [← hseg_curve _ _ e, hz])
    have h2 : ∀ i ∈ range (j + 1), M.A.segmentOf z ≠ M.A.segmentOf ((M.A.straight ^ i) v) :=
      fun i _ e => hCC (by rw [← hz, hseg_curve _ _ e, Walk.curve_pow, cv])
    simp only [Chain.δ, if_neg h1]
    rw [Finset.sum_eq_zero (fun i hi => if_neg (h2 i hi))]
    simp
  have hrg : r (M.A.cellOf g) = 1 := by
    have h := hr g
    have hαg : ¬ Λ.Q (M.A.cellOf (M.A.α g)) := fun h' => by
      rw [hQ, M.inside_α] at h'; simp [hgC, cg] at h'
    rw [hnorm _ hαg, add_zero, hcz g cg, if_pos rfl] at h
    exact h
  -- the dart `w = φ v` of `c` at the end of `v`
  set w := M.A.φ v with hwdef
  have cwC' : M.A.curve w ≠ C' := by rw [hwdef, ← cv]; exact M.A.curve_φ_ne v
  have cwC : M.A.curve w ≠ C := by
    have := hjmin 0 hj0; rwa [pow_zero, Perm.one_apply] at this
  have hcw : M.A.cellOf w = M.A.cellOf g := by rw [hwdef, M.A.cellOf_φ, hcv]
  have hrw : r (M.A.cellOf (M.A.σ (M.A.α w))) = 1 := by
    rw [← M.A.φ_apply, M.A.cellOf_φ, hcw, hrg]
  have hwC : M.Inside C (M.A.cellOf w) := by rw [hcw]; exact hgC
  have hwC' : ¬ M.Inside C' (M.A.cellOf w) := by rw [hcw]; exact hgC'
  by_cases hC : C ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α w))
  · -- the segment of `w` ends on `C`: an `R`-dart with chain value `0`
    set x := M.A.σ (M.A.α w) with hxdef
    have cx : M.A.curve x = C := (M.A.mem_curves_end_iff cwC).1 hC
    have hcx : M.A.cellOf x = M.A.cellOf g := by rw [hxdef, ← M.A.φ_apply, M.A.cellOf_φ, hcw]
    have hR : Λ.R x := ⟨cx, by rw [hcx]; exact hQg⟩
    have h0 : c (M.A.segmentOf x) = 0 := by
      rw [hcz x cx, if_neg]
      intro e
      rcases eq_or_eq_α_of_segmentOf e with h | h
      · apply hX₁
        have hx' : M.A.crossingOf x = M.A.crossingOf g := by rw [h]
        have h' : C' ∈ Crossing.curves M.A (M.A.crossingOf x) := by
          rw [hx', hgdef, M.A.crossingOf_σσ, ← hσa]; exact M.A.mem_curves_crossingOf_σ a
        rw [hxdef, M.A.crossingOf_σ, M.A.curves_crossingOf, M.A.curve_α, mem_insert,
          mem_singleton] at h'
        rcases h' with h' | h'
        · exact absurd h'.symm cwC'
        · exact absurd (h'.trans (by rw [← hxdef]; exact cx)) hCC.symm
      · have : M.Inside C (M.A.cellOf (M.A.α g)) := by rw [← h, hcx]; exact hgC
        rw [M.inside_α] at this; simp [hgC, cg] at this
    have := Chain.norm_R Λ hr hnorm hR h0
    rw [hrw] at this
    exact one_ne_zero this
  by_cases hC' : C' ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α w))
  · -- both ends of `w` on `C'`
    have hs : C' ∈ Crossing.curves M.A (M.A.crossingOf w) := by
      rw [hwdef, M.A.crossingOf_φ, ← cv, ← M.A.curve_α]; exact M.A.mem_curves_crossingOf _
    exact M.par_no_C'_chord hpar cwC cwC' hs hC' hwC'
  · -- a crossing of two other curves in the band
    apply hpar.2.2 _ hC hC'
    rw [M.crossInside_iff hC, M.crossInside_iff hC', M.inside_α, M.inside_α]
    simp [hwC, hwC', cwC, cwC']

/-- The `C`-darts at the corners of the digon: `a`, `σ² a` (at the start of `a`) and `α a`,
`σ² (α a)` (at its end). -/
theorem par_CC'_dart {C C' : Fin n} (hCC : C ≠ C') {a : D} (hD : M.A.IsDigon (M.A.cellOf a))
    (ha : M.A.curve a = C) (hφa : M.A.curve (M.A.φ a) = C') (hout : ¬ M.Inside C (M.A.cellOf a))
    (hin : M.Inside C' (M.A.cellOf a)) {x : D} (hx : M.A.curve x = C)
    (hx' : C' ∈ Crossing.curves M.A (M.A.crossingOf x)) :
    x = a ∨ x = M.A.σ (M.A.σ a) ∨ x = M.A.α a ∨ x = M.A.σ (M.A.σ (M.A.α a)) := by
  have hσx : M.A.curve (M.A.σ x) = C' := by
    rw [M.A.curves_crossingOf, hx, mem_insert, mem_singleton] at hx'
    rcases hx' with h | h
    · exact absurd h.symm hCC
    · exact h.symm
  have hσφ : ∀ y, M.A.σ y = M.A.φ a → M.A.σ (M.A.α a) = M.A.σ y := fun y h => by
    rw [h, M.A.φ_apply]
  have dig := fun {w : D} => M.par_digon_cell hD ha hφa hout hin (w := w)
  by_cases p : M.Inside C (M.A.cellOf x) <;> by_cases q : M.Inside C' (M.A.cellOf x)
  · -- `σ x` is the digon dart on `C'`
    have h1 : ¬ M.Inside C (M.A.cellOf (M.A.σ x)) := by
      rw [M.A.cellOf_σ, M.inside_α]; simp [p, hx]
    have h2 : M.Inside C' (M.A.cellOf (M.A.σ x)) := by
      rw [M.A.cellOf_σ, M.inside_α]; simp [q, hx, hCC]
    rcases M.digon_darts hD (dig h1 h2) with h | h
    · exfalso; rw [← h, hσx] at ha; exact hCC ha.symm
    · right; right; left
      exact M.A.σ.injective (hσφ x h).symm
  · -- `σ² x` is `a`
    have h1 : ¬ M.Inside C (M.A.cellOf (M.A.σ (M.A.σ x))) := by
      rw [M.inside_σσ_iff, hx, hσx]; simp [p, hCC.symm]
    have h2 : M.Inside C' (M.A.cellOf (M.A.σ (M.A.σ x))) := by
      rw [M.inside_σσ_iff, hx, hσx]; simp [q, hCC]
    rcases M.digon_darts hD (dig h1 h2) with h | h
    · right; left; rw [← h, M.A.σ_σ_σ_σ]
    · exfalso; have := congrArg M.A.curve h; rw [M.A.curve_σσ, hx, hφa] at this; exact hCC this
  · left
    rcases M.digon_darts hD (dig p q) with h | h
    · exact h
    · exfalso; have := congrArg M.A.curve h; rw [hx, hφa] at this; exact hCC this
  · -- `σ³ x` is the digon dart on `C'`
    have h1 : ¬ M.Inside C (M.A.cellOf (M.A.σ (M.A.σ (M.A.σ x)))) := by
      rw [M.A.cellOf_σ, M.inside_α, M.inside_σσ_iff, hx, hσx, M.A.curve_σσ, hx]; simp [p, hCC.symm]
    have h2 : M.Inside C' (M.A.cellOf (M.A.σ (M.A.σ (M.A.σ x)))) := by
      rw [M.A.cellOf_σ, M.inside_α, M.inside_σσ_iff, hx, hσx, M.A.curve_σσ, hx]; simp [q, hCC]
    rcases M.digon_darts hD (dig h1 h2) with h | h
    · exfalso; have := congrArg M.A.curve h; rw [M.A.curve_σσσ, hσx, ha] at this; exact hCC this.symm
    · right; right; right
      have e := M.A.σ.injective (hσφ _ h)
      rw [e, M.A.σ_σ_σ_σ]

/-- The far end `X₀` of `straight a` is not on `C'`. -/
theorem digon_X0 (hn : 3 ≤ n) {C' : Fin n} {a : D} (ha : M.A.curve a ≠ C')
    (h0 : C' ∈ Crossing.curves M.A (M.A.crossingOf a))
    (h1 : C' ∈ Crossing.curves M.A (M.A.crossingOf (M.A.α a))) :
    C' ∉ Crossing.curves M.A (M.A.crossingOf (M.A.α (M.A.straight a))) := by
  have hP := M.A.two_mul_le_period_straight a
  obtain ⟨-, hfa⟩ := M.walk_flips ha h0 h1
  intro h
  have h1 : 1 ∈ Walk.flipsOn M.A C' a := by
    rw [Walk.mem_flipsOn, pow_one]
    exact ⟨by omega, (M.A.mem_curves_end_iff (by rw [M.A.curve_straight]; exact ha)).1 h⟩
  rw [hfa, mem_insert, mem_singleton] at h1
  omega

end Marked

end Pca.FlipGraph
