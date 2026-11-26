/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): every intersecting arrangement can be flipped to a cylindrical one

FROS, proof of Theorem 3 (`sec:main_ipa`): "We show by induction on `n` that `𝒜` can be transformed
into a cylindrical arrangement with a finite number of triangle flips. [...] we choose `p` as a
point which lies inside a maximum number of pseudocircles. [...] there exists a pseudocircle `C`
which does not contain `p` in its interior. We show how to expand `C` using only triangle flips
until it contains `p`. First observe that Lemma [SH] guarantees the existence of a flip to expand
`C`. Since `C` already intersects all other pseudocircles, this must be a triangle or digon-collapse
flip. As long as there exists a triangle flip expanding `C`, we perform it [...]. Suppose now that
`C` does not yet contain `p` and can only be expanded by collapsing a digon `D` formed with another
pseudocircle `C'`. Note that we may assume `p` to not lie in `D` (and in no other cell adjacent to
`C`), since otherwise we could expand `C` until it contains `p` without performing any flip.
Furthermore, every other pseudocircle `C''` intersects the lens `int C ∩ ext C'` transversally [...]
Now we can use Lemma [zipping] to expand `C'` until `C` and `C'` are parallel." Then `𝒜 − {C'}` and
the mimicking (`Mimic.lean`).

Graph language: the point `p` is a cell; "`p` adjacent to `C`" is handled by moving to the cell
across (it lies inside one more curve); SH's lemma is `Arrangement.sweepFirstMove` with the marked
cell as `f₀` (the digon or triangle lies outside `C`, has a side on `C`, and is not the marked cell).

* `expand_triangle`: flipping a triangle outside `C` with a side on `C` (not the marked cell) puts
  one more crossing into the interior of `C` and changes no interior status of other cells.
* `stuck_digon`: if the expanding cell of SH's lemma is a digon `D` with `C'`, then `D` lies in
  `int C'` and the lens `int C ∩ ext C'` is transversal (crossing form); after zipping, `C` and
  `C'` are parallel.
* `reach_cylindrical`: the induction.
-/
import Pca.FlipGraph.Zip
import Pca.FlipGraph.Mimic
import Pca.SweepLemma

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace Marked

variable (M : Marked n D)

open Classical in
/-- Four times the number of crossings in the interior of `C` (counted by their darts: darts at a
crossing not on `C` whose cell lies inside `C`). -/
noncomputable def numInside (C : Fin n) : ℕ :=
  (univ.filter (fun y : D => C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf y) ∧
    M.Inside C (M.A.cellOf y))).card

end Marked

/-- **Expanding `C` by a triangle flip**: flipping a triangle outside `C` with a side on `C` (not
the marked cell) increases the number of crossings inside `C`. -/
theorem expand_triangle (M : Marked n D) {C : Fin n} {d : D} (hT : M.A.IsTriangle (M.A.cellOf d))
    (hz : M.A.cellOf d ≠ M.z) (hout : ¬ M.Inside C (M.A.cellOf d)) (hC : M.A.curve d = C) :
    M.numInside C < (M.flip d hT).numInside C := by
  unfold Marked.numInside
  apply card_lt_card
  set w := M.A.σ (M.A.σ (M.A.φ (M.A.φ d)))
  have hTv : M.A.cellOf (M.A.φ (M.A.φ d)) = M.A.cellOf d := by
    rw [M.A.cellOf_φ, M.A.cellOf_φ]
  have hv : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf w) := by
    rw [M.A.crossingOf_σσ, ← hC]; exact Arrangement.tri_curve_not_mem hT
  -- the dart `w` at the apex: its cell is `T` after the flip, not inside `C` before
  have hwold : ¬ M.Inside C (M.A.cellOf w) := by
    rw [← (M.crossInside_iff hv), M.A.crossingOf_σσ, M.crossInside_iff (by
      rw [← hC]; exact Arrangement.tri_curve_not_mem hT), hTv]
    exact hout
  have hwnew : (M.flip d hT).Inside C ((M.flip d hT).A.cellOf w) := by
    change (M.flip d hT).Inside C ((M.A.flip d hT).cellOf w)
    rw [Arrangement.flip_cellOf, Arrangement.flipG'_σσ hTv, hTv, flip_inside M hT hz]
    have hHas : M.HasSideOn C (M.A.cellOf d) := ⟨d, Orbit.mem_darts.2 rfl, hC⟩
    tauto
  refine ⟨fun y hy => ?_, fun h => ?_⟩
  swap
  · have := @h w (by simp only [mem_filter, mem_univ, true_and]; exact ⟨hv, hwnew⟩)
    simp only [mem_filter, mem_univ, true_and] at this
    exact hwold this.2
  simp only [mem_filter, mem_univ, true_and] at hy ⊢
  obtain ⟨hyC, hyin⟩ := hy
  refine ⟨hyC, ?_⟩
  have hy : ¬ M.A.IsCorner d y := by
    intro hcor
    rw [Arrangement.IsCorner, Arrangement.corners_tri hT] at hcor
    simp only [mem_insert, mem_singleton] at hcor
    rcases hcor with h | h | h
    · apply hyC; rw [h, ← hC]; exact M.A.mem_curves_crossingOf d
    · apply hyC; rw [h, ← hC, M.A.φ_apply, M.A.crossingOf_σ]
      have := M.A.mem_curves_crossingOf (M.A.α d)
      rwa [M.A.curve_α] at this
    · apply hwold
      rw [← M.crossInside_iff hv, M.A.crossingOf_σσ, ← h, M.crossInside_iff hyC]
      exact hyin
  change (M.flip d hT).Inside C ((M.A.flip d hT).cellOf y)
  rw [Arrangement.flip_cellOf_of_not_corner hT hy, flip_inside M hT hz]
  have hne : M.A.cellOf y ≠ M.A.cellOf d := Arrangement.not_mem_of_not_corner hy
  tauto

/-- **The digon case** (FROS: "`C` can only be expanded by collapsing a digon `D` formed with
another pseudocircle `C'`"): a digon outside `C` with a side on `C` and not the marked cell lies in
`int C'`, and every other curve meets the lens `int C ∩ ext C'` transversally (it crosses `C'` only
in `int C` and `C` only in `ext C'`). In the notation of `twoLens`: `L ⊂ C'`, `R ⊂ C`, the lens is
`ext C' ∩ int C`. -/
theorem stuck_digon (M : Marked n D) {a : D} (hD : M.A.IsDigon (M.A.cellOf a))
    (hz : M.A.cellOf a ≠ M.z) (hout : ¬ M.Inside (M.A.curve a) (M.A.cellOf a)) :
    M.Inside (M.A.curve (M.A.φ a)) (M.A.cellOf a) ∧
      M.TwoTransversal (M.A.curve (M.A.φ a)) (M.A.curve a) False True := by
  set C := M.A.curve a
  set C' := M.A.curve (M.A.φ a)
  have hCC : C ≠ C' := (M.A.curve_φ_ne a).symm
  have hφφ : M.A.φ (M.A.φ a) = a := M.A.φ_φ_of_digon hD
  obtain ⟨s, hs⟩ := M.A.exists_isSide C
  obtain ⟨s', hs'⟩ := M.A.exists_isSide C'
  have key : ∀ u v : ZMod 2, ¬ (u ≠ v) → u = v := fun u v h => not_not.1 h
  have hsg : s (M.A.cellOf a) = s M.z := key _ _ (by rw [← M.inside_iff hs]; exact hout)
  -- the digon lies inside `C'`
  have hin : M.Inside C' (M.A.cellOf a) := by
    by_contra h
    have hs'g : s' (M.A.cellOf a) = s' M.z := key _ _ (by rw [← M.inside_iff hs']; exact h)
    exact hz (digon_region hD hs hs' hsg.symm hs'g.symm).symm
  refine ⟨hin, fun c hcL hcR => Or.inl ⟨fun x hx => ?_, fun x hx => ?_⟩⟩
  -- the corners of the digon are the crossings of `C` and `C'`
  · have hcorner : ∀ w, M.A.curve w = C' → M.A.segmentOf w = M.A.segmentOf (M.A.φ a) →
        C ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf w) := by
      intro w hw hseg
      rcases eq_or_eq_α_of_segmentOf hseg with h | h
      · rw [h, M.A.φ_apply, M.A.crossingOf_σ]
        have := M.A.mem_curves_crossingOf (M.A.α a); rwa [M.A.curve_α] at this
      · rw [h, ← M.A.crossingOf_σ, ← M.A.φ_apply, hφφ]; exact M.A.mem_curves_crossingOf a
    obtain ⟨y₀, rfl⟩ := x.exists_mk
    change Arrangement.Crossing.curves M.A (M.A.crossingOf y₀) = {c, C'} at hx
    obtain ⟨w, hw, hwx⟩ : ∃ w, M.A.curve w = C' ∧ M.A.crossingOf w = M.A.crossingOf y₀ := by
      rw [M.A.curves_crossingOf] at hx
      by_cases h0 : M.A.curve y₀ = C'
      · exact ⟨y₀, h0, rfl⟩
      · refine ⟨M.A.σ y₀, ?_, M.A.crossingOf_σ y₀⟩
        have : M.A.curve (M.A.σ y₀) ∈ ({c, C'} : Finset (Fin n)) := by rw [← hx]; simp
        have h1 : M.A.curve y₀ ∈ ({c, C'} : Finset (Fin n)) := by rw [← hx]; simp
        rcases mem_insert.1 this with h' | h'
        · rcases mem_insert.1 h1 with h'' | h''
          · exact absurd (h'.trans h''.symm) (M.A.isArrangement.curve_σ y₀)
          · exact absurd (mem_singleton.1 h'') h0
        · exact mem_singleton.1 h'
    have hxC : C ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf w) := by
      rw [hwx, hx]; simp [Ne.symm hcR, hCC]
    change M.CrossInside C (M.A.crossingOf y₀) ↔ True
    rw [← hwx, M.crossInside_iff hxC, iff_true, M.inside_iff hs]
    intro hsw
    have hg : s (M.A.cellOf w) = s (M.A.cellOf (M.A.φ a)) := by rw [hsw, M.A.cellOf_φ, hsg]
    have hs2 : M.A.IsSide (M.A.curve (M.A.φ (M.A.φ a))) s := by rw [hφφ]; exact hs
    exact hxC (hcorner w hw (digon_side_run (by rw [M.A.cellOf_φ]; exact hD) hs2 hw hg))
  · obtain ⟨y₀, rfl⟩ := x.exists_mk
    change Arrangement.Crossing.curves M.A (M.A.crossingOf y₀) = {c, C} at hx
    obtain ⟨w, hw, hwx⟩ : ∃ w, M.A.curve w = C ∧ M.A.crossingOf w = M.A.crossingOf y₀ := by
      rw [M.A.curves_crossingOf] at hx
      by_cases h0 : M.A.curve y₀ = C
      · exact ⟨y₀, h0, rfl⟩
      · refine ⟨M.A.σ y₀, ?_, M.A.crossingOf_σ y₀⟩
        have : M.A.curve (M.A.σ y₀) ∈ ({c, C} : Finset (Fin n)) := by rw [← hx]; simp
        have h1 : M.A.curve y₀ ∈ ({c, C} : Finset (Fin n)) := by rw [← hx]; simp
        rcases mem_insert.1 this with h' | h'
        · rcases mem_insert.1 h1 with h'' | h''
          · exact absurd (h'.trans h''.symm) (M.A.isArrangement.curve_σ y₀)
          · exact absurd (mem_singleton.1 h'') h0
        · exact mem_singleton.1 h'
    have hxC : C' ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf w) := by
      rw [hwx, hx]; simp [Ne.symm hcL, Ne.symm hCC]
    change M.CrossInside C' (M.A.crossingOf y₀) ↔ False
    rw [← hwx, M.crossInside_iff hxC, iff_false]
    intro hw'
    have hgs : s' (M.A.cellOf w) = s' (M.A.cellOf a) := by
      have h1 := (M.inside_iff hs' _).1 hw'
      have h2 := (M.inside_iff hs' _).1 hin
      generalize s' (M.A.cellOf w) = u at *
      generalize s' (M.A.cellOf a) = v at *
      generalize s' M.z = t at *
      revert u v t; decide
    rcases eq_or_eq_α_of_segmentOf (digon_side_run hD hs' hw hgs) with h | h
    · apply hxC
      rw [h, ← hφφ, M.A.φ_apply, M.A.crossingOf_σ]
      have := M.A.mem_curves_crossingOf (M.A.α (M.A.φ a)); rwa [M.A.curve_α] at this
    · apply hxC
      rw [h, ← M.A.crossingOf_σ, ← M.A.φ_apply]; exact M.A.mem_curves_crossingOf (M.A.φ a)

/-- After zipping the lens `int C ∩ ext C'` (FROS: "expand `C'` until `C` and `C'` are parallel")
the digon is still there and `C`, `C'` are parallel. -/
theorem par_of_zipping (M : Marked n D) {a : D} (hD : M.A.IsDigon (M.A.cellOf a))
    (hz : M.A.cellOf a ≠ M.z) (hout : ¬ M.Inside (M.A.curve a) (M.A.cellOf a))
    (h : M.A.curve (M.A.φ a) ≠ M.A.curve a) {N : Marked n D}
    (hN : Relation.ReflTransGen (Marked.LensFlip h False True) M N)
    (hv : ∀ x, ¬ (N.twoLens h False True).IsVertex x) :
    N.Par (M.A.curve a) (M.A.curve (M.A.φ a)) :=
  par_of_zipping' M hD hout (stuck_digon M hD hz hout).1 h hN hv

/-- Every arrangement of two curves is cylindrical (the cell across a side of the marked cell,
then across its side on the other curve). -/
theorem cylindrical_of_two (M : Marked n D) (hn : n = 2) : M.Cylindrical := by
  obtain ⟨y, hy⟩ := M.z.exists_mk
  change M.A.cellOf y = M.z at hy
  set y₁ := M.A.α y
  set y₂ := M.A.φ y₁
  have hc1 : M.A.curve y₁ = M.A.curve y := M.A.curve_α y
  have h12 : M.A.curve y₂ ≠ M.A.curve y := by rw [← hc1]; exact M.A.curve_φ_ne y₁
  have hf₁ : M.A.cellOf y₂ = M.A.cellOf y₁ := M.A.cellOf_φ y₁
  refine ⟨M.A.cellOf (M.A.α y₂), fun C => ?_⟩
  have hz : ¬ M.Inside C (M.A.cellOf y) := by rw [hy]; exact M.not_inside_z C
  have e1 := M.inside_α C y
  have e2 := M.inside_α C y₂
  rw [hf₁] at e2
  have hC : C = M.A.curve y ∨ C = M.A.curve y₂ := by
    by_cases h : C = M.A.curve y
    · exact Or.inl h
    · right
      apply Fin.ext
      have := C.isLt; have := (M.A.curve y).isLt; have := (M.A.curve y₂).isLt
      have h' : (M.A.curve y₂).val ≠ (M.A.curve y).val := fun e => h12 (Fin.ext e)
      have h'' : C.val ≠ (M.A.curve y).val := fun e => h (Fin.ext e)
      omega
  rcases hC with rfl | rfl
  · rw [e2, e1]
    simp only [ne_eq, not_true_eq_false, iff_false, h12, not_false_eq_true, iff_true]
    exact hz
  · rw [e2, e1]
    simp only [ne_eq, not_true_eq_false, iff_false, Ne.symm h12, not_false_eq_true, iff_true]
    exact hz

/-- One expansion (FROS: "We show how to expand `C` using only triangle flips until it contains
`p`"): either the arrangement becomes cylindrical (digon case: zipping, deletion, induction,
mimicking), or `C` comes to contain a cell `p'` that is inside every curve containing `p`. -/
theorem expand_curve {m : ℕ} (hm : 2 ≤ m)
    (IH : ∀ (D' : Type u) [Fintype D'] [DecidableEq D'] (M' : Marked m D'),
      ∃ N', Reach M' N' ∧ N'.Cylindrical)
    (C : Fin (m + 1)) :
    ∀ (k : ℕ) (M : Marked (m + 1) D) (p : M.A.Cell), Fintype.card D - M.numInside C = k →
      ¬ M.Inside C p →
      (∃ N, Reach M N ∧ N.Cylindrical) ∨
        ∃ (N : Marked (m + 1) D) (p' : N.A.Cell), Reach M N ∧
          (∀ C', M.Inside C' p → N.Inside C' p') ∧ N.Inside C p' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M p hk hp
  -- `p` has a side on `C`: move to the cell across
  by_cases hside : M.HasSideOn C p
  · obtain ⟨y, hy, hyC⟩ := hside
    rw [Orbit.mem_darts] at hy
    change M.A.cellOf y = p at hy
    refine Or.inr ⟨M, M.A.cellOf (M.A.α y), Relation.ReflTransGen.refl, fun C' hC' => ?_, ?_⟩
    · rw [M.inside_α C' y, hy]
      by_cases h : C' = C
      · subst h; exact absurd hC' hp
      · simp only [hC', true_iff]; rw [hyC]; exact Ne.symm h
    · rw [M.inside_α C y, hy]; simp [hp, hyC]
  obtain ⟨s, hs⟩ := M.A.exists_isSide C
  obtain ⟨g, hgz, hgs, ⟨e, he, heC⟩, hdt⟩ := M.A.sweepFirstMove C s hs M.z
  rw [Orbit.mem_darts] at he
  change M.A.cellOf e = g at he
  subst he
  have hgout : ¬ M.Inside C (M.A.cellOf e) := by rw [M.inside_iff hs, hgs]; exact fun h => h rfl
  rcases hdt with hD | hT
  · -- the digon case
    left
    obtain ⟨hin, htr⟩ := stuck_digon M hD hgz (by rw [heC]; exact hgout)
    have hne : M.A.curve (M.A.φ e) ≠ M.A.curve e := M.A.curve_φ_ne e
    have hzQ : ∀ N : Marked (m + 1) D, ¬ N.TwoQ (M.A.curve (M.A.φ e)) (M.A.curve e) False True N.z :=
      fun N h => N.not_inside_z _ (h.2.2 trivial)
    obtain ⟨N, hN, hv, -⟩ := M.zipping hne False True (hzQ M) htr
    have hpar := par_of_zipping M hD hgz (by rw [heC]; exact hgout) hne hN hv
    have hNr : Reach M N := by
      clear hv hpar
      induction hN with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hs' ihN => exact ihN.tail (Marked.LensFlip.flipStep (hzQ _) hs')
    obtain ⟨N', hrel⟩ := exists_mimicRel hm N hpar
    obtain ⟨N'', hr'', hc''⟩ := IH _ N'
    obtain ⟨N₃, hr₃, hrel₃⟩ := mimic_reach hrel hr''
    exact ⟨N₃, hNr.trans hr₃, hrel₃.cylindrical hc''⟩
  · -- the triangle case: flip it, `C` gets one more crossing inside
    have hpg : p ≠ M.A.cellOf e := fun h => hside ⟨e, by rw [h]; exact Orbit.mem_darts.2 rfl, heC⟩
    have hlt := expand_triangle M hT hgz hgout heC
    have hle : (M.flip e hT).numInside C ≤ Fintype.card D := by
      unfold Marked.numInside; exact card_le_univ _
    have hp' : ¬ (M.flip e hT).Inside C (Arrangement.flipCellEquiv hT p) := by
      rw [flip_inside M hT hgz]; tauto
    rcases ih _ (by omega) (M.flip e hT) _ rfl hp' with h | ⟨N, p', hN, hN1, hN2⟩
    · obtain ⟨N, hN, hc⟩ := h
      exact Or.inl ⟨N, (Relation.ReflTransGen.single ⟨e, hT, hgz, rfl⟩).trans hN, hc⟩
    · refine Or.inr ⟨N, p', (Relation.ReflTransGen.single ⟨e, hT, hgz, rfl⟩).trans hN,
        fun C' hC' => hN1 C' ?_, hN2⟩
      rw [flip_inside M hT hgz]; tauto

/-- **FROS Theorem 3, first part**: every intersecting arrangement can be transformed into a
cylindrical arrangement by a finite sequence of triangle flips. -/
theorem reach_cylindrical (M : Marked n D) : ∃ N, Reach M N ∧ N.Cylindrical := by
  induction n using Nat.strong_induction_on generalizing D with
  | _ n ihn =>
  have hn2 := M.A.two_le_n
  rcases Nat.lt_or_ge n 3 with hn | hn
  · exact ⟨M, Relation.ReflTransGen.refl, cylindrical_of_two M (by omega)⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have IH : ∀ (D' : Type u) [Fintype D'] [DecidableEq D'] (M' : Marked m D'),
      ∃ N', Reach M' N' ∧ N'.Cylindrical := fun D' _ _ M' => ihn m (by omega) M'
  classical
  -- the outer loop: the number of curves not containing the tracked cell `p`
  suffices key : ∀ (k : ℕ) (M : Marked (m + 1) D) (p : M.A.Cell),
      (univ.filter (fun C => ¬ M.Inside C p)).card = k → ∃ N, Reach M N ∧ N.Cylindrical from
    key _ M M.z rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro M p hk
  by_cases hall : ∀ C, M.Inside C p
  · exact ⟨M, Relation.ReflTransGen.refl, p, hall⟩
  push Not at hall
  obtain ⟨C, hC⟩ := hall
  rcases expand_curve (by omega) IH C _ M p rfl hC with h | ⟨N, p', hN, hN1, hN2⟩
  · exact h
  · have hlt : (univ.filter (fun C => ¬ N.Inside C p')).card < k := by
      rw [← hk]
      apply card_lt_card
      refine ⟨fun C' hC' => ?_, fun h => ?_⟩
      · simp only [mem_filter, mem_univ, true_and] at hC' ⊢
        exact fun h => hC' (hN1 C' h)
      · have := @h C (by simp only [mem_filter, mem_univ, true_and]; exact hC)
        simp only [mem_filter, mem_univ, true_and] at this
        exact this hN2
    obtain ⟨N', hN', hc⟩ := ihk _ hlt N p' rfl
    exact ⟨N', hN.trans hN', hc⟩

end Pca.FlipGraph
