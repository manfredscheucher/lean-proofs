/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The quarter lemma: three consecutive crossings bound a triangle (`doc/pca/great.md` 3.3)
-/
import Pca.Great.Q_Sys

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

namespace Frame

variable (F : Frame A) (hA : A.IsGreat)
include hA

/-- The other curve at a crossing of a chord. -/
theorem curve_at {t u : Fin n} (ht : t ≠ F.c0) (htu : t ≠ u) {k : ℕ} {z : D}
    (hu : u ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ k) (F.β t))))
    (hz : A.crossingOf z = A.crossingOf ((A.straight ^ k) (F.β t))) (hzt : A.curve z ≠ t) :
    A.curve z = u := by
  have hm := A.mem_curves_crossingOf z
  rw [hz, A.curves_eq_pair (F.mem_curves_chord hA ht k) hu htu, mem_insert, mem_singleton] at hm
  rcases hm with hm | hm
  · exact absurd hm hzt
  · exact hm

theorem side_bwd {x : Fin n} {z : D} (hzx : A.curve z ≠ x) (hσ : A.curve (A.σ z) = x) :
    F.sR x (A.cellOf (A.σ (A.σ z))) = F.sR x (A.cellOf z) + 1 := by
  rw [A.side_σσ (F.isSide_sR x), if_neg hzx, if_pos hσ, add_zero]

/-- **Triangle recognition.** A dart `d` on `ℓ` from the crossing with `w'` to the crossing with `w`
whose cell lies on the side of the crossing `v` of `w, w'`, where `v` is next to both crossings
along `w` and `w'`, bounds a triangle. -/
theorem tri_cell {ℓ w w' : Fin n} (hℓ : ℓ ≠ F.c0) (hw : w ≠ F.c0) (hw' : w' ≠ F.c0)
    (hℓw : ℓ ≠ w) (hℓw' : ℓ ≠ w') (hww' : w ≠ w') {d : D} (hd : A.curve d = ℓ)
    (h1 : A.crossingOf d = A.crossingOf ((A.straight ^ F.hpos w' ℓ) (F.β w')))
    (h2 : A.crossingOf (A.α d) = A.crossingOf ((A.straight ^ F.hpos w ℓ) (F.β w)))
    (hN : F.sR ℓ (A.cellOf d) = F.sR ℓ (F.cell w (F.hpos w w')))
    (adj1 : F.hpos w w' = F.hpos w ℓ + 1 ∨ F.hpos w w' + 1 = F.hpos w ℓ)
    (adj2 : F.hpos w' ℓ = F.hpos w' w + 1 ∨ F.hpos w' ℓ + 1 = F.hpos w' w) :
    A.IsTriangle (A.cellOf d) ∧ A.curve (A.φ d) = w ∧ A.curve (A.φ (A.φ d)) = w' := by
  have hn := A.two_le_n
  -- step 1: `φ d` is the dart of `w` at its crossing with `ℓ`, towards `v`
  set zf := (A.straight ^ F.hpos w ℓ) (F.β w)
  have hφx : A.crossingOf (A.φ d) = A.crossingOf zf := by
    show A.crossingOf (A.σ (A.α d)) = _; rw [A.crossingOf_σ, h2]
  have hxw : ℓ ∈ Arrangement.Crossing.curves A (A.crossingOf zf) := by
    rw [← F.crossingOf_hpos hA hℓ hw hℓw]; exact F.mem_curves_chord hA hℓ _
  have hcf : A.curve zf = w := by rw [curve_straight_pow, F.curve_β hA hw]
  have hφc : A.curve (A.φ d) = w := by
    have hm := A.mem_curves_crossingOf (A.φ d)
    rw [hφx, A.curves_eq_pair (F.mem_curves_chord hA hw _) hxw (Ne.symm hℓw), mem_insert,
      mem_singleton] at hm
    rcases hm with hm | hm
    · exact hm
    · exact absurd (hm.trans hd.symm) (A.curve_φ_ne d)
  have hσf : A.curve (A.σ zf) = ℓ := F.curve_at hA hw (Ne.symm hℓw) hxw (A.crossingOf_σ zf)
    (by rw [← hcf]; exact A.isArrangement.curve_σ zf)
  have sf := F.sR_chord hA hℓ hw hℓw (k := F.hpos w ℓ) (F.hpos_spec hA hw hℓ (Ne.symm hℓw)).2.1
  rw [if_pos le_rfl] at sf
  have sb := F.side_bwd hA (x := ℓ) (z := zf) (by rw [hcf]; exact Ne.symm hℓw) hσf
  have sv := F.sR_chord hA hℓ hw hℓw (k := F.hpos w w') (F.hpos_spec hA hw hw' hww').2.1
  have hφcell : A.cellOf (A.φ d) = A.cellOf d := A.cellOf_φ d
  -- the far end of `φ d` is `v`
  have hv : A.crossingOf (A.α (A.φ d)) = A.crossingOf ((A.straight ^ F.hpos w w') (F.β w)) := by
    rcases F.dart_on_chord hA hw hφx hφc with hz | hz
    · rcases adj1 with ha | ha
      · rw [hz, F.far_fwd hA, ha]
      · exfalso
        have := congrArg (F.sR ℓ) hφcell
        rw [hz, sf, hN, sv, if_neg (show ¬ (F.hpos w ℓ ≤ F.hpos w w') by omega)] at this
        simp at this
    · rcases adj1 with ha | ha
      · exfalso
        have := congrArg (F.sR ℓ) hφcell
        rw [hz, sb, sf, hN, sv, if_pos (show F.hpos w ℓ ≤ F.hpos w w' by omega)] at this
        have hz2 : ∀ a : ZMod 2, a + 1 + 1 ≠ a + 1 := by decide
        exact hz2 _ this
      · rw [hz, ← ha, F.far_bwd hA]
  -- step 2: `φ² d` is the dart of `w'` at `v`, towards the crossing with `ℓ`
  set yf := (A.straight ^ F.hpos w' w) (F.β w')
  have hv' : A.crossingOf (A.α (A.φ d)) = A.crossingOf yf := hv.trans (F.crossingOf_hpos hA hw hw' hww')
  have hφ2x : A.crossingOf (A.φ (A.φ d)) = A.crossingOf yf := by
    show A.crossingOf (A.σ (A.α _)) = _; rw [A.crossingOf_σ, hv']
  have hwv : w ∈ Arrangement.Crossing.curves A (A.crossingOf yf) := by
    rw [← F.crossingOf_hpos hA hw hw' hww']; exact F.mem_curves_chord hA hw _
  have hcyf : A.curve yf = w' := by rw [curve_straight_pow, F.curve_β hA hw']
  have hφ2c : A.curve (A.φ (A.φ d)) = w' := by
    have hm := A.mem_curves_crossingOf (A.φ (A.φ d))
    rw [hφ2x, A.curves_eq_pair (F.mem_curves_chord hA hw' _) hwv hww'.symm, mem_insert,
      mem_singleton] at hm
    rcases hm with hm | hm
    · exact hm
    · exact absurd (hm.trans hφc.symm) (A.curve_φ_ne _)
  have hσyf : A.curve (A.σ yf) = w := F.curve_at hA hw' (Ne.symm hww') hwv (A.crossingOf_σ yf)
    (by rw [← hcyf]; exact A.isArrangement.curve_σ yf)
  have tf := F.sR_chord hA hw hw' hww' (k := F.hpos w' w) (F.hpos_spec hA hw' hw hww'.symm).2.1
  rw [if_pos le_rfl] at tf
  have tb := F.side_bwd hA (x := w) (z := yf) (by rw [hcyf]; exact hww'.symm) hσyf
  have tℓ := F.sR_chord hA hw hw' hww' (k := F.hpos w' ℓ) (F.hpos_spec hA hw' hℓ hℓw'.symm).2.1
  have hxw' : w ∉ Arrangement.Crossing.curves A (A.crossingOf d) := by
    rw [h1, A.curves_eq_pair (F.mem_curves_chord hA hw' _)
      (by rw [← F.crossingOf_hpos hA hℓ hw' hℓw']; exact F.mem_curves_chord hA hℓ _) hℓw'.symm,
      mem_insert, mem_singleton, not_or]
    exact ⟨hww', hℓw.symm⟩
  have hdw : F.sR w (A.cellOf d) = F.sR w (F.cell w' (F.hpos w' ℓ)) :=
    side_same_crossing (F.isSide_sR w) h1 hxw'
  have hφ2cell : A.cellOf (A.φ (A.φ d)) = A.cellOf d := by rw [A.cellOf_φ, A.cellOf_φ]
  refine ⟨isTriangle_of_far_end ?_ (by rw [hφ2c, hd]; exact hℓw'.symm), hφc, hφ2c⟩
  rcases F.dart_on_chord hA hw' hφ2x hφ2c with hz | hz
  · rcases adj2 with ha | ha
    · rw [hz, F.far_fwd hA, ← ha, h1]
    · exfalso
      have := congrArg (F.sR w) hφ2cell
      rw [hz, tf, hdw, tℓ, if_neg (show ¬ (F.hpos w' w ≤ F.hpos w' ℓ) by omega)] at this
      simp at this
  · rcases adj2 with ha | ha
    · exfalso
      have := congrArg (F.sR w) hφ2cell
      rw [hz, tb, tf, hdw, tℓ, if_pos (show F.hpos w' w ≤ F.hpos w' ℓ by omega)] at this
      have hz2 : ∀ a : ZMod 2, a + 1 + 1 ≠ a + 1 := by decide
      exact hz2 _ this
    · rw [hz, ← ha, F.far_bwd hA, h1]

end Frame

end Pca.Great
