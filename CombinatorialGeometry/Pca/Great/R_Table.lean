/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: the rotation table of a great arrangement in frame coordinates (`doc/pca/great.md` 3.4)

With the base darts `β0` (on `c0`) and `β e` (on the chords), `σ` in coordinates is an explicit
function of the frame data: the positions `p` on `c0`, the chord at a position of `c0`, the curve
at a position of a chord, and the positions `hpos` (`tab_spec`).
-/
import Pca.Great.Coord
import Pca.Great.R_Reach

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- The data a rotation table is computed from. -/
structure FData (n : ℕ) where
  c0 : Fin n
  p : Fin n → ℕ
  hp : Fin n → Fin n → ℕ
  chordAt : ℕ → Fin n
  curveAt : Fin n → ℕ → Fin n

/-- The rotation table from frame data. -/
def FData.tab (X : FData n) (c : Fin n) (k : ℕ) : Fin n × ℕ × Bool :=
  if c = X.c0 then
    (if k < n - 1 then (X.chordAt k, 0, false) else (X.chordAt (k - (n - 1)), n - 1, true))
  else if k = 0 then (X.c0, X.p c, true)
  else if k < n - 1 then (X.curveAt c k, X.hp (X.curveAt c k) c, decide ¬ (X.p c < X.p (X.curveAt c k)))
  else if k = n - 1 then (X.c0, X.p c + (n - 1), false)
  else (X.curveAt c (k - (n - 1)), X.hp (X.curveAt c (k - (n - 1))) c + (n - 1),
    decide (X.p c < X.p (X.curveAt c (k - (n - 1)))))

theorem σ_ant (hA : A.IsGreat) (y : D) : A.σ (ant A y) = A.σ (A.σ (ant A (A.σ y))) := by
  rw [ant_σ hA]
  simp only [A.σ_σ_σ_σ]

theorem ant_code_false (A : Arrangement n D) (β : Fin n → D) (c : Fin n) (k : ℕ) :
    ant A (code A β c k false) = code A β c (k + (n - 1)) false := by
  simp only [code, Bool.false_eq_true, if_false, ant, ← Perm.mul_apply, ← pow_add, add_comm]

theorem ant_code (A : Arrangement n D) (β : Fin n → D) (c : Fin n) (k : ℕ) (b : Bool) :
    ant A (code A β c k b) = code A β c (k + (n - 1)) b := by
  cases b
  · exact ant_code_false A β c k
  · have h1 : code A β c k true = A.σ (A.σ (code A β c k false)) := by rw [code_σσ]; rfl
    have h2 : code A β c (k + (n - 1)) true = A.σ (A.σ (code A β c (k + (n - 1)) false)) := by
      rw [code_σσ]; rfl
    rw [h1, h2, ant_σσ, ant_code_false]

namespace Frame

variable (F : Frame A)

/-- Base darts on all curves: `β0` on `c0`, `β e` on the chords. -/
noncomputable def βf (c : Fin n) : D := if c = F.c0 then F.β0 else F.β c

open Classical in
/-- The frame data of `F`. -/
noncomputable def data : FData n where
  c0 := F.c0
  p := F.p
  hp := F.hpos
  chordAt k := if h : ∃ e, e ≠ F.c0 ∧ F.p e = k then Classical.choose h else F.c0
  curveAt c k := A.curve (A.σ ((A.straight ^ k) (F.β c)))

theorem data_c0 : F.data.c0 = F.c0 := rfl
theorem data_p : F.data.p = F.p := rfl
theorem data_hp : F.data.hp = F.hpos := rfl
theorem data_curveAt (c : Fin n) (k : ℕ) :
    F.data.curveAt c k = A.curve (A.σ ((A.straight ^ k) (F.β c))) := rfl

variable (hA : A.IsGreat)
include hA

theorem curve_βf (c : Fin n) : A.curve (F.βf c) = c := by
  unfold βf
  split_ifs with h
  · rw [F.curve_β0, h]
  · exact F.curve_β hA h

theorem chordAt_eq {e : Fin n} (he : e ≠ F.c0) : F.data.chordAt (F.p e) = e := by
  classical
  show (if h : ∃ e', e' ≠ F.c0 ∧ F.p e' = F.p e then Classical.choose h else F.c0) = e
  rw [dif_pos ⟨e, he, rfl⟩]
  have hs := Classical.choose_spec (⟨e, he, rfl⟩ : ∃ e', e' ≠ F.c0 ∧ F.p e' = F.p e)
  exact F.p_inj hA hs.1 he hs.2

/-- **The rotation table.** -/
theorem tab_spec (c : Fin n) {k : ℕ} (hk : k < 2 * (n - 1)) :
    A.σ (code A F.βf c k false) = code A F.βf (F.data.tab c k).1 (F.data.tab c k).2.1
      (F.data.tab c k).2.2 := by
  have hn := A.two_le_n
  have hβc0 : F.βf F.c0 = F.β0 := if_pos rfl
  have hβe : ∀ e, e ≠ F.c0 → F.βf e = F.β e := fun e he => if_neg he
  unfold FData.tab
  by_cases hc : c = F.c0
  · rw [if_pos (show c = F.data.c0 from hc)]
    subst hc
    change A.σ ((A.straight ^ k) (F.βf F.c0)) = _
    rw [hβc0]
    -- the chord at position `k` of `c0`
    set e := A.curve (A.σ ((A.straight ^ k) F.β0))
    have he0 : e ≠ F.c0 := by
      rw [← F.curve_β0, ← curve_straight_pow k F.β0]; exact A.isArrangement.curve_σ _
    have hk' := (F.mem_curves_c0_iff hA he0 hk).1 (A.mem_curves_crossingOf_σ _)
    have hpe := F.p_lt hA he0
    by_cases hkm : k < n - 1
    · rw [if_pos hkm]
      have hke : k = F.p e := by omega
      rw [hke, F.chordAt_eq hA he0]
      simp only [code, Bool.false_eq_true, if_false, pow_zero, Perm.one_apply, hβe e he0]
      rfl
    · rw [if_neg hkm]
      have hke : k = F.p e + (n - 1) := by omega
      rw [show k - (n - 1) = F.p e by omega, F.chordAt_eq hA he0, hke, add_comm,
        straight_pow_add]
      change A.σ (ant A ((A.straight ^ F.p e) F.β0)) = _
      rw [σ_ant hA]
      simp only [code, if_true, hβe e he0]
      rfl
  · rw [if_neg (show ¬ c = F.data.c0 from hc)]
    have hβ := hβe c hc
    change A.σ ((A.straight ^ k) (F.βf c)) = _
    rw [hβ]
    -- the crossings of the chord in `H`
    have hHc : ∀ k', 0 < k' → k' < n - 1 →
        A.σ ((A.straight ^ k') (F.β c)) = code A F.βf (F.data.curveAt c k')
          (F.hpos (F.data.curveAt c k') c) (decide ¬ (F.p c < F.p (F.data.curveAt c k'))) := by
      intro k' hk0 hkm
      rw [data_curveAt]
      set u := A.curve (A.σ ((A.straight ^ k') (F.β c)))
      have hcu : c ≠ u := by
        intro h
        apply A.isArrangement.curve_σ ((A.straight ^ k') (F.β c))
        rw [curve_straight_pow, F.curve_β hA hc]; exact h.symm
      have hu0 : u ≠ F.c0 := by
        intro h
        have := A.mem_curves_crossingOf_σ ((A.straight ^ k') (F.β c))
        rw [show A.curve (A.σ ((A.straight ^ k') (F.β c))) = F.c0 from h] at this
        rcases (F.c0_mem_chord_iff hA hc (k := k') (by omega)).1 this with h' | h' <;> omega
      have hku := F.hpos_unique hA hc hcu hkm (A.mem_curves_crossingOf_σ _)
      have hs := F.σ_hpos hA hc hu0 hcu
      rw [← hku] at hs
      rw [hs]
      unfold code
      rw [hβe u hu0]
      by_cases hp : F.p c < F.p u
      · simp [code, hp]
      · simp [code, hp]
    by_cases hk0 : k = 0
    · rw [if_pos hk0]
      subst hk0
      change A.σ (A.σ ((A.straight ^ F.p c) F.β0)) = A.σ (A.σ ((A.straight ^ F.p c) (F.βf F.c0)))
      rw [hβc0]
    rw [if_neg hk0]
    by_cases hkm : k < n - 1
    · rw [if_pos hkm]; exact hHc k (by omega) hkm
    rw [if_neg hkm]
    by_cases hkm' : k = n - 1
    · rw [if_pos hkm']
      subst hkm'
      change A.σ (ant A (F.β c)) = (A.straight ^ (F.p c + (n - 1))) (F.βf F.c0)
      rw [σ_ant hA, hβc0, β, ant_σσ, A.σ_σ_σ_σ, ant, add_comm, straight_pow_add]
    rw [if_neg hkm']
    have hk' : k = (n - 1) + (k - (n - 1)) := by omega
    have h1 := hHc (k - (n - 1)) (by omega) (by omega)
    conv_lhs => rw [hk', straight_pow_add]
    change A.σ (ant A ((A.straight ^ (k - (n - 1))) (F.β c))) = _
    rw [σ_ant hA, h1, ant_code, code_σσ]
    congr 1
    rw [data_p]
    by_cases hp : F.p c < F.p (F.data.curveAt c (k - (n - 1))) <;> simp [hp]

end Frame

end Pca.Great
