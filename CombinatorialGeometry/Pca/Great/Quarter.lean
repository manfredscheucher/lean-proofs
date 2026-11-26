/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The quarter lemma (`doc/pca/great.md` section 3.3)

Frame `F` (curve `c0`, side `H` = `s0 = 1`), a curve `ℓ ≠ c0`, a side `N` of `ℓ` (`sR ℓ = N`), and
a set `T` of curves with `c0, ℓ ∈ T`. The quarter `Q = H ∩ {sR ℓ = N}`. If `Q` contains a crossing
of two curves of `T \ {c0, ℓ}`, and every curve `t ∉ T` has all crossings in `H` of pairs of curves
of `T \ {c0}` on one side, then `Q` contains a triangle cell with a side on `ℓ` whose other two
sides lie on curves of `T \ {c0, ℓ}`. With `T = univ` the second hypothesis is empty: this is the
sweep of a lune by triangle flips (FROS Lemma 2, "zipping", for the lune of `ℓ` and `c0`).
-/
import Pca.Great.Q_Cell

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

namespace Frame

variable (F : Frame A) (hA : A.IsGreat)
include hA

theorem s0_cell {t : Fin n} (ht : t ≠ F.c0) {k : ℕ} (hk : k < n - 1) : F.s0 (F.cell t k) = 1 := by
  rw [F.s0_chord hA ht (by omega), if_pos hk]

theorem curves_hcross {a b : Fin n} (ha : a ≠ F.c0) (hb : b ≠ F.c0) (hab : a ≠ b) :
    Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ F.hpos a b) (F.β a))) = {a, b} :=
  A.curves_eq_pair (F.mem_curves_chord hA ha _) (F.hpos_spec hA ha hb hab).2.2 hab

/-- A crossing of two chords in `H` is their `H`-crossing. -/
theorem eq_hcross {a b : Fin n} (ha : a ≠ F.c0) (hb : b ≠ F.c0) (hab : a ≠ b) {d : D}
    (hcur : Arrangement.Crossing.curves A (A.crossingOf d) = {a, b}) (hs : F.s0 (A.cellOf d) = 1) :
    A.crossingOf d = A.crossingOf ((A.straight ^ F.hpos a b) (F.β a)) := by
  by_contra hne
  have := hA a b F.c0 hab ha hb F.s0 F.isSide_s0 _ _ hne hcur (F.curves_hcross hA ha hb hab)
    d (Orbit.mem_darts.2 rfl) _ (Orbit.mem_darts.2 rfl)
  exact this (hs.trans (F.s0_cell hA ha (F.hpos_spec hA ha hb hab).2.1).symm)

/-- Consecutive positions: no chord crosses strictly between. -/
theorem adj_of {t : Fin n} (ht : t ≠ F.c0) {a b : ℕ} (hab : a < b) (hb : b < n - 1)
    (hno : ∀ u, u ≠ F.c0 → u ≠ t → ¬ (a < F.hpos t u ∧ F.hpos t u < b)) : b = a + 1 := by
  by_contra hne
  set z := (A.straight ^ (a + 1)) (F.β t)
  have hz : A.curve z = t := by rw [curve_straight_pow, F.curve_β hA ht]
  have hu := A.mem_curves_crossingOf_σ z
  have hut : A.curve (A.σ z) ≠ t := by rw [← hz]; exact A.isArrangement.curve_σ z
  have hu0 : A.curve (A.σ z) ≠ F.c0 := by
    intro h
    rw [h] at hu
    rcases (F.c0_mem_chord_iff hA ht (k := a + 1) (by omega)).1 hu with h | h <;> omega
  have := F.hpos_unique hA ht (Ne.symm hut) (k := a + 1) (by omega) hu
  exact hno _ hu0 hut ⟨by omega, by omega⟩

variable {T : Finset (Fin n)}
  (hout : ∀ t, t ∉ T → ∀ d d' : D,
      F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d) →
      Arrangement.Crossing.curves A (A.crossingOf d) ⊆ T → F.s0 (A.cellOf d) = 1 →
      F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf d') →
      Arrangement.Crossing.curves A (A.crossingOf d') ⊆ T → F.s0 (A.cellOf d') = 1 →
      F.sR t (A.cellOf d) = F.sR t (A.cellOf d'))
include hout

/-- A curve outside `T` does not cross a chord of `T` between two crossings with chords of `T`. -/
theorem no_out_between {t a b u : Fin n} (ht : t ≠ F.c0) (ha : a ≠ F.c0) (hb : b ≠ F.c0)
    (hta : t ≠ a) (htb : t ≠ b) (htT : t ∈ T) (haT : a ∈ T) (hbT : b ∈ T) (hu : u ∉ T)
    (hu0 : u ≠ F.c0) (hut : u ≠ t) (hbet : Comb.Bet (F.hpos t u) (F.hpos t a) (F.hpos t b)) :
    False := by
  have ka := (F.hpos_spec hA ht ha hta).2.1
  have kb := (F.hpos_spec hA ht hb htb).2.1
  have hsub : ∀ c, c ∈ T → c ≠ F.c0 → t ≠ c →
      Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ F.hpos t c) (F.β t))) ⊆ T ∧
      F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ F.hpos t c) (F.β t))) :=
    fun c hcT hc0 htc => by
      rw [F.curves_hcross hA ht hc0 htc]
      refine ⟨by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption, ?_⟩
      simp only [mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm ht, Ne.symm hc0⟩
  have h := hout u hu _ _ (hsub a haT ha hta).2 (hsub a haT ha hta).1 (F.s0_cell hA ht ka)
    (hsub b hbT hb htb).2 (hsub b hbT hb htb).1 (F.s0_cell hA ht kb)
  rw [F.sR_chord hA hu0 ht hut ka, F.sR_chord hA hu0 ht hut kb] at h
  unfold Comb.Bet at hbet
  rcases hbet with hbet | hbet
  · rw [if_neg (show ¬ (F.hpos t u ≤ F.hpos t a) by omega),
      if_pos (show F.hpos t u ≤ F.hpos t b by omega)] at h
    simp at h
  · rw [if_pos (show F.hpos t u ≤ F.hpos t a by omega),
      if_neg (show ¬ (F.hpos t u ≤ F.hpos t b) by omega)] at h
    simp at h

end Frame

end Pca.Great
