/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The sweep (`doc/pca/great.md` 4.3-4.4)

Fix the frame curve `c0` (the doubled curve) and the new curve `L`. While the cell `f₂` is not
passed, the pair of curves of a corner `x` of `f₂` (off `c0`) is unswept: the crossing of the pair
on the `H` side of `c0` is on side `N` of `L`. The quarter lemma gives a triangle with a side on
`L` in that quarter; its antipodal flip sweeps exactly its own pair. When the swept pair is the
pair of `x`, the crossing `x` is the old corner of the triangle or of its antipode, and `f₂`
becomes passed. The number of unswept pairs decreases, so the process ends.
-/
import Pca.Great.Swp_Aux

open Equiv Finset

namespace Pca.Great

variable {D D' : Type*} [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] {n : ℕ}
  {A : Arrangement n D} {ι : D → D'}

open Classical in
/-- The unswept ordered pairs. -/
noncomputable def unswept {B : Arrangement (n + 1) D'} (F : Frame B) (N : ZMod 2) :
    Finset (Fin (n + 1) × Fin (n + 1)) :=
  univ.filter (fun p => p.1 ≠ p.2 ∧ p.1 ≠ F.c0 ∧ p.2 ≠ F.c0 ∧ p.1 ≠ Fin.last n ∧
    p.2 ≠ Fin.last n ∧ (F.Neg (Fin.last n) p.1 p.2 ↔ N = 0))

theorem zmod2_eq_of_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  revert a b; decide

/-- The `H`-crossing of a pair is on side `N` of `L` iff the pair is unswept. -/
theorem neg_iff_side {B : Arrangement (n + 1) D'} (F : Frame B) (hB : B.IsGreat)
    {b c : Fin (n + 1)} (hb : b ≠ F.c0) (hc : c ≠ F.c0) (hbc : b ≠ c) {L : Fin (n + 1)}
    (hLb : L ≠ b) (hLc : L ≠ c) {x : B.Crossing}
    (hx : Arrangement.Crossing.curves B x = {b, c}) (hs : B.crossSide F.s0 x = 1) (N : ZMod 2) :
    (F.Neg L b c ↔ N = 0) ↔ B.crossSide (F.sR L) x = N := by
  rw [F.neg_iff' hB hb hc hbc hx hs]
  constructor
  · intro h; exact zmod2_eq_of_iff h
  · rintro rfl; rfl

end Pca.Great
