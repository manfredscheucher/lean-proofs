/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Ringel: triple signs and the potential (`doc/pca/great.md` section 3.4)

For chords `a, b, c` (curves `≠ c0`), the triple is **negative** (`Neg`) if the crossing of `b, c`
in `H` lies on side `0` of `a`. For `p a < p b < p c` this is the "−" orientation; the canonical
form has no negative triple. The potential `pot` counts the negative sorted triples. An antipodal
flip of a triangle in `H` not touching `c0` changes exactly the sign of its own triple
(`pot_flip`).
-/
import Pca.Great.R_Flip
import Pca.Great.Q_Final

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

namespace Frame

variable (F : Frame A)

/-- The triple `a; b, c` is negative: the crossing of `b, c` in `H` is on side `0` of `a`. -/
def Neg (a b c : Fin n) : Prop :=
  ∀ x : A.Crossing, Arrangement.Crossing.curves A x = {b, c} → A.crossSide F.s0 x = 1 →
    A.crossSide (F.sR a) x = 0

/-- A negative sorted triple of chords. -/
def Bad (t : Fin n × Fin n × Fin n) : Prop :=
  t.1 ≠ F.c0 ∧ t.2.1 ≠ F.c0 ∧ t.2.2 ≠ F.c0 ∧ F.p t.1 < F.p t.2.1 ∧ F.p t.2.1 < F.p t.2.2 ∧
    F.Neg t.1 t.2.1 t.2.2

open Classical in
/-- The potential: the number of negative sorted triples. -/
noncomputable def pot : ℕ := (univ.filter F.Bad).card

variable (hA : A.IsGreat)
include hA

/-- The crossing of two chords in `H` is unique. -/
theorem hcross_unique {b c : Fin n} (hb : b ≠ F.c0) (hc : c ≠ F.c0) (hbc : b ≠ c)
    {x : A.Crossing} (hx : Arrangement.Crossing.curves A x = {b, c})
    (hs : A.crossSide F.s0 x = 1) :
    x = A.crossingOf ((A.straight ^ F.hpos b c) (F.β b)) := by
  obtain ⟨y, rfl⟩ := x.exists_mk
  have hy : F.c0 ∉ Arrangement.Crossing.curves A (A.crossingOf y) := by
    change Arrangement.Crossing.curves A (A.crossingOf y) = _ at hx
    rw [hx, mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hb, Ne.symm hc⟩
  change A.crossSide F.s0 (A.crossingOf y) = 1 at hs
  rw [crossSide_eq F.isSide_s0 hy] at hs
  exact F.eq_hcross hA hb hc hbc hx hs

theorem neg_iff {a b c : Fin n} (ha : a ≠ F.c0) (hb : b ≠ F.c0) (hc : c ≠ F.c0) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    F.Neg a b c ↔ A.crossSide (F.sR a) (A.crossingOf ((A.straight ^ F.hpos b c) (F.β b))) = 0 := by
  constructor
  · intro h
    refine h _ (F.curves_hcross hA hb hc hbc) ?_
    have hn0 : F.c0 ∉ Arrangement.Crossing.curves A
        (A.crossingOf ((A.straight ^ F.hpos b c) (F.β b))) := by
      rw [F.curves_hcross hA hb hc hbc, mem_insert, mem_singleton, not_or]
      exact ⟨Ne.symm hb, Ne.symm hc⟩
    rw [crossSide_eq F.isSide_s0 hn0]
    exact F.s0_cell hA hb (F.hpos_spec hA hb hc hbc).2.1
  · intro h x hx hs
    rw [F.hcross_unique hA hb hc hbc hx hs]; exact h

end Frame

end Pca.Great
