/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The chords of a frame as a chord system (`doc/pca/great.md` section 3.3)
-/
import Pca.Great.Q_Geo

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

theorem zmod_iff {a b c d : Prop} [Decidable a] [Decidable b] [Decidable c] [Decidable d]
    (h : ((if a then 1 else 0 : ZMod 2) + if b then 1 else 0) =
      (if c then 1 else 0 : ZMod 2) + if d then 1 else 0) : ((a ↔ b) ↔ (c ↔ d)) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> by_cases hd : d <;>
    simp only [ha, hb, hc, hd, if_true, if_false] at h <;> first | (exact absurd h (by decide)) |
    simp [ha, hb, hc, hd]

theorem zmod_one_iff {a b : Prop} [Decidable a] [Decidable b] :
    ((if a then 1 else 0 : ZMod 2) + (if b then 1 else 0) = 1) ↔ ¬ (a ↔ b) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb] <;> decide

namespace Frame

variable (F : Frame A) (hA : A.IsGreat)

/-- The chords of the frame. -/
abbrev Ch (F : Frame A) := {e : Fin n // e ≠ F.c0}

/-- The cell of the chord dart at position `k` (the cell right of `straight^k (β t)`). -/
noncomputable abbrev cell (t : Fin n) (k : ℕ) : A.Cell := A.cellOf ((A.straight ^ k) (F.β t))


/-- Two cells at the same crossing not on `e` are on the same side of `e`. -/
theorem side_same_crossing {e : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide e s) {y z : D}
    (h : A.crossingOf y = A.crossingOf z)
    (he : e ∉ Arrangement.Crossing.curves A (A.crossingOf y)) :
    s (A.cellOf y) = s (A.cellOf z) := by
  rw [← crossSide_eq hs he, ← crossSide_eq hs (h ▸ he), h]

include hA

/-- The chord system of the frame. -/
noncomputable def chordSys : Comb.ChordSys F.Ch where
  P e := F.p e.1
  H e f := F.hpos e.1 f.1
  m := n - 1
  P_inj e f h := Subtype.ext (F.p_inj hA e.2 f.2 h)
  H_inj e f g hf hg h := by
    have hf' : f.1 ≠ e.1 := fun h' => hf (Subtype.ext h')
    have hg' : g.1 ≠ e.1 := fun h' => hg (Subtype.ext h')
    obtain ⟨-, -, h1⟩ := F.hpos_spec hA e.2 f.2 (Ne.symm hf')
    obtain ⟨-, -, h2⟩ := F.hpos_spec hA e.2 g.2 (Ne.symm hg')
    have he := F.mem_curves_chord hA e.2 (F.hpos e.1 f.1)
    change F.hpos e.1 f.1 = F.hpos e.1 g.1 at h
    rw [← h] at h2
    rw [A.curves_eq_pair he h1 (Ne.symm hf'), mem_insert, mem_singleton] at h2
    rcases h2 with h2 | h2
    · exact absurd h2 hg'
    · exact Subtype.ext h2.symm
  H_pos e f hf := (F.hpos_spec hA e.2 f.2 (fun h => hf (Subtype.ext h).symm)).1
  H_lt e f hf := (F.hpos_spec hA e.2 f.2 (fun h => hf (Subtype.ext h).symm)).2.1
  rel e f g hef heg hfg := by
    have hef' : e.1 ≠ f.1 := fun h => hef (Subtype.ext h)
    have heg' : e.1 ≠ g.1 := fun h => heg (Subtype.ext h)
    have hfg' : f.1 ≠ g.1 := fun h => hfg (Subtype.ext h)
    have h1 := F.sR_chord hA e.2 f.2 hef' (k := F.hpos f.1 g.1)
      (F.hpos_spec hA f.2 g.2 hfg').2.1
    have h2 := F.sR_chord hA e.2 g.2 heg' (k := F.hpos g.1 f.1)
      (F.hpos_spec hA g.2 f.2 (Ne.symm hfg')).2.1
    have hx := F.crossingOf_hpos hA f.2 g.2 hfg'
    have hne : e.1 ∉ Arrangement.Crossing.curves A
        (A.crossingOf ((A.straight ^ F.hpos f.1 g.1) (F.β f.1))) := by
      rw [A.curves_eq_pair (F.mem_curves_chord hA f.2 _) (F.hpos_spec hA f.2 g.2 hfg').2.2 hfg',
        mem_insert, mem_singleton, not_or]
      exact ⟨hef', heg'⟩
    have := side_same_crossing (F.isSide_sR e.1) hx hne
    rw [h1, h2] at this
    exact zmod_iff this

/-- The side `Rt` of the chord system is the side function `sR`. -/
theorem rt_iff {x t : F.Ch} (hxt : x ≠ t) {k : ℕ} (hk : k < n - 1) :
    (F.chordSys hA).Rt x t k ↔ F.sR x.1 (F.cell t.1 k) = 1 := by
  rw [F.sR_chord hA x.2 t.2 (fun h => hxt (Subtype.ext h)) hk, zmod_one_iff]
  rfl

end Frame

end Pca.Great
