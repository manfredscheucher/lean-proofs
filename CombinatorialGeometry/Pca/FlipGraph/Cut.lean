/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): cuts along even sets of segments (Jordan in graph language)

`exists_cut`: an even set `E` of segments (every crossing is the end of an even number of darts
with segment in `E`, e.g. the segments of a closed walk) cuts the cells into two classes: there
is `r` changing exactly across the segments of `E` (FROS use the Jordan curve theorem for "the
region bounded by"; in the dart model this is `Sweep.SConf.exists_cut`, transported along
`sconfOf`). `cut_straight`: along a straight walk, `r` changes exactly when the walk passes a
segment of `E` at a crossing. These are the tools for the region arguments of FROS (Claims A and
B of Lemma 2, nesting of arcs).
-/
import Pca.FlipGraph.SConfOf
import Pca.FlipGraph.Walk

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace Cut

variable (A : Arrangement n D)

/-- `r` cuts the cells along `E`. -/
def IsCut (E : Finset A.Segment) (r : A.Cell → ZMod 2) : Prop :=
  ∀ y, r (A.cellOf y) + r (A.cellOf (A.α y)) = if A.segmentOf y ∈ E then 1 else 0

/-- `E` is even at every crossing. -/
def IsEven (E : Finset A.Segment) : Prop :=
  ∀ x : A.Crossing, Even (x.darts.filter (fun y => A.segmentOf y ∈ E)).card

/-- **Jordan (cut form)**: an even set of segments is a cut. -/
theorem exists_cut (E : Finset A.Segment) (hE : IsEven A E) : ∃ r, IsCut A E r := by
  have hn := A.two_le_n
  obtain ⟨s, hs⟩ := A.exists_isSide ⟨0, by omega⟩
  obtain ⟨y, hy, hyb⟩ := A.exists_dart_on_side hs 0
  exact Sweep.SConf.exists_cut (Γ := sconfOf A ⟨0, by omega⟩ s hs 0 y hy hyb) E hE

variable {A}

theorem cut_α {E : Finset A.Segment} {r : A.Cell → ZMod 2} (hr : IsCut A E r) (y : D) :
    r (A.cellOf (A.α y)) = r (A.cellOf y) + if A.segmentOf y ∈ E then 1 else 0 :=
  Arrangement.zmod2_eq_add_of_add_eq (hr y)

/-- Along a straight walk the cut changes exactly at the segments of `E` passed at the end
crossing (the segment of `σ (α y)`). -/
theorem cut_straight {E : Finset A.Segment} {r : A.Cell → ZMod 2} (hr : IsCut A E r) (y : D) :
    r (A.cellOf (A.straight y)) =
      r (A.cellOf y) + if A.segmentOf (A.σ (A.α y)) ∈ E then 1 else 0 := by
  rw [A.straight_apply, A.cellOf_σ, cut_α hr, A.cellOf_σ, A.α_α]

/-- The value of the cut along a straight walk: the start value plus the number of segments of
`E` passed so far. -/
theorem cut_pow {E : Finset A.Segment} {r : A.Cell → ZMod 2} (hr : IsCut A E r) (y : D) (k : ℕ) :
    r (A.cellOf ((A.straight ^ k) y)) = r (A.cellOf y) +
      ∑ i ∈ range k,
        if A.segmentOf (A.σ (A.α ((A.straight ^ i) y))) ∈ E then (1 : ZMod 2) else 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Walk.pow_succ_apply, cut_straight hr, ih, sum_range_succ, add_assoc]

end Cut

end Pca.FlipGraph
