/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import NonCirc.Plane

/-! # Fingerprints and plane circle realizations (definitions a human must check)

A fingerprint (rusty-arrangements convention, as in `Pca/Fingerprint.lean`, same
representation) is a list of lists of signed circle labels: the list number `m - 1` is the
cyclic sequence of crossings along circle `m` (`m = 1..n`); entry `+d` means that circle `d`
crosses `m` from the right of `m` to its left, `-d` from left to right. The same crossing is
`+d` in the list of `m` and `-m` in the list of `d`.

Crossing labels: `(j, k, s)` with `j < k` and `s = ±1`; `(j, k, 1)` is the crossing `p⁺_jk` that
appears as `+k` in the list of `j` (and as `-j` in the list of `k`), `(j, k, -1)` the other one.

Everything used by the statement `IsCircleRealization` is defined in this file:
`lst`, `entry`, `sideVia`, `side`, `label`, `order`, `IsLabel`, `IsCircleRealization`, and from
`NonCirc/Plane.lean`: `dist2`, `det3`.
-/

namespace NonCirc

/-- A fingerprint: for every circle the cyclic list of signed (1-based) circle labels. -/
abbrev Fingerprint := List (List ℤ)

namespace Fingerprint

variable (F : Fingerprint)

/-- The number of circles. -/
def n : ℕ := F.length

/-- The list of circle `m` (circles are numbered from `1`). -/
def lst (m : ℕ) : List ℤ := F.getD (m - 1) []

/-- The entry of the crossing `(j, k, s)` in the list of circle `m ∈ {j, k}`. -/
def entry (j k : ℕ) (s : ℤ) (m : ℕ) : ℤ := if m = j then s * k else -(s * j)

/-- The side of the crossing `(j, k, s)` with respect to circle `m`, read along the list of
circle `d ∈ {j, k}`: walk the list of `d` backwards (cyclically) from the crossing to the last
entry `±m`; `-m` means that `d` has just crossed `m` from right to left, so the crossing is to
the left of `m` (`1`); `+m` means right (`-1`); `0` if there is no such entry. -/
def sideVia (d j k : ℕ) (s : ℤ) (m : ℕ) : ℤ :=
  let L := F.lst d
  let t := L.idxOf (entry j k s d)
  match ((L.take t).reverse ++ (L.drop (t + 1)).reverse).find? (fun e => e.natAbs == m) with
  | some e => if e < 0 then 1 else -1
  | none => 0

/-- The side of the crossing `(j, k, s)` with respect to circle `m` (read along circle `j`;
`WellFormed` checks that circle `k` gives the same value). -/
def side (j k : ℕ) (s : ℤ) (m : ℕ) : ℤ := F.sideVia j j k s m

/-- The crossing label of the entry `e` of the list of circle `m`. -/
def label (m : ℕ) (e : ℤ) : ℕ × ℕ × ℤ :=
  if m < e.natAbs then (m, e.natAbs, e.sign) else (e.natAbs, m, -e.sign)

/-- The crossings along circle `m`, in the order of the fingerprint. -/
def order (m : ℕ) : List (ℕ × ℕ × ℤ) := (F.lst m).map (label m)

/-- A valid crossing label. -/
def IsLabel (j k : ℕ) (s : ℤ) : Prop := 1 ≤ j ∧ j < k ∧ k ≤ F.n ∧ (s = 1 ∨ s = -1)

instance (j k : ℕ) (s : ℤ) : Decidable (F.IsLabel j k s) := by unfold IsLabel; infer_instance

/-- The plane point of a crossing label. -/
def pt (P : ℕ → ℕ → ℤ → ℝ × ℝ) (l : ℕ × ℕ × ℤ) : ℝ × ℝ := P l.1 l.2.1 l.2.2

/-- A circle realization in the plane of the fingerprint `F`:

* circle `i` (`1 ≤ i ≤ n`) has centre `c i`, radius `r i > 0` and orientation `ε i = ±1`
  (`ε i = 1`: counterclockwise, so the left side of circle `i` is its interior);
* every two circles cross;
* `P j k s` lies on circles `j` and `k`, for every crossing label;
* sides: `P j k s` is to the left of circle `m ∉ {j, k}` if `side = 1` and to the right if
  `side = -1`, where left = inside if `ε m = 1` and outside if `ε m = -1`;
* cyclic order: three crossings that appear in this order in the list of circle `m` are
  counterclockwise if `ε m = 1` and clockwise if `ε m = -1` (the list order is the order
  of traversal, and a circle traversed counterclockwise has its interior on the left). -/
structure IsCircleRealization (c : ℕ → ℝ × ℝ) (r ε : ℕ → ℝ) (P : ℕ → ℕ → ℤ → ℝ × ℝ) :
    Prop where
  radius_pos : ∀ i, 1 ≤ i → i ≤ F.n → 0 < r i
  orientation : ∀ i, 1 ≤ i → i ≤ F.n → ε i = 1 ∨ ε i = -1
  cross : ∀ i j, 1 ≤ i → i < j → j ≤ F.n →
    (r i - r j) ^ 2 < dist2 (c i) (c j) ∧ dist2 (c i) (c j) < (r i + r j) ^ 2
  on_circles : ∀ j k s, F.IsLabel j k s →
    dist2 (P j k s) (c j) = r j ^ 2 ∧ dist2 (P j k s) (c k) = r k ^ 2
  sides : ∀ j k s m, F.IsLabel j k s → 1 ≤ m → m ≤ F.n → m ≠ j → m ≠ k →
    0 < (F.side j k s m : ℝ) * (ε m * (r m ^ 2 - dist2 (P j k s) (c m)))
  cyclic : ∀ m i₁ i₂ i₃, 1 ≤ m → m ≤ F.n → i₁ < i₂ → i₂ < i₃ → i₃ < (F.order m).length →
    0 < ε m * det3 (pt P ((F.order m).getD i₁ (0, 0, 0))) (pt P ((F.order m).getD i₂ (0, 0, 0)))
      (pt P ((F.order m).getD i₃ (0, 0, 0)))

/-- Well-formedness of a fingerprint (checked by `decide` for each concrete fingerprint, so the
hypotheses of `IsCircleRealization` are not contradictory by themselves): every list has
`2(n-1)` entries, every other circle occurs once with each sign, and every side is `±1` and the
same when read along both circles of the crossing. -/
def WellFormed : Bool :=
  (List.range F.n).all fun m0 =>
    let m := m0 + 1
    (F.lst m).length == 2 * (F.n - 1) &&
    (List.range F.n).all fun d0 =>
      let d := d0 + 1
      if d == m then !(F.lst m).contains (d : ℤ) && !(F.lst m).contains (-(d : ℤ))
      else (F.lst m).count (d : ℤ) == 1 && (F.lst m).count (-(d : ℤ)) == 1 &&
        (if m < d then
          [1, -1].all fun s => (List.range F.n).all fun q0 =>
            let q := q0 + 1
            q == m || q == d ||
              ((F.side m d s q == 1 || F.side m d s q == -1) && F.side m d s q == F.sideVia d m d s q)
        else true)

end Fingerprint

end NonCirc
