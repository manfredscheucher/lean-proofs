/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Arrangements from fingerprints (the format of rusty-arrangements)

A fingerprint lists, for every circle `c = 0, …, n-1`, the cyclic sequence of signed labels
of the circles crossing it: entry `+(d+1)` in the list of `c` means that `d` crosses `c` from
the right of `c` to its left, `-(d+1)` from left to right (rusty-arrangements, `doc/spec.md`,
"Fingerprint convention").

The dart encoding is the one of rusty-arrangements (`src/arrangement.rs`): the entries of all
lists are concatenated; the crossing at position `i` of the list of `c` has the global index
`k = offset c + i`, and the darts at this entry are `2k` (leaving the crossing forward along
`c`) and `2k + 1` (backward). With `p` the index of the same crossing in the list of the other
circle, the counter-clockwise order at the crossing is `2k, 2p, 2k+1, 2p+1` if the entry `e`
at `k` is positive and `2k, 2p+1, 2k+1, 2p` if it is negative. Hence
`σ (2k + dir) = 2p + (dir xor [e < 0])`, and `φ = σ ∘ α` is exactly
`Arrangement::face_successors` of rusty-arrangements.
-/
import Pca.Model

open Equiv

namespace Pca

/-- A fingerprint: for every circle the cyclic list of signed (1-based) circle labels. -/
abbrev Fingerprint := List (List ℤ)

namespace Fingerprint

variable (fp : Fingerprint)

/-- All entries, concatenated. -/
def entries : List ℤ := fp.flatten

/-- `offset c`: global index of the first entry of circle `c`. -/
def offset (c : ℕ) : ℕ := ((fp.take c).map List.length).sum

/-- The number of entries of circle `c`. -/
def len (c : ℕ) : ℕ := (fp.getD c []).length

/-- The number of darts (two per entry, i.e. four per crossing). -/
def numDarts : ℕ := 2 * fp.entries.length

/-- The (0-based) circle of a signed label. -/
def circleOfEntry (e : ℤ) : ℕ := e.natAbs - 1

/-- The circle whose list contains the global index `k`. -/
def circleOfIndex (k : ℕ) : ℕ :=
  ((List.range fp.length).filter (fun c => fp.offset (c + 1) ≤ k)).length

/-- The entry at global index `k`. -/
def entry (k : ℕ) : ℤ := fp.entries.getD k 0

/-- The global index of the same crossing in the list of the other circle: the entry
`-(sign e) * (c + 1)` in the list of `d`, where `e` is the entry at `k` (on circle `c`) and
`d` its circle (`sign_d(c) = - sign_c(d)`). -/
def partner (k : ℕ) : ℕ :=
  let c := fp.circleOfIndex k
  let e := fp.entry k
  let d := circleOfEntry e
  let target : ℤ := if 0 < e then -((c : ℤ) + 1) else (c : ℤ) + 1
  fp.offset d + (((fp.getD d []).idxOf target))

/-- The rotation `σ` on dart numbers. -/
def sigmaNat (a : ℕ) : ℕ :=
  let k := a / 2
  let dir := a % 2
  let flip := if fp.entry k < 0 then 1 else 0
  2 * fp.partner k + (if dir = flip then 0 else 1)

/-- The edge involution `α` on dart numbers. -/
def alphaNat (a : ℕ) : ℕ :=
  let k := a / 2
  let c := fp.circleOfIndex k
  let off := fp.offset c
  let l := fp.len c
  let i := k - off
  if a % 2 = 0 then 2 * (off + (i + 1) % l) + 1 else 2 * (off + (i + l - 1) % l)

/-- The curve (0-based circle) of a dart number. -/
def curveNat (a : ℕ) : ℕ := fp.circleOfIndex (a / 2)

/-- Well-formedness of the encoding for `n` circles and `m` darts. Besides the sizes, it rules
out every silent fallback of the definitions above (`getD` defaults, `idxOf` not finding the
label): every entry is a nonzero label of another circle, `partner` is an involution on the
entries, and the partner entry lies on the circle named by the entry, names the circle of the
entry, and has the opposite sign. Finally the tables of `σ`, `α` and `curve` stay in range (so
the reductions modulo `m` and `n` below are the identity). The arrangement axioms themselves
are checked on the resulting map. -/
def WellFormed (n m : ℕ) : Prop :=
  fp.length = n ∧ fp.numDarts = m ∧
    (∀ k < fp.entries.length,
      fp.entry k ≠ 0 ∧
      circleOfEntry (fp.entry k) < n ∧
      circleOfEntry (fp.entry k) ≠ fp.circleOfIndex k ∧
      fp.partner k < fp.entries.length ∧
      fp.partner (fp.partner k) = k ∧
      fp.circleOfIndex (fp.partner k) = circleOfEntry (fp.entry k) ∧
      circleOfEntry (fp.entry (fp.partner k)) = fp.circleOfIndex k ∧
      (0 < fp.entry (fp.partner k) ↔ fp.entry k < 0)) ∧
    ∀ a < m, fp.sigmaNat a < m ∧ fp.alphaNat a < m ∧ fp.curveNat a < n

instance (n m : ℕ) : Decidable (fp.WellFormed n m) := by
  unfold WellFormed; infer_instance

/-- A table on `ℕ` as a function on `Fin m` (reduced modulo `m`). -/
def finFun (m : ℕ) (g : ℕ → ℕ) : Fin m → Fin m :=
  fun i => ⟨g i % m, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

/-- `σ` as a function on `Fin m`. -/
def sigmaFun (m : ℕ) : Fin m → Fin m := finFun m fp.sigmaNat
/-- `α` as a function on `Fin m`. -/
def alphaFun (m : ℕ) : Fin m → Fin m := finFun m fp.alphaNat
/-- `curve` as a function on `Fin m`. -/
def curveFun (n m : ℕ) [NeZero n] : Fin m → Fin n := fun a => Fin.ofNat n (fp.curveNat a)

/-- A permutation from a function `f` with `f⁴ = id` (inverse `f³`). -/
def permOfPow4 {m : ℕ} (f : Fin m → Fin m) (h : ∀ i, f (f (f (f i))) = i) : Perm (Fin m) where
  toFun := f
  invFun := fun i => f (f (f i))
  left_inv := h
  right_inv := h

/-- A permutation from an involution. -/
def permOfInvolution {m : ℕ} (f : Fin m → Fin m) (h : ∀ i, f (f i) = i) : Perm (Fin m) where
  toFun := f
  invFun := f
  left_inv := h
  right_inv := h

/-- The arrangement described by a fingerprint, given the (decidable) checks. -/
def toArrangement (n m : ℕ) [NeZero n] (_hwf : fp.WellFormed n m)
    (hσ : ∀ i, fp.sigmaFun m (fp.sigmaFun m (fp.sigmaFun m (fp.sigmaFun m i))) = i)
    (hα : ∀ i, fp.alphaFun m (fp.alphaFun m i) = i)
    (h : IsArrangement n (permOfPow4 _ hσ) (permOfInvolution _ hα) (fp.curveFun n m)) :
    Arrangement n (Fin m) where
  σ := permOfPow4 _ hσ
  α := permOfInvolution _ hα
  curve := fp.curveFun n m
  isArrangement := h

/-- `A` is the arrangement of the fingerprint `fp`, read off from the map `A` alone (not from the
tables above): walking straight along circle `c` from the dart `2 · offset c` visits the darts
`2 (offset c + i)` of the list of `c` in order, and at the crossing of the entry `k` the other
curve (the curve of `σ (2k)`) is the circle named by the entry. -/
def Describes {n m : ℕ} (A : Arrangement n (Fin m)) : Prop :=
  fp.numDarts = m ∧
  (∀ c < fp.length, ∀ i < fp.len c, ∀ a : Fin m, a.val = 2 * fp.offset c →
    ((A.straight)^[i] a).val = 2 * (fp.offset c + i)) ∧
  (∀ k < fp.entries.length, ∀ a : Fin m, a.val = 2 * k →
    (A.curve (A.σ a)).val = (fp.entry k).natAbs - 1)

instance {n m : ℕ} (A : Arrangement n (Fin m)) : Decidable (fp.Describes A) := by
  unfold Describes; infer_instance

/-- The labels and signs of `fp`, read off from `A`: the dart `2k` of the list of `c` lies on
curve `c`, and the entry `k` is positive iff `σ (2k)` is a forward dart (even number) of the
other curve, i.e. the other curve crosses from the right of `c` to its left. Together with
`Describes` this determines `fp` from `A` and the dart numbering. -/
def DescribesSigns {n m : ℕ} (A : Arrangement n (Fin m)) : Prop :=
  ∀ k < fp.entries.length, ∀ a : Fin m, a.val = 2 * k →
    (A.curve a).val = fp.circleOfIndex k ∧ ((A.σ a).val % 2 = 0 ↔ 0 < fp.entry k)

instance {n m : ℕ} (A : Arrangement n (Fin m)) : Decidable (fp.DescribesSigns A) := by
  unfold DescribesSigns; infer_instance

end Fingerprint

end Pca
