/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import NonCirc.Fingerprint
import Mathlib.Data.Nat.Pairing

/-! # The three-valued sign encoding (layer 2)

`encode F tags` is a CNF. Its variables are, for every *quantity* `q` (a bracket of four index
vectors, a Lorentz product of two, or a product of two quantities), two Booleans: `(q, true)`
"`q > 0`" and `(q, false)` "`q < 0`" (both false: `q = 0`). Every clause is a sign fact that holds
for every circle realization (`encode_sound` in `NonCirc/EncodeSound.lean`):

* identities (`dep`, `gp`, `f1`): `NAE` of the signed terms;
* proved sign rules (`type3`, `krupp`, `knz`, `perm`) and known signs (`ipFact`);
* the definition of product quantities and the consistency `¬(q > 0 ∧ q < 0)`.

The tags (which instances to use) come from an untrusted script. Every tag is checked here
against the fingerprint; an invalid tag contributes no clause. So the soundness of the encoding
does not depend on the script.
-/

namespace NonCirc

/-- Index vectors: circle `i`, or the crossing point with label `(j, k, s)`. -/
inductive Idx
  | circ (i : ℕ)
  | pt (j k : ℕ) (s : ℤ)
  deriving DecidableEq, Repr

/-- Quantities whose signs are the variables. -/
inductive Q
  | br (a b c d : Idx)
  | ip (x y : Idx)
  | mul (u w : Q)
  deriving DecidableEq, Repr

/-- Injective codes of indices, quantities and variables (for numbering the CNF). -/
def intCode (s : ℤ) : ℕ := Nat.pair s.toNat (-s).toNat

def Idx.code : Idx → ℕ
  | .circ i => Nat.pair 0 i
  | .pt j k s => Nat.pair 1 (Nat.pair j (Nat.pair k (intCode s)))

def Q.code : Q → ℕ
  | .br a b c d => Nat.pair 0 (Nat.pair (Nat.pair a.code b.code) (Nat.pair c.code d.code))
  | .ip x y => Nat.pair 1 (Nat.pair x.code y.code)
  | .mul u w => Nat.pair 2 (Nat.pair u.code w.code)

def varCode (v : Q × Bool) : ℕ := 2 * v.1.code + (if v.2 then 1 else 0)

lemma intCode_inj {s t : ℤ} (h : intCode s = intCode t) : s = t := by
  unfold intCode at h
  rw [Nat.pair_eq_pair] at h
  omega

lemma Idx.code_inj : ∀ {x y : Idx}, x.code = y.code → x = y
  | .circ i, .circ i', h => by simp only [Idx.code, Nat.pair_eq_pair] at h; rw [h.2]
  | .pt j k s, .pt j' k' s', h => by
    simp only [Idx.code, Nat.pair_eq_pair] at h
    obtain ⟨-, h1, h2, h3⟩ := h
    rw [h1, h2, intCode_inj h3]
  | .circ _, .pt .., h | .pt .., .circ _, h => by simp only [Idx.code, Nat.pair_eq_pair] at h; omega

lemma Q.code_inj : ∀ {q q' : Q}, q.code = q'.code → q = q'
  | .br a b c d, .br a' b' c' d', h => by
    simp only [Q.code, Nat.pair_eq_pair] at h
    obtain ⟨-, ⟨h1, h2⟩, h3, h4⟩ := h
    rw [Idx.code_inj h1, Idx.code_inj h2, Idx.code_inj h3, Idx.code_inj h4]
  | .ip x y, .ip x' y', h => by
    simp only [Q.code, Nat.pair_eq_pair] at h
    rw [Idx.code_inj h.2.1, Idx.code_inj h.2.2]
  | .mul u w, .mul u' w', h => by
    simp only [Q.code, Nat.pair_eq_pair] at h
    rw [Q.code_inj h.2.1, Q.code_inj h.2.2]
  | .br .., .ip .., h | .br .., .mul .., h | .ip .., .br .., h | .ip .., .mul .., h
  | .mul .., .br .., h | .mul .., .ip .., h => by
    simp only [Q.code, Nat.pair_eq_pair] at h; omega

lemma varCode_inj : Function.Injective varCode := by
  intro v w h
  obtain ⟨q, b⟩ := v
  obtain ⟨q', b'⟩ := w
  simp only [varCode] at h
  have hb : b = b' := by cases b <;> cases b' <;> simp_all <;> omega
  subst hb
  have : q.code = q'.code := by cases b <;> simp at h <;> omega
  rw [Q.code_inj this]

/-- A literal: the variable `(q, pos)` with a polarity. -/
abbrev Lit := (Q × Bool) × Bool

/-- A clause over these literals. -/
abbrev Clause := List Lit

/-- Clause literals saying `sign q ≠ s`. -/
def notIs (q : Q) : SignType → Clause
  | 1 => [((q, true), false)]
  | -1 => [((q, false), false)]
  | 0 => [((q, true), true), ((q, false), true)]

/-- All sign tuples of length `k`. -/
def tuples : ℕ → List (List SignType)
  | 0 => [[]]
  | k + 1 => (tuples k).flatMap fun t => [1, 0, -1].map (· :: t)

/-- Clauses forbidding every sign tuple of `qs` that violates `rel`. -/
def forbid (rel : List SignType → Bool) (qs : List Q) : List Clause :=
  ((tuples qs.length).filter (fun t => !rel t)).map fun t => (qs.zip t).flatMap fun p => notIs p.1 p.2

/-- `q` is not both positive and negative. -/
def consistent (q : Q) : Clause := [((q, true), false), ((q, false), false)]

/-- `sign (mul u w) = sign u * sign w`, with consistency of the three quantities. -/
def mulDef (u w : Q) : List Clause :=
  [consistent (.mul u w), consistent u, consistent w] ++
    forbid (fun t => t.getD 0 0 == t.getD 1 0 * t.getD 2 0) [.mul u w, u, w]

/-- `sign t = σ * sign u`. -/
def eqRel (σ : SignType) (t u : Q) : List Clause :=
  [consistent t, consistent u] ++ forbid (fun x => x.getD 0 0 == σ * x.getD 1 0) [t, u]

/-- `sign q = s`. -/
def factRel (s : SignType) (q : Q) : List Clause :=
  [consistent q] ++ forbid (fun x => x.getD 0 0 == s) [q]

/-- `q ≠ 0`. -/
def nzRel (q : Q) : List Clause := [consistent q, [((q, true), true), ((q, false), true)]]

/-- `NAE` of the signs `σ_i * sign q_i`: if one is positive, another is negative, and conversely. -/
def naeRel (ts : List (SignType × Q)) : List Clause :=
  let posLit : SignType × Q → Lit := fun t => ((t.2, t.1 == 1), true)
  let negLit : SignType × Q → Lit := fun t => ((t.2, t.1 != 1), true)
  ts.map (fun t => consistent t.2) ++
  ts.flatMap fun t =>
    [((posLit t).1, false) :: ts.map negLit, ((negLit t).1, false) :: ts.map posLit]

namespace Fingerprint

variable (F : Fingerprint)

/-- A valid circle index. -/
def isCirc (m : ℕ) : Bool := 1 ≤ m && m ≤ F.n

/-- `w` is a circle through neither crossing and separates them. -/
def separates (l l' : ℕ × ℕ × ℤ) (w : ℕ) : Bool :=
  F.isCirc w && w != l.1 && w != l.2.1 && w != l'.1 && w != l'.2.1 &&
    F.side l.1 l.2.1 l.2.2 w * F.side l'.1 l'.2.1 l'.2.2 w == -1

/-- `w` distinguishes two crossings: it separates them, or it passes through exactly one of them. -/
def distinct (l l' : ℕ × ℕ × ℤ) (w : ℕ) : Bool :=
  F.separates l l' w ||
    (F.isCirc w && (w == l.1 || w == l.2.1) && w != l'.1 && w != l'.2.1) ||
    (F.isCirc w && (w == l'.1 || w == l'.2.1) && w != l.1 && w != l.2.1)

end Fingerprint

/-- A witness that two crossings are different points: a circle (separating them, or through
exactly one of them), or three positions `i < j < k` of the list of circle `m` that hold both
crossings (three crossings in this order on a circle are pairwise different points). -/
inductive Wit
  | circ (w : ℕ)
  | cyc (m i j k : ℕ)
  deriving Repr

namespace Fingerprint

variable (F : Fingerprint)

/-- The witness `w` shows that the crossings `l, l'` are different points. -/
def distinctW (l l' : ℕ × ℕ × ℤ) : Wit → Bool
  | .circ w => F.distinct l l' w
  | .cyc m i j k =>
    let L := F.order m
    let ls := [L.getD i (0, 0, 0), L.getD j (0, 0, 0), L.getD k (0, 0, 0)]
    F.isCirc m && i < j && j < k && k < L.length && l != l' && ls.contains l && ls.contains l'

/-- The known sign of `<x, y>` for an index pair, if any. -/
def ipSign (x y : Idx) (w : Wit) : Option SignType :=
  match x, y with
  | .pt j k s, .pt j' k' s' =>
    if (j, k, s) == (j', k', s') then some 0
    else if decide (F.IsLabel j k s) && decide (F.IsLabel j' k' s') &&
        F.distinctW (j, k, s) (j', k', s') w then some (-1) else none
  | .circ m, .pt j k s | .pt j k s, .circ m =>
    if decide (F.IsLabel j k s) && F.isCirc m then
      (if m == j || m == k then some 0 else some (SignType.sign (F.side j k s m)))
    else none
  | .circ _, .circ _ => none

end Fingerprint

/-- Tags: one instance of an identity or a sign rule. -/
inductive Tag
  /-- five-vector dependency `Σ (-1)^(t+1) [X \ x_t] <x_t, y> = 0` -/
  | dep (x0 x1 x2 x3 x4 y : Idx)
  /-- 3-term Grassmann-Plücker relation -/
  | gp (a b c d e f : Idx)
  /-- family 1: the crossings at positions `i1 < i2 < i3 < i4` of the list of circle `m` -/
  | f1 (x y z : Idx) (m i1 i2 i3 i4 : ℕ)
  /-- swap of two adjacent entries of a bracket (`k = 0, 1, 2`) -/
  | perm (a b c d : Idx) (k : ℕ)
  /-- known sign of `<x, y>` (`w`: two different points) -/
  | ipFact (x y : Idx) (w : Wit)
  /-- `[v_j v_k p⁺ p⁻] ≠ 0` (`w`: `p⁺ ≠ p⁻`) -/
  | knz (j k : ℕ) (w : Wit)
  /-- type 3: `[v_j v_k x p⁺]` has the sign of `[v_j v_k p⁺ p⁻] <x, p⁺>` (`plus`), and
  `[v_j v_k x p⁻]` the sign of `-[v_j v_k p⁺ p⁻] <x, p⁻>` (`!plus`) -/
  | type3 (j k : ℕ) (x : Idx) (plus : Bool) (w : Wit)
  /-- Krupp tie: if circle `m` separates `p^±_jk`, `[v_j v_k v_m q]` and `[v_j v_k v_m p⁺_jk]` have
  the same sign (`w`: `p⁺ ≠ p⁻`; `wq`: `q` differs from `p⁺` (`useP`) or from `p⁻`) -/
  | krupp (j k m : ℕ) (q : Idx) (w wq : Wit) (useP : Bool)
  deriving Repr

namespace Fingerprint

variable (F : Fingerprint)

/-- The circle vector index of `i` and the crossing point index of a label. -/
def C (i : ℕ) : Idx := .circ i
def Pi (l : ℕ × ℕ × ℤ) : Idx := .pt l.1 l.2.1 l.2.2

/-- The clauses of one tag (none if the tag is invalid). -/
def encodeTag : Tag → List Clause
  | .dep x0 x1 x2 x3 x4 y =>
    let ts : List (SignType × Q × Q) :=
      [(-1, .br x1 x2 x3 x4, .ip x0 y), (1, .br x0 x2 x3 x4, .ip x1 y), (-1, .br x0 x1 x3 x4, .ip x2 y),
       (1, .br x0 x1 x2 x4, .ip x3 y), (-1, .br x0 x1 x2 x3, .ip x4 y)]
    ts.flatMap (fun t => mulDef t.2.1 t.2.2) ++ naeRel (ts.map fun t => (t.1, .mul t.2.1 t.2.2))
  | .gp a b c d e f =>
    let ts : List (SignType × Q × Q) :=
      [(1, .br a b c d, .br a b e f), (-1, .br a b c e, .br a b d f), (1, .br a b c f, .br a b d e)]
    ts.flatMap (fun t => mulDef t.2.1 t.2.2) ++ naeRel (ts.map fun t => (t.1, .mul t.2.1 t.2.2))
  | .f1 x y z m i1 i2 i3 i4 =>
    let L := F.order m
    let l1 := L.getD i1 (0, 0, 0)
    let l2 := L.getD i2 (0, 0, 0)
    let l3 := L.getD i3 (0, 0, 0)
    let l4 := L.getD i4 (0, 0, 0)
    if F.isCirc m && i1 < i2 && i2 < i3 && i3 < i4 && i4 < L.length &&
        [l1, l2, l3, l4].all (fun l => decide (F.IsLabel l.1 l.2.1 l.2.2) && (l.1 == m || l.2.1 == m))
    then
      naeRel [(1, .br x y z (Pi l1)), (-1, .br x y z (Pi l2)), (1, .br x y z (Pi l3)),
        (-1, .br x y z (Pi l4))]
    else []
  | .perm a b c d k =>
    match k with
    | 0 => eqRel (-1) (.br b a c d) (.br a b c d)
    | 1 => eqRel (-1) (.br a c b d) (.br a b c d)
    | 2 => eqRel (-1) (.br a b d c) (.br a b c d)
    | _ => []
  | .ipFact x y w =>
    match F.ipSign x y w with
    | some s => factRel s (.ip x y)
    | none => []
  | .knz j k w =>
    if decide (F.IsLabel j k 1) && F.distinctW (j, k, 1) (j, k, -1) w then
      nzRel (.br (C j) (C k) (.pt j k 1) (.pt j k (-1)))
    else []
  | .type3 j k x plus w =>
    if decide (F.IsLabel j k 1) && F.distinctW (j, k, 1) (j, k, -1) w then
      let K : Q := .br (C j) (C k) (.pt j k 1) (.pt j k (-1))
      let p : Idx := .pt j k (if plus then 1 else -1)
      mulDef K (.ip x p) ++ eqRel (if plus then 1 else -1) (.br (C j) (C k) x p) (.mul K (.ip x p))
    else []
  | .krupp j k m q w wq useP =>
    match q with
    | .pt a b s =>
      if decide (F.IsLabel j k 1) && F.distinctW (j, k, 1) (j, k, -1) w && F.isCirc m &&
          m != j && m != k && F.side j k 1 m * F.side j k (-1) m == -1 &&
          decide (F.IsLabel a b s) && F.distinctW (a, b, s) (j, k, if useP then 1 else -1) wq then
        eqRel 1 (.br (C j) (C k) (C m) q) (.br (C j) (C k) (C m) (.pt j k 1))
      else []
    | .circ _ => []

/-- The CNF of a list of tags. -/
def encode (tags : List Tag) : List Clause := tags.flatMap F.encodeTag

end Fingerprint

end NonCirc
