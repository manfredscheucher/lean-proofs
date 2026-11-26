/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# 3-signotopes (Levi's lemma, signotope variant P4'; `doc/pca/great.md` section 5)

Source: H. Bergold, S. Felsner, M. Scheucher, *An extension theorem for signotopes*,
https://arxiv.org/abs/2303.04079 (BFS), sections 1.1 and 1.2, for rank `r = 3`.

* A **3-signotope** on `[n]` (here `Fin n`) is a map `σ` from the 3-subsets to `{+, -}` (here
  `Bool`, `true = +`) such that for every 4-subset `X = (x₁ < x₂ < x₃ < x₄)` the sequence
  `σ(X \ x₁), σ(X \ x₂), σ(X \ x₃), σ(X \ x₄)` has at most one sign change (BFS 1.1). Values of
  `σ` on sets that are not 3-subsets are ignored.
* **Deletion** `σ↓k` of `k : Fin (n + 1)` from a signotope on `[n+1]` (BFS 1.2,
  `σ↓k(X↓k) = σ(X)` for `k ∉ X`): `(σ↓k)(Y) = σ(Y shifted up past k)`, the shift being
  `Fin.succAbove k`.
* A 3-subset `F` is a **fliple** of `σ` if both signs on `F` give a signotope (BFS 1.2).

In BFS 1.1 a 3-signotope encodes a simple (marked) Euclidean pseudoline arrangement with lines
`1, …, n` from top to bottom on the left: `σ(a,b,c) = +` iff the crossing of `a` and `c` lies below
`b` (Felsner-Weil: bijection with arrangements with a fixed top cell); triangles correspond to
fliples. This correspondence is not formalized here.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fintype.Fin

open Finset

namespace Pca.Great.Sig

/-- At most one sign change in a list of signs. -/
def AtMostOneChange : List Bool → Prop
  | a :: b :: l => (a = b ∧ AtMostOneChange (b :: l)) ∨ (a ≠ b ∧ ∀ c ∈ l, c = b)
  | _ => True

instance : DecidablePred AtMostOneChange := by
  intro l
  induction l with
  | nil => exact isTrue trivial
  | cons a l ih =>
    cases l with
    | nil => exact isTrue trivial
    | cons b l => unfold AtMostOneChange; exact inferInstance

/-- `σ` is a **3-signotope** on `Fin n`: at most one sign change on every 4-packet, the 3-subsets
listed in reverse lexicographic order `X \ x₁, X \ x₂, X \ x₃, X \ x₄`. -/
def IsSig {n : ℕ} (σ : Finset (Fin n) → Bool) : Prop :=
  ∀ x₁ x₂ x₃ x₄ : Fin n, x₁ < x₂ → x₂ < x₃ → x₃ < x₄ →
    AtMostOneChange [σ {x₂, x₃, x₄}, σ {x₁, x₃, x₄}, σ {x₁, x₂, x₄}, σ {x₁, x₂, x₃}]

/-- **Deletion** of the element `k` from a map on the subsets of `Fin (n + 1)`. -/
def del {n : ℕ} (σ : Finset (Fin (n + 1)) → Bool) (k : Fin (n + 1)) : Finset (Fin n) → Bool :=
  fun Y => σ (Y.map (Fin.succAboveEmb k))

/-- The 3-subset `F` is a **fliple** of `σ`: `σ` and `σ` with the sign of `F` changed are both
signotopes. -/
def IsFliple {n : ℕ} (σ : Finset (Fin n) → Bool) (F : Finset (Fin n)) : Prop :=
  F.card = 3 ∧ IsSig σ ∧ IsSig (Function.update σ F (!σ F))

/-- The signotope `σ'` on `Fin (n + 1)` **extends** `σ` by the element `k`: deleting `k` gives `σ`
(on all 3-subsets). -/
def Extends {n : ℕ} (σ' : Finset (Fin (n + 1)) → Bool) (k : Fin (n + 1))
    (σ : Finset (Fin n) → Bool) : Prop :=
  ∀ X : Finset (Fin n), X.card = 3 → del σ' k X = σ X

/-- The lift `I*` of a 2-subset `I` of `Fin n` for the extending element `k`: `I*↓k = I`, `k ∈ I*`. -/
def lift {n : ℕ} (k : Fin (n + 1)) (I : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  insert k (I.map (Fin.succAboveEmb k))

end Pca.Great.Sig
