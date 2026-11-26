/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): the canonical cylindrical arrangement `𝒜_n^-`

FROS (`sec:main_cipa`) define `𝔅_n^-` as an arrangement of pseudoparabolas: "On the left, the
pseudoparabolas are labelled `C_1, …, C_n` from top to bottom and on the right, the top to bottom
order is the same. For every `1 ≤ i ≤ n`, the pseudoparabola `C_i` intersects the other
pseudoparabolas first in increasing and then in decreasing order: `C_1, …, C_n, C_n, …, C_1`."
Closing the pseudoparabolas above gives the cylindrical arrangement `𝒜_n^-`; "every triple of
pseudocircles forms a NonKrupp(2) in `𝒜_n^-`".

Graph language (no pseudoparabolas): with the curves labelled `c 0, …, c (n-1)`, `Canon M c` says

* for `j < l` and `i ∉ {j, l}`, the crossings of `c j` and `c l` lie in the interior of `c i`
  exactly when `j < i < l` (in `𝔅_n^-` the crossings of `C_j` and `C_l` lie below `C_i` exactly for
  the `C_i` between them), and
* the marked cell has a side on `c 0` (the unbounded cell is above `C_1`).

This determines the arrangement: on every curve `c i` the arcs inside / outside the other curves
are nested, so the order of the crossings along `c i` is `c 0, …, c (n-1), c (n-1), …, c 0` (without `c i`),
and the orientation at each crossing follows from the sides (`canon_iso`, `CanonIso.lean`).
-/
import Pca.FlipGraph.Lens

open Equiv Finset

namespace Pca.FlipGraph

universe u v

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- The crossing pattern of `𝒜_n^-` for the processed curves: the condition of `Canon` for all
triples whose smallest index is `< k` (the invariant of FROS' proof of Theorem 4 after `k` curves
have been processed). -/
def Marked.CanonUpTo (M : Marked n D) (c : Fin n ≃ Fin n) (k : ℕ) : Prop :=
  ∀ i j l : Fin n, i ≠ j → i ≠ l → j < l → (i.val < k ∨ j.val < k) →
    ∀ x : M.A.Crossing, Arrangement.Crossing.curves M.A x = {c j, c l} →
      (M.CrossInside (c i) x ↔ j < i ∧ i < l)

/-- The marked cell has a side on the first curve `c 0`. -/
def Marked.MarkOnFirst (M : Marked n D) (c : Fin n ≃ Fin n) : Prop :=
  ∃ y, M.A.cellOf y = M.z ∧ (c.symm (M.A.curve y)).val = 0

/-- **The canonical arrangement `𝒜_n^-`** (with labels `c`). -/
def Marked.Canon (M : Marked n D) (c : Fin n ≃ Fin n) : Prop :=
  M.CanonUpTo c n ∧ M.MarkOnFirst c

end Pca.FlipGraph
