/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): flipping a cylindrical arrangement to `𝒜_n^-`, curve by curve

FROS, proof of Theorem 4: "The idea is to flip the pseudoparabolas downwards one by one in the
order of increasing indices. When `C_n` has been processed the arrangement `𝔅_n^-` [...] is
reached. When flipping `C_k` downwards the following invariant holds [the orders of the crossings
on `C_i`]. Let `𝒜_{≥k}` denote the subarrangement induced by `C_k, …, C_n`. We claim that in
`𝒜_{≥k}` the pseudoparabola `C_k` can be swept downwards using only triangle flips. [...] By the
invariant, all crossings of `𝒜_{≥k}` lie above all the pseudoparabolas `C_1, …, C_{k−1}`.
Therefore, we can perform the flip sequence from `𝒜_{≥k}` also in the original arrangement."

Graph language (no pseudoparabola picture; `doc/pca/flipgraph.md`, Track F): "downwards" is towards a
center `p`; "above `C_i`" is the exterior of `C_i`; the order `C_1, …, C_n` (top to bottom on the
left) is read off the first processed curve; the invariant is `CanonUpTo c k`.

* `clear_first`: the first curve `C_1` (one with a side on the marked cell: "topmost") is swept
  downwards until no crossing of other curves lies inside it, by good flips (`First.lean`: SH's
  lemma `sweepFirstMove` while the center has no side on `C_1`, else the zipping step for the lens
  `int C_1` whose two arcs are the parts of `C_1` between the marked side and the side of the
  center).
* `order_of_first` (`Order.lean`): afterwards the parts of `C_1` inside the other curves are
  nested; this order labels the curves, and `CanonUpTo c 1` holds.
* `process_step`: with `C_1, …, C_k` processed, `C_{k+1}` is swept downwards in the lens
  `int C_{k+1} ∩ ext C_k` (zipping, `Zip.lean`; FROS sweep `C_{k+1}` in `𝒜_{≥k+1}` with SH's lemma,
  in graph language the region below `C_{k+1}` and above the processed curves is this lens).
-/
import Pca.FlipGraph.CanonIso
import Pca.FlipGraph.First
import Pca.FlipGraph.Order
import Pca.FlipGraph.Zip
import Pca.FlipGraph.ProcessStep
import Pca.SweepLemma

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- **Processing the first curve**: a curve `C₀` with a side on the marked cell can be swept by
triangle flips (inside the class of cylindrical arrangements) until no crossing of two other
curves lies in its interior; the marked cell keeps a side on `C₀`. -/
theorem clear_first (M : Marked n D) (hc : M.Cylindrical) {y₀ : D} (hy₀ : M.A.cellOf y₀ = M.z) :
    ∃ N, CylReach M N ∧
      (∀ x : N.A.Crossing, M.A.curve y₀ ∉ Arrangement.Crossing.curves N.A x → ¬ N.CrossInside (M.A.curve y₀) x) ∧
      ∃ y, N.A.curve y = M.A.curve y₀ ∧ N.A.cellOf y = N.z := by
  classical
  set C₀ := M.A.curve y₀ with hC₀
  suffices H : ∀ m (M' : Marked n D), First.mu M' C₀ = m → M'.Cylindrical → ∀ y,
      M'.A.curve y = C₀ → M'.A.cellOf y = M'.z → ∃ N, CylReach M' N ∧
        (∀ x : N.A.Crossing, C₀ ∉ Arrangement.Crossing.curves N.A x → ¬ N.CrossInside C₀ x) ∧
        ∃ y, N.A.curve y = C₀ ∧ N.A.cellOf y = N.z from H _ M rfl hc y₀ rfl hy₀
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro M' hm hc' y hyc hyz
  rcases Nat.eq_zero_or_pos (First.mu M' C₀) with h0 | hpos
  · refine ⟨M', Relation.ReflTransGen.refl, fun x hx hin => ?_, y, hyc, hyz⟩
    obtain ⟨w, rfl⟩ := x.exists_mk
    have : w ∈ univ.filter (fun y : D => C₀ ∉ Arrangement.Crossing.curves M'.A (M'.A.crossingOf y) ∧
        M'.CrossInside C₀ (M'.A.crossingOf y)) := mem_filter.2 ⟨mem_univ _, hx, hin⟩
    unfold First.mu at h0
    rw [card_eq_zero] at h0
    rw [h0] at this
    exact Finset.notMem_empty _ this
  · rw [← hyc] at hpos
    obtain ⟨p, hp, d, hT, hd, hin, hne, hnp⟩ := First.exists_good M' hyz hc' hpos
    obtain ⟨hst, hlt, y', hy'c, hy'z⟩ := First.good_flip M' hyz hp hT hd hin hne hnp
    rw [hyc] at hlt hy'c
    obtain ⟨N, hN, hcl, hz⟩ := ih _ (hm ▸ hlt) (M'.flip d hT) rfl hst.2.2 y' hy'c hy'z
    exact ⟨N, Relation.ReflTransGen.head hst hN, hcl, hz⟩

/-- **Processing the next curve**: with `c 0, …, c (k-1)` processed (`1 ≤ k < n`), the curve `c k`
is swept downwards by zipping the lens `int (c k) ∩ ext (c (k-1))`; afterwards `c 0, …, c k` are
processed. -/
theorem process_step (M : Marked n D) (hc : M.Cylindrical) (c : Fin n ≃ Fin n) {k : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) (hinv : M.CanonUpTo c k) (hmark : M.MarkOnFirst c) :
    ∃ N, CylReach M N ∧ N.CanonUpTo c (k + 1) ∧ N.MarkOnFirst c := by
  have hne : c ⟨k, hkn⟩ ≠ c ⟨k - 1, by omega⟩ := fun h => by
    have := congrArg Fin.val (c.injective h); simp at this; omega
  have hzQ : ∀ N : Marked n D, ¬ N.TwoQ (c ⟨k, hkn⟩) (c ⟨k - 1, by omega⟩) True False N.z :=
    fun N h => N.not_inside_z _ (h.1.2 trivial)
  obtain ⟨N, hP, hv, htr⟩ := M.zipping hne True False (hzQ M)
    (twoTransversal_of_canon hinv hk hkn)
  have key : CylReach M N ∧ N.Cylindrical ∧ N.CanonUpTo c k ∧ N.MarkOnFirst c := by
    clear hv htr
    induction hP with
    | refl => exact ⟨Relation.ReflTransGen.refl, hc, hinv, hmark⟩
    | tail _ hs ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      obtain ⟨hst, h3', h4'⟩ := lensFlip_step h3 h4 h2 hk hkn hne hs
      exact ⟨h1.tail hst, hst.2.2, h3', h4'⟩
  obtain ⟨hr, -, hinvN, hmN⟩ := key
  exact ⟨N, hr, canon_succ hinvN hk hkn hne hv (N.twoLens_transversal hne htr), hmN⟩

end Pca.FlipGraph
