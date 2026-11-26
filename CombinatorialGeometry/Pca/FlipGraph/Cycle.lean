/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): simple directed cycles of `A|_Q` and their regions

Tools for FROS Claim B ("the directed graph of `A|_Q` is acyclic", `ClaimB.lean`). A **simple
directed cycle** (`Cyc`) is a cyclic sequence `z : ZMod k → D` of forward chord darts, each ending
where the next starts, at distinct vertices of `Q`. Its chain (`chain`, the sum of its segments) is
even, its **region** is the normalized cut (`cut`, Jordan in cut form, vanishing off `Q`), and
`size` counts the cells of the region.

* `inZ_at`: at the crossing of `z i` exactly the darts `z i` and `α (z (i - 1))` lie on segments
  of the cycle (simplicity).
* `change_all_or_none`: a function on the cells that changes only across segments of the cycle
  changes across all of them or across none (the even subchains of a simple cycle are `0` and
  the cycle).
* `cut_le` (**monotonicity**): an even chain supported in `Q` whose segments all touch the region
  has its normalized cut inside the region. This replaces "the complement of the region of a
  simple cycle is connected".
-/
import Pca.FlipGraph.SourceTri

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

open Arrangement' Chain

/-- Propagation along `ZMod k`. -/
theorem zmod_induct {k : ℕ} [NeZero k] (P : ZMod k → Prop) (h : ∀ i, P i → P (i + 1)) {i : ZMod k}
    (hi : P i) (j : ZMod k) : P j := by
  have key : ∀ m : ℕ, P (i + m) := fun m => by
    induction m with
    | zero => simpa using hi
    | succ m ih => rw [Nat.cast_succ, ← add_assoc]; exact h _ ih
  have := key (j - i).val
  rwa [ZMod.natCast_zmod_val, add_sub_cancel] at this

theorem zmod_induct_down {k : ℕ} [NeZero k] (P : ZMod k → Prop) (h : ∀ i, P (i + 1) → P i)
    {i : ZMod k} (hi : P i) (j : ZMod k) : P j := by
  have := zmod_induct (fun t => P (-t)) (fun t ht => h (-(t + 1)) (by
    rw [show -(t + 1) + 1 = -t by ring]; exact ht)) (i := -i) (by rw [neg_neg]; exact hi) (-j)
  rwa [neg_neg] at this

namespace Lens

variable {A : Arrangement n D} (Λ : Lens A)

/-- A **simple directed cycle** of `A|_Q`. -/
structure Cyc where
  k : ℕ
  one_lt : 1 < k
  z : ZMod k → D
  fwd : ∀ i, Λ.Fwd (z i)
  link : ∀ i, A.crossingOf (A.α (z i)) = A.crossingOf (z (i + 1))
  inj : ∀ i j, A.crossingOf (z i) = A.crossingOf (z j) → i = j
  vert : ∀ i, Λ.IsVertex (A.crossingOf (z i))

variable {Λ}

namespace Cyc

variable (Z : Λ.Cyc)

instance : NeZero Z.k := ⟨by have := Z.one_lt; omega⟩

/-- The chain of the cycle. -/
def chain : A.Segment → ZMod 2 := ∑ i, δ (A.segmentOf (Z.z i))

/-- `d` lies on a segment of the cycle. -/
def InZ (d : D) : Prop := ∃ i, A.segmentOf d = A.segmentOf (Z.z i)

theorem segmentOf_α (d : D) : A.segmentOf (A.α d) = A.segmentOf d :=
  Orbit.mk_eq_mk.2 (Perm.SameCycle.refl _ _ |>.trans ⟨1, by simp [A.α_α]⟩)

theorem inZ_α {d : D} : Z.InZ (A.α d) ↔ Z.InZ d := by
  unfold InZ; rw [segmentOf_α]

theorem inZ_z (i : ZMod Z.k) : Z.InZ (Z.z i) := ⟨i, rfl⟩

theorem inZ_cases {d : D} (h : Z.InZ d) : ∃ i, d = Z.z i ∨ d = A.α (Z.z i) := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, eq_or_eq_α_of_segmentOf hi⟩

theorem crossing_α (i : ZMod Z.k) : A.crossingOf (A.α (Z.z (i - 1))) = A.crossingOf (Z.z i) := by
  rw [Z.link, sub_add_cancel]

/-- **Simplicity at a vertex**: at the crossing of `z i` only `z i` and `α (z (i - 1))` lie on
segments of the cycle. -/
theorem inZ_at {i : ZMod Z.k} {d : D} (hd : A.crossingOf d = A.crossingOf (Z.z i)) (h : Z.InZ d) :
    d = Z.z i ∨ d = A.α (Z.z (i - 1)) := by
  obtain ⟨j, rfl | rfl⟩ := Z.inZ_cases h
  · exact Or.inl (by rw [Z.inj _ _ hd])
  · right
    have : j + 1 = i := Z.inj _ _ (by rw [← Z.link]; exact hd)
    rw [← this, add_sub_cancel_right]

/-- A dart on a segment of the cycle is at a vertex of the cycle. -/
theorem inZ_vertex {d : D} (h : Z.InZ d) : ∃ i, A.crossingOf d = A.crossingOf (Z.z i) := by
  obtain ⟨j, rfl | rfl⟩ := Z.inZ_cases h
  · exact ⟨j, rfl⟩
  · exact ⟨j + 1, Z.link j⟩

theorem inZ_chord {d : D} (h : Z.InZ d) : Λ.Chord d := by
  obtain ⟨j, rfl | rfl⟩ := Z.inZ_cases h
  · exact (Z.fwd j).1
  · exact chord_α (Z.fwd j).1

variable (hs : Λ.Sep) (ht : Λ.Transversal)
include hs ht

/-- The segments of the cycle are distinct. -/
theorem seg_inj {i j : ZMod Z.k} (h : A.segmentOf (Z.z i) = A.segmentOf (Z.z j)) : i = j := by
  rcases eq_or_eq_α_of_segmentOf h with h | h
  · exact Z.inj _ _ (by rw [h])
  · exfalso
    have := Z.fwd i
    rw [h] at this
    exact (fwd_α_iff hs ht (Z.fwd j).1).1 this (Z.fwd j)

open Classical in
theorem chain_apply (d : D) : Z.chain (A.segmentOf d) = if Z.InZ d then 1 else 0 := by
  classical
  unfold chain
  rw [Finset.sum_apply]
  simp only [δ]
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    rw [sum_eq_single i (fun j _ hj => if_neg fun e => hj (Z.seg_inj hs ht (e.symm.trans hi)))
      (fun h => absurd (mem_univ i) h), if_pos hi]
  · exact sum_eq_zero fun i _ => if_neg fun e => h ⟨i, e⟩

theorem chain_z (i : ZMod Z.k) : Z.chain (A.segmentOf (Z.z i)) = 1 := by
  rw [Z.chain_apply hs ht, if_pos (Z.inZ_z i)]

theorem chain_not {d : D} (h : ¬ Z.InZ d) : Z.chain (A.segmentOf d) = 0 := by
  rw [Z.chain_apply hs ht, if_neg h]

omit hs ht

theorem chain_even : IsEven Z.chain := fun x => by
  unfold chain
  rw [bd_sum]
  simp_rw [bd_δ, Z.link, sum_add_distrib]
  have : ∑ i : ZMod Z.k, δx (A.crossingOf (Z.z (i + 1))) x = ∑ i, δx (A.crossingOf (Z.z i)) x :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  rw [this]
  exact Arrangement.zmod2_add_self _

theorem chain_supp : Supp Λ Z.chain := fun y hy => by
  have : Z.InZ y := by
    by_contra h
    apply hy
    unfold chain
    rw [Finset.sum_apply]
    exact sum_eq_zero fun i _ => by simp only [δ]; exact if_neg fun e => h ⟨i, e⟩
  exact Or.inl (Z.inZ_chord this).1

/-- The **region** of the cycle: its normalized cut. -/
noncomputable def cut : A.Cell → ZMod 2 :=
  Classical.choose (exists_norm Λ Z.chain_even Z.chain_supp)

theorem cut_isCut : IsCut Z.chain Z.cut :=
  (Classical.choose_spec (exists_norm Λ Z.chain_even Z.chain_supp)).1

theorem cut_norm : Norm Λ Z.cut :=
  (Classical.choose_spec (exists_norm Λ Z.chain_even Z.chain_supp)).2

/-- The number of cells of the region. -/
noncomputable def size : ℕ := by
  classical exact (univ.filter fun g => Z.cut g = 1).card

include hs ht

theorem cut_z (i : ZMod Z.k) : Z.cut (A.cellOf (A.α (Z.z i))) = Z.cut (A.cellOf (Z.z i)) + 1 := by
  rw [cut_α Z.cut_isCut, Z.chain_z hs ht]

theorem cut_not {d : D} (h : ¬ Z.InZ d) : Z.cut (A.cellOf (A.α d)) = Z.cut (A.cellOf d) := by
  rw [cut_α Z.cut_isCut, Z.chain_not hs ht h, add_zero]

omit hs ht

/-- Around a crossing the changes of a function on the cells add up to `0`. -/
theorem around (q : A.Cell → ZMod 2) (e : D) :
    (q (A.cellOf e) + q (A.cellOf (A.α e))) +
      (q (A.cellOf (A.σ e)) + q (A.cellOf (A.α (A.σ e)))) +
      (q (A.cellOf (A.σ (A.σ e))) + q (A.cellOf (A.α (A.σ (A.σ e))))) +
      (q (A.cellOf (A.σ (A.σ (A.σ e)))) + q (A.cellOf (A.α (A.σ (A.σ (A.σ e)))))) = 0 := by
  rw [← A.cellOf_σ, ← A.cellOf_σ, ← A.cellOf_σ, ← A.cellOf_σ, A.σ_σ_σ_σ]
  have key : ∀ a b c d : ZMod 2, a + b + (b + c) + (c + d) + (d + a) = 0 := by decide
  exact key _ _ _ _

include hs ht

/-- **Even subchains of a simple cycle**: a function on the cells changing only across segments of
the cycle changes across all of them or across none. -/
theorem change_all_or_none (q : A.Cell → ZMod 2)
    (hq : ∀ y, ¬ Z.InZ y → q (A.cellOf y) = q (A.cellOf (A.α y))) :
    (∀ i, q (A.cellOf (Z.z i)) = q (A.cellOf (A.α (Z.z i)))) ∨
      (∀ i, q (A.cellOf (Z.z i)) ≠ q (A.cellOf (A.α (Z.z i)))) := by
  set ch : D → ZMod 2 := fun y => q (A.cellOf y) + q (A.cellOf (A.α y)) with hch
  have h0 : ∀ y, ¬ Z.InZ y → ch y = 0 := fun y hy => by
    simp only [hch, hq y hy]; exact Arrangement.zmod2_add_self _
  have hα : ∀ y, ch (A.α y) = ch y := fun y => by simp only [hch, A.α_α]; ring
  -- the step: the change across `z (i - 1)` equals the change across `z i`
  have step : ∀ i : ZMod Z.k, ch (Z.z (i - 1)) = ch (Z.z i) := by
    intro i
    set e := A.α (Z.z (i - 1))
    have hxe : A.crossingOf e = A.crossingOf (Z.z i) := Z.crossing_α i
    have hnot : ∀ d, A.crossingOf d = A.crossingOf (Z.z i) → d ≠ Z.z i → d ≠ e → ch d = 0 :=
      fun d hd h1 h2 => h0 d fun h => by rcases Z.inZ_at hd h with h' | h' <;> contradiction
    have hsum : ch e + ch (A.σ e) + ch (A.σ (A.σ e)) + ch (A.σ (A.σ (A.σ e))) = 0 := around q e
    have hzi : Z.z i ≠ e := fun h =>
      (fwd_α_iff hs ht (Z.fwd (i - 1)).1).1 (show Λ.Fwd e from h ▸ Z.fwd i) (Z.fwd (i - 1))
    have x1 : A.crossingOf (A.σ e) = A.crossingOf (Z.z i) := by rw [A.crossingOf_σ, hxe]
    have x2 : A.crossingOf (A.σ (A.σ e)) = A.crossingOf (Z.z i) := by rw [A.crossingOf_σσ, hxe]
    have x3 : A.crossingOf (A.σ (A.σ (A.σ e))) = A.crossingOf (Z.z i) := by
      rw [A.crossingOf_σσσ, hxe]
    have n10 : A.σ e ≠ e := A.σ_ne e
    have n20 : A.σ (A.σ e) ≠ e := fun h => A.cellOf_σσ_ne e (by rw [h])
    have n21 : A.σ (A.σ e) ≠ A.σ e := A.σ_ne _
    have n32 : A.σ (A.σ (A.σ e)) ≠ A.σ (A.σ e) := A.σ_ne _
    have n31 : A.σ (A.σ (A.σ e)) ≠ A.σ e := fun h =>
      A.cellOf_σσ_ne (A.σ e) (by rw [h])
    have n30 : A.σ (A.σ (A.σ e)) ≠ e := fun h => n10 (by
      have := congrArg A.σ h; rw [A.σ_σ_σ_σ] at this; exact this.symm)
    have hmem := (A.crossingOf_eq_iff).1 hxe
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hmem
    have hfin : ch e = ch (Z.z i) := by
      have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      rcases hmem with h | h | h | h
      · exact absurd h hzi
      · rw [hnot _ x2 (by rw [h]; exact n21) n20, hnot _ x3 (by rw [h]; exact n31) n30, ← h]
          at hsum
        exact key _ _ (by simpa using hsum)
      · rw [hnot _ x1 (by rw [h]; exact n21.symm) n10, hnot _ x3 (by rw [h]; exact n32) n30, ← h]
          at hsum
        exact key _ _ (by simpa using hsum)
      · rw [hnot _ x1 (by rw [h]; exact n31.symm) n10, hnot _ x2 (by rw [h]; exact n32.symm) n20,
          ← h] at hsum
        exact key _ _ (by simpa using hsum)
    rw [← hfin, hα]
  have hall : ∀ i j : ZMod Z.k, ch (Z.z i) = ch (Z.z j) := fun i j =>
    zmod_induct (fun t => ch (Z.z t) = ch (Z.z i)) (fun t ht' => by
      rw [← ht', ← step (t + 1), add_sub_cancel_right]) rfl j |>.symm
  rcases Chain.zmod2_cases (ch (Z.z 0)) with h | h
  · left
    intro i
    have := (hall i 0).trans h
    simp only [hch] at this
    have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact key _ _ this
  · right
    intro i e'
    have := (hall i 0).trans h
    simp only [hch, e', Arrangement.zmod2_add_self] at this
    exact absurd this (by decide)

/-- The region is not empty. -/
theorem exists_region : ∃ g, Z.cut g = 1 := by
  have h1 := Z.cut_z hs ht 0
  rcases Chain.zmod2_cases (Z.cut (A.cellOf (Z.z 0))) with h2 | h2
  · exact ⟨_, by rw [h1, h2]; rfl⟩
  · exact ⟨_, h2⟩

/-- **Monotonicity**: the normalized cut of an even chain whose segments all touch the region of
the cycle lies inside the region. -/
theorem cut_le {c : A.Segment → ZMod 2} {r : A.Cell → ZMod 2} (hr : IsCut c r) (hn : Norm Λ r)
    (hsupp : ∀ y, c (A.segmentOf y) ≠ 0 → Z.cut (A.cellOf y) = 1 ∨ Z.cut (A.cellOf (A.α y)) = 1)
    {h : A.Cell} (hh : Z.cut h = 0) : r h = 0 := by
  classical
  set q : A.Cell → ZMod 2 := fun g => if Z.cut g = 0 then r g else 0 with hqdef
  have hq : ∀ y, ¬ Z.InZ y → q (A.cellOf y) = q (A.cellOf (A.α y)) := by
    intro y hy
    have e := Z.cut_not hs ht hy
    simp only [hqdef, e]
    split_ifs with h0
    · have hc : c (A.segmentOf y) = 0 := by
        by_contra hne
        rcases hsupp y hne with h1 | h1
        · rw [h0] at h1; exact absurd h1 (by decide)
        · rw [e, h0] at h1; exact absurd h1 (by decide)
      rw [cut_α hr y, hc, add_zero]
    · rfl
  have hoff : ∀ g, ¬ Λ.Q g → q g = 0 := fun g hg => by
    simp only [hqdef, Z.cut_norm g hg, if_true]; exact hn g hg
  have key1 : ∀ a b : ZMod 2, a ≠ b → a + b = 1 := by decide
  rcases Z.change_all_or_none hs ht q hq with hall | hall
  · have h0 : IsCut 0 q := by
      intro y
      by_cases hy : Z.InZ y
      · obtain ⟨i, rfl | rfl⟩ := Z.inZ_cases hy
        · rw [hall i, Arrangement.zmod2_add_self]; rfl
        · rw [A.α_α, ← hall i, Arrangement.zmod2_add_self]; rfl
      · rw [hq y hy, Arrangement.zmod2_add_self]; rfl
    obtain ⟨g, hg⟩ := exists_not_Q Λ
    have := const_of_cut_zero h0 h g
    rw [hoff g hg] at this
    simpa [hqdef, hh] using this
  · exfalso
    have hcut : IsCut Z.chain q := by
      intro y
      by_cases hy : Z.InZ y
      · obtain ⟨i, rfl | rfl⟩ := Z.inZ_cases hy
        · rw [Z.chain_z hs ht i]; exact key1 _ _ (hall i)
        · rw [A.α_α, segmentOf_α, Z.chain_z hs ht i]; exact key1 _ _ (Ne.symm (hall i))
      · rw [Z.chain_not hs ht hy, hq y hy, Arrangement.zmod2_add_self]
    have := norm_unique Λ hcut hoff Z.cut_isCut Z.cut_norm
    obtain ⟨g, hg⟩ := Z.exists_region hs ht
    have e := congrFun this g
    simp only [hqdef, hg, one_ne_zero, if_false] at e
    exact absurd e (by decide)

end Cyc

end Lens

end Pca.FlipGraph
