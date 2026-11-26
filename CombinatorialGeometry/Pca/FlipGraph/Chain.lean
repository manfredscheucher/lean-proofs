/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): chains and normalized cuts in a lens

Tools for the region arguments of FROS Lemma 2 (`Lens.zipStep`). A **chain** is a `ZMod 2`-valued
function on the segments (a set of segments with symmetric difference as sum); its boundary at a
crossing is the sum of its values on the four darts there. An even chain (boundary `0`) is cut by
a function on the cells (`exists_cut`, Jordan in cut form, from `Cut.exists_cut`). In a lens, a
chain supported on segments with a cell in `Q` has a unique cut vanishing off `Q`
(`exists_norm`, `norm_unique`); normalized cuts add (`IsCut.add`). Along a straight walk a cut
changes by the values of the passed segments (`cut_pow`). A straight walk of `k` darts has
boundary `δ start + δ end` (`bd_walk`).
-/
import Pca.FlipGraph.Trap

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace Chain

variable {A : Arrangement n D}

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

/-- The boundary of a chain at a crossing. -/
def bd (c : A.Segment → ZMod 2) (x : A.Crossing) : ZMod 2 := ∑ y ∈ x.darts, c (A.segmentOf y)

/-- An even chain: boundary `0` everywhere. -/
def IsEven (c : A.Segment → ZMod 2) : Prop := ∀ x, bd c x = 0

/-- `r` cuts the cells along the chain `c`. -/
def IsCut (c : A.Segment → ZMod 2) (r : A.Cell → ZMod 2) : Prop :=
  ∀ y, r (A.cellOf y) + r (A.cellOf (A.α y)) = c (A.segmentOf y)

theorem bd_add (c c' : A.Segment → ZMod 2) (x : A.Crossing) : bd (c + c') x = bd c x + bd c' x := by
  unfold bd; simp only [Pi.add_apply, sum_add_distrib]

theorem bd_sum {ι : Type*} (s : Finset ι) (c : ι → A.Segment → ZMod 2) (x : A.Crossing) :
    bd (∑ i ∈ s, c i) x = ∑ i ∈ s, bd (c i) x := by
  unfold bd; simp only [Finset.sum_apply]; exact sum_comm

theorem IsEven.add {c c' : A.Segment → ZMod 2} (h : IsEven c) (h' : IsEven c') : IsEven (c + c') :=
  fun x => by rw [bd_add, h x, h' x, add_zero]

/-- **Jordan (cut form)** for chains. -/
theorem exists_cut {c : A.Segment → ZMod 2} (hc : IsEven c) : ∃ r, IsCut c r := by
  classical
  set E : Finset A.Segment := univ.filter (fun s => c s = 1) with hE
  have hval : ∀ y, (if A.segmentOf y ∈ E then (1 : ZMod 2) else 0) = c (A.segmentOf y) := by
    intro y
    simp only [hE, mem_filter, mem_univ, true_and]
    rcases zmod2_cases (c (A.segmentOf y)) with h | h <;> simp [h]
  have hev : Cut.IsEven A E := by
    intro x
    have h := hc x
    unfold bd at h
    rw [← ZMod.natCast_eq_zero_iff_even, natCast_card_filter]
    calc _ = ∑ y ∈ x.darts, c (A.segmentOf y) := sum_congr rfl fun y _ => hval y
      _ = 0 := h
  obtain ⟨r, hr⟩ := Cut.exists_cut A E hev
  exact ⟨r, fun y => by rw [hr y, hval y]⟩

theorem IsCut.add {c c' : A.Segment → ZMod 2} {r r' : A.Cell → ZMod 2} (h : IsCut c r)
    (h' : IsCut c' r') : IsCut (c + c') (r + r') := fun y => by
  simp only [Pi.add_apply]
  rw [← h y, ← h' y]; ring

theorem IsCut.sum {ι : Type*} (s : Finset ι) {c : ι → A.Segment → ZMod 2}
    {r : ι → A.Cell → ZMod 2} (h : ∀ i ∈ s, IsCut (c i) (r i)) :
    IsCut (∑ i ∈ s, c i) (∑ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro y; simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem cut_α {c : A.Segment → ZMod 2} {r : A.Cell → ZMod 2} (hr : IsCut c r) (y : D) :
    r (A.cellOf (A.α y)) = r (A.cellOf y) + c (A.segmentOf y) :=
  Arrangement.zmod2_eq_add_of_add_eq (hr y)

/-- Around a crossing: the cell of `σ y` is the cell across the segment of `y`. -/
theorem cut_σ {c : A.Segment → ZMod 2} {r : A.Cell → ZMod 2} (hr : IsCut c r) (y : D) :
    r (A.cellOf (A.σ y)) = r (A.cellOf y) + c (A.segmentOf y) := by
  rw [A.cellOf_σ, cut_α hr]

/-- A cut of the zero chain is constant. -/
theorem const_of_cut_zero {r : A.Cell → ZMod 2} (hr : IsCut 0 r) (f g : A.Cell) : r f = r g := by
  have hα : ∀ y, r (A.cellOf (A.α y)) = r (A.cellOf y) := fun y => by
    rw [cut_α hr]; simp
  obtain ⟨y, rfl⟩ := f.exists_mk
  obtain ⟨z, rfl⟩ := g.exists_mk
  exact A.const_of_invariant (fun y => r (A.cellOf y))
    (fun y => by show r (A.cellOf (A.σ y)) = r (A.cellOf y); rw [A.cellOf_σ, hα]) hα y z

/-- Along a straight walk the cut changes by the values of the passed segments (the segment of
`σ (α ·)` at each end crossing). -/
theorem cut_straight {c : A.Segment → ZMod 2} {r : A.Cell → ZMod 2} (hr : IsCut c r) (y : D) :
    r (A.cellOf (A.straight y)) = r (A.cellOf y) + c (A.segmentOf (A.σ (A.α y))) := by
  rw [A.straight_apply, A.cellOf_σ, cut_α hr, A.cellOf_σ, A.α_α]

theorem cut_pow {c : A.Segment → ZMod 2} {r : A.Cell → ZMod 2} (hr : IsCut c r) (y : D) (k : ℕ) :
    r (A.cellOf ((A.straight ^ k) y)) = r (A.cellOf y) +
      ∑ i ∈ range k, c (A.segmentOf (A.σ (A.α ((A.straight ^ i) y)))) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Walk.pow_succ_apply, cut_straight hr, ih, sum_range_succ, add_assoc]

/-! ## Atoms and walks -/

/-- The chain of one segment. -/
def δ (s : A.Segment) : A.Segment → ZMod 2 := fun t => if t = s then 1 else 0

/-- The indicator of a crossing. -/
def δx (x : A.Crossing) : A.Crossing → ZMod 2 := fun x' => if x' = x then 1 else 0

theorem bd_δ (z : D) (x : A.Crossing) :
    bd (δ (A.segmentOf z)) x = δx (A.crossingOf z) x + δx (A.crossingOf (A.α z)) x := by
  classical
  unfold bd δ δx
  have hseg : ∀ y, A.segmentOf y = A.segmentOf z ↔ y = z ∨ y = A.α z := fun y =>
    ⟨eq_or_eq_α_of_segmentOf, by
      rintro (rfl | rfl)
      · rfl
      · exact Orbit.mk_eq_mk.2 (Perm.SameCycle.refl _ _ |>.trans ⟨1, by simp⟩).symm⟩
  have hne : z ≠ A.α z := fun h => A.isArrangement.α_ne z h.symm
  simp_rw [hseg]
  rw [← natCast_card_filter]
  have : x.darts.filter (fun y => y = z ∨ y = A.α z) =
      (if A.crossingOf z = x then {z} else ∅) ∪ (if A.crossingOf (A.α z) = x then {A.α z} else ∅) := by
    ext y
    simp only [mem_filter, Orbit.mem_darts, mem_union]
    constructor
    · rintro ⟨hy, rfl | rfl⟩
      · left; rw [if_pos (by rw [← hy]; rfl)]; exact mem_singleton_self _
      · right; rw [if_pos (by rw [← hy]; rfl)]; exact mem_singleton_self _
    · rintro (h | h)
      · split_ifs at h with h1
        · rw [mem_singleton.1 h]; exact ⟨h1.symm ▸ rfl, Or.inl rfl⟩
        · simp at h
      · split_ifs at h with h1
        · rw [mem_singleton.1 h]; exact ⟨h1.symm ▸ rfl, Or.inr rfl⟩
        · simp at h
  rw [this]
  have hdisj : Disjoint (if A.crossingOf z = x then ({z} : Finset D) else ∅)
      (if A.crossingOf (A.α z) = x then {A.α z} else ∅) := by
    split_ifs <;> simp [hne]
  rw [card_union_of_disjoint hdisj]
  push_cast
  congr 1
  · split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  · split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp

/-- The chain of the first `k` darts of the straight walk of `y`. -/
def walk (y : D) (k : ℕ) : A.Segment → ZMod 2 :=
  ∑ i ∈ range k, δ (A.segmentOf ((A.straight ^ i) y))

theorem crossingOf_α_pow (y : D) (i : ℕ) :
    A.crossingOf (A.α ((A.straight ^ i) y)) = A.crossingOf ((A.straight ^ (i + 1)) y) := by
  rw [Walk.pow_succ_apply, A.straight_apply, A.crossingOf_σσ]

/-- The boundary of a straight walk: its start and its end. -/
theorem bd_walk (y : D) (k : ℕ) (x : A.Crossing) :
    bd (walk y k) x = δx (A.crossingOf y) x + δx (A.crossingOf ((A.straight ^ k) y)) x := by
  induction k with
  | zero =>
    simp only [walk, range_zero, sum_empty, pow_zero, Perm.one_apply]
    unfold bd; simp only [Pi.zero_apply, sum_const_zero]
    exact (Arrangement.zmod2_add_self _).symm
  | succ k ih =>
    rw [walk, sum_range_succ, bd_add, ← walk, ih, bd_δ, crossingOf_α_pow]
    have key : ∀ a b c : ZMod 2, a + b + (b + c) = a + c := by decide
    exact key _ _ _

theorem walk_apply (y : D) (k : ℕ) (s : A.Segment) :
    walk y k s = ∑ i ∈ range k, if s = A.segmentOf ((A.straight ^ i) y) then 1 else 0 := by
  simp only [walk, Finset.sum_apply, δ]

/-! ## Normalized cuts in a lens -/

variable (Λ : Lens A)

/-- `c` is supported on segments with a cell in `Q`. -/
def Supp (c : A.Segment → ZMod 2) : Prop :=
  ∀ y, c (A.segmentOf y) ≠ 0 → Λ.Q (A.cellOf y) ∨ Λ.Q (A.cellOf (A.α y))

/-- `r` vanishes off `Q`. -/
def Norm (r : A.Cell → ZMod 2) : Prop := ∀ f, ¬ Λ.Q f → r f = 0

theorem Supp.add {c c' : A.Segment → ZMod 2} (h : Supp Λ c) (h' : Supp Λ c') : Supp Λ (c + c') :=
  fun y hy => by
    by_cases h1 : c (A.segmentOf y) = 0
    · simp only [Pi.add_apply, h1, zero_add] at hy; exact h' y hy
    · exact h y h1

theorem Norm.add {r r' : A.Cell → ZMod 2} (h : Norm Λ r) (h' : Norm Λ r') : Norm Λ (r + r') :=
  fun f hf => by simp only [Pi.add_apply, h f hf, h' f hf, add_zero]

/-- A lens has a cell outside `Q` (across its first `L`-dart). -/
theorem exists_not_Q : ∃ f, ¬ Λ.Q f := by
  obtain ⟨y₀, k, hk⟩ := Λ.L_run
  have hy : Λ.L y₀ := (hk y₀).2 ⟨0, Nat.zero_le _, by simp⟩
  exact ⟨_, (Λ.L_bd y₀ hy).2⟩

/-- **Normalized cut**: an even chain supported in the lens is cut by a function vanishing off
`Q`. -/
theorem exists_norm {c : A.Segment → ZMod 2} (hc : IsEven c) (hs : Supp Λ c) :
    ∃ r, IsCut c r ∧ Norm Λ r := by
  obtain ⟨r₀, hr₀⟩ := exists_cut hc
  have hconst : ∀ f g, ¬ Λ.Q f → ¬ Λ.Q g → r₀ f = r₀ g := by
    intro f g hf hg
    have key := Λ.compl_conn f g hf hg
    clear hf hg
    induction key with
    | rel a b h =>
      obtain ⟨y, ⟨hy1, hy2⟩, rfl, rfl⟩ := h
      have h0 : c (A.segmentOf y) = 0 := by
        by_contra hne
        rcases hs y hne with h | h
        · exact hy1 h
        · exact hy2 h
      rw [cut_α hr₀ y, h0, add_zero]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  obtain ⟨g, hg⟩ := exists_not_Q Λ
  refine ⟨fun f => r₀ f + r₀ g, fun y => ?_, fun f hf => ?_⟩
  · have h := hr₀ y
    have key : ∀ a b c : ZMod 2, a + c + (b + c) = a + b := by decide
    simp only [key, h]
  · show r₀ f + r₀ g = 0
    rw [hconst f g hf hg]; exact Arrangement.zmod2_add_self _

/-- Normalized cuts are unique. -/
theorem norm_unique {c : A.Segment → ZMod 2} {r r' : A.Cell → ZMod 2} (h : IsCut c r)
    (hn : Norm Λ r) (h' : IsCut c r') (hn' : Norm Λ r') : r = r' := by
  have h0 : IsCut 0 (r + r') := by
    have := h.add h'
    intro y
    have hy := this y
    simp only [Pi.add_apply] at hy ⊢
    rw [hy, Arrangement.zmod2_add_self]; rfl
  obtain ⟨g, hg⟩ := exists_not_Q Λ
  funext f
  have := const_of_cut_zero h0 f g
  simp only [Pi.add_apply, hn g hg, hn' g hg, add_zero] at this
  have key : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact key _ _ this

/-- The cell of an `R`-dart has normalized value `0` if the chain vanishes on its segment. -/
theorem norm_R {c : A.Segment → ZMod 2} {r : A.Cell → ZMod 2} (hr : IsCut c r) (hn : Norm Λ r)
    {u : D} (hu : Λ.R u) (h0 : c (A.segmentOf u) = 0) : r (A.cellOf u) = 0 := by
  have h1 := hr u
  rw [h0, hn _ (Λ.R_bd u hu).2, add_zero] at h1
  exact h1

/-- The cell of an `L`-dart has normalized value the chain value of its segment. -/
theorem norm_L {c : A.Segment → ZMod 2} {r : A.Cell → ZMod 2} (hr : IsCut c r) (hn : Norm Λ r)
    {u : D} (hu : Λ.L u) : r (A.cellOf u) = c (A.segmentOf u) := by
  have h1 := hr u
  rw [hn _ (Λ.L_bd u hu).2, add_zero] at h1
  exact h1

end Chain

end Pca.FlipGraph
