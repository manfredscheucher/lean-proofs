/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): the walk along a curve of `𝒜_n^-`

For a canonical arrangement (`Marked.CanonUpTo c n`) and a curve `c i`, walk along `c i` with the
cells outside `c i` on the right. The **height** of a cell is the number of curves `c l`, `l > i`,
containing it minus the number of curves `c l`, `l < i`, containing it. At the crossing with
`c j` the two cells to the right (before and after) are inside exactly the curves strictly
between `c i` and `c j`, and one of them also inside `c j` (the side condition of `Canon`); so the
height changes by `±1` and determines `j`. The height lies in `[-i, n-1-i]`, both ends are
attained, and a period has `2 (n-1)` steps: so the walk goes straight up from `-i` to `n-1-i` and
straight down again (`walk_canon`). This fixes the crossing sequence along every curve
(`labF`, `flagF`): the arcs are nested (`doc/pca/flipgraph.md`, F-D7).
-/
import Pca.FlipGraph.Order
import Pca.Great.Basic

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- The label of the `s`-th crossing along the curve with index `i` in `𝒜_n^-` (from the base dart
after the lowest cell). -/
def labF (n i s : ℕ) : ℕ :=
  if s < n - 1 then (if s < i then s else s + 1)
  else (if i < 2 * n - 2 - s then 2 * n - 2 - s else 2 * n - 3 - s)

/-- Whether after the `s`-th crossing the walk is inside the crossed curve. -/
def flagF (n i s : ℕ) : Bool :=
  if s < n - 1 then decide (i < labF n i s) else decide (labF n i s < i)

/-- The height of the cell after the `s`-th step. -/
def hgtF (n i s : ℕ) : ℤ :=
  if s ≤ n - 1 then (s : ℤ) - i else (2 * (n - 1) : ℕ) - (s : ℤ) - i

open Classical in
/-- The height of a cell w.r.t. the curve `c i`. -/
noncomputable def Marked.hgt (M : Marked n D) (c : Fin n ≃ Fin n) (i : Fin n) (f : M.A.Cell) :
    ℤ :=
  ((univ.filter (fun l : Fin n => i < l ∧ M.Inside (c l) f)).card : ℤ) -
    (univ.filter (fun l : Fin n => l < i ∧ M.Inside (c l) f)).card

open Classical in
theorem card_between (i j : Fin n) (hij : i ≠ j) (P : Fin n → Prop)
    (hP : ∀ l, l ≠ i → l ≠ j → (P l ↔ (i < l ∧ l < j ∨ j < l ∧ l < i))) :
    (((univ.filter (fun l => i < l ∧ P l)).card : ℤ) - (univ.filter (fun l => l < i ∧ P l)).card)
      = if i < j then ((j : ℕ) : ℤ) - (i : ℕ) - 1 + (if P j then 1 else 0)
        else ((j : ℕ) : ℤ) - (i : ℕ) + 1 - (if P j then 1 else 0) := by
  have hPj : ∀ l, l = j → (P l ↔ P j) := fun l h => by rw [h]
  rcases lt_or_gt_of_ne hij with h | h
  · rw [if_pos h]
    have e1 : univ.filter (fun l => i < l ∧ P l) =
        Ioo i j ∪ univ.filter (fun l => l = j ∧ P j) := by
      ext l
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_Ioo]
      by_cases hl : l = j
      · subst hl; simp [h]
      by_cases hli : l = i
      · subst hli; simp [hl]
      rw [hP l hli hl]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact Or.inl h2
        · exact absurd (h2.2.trans h1) (lt_irrefl _)
      · rintro (h2 | h2)
        · exact ⟨h2.1, Or.inl h2⟩
        · exact absurd h2.1 hl
    have e2 : univ.filter (fun l => l < i ∧ P l) = ∅ := by
      ext l
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
      intro hl hp
      have hli : l ≠ i := ne_of_lt hl
      have hlj : l ≠ j := ne_of_lt (hl.trans h)
      rcases (hP l hli hlj).1 hp with h2 | h2
      · exact lt_asymm hl h2.1
      · exact lt_asymm (hl.trans h) h2.1
    have hd : Disjoint (Ioo i j) (univ.filter (fun l => l = j ∧ P j)) := by
      rw [disjoint_left]
      intro l hl hl'
      simp only [mem_filter, mem_univ, true_and] at hl'
      rw [mem_Ioo, hl'.1] at hl
      exact lt_irrefl _ hl.2
    rw [e1, e2, card_union_of_disjoint hd, Fin.card_Ioo, card_empty]
    have : (univ.filter (fun l => l = j ∧ P j)).card = if P j then 1 else 0 := by
      by_cases hp : P j
      · rw [if_pos hp]
        rw [show univ.filter (fun l => l = j ∧ P j) = {j} by ext l; simp [hp]]
        rfl
      · rw [if_neg hp]
        rw [show univ.filter (fun l => l = j ∧ P j) = ∅ by ext l; simp [hp]]
        rfl
    rw [this]
    have hv : (i : ℕ) < j := h
    split_ifs <;> push_cast <;> omega
  · have hn : ¬ i < j := not_lt.2 h.le
    rw [if_neg hn]
    have e1 : univ.filter (fun l => l < i ∧ P l) =
        Ioo j i ∪ univ.filter (fun l => l = j ∧ P j) := by
      ext l
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_Ioo]
      by_cases hl : l = j
      · subst hl; simp [h]
      by_cases hli : l = i
      · subst hli; simp [hl]
      rw [hP l hli hl]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact absurd (h1.trans h2.1) (lt_irrefl _)
        · exact Or.inl h2
      · rintro (h2 | h2)
        · exact ⟨h2.2, Or.inr h2⟩
        · exact absurd h2.1 hl
    have e2 : univ.filter (fun l => i < l ∧ P l) = ∅ := by
      ext l
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
      intro hl hp
      have hli : l ≠ i := ne_of_gt hl
      have hlj : l ≠ j := ne_of_gt (h.trans hl)
      rcases (hP l hli hlj).1 hp with h2 | h2
      · exact lt_asymm (h.trans hl) h2.2
      · exact lt_asymm hl h2.2
    have hd : Disjoint (Ioo j i) (univ.filter (fun l => l = j ∧ P j)) := by
      rw [disjoint_left]
      intro l hl hl'
      simp only [mem_filter, mem_univ, true_and] at hl'
      rw [mem_Ioo, hl'.1] at hl
      exact lt_irrefl _ hl.1
    rw [e1, e2, card_union_of_disjoint hd, Fin.card_Ioo, card_empty]
    have : (univ.filter (fun l => l = j ∧ P j)).card = if P j then 1 else 0 := by
      by_cases hp : P j
      · rw [if_pos hp]
        rw [show univ.filter (fun l => l = j ∧ P j) = {j} by ext l; simp [hp]]
        rfl
      · rw [if_neg hp]
        rw [show univ.filter (fun l => l = j ∧ P j) = ∅ by ext l; simp [hp]]
        rfl
    rw [this]
    have hv : (j : ℕ) < i := h
    split_ifs <;> push_cast <;> omega

theorem Marked.hgt_bounds (M : Marked n D) (c : Fin n ≃ Fin n) (i : Fin n) (f : M.A.Cell) :
    -((i : ℕ) : ℤ) ≤ M.hgt c i f ∧ M.hgt c i f ≤ (n : ℤ) - 1 - (i : ℕ) := by
  classical
  have h1 : (univ.filter (fun l : Fin n => i < l ∧ M.Inside (c l) f)).card ≤ n - 1 - i := by
    rw [← Fin.card_Ioi]
    exact card_le_card (fun l hl => by simp only [mem_filter] at hl; simpa using hl.2.1)
  have h2 : (univ.filter (fun l : Fin n => l < i ∧ M.Inside (c l) f)).card ≤ i := by
    rw [← Fin.card_Iio]
    exact card_le_card (fun l hl => by simp only [mem_filter] at hl; simpa using hl.2.1)
  have hi := i.isLt
  unfold Marked.hgt
  omega

section Walk

variable (M : Marked n D) (c : Fin n ≃ Fin n) (hcan : M.CanonUpTo c n) {i : Fin n} {y : D}
  (hy : M.A.curve y = c i) (hout : ¬ M.Inside (c i) (M.A.cellOf y))

include hy hout in
/-- The cells to the right of the walk are outside `c i`. -/
theorem CanonWalk.out (k : ℕ) : ¬ M.Inside (c i) (M.A.cellOf ((M.A.straight ^ k) y)) := by
  induction k with
  | zero => simpa using hout
  | succ k ih =>
    rw [Order.in_succ]
    have := Order.nx_ne M hy k
    tauto

include hcan hy in
/-- One step of the walk: the crossed curve `c j` and the heights before and after. -/
theorem CanonWalk.step (k : ℕ) : ∃ j : Fin n, j ≠ i ∧
    c j = M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ k) y))) ∧
    (i < j → ((M.Inside (c j) (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) ∧
        M.hgt c i (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) = (j : ℕ) - (i : ℕ) ∧
        M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j : ℕ) - (i : ℕ) - 1) ∨
      (¬ M.Inside (c j) (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) ∧
        M.hgt c i (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) = (j : ℕ) - (i : ℕ) - 1 ∧
        M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j : ℕ) - (i : ℕ)))) ∧
    (j < i → ((M.Inside (c j) (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) ∧
        M.hgt c i (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) = (j : ℕ) - (i : ℕ) ∧
        M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j : ℕ) - (i : ℕ) + 1) ∨
      (¬ M.Inside (c j) (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) ∧
        M.hgt c i (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) = (j : ℕ) - (i : ℕ) + 1 ∧
        M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j : ℕ) - (i : ℕ)))) := by
  classical
  set x := M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ k) y))) with hx
  set j := c.symm x with hj
  have hcj : c j = x := by rw [hj, Equiv.apply_symm_apply]
  have hji : j ≠ i := fun h => Order.nx_ne M hy k (by rw [← hx, ← hcj, h])
  -- interior status at the crossing
  have hbet : ∀ l, l ≠ i → l ≠ j →
      (M.Inside (c l) (M.A.cellOf ((M.A.straight ^ k) y)) ↔ (i < l ∧ l < j ∨ j < l ∧ l < i)) := by
    intro l hli hlj
    have hb : c l ≠ c i := fun h => hli (c.injective h)
    have hxl : x ≠ c l := fun h => hlj (by rw [hj, h, Equiv.symm_apply_apply])
    rw [← Order.cross_x M hy hb hxl]
    have hcur := Order.curves_x M hy k
    rw [← hx, ← hcj] at hcur
    rcases lt_or_gt_of_ne hji with h | h
    · have := hcan l j i hlj hli h (Or.inl l.isLt) _ (by rw [hcur, pair_comm])
      rw [this]
      constructor
      · intro h'; exact Or.inr h'
      · rintro (h' | h')
        · exact absurd (h'.1.trans h'.2) (lt_asymm h)
        · exact h'
    · have := hcan l i j hli hlj h (Or.inl l.isLt) _ hcur
      rw [this]
      constructor
      · intro h'; exact Or.inl h'
      · rintro (h' | h')
        · exact h'
        · exact absurd (h'.1.trans h'.2) (lt_asymm h)
  have hsucc : ∀ l : Fin n, (M.Inside (c l) (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) ↔
      (M.Inside (c l) (M.A.cellOf ((M.A.straight ^ k) y)) ↔ l ≠ j)) := by
    intro l
    rw [Order.in_succ, ← hx]
    have : x ≠ c l ↔ l ≠ j := by
      constructor
      · intro h h'; exact h (by rw [h', hcj])
      · intro h h'; exact h (by rw [hj, h', Equiv.symm_apply_apply])
    rw [this]
  have hbet' : ∀ l, l ≠ i → l ≠ j →
      (M.Inside (c l) (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) ↔
        (i < l ∧ l < j ∨ j < l ∧ l < i)) := by
    intro l hli hlj
    rw [hsucc l, ← hbet l hli hlj]
    simp [hlj]
  have hj' : M.Inside (c j) (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) ↔
      ¬ M.Inside (c j) (M.A.cellOf ((M.A.straight ^ k) y)) := by
    rw [hsucc j]; simp
  have e0 := card_between i j (Ne.symm hji) _ hbet
  have e1 := card_between i j (Ne.symm hji) _ hbet'
  have h0 : M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = _ := e0
  have h1 : M.hgt c i (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) = _ := e1
  refine ⟨j, hji, hcj, fun hij => ?_, fun hij => ?_⟩
  · rw [if_pos hij] at h0 h1
    by_cases hin : M.Inside (c j) (M.A.cellOf ((M.A.straight ^ (k + 1)) y))
    · have hin' := hj'.1 hin
      rw [if_pos hin] at h1; rw [if_neg hin'] at h0
      exact Or.inl ⟨hin, by rw [h1]; ring, by rw [h0]; ring⟩
    · have hin' : M.Inside (c j) (M.A.cellOf ((M.A.straight ^ k) y)) := by tauto
      rw [if_neg hin] at h1; rw [if_pos hin'] at h0
      exact Or.inr ⟨hin, by rw [h1]; ring, by rw [h0]; ring⟩
  · rw [if_neg (not_lt.2 hij.le)] at h0 h1
    by_cases hin : M.Inside (c j) (M.A.cellOf ((M.A.straight ^ (k + 1)) y))
    · have hin' := hj'.1 hin
      rw [if_pos hin] at h1; rw [if_neg hin'] at h0
      exact Or.inl ⟨hin, by rw [h1]; ring, by rw [h0]; ring⟩
    · have hin' : M.Inside (c j) (M.A.cellOf ((M.A.straight ^ k) y)) := by tauto
      rw [if_neg hin] at h1; rw [if_pos hin'] at h0
      exact Or.inr ⟨hin, by rw [h1]; ring, by rw [h0]; ring⟩


omit hcan in
theorem CanonWalk.period (k : ℕ) :
    (M.A.straight ^ (k + 2 * (n - 1))) y = (M.A.straight ^ k) y := by
  rw [pow_add, Perm.mul_apply, Great.straight_pow_period]

theorem CanonWalk.period_mul (k t : ℕ) :
    (M.A.straight ^ (k + 2 * (n - 1) * t)) y = (M.A.straight ^ k) y := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← add_assoc, CanonWalk.period, ih]

include hcan hy in
/-- The height changes by at most one per step. -/
theorem CanonWalk.lip (a t : ℕ) :
    M.hgt c i (M.A.cellOf ((M.A.straight ^ a) y)) - t ≤
        M.hgt c i (M.A.cellOf ((M.A.straight ^ (a + t)) y)) ∧
      M.hgt c i (M.A.cellOf ((M.A.straight ^ (a + t)) y)) ≤
        M.hgt c i (M.A.cellOf ((M.A.straight ^ a) y)) + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨j, hji, -, h1, h2⟩ := CanonWalk.step M c hcan hy (a + t)
    rw [show a + (t + 1) = a + t + 1 by omega, Nat.cast_succ]
    rcases lt_or_gt_of_ne hji with h | h
    · rcases h2 h with h3 | h3 <;> omega
    · rcases h1 h with h3 | h3 <;> omega

include hy in
theorem CanonWalk.exists_cross {j₀ : Fin n} (h : j₀ ≠ i) :
    ∃ k, c j₀ = M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ k) y))) := by
  have hd : M.A.curve y ≠ c j₀ := fun h' => h (c.injective (hy.symm.trans h')).symm
  obtain ⟨k, hk⟩ := card_pos.1 (show 0 < (Walk.flipsOn M.A (c j₀) y).card by
    rw [Walk.card_flipsOn M.A hd]; omega)
  exact ⟨k, ((Walk.mem_flipsOn M.A).1 hk).2.symm⟩

include hcan hy in
theorem CanonWalk.hgt_at {j₀ : Fin n} (h : j₀ ≠ i) : ∃ k,
    (i < j₀ → (M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j₀ : ℕ) - (i : ℕ) - 1 ∨
      M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j₀ : ℕ) - (i : ℕ))) ∧
    (j₀ < i → (M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j₀ : ℕ) - (i : ℕ) + 1 ∨
      M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j₀ : ℕ) - (i : ℕ))) ∧
    (i < j₀ → (M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j₀ : ℕ) - (i : ℕ) - 1 ∨
      M.hgt c i (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) = (j₀ : ℕ) - (i : ℕ) - 1)) ∧
    (i < j₀ → (M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j₀ : ℕ) - (i : ℕ) ∨
      M.hgt c i (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) = (j₀ : ℕ) - (i : ℕ))) ∧
    (j₀ < i → (M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j₀ : ℕ) - (i : ℕ) + 1 ∨
      M.hgt c i (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) = (j₀ : ℕ) - (i : ℕ) + 1)) ∧
    (j₀ < i → (M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) = (j₀ : ℕ) - (i : ℕ) ∨
      M.hgt c i (M.A.cellOf ((M.A.straight ^ (k + 1)) y)) = (j₀ : ℕ) - (i : ℕ))) := by
  obtain ⟨k, hk⟩ := CanonWalk.exists_cross M c hy h
  obtain ⟨j, -, hcj, h1, h2⟩ := CanonWalk.step M c hcan hy k
  have hj : j = j₀ := c.injective (hcj.trans hk.symm)
  subst hj
  refine ⟨k, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_, fun h' => ?_⟩
  · rcases h1 h' with h3 | h3 <;> omega
  · rcases h2 h' with h3 | h3 <;> omega
  · rcases h1 h' with h3 | h3 <;> omega
  · rcases h1 h' with h3 | h3 <;> omega
  · rcases h2 h' with h3 | h3 <;> omega
  · rcases h2 h' with h3 | h3 <;> omega

include hcan hy in
/-- The heights along the walk from the lowest cell: straight up, then straight down. -/
theorem CanonWalk.geodesic : ∃ k₀, ∀ s, s ≤ 2 * (n - 1) →
    M.hgt c i (M.A.cellOf ((M.A.straight ^ (k₀ + s)) y)) = hgtF n i s := by
  have hn := M.A.two_le_n
  have hi := i.isLt
  set H : ℕ → ℤ := fun k => M.hgt c i (M.A.cellOf ((M.A.straight ^ k) y)) with hH
  have lip : ∀ a t, H a - t ≤ H (a + t) ∧ H (a + t) ≤ H a + t := CanonWalk.lip M c hcan hy
  have per : ∀ k t, H (k + 2 * (n - 1) * t) = H k := fun k t => by
    simp only [hH, CanonWalk.period_mul]
  have bnd : ∀ k, -((i : ℕ) : ℤ) ≤ H k ∧ H k ≤ (n : ℤ) - 1 - (i : ℕ) := fun k =>
    M.hgt_bounds c i _
  -- the lowest height `-i` is attained
  obtain ⟨k₀, hk₀⟩ : ∃ k, H k = -((i : ℕ) : ℤ) := by
    by_cases hi0 : (i : ℕ) = 0
    · have h1 : (⟨1, by omega⟩ : Fin n) ≠ i := fun h => by rw [← h] at hi0; simp at hi0
      obtain ⟨k, -, -, h3, -⟩ := CanonWalk.hgt_at M c hcan hy h1
      have hlt : i < ⟨1, by omega⟩ := by change (i : ℕ) < 1; omega
      rcases h3 hlt with h | h
      · exact ⟨k, by simp only [hH]; rw [h]; simp [hi0]⟩
      · exact ⟨k + 1, by simp only [hH]; rw [h]; simp [hi0]⟩
    · have h1 : (⟨0, by omega⟩ : Fin n) ≠ i := fun h => by rw [← h] at hi0; simp at hi0
      obtain ⟨k, -, -, -, -, -, h3⟩ := CanonWalk.hgt_at M c hcan hy h1
      have hlt : (⟨0, by omega⟩ : Fin n) < i := by change 0 < (i : ℕ); omega
      rcases h3 hlt with h | h
      · exact ⟨k, by simp only [hH]; rw [h]; simp⟩
      · exact ⟨k + 1, by simp only [hH]; rw [h]; simp⟩
  -- the highest height `n-1-i` is attained
  obtain ⟨k₁, hk₁⟩ : ∃ k, H k = (n : ℤ) - 1 - (i : ℕ) := by
    by_cases hin : (i : ℕ) = n - 1
    · have h1 : (⟨n - 2, by omega⟩ : Fin n) ≠ i := fun h => by
        rw [← h] at hin; simp at hin; omega
      obtain ⟨k, -, -, -, -, h3, -⟩ := CanonWalk.hgt_at M c hcan hy h1
      have hlt : (⟨n - 2, by omega⟩ : Fin n) < i := by change n - 2 < (i : ℕ); omega
      rcases h3 hlt with h | h
      · exact ⟨k, by simp only [hH]; rw [h]; push_cast; omega⟩
      · exact ⟨k + 1, by simp only [hH]; rw [h]; push_cast; omega⟩
    · have h1 : (⟨n - 1, by omega⟩ : Fin n) ≠ i := fun h => by rw [← h] at hin; simp at hin
      obtain ⟨k, -, -, -, h3, -⟩ := CanonWalk.hgt_at M c hcan hy h1
      have hlt : i < ⟨n - 1, by omega⟩ := by change (i : ℕ) < n - 1; omega
      rcases h3 hlt with h | h
      · exact ⟨k, by simp only [hH]; rw [h]; push_cast; omega⟩
      · exact ⟨k + 1, by simp only [hH]; rw [h]; push_cast; omega⟩
  -- move `k₁` into `[k₀, k₀ + 2 (n-1))`
  obtain ⟨d, hd, hkd⟩ : ∃ d, d < 2 * (n - 1) ∧ H (k₀ + d) = (n : ℤ) - 1 - (i : ℕ) := by
    have hP : 0 < 2 * (n - 1) := by omega
    refine ⟨(k₁ + 2 * (n - 1) * k₀ - k₀) % (2 * (n - 1)), Nat.mod_lt _ hP, ?_⟩
    have e := Nat.div_add_mod (k₁ + 2 * (n - 1) * k₀ - k₀) (2 * (n - 1))
    have hle : k₀ ≤ 2 * (n - 1) * k₀ := Nat.le_mul_of_pos_left _ hP
    rw [← per (k₀ + _) ((k₁ + 2 * (n - 1) * k₀ - k₀) / (2 * (n - 1))),
      show k₀ + (k₁ + 2 * (n - 1) * k₀ - k₀) % (2 * (n - 1)) +
        2 * (n - 1) * ((k₁ + 2 * (n - 1) * k₀ - k₀) / (2 * (n - 1))) = k₁ + 2 * (n - 1) * k₀ by
        omega, per, hk₁]
  have hPk : H (k₀ + 2 * (n - 1)) = -((i : ℕ) : ℤ) := by
    have := per k₀ 1; rw [mul_one] at this; rw [this, hk₀]
  have hdm : d = n - 1 := by
    have l1 := (lip k₀ d).2
    have l2 := (lip (k₀ + d) (2 * (n - 1) - d)).1
    rw [show k₀ + d + (2 * (n - 1) - d) = k₀ + 2 * (n - 1) by omega, hPk] at l2
    push_cast [Nat.cast_sub hd.le] at l2
    omega
  subst hdm
  refine ⟨k₀, fun s hs => ?_⟩
  unfold hgtF
  split_ifs with h
  · have l1 := (lip k₀ s).2
    have l2 := (lip (k₀ + s) (n - 1 - s)).2
    rw [show k₀ + s + (n - 1 - s) = k₀ + (n - 1) by omega] at l2
    push_cast [Nat.cast_sub h] at l2
    change H (k₀ + s) = _
    omega
  · have l1 := (lip (k₀ + (n - 1)) (s - (n - 1))).1
    rw [show k₀ + (n - 1) + (s - (n - 1)) = k₀ + s by omega] at l1
    have l2 := (lip (k₀ + s) (2 * (n - 1) - s)).1
    rw [show k₀ + s + (2 * (n - 1) - s) = k₀ + 2 * (n - 1) by omega, hPk] at l2
    push_cast [Nat.cast_sub hs, Nat.cast_sub (show n - 1 ≤ s by omega)] at l1 l2
    change H (k₀ + s) = _
    push_cast
    omega

end Walk

/-- **The walk along a curve of `𝒜_n^-`**: from a suitable base dart on `c i` (cells outside `c i`
on the right), the `s`-th crossing is with `c (labF n i s)`, afterwards the walk is inside that
curve iff `flagF n i s`, and the cell after the `s`-th step has height `hgtF n i (s + 1)`. -/
theorem walk_canon (M : Marked n D) (c : Fin n ≃ Fin n) (hcan : M.CanonUpTo c n) (i : Fin n) : ∃ y', M.A.curve y' = c i ∧
    (∀ k, ¬ M.Inside (c i) (M.A.cellOf ((M.A.straight ^ k) y'))) ∧
    ∀ s, s < 2 * (n - 1) →
      ((c.symm (M.A.curve (M.A.σ ((M.A.straight ^ s) y')))) : ℕ) = labF n i s ∧
      (M.Inside (M.A.curve (M.A.σ ((M.A.straight ^ s) y'))) (M.A.cellOf ((M.A.straight ^ s) y'))
        ↔ flagF n i s = true) ∧
      M.hgt c i (M.A.cellOf ((M.A.straight ^ s) y')) = hgtF n i (s + 1) := by
  obtain ⟨y, hy, hout⟩ : ∃ y, M.A.curve y = c i ∧ ¬ M.Inside (c i) (M.A.cellOf y) := by
    obtain ⟨d, hd⟩ := M.A.exists_dart_on (c i)
    by_cases h : M.Inside (c i) (M.A.cellOf d)
    · refine ⟨M.A.α d, by rw [M.A.curve_α, hd], ?_⟩
      rw [M.inside_α, hd]; simpa using h
    · exact ⟨d, hd, h⟩
  obtain ⟨k₀, hk₀⟩ := CanonWalk.geodesic M c hcan hy
  have shift : ∀ k, (M.A.straight ^ k) ((M.A.straight ^ (k₀ + 1)) y) =
      (M.A.straight ^ (k₀ + k + 1)) y := fun k => by
    rw [← Perm.mul_apply, ← pow_add, show k + (k₀ + 1) = k₀ + k + 1 by omega]
  refine ⟨(M.A.straight ^ (k₀ + 1)) y, by rw [Walk.curve_pow, hy], fun k => ?_, fun s hs => ?_⟩
  · rw [shift]; exact CanonWalk.out M c hy hout _
  have hn := M.A.two_le_n
  have hi := i.isLt
  obtain ⟨j, hji, hcj, h1, h2⟩ := CanonWalk.step M c hcan hy (k₀ + s)
  have hσ : M.A.curve (M.A.σ ((M.A.straight ^ (k₀ + s + 1)) y)) =
      M.A.curve (M.A.σ (M.A.α ((M.A.straight ^ (k₀ + s)) y))) := by
    rw [Walk.pow_succ_apply, M.A.straight_apply, M.A.isArrangement.curve_σσ]
  rw [shift, hσ, ← hcj, Equiv.symm_apply_apply]
  have g0 := hk₀ s (by omega)
  have g1 := hk₀ (s + 1) (by omega)
  rw [show k₀ + (s + 1) = k₀ + s + 1 by omega] at g1
  have hv : (j : ℕ) ≠ i := Fin.val_ne_of_ne hji
  refine ⟨?_, ?_, g1⟩
  · rcases lt_or_gt_of_ne (Ne.symm hji) with h | h
    · have h' : (i : ℕ) < j := h
      unfold hgtF at g0 g1
      rcases h1 h with ⟨-, ha, hb⟩ | ⟨-, ha, hb⟩ <;> rw [ha] at g1 <;> rw [hb] at g0 <;>
        unfold labF <;> split_ifs at g0 g1 ⊢ <;> omega
    · have h' : (j : ℕ) < i := h
      unfold hgtF at g0 g1
      rcases h2 h with ⟨-, ha, hb⟩ | ⟨-, ha, hb⟩ <;> rw [ha] at g1 <;> rw [hb] at g0 <;>
        unfold labF <;> split_ifs at g0 g1 ⊢ <;> omega
  · rcases lt_or_gt_of_ne (Ne.symm hji) with h | h
    · have h' : (i : ℕ) < j := h
      unfold hgtF at g0 g1
      rcases h1 h with ⟨hin, ha, hb⟩ | ⟨hin, ha, hb⟩ <;> rw [ha] at g1 <;> rw [hb] at g0 <;>
        simp only [hin, true_iff, false_iff] <;> unfold flagF labF <;>
        split_ifs at g0 g1 ⊢ <;> simp <;> omega
    · have h' : (j : ℕ) < i := h
      unfold hgtF at g0 g1
      rcases h2 h with ⟨hin, ha, hb⟩ | ⟨hin, ha, hb⟩ <;> rw [ha] at g1 <;> rw [hb] at g0 <;>
        simp only [hin, true_iff, false_iff] <;> unfold flagF labF <;>
        split_ifs at g0 g1 ⊢ <;> simp <;> omega

end Pca.FlipGraph
