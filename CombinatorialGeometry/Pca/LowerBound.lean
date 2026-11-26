/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Lower bounds on the number of triangles (milestone 8)

Felsner, Scheucher, *Arrangements of pseudocircles: triangles and drawings*, DCG 2021
(https://arxiv.org/abs/1708.06449):

* `Arrangement.in_out` (`lem:in-out`, `n ≥ 3`): all digons incident to a pseudocircle `C` lie on
  the same side of `C` (no axiom),
* `Arrangement.two_le_tC` (`n ≥ 3`): every pseudocircle is incident to at least two triangles,
* `Arrangement.lower_bound_two_thirds` (`thm:2n_3_triangles`, `n ≥ 3`): `2n ≤ 3 p_3`,
* `Arrangement.sum_dtC`, `Arrangement.four_le_dtC`, `Arrangement.sh_bound`
  (Snoeyink-Hershberger, Lemma 4.1; FS2021 lines 176-180): `4n ≤ 2 p_2 + 3 p_3`,
* `Arrangement.lower_bound_digon_free`: digon-free implies `4n ≤ 3 p_3`,
* `TriangleConjecture` (`conj:general_lower`): `p_3 ≥ n - 1` for `n ≥ 3`, stated, **not proved**.

The bounds use the sweeping lemma `Arrangement.sweepFirstMove` (`Pca/SweepLemma.lean`, proved);
`in_out` and the counting lemmas do not.
-/
import Pca.SweepLemma

open Equiv Finset

namespace Pca.Arrangement

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (A : Arrangement n D)

/-! ## Walking along a curve -/

variable {A}

theorem curve_straight_iterate (k : ℕ) (d : D) : A.curve (A.straight^[k] d) = A.curve d := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', curve_straight, ih]

theorem sameCycle_straight_iterate (k : ℕ) (d : D) : A.straight.SameCycle d (A.straight^[k] d) := by
  rw [← Perm.coe_pow]; exact Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _)

/-- Within one period, the straight walk visits every crossing at most once. -/
theorem iterate_eq_of_crossingOf_eq {e : D} {a b : ℕ} (ha : a < period A.straight e)
    (hb : b < period A.straight e)
    (h : A.crossingOf (A.straight^[a] e) = A.crossingOf (A.straight^[b] e)) : a = b := by
  rcases A.eq_or_eq_σσ h (by rw [curve_straight_iterate, curve_straight_iterate]) with h' | h'
  · rw [period_eq_minimalPeriod] at ha hb
    exact ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hb ha).1 h').symm
  · exfalso
    refine A.not_sameCycle_straight_σσ (A.straight^[a] e) ?_
    rw [← h']
    exact ((sameCycle_straight_iterate a e).symm).trans (sameCycle_straight_iterate b e)

/-- A dart on the straight walk of `e` is `straight^[i] e` with `i` less than the period. -/
theorem exists_iterate_of_sameCycle {e w : D} (h : A.straight.SameCycle e w) :
    ∃ i < period A.straight e, A.straight^[i] e = w := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (mem_orbitList.2 h)
  exact ⟨i, List.mem_range.1 hi, rfl⟩

/-- **The far side of a digon.** Let the cell of `d` be a digon with `d` on `C`, and let `C'` be
the curve of its other side `φ d`. Then every dart `w` of `C'` at a crossing not on `C` lies on
the other side of `C` than the digon: `C'` meets `C` only at the two corners of the digon, and
walking along `C'` the side of `C` changes only there. -/
theorem side_far_of_digon {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s) {d : D}
    (hdC : A.curve d = C) (hD : A.IsDigon (A.cellOf d)) {w : D}
    (hw : A.curve w = A.curve (A.φ d)) (hwC : C ∉ Crossing.curves A (A.crossingOf w)) :
    s (A.cellOf w) = s (A.cellOf d) + 1 := by
  set d₂ := A.φ d with hd₂
  have hC' : A.curve d₂ ≠ C := hdC ▸ A.curve_φ_ne d
  have hφ : A.φ d₂ = d := A.φ_φ_of_digon hD
  set p := period A.straight d₂ with hp
  -- the two crossings of `C'` with `C`: `x₀` (start of `d₂`) and `x₁` (its end)
  have hx₀ : Crossing.curves A (A.crossingOf d₂) = {A.curve (A.φ d₂), A.curve d₂} := by
    conv_lhs => rw [hd₂, curves_crossingOf_φ, ← hd₂]
    rw [hφ, pair_comm]
  have hend : A.crossingOf (A.straight d₂) = A.crossingOf d := by
    rw [straight_apply, crossingOf_σσ, ← crossingOf_φ, hφ]
  have hx₁ : Crossing.curves A (A.crossingOf (A.straight d₂)) =
      {A.curve (A.φ d₂), A.curve d₂} := by
    rw [hend, ← hφ, curves_crossingOf_φ, hφ, pair_comm]
  have hne : A.crossingOf d₂ ≠ A.crossingOf (A.straight d₂) := by
    rw [hend]; exact A.crossingOf_φ_ne d
  rw [hφ, hdC] at hx₀ hx₁
  have hp1 : 1 < p := by
    have := A.two_mul_le_period_straight d₂
    have := A.two_le_n
    omega
  -- one step along `C'`
  have hstep : ∀ k, s (A.cellOf (A.straight^[k + 1] d₂)) = s (A.cellOf (A.straight^[k] d₂)) +
      if C ∈ Crossing.curves A (A.crossingOf (A.straight^[k + 1] d₂)) then 1 else 0 := by
    intro k
    have hk : A.curve (A.straight^[k] d₂) ≠ C := by rw [curve_straight_iterate]; exact hC'
    rw [Function.iterate_succ_apply', A.side_straight hs hk]
    congr 1
    rw [straight_apply, crossingOf_σσ]
    exact if_congr (A.mem_curves_end_iff hk).symm rfl rfl
  -- away from `x₀`, `x₁` the walk does not meet `C`
  have hoff : ∀ k, 2 ≤ k → k < p → C ∉ Crossing.curves A (A.crossingOf (A.straight^[k] d₂)) := by
    intro k hk2 hkp hC
    have hpair : Crossing.curves A (A.crossingOf (A.straight^[k] d₂)) = {C, A.curve d₂} :=
      A.curves_eq_pair hC (by rw [← curve_straight_iterate k d₂]; exact A.mem_curves_crossingOf _)
        hC'.symm
    rcases A.eq_or_eq_of_curves hC'.symm hx₀ hx₁ hpair hne with h | h
    · have := A.iterate_eq_of_crossingOf_eq (a := k) (b := 0) hkp (by omega) h
      omega
    · have := A.iterate_eq_of_crossingOf_eq (a := k) (b := 1) hkp hp1 h
      omega
  have hside : ∀ k, 1 ≤ k → k < p → s (A.cellOf (A.straight^[k] d₂)) = s (A.cellOf d) + 1 := by
    intro k hk1 hkp
    induction k with
    | zero => omega
    | succ k ih =>
      rw [hstep k]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [Function.iterate_one, if_pos (by rw [hx₁]; exact mem_insert_self _ _),
          Function.iterate_zero_apply, hd₂, cellOf_φ]
      · rw [ih hk (by omega), if_neg (hoff (k + 1) (by omega) hkp), add_zero]
  have hwC' : A.curve d₂ = A.curve w := hw.symm
  rcases A.isArrangement.straight d₂ w hwC' with h | h
  · obtain ⟨i, hi, rfl⟩ := exists_iterate_of_sameCycle h
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact absurd (by rw [Function.iterate_zero_apply, hx₀]; exact mem_insert_self _ _) hwC
    · exact hside i hi0 hi
  · obtain ⟨i, hi, hiw⟩ := exists_iterate_of_sameCycle h
    have hcr : A.crossingOf (A.σ (A.σ w)) = A.crossingOf w := A.crossingOf_σσ w
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [Function.iterate_zero_apply] at hiw
      exact absurd (by rw [← hcr, ← hiw, hx₀]; exact mem_insert_self _ _) hwC
    · have h1 := hside i hi0 hi
      rw [hiw] at h1
      have h2 := A.side_σσ hs (A.σ (A.σ w))
      rw [A.σ_σ_σ_σ] at h2
      have hc1 : A.curve (A.σ (A.σ w)) ≠ C := by
        rw [curve_σσ]; intro h; exact hwC (h ▸ A.mem_curves_crossingOf w)
      have hc2 : A.curve (A.σ (A.σ (A.σ w))) ≠ C := by
        intro h; apply hwC
        rw [← h, ← A.crossingOf_σσσ w]
        exact A.mem_curves_crossingOf _
      rw [h2, if_neg hc1, if_neg hc2, add_zero, add_zero, h1]

/-- Two distinct curves cross: there is a dart `w` with `curve w = c` and `curve (σ w) = c'`. -/
theorem exists_dart_crossing {c c' : Fin n} (h : c ≠ c') :
    ∃ w, A.curve w = c ∧ A.curve (A.σ w) = c' := by
  have hcard := A.isArrangement.intersecting c c' h
  obtain ⟨x, hx⟩ := card_pos.1 (show 0 < (univ.filter (fun x : A.Crossing =>
    Crossing.curves A x = {c, c'})).card by
      change 0 < (univ.filter (fun x : Orbit A.σ => crossingCurves A.σ A.curve x = {c, c'})).card
      rw [hcard]; norm_num)
  have hx' : Crossing.curves A x = {c, c'} := (mem_filter.1 hx).2
  obtain ⟨w₀, rfl⟩ := x.exists_mk
  have hw₀ : Crossing.curves A (A.crossingOf w₀) = {c, c'} := hx'
  have m0 := A.mem_curves_crossingOf w₀
  have m1 := A.mem_curves_crossingOf_σ w₀
  have hne := A.isArrangement.curve_σ w₀
  rw [hw₀, mem_insert, mem_singleton] at m0 m1
  rcases m0 with h0 | h0
  · refine ⟨w₀, h0, ?_⟩
    rcases m1 with h1 | h1
    · exact absurd (h1.trans h0.symm) hne
    · exact h1
  · refine ⟨A.σ w₀, ?_, by rw [curve_σσ, h0]⟩
    rcases m1 with h1 | h1
    · exact h1
    · exact absurd (h1.trans h0.symm) hne

/-- The crossing of a dart `w` with `curve w = c`, `curve (σ w) = c'` is not on a third curve. -/
theorem not_mem_curves_of_ne {w : D} {C : Fin n} (h1 : A.curve w ≠ C) (h2 : A.curve (A.σ w) ≠ C) :
    C ∉ Crossing.curves A (A.crossingOf w) := by
  rw [curves_crossingOf, mem_insert, mem_singleton, not_or]
  exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩

/-! ## `lem:in-out` -/

/-- **`lem:in-out`** (FS2021, `n ≥ 3`): all digons incident to a pseudocircle `C` lie on the same
side of `C`. If digons at `C` with other sides on `C'` and `C''` were on different sides of `C`,
then `C'` would lie on one side of `C` and `C''` on the other (except for the sides of the
digons, which are crossed by no curve), so `C'` and `C''` could not cross; if `C' = C''`, then
`C'` would have no crossing off `C`, but it crosses a third curve. -/
theorem in_out (hn : 3 ≤ n) {C : Fin n} {s : A.Cell → ZMod 2} (hs : A.IsSide C s)
    {g g' : A.Cell} (hg : A.IsDigon g) (hg' : A.IsDigon g')
    (hgC : ∃ d ∈ g.darts, A.curve d = C) (hg'C : ∃ d ∈ g'.darts, A.curve d = C) : s g = s g' := by
  obtain ⟨d, hd, hdC⟩ := hgC
  obtain ⟨e, he, heC⟩ := hg'C
  rw [← Orbit.mem_darts.1 hd] at hg ⊢
  rw [← Orbit.mem_darts.1 he] at hg' ⊢
  have hd' : A.curve (A.φ d) ≠ C := hdC ▸ A.curve_φ_ne d
  have he' : A.curve (A.φ e) ≠ C := heC ▸ A.curve_φ_ne e
  by_cases hCC : A.curve (A.φ d) = A.curve (A.φ e)
  · -- the same second curve: it crosses a third curve off `C`
    by_contra hne
    obtain ⟨c₃, hc₃⟩ : ∃ c₃ : Fin n, c₃ ≠ C ∧ c₃ ≠ A.curve (A.φ d) := by
      by_contra hcon
      push Not at hcon
      have hsub : (univ : Finset (Fin n)) ⊆ {C, A.curve (A.φ d)} := fun c _ => by
        rw [mem_insert, mem_singleton]
        by_cases hc : c = C
        · exact Or.inl hc
        · exact Or.inr (hcon c hc)
      have := card_le_card hsub
      rw [card_univ, Fintype.card_fin] at this
      have := card_insert_le C ({A.curve (A.φ d)} : Finset (Fin n))
      rw [card_singleton] at this
      omega
    obtain ⟨w, hw1, hw2⟩ := A.exists_dart_crossing hc₃.2.symm
    have hwC := A.not_mem_curves_of_ne (hw1 ▸ hd') (hw2 ▸ hc₃.1)
    have h1 := A.side_far_of_digon hs hdC hg hw1 hwC
    have h2 := A.side_far_of_digon hs heC hg' (hw1.trans hCC) hwC
    rw [h1] at h2
    exact hne (add_right_cancel h2)
  · obtain ⟨w, hw1, hw2⟩ := A.exists_dart_crossing hCC
    have hwC := A.not_mem_curves_of_ne (hw1 ▸ hd') (hw2 ▸ he')
    have h1 := A.side_far_of_digon hs hdC hg hw1 hwC
    have h2 := A.side_far_of_digon hs heC hg' hw2 (by rwa [crossingOf_σ])
    have h3 := A.side_σ hs w
    rw [if_neg (hw1 ▸ hd'), add_zero, h2, h1] at h3
    exact (add_right_cancel h3).symm

/-! ## `thm:2n_3_triangles` -/

/-- Every pseudocircle is incident to at least two triangles (`n ≥ 3`; FS2021, proof of
`thm:2n_3_triangles`): take the side of `C` without digons of `C` (`in_out`) and apply the
sweeping lemma twice. -/
theorem two_le_tC (hn : 3 ≤ n) (C : Fin n) : 2 ≤ A.tC C := by
  obtain ⟨s, hs⟩ := exists_isSide (A := A) C
  -- a side `b` of `C` that contains no digon incident to `C`
  obtain ⟨b, hb⟩ : ∃ b : ZMod 2, ∀ g, A.IsDigon g → (∃ d ∈ g.darts, A.curve d = C) → s g ≠ b := by
    by_cases hex : ∃ g, A.IsDigon g ∧ ∃ d ∈ g.darts, A.curve d = C
    · obtain ⟨g₀, hg₀, hg₀C⟩ := hex
      refine ⟨s g₀ + 1, fun g hg hgC h => ?_⟩
      rw [A.in_out hn hs hg hg₀ hgC hg₀C] at h
      have : (0 : ZMod 2) = 1 := by
        have := congrArg (· + s g₀) h
        simp [add_comm, ← add_assoc, zmod2_add_self] at this
      exact absurd this (by decide)
    · push Not at hex
      exact ⟨0, fun g hg ⟨d, hd, hdC⟩ _ => hex g hg d hd hdC⟩
  obtain ⟨y, -, hy⟩ := exists_dart_on_side hs b
  have tri : ∀ g, s g = b → (∃ d ∈ g.darts, A.curve d = C) → (A.IsDigon g ∨ A.IsTriangle g) →
      A.IsTriangle g := fun g h1 h2 h3 => h3.resolve_left fun h => hb g h h2 h1
  obtain ⟨g₁, -, hs₁, hC₁, hk₁⟩ := A.sweepFirstMove C s hs (A.cellOf y)
  obtain ⟨g₂, hne, hs₂, hC₂, hk₂⟩ := A.sweepFirstMove C s hs g₁
  have ht₁ := tri g₁ (hs₁.trans hy) hC₁ hk₁
  have ht₂ := tri g₂ (hs₂.trans (hs₁.trans hy)) hC₂ hk₂
  have hsub : ({g₁, g₂} : Finset A.Cell) ⊆
      A.triangles.filter (fun f => ∃ d ∈ f.darts, A.curve d = C) := by
    intro f hf
    rw [mem_insert, mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ht₁⟩, hC₁⟩
    · exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ht₂⟩, hC₂⟩
  have := card_le_card hsub
  rw [card_pair hne.symm] at this
  exact this

variable (A)

/-- **`thm:2n_3_triangles`** (FS2021): every intersecting arrangement of `n ≥ 3` pseudocircles has
at least `2n/3` triangles; integer form `2n ≤ 3 p_3`. -/
theorem lower_bound_two_thirds (hn : 3 ≤ n) : 2 * n ≤ 3 * A.p 3 := by
  rw [← sum_tC]
  calc 2 * n = ∑ _C : Fin n, 2 := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
        mul_comm]
    _ ≤ ∑ C : Fin n, A.tC C := sum_le_sum fun C _ => two_le_tC hn C

/-- `thm:2n_3_triangles` as stated: `p_3 ≥ 2n/3` (in `ℚ`). -/
theorem lower_bound_two_thirds_rat (hn : 3 ≤ n) : (2 * n : ℚ) / 3 ≤ A.p 3 := by
  have := A.lower_bound_two_thirds hn
  rw [div_le_iff₀ (by norm_num)]
  exact_mod_cast (by omega : 2 * n ≤ A.p 3 * 3)

/-! ## Snoeyink-Hershberger: `2 p_2 + 3 p_3 ≥ 4n` -/

/-- The number of digons and triangles incident to `C` (with a side on `C`). Counting helper. -/
def dtC (C : Fin n) : ℕ :=
  (univ.filter (fun f : A.Cell => (A.IsDigon f ∨ A.IsTriangle f) ∧
    ∃ d ∈ f.darts, A.curve d = C)).card

/-- `dtC C` is the number of darts on `C` whose cell is a digon or a triangle (the darts of such a
cell lie on distinct curves). -/
theorem dtC_eq_card_darts (C : Fin n) : A.dtC C =
    (univ.filter (fun d => A.curve d = C ∧ (A.IsDigon (A.cellOf d) ∨ A.IsTriangle (A.cellOf d)))).card := by
  rw [card_filter_eq_sum_orbits A.φ, dtC, card_filter]
  refine sum_congr rfl fun f _ => ?_
  symm
  have hf : ∀ d ∈ f.darts, A.cellOf d = f := fun d hd => Orbit.mem_darts.1 hd
  by_cases ht : A.IsDigon f ∨ A.IsTriangle f
  · rw [filter_congr (q := fun d => A.curve d = C) fun d hd => by simp [hf d hd, ht]]
    have hinj : Set.InjOn A.curve (f.darts : Set D) := by
      obtain ⟨a, rfl⟩ := A.exists_cellOf f
      refine A.injOn_curve ?_
      have := A.period_of_size (k := (A.cellOf a).size) rfl
      rcases ht with h | h <;> simp only [IsDigon, IsTriangle, IsKCell] at h <;> omega
    by_cases hC : ∃ d ∈ f.darts, A.curve d = C
    · rw [if_pos ⟨ht, hC⟩]
      obtain ⟨d, hd, hdC⟩ := hC
      refine le_antisymm (card_le_one.2 fun a ha b hb => ?_) (card_pos.2 ⟨d, by simp [hd, hdC]⟩)
      simp only [mem_filter] at ha hb
      exact hinj ha.1 hb.1 (ha.2.trans hb.2.symm)
    · rw [if_neg fun h => hC h.2, card_eq_zero, filter_eq_empty_iff]
      exact fun d hd hdC => hC ⟨d, hd, hdC⟩
  · rw [if_neg fun h => ht h.1, card_eq_zero, filter_eq_empty_iff]
    intro d hd h
    exact ht (hf d hd ▸ h.2)

/-- `∑_C dtC C = 2 p_2 + 3 p_3`: a digon is incident to two curves, a triangle to three. -/
theorem sum_dtC : ∑ C : Fin n, A.dtC C = 2 * A.p 2 + 3 * A.p 3 := by
  have h1 : ∑ C : Fin n, A.dtC C =
      (univ.filter (fun d => A.IsDigon (A.cellOf d) ∨ A.IsTriangle (A.cellOf d))).card := by
    rw [card_eq_sum_card_fiberwise (f := A.curve) (t := univ) (fun _ _ => mem_univ _)]
    refine sum_congr rfl fun C _ => ?_
    rw [dtC_eq_card_darts, filter_filter]
    congr 1
    ext d
    simp [and_comm]
  rw [h1, card_filter_eq_sum_orbits A.φ,
    sum_congr rfl fun f _ => A.card_filter_cell f (fun g => A.IsDigon g ∨ A.IsTriangle g)]
  have h2 : ∀ f : A.Cell, (if A.IsDigon f ∨ A.IsTriangle f then f.size else 0) =
      (if A.IsKCell 2 f then 2 else 0) + (if A.IsKCell 3 f then 3 else 0) := by
    intro f
    unfold IsDigon IsTriangle IsKCell
    by_cases h2 : f.size = 2 <;> by_cases h3 : f.size = 3 <;> simp [h2, h3]
  rw [sum_congr rfl fun f _ => h2 f, sum_add_distrib, ← sum_filter, ← sum_filter, sum_const,
    sum_const, smul_eq_mul, smul_eq_mul, p, p, mul_comm, mul_comm (card _) 3]

/-- Four digons or triangles are incident to every pseudocircle, two on each side (sweeping
lemma, SH91 form). -/
theorem four_le_dtC (C : Fin n) : 4 ≤ A.dtC C := by
  obtain ⟨s, hs⟩ := exists_isSide (A := A) C
  have h := A.sweepTwoCells C s hs
  have hsplit := card_filter_add_card_filter_not (s := univ.filter
    (fun f : A.Cell => (A.IsDigon f ∨ A.IsTriangle f) ∧ ∃ d ∈ f.darts, A.curve d = C))
    (fun f => s f = 0)
  have hside : ∀ b : ZMod 2, 2 ≤ ((univ.filter (fun f : A.Cell => (A.IsDigon f ∨ A.IsTriangle f) ∧
      ∃ d ∈ f.darts, A.curve d = C)).filter (fun f => s f = b)).card := by
    intro b
    obtain ⟨g₁, g₂, hne, h₁, h₂, ⟨c₁, k₁⟩, ⟨c₂, k₂⟩⟩ := h b
    exact one_lt_card.2 ⟨g₁, by simp [h₁, c₁, k₁], g₂, by simp [h₂, c₂, k₂], hne⟩
  have hneg : ((univ.filter (fun f : A.Cell => (A.IsDigon f ∨ A.IsTriangle f) ∧
      ∃ d ∈ f.darts, A.curve d = C)).filter (fun f => ¬ s f = 0)) =
      ((univ.filter (fun f : A.Cell => (A.IsDigon f ∨ A.IsTriangle f) ∧
      ∃ d ∈ f.darts, A.curve d = C)).filter (fun f => s f = 1)) := by
    refine filter_congr fun f _ => ?_
    generalize s f = a
    revert a; decide
  rw [hneg] at hsplit
  have := hside 0
  have := hside 1
  unfold dtC
  omega

/-- **Snoeyink-Hershberger, Lemma 4.1** (quoted in FS2021, lines 176-180): in every intersecting
arrangement `2 p_2 + 3 p_3 ≥ 4n`. -/
theorem sh_bound : 4 * n ≤ 2 * A.p 2 + 3 * A.p 3 := by
  rw [← sum_dtC]
  calc 4 * n = ∑ _C : Fin n, 4 := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
        mul_comm]
    _ ≤ ∑ C : Fin n, A.dtC C := sum_le_sum fun C _ => A.four_le_dtC C

/-- **Digon-free lower bound** (FS2021, lines 179-180, from SH91): every intersecting digon-free
arrangement has at least `4n/3` triangles; integer form `4n ≤ 3 p_3`. -/
theorem lower_bound_digon_free (h : A.p 2 = 0) : 4 * n ≤ 3 * A.p 3 := by
  have := A.sh_bound
  omega

/-- The digon-free lower bound as stated: `p_3 ≥ 4n/3` (in `ℚ`). -/
theorem lower_bound_digon_free_rat (h : A.p 2 = 0) : (4 * n : ℚ) / 3 ≤ A.p 3 := by
  have := A.lower_bound_digon_free h
  rw [div_le_iff₀ (by norm_num)]
  exact_mod_cast (by omega : 4 * n ≤ A.p 3 * 3)

end Pca.Arrangement

namespace Pca

universe u

/-- **Conjecture `conj:general_lower`** (FS2021, lines 700-703): "Every intersecting arrangement of
`n ≥ 3` pseudocircles has at least `n - 1` triangles." (Simple arrangements, as everywhere in
FS2021, line 163.) **Open**: stated as a `Prop`, neither proved nor assumed. True for `n ≤ 7` by
the enumeration of FS2021 (line 697); on the test instances it holds with equality for line 1 of
`all3.txt` and line 3 of `all4.txt`. -/
def TriangleConjecture : Prop :=
  ∀ (n : ℕ) (D : Type u) [Fintype D] [DecidableEq D] (A : Arrangement n D), 3 ≤ n → n - 1 ≤ A.p 3

end Pca
