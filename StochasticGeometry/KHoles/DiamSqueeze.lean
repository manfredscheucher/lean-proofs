/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import KHoles.HullMeasurable
import KHoles.ConvexInvariance
import KHoles.Symmetrize

/-!
# Squeezing `emptyProb` between diameter-restricted integrals

Step 3 of `doc/kholes/kholes.md` (wave 2, §3.2 `DiamSqueeze.lean`). For `k = m + 2`
points and `q : Fin k → ℝ × ℝ`, count ordered pairs `(i, j)` with `i ≠ j`:

* at least two of them are weak diameter pairs (`IsDiamLE 1 q i j`): a maximising pair and its
  reverse;
* at most two of them are strict diameter pairs (`IsDiamLT 1 q i j`).

Every pair contributes the same integral as the pair `(0, 1)` (permute the coordinates by a
`σ` with `σ 0 = i`, `σ 1 = j`; convex independence and the hull area are permutation
invariant). Since there are `k (k - 1)` ordered pairs:

* `two_mul_emptyProb_le : 2 · emptyProb ≤ k(k-1) · diamProb_LE`,
* `diamProb_lt_le : k(k-1) · diamProb_LT ≤ 2 · emptyProb`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### Diameter events under permutations -/

lemma isDiamLE_comp_perm {k : ℕ} (c : ℝ) (q : Fin k → ℝ × ℝ) (σ : Equiv.Perm (Fin k))
    (i j : Fin k) : IsDiamLE c (q ∘ σ) i j ↔ IsDiamLE c q (σ i) (σ j) := by
  constructor
  · intro h a b
    have := h (σ.symm a) (σ.symm b)
    simpa using this
  · intro h a b
    exact h (σ a) (σ b)

lemma isDiamLT_comp_perm {k : ℕ} (c : ℝ) (q : Fin k → ℝ × ℝ) (σ : Equiv.Perm (Fin k))
    (i j : Fin k) : IsDiamLT c (q ∘ σ) i j ↔ IsDiamLT c q (σ i) (σ j) := by
  constructor
  · intro h a b hab h1 h2
    have := h (σ.symm a) (σ.symm b) (by simpa using hab)
      (by intro e; apply h1; simp only [Prod.mk.injEq] at e ⊢
          exact ⟨by rw [← e.1]; simp, by rw [← e.2]; simp⟩)
      (by intro e; apply h2; simp only [Prod.mk.injEq] at e ⊢
          exact ⟨by rw [← e.1]; simp, by rw [← e.2]; simp⟩)
    simpa using this
  · intro h a b hab h1 h2
    exact h (σ a) (σ b) (σ.injective.ne hab)
      (by intro e; apply h1; simp only [Prod.mk.injEq] at e ⊢
          exact ⟨σ.injective e.1, σ.injective e.2⟩)
      (by intro e; apply h2; simp only [Prod.mk.injEq] at e ⊢
          exact ⟨σ.injective e.1, σ.injective e.2⟩)

/-- A permutation of `Fin (m + 2)` sending `0 ↦ i`, `1 ↦ j` for `i ≠ j`. -/
lemma exists_perm_zero_one {m : ℕ} {i j : Fin (m + 2)} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin (m + 2)), σ 0 = i ∧ σ 1 = j := by
  classical
  set τ := Equiv.swap (0 : Fin (m + 2)) i
  have hj' : τ j ≠ 0 := by
    intro h
    have : j = τ 0 := by rw [← h]; simp [τ]
    exact hij (by rw [this]; simp [τ])
  refine ⟨τ * Equiv.swap 1 (τ j), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by simp) hj'.symm]
    simp [τ]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    simp [τ]

/-! ### The integrand of a pair -/

/-- The integrand `1[q convex independent, D q i j] (1 - area)^N`. -/
noncomputable def pairIntegrand {k : ℕ} (D : (Fin k → ℝ × ℝ) → Fin k → Fin k → Prop)
    (N : ℕ) (i j : Fin k) (q : Fin k → ℝ × ℝ) : ℝ≥0∞ :=
  {q | q ∈ ciSet (Fin k) ∧ D q i j}.indicator (fun q => (1 - hullArea q) ^ N) q

lemma measurable_pairIntegrand {k : ℕ} (D : (Fin k → ℝ × ℝ) → Fin k → Fin k → Prop)
    (hD : ∀ i j, MeasurableSet {q | D q i j}) (N : ℕ) (i j : Fin k) :
    Measurable (pairIntegrand D N i j) := by
  unfold pairIntegrand
  refine Measurable.indicator ?_ ((measurableSet_ciSet _).inter (hD i j))
  exact (measurable_const.sub (measurable_hullArea _)).pow_const N

lemma pairIntegrand_eq_ite {k : ℕ} (D : (Fin k → ℝ × ℝ) → Fin k → Fin k → Prop)
    (N : ℕ) (i j : Fin k) (q : Fin k → ℝ × ℝ) [Decidable (D q i j)] :
    pairIntegrand D N i j q =
      if D q i j then (ciSet (Fin k)).indicator (fun q => (1 - hullArea q) ^ N) q else 0 := by
  unfold pairIntegrand
  by_cases h : D q i j <;> by_cases hc : ConvexIndependent ℝ q <;>
    simp [h, hc]

/-- Every ordered pair of distinct indices gives the same integral as `(0, 1)`. -/
lemma lintegral_pairIntegrand_eq {K : Set (ℝ × ℝ)} {m : ℕ}
    (D : (Fin (m + 2) → ℝ × ℝ) → Fin (m + 2) → Fin (m + 2) → Prop)
    (hD : ∀ (q : Fin (m + 2) → ℝ × ℝ) (σ : Equiv.Perm (Fin (m + 2))) i j,
      D (q ∘ σ) i j ↔ D q (σ i) (σ j))
    (N : ℕ) {i j : Fin (m + 2)} (hij : i ≠ j) :
    ∫⁻ q, pairIntegrand D N i j q ∂ptLaw K (m + 2) =
      ∫⁻ q, pairIntegrand D N 0 1 q ∂ptLaw K (m + 2) := by
  obtain ⟨σ, h0, h1⟩ := exists_perm_zero_one hij
  rw [ptLaw, ← lintegral_comp_perm_pi (volume.restrict K) σ (pairIntegrand D N 0 1)]
  congr 1
  funext q
  unfold pairIntegrand
  have hset : (q ∘ σ ∈ {q | q ∈ ciSet (Fin (m + 2)) ∧ D q 0 1}) ↔
      (q ∈ {q | q ∈ ciSet (Fin (m + 2)) ∧ D q i j}) := by
    simp only [mem_ofPred_eq, mem_ciSet, convexIndependent_comp_equiv_iff, hD, h0, h1]
  by_cases h : q ∈ {q | q ∈ ciSet (Fin (m + 2)) ∧ D q i j}
  · rw [indicator_of_mem h, indicator_of_mem (hset.2 h), hullArea_comp_equiv]
  · rw [indicator_of_notMem h, indicator_of_notMem (fun h' => h (hset.1 h'))]

lemma card_offDiag_univ (m : ℕ) :
    ((Finset.univ : Finset (Fin (m + 2))).offDiag.card : ℝ≥0∞) = ((m + 2) * (m + 1) : ℕ) := by
  rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  congr 1
  apply Nat.sub_eq_of_eq_add
  ring

/-- Summing over all ordered pairs. -/
lemma sum_lintegral_pairIntegrand {K : Set (ℝ × ℝ)} {m : ℕ}
    (D : (Fin (m + 2) → ℝ × ℝ) → Fin (m + 2) → Fin (m + 2) → Prop)
    (hDm : ∀ i j, MeasurableSet {q | D q i j})
    (hD : ∀ (q : Fin (m + 2) → ℝ × ℝ) (σ : Equiv.Perm (Fin (m + 2))) i j,
      D (q ∘ σ) i j ↔ D q (σ i) (σ j)) (N : ℕ) :
    ∫⁻ q, ∑ p ∈ (Finset.univ : Finset (Fin (m + 2))).offDiag, pairIntegrand D N p.1 p.2 q
        ∂ptLaw K (m + 2) =
      ((m + 2) * (m + 1) : ℕ) * ∫⁻ q, pairIntegrand D N 0 1 q ∂ptLaw K (m + 2) := by
  rw [lintegral_finsetSum _ (fun p _ => measurable_pairIntegrand D hDm N p.1 p.2)]
  rw [Finset.sum_congr rfl (fun p hp => lintegral_pairIntegrand_eq D hD N
    (Finset.mem_offDiag.1 hp).2.2)]
  rw [Finset.sum_const, nsmul_eq_mul, card_offDiag_univ]

/-- Pointwise: the sum over pairs is the base integrand times the number of `D`-pairs. -/
lemma sum_pairIntegrand_eq {k : ℕ} (D : (Fin k → ℝ × ℝ) → Fin k → Fin k → Prop)
    (N : ℕ) (q : Fin k → ℝ × ℝ) [DecidablePred fun p : Fin k × Fin k => D q p.1 p.2] :
    ∑ p ∈ (Finset.univ : Finset (Fin k)).offDiag, pairIntegrand D N p.1 p.2 q =
      ((Finset.univ : Finset (Fin k)).offDiag.filter fun p => D q p.1 p.2).card *
        (ciSet (Fin k)).indicator (fun q => (1 - hullArea q) ^ N) q := by
  classical
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pairIntegrand_eq_ite]
  split_ifs <;> simp

/-! ### Counting diameter pairs -/

lemma two_le_card_isDiamLE {m : ℕ} (q : Fin (m + 2) → ℝ × ℝ)
    [DecidablePred fun p : Fin (m + 2) × Fin (m + 2) => IsDiamLE 1 q p.1 p.2] :
    2 ≤ ((Finset.univ : Finset (Fin (m + 2))).offDiag.filter
      fun p => IsDiamLE 1 q p.1 p.2).card := by
  have hne : ((Finset.univ : Finset (Fin (m + 2))).offDiag).Nonempty :=
    ⟨(0, 1), by simp⟩
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image _
    (fun p : Fin (m + 2) × Fin (m + 2) => sqDist 1 (q p.1) (q p.2)) hne
  have hp' := Finset.mem_offDiag.1 hp
  have hdiam : ∀ a b, sqDist 1 (q a) (q b) ≤ sqDist 1 (q p.1) (q p.2) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [sqDist_self]
      exact sqDist_nonneg zero_le_one _ _
    · exact hmax (a, b) (by simp [hab])
  have h1 : p ∈ (Finset.univ : Finset (Fin (m + 2))).offDiag.filter
      fun p => IsDiamLE 1 q p.1 p.2 := Finset.mem_filter.2 ⟨hp, hdiam⟩
  have h2 : (p.2, p.1) ∈ (Finset.univ : Finset (Fin (m + 2))).offDiag.filter
      fun p => IsDiamLE 1 q p.1 p.2 := by
    refine Finset.mem_filter.2 ⟨by simp [Ne.symm hp'.2.2], fun a b => ?_⟩
    show _ ≤ sqDist 1 (q p.2) (q p.1)
    rw [sqDist_comm 1 (q p.2)]
    exact hdiam a b
  have hsub : ({p, (p.2, p.1)} : Finset (Fin (m + 2) × Fin (m + 2))) ⊆
      (Finset.univ : Finset (Fin (m + 2))).offDiag.filter fun p => IsDiamLE 1 q p.1 p.2 := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact h1
    · rw [Finset.mem_singleton.1 hx]; exact h2
  have hcard : ({p, (p.2, p.1)} : Finset (Fin (m + 2) × Fin (m + 2))).card = 2 := by
    rw [Finset.card_pair]
    intro e
    exact hp'.2.2 (Prod.mk.injEq _ _ _ _ ▸ e).1
  exact hcard.symm.le.trans (Finset.card_le_card hsub)

lemma card_isDiamLT_le_two {k : ℕ} (q : Fin k → ℝ × ℝ)
    [DecidablePred fun p : Fin k × Fin k => IsDiamLT 1 q p.1 p.2] :
    ((Finset.univ : Finset (Fin k)).offDiag.filter
      fun p => IsDiamLT 1 q p.1 p.2).card ≤ 2 := by
  classical
  set S := (Finset.univ : Finset (Fin k)).offDiag.filter fun p => IsDiamLT 1 q p.1 p.2
  rcases S.eq_empty_or_nonempty with h | ⟨p, hp⟩
  · rw [h]; simp
  have hp' := Finset.mem_filter.1 hp
  have hsub : S ⊆ {p, (p.2, p.1)} := by
    intro x hx
    have hx' := Finset.mem_filter.1 hx
    by_contra hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    have hxne := (Finset.mem_offDiag.1 hx'.1).2.2
    have hpne := (Finset.mem_offDiag.1 hp'.1).2.2
    have a1 := hp'.2 x.1 x.2 hxne hnot.1 hnot.2
    have a2 := hx'.2 p.1 p.2 hpne (fun e => hnot.1 e.symm)
      (fun e => hnot.2 (by
        simp only [Prod.mk.injEq] at e
        exact Prod.ext e.2.symm e.1.symm))
    exact lt_asymm a1 a2
  exact (Finset.card_le_card hsub).trans (Finset.card_le_two)

/-! ### The two inequalities -/

theorem two_mul_emptyProb_le (K : Set (ℝ × ℝ)) (m N : ℕ) :
    2 * emptyProb K (m + 2) N ≤
      ((m + 2) * (m + 1) : ℕ) * diamProb K m (fun q => IsDiamLE 1 q 0 1) N := by
  classical
  have hdp : diamProb K m (fun q => IsDiamLE 1 q 0 1) N =
      ∫⁻ q, pairIntegrand (fun q i j => IsDiamLE 1 q i j) N 0 1 q ∂ptLaw K (m + 2) := rfl
  rw [hdp, ← sum_lintegral_pairIntegrand _ (fun i j => measurableSet_isDiamLE 1 i j)
    (fun q σ i j => isDiamLE_comp_perm 1 q σ i j), emptyProb,
    ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun q => ?_
  rw [sum_pairIntegrand_eq]
  gcongr
  exact_mod_cast two_le_card_isDiamLE q

theorem diamProb_lt_le (K : Set (ℝ × ℝ)) (m N : ℕ) :
    ((m + 2) * (m + 1) : ℕ) * diamProb K m (fun q => IsDiamLT 1 q 0 1) N ≤
      2 * emptyProb K (m + 2) N := by
  classical
  have hdp : diamProb K m (fun q => IsDiamLT 1 q 0 1) N =
      ∫⁻ q, pairIntegrand (fun q i j => IsDiamLT 1 q i j) N 0 1 q ∂ptLaw K (m + 2) := rfl
  rw [hdp, ← sum_lintegral_pairIntegrand _ (fun i j => measurableSet_isDiamLT 1 i j)
    (fun q σ i j => isDiamLT_comp_perm 1 q σ i j), emptyProb,
    ← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun q => ?_
  rw [sum_pairIntegrand_eq]
  gcongr
  exact_mod_cast card_isDiamLT_le_two q

end KHoles
