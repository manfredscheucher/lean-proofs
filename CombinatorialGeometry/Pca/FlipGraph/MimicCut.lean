/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): the triangle cut off from a triangle of `M − C'` by `C'`

Third case of the mimicking, crossed form: `T` is a triangle of `M − C'` with sides on `C`, `c₁`,
`c₂`; its side on `C` is one segment `b` of `M`, its other sides are crossed by `C'` once each
(`M`-segments `p, s₀` on `c₁` and `q, s₁` on `c₂`). Then `T₂ = (s₀, q, r)` is a triangle of `M`
(`r` the dart of `C'` after `q`). Jordan argument: a cut `ρ` along the chain of the five segments
(`Chain.exists_cut`); along each of the curves `C`, `c₁`, `c₂` the cut value `1` occurs only on
these segments (`cut_one_curve`), and every other curve never meets them. The curve after the
`C'`-side of `T₂` is then `c₁`.
-/
import Pca.FlipGraph.Chain
import Pca.FlipGraph.Chord

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

namespace Chain

variable {A : Arrangement n D}

/-- Along the walk of `y₀`: if the cut has value `1` at `y₀`, the first `ℓ` segments are in the
chain, the walk stays in the cut region along them and leaves it at the end of the `ℓ`-th, and no
further segment of the walk (nor any segment met at its crossings) is in the chain, then the darts
of the curve with cut value `1` are the first `ℓ` darts of the walk. -/
theorem cut_one_curve {c : A.Segment → ZMod 2} {r : A.Cell → ZMod 2} (hr : IsCut c r) {y₀ : D}
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (h0 : r (A.cellOf y₀) = 1)
    (hE : ∀ i < ℓ, c (A.segmentOf ((A.straight ^ i) y₀)) = 1)
    (hσ : ∀ i, i + 1 < ℓ → c (A.segmentOf (A.σ (A.α ((A.straight ^ i) y₀)))) = 0)
    (hlast : c (A.segmentOf (A.σ (A.α ((A.straight ^ (ℓ - 1)) y₀)))) = 1)
    (hrest : ∀ i, ℓ ≤ i → i < period A.straight y₀ → c (A.segmentOf ((A.straight ^ i) y₀)) = 0)
    (hrestσ : ∀ i, ℓ ≤ i → i + 1 < period A.straight y₀ →
      c (A.segmentOf (A.σ (A.α ((A.straight ^ i) y₀)))) = 0)
    {g : D} (hg : A.curve g = A.curve y₀) (hg1 : r (A.cellOf g) = 1) :
    ∃ i < ℓ, g = (A.straight ^ i) y₀ := by
  have hv : ∀ i, i < period A.straight y₀ →
      r (A.cellOf ((A.straight ^ i) y₀)) = if i < ℓ then 1 else 0 := by
    intro i
    induction i with
    | zero => intro _; rw [if_pos (by omega)]; exact h0
    | succ i ih =>
      intro hi
      rw [Walk.pow_succ_apply, cut_straight hr, ih (by omega)]
      rcases Nat.lt_or_ge (i + 1) ℓ with h | h
      · rw [if_pos (by omega), if_pos h, hσ i h, add_zero]
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · have hi' : i = ℓ - 1 := by omega
        subst hi'
        rw [if_pos (by omega), if_neg (by omega), hlast]; decide
      · rw [if_neg (by omega), if_neg (by omega), hrestσ i (by omega) hi, add_zero]
  have hvα : ∀ i, i < period A.straight y₀ → r (A.cellOf (A.α ((A.straight ^ i) y₀))) = 0 := by
    intro i hi
    rw [cut_α hr, hv i hi]
    rcases Nat.lt_or_ge i ℓ with h | h
    · rw [if_pos h, hE i h]; decide
    · rw [if_neg (by omega), hrest i h hi]; decide
  rcases A.isArrangement.straight y₀ g hg.symm with h | h
  · obtain ⟨k, hk, rfl⟩ := Walk.exists_idx A h
    refine ⟨k, ?_, rfl⟩
    by_contra hk'
    rw [hv k hk, if_neg hk'] at hg1
    exact zero_ne_one hg1
  · obtain ⟨k, hk, hke⟩ := Walk.exists_idx A h
    have hp := period_pos A.straight y₀
    -- `g = σ² (straight^k y₀) = α (straight^(k-1) y₀)` (indices mod the period)
    obtain ⟨j, hj, hgj⟩ : ∃ j < period A.straight y₀, g = A.α ((A.straight ^ j) y₀) := by
      have hσσ : ∀ w, A.σ (A.σ (A.straight w)) = A.α w := fun w => by
        rw [A.straight_apply, A.σ_σ_σ_σ]
      have hg' : g = A.σ (A.σ ((A.straight ^ k) y₀)) := by
        change _ = A.σ (A.σ _) at hke; rw [hke, A.σ_σ_σ_σ]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · refine ⟨period A.straight y₀ - 1, by omega, ?_⟩
        rw [hg', ← hσσ, ← Walk.pow_succ_apply, Nat.sub_add_cancel hp, Walk.pow_period_apply,
          pow_zero, Perm.one_apply]
      · refine ⟨k - 1, by omega, ?_⟩
        rw [hg', ← hσσ, ← Walk.pow_succ_apply, Nat.sub_add_cancel hk0]
    rw [hgj, hvα j hj] at hg1
    exact absurd hg1 zero_ne_one

/-- **The triangle cut off from a triangle of `M − C'` by `C'`** (see the module docstring):
`b` (on `C`), `p, s₀` (on `c₁`), `q, s₁` (on `c₂`) are the `M`-segments of the sides of the
triangle, `C'` passes through the crossings `Y₁` (start of `s₀`) and `Y₂` (start of `s₁`) only.
Then the dart after the `C'`-dart `φ q` is `s₀`: the cell of `s₀` is a triangle. -/
theorem tri_cut {C' : Fin n} {b p s₀ q s₁ : D} (hp : A.φ b = p) (hs₀ : A.straight p = s₀)
    (hq : A.φ s₀ = q) (hs₁ : A.straight q = s₁) (hb : A.φ s₁ = b)
    (hY₁ : C' ∈ Arrangement.Crossing.curves A (A.crossingOf s₀))
    (hY₂ : C' ∈ Arrangement.Crossing.curves A (A.crossingOf s₁))
    (hX₀ : C' ∉ Arrangement.Crossing.curves A (A.crossingOf b))
    (hX₁ : C' ∉ Arrangement.Crossing.curves A (A.crossingOf p))
    (hX₂ : C' ∉ Arrangement.Crossing.curves A (A.crossingOf q)) :
    A.φ (A.φ q) = s₀ := by
  classical
  -- crossings
  have e1 : A.crossingOf (A.α b) = A.crossingOf p := by rw [← hp, A.φ_apply, A.crossingOf_σ]
  have e2 : A.crossingOf (A.α p) = A.crossingOf s₀ := by rw [← hs₀, A.crossingOf_straight]
  have e3 : A.crossingOf (A.α s₀) = A.crossingOf q := by rw [← hq, A.φ_apply, A.crossingOf_σ]
  have e4 : A.crossingOf (A.α q) = A.crossingOf s₁ := by rw [← hs₁, A.crossingOf_straight]
  have e5 : A.crossingOf (A.α s₁) = A.crossingOf b := by rw [← hb, A.φ_apply, A.crossingOf_σ]
  -- curves
  have cs₀ : A.curve s₀ = A.curve p := by rw [← hs₀, A.curve_straight]
  have cs₁ : A.curve s₁ = A.curve q := by rw [← hs₁, A.curve_straight]
  have kb : Arrangement.Crossing.curves A (A.crossingOf b) = {A.curve q, A.curve b} := by
    rw [← hb, A.curves_crossingOf_φ, hb, cs₁]
  have kp : Arrangement.Crossing.curves A (A.crossingOf p) = {A.curve b, A.curve p} := by
    rw [← hp, A.curves_crossingOf_φ, hp]
  have kq : Arrangement.Crossing.curves A (A.crossingOf q) = {A.curve p, A.curve q} := by
    rw [← hq, A.curves_crossingOf_φ, hq, cs₀]
  have nC'p : C' ≠ A.curve p := fun h => hX₁ (by rw [kp, h]; simp)
  have nC'q : C' ≠ A.curve q := fun h => hX₂ (by rw [kq, h]; simp)
  have nC'b : C' ≠ A.curve b := fun h => hX₀ (by rw [kb, h]; simp)
  have ks₀ : Arrangement.Crossing.curves A (A.crossingOf s₀) = {A.curve p, C'} := by
    have h := hY₁
    rw [← e2, A.curves_crossingOf, A.curve_α, mem_insert, mem_singleton] at h
    rw [← e2, A.curves_crossingOf, A.curve_α, h.resolve_left nC'p]
  have ks₁ : Arrangement.Crossing.curves A (A.crossingOf s₁) = {A.curve q, C'} := by
    have h := hY₂
    rw [← e4, A.curves_crossingOf, A.curve_α, mem_insert, mem_singleton] at h
    rw [← e4, A.curves_crossingOf, A.curve_α, h.resolve_left nC'q]
  have nbp : A.curve b ≠ A.curve p := by rw [← hp]; exact (A.curve_φ_ne b).symm
  have npq : A.curve p ≠ A.curve q := by rw [← hq, ← cs₀]; exact (A.curve_φ_ne s₀).symm
  have nbq : A.curve b ≠ A.curve q := by rw [← hb, ← cs₁]; exact A.curve_φ_ne s₁
  -- the `C'`-darts after `p` and `q`
  have cφp : A.curve (A.σ (A.α p)) = C' := by
    have h := hY₁
    rw [← e2, A.curves_crossingOf, A.curve_α, mem_insert, mem_singleton] at h
    exact (h.resolve_left nC'p).symm
  have cφq : A.curve (A.σ (A.α q)) = C' := by
    have h := hY₂
    rw [← e4, A.curves_crossingOf, A.curve_α, mem_insert, mem_singleton] at h
    exact (h.resolve_left nC'q).symm
  -- the chain of the five segments
  set ch : A.Segment → ZMod 2 := δ (A.segmentOf b) + δ (A.segmentOf p) + δ (A.segmentOf s₀) +
    δ (A.segmentOf q) + δ (A.segmentOf s₁) with hch
  have key5 : ∀ a b c d e : ZMod 2, a + b + (b + c) + (c + d) + (d + e) + (e + a) = 0 := by decide
  have heven : IsEven ch := by
    intro x
    rw [hch, bd_add, bd_add, bd_add, bd_add, bd_δ, bd_δ, bd_δ, bd_δ, bd_δ, e1, e2, e3, e4, e5]
    exact key5 _ _ _ _ _
  have hsegc : ∀ z t, A.segmentOf z = A.segmentOf t → A.curve z = A.curve t := fun z t h => by
    rcases eq_or_eq_α_of_segmentOf h with rfl | rfl
    · rfl
    · exact A.curve_α t
  have hval : ∀ z, ch (A.segmentOf z) =
      (if A.segmentOf z = A.segmentOf b then 1 else 0) + (if A.segmentOf z = A.segmentOf p then 1 else 0) +
      (if A.segmentOf z = A.segmentOf s₀ then 1 else 0) + (if A.segmentOf z = A.segmentOf q then 1 else 0) +
      (if A.segmentOf z = A.segmentOf s₁ then 1 else 0) := fun z => rfl
  have hzero : ∀ z, A.curve z ≠ A.curve b → A.curve z ≠ A.curve p → A.curve z ≠ A.curve q →
      ch (A.segmentOf z) = 0 := by
    intro z h1 h2 h3
    rw [hval, if_neg (fun h => h1 (hsegc _ _ h)), if_neg (fun h => h2 (hsegc _ _ h)),
      if_neg (fun h => h2 ((hsegc _ _ h).trans cs₀)), if_neg (fun h => h3 (hsegc _ _ h)),
      if_neg (fun h => h3 ((hsegc _ _ h).trans cs₁))]
    decide
  have hσσne : ∀ y, A.σ (A.σ y) ≠ y := fun y h => A.cellOf_σσ_ne y (by rw [h])
  have nps₀ : A.segmentOf s₀ ≠ A.segmentOf p := fun h => by
    rcases eq_or_eq_α_of_segmentOf h with h' | h'
    · exact hX₁ (by rw [← h']; exact hY₁)
    · exact hσσne (A.α p) (by rw [← A.straight_apply, hs₀, h'])
  have nqs₁ : A.segmentOf s₁ ≠ A.segmentOf q := fun h => by
    rcases eq_or_eq_α_of_segmentOf h with h' | h'
    · exact hX₂ (by rw [← h']; exact hY₂)
    · exact hσσne (A.α q) (by rw [← A.straight_apply, hs₁, h'])
  have v_b : ch (A.segmentOf b) = 1 := by
    rw [hval, if_pos rfl, if_neg (fun h => nbp (hsegc _ _ h)),
      if_neg (fun h => nbp ((hsegc _ _ h).trans cs₀)), if_neg (fun h => nbq (hsegc _ _ h)),
      if_neg (fun h => nbq ((hsegc _ _ h).trans cs₁))]; decide
  have v_p : ch (A.segmentOf p) = 1 := by
    rw [hval, if_neg (fun h => nbp (hsegc _ _ h).symm), if_pos rfl, if_neg (Ne.symm nps₀),
      if_neg (fun h => npq (hsegc _ _ h)), if_neg (fun h => npq ((hsegc _ _ h).trans cs₁))]; decide
  have v_s₀ : ch (A.segmentOf s₀) = 1 := by
    rw [hval, if_neg (fun h => nbp ((hsegc _ _ h).symm.trans cs₀)), if_neg nps₀, if_pos rfl,
      if_neg (fun h => npq (cs₀.symm.trans (hsegc _ _ h))),
      if_neg (fun h => npq (cs₀.symm.trans ((hsegc _ _ h).trans cs₁)))]; decide
  have v_q : ch (A.segmentOf q) = 1 := by
    rw [hval, if_neg (fun h => nbq (hsegc _ _ h).symm), if_neg (fun h => npq (hsegc _ _ h).symm),
      if_neg (fun h => npq ((hsegc _ _ h).trans cs₀).symm), if_pos rfl, if_neg (Ne.symm nqs₁)]; decide
  have v_s₁ : ch (A.segmentOf s₁) = 1 := by
    rw [hval, if_neg (fun h => nbq ((hsegc _ _ h).symm.trans cs₁)),
      if_neg (fun h => npq (cs₁.symm.trans (hsegc _ _ h)).symm),
      if_neg (fun h => npq (cs₁.symm.trans ((hsegc _ _ h).trans cs₀)).symm), if_neg nqs₁,
      if_pos rfl]; decide
  have hnot : ∀ z t, A.curve z ≠ A.curve t → A.segmentOf z ≠ A.segmentOf t :=
    fun z t h e => h (hsegc _ _ e)
  -- a segment of the chain lies at one of the five crossings
  have hfive : ∀ w, ch (A.segmentOf w) ≠ 0 → A.crossingOf w = A.crossingOf b ∨
      A.crossingOf w = A.crossingOf p ∨ A.crossingOf w = A.crossingOf s₀ ∨
      A.crossingOf w = A.crossingOf q ∨ A.crossingOf w = A.crossingOf s₁ := by
    intro w hw
    have hcr : ∀ t, A.segmentOf w = A.segmentOf t →
        A.crossingOf w = A.crossingOf t ∨ A.crossingOf w = A.crossingOf (A.α t) := fun t h => by
      rcases eq_or_eq_α_of_segmentOf h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    by_cases h1 : A.segmentOf w = A.segmentOf b
    · rcases hcr b h1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (h.trans e1))
    by_cases h2 : A.segmentOf w = A.segmentOf p
    · rcases hcr p h2 with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (h.trans e2)))
    by_cases h3 : A.segmentOf w = A.segmentOf s₀
    · rcases hcr s₀ h3 with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (h.trans e3))))
    by_cases h4 : A.segmentOf w = A.segmentOf q
    · rcases hcr q h4 with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (h.trans e4))))
    by_cases h5 : A.segmentOf w = A.segmentOf s₁
    · rcases hcr s₁ h5 with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inl (h.trans e5)
    exfalso; apply hw
    rw [hval, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]; decide
  have hcur5 : ∀ w c, ch (A.segmentOf w) ≠ 0 → c ∈ Arrangement.Crossing.curves A (A.crossingOf w) →
      c = A.curve b ∨ c = A.curve p ∨ c = A.curve q ∨ c = C' := by
    intro w c hw hc
    rcases hfive w hw with h | h | h | h | h <;> rw [h] at hc
    · rw [kb] at hc; simp only [mem_insert, mem_singleton] at hc
      rcases hc with hc | hc <;> simp [hc]
    · rw [kp] at hc; simp only [mem_insert, mem_singleton] at hc
      rcases hc with hc | hc <;> simp [hc]
    · rw [ks₀] at hc; simp only [mem_insert, mem_singleton] at hc
      rcases hc with hc | hc <;> simp [hc]
    · rw [kq] at hc; simp only [mem_insert, mem_singleton] at hc
      rcases hc with hc | hc <;> simp [hc]
    · rw [ks₁] at hc; simp only [mem_insert, mem_singleton] at hc
      rcases hc with hc | hc <;> simp [hc]
  -- the cut, normalized to `1` on the cell of `b`
  obtain ⟨r, hr, hrb⟩ : ∃ r, IsCut ch r ∧ r (A.cellOf b) = 1 := by
    obtain ⟨r0, hr0⟩ := exists_cut heven
    rcases zmod2_cases (r0 (A.cellOf b)) with h | h
    · refine ⟨fun f => r0 f + 1, fun y => ?_, by simp [h]⟩
      have k : ∀ a c : ZMod 2, a + 1 + (c + 1) = a + c := by decide
      simp only [k]; exact hr0 y
    · exact ⟨r0, hr0, h⟩
  have hcrσα : ∀ y i, A.crossingOf (A.σ (A.α ((A.straight ^ i) y))) =
      A.crossingOf ((A.straight ^ (i + 1)) y) := fun y i => by
    rw [A.crossingOf_σ, Walk.pow_succ_apply, A.crossingOf_straight]
  have hmemw : ∀ y i, A.curve y ∈ Arrangement.Crossing.curves A
      (A.crossingOf ((A.straight ^ i) y)) := fun y i => by
    rw [← Walk.curve_pow A y i]; exact A.mem_curves_crossingOf _
  have hpow1 : ∀ y, (A.straight ^ 1) y = A.straight y := fun y => by rw [pow_one]
  have hpow0 : ∀ y, (A.straight ^ 0) y = y := fun y => by rw [pow_zero, Perm.one_apply]
  have hseg0 : ∀ y i, 1 ≤ i → i < period A.straight y →
      A.segmentOf ((A.straight ^ i) y) ≠ A.segmentOf y := fun y i hi hip h => by
    have := Lens.seg_inj (z := y) hip le_rfl (Nat.zero_le i) (by rw [hpow0]; exact h)
    omega
  have hseg1 : ∀ y i, 2 ≤ i → i < period A.straight y →
      A.segmentOf ((A.straight ^ i) y) ≠ A.segmentOf (A.straight y) := fun y i hi hip h => by
    have := Lens.seg_inj (z := y) hip le_rfl (by omega : 1 ≤ i) (by rw [hpow1]; exact h)
    omega
  have hcr_inj : ∀ y i j, i < period A.straight y → j ≤ i →
      A.crossingOf ((A.straight ^ i) y) = A.crossingOf ((A.straight ^ j) y) → i = j :=
    fun y i j hip hj h => Lens.cross_inj (z := y) hip le_rfl hj h
  -- the darts of `C` with cut value `1`: only `b`
  have oneC : ∀ g, A.curve g = A.curve b → r (A.cellOf g) = 1 → g = b := by
    intro g hg hg1
    obtain ⟨i, hi, rfl⟩ := cut_one_curve hr (ℓ := 1) le_rfl hrb
      (fun i hi => by obtain rfl : i = 0 := by omega
                      rw [hpow0]; exact v_b)
      (fun i hi => by omega)
      (by rw [Nat.sub_self, hpow0, ← A.φ_apply, hp]; exact v_p)
      (fun i hi hip => by
        rw [hval, if_neg (hseg0 b i hi hip), if_neg (hnot _ _ (by rw [Walk.curve_pow]; exact nbp)),
          if_neg (hnot _ _ (by rw [Walk.curve_pow, cs₀]; exact nbp)),
          if_neg (hnot _ _ (by rw [Walk.curve_pow]; exact nbq)),
          if_neg (hnot _ _ (by rw [Walk.curve_pow, cs₁]; exact nbq))]; decide)
      (fun i hi hip => by
        by_contra h
        have hm := hmemw b (i + 1)
        rcases hfive _ h with h' | h' | h' | h' | h' <;> rw [hcrσα] at h'
        · have := hcr_inj b (i + 1) 0 hip (Nat.zero_le _) (by rw [hpow0]; exact h'); omega
        · have := hcr_inj b (i + 1) 1 hip (by omega) (by rw [hpow1, A.crossingOf_straight, e1]; exact h')
          omega
        · rw [h', ks₀] at hm; simp only [mem_insert, mem_singleton] at hm
          rcases hm with hm | hm
          · exact nbp hm
          · exact nC'b hm.symm
        · rw [h', kq] at hm; simp only [mem_insert, mem_singleton] at hm
          rcases hm with hm | hm
          · exact nbp hm
          · exact nbq hm
        · rw [h', ks₁] at hm; simp only [mem_insert, mem_singleton] at hm
          rcases hm with hm | hm
          · exact nbq hm
          · exact nC'b hm.symm)
      hg hg1
    obtain rfl : i = 0 := by omega
    exact hpow0 b
  have rp : r (A.cellOf p) = 1 := by rw [← hp, A.cellOf_φ]; exact hrb
  have z_p : ch (A.segmentOf (A.σ (A.α p))) = 0 :=
    hzero _ (by rw [cφp]; exact nC'b) (by rw [cφp]; exact nC'p) (by rw [cφp]; exact nC'q)
  have z_q : ch (A.segmentOf (A.σ (A.α q))) = 0 :=
    hzero _ (by rw [cφq]; exact nC'b) (by rw [cφq]; exact nC'p) (by rw [cφq]; exact nC'q)
  have rs₀ : r (A.cellOf s₀) = 1 := by rw [← hs₀, cut_straight hr, rp, z_p, add_zero]
  have rq : r (A.cellOf q) = 1 := by rw [← hq, A.cellOf_φ]; exact rs₀
  have hpow2 : ∀ y, (A.straight ^ 2) y = A.straight (A.straight y) := fun y => by
    rw [Walk.pow_succ_apply, hpow1]
  -- the darts of `c₁` with cut value `1`: `p` and `s₀`
  have one1 : ∀ g, A.curve g = A.curve p → r (A.cellOf g) = 1 → g = p ∨ g = s₀ := by
    intro g hg hg1
    obtain ⟨i, hi, rfl⟩ := cut_one_curve hr (ℓ := 2) (by omega) rp
      (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rw [hpow0]; exact v_p
        · rw [hpow1, hs₀]; exact v_s₀)
      (fun i hi => by obtain rfl : i = 0 := by omega
                      rw [hpow0]; exact z_p)
      (by rw [show 2 - 1 = 1 from rfl, hpow1, hs₀, ← A.φ_apply, hq]; exact v_q)
      (fun i hi hip => by
        rw [hval, if_neg (hnot _ _ (by rw [Walk.curve_pow]; exact nbp.symm)),
          if_neg (hseg0 p i (by omega) hip), if_neg (by rw [← hs₀]; exact hseg1 p i hi hip),
          if_neg (hnot _ _ (by rw [Walk.curve_pow]; exact npq)),
          if_neg (hnot _ _ (by rw [Walk.curve_pow, cs₁]; exact npq))]; decide)
      (fun i hi hip => by
        by_contra h
        have hm := hmemw p (i + 1)
        rcases hfive _ h with h' | h' | h' | h' | h' <;> rw [hcrσα] at h'
        · rw [h', kb] at hm; simp only [mem_insert, mem_singleton] at hm
          rcases hm with hm | hm
          · exact npq hm
          · exact nbp hm.symm
        · have := hcr_inj p (i + 1) 0 hip (Nat.zero_le _) (by rw [hpow0]; exact h'); omega
        · have := hcr_inj p (i + 1) 1 hip (by omega) (by rw [hpow1, hs₀]; exact h'); omega
        · have := hcr_inj p (i + 1) 2 hip (by omega)
            (by rw [hpow2, hs₀, A.crossingOf_straight, e3]; exact h'); omega
        · rw [h', ks₁] at hm; simp only [mem_insert, mem_singleton] at hm
          rcases hm with hm | hm
          · exact npq hm
          · exact nC'p hm.symm)
      hg hg1
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl (hpow0 p)
    · exact Or.inr (by rw [hpow1, hs₀])
  -- the darts of `c₂` with cut value `1`: `q` and `s₁`
  have one2 : ∀ g, A.curve g = A.curve q → r (A.cellOf g) = 1 → g = q ∨ g = s₁ := by
    intro g hg hg1
    obtain ⟨i, hi, rfl⟩ := cut_one_curve hr (ℓ := 2) (by omega) rq
      (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · rw [hpow0]; exact v_q
        · rw [hpow1, hs₁]; exact v_s₁)
      (fun i hi => by obtain rfl : i = 0 := by omega
                      rw [hpow0]; exact z_q)
      (by rw [show 2 - 1 = 1 from rfl, hpow1, hs₁, ← A.φ_apply, hb]; exact v_b)
      (fun i hi hip => by
        rw [hval, if_neg (hnot _ _ (by rw [Walk.curve_pow]; exact nbq.symm)),
          if_neg (hnot _ _ (by rw [Walk.curve_pow]; exact npq.symm)),
          if_neg (hnot _ _ (by rw [Walk.curve_pow, cs₀]; exact npq.symm)),
          if_neg (hseg0 q i (by omega) hip), if_neg (by rw [← hs₁]; exact hseg1 q i hi hip)]
        decide)
      (fun i hi hip => by
        by_contra h
        have hm := hmemw q (i + 1)
        rcases hfive _ h with h' | h' | h' | h' | h' <;> rw [hcrσα] at h'
        · have := hcr_inj q (i + 1) 2 hip (by omega)
            (by rw [hpow2, hs₁, A.crossingOf_straight, e5]; exact h'); omega
        · rw [h', kp] at hm; simp only [mem_insert, mem_singleton] at hm
          rcases hm with hm | hm
          · exact nbq hm.symm
          · exact npq hm.symm
        · rw [h', ks₀] at hm; simp only [mem_insert, mem_singleton] at hm
          rcases hm with hm | hm
          · exact npq hm.symm
          · exact nC'q hm.symm
        · have := hcr_inj q (i + 1) 0 hip (Nat.zero_le _) (by rw [hpow0]; exact h'); omega
        · have := hcr_inj q (i + 1) 1 hip (by omega) (by rw [hpow1, hs₁]; exact h'); omega)
      hg hg1
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl (hpow0 q)
    · exact Or.inr (by rw [hpow1, hs₁])
  -- the dart after the `C'`-dart `φ q`
  have crr : A.curve (A.φ q) = C' := by rw [A.φ_apply]; exact cφq
  have hy3 : r (A.cellOf (A.φ (A.φ q))) = 1 := by rw [A.cellOf_φ, A.cellOf_φ]; exact rq
  have hC'y3 : C' ∈ Arrangement.Crossing.curves A (A.crossingOf (A.φ (A.φ q))) := by
    rw [A.φ_apply (A.φ q), A.crossingOf_σ, ← crr, ← A.curve_α]
    exact A.mem_curves_crossingOf _
  by_cases hc1 : A.curve (A.φ (A.φ q)) = A.curve b
  · exact absurd (by rw [← oneC _ hc1 hy3]; exact hC'y3) hX₀
  by_cases hc2 : A.curve (A.φ (A.φ q)) = A.curve p
  · rcases one1 _ hc2 hy3 with h | h
    · exact absurd (by rw [← h]; exact hC'y3) hX₁
    · exact h
  by_cases hc3 : A.curve (A.φ (A.φ q)) = A.curve q
  · rcases one2 _ hc3 hy3 with h | h
    · exact absurd (by rw [← h]; exact hC'y3) hX₂
    · exfalso
      rw [← hs₁, A.φ_apply (A.φ q), A.straight_apply] at h
      have h' := A.σ.injective h
      rw [A.φ_apply] at h'
      exact A.isArrangement.α_ne _ h'
  · exfalso
    have hc4 : A.curve (A.φ (A.φ q)) ≠ C' := by rw [← crr]; exact A.curve_φ_ne _
    have hcard := Walk.card_flipsOn A hc1
    obtain ⟨i, hi⟩ := card_pos.1 (by omega : 0 < (Walk.flipsOn A (A.curve b) (A.φ (A.φ q))).card)
    rw [Walk.mem_flipsOn] at hi
    have hsum : ∑ j ∈ range i, ch (A.segmentOf (A.σ (A.α ((A.straight ^ j) (A.φ (A.φ q)))))) = 0 := by
      refine sum_eq_zero fun j _ => ?_
      by_contra h
      have hm := hmemw (A.φ (A.φ q)) (j + 1)
      rw [← hcrσα] at hm
      rcases hcur5 _ _ h hm with h' | h' | h' | h'
      · exact hc1 h'
      · exact hc2 h'
      · exact hc3 h'
      · exact hc4 h'
    have hg1 : r (A.cellOf (A.σ (A.α ((A.straight ^ i) (A.φ (A.φ q)))))) = 1 := by
      rw [← A.φ_apply, A.cellOf_φ, cut_pow hr, hsum, add_zero]; exact hy3
    have hgb := oneC _ hi.2 hg1
    have hm := hmemw (A.φ (A.φ q)) (i + 1)
    rw [← hcrσα, hgb, kb] at hm
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with hm | hm
    · exact hc3 hm
    · exact hc1 hm

end Chain

end Pca.FlipGraph
