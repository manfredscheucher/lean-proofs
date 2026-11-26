/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.HoleDefs
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.Topology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Upper and lower caps are independent (Step 5a of `doc/kholes/kholes.md`)

Let `B₀ = {(0,0), (1,0)}`, `U` a set of points with `0 < x < 1`, `y > 0` and `L` a set of
points with `0 < x < 1`, `y < 0`. We prove

* `convexHull_caps_union`: `conv (B₀ ∪ U ∪ L) = conv (B₀ ∪ U) ∪ conv (B₀ ∪ L)`;
* `convexIndependent_caps_union`: `B₀ ∪ U ∪ L` is convex independent iff `B₀ ∪ U` and
  `B₀ ∪ L` are;
* `convexIndependent_baseCfg_split`, `hullArea_baseCfg_split`: the same for the families
  `baseCfg z`, `baseCfg u`, `baseCfg l` with `range z = range u ∪ range l` (the hull areas
  add up because the two hulls meet only on the null line `y = 0`).

The key geometric fact is a segment-crossing argument (`mem_of_crossing`): if `p` lies in a
convex set `A ⊇ [(0,0),(1,0)]` above the `x`-axis and `q` lies below it, then every point of
`[p, q]` above the axis lies in `A`, because it lies on `[p, c]`, where `c` is the point where
`[p, q]` crosses the axis. The side of the axis is encoded by a sign `e ≠ 0`
(`0 ≤ e * y`), so that every argument is written once for both caps.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-! ### Strips and half-planes -/

lemma convex_strip (e : ℝ) :
    Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ e * p.2} := by
  intro x hx y hy α β hα hβ hαβ
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    exact add_nonneg (mul_nonneg hα hx1) (mul_nonneg hβ hy1)
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx2 hα, mul_le_mul_of_nonneg_left hy2 hβ]
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    nlinarith [mul_nonneg hα hx3, mul_nonneg hβ hy3]

lemma convexHull_subset_strip {S : Set (ℝ × ℝ)} {e : ℝ}
    (hS : ∀ p ∈ S, 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ e * p.2) :
    convexHull ℝ S ⊆ {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ e * p.2} :=
  convexHull_min (fun p hp => hS p hp) (convex_strip e)

/-- The hull of `B₀ ∪ S` stays in the strip if `S` does. -/
lemma convexHull_base_subset_strip {S : Set (ℝ × ℝ)} {e : ℝ}
    (hS : ∀ p ∈ S, 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ e * p.2) :
    convexHull ℝ (insert (0, 0) (insert (1, 0) S)) ⊆
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ e * p.2} := by
  apply convexHull_subset_strip
  rintro p (rfl | rfl | hp)
  · simp
  · simp
  · exact hS p hp

/-! ### The segment-crossing argument -/

lemma mk_mem_of_base {A : Set (ℝ × ℝ)} (hA : Convex ℝ A) (h0 : ((0 : ℝ), (0 : ℝ)) ∈ A)
    (h1 : ((1 : ℝ), (0 : ℝ)) ∈ A) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (x, (0 : ℝ)) ∈ A := by
  have := hA h0 h1 (sub_nonneg.2 hx1) hx0 (sub_add_cancel 1 x)
  convert this using 1
  ext <;> simp

/-- Segment crossing: `p ∈ A` above the axis (`0 ≤ e * p.2`), `q` below it, both with
`x ∈ [0, 1]`; then every point of `[p, q]` above the axis lies in `A`. -/
lemma mem_of_crossing {A : Set (ℝ × ℝ)} (hA : Convex ℝ A) (h0 : ((0 : ℝ), (0 : ℝ)) ∈ A)
    (h1 : ((1 : ℝ), (0 : ℝ)) ∈ A) {e : ℝ} (he : e ≠ 0) {p q : ℝ × ℝ} (hp : p ∈ A)
    (hp1 : 0 ≤ p.1) (hp1' : p.1 ≤ 1) (hp2 : 0 ≤ e * p.2) (hq1 : 0 ≤ q.1) (hq1' : q.1 ≤ 1)
    (hq2 : e * q.2 ≤ 0) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hx : 0 ≤ e * (α • p + β • q).2) : α • p + β • q ∈ A := by
  obtain rfl : α = 1 - β := by linarith
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at hx
  rcases eq_or_lt_of_le (show 0 ≤ e * p.2 - e * q.2 by linarith) with hd0 | hdpos
  · -- `p` and `q` both lie on the axis
    have hq2' : q.2 = 0 := by
      have : e * q.2 = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left he
    have hqA : q ∈ A := by
      have hq : (q.1, (0 : ℝ)) = q := Prod.ext rfl hq2'.symm
      exact hq ▸ mk_mem_of_base hA h0 h1 hq1 hq1'
    exact hA hp hqA hα hβ hαβ
  · set d := e * p.2 - e * q.2 with hd
    set t := e * p.2 / d with ht
    have ht0 : 0 ≤ t := div_nonneg hp2 hdpos.le
    have ht1 : t ≤ 1 := (div_le_one hdpos).2 (by linarith)
    have htd : t * d = e * p.2 := div_mul_cancel₀ _ hdpos.ne'
    have hβt : β ≤ t := by
      rw [ht, le_div_iff₀ hdpos, hd]
      nlinarith
    set c : ℝ × ℝ := (1 - t) • p + t • q with hc
    have hc2 : c.2 = 0 := by
      have : e * c.2 = 0 := by
        simp only [hc, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        rw [hd] at htd
        linear_combination (-1 : ℝ) * htd
      exact (mul_eq_zero.1 this).resolve_left he
    have hc1 : 0 ≤ c.1 := by
      simp only [hc, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      exact add_nonneg (mul_nonneg (sub_nonneg.2 ht1) hp1) (mul_nonneg ht0 hq1)
    have hc1' : c.1 ≤ 1 := by
      simp only [hc, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith [mul_le_mul_of_nonneg_left hp1' (sub_nonneg.2 ht1),
        mul_le_mul_of_nonneg_left hq1' ht0]
    have hcA : c ∈ A := by
      have hc' : (c.1, (0 : ℝ)) = c := Prod.ext rfl hc2.symm
      exact hc' ▸ mk_mem_of_base hA h0 h1 hc1 hc1'
    rcases eq_or_lt_of_le ht0 with ht0' | htpos
    · have hβ0 : β = 0 := le_antisymm (ht0' ▸ hβt) hβ
      subst hβ0
      simpa using hp
    · have hbt : β / t * t = β := div_mul_cancel₀ β htpos.ne'
      have heq : (1 - β) • p + β • q = (1 - β / t) • p + (β / t) • c := by
        ext
        · simp only [hc, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          linear_combination (p.1 - q.1) * hbt
        · simp only [hc, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          linear_combination (p.2 - q.2) * hbt
      rw [heq]
      exact hA hp hcA (sub_nonneg.2 ((div_le_one htpos).2 hβt)) (div_nonneg hβ htpos.le)
        (by ring)

/-- One side of `convexHull_caps_union`, for a general sign `e` and weak inequalities: a point
of `conv (B₀ ∪ U ∪ L)` on the side of `U` lies in `conv (B₀ ∪ U)`. -/
lemma mem_convexHull_side {U L : Set (ℝ × ℝ)} {e : ℝ} (he : e ≠ 0)
    (hU : ∀ p ∈ U, 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ e * p.2)
    (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ e * p.2 ≤ 0) {x : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ (insert (0, 0) (insert (1, 0) U) ∪ L)) (hx2 : 0 ≤ e * x.2) :
    x ∈ convexHull ℝ (insert (0, 0) (insert (1, 0) U)) := by
  rcases L.eq_empty_or_nonempty with hLe | hLne
  · rwa [hLe, union_empty] at hx
  rw [convexHull_union (insert_nonempty _ _) hLne, mem_convexJoin] at hx
  obtain ⟨p, hp, q, hq, α, β, hα, hβ, hαβ, rfl⟩ := hx
  obtain ⟨hp1, hp1', hp2⟩ := convexHull_base_subset_strip hU hp
  have hL' : ∀ r ∈ L, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ -e * r.2 := fun r hr => by
    obtain ⟨h1, h2, h3⟩ := hL r hr
    exact ⟨h1, h2, by linarith⟩
  obtain ⟨hq1, hq1', hq2⟩ := convexHull_subset_strip hL' hq
  exact mem_of_crossing (convex_convexHull ℝ _) (subset_convexHull ℝ _ (mem_insert _ _))
    (subset_convexHull ℝ _ (mem_insert_of_mem _ (mem_insert _ _))) he hp hp1 hp1' hp2 hq1 hq1'
    (by linarith) hα hβ hαβ hx2

lemma insert_insert_union_eq (U L : Set (ℝ × ℝ)) :
    insert ((0 : ℝ), (0 : ℝ)) (insert ((1 : ℝ), (0 : ℝ)) (U ∪ L)) =
      insert (0, 0) (insert (1, 0) U) ∪ L := by
  ext y
  simp only [mem_insert_iff, mem_union]
  tauto

/-! ### The hull of the union -/

theorem convexHull_caps_union {U L : Set (ℝ × ℝ)}
    (hU : ∀ p ∈ U, 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2) (hL : ∀ p ∈ L, 0 < p.1 ∧ p.1 < 1 ∧ p.2 < 0) :
    convexHull ℝ (insert (0, 0) (insert (1, 0) (U ∪ L))) =
      convexHull ℝ (insert (0, 0) (insert (1, 0) U)) ∪
        convexHull ℝ (insert (0, 0) (insert (1, 0) L)) := by
  apply Subset.antisymm
  · intro x hx
    by_cases hx2 : 0 ≤ x.2
    · left
      rw [insert_insert_union_eq] at hx
      refine mem_convexHull_side (e := 1) one_ne_zero (fun p hp => ?_) (fun p hp => ?_) hx
        (by linarith)
      · obtain ⟨h1, h2, h3⟩ := hU p hp
        exact ⟨h1.le, h2.le, by linarith⟩
      · obtain ⟨h1, h2, h3⟩ := hL p hp
        exact ⟨h1.le, h2.le, by linarith⟩
    · right
      rw [union_comm, insert_insert_union_eq] at hx
      refine mem_convexHull_side (e := -1) (by norm_num) (fun p hp => ?_) (fun p hp => ?_) hx
        (by linarith)
      · obtain ⟨h1, h2, h3⟩ := hL p hp
        exact ⟨h1.le, h2.le, by linarith⟩
      · obtain ⟨h1, h2, h3⟩ := hU p hp
        exact ⟨h1.le, h2.le, by linarith⟩
  · exact union_subset
      (convexHull_mono (insert_subset_insert (insert_subset_insert subset_union_left)))
      (convexHull_mono (insert_subset_insert (insert_subset_insert subset_union_right)))

/-! ### Convex independence of the union -/

/-- A point `v ∈ U` is not in the hull of the other points of `B₀ ∪ U ∪ L` if `B₀ ∪ U` is
convex independent (general sign `e`). -/
lemma notMem_convexHull_side {U L : Set (ℝ × ℝ)} {e : ℝ} (he : e ≠ 0)
    (hU : ∀ p ∈ U, 0 < p.1 ∧ p.1 < 1 ∧ 0 < e * p.2)
    (hL : ∀ p ∈ L, 0 < p.1 ∧ p.1 < 1 ∧ e * p.2 < 0)
    (hCI : ConvexIndependent ℝ ((↑) : (insert (0, 0) (insert (1, 0) U) : Set (ℝ × ℝ)) → ℝ × ℝ))
    {v : ℝ × ℝ} (hv : v ∈ U) :
    v ∉ convexHull ℝ (insert (0, 0) (insert (1, 0) (U ∪ L)) \ {v}) := by
  intro hmem
  have hv2 : 0 < e * v.2 := (hU v hv).2.2
  have hv0 : v ≠ (0, 0) := by rintro rfl; simp at hv2
  have hv1 : v ≠ (1, 0) := by rintro rfl; simp at hv2
  have hvL : v ∉ L := fun h => by linarith [(hL v h).2.2]
  have hset : insert ((0 : ℝ), (0 : ℝ)) (insert ((1 : ℝ), (0 : ℝ)) (U ∪ L)) \ {v} =
      insert (0, 0) (insert (1, 0) (U \ {v})) ∪ L := by
    ext y
    simp only [Set.mem_sdiff, mem_insert_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨h | h | h | h, hne⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr ⟨h, hne⟩))
      · exact Or.inr h
    · rintro ((h | h | ⟨h, hne⟩) | h)
      · exact ⟨Or.inl h, fun hyv => hv0 (hyv.symm.trans h)⟩
      · exact ⟨Or.inr (Or.inl h), fun hyv => hv1 (hyv.symm.trans h)⟩
      · exact ⟨Or.inr (Or.inr (Or.inl h)), hne⟩
      · exact ⟨Or.inr (Or.inr (Or.inr h)), fun hyv => hvL (hyv ▸ h)⟩
  rw [hset] at hmem
  have hside := mem_convexHull_side he
    (fun p hp => ⟨(hU p hp.1).1.le, (hU p hp.1).2.1.le, (hU p hp.1).2.2.le⟩)
    (fun p hp => ⟨(hL p hp).1.le, (hL p hp).2.1.le, (hL p hp).2.2.le⟩) hmem hv2.le
  have hsub : insert ((0 : ℝ), (0 : ℝ)) (insert ((1 : ℝ), (0 : ℝ)) (U \ {v})) ⊆
      insert (0, 0) (insert (1, 0) U) \ {v} := by
    rintro y (rfl | rfl | ⟨hyU, hyv⟩)
    · exact ⟨mem_insert _ _, fun h => hv0 (Eq.symm h)⟩
    · exact ⟨mem_insert_of_mem _ (mem_insert _ _), fun h => hv1 (Eq.symm h)⟩
    · exact ⟨mem_insert_of_mem _ (mem_insert_of_mem _ hyU), hyv⟩
  exact convexIndependent_set_iff_notMem_convexHull_sdiff.1 hCI v
    (mem_insert_of_mem _ (mem_insert_of_mem _ hv)) (convexHull_mono hsub hside)

theorem convexIndependent_caps_union {U L : Set (ℝ × ℝ)}
    (hU : ∀ p ∈ U, 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2) (hL : ∀ p ∈ L, 0 < p.1 ∧ p.1 < 1 ∧ p.2 < 0) :
    ConvexIndependent ℝ ((↑) : (insert (0, 0) (insert (1, 0) (U ∪ L)) : Set (ℝ × ℝ)) → ℝ × ℝ) ↔
      ConvexIndependent ℝ ((↑) : (insert (0, 0) (insert (1, 0) U) : Set (ℝ × ℝ)) → ℝ × ℝ) ∧
        ConvexIndependent ℝ ((↑) : (insert (0, 0) (insert (1, 0) L) : Set (ℝ × ℝ)) → ℝ × ℝ) := by
  constructor
  · intro h
    exact ⟨h.mono (insert_subset_insert (insert_subset_insert subset_union_left)),
      h.mono (insert_subset_insert (insert_subset_insert subset_union_right))⟩
  · rintro ⟨hCU, hCL⟩
    rw [convexIndependent_set_iff_notMem_convexHull_sdiff]
    rintro x (rfl | rfl | hxU | hxL)
    · -- `(0,0)`: all other points have `x > 0`
      intro hmem
      have hsub : insert ((0 : ℝ), (0 : ℝ)) (insert ((1 : ℝ), (0 : ℝ)) (U ∪ L)) \ {(0, 0)} ⊆
          LinearMap.fst ℝ ℝ ℝ ⁻¹' Ioi 0 := by
        rintro y ⟨hy | hy | hy | hy, hne⟩
        · exact absurd hy hne
        · subst hy; show (0 : ℝ) < 1; norm_num
        · exact (hU y hy).1
        · exact (hL y hy).1
      have := convexHull_min hsub ((convex_Ioi 0).linear_preimage _) hmem
      simp at this
    · -- `(1,0)`: all other points have `x < 1`
      intro hmem
      have hsub : insert ((0 : ℝ), (0 : ℝ)) (insert ((1 : ℝ), (0 : ℝ)) (U ∪ L)) \ {(1, 0)} ⊆
          LinearMap.fst ℝ ℝ ℝ ⁻¹' Iio 1 := by
        rintro y ⟨hy | hy | hy | hy, hne⟩
        · subst hy; show (0 : ℝ) < 1; norm_num
        · exact absurd hy hne
        · exact (hU y hy).2.1
        · exact (hL y hy).2.1
      have := convexHull_min hsub ((convex_Iio 1).linear_preimage _) hmem
      simp at this
    · exact notMem_convexHull_side (e := 1) one_ne_zero
        (fun p hp => by obtain ⟨h1, h2, h3⟩ := hU p hp; exact ⟨h1, h2, by linarith⟩)
        (fun p hp => by obtain ⟨h1, h2, h3⟩ := hL p hp; exact ⟨h1, h2, by linarith⟩) hCU hxU
    · rw [union_comm]
      exact notMem_convexHull_side (e := -1) (by norm_num)
        (fun p hp => by obtain ⟨h1, h2, h3⟩ := hL p hp; exact ⟨h1, h2, by linarith⟩)
        (fun p hp => by obtain ⟨h1, h2, h3⟩ := hU p hp; exact ⟨h1, h2, by linarith⟩) hCL hxL

/-! ### Families: `baseCfg` -/

lemma injective_baseCfg_iff {m : ℕ} (z : Fin m → ℝ × ℝ) (hz : ∀ i, (z i).2 ≠ 0) :
    Function.Injective (baseCfg z) ↔ Function.Injective z := by
  show Function.Injective (Fin.cons (0, 0) (Fin.cons (1, 0) z : Fin (m + 1) → ℝ × ℝ) :
      Fin (m + 1).succ → ℝ × ℝ) ↔ _
  rw [Fin.cons_injective_iff, Fin.cons_injective_iff, Fin.range_cons]
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · intro h
    refine ⟨?_, ?_, h⟩
    · rintro (h0 | ⟨i, hi⟩)
      · simp at h0
      · exact hz i (by rw [hi])
    · rintro ⟨i, hi⟩
      exact hz i (by rw [hi])

/-- Convex independence of `baseCfg f` as injectivity plus convex independence of the set. -/
lemma convexIndependent_baseCfg_iff {n : ℕ} (f : Fin n → ℝ × ℝ) (hf : ∀ i, (f i).2 ≠ 0) :
    ConvexIndependent ℝ (baseCfg f) ↔ Function.Injective f ∧
      ConvexIndependent ℝ
        ((↑) : (insert (0, 0) (insert (1, 0) (range f)) : Set (ℝ × ℝ)) → ℝ × ℝ) := by
  constructor
  · intro h
    have hi := h.injective
    refine ⟨(injective_baseCfg_iff f hf).1 hi, ?_⟩
    have := hi.convexIndependent_iff_set (𝕜 := ℝ)
    rw [range_baseCfg] at this
    exact this.2 h
  · rintro ⟨hi, hs⟩
    have hi' := (injective_baseCfg_iff f hf).2 hi
    have := hi'.convexIndependent_iff_set (𝕜 := ℝ)
    rw [range_baseCfg] at this
    exact this.1 hs

/-- Injectivity transfers between `z` and `(u, l)` when the ranges are disjoint and the
sizes add up. -/
lemma injective_split_iff {m a b : ℕ} (z : Fin m → ℝ × ℝ) (u : Fin a → ℝ × ℝ)
    (l : Fin b → ℝ × ℝ) (hm : m = a + b) (hz : range z = range u ∪ range l)
    (hdisj : Disjoint (range u) (range l)) :
    Function.Injective z ↔ Function.Injective u ∧ Function.Injective l := by
  classical
  have key : ∀ {n : ℕ} (f : Fin n → ℝ × ℝ),
      Function.Injective f ↔ (Finset.univ.image f).card = n := fun {n} f => by
    have := Finset.card_image_iff (s := (Finset.univ : Finset (Fin n))) (f := f)
    rw [Finset.card_univ, Fintype.card_fin, Finset.coe_univ, Set.injOn_univ] at this
    exact this.symm
  have himg : Finset.univ.image z = Finset.univ.image u ∪ Finset.univ.image l := by
    apply Finset.coe_injective
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ, hz]
  have hdis : Disjoint (Finset.univ.image u) (Finset.univ.image l) := by
    rw [← Finset.disjoint_coe]
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hdisj
  have hcu : (Finset.univ.image u).card ≤ a := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin a))) (f := u)
  have hcl : (Finset.univ.image l).card ≤ b := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin b))) (f := l)
  rw [key z, key u, key l, himg, Finset.card_union_of_disjoint hdis]
  omega

theorem convexIndependent_baseCfg_split {m a b : ℕ} (z : Fin m → ℝ × ℝ) (u : Fin a → ℝ × ℝ)
    (l : Fin b → ℝ × ℝ) (hm : m = a + b) (hz : range z = range u ∪ range l)
    (hu : ∀ i, 0 < (u i).1 ∧ (u i).1 < 1 ∧ 0 < (u i).2)
    (hl : ∀ i, 0 < (l i).1 ∧ (l i).1 < 1 ∧ (l i).2 < 0) :
    ConvexIndependent ℝ (baseCfg z) ↔
      ConvexIndependent ℝ (baseCfg u) ∧ ConvexIndependent ℝ (baseCfg l) := by
  have hu0 : ∀ i, (u i).2 ≠ 0 := fun i => (hu i).2.2.ne'
  have hl0 : ∀ i, (l i).2 ≠ 0 := fun i => (hl i).2.2.ne
  have hz0 : ∀ i, (z i).2 ≠ 0 := by
    intro i
    have : z i ∈ range u ∪ range l := hz ▸ mem_range_self i
    rcases this with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [← hj]; exact hu0 j
    · rw [← hj]; exact hl0 j
  have hdisj : Disjoint (range u) (range l) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    have h1 := (hu i).2.2
    have h2 := (hl j).2.2
    rw [hj] at h2
    linarith
  have hU : ∀ p ∈ range u, 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 := by
    rintro _ ⟨i, rfl⟩; exact hu i
  have hL : ∀ p ∈ range l, 0 < p.1 ∧ p.1 < 1 ∧ p.2 < 0 := by
    rintro _ ⟨i, rfl⟩; exact hl i
  rw [convexIndependent_baseCfg_iff z hz0, convexIndependent_baseCfg_iff u hu0,
    convexIndependent_baseCfg_iff l hl0, hz, convexIndependent_caps_union hU hL,
    injective_split_iff z u l hm hz hdisj]
  tauto

/-! ### Areas -/

lemma volume_xAxis : volume {p : ℝ × ℝ | p.2 = 0} = 0 := by
  have : {p : ℝ × ℝ | p.2 = 0} = univ ×ˢ {0} := by
    ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem hullArea_baseCfg_split {m a b : ℕ} (z : Fin m → ℝ × ℝ) (u : Fin a → ℝ × ℝ)
    (l : Fin b → ℝ × ℝ) (hz : range z = range u ∪ range l)
    (hu : ∀ i, 0 < (u i).1 ∧ (u i).1 < 1 ∧ 0 < (u i).2)
    (hl : ∀ i, 0 < (l i).1 ∧ (l i).1 < 1 ∧ (l i).2 < 0) :
    hullArea (baseCfg z) = hullArea (baseCfg u) + hullArea (baseCfg l) := by
  have hU : ∀ p ∈ range u, 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 := by
    rintro _ ⟨i, rfl⟩; exact hu i
  have hL : ∀ p ∈ range l, 0 < p.1 ∧ p.1 < 1 ∧ p.2 < 0 := by
    rintro _ ⟨i, rfl⟩; exact hl i
  unfold hullArea
  rw [range_baseCfg, range_baseCfg, range_baseCfg, hz, convexHull_caps_union hU hL]
  have hmeas : MeasurableSet (convexHull ℝ (insert ((0 : ℝ), (0 : ℝ))
      (insert ((1 : ℝ), (0 : ℝ)) (range l)))) :=
    (Set.Finite.isClosed_convexHull (𝕜 := ℝ)
      (((Set.finite_range l).insert _).insert _)).measurableSet
  have hnull : volume (convexHull ℝ (insert ((0 : ℝ), (0 : ℝ)) (insert ((1 : ℝ), (0 : ℝ))
      (range u))) ∩ convexHull ℝ (insert (0, 0) (insert (1, 0) (range l)))) = 0 := by
    refine measure_mono_null ?_ volume_xAxis
    rintro p ⟨hpU, hpL⟩
    have h1 := (convexHull_base_subset_strip (e := 1) (fun q hq =>
      ⟨(hU q hq).1.le, (hU q hq).2.1.le, by linarith [(hU q hq).2.2]⟩) hpU).2.2
    have h2 := (convexHull_base_subset_strip (e := -1) (fun q hq =>
      ⟨(hL q hq).1.le, (hL q hq).2.1.le, by linarith [(hL q hq).2.2]⟩) hpL).2.2
    show p.2 = 0
    linarith
  rw [← measure_union_add_inter _ hmeas, hnull, add_zero]

end KHoles
