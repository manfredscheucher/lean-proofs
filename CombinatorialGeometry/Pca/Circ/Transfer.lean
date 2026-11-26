/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: no event, no change (`doc/pca/circ.md`, decision C-D2)

The key analytic lemma of the scaling arguments (arXiv:1712.02149, proofs of Theorems 1, 16, 19,
27): along a continuous path of plane families with no event, the combinatorial type is constant.

`IsCircleRep.transfer` (C-D2): planes `u s`, `h s` and crossing points `q x s` for `s ∈ [0, 1]`,
continuous in `s`; for every `s` the planes give circles, the points are on the sphere and on the
planes of their curves, distinct (no three circles through a point), and not tangency points
(`det3 u_a u_b p ≠ 0`). If the data at `s = 0` is a representation of `A` (with directions `sgn`),
so is the data at `s = 1`, with the same directions. Proof: every sign condition of
`IsCircleRep` is a continuous function of `s` that never vanishes (three distinct points of a
circle are not collinear; tangents of non-tangent circles are independent), so it keeps its sign
(intermediate value theorem).
-/
import Pca.Circ.Fact1
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

open Equiv Finset Matrix Set

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- A continuous function on `[0, 1]` without zeros keeps its sign. -/
theorem pos_one_of_ne_zero {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) (h0 : 0 < f 0)
    (hne : ∀ s ∈ Icc (0 : ℝ) 1, f s ≠ 0) : 0 < f 1 := by
  by_contra h1
  push_neg at h1
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hf ⟨h1, h0.le⟩
  exact hne s hs hfs

theorem continuousOn_det3 {S : Set ℝ} {f g k : ℝ → V} (hf : ContinuousOn f S)
    (hg : ContinuousOn g S) (hk : ContinuousOn k S) :
    ContinuousOn (fun s => det3 (f s) (g s) (k s)) S := by
  have c : ∀ {F : ℝ → V}, ContinuousOn F S → ∀ i, ContinuousOn (fun s => F s i) S :=
    fun hF i => (continuous_apply i).comp_continuousOn hF
  simp only [det3_eq]
  have := c hf 0; have := c hf 1; have := c hf 2
  have := c hg 0; have := c hg 1; have := c hg 2
  have := c hk 0; have := c hk 1; have := c hk 2
  fun_prop

theorem curve_σ_eq {x : A.Crossing} {i j : Fin n} {d : D} (hx : Arrangement.Crossing.curves A x = {i, j})
    (hdx : A.crossingOf d = x) (hdi : A.curve d = i) : A.curve (A.σ d) = j := by
  have h1 := A.mem_curves_crossingOf_σ d
  rw [hdx, hx, Finset.mem_insert, Finset.mem_singleton] at h1
  rcases h1 with h1 | h1
  · exact absurd (h1.trans hdi.symm) (A.isArrangement.curve_σ d)
  · exact h1

namespace IsCircleRep

/-- **No event, no change** (C-D2). -/
theorem transfer {u : ℝ → Fin n → V} {h : ℝ → Fin n → ℝ} {q : A.Crossing → ℝ → V} {sgn : D → ℝ}
    (R : IsCircleRep A (u 0) (h 0) (fun x => q x 0) sgn)
    (hu : ∀ i, ContinuousOn (fun s => u s i) (Icc 0 1))
    (hq : ∀ x, ContinuousOn (q x) (Icc 0 1))
    (hcirc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, h s i ^ 2 < u s i ⬝ᵥ u s i)
    (hsph : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, q x s ⬝ᵥ q x s = 1)
    (hpl : ∀ s ∈ Icc (0 : ℝ) 1, ∀ d, u s (A.curve d) ⬝ᵥ q (A.crossingOf d) s = h s (A.curve d))
    (hinj : ∀ s ∈ Icc (0 : ℝ) 1, Function.Injective (fun x => q x s))
    (htan : ∀ s ∈ Icc (0 : ℝ) 1, ∀ d,
      det3 (u s (A.curve d)) (u s (A.curve (A.σ d))) (q (A.crossingOf d) s) ≠ 0) :
    IsCircleRep A (u 1) (h 1) (fun x => q x 1) sgn := by
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hune : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, u s i ≠ 0 := fun s hs i h0 => by
    have := hcirc s hs i
    rw [h0, zero_dotProduct] at this
    nlinarith [sq_nonneg (h s i)]
  have honc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : A.Crossing) (i : Fin n),
      i ∈ Arrangement.Crossing.curves A x → OnCirc (u s i) (h s i) (q x s) := by
    intro s hs x i hi
    obtain ⟨d, rfl, rfl⟩ := exists_dart_of_mem hi
    exact ⟨hsph s hs _, hpl s hs d⟩
  refine ⟨fun i => hcirc 1 h1 i, fun x => hsph 1 h1 x, fun d => hpl 1 h1 d, hinj 1 h1, ?_,
    R.sgn_pm, R.sgn_α, R.sgn_σσ, ?_, ?_⟩
  · -- surjectivity: two circles meet in at most two points
    intro i j p hij hp hpi hpj
    obtain ⟨z₁, z₂, hz, hz₁, hz₂⟩ := exists_pair A hij
    obtain ⟨d, hdz, hdi⟩ := exists_dart_of_mem (show i ∈ Arrangement.Crossing.curves A z₁ by
      rw [hz₁]; simp)
    have hw : u 1 i ⨯₃ u 1 j ≠ 0 := by
      intro h0
      have := htan 1 h1 d
      rw [hdi, curve_σ_eq hz₁ hdz hdi, det3_cross, h0, zero_dotProduct] at this
      exact this rfl
    obtain ⟨a₁, b₁⟩ := And.intro (honc 1 h1 z₁ i (by rw [hz₁]; simp))
      (honc 1 h1 z₁ j (by rw [hz₁]; simp))
    obtain ⟨a₂, b₂⟩ := And.intro (honc 1 h1 z₂ i (by rw [hz₂]; simp))
      (honc 1 h1 z₂ j (by rw [hz₂]; simp))
    by_contra hne
    push_neg at hne
    exact not_three_on_two_planes hw a₁.1 a₁.2 b₁.2 a₂.1 a₂.2 b₂.2 hp hpi hpj
      (fun e => hz (hinj 1 h1 e)) (hne z₁) (hne z₂)
  · -- order
    intro d z hz hzx hzy
    set a := A.curve d
    have hxy : A.crossingOf d ≠ A.crossingOf (A.α d) := (A.crossingOf_α_ne d).symm
    refine pos_one_of_ne_zero (f := fun s => sgn d * orient (u s a) (q (A.crossingOf d) s)
      (q (A.crossingOf (A.α d)) s) (q z s)) ?_ (R.next d z hz hzx hzy) ?_
    · unfold orient
      exact continuousOn_const.mul (continuousOn_det3 ((hq _).sub (hq _)) ((hq _).sub (hq _))
        (hu a))
    · intro s hs
      have hsgn : sgn d ≠ 0 := by rcases R.sgn_pm d with e | e <;> rw [e] <;> norm_num
      refine mul_ne_zero hsgn ((honc s hs _ a (A.mem_curves_crossingOf d)).orient_ne_zero
        (hune s hs a) (honc s hs _ a (A.mem_curves_end d))
        (honc s hs z a hz) ?_ ?_ ?_)
      · exact fun e => hxy (hinj s hs e)
      · exact fun e => hzx (hinj s hs e).symm
      · exact fun e => hzy (hinj s hs e).symm
  · -- orientation
    intro d
    refine pos_one_of_ne_zero (f := fun s => det3 (tangent (u s (A.curve d)) (sgn d)
      (q (A.crossingOf d) s)) (tangent (u s (A.curve (A.σ d))) (sgn (A.σ d))
      (q (A.crossingOf d) s)) (q (A.crossingOf d) s)) ?_ ?_ ?_
    · unfold tangent
      have hc : ∀ (i : Fin n) (c : ℝ), ContinuousOn
          (fun s => c • (u s i ⨯₃ q (A.crossingOf d) s)) (Icc 0 1) := by
        intro i c
        refine ContinuousOn.const_smul ?_ c
        have hcr : Continuous (fun t : V × V => t.1 ⨯₃ t.2) := by
          have : (fun t : V × V => t.1 ⨯₃ t.2) = fun t => ![t.1 1 * t.2 2 - t.1 2 * t.2 1,
              t.1 2 * t.2 0 - t.1 0 * t.2 2, t.1 0 * t.2 1 - t.1 1 * t.2 0] := by
            funext t; exact cross_apply _ _
          rw [this]
          refine continuous_pi fun k => ?_
          fin_cases k <;> simp <;> fun_prop
        exact hcr.comp_continuousOn ((hu i).prodMk (hq _))
      exact continuousOn_det3 (hc _ _) (hc _ _) (hq _)
    · exact R.rot d
    · intro s hs
      simp only [tangent]
      rw [det3_smul_smul, det3_cross_cross, hsph s hs, one_mul]
      have h1' : sgn d ≠ 0 := by rcases R.sgn_pm d with e | e <;> rw [e] <;> norm_num
      have h2' : sgn (A.σ d) ≠ 0 := by rcases R.sgn_pm (A.σ d) with e | e <;> rw [e] <;> norm_num
      exact mul_ne_zero (mul_ne_zero h1' h2') (htan s hs d)

end IsCircleRep

end Pca.Circ
