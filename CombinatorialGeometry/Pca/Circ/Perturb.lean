/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: small perturbations (`doc/pca/circ.md`, decision C-D4)

Representations are open: for every continuous family of planes `U τ`, `H τ` through the planes
of a representation at `τ = 0`, the planes `U τ`, `H τ` still represent the arrangement for all
small `τ ≥ 0` (`IsCircleRep.perturb`). Proof: all conditions of the transfer lemma (C-D2) are
strict inequalities between functions continuous at `τ = 0`, so they hold near `0`; then transfer
along `s ↦ s τ`.
-/
import Pca.Circ.Scaling

open Equiv Finset Matrix Set Filter Topology

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

theorem continuous_cross : Continuous (fun t : V × V => t.1 ⨯₃ t.2) := by
  have h0 : Continuous (fun t : V × V => (t.1 ⨯₃ t.2) 0) := by simp only [cross_0]; fun_prop
  have h1 : Continuous (fun t : V × V => (t.1 ⨯₃ t.2) 1) := by simp only [cross_1]; fun_prop
  have h2 : Continuous (fun t : V × V => (t.1 ⨯₃ t.2) 2) := by simp only [cross_2]; fun_prop
  refine continuous_pi fun k => ?_
  fin_cases k
  exacts [h0, h1, h2]

theorem continuous_dot : Continuous (fun p : V × V => p.1 ⬝ᵥ p.2) := by
  simp only [dot_eq]; fun_prop

theorem contAt_cross {f g : ℝ → V} {τ : ℝ} (hf : ContinuousAt f τ) (hg : ContinuousAt g τ) :
    ContinuousAt (fun t => f t ⨯₃ g t) τ :=
  continuous_cross.continuousAt.comp (f := fun t => (f t, g t)) (hf.prodMk hg)

theorem contAt_dot {f g : ℝ → V} {τ : ℝ} (hf : ContinuousAt f τ) (hg : ContinuousAt g τ) :
    ContinuousAt (fun t => f t ⬝ᵥ g t) τ :=
  continuous_dot.continuousAt.comp (f := fun t => (f t, g t)) (hf.prodMk hg)

theorem continuousAt_foot {ui uj : ℝ → V} {hi hj : ℝ → ℝ} {τ : ℝ} (h1 : ContinuousAt ui τ)
    (h2 : ContinuousAt uj τ) (h3 : ContinuousAt hi τ) (h4 : ContinuousAt hj τ)
    (hw : ui τ ⨯₃ uj τ ≠ 0) :
    ContinuousAt (fun t => foot (ui t) (uj t) (hi t) (hj t)) τ := by
  have hw' : ContinuousAt (fun t => ui t ⨯₃ uj t) τ := contAt_cross h1 h2
  have hww : ContinuousAt (fun t => (ui t ⨯₃ uj t) ⬝ᵥ (ui t ⨯₃ uj t)) τ := contAt_dot hw' hw'
  have hne : (ui τ ⨯₃ uj τ) ⬝ᵥ (ui τ ⨯₃ uj τ) ≠ 0 := (dot_self_pos hw).ne'
  have a1 : ContinuousAt (fun t => uj t ⨯₃ (ui t ⨯₃ uj t)) τ := contAt_cross h2 hw'
  have a2 : ContinuousAt (fun t => (ui t ⨯₃ uj t) ⨯₃ ui t) τ := contAt_cross hw' h1
  have a3 : ContinuousAt (fun t => hi t • (uj t ⨯₃ (ui t ⨯₃ uj t)) +
      hj t • ((ui t ⨯₃ uj t) ⨯₃ ui t)) τ := (h3.fun_smul a1).add (h4.fun_smul a2)
  have a4 : ContinuousAt (fun t => 1 / ((ui t ⨯₃ uj t) ⬝ᵥ (ui t ⨯₃ uj t))) τ :=
    continuousAt_const.div hww hne
  exact a4.fun_smul a3

theorem continuousAt_interPt {ui uj : ℝ → V} {hi hj : ℝ → ℝ} {τ ε : ℝ} (h1 : ContinuousAt ui τ)
    (h2 : ContinuousAt uj τ) (h3 : ContinuousAt hi τ) (h4 : ContinuousAt hj τ)
    (hw : ui τ ⨯₃ uj τ ≠ 0) :
    ContinuousAt (fun t => interPt (ui t) (uj t) (hi t) (hj t) ε) τ := by
  have hw' : ContinuousAt (fun t => ui t ⨯₃ uj t) τ := contAt_cross h1 h2
  have hww : ContinuousAt (fun t => (ui t ⨯₃ uj t) ⬝ᵥ (ui t ⨯₃ uj t)) τ := contAt_dot hw' hw'
  have hne : (ui τ ⨯₃ uj τ) ⬝ᵥ (ui τ ⨯₃ uj τ) ≠ 0 := (dot_self_pos hw).ne'
  have hf := continuousAt_foot h1 h2 h3 h4 hw
  have hff := contAt_dot hf hf
  have a1 : ContinuousAt (fun t => ε * Real.sqrt ((1 - foot (ui t) (uj t) (hi t) (hj t) ⬝ᵥ
      foot (ui t) (uj t) (hi t) (hj t)) / ((ui t ⨯₃ uj t) ⬝ᵥ (ui t ⨯₃ uj t)))) τ :=
    continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
      ((continuousAt_const.sub hff).div hww hne))
  exact hf.add (a1.fun_smul hw')

namespace IsCircleRep

variable {u : Fin n → V} {h : Fin n → ℝ} {pt : A.Crossing → V} {sgn : D → ℝ}

/-- **Openness** (C-D4): small perturbations of the planes of a representation still represent
the arrangement, with the same directions. -/
theorem perturb (R : IsCircleRep A u h pt sgn) {U : ℝ → Fin n → V} {H : ℝ → Fin n → ℝ}
    (hU : ∀ i, Continuous (fun τ => U τ i)) (hH : ∀ i, Continuous (fun τ => H τ i))
    (hU0 : U 0 = u) (hH0 : H 0 = h) :
    ∃ δ > 0, ∀ τ, 0 ≤ τ → τ < δ → ∃ pt' : A.Crossing → V, IsCircleRep A (U τ) (H τ) pt' sgn := by
  subst hU0 hH0
  let I : A.Crossing → Fin n := fun x => A.curve (cdart A x)
  let J : A.Crossing → Fin n := fun x => A.curve (A.σ (cdart A x))
  have hIJ : ∀ x, I x ≠ J x := fun x => (A.isArrangement.curve_σ _).symm
  let ε : A.Crossing → ℝ := fun x => if 0 < det3 (U 0 (I x)) (U 0 (J x)) (pt x) then 1 else -1
  have hε : ∀ x, ε x ^ 2 = 1 := fun x => by simp only [ε]; split_ifs <;> norm_num
  let W : A.Crossing → ℝ → V := fun x t => U t (I x) ⨯₃ U t (J x)
  let M : A.Crossing → ℝ → V := fun x t => foot (U t (I x)) (U t (J x)) (H t (I x)) (H t (J x))
  let q : A.Crossing → ℝ → V := fun x t =>
    interPt (U t (I x)) (U t (J x)) (H t (I x)) (H t (J x)) (ε x)
  have hcx : ∀ x, Arrangement.Crossing.curves A x = {I x, J x} := curves_cdart
  have hw0 : ∀ x, W x 0 ≠ 0 := fun x => R.cross_ne_zero (hIJ x)
  have hdet0 : ∀ x, det3 (U 0 (I x)) (U 0 (J x)) (pt x) ≠ 0 := fun x => by
    have := R.det3_ne_zero (cdart A x); rwa [crossingOf_cdart] at this
  have honI : ∀ x, U 0 (I x) ⬝ᵥ pt x = H 0 (I x) := fun x => by
    have := R.on_plane (cdart A x); rwa [crossingOf_cdart] at this
  have honJ : ∀ x, U 0 (J x) ⬝ᵥ pt x = H 0 (J x) := fun x => by
    have := R.on_plane (A.σ (cdart A x)); rwa [A.crossingOf_σ, crossingOf_cdart] at this
  have hq0 : ∀ x, q x 0 = pt x := fun x =>
    (eq_interPt (hw0 x) (R.on_sphere x) (honI x) (honJ x) (hdet0 x)).symm
  have hWc : ∀ x, ContinuousAt (W x) 0 := fun x =>
    contAt_cross (hU (I x)).continuousAt (hU (J x)).continuousAt
  -- the open conditions near `0`
  have e1 : ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), H t i ^ 2 < U t i ⬝ᵥ U t i := fun i =>
    ContinuousAt.eventually_lt ((hH i).pow 2).continuousAt
      (contAt_dot (hU i).continuousAt (hU i).continuousAt) (R.isCircle i)
  have e2 : ∀ x, ∀ᶠ t in 𝓝 (0 : ℝ), W x t ≠ 0 := fun x =>
    (hWc x).eventually_ne (hw0 x)
  have hMc : ∀ x, ContinuousAt (M x) 0 := fun x =>
    continuousAt_foot (hU (I x)).continuousAt (hU (J x)).continuousAt (hH (I x)).continuousAt
      (hH (J x)).continuousAt (hw0 x)
  have e3 : ∀ x, ∀ᶠ t in 𝓝 (0 : ℝ), M x t ⬝ᵥ M x t < 1 := fun x =>
    ContinuousAt.eventually_lt (contAt_dot (hMc x) (hMc x))
      continuousAt_const (R.foot_lt_one (hIJ x))
  have hqc : ∀ x t, W x t ≠ 0 → ContinuousAt (q x) t := fun x t hw =>
    continuousAt_interPt (hU (I x)).continuousAt (hU (J x)).continuousAt (hH (I x)).continuousAt
      (hH (J x)).continuousAt hw
  have e4 : ∀ p : A.Crossing × A.Crossing, ∀ᶠ t in 𝓝 (0 : ℝ), p.1 ≠ p.2 → q p.1 t ≠ q p.2 t := by
    intro p
    by_cases hp : p.1 = p.2
    · exact Eventually.of_forall fun _ h' => absurd hp h'
    · have := ((hqc p.1 0 (hw0 _)).sub (hqc p.2 0 (hw0 _))).eventually_ne
        (show q p.1 0 - q p.2 0 ≠ 0 by
          rw [hq0, hq0]; exact sub_ne_zero.2 (fun e => hp (R.inj e)))
      exact this.mono fun t ht _ he => ht (by simp only [Pi.sub_apply, he, sub_self])
  have hall : ∀ᶠ t in 𝓝 (0 : ℝ), (∀ i, H t i ^ 2 < U t i ⬝ᵥ U t i) ∧ (∀ x, W x t ≠ 0) ∧
      (∀ x, M x t ⬝ᵥ M x t < 1) ∧ (∀ p : A.Crossing × A.Crossing, p.1 ≠ p.2 → q p.1 t ≠ q p.2 t) :=
    (eventually_all.2 e1).and ((eventually_all.2 e2).and ((eventually_all.2 e3).and
      (eventually_all.2 e4)))
  obtain ⟨δ, hδ, hδall⟩ := Metric.eventually_nhds_iff.1 hall
  refine ⟨δ, hδ, fun τ hτ0 hτδ => ?_⟩
  have hin : ∀ s ∈ Icc (0 : ℝ) 1, dist (s * τ) 0 < δ := by
    intro s hs
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hs.1 hτ0)]
    calc s * τ ≤ 1 * τ := by gcongr; exact hs.2
      _ < δ := by linarith
  have hC : ∀ s ∈ Icc (0 : ℝ) 1, _ := fun s hs => hδall (hin s hs)
  -- the path `s ↦ s τ`
  have hpair : ∀ (x : A.Crossing) (d : D), A.crossingOf d = x →
      (A.curve d = I x ∧ A.curve (A.σ d) = J x) ∨ (A.curve d = J x ∧ A.curve (A.σ d) = I x) := by
    intro x d hdx
    have hmem := A.mem_curves_crossingOf d
    rw [hdx, hcx] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with e | e
    · exact Or.inl ⟨e, curve_σ_eq (hcx x) hdx e⟩
    · refine Or.inr ⟨e, curve_σ_eq (i := J x) (j := I x) ?_ hdx e⟩
      rw [hcx, Finset.pair_comm]
  have hR0 : IsCircleRep A (U (0 * τ)) (H (0 * τ)) (fun x => q x (0 * τ)) sgn := by
    simp only [zero_mul]
    have e : (fun x => q x 0) = pt := funext hq0
    rw [e]; exact R
  refine ⟨fun x => q x (1 * τ), ?_⟩
  have key := IsCircleRep.transfer (u := fun s => U (s * τ)) (h := fun s => H (s * τ))
    (q := fun x s => q x (s * τ)) hR0
    (fun i => ((hU i).comp (continuous_mul_const τ)).continuousOn)
    (fun x => by
      intro s hs
      exact ((hqc x (s * τ) ((hC s hs).2.1 x)).comp
        (continuous_mul_const τ).continuousAt (x := s)).continuousWithinAt)
    (fun s hs i => (hC s hs).1 i)
    (fun s hs x => interPt_on_sphere _ _ _ _ _ ((hC s hs).2.1 x) (hε x)
      ((hC s hs).2.2.1 x).le)
    (fun s hs d => by
      have hmem := A.mem_curves_crossingOf d
      rw [hcx] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with e | e
      · rw [e]; exact dot_interPt_left _ _ _ _ _ ((hC s hs).2.1 _)
      · rw [e]; exact dot_interPt_right _ _ _ _ _ ((hC s hs).2.1 _))
    (fun s hs x y hxy => by
      by_contra hne
      exact (hC s hs).2.2.2 (x, y) hne hxy)
    (fun s hs d => by
      have hdet := det3_interPt (U (s * τ) (I (A.crossingOf d))) (U (s * τ) (J (A.crossingOf d)))
        (H (s * τ) (I (A.crossingOf d))) (H (s * τ) (J (A.crossingOf d))) (ε (A.crossingOf d))
      have hw := (hC s hs).2.1 (A.crossingOf d)
      have hm := (hC s hs).2.2.1 (A.crossingOf d)
      have hpos := dot_self_pos hw
      have hr := Real.sqrt_pos.2 (div_pos (by linarith) hpos :
        0 < (1 - M (A.crossingOf d) (s * τ) ⬝ᵥ M (A.crossingOf d) (s * τ)) /
          (W (A.crossingOf d) (s * τ) ⬝ᵥ W (A.crossingOf d) (s * τ)))
      have hεne : ε (A.crossingOf d) ≠ 0 := by
        intro e; have := hε (A.crossingOf d); rw [e] at this; norm_num at this
      have hne : det3 (U (s * τ) (I (A.crossingOf d))) (U (s * τ) (J (A.crossingOf d)))
          (q (A.crossingOf d) (s * τ)) ≠ 0 := by
        simp only [q]; rw [hdet]
        exact mul_ne_zero (mul_ne_zero hεne hr.ne') hpos.ne'
      rcases hpair _ d rfl with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact hne
      · rw [e1, e2, det3_swap]; exact neg_ne_zero.2 hne)
  simpa using key

end IsCircleRep

end Pca.Circ
