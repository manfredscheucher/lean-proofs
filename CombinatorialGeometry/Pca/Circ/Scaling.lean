/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: scaling the planes (`doc/pca/circ.md`, decision C-D2)

Source: arXiv:1712.02149 (v6), proof of Theorem 1: "for time `t ≥ 1` let `ℰ_t := {1/t · E}`";
proof of Theorem 16: `ℰ_t := {t · E}`. Scaling the plane `⟨u, x⟩ = h` by `λ` gives
`⟨u, x⟩ = λ h`.

`IsCircleRep.scale`: a representation stays a representation (with the same directions) when the
planes are scaled along a continuous path `c : [0, 1] → ℝ`, `c 0 = 1`, as long as no event happens:
the scaled planes give circles, the scaled pairs of circles still cross (foot point inside), and no
three scaled circles pass through a common point of the sphere. `IsCircleRep.scale_in`: for
inward scaling (`0 ≤ c ≤ 1`) only the last condition remains.
-/
import Pca.Circ.Transfer

open Equiv Finset Matrix Set

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

theorem foot_smul (ui uj : V) (hi hj t : ℝ) :
    foot ui uj (t * hi) (t * hj) = t • foot ui uj hi hj := by
  unfold foot
  ext k; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring

theorem interPt_scale (ui uj : V) (hi hj ε t : ℝ) :
    interPt ui uj (t * hi) (t * hj) ε = t • foot ui uj hi hj +
      (ε * Real.sqrt ((1 - t ^ 2 * (foot ui uj hi hj ⬝ᵥ foot ui uj hi hj)) /
        ((ui ⨯₃ uj) ⬝ᵥ (ui ⨯₃ uj)))) • (ui ⨯₃ uj) := by
  unfold interPt
  rw [foot_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq]

/-- The canonical dart of a crossing. -/
noncomputable def cdart (A : Arrangement n D) (x : A.Crossing) : D :=
  Quotient.out (s := Perm.SameCycle.setoid A.σ) x

theorem crossingOf_cdart (x : A.Crossing) : A.crossingOf (cdart A x) = x := Quotient.out_eq _

theorem curves_cdart (x : A.Crossing) : Arrangement.Crossing.curves A x =
    {A.curve (cdart A x), A.curve (A.σ (cdart A x))} := by
  rw [← A.curves_crossingOf, crossingOf_cdart]

namespace IsCircleRep

variable {u : Fin n → V} {h : Fin n → ℝ} {pt : A.Crossing → V} {sgn : D → ℝ}

/-- The foot point of two crossing circles is inside the ball (no tangency). -/
theorem foot_lt_one (R : IsCircleRep A u h pt sgn) {i j : Fin n} (hij : i ≠ j) :
    foot (u i) (u j) (h i) (h j) ⬝ᵥ foot (u i) (u j) (h i) (h j) < 1 := by
  obtain ⟨x, -, -, hx, -⟩ := exists_pair A hij
  obtain ⟨d, hdx, hdi⟩ := exists_dart_of_mem (show i ∈ Arrangement.Crossing.curves A x by
    rw [hx]; simp)
  have hdj := curve_σ_eq hx hdx hdi
  have hw := R.cross_ne_zero hij
  have hpi := R.on_plane d
  have hpj := R.on_plane (A.σ d)
  rw [A.crossingOf_σ, hdx, hdj] at hpj
  rw [hdx, hdi] at hpi
  obtain ⟨l, hl, hl2⟩ := exists_lam hw (R.on_sphere x) hpi hpj
  have hdet := R.det3_ne_zero d
  rw [hdi, hdj, hdx, det3_cross, hl, dotProduct_add, cross_dot_foot, zero_add,
    dotProduct_smul, smul_eq_mul] at hdet
  have hl0 : l ≠ 0 := fun e => hdet (by rw [e, zero_mul])
  have := dot_self_pos hw
  have : 0 < l ^ 2 := by positivity
  nlinarith

/-- **Scaling** (C-D2): no event along the scaling path `c`, no change. -/
theorem scale (R : IsCircleRep A u h pt sgn) {c : ℝ → ℝ} (hc : ContinuousOn c (Icc 0 1))
    (hc0 : c 0 = 1)
    (hcirc : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i, (c s * h i) ^ 2 < u i ⬝ᵥ u i)
    (hfoot : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j, i ≠ j →
      c s ^ 2 * (foot (u i) (u j) (h i) (h j) ⬝ᵥ foot (u i) (u j) (h i) (h j)) < 1)
    (htriple : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → ∀ p : V,
      p ⬝ᵥ p = 1 → u i ⬝ᵥ p = c s * h i → u j ⬝ᵥ p = c s * h j → u k ⬝ᵥ p = c s * h k → False) :
    ∃ pt' : A.Crossing → V, IsCircleRep A u (fun i => c 1 * h i) pt' sgn := by
  -- the data of a crossing
  let I : A.Crossing → Fin n := fun x => A.curve (cdart A x)
  let J : A.Crossing → Fin n := fun x => A.curve (A.σ (cdart A x))
  have hIJ : ∀ x, I x ≠ J x := fun x => (A.isArrangement.curve_σ _).symm
  let ε : A.Crossing → ℝ := fun x => if 0 < det3 (u (I x)) (u (J x)) (pt x) then 1 else -1
  let q : A.Crossing → ℝ → V := fun x s =>
    interPt (u (I x)) (u (J x)) (c s * h (I x)) (c s * h (J x)) (ε x)
  have hε : ∀ x, ε x ^ 2 = 1 := fun x => by
    simp only [ε]; split_ifs <;> norm_num
  have hw : ∀ x, u (I x) ⨯₃ u (J x) ≠ 0 := fun x => R.cross_ne_zero (hIJ x)
  have hcx : ∀ x, Arrangement.Crossing.curves A x = {I x, J x} := curves_cdart
  have hdet0 : ∀ x, det3 (u (I x)) (u (J x)) (pt x) ≠ 0 := fun x => by
    have := R.det3_ne_zero (cdart A x); rwa [crossingOf_cdart] at this
  have honI : ∀ x, u (I x) ⬝ᵥ pt x = h (I x) := fun x => by
    have := R.on_plane (cdart A x); rwa [crossingOf_cdart] at this
  have honJ : ∀ x, u (J x) ⬝ᵥ pt x = h (J x) := fun x => by
    have := R.on_plane (A.σ (cdart A x)); rwa [A.crossingOf_σ, crossingOf_cdart] at this
  have hq0 : ∀ x, q x 0 = pt x := fun x => by
    simp only [q, hc0, one_mul]
    exact (eq_interPt (hw x) (R.on_sphere x) (honI x) (honJ x) (hdet0 x)).symm
  have hfoot' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, foot (u (I x)) (u (J x)) (c s * h (I x))
      (c s * h (J x)) ⬝ᵥ foot (u (I x)) (u (J x)) (c s * h (I x)) (c s * h (J x)) < 1 := by
    intro s hs x
    rw [foot_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq]
    exact hfoot s hs _ _ (hIJ x)
  -- the sign of `det3 u_I u_J (q x s)` is `ε x`, and it is nonzero
  have hdetq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, 0 < ε x * det3 (u (I x)) (u (J x)) (q x s) := by
    intro s hs x
    simp only [q]
    rw [det3_interPt]
    have hpos := dot_self_pos (hw x)
    have hr : 0 < Real.sqrt ((1 - foot (u (I x)) (u (J x)) (c s * h (I x)) (c s * h (J x)) ⬝ᵥ
        foot (u (I x)) (u (J x)) (c s * h (I x)) (c s * h (J x))) /
        ((u (I x) ⨯₃ u (J x)) ⬝ᵥ (u (I x) ⨯₃ u (J x)))) :=
      Real.sqrt_pos.2 (div_pos (by linarith [hfoot' s hs x]) hpos)
    have key : ∀ r W : ℝ, 0 < r → 0 < W → 0 < ε x * (ε x * r * W) := fun r W hr hW => by
      rw [show ε x * (ε x * r * W) = ε x ^ 2 * (r * W) by ring, hε, one_mul]
      exact mul_pos hr hW
    exact key _ _ hr hpos
  have hpm : ∀ x, ε x = 1 ∨ ε x = -1 := fun x => by simp only [ε]; split_ifs <;> simp
  -- for either order of the curves of `x`, the sign of `det3` along the path is constant
  have hsign : ∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : A.Crossing) (i j : Fin n),
      (i = I x ∧ j = J x) ∨ (i = J x ∧ j = I x) →
      0 < det3 (u i) (u j) (q x s) * det3 (u i) (u j) (pt x) := by
    intro s hs x i j hij
    have h1 := hdetq s hs x
    have h0 := hdetq 0 ⟨le_rfl, zero_le_one⟩ x
    rw [hq0] at h0
    have key : 0 < det3 (u (I x)) (u (J x)) (q x s) * det3 (u (I x)) (u (J x)) (pt x) :=
      mul_pos_of_sgn (hpm x) h1 h0
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact key
    · rw [det3_swap (u (I x)) (u (J x)) (q x s), det3_swap (u (I x)) (u (J x)) (pt x),
        neg_mul_neg]
      exact key
  -- apply the transfer lemma
  have hu : ∀ i, ContinuousOn (fun _ : ℝ => u i) (Icc 0 1) := fun i => continuousOn_const
  have hqc : ∀ x, ContinuousOn (q x) (Icc 0 1) := by
    intro x
    have e : q x = fun s => c s • foot (u (I x)) (u (J x)) (h (I x)) (h (J x)) +
        (ε x * Real.sqrt ((1 - c s ^ 2 * (foot (u (I x)) (u (J x)) (h (I x)) (h (J x)) ⬝ᵥ
          foot (u (I x)) (u (J x)) (h (I x)) (h (J x)))) /
          ((u (I x) ⨯₃ u (J x)) ⬝ᵥ (u (I x) ⨯₃ u (J x))))) • (u (I x) ⨯₃ u (J x)) := by
      funext s; exact interPt_scale _ _ _ _ _ _
    rw [e]
    have hs : ContinuousOn (fun s => Real.sqrt ((1 - c s ^ 2 * (foot (u (I x)) (u (J x))
        (h (I x)) (h (J x)) ⬝ᵥ foot (u (I x)) (u (J x)) (h (I x)) (h (J x)))) /
        ((u (I x) ⨯₃ u (J x)) ⬝ᵥ (u (I x) ⨯₃ u (J x))))) (Icc 0 1) :=
      Real.continuous_sqrt.comp_continuousOn
        (((continuousOn_const.sub ((hc.pow 2).mul continuousOn_const))).div_const _)
    exact (hc.smul continuousOn_const).add ((continuousOn_const.mul hs).smul continuousOn_const)
  have hR0 : IsCircleRep A ((fun _ : ℝ => u) 0) ((fun s i => c s * h i) 0)
      (fun x => q x 0) sgn := by
    have e1 : (fun x => q x 0) = pt := funext hq0
    have e2 : ((fun s i => c s * h i) 0 : Fin n → ℝ) = h := by funext i; simp [hc0]
    rw [e1, e2]; exact R
  have hon : ∀ s ∈ Icc (0 : ℝ) 1, ∀ d, u (A.curve d) ⬝ᵥ q (A.crossingOf d) s =
      c s * h (A.curve d) := by
    intro s hs d
    have hmem := A.mem_curves_crossingOf d
    rw [hcx] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with e | e
    · rw [e]; exact dot_interPt_left _ _ _ _ _ (hw _)
    · rw [e]; exact dot_interPt_right _ _ _ _ _ (hw _)
  have hsph : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, q x s ⬝ᵥ q x s = 1 := fun s hs x =>
    interPt_on_sphere _ _ _ _ _ (hw x) (hε x) (hfoot' s hs x).le
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
  refine ⟨fun x => q x 1, IsCircleRep.transfer (u := fun _ => u) (h := fun s i => c s * h i)
    (q := q) hR0 hu hqc (fun s hs i => hcirc s hs i) hsph hon ?_ ?_⟩
  · -- injectivity
    intro s hs x y hxy
    simp only at hxy
    by_cases hcur : Arrangement.Crossing.curves A x = Arrangement.Crossing.curves A y
    · -- same pair: the signs agree, so the original points agree
      have hy : (I x = I y ∧ J x = J y) ∨ (I x = J y ∧ J x = I y) := by
        have e := (hcx x).symm.trans (hcur.trans (hcx y))
        have h1 : I x ∈ ({I y, J y} : Finset (Fin n)) := by rw [← e]; simp
        have h2 : J x ∈ ({I y, J y} : Finset (Fin n)) := by rw [← e]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) (hIJ x)
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
        · exact absurd (h1.trans h2.symm) (hIJ x)
      have sx := hsign s hs x (I x) (J x) (Or.inl ⟨rfl, rfl⟩)
      have sy := hsign s hs y (I x) (J x) hy
      rw [hxy] at sx
      have hd0y : det3 (u (I x)) (u (J x)) (q y s) ≠ 0 := by
        intro e; rw [e, zero_mul] at sy; exact lt_irrefl _ sy
      have hb : (0 < det3 (u (I x)) (u (J x)) (pt x)) ↔ (0 < det3 (u (I x)) (u (J x)) (pt y)) := by
        constructor
        · intro hp
          rcases lt_or_gt_of_ne hd0y with h1 | h1
          · nlinarith
          · by_contra hn; push_neg at hn; nlinarith
        · intro hp
          rcases lt_or_gt_of_ne hd0y with h1 | h1
          · nlinarith
          · by_contra hn; push_neg at hn; nlinarith
      have hyI : u (I x) ⬝ᵥ pt y = h (I x) := by
        rcases hy with ⟨e1, -⟩ | ⟨e1, -⟩
        · rw [e1]; exact honI y
        · rw [e1]; exact honJ y
      have hyJ : u (J x) ⬝ᵥ pt y = h (J x) := by
        rcases hy with ⟨-, e2⟩ | ⟨-, e2⟩
        · rw [e2]; exact honJ y
        · rw [e2]; exact honI y
      have hdy : det3 (u (I x)) (u (J x)) (pt y) ≠ 0 := by
        intro e; rw [e, mul_zero] at sy; exact lt_irrefl _ sy
      have ex := eq_interPt (hw x) (R.on_sphere x) (honI x) (honJ x) (hdet0 x)
      have ey := eq_interPt (hw x) (R.on_sphere y) hyI hyJ hdy
      apply R.inj
      rw [ex, ey]
      simp only [hb]
    · -- different pairs: three circles through a point
      obtain ⟨k, hky, hkx⟩ : ∃ k ∈ Arrangement.Crossing.curves A y,
          k ∉ Arrangement.Crossing.curves A x := by
        by_contra hc'
        push_neg at hc'
        exact hcur (Finset.eq_of_subset_of_card_le hc' (by rw [A.card_curves, A.card_curves])).symm
      rw [hcx] at hkx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkx
      obtain ⟨d, hdy, hdk⟩ := exists_dart_of_mem hky
      have hpk := hon s hs d
      rw [hdy, hdk, ← hxy] at hpk
      have hpI := hon s hs (cdart A x)
      have hpJ := hon s hs (A.σ (cdart A x))
      rw [crossingOf_cdart] at hpI
      rw [A.crossingOf_σ, crossingOf_cdart] at hpJ
      exact (htriple s hs (I x) (J x) k (hIJ x) (Ne.symm hkx.1) (Ne.symm hkx.2) (q x s)
        (hsph s hs x) hpI hpJ hpk).elim
  · -- no tangency
    intro s hs d
    have h1 := hsign s hs (A.crossingOf d) (A.curve d) (A.curve (A.σ d)) (by
      rcases hpair _ d rfl with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1, e2⟩
      · exact Or.inr ⟨e1, e2⟩)
    intro e
    rw [e, zero_mul] at h1
    exact lt_irrefl _ h1

/-- **Inward scaling**: for `0 ≤ c ≤ 1` only triple points have to be excluded. -/
theorem scale_in (R : IsCircleRep A u h pt sgn) {c : ℝ → ℝ} (hc : ContinuousOn c (Icc 0 1))
    (hc0 : c 0 = 1) (hc01 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ c s ∧ c s ≤ 1)
    (htriple : ∀ s ∈ Icc (0 : ℝ) 1, ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → ∀ p : V,
      p ⬝ᵥ p = 1 → u i ⬝ᵥ p = c s * h i → u j ⬝ᵥ p = c s * h j → u k ⬝ᵥ p = c s * h k → False) :
    ∃ pt' : A.Crossing → V, IsCircleRep A u (fun i => c 1 * h i) pt' sgn := by
  refine R.scale hc hc0 ?_ ?_ htriple
  · intro s hs i
    have h1 := R.isCircle i
    obtain ⟨a, b⟩ := hc01 s hs
    have : c s ^ 2 ≤ 1 := by nlinarith
    calc (c s * h i) ^ 2 = c s ^ 2 * h i ^ 2 := by ring
      _ ≤ 1 * h i ^ 2 := by gcongr
      _ < _ := by linarith
  · intro s hs i j hij
    have h1 := R.foot_lt_one hij
    obtain ⟨a, b⟩ := hc01 s hs
    have : c s ^ 2 ≤ 1 := by nlinarith
    have h0 := dot_self_nonneg (foot (u i) (u j) (h i) (h j))
    nlinarith

end IsCircleRep

end Pca.Circ
