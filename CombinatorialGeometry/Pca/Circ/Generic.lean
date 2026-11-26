/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: generic representations (`doc/pca/circ.md`, decision C-D4)

Every circularizable arrangement has a **generic** representation: the normals of any three
planes are independent (`det3 ≠ 0`) and no four planes have a common point
(`CircleRep.exists_generic`). Proof: perturb the planes `(u_i, h_i)` along the moment curve,
`(u_i, h_i) + τ (1, i, i², i³)` (openness, C-D4); each degeneracy is the vanishing of a polynomial
in `τ` whose leading coefficient is a Vandermonde determinant, so only finitely many `τ` are bad.
-/
import Pca.Circ.Perturb
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

open Equiv Finset Matrix Set Polynomial

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- `det (M₀ + τ M₁) = 0` for only finitely many `τ` if `det M₁ ≠ 0`. -/
theorem finite_det_eq_zero {m : ℕ} (M₀ M₁ : Matrix (Fin m) (Fin m) ℝ) (h₁ : M₁.det ≠ 0) :
    {τ : ℝ | (M₀ + τ • M₁).det = 0}.Finite := by
  set P : ℝ[X] := (M₀.map C + (X : ℝ[X]) • M₁.map C).det
  have hP : ∀ τ, P.eval τ = (M₀ + τ • M₁).det := by
    intro τ
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j; simp; try ring
  set Q : ℝ[X] := ((X : ℝ[X]) • M₀.map C + M₁.map C).det
  have hQ : ∀ s, Q.eval s = (s • M₀ + M₁).det := by
    intro s
    rw [← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j; simp; try ring
  have hP0 : P ≠ 0 := by
    intro h0
    have hQ0 : Q = 0 := by
      apply eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono (s := {s : ℝ | s ≠ 0}) ?_ ?_
      · intro s hs
        simp only [Set.mem_ofPred_eq] at hs ⊢
        rw [IsRoot, hQ]
        have e : s • M₀ + M₁ = s • (M₀ + s⁻¹ • M₁) := by
          rw [smul_add, smul_smul, mul_inv_cancel₀ hs, one_smul]
        rw [e, det_smul, ← hP, h0, eval_zero, mul_zero]
      · exact (Set.finite_singleton (0 : ℝ)).infinite_compl.mono (fun s hs => hs)
    have := hQ 0
    rw [hQ0, eval_zero, zero_smul, zero_add] at this
    exact h₁ this.symm
  refine (finite_setOfPred_isRoot hP0).subset ?_
  intro τ hτ
  simp only [Set.mem_ofPred_eq] at hτ ⊢
  rw [IsRoot, hP]; exact hτ

/-- The moment curve point of a curve index. -/
noncomputable def mom (i : Fin n) : V := ![1, (i : ℝ), (i : ℝ) ^ 2]

theorem det_vandermonde_ne_zero {m : ℕ} {x : Fin m → ℝ} (hx : Function.Injective x) :
    (vandermonde x).det ≠ 0 := by
  rw [det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  exact sub_ne_zero.2 (fun e => (ne_of_gt (Finset.mem_Ioi.1 hj)) (hx e))

theorem cast_inj3 {a b c : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (![(a : ℝ), (b : ℝ), (c : ℝ)]) := by
  have h : ∀ {x y : Fin n}, x ≠ y → (x : ℕ) ≠ (y : ℕ) := fun hxy e => hxy (Fin.ext e)
  intro i j e
  fin_cases i <;> fin_cases j <;> simp at e ⊢ <;>
    first | exact absurd e (h hab) | exact absurd e (h hac) | exact absurd e (h hbc) |
      exact absurd e.symm (h hab) | exact absurd e.symm (h hac) | exact absurd e.symm (h hbc)

theorem cast_inj4 {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![(a : ℝ), (b : ℝ), (c : ℝ), (d : ℝ)]) := by
  have h : ∀ {x y : Fin n}, x ≠ y → (x : ℕ) ≠ (y : ℕ) := fun hxy e => hxy (Fin.ext e)
  intro i j e
  fin_cases i <;> fin_cases j <;> simp at e ⊢ <;>
    first | exact absurd e (h hab) | exact absurd e (h hac) | exact absurd e (h had) |
      exact absurd e (h hbc) | exact absurd e (h hbd) | exact absurd e (h hcd) |
      exact absurd e.symm (h hab) | exact absurd e.symm (h hac) | exact absurd e.symm (h had) |
      exact absurd e.symm (h hbc) | exact absurd e.symm (h hbd) | exact absurd e.symm (h hcd)

/-- The plane matrix of four planes: rows `(u_a, h_a)`. -/
def planeMat (u : Fin n → V) (h : Fin n → ℝ) (a b c d : Fin n) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![![u a 0, u a 1, u a 2, h a], ![u b 0, u b 1, u b 2, h b],
    ![u c 0, u c 1, u c 2, h c], ![u d 0, u d 1, u d 2, h d]]

/-- Four planes with a common point have a singular plane matrix. -/
theorem planeMat_det_eq_zero {u : Fin n → V} {h : Fin n → ℝ} {a b c d : Fin n} {p : V}
    (ha : u a ⬝ᵥ p = h a) (hb : u b ⬝ᵥ p = h b) (hc : u c ⬝ᵥ p = h c) (hd : u d ⬝ᵥ p = h d) :
    (planeMat u h a b c d).det = 0 := by
  rw [← exists_mulVec_eq_zero_iff]
  refine ⟨![p 0, p 1, p 2, -1], fun e => by
    have := congrFun e 3; simp at this, ?_⟩
  rw [dot_eq] at ha hb hc hd
  ext r
  fin_cases r <;> simp [planeMat, mulVec, dotProduct, Fin.sum_univ_four] <;> linarith

namespace CircleRep

/-- **Generic representations** (C-D4). -/
theorem exists_generic (R : CircleRep A) :
    ∃ R' : CircleRep A, (∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c →
      det3 (R'.u a) (R'.u b) (R'.u c) ≠ 0) ∧
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → ∀ p : V,
        R'.u a ⬝ᵥ p = R'.h a → R'.u b ⬝ᵥ p = R'.h b → R'.u c ⬝ᵥ p = R'.h c →
        R'.u d ⬝ᵥ p = R'.h d → False) := by
  set U : ℝ → Fin n → V := fun τ i => R.u i + τ • mom i
  set H : ℝ → Fin n → ℝ := fun τ i => R.h i + τ * (i : ℝ) ^ 3
  have hU : ∀ i, Continuous (fun τ => U τ i) := fun i => by
    simp only [U]; fun_prop
  have hH : ∀ i, Continuous (fun τ => H τ i) := fun i => by
    simp only [H]; fun_prop
  obtain ⟨δ, hδ, hrep⟩ := R.isRep.perturb hU hH (by funext i; simp [U]) (by funext i; simp [H])
  -- the bad parameters
  set B3 : Set ℝ := ⋃ t ∈ (univ.filter (fun t : Fin n × Fin n × Fin n =>
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) : Set (Fin n × Fin n × Fin n)),
    {τ | det3 (U τ t.1) (U τ t.2.1) (U τ t.2.2) = 0}
  set B4 : Set ℝ := ⋃ t ∈ (univ.filter (fun t : Fin n × Fin n × Fin n × Fin n =>
      t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧ t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧
        t.2.2.1 ≠ t.2.2.2) : Set (Fin n × Fin n × Fin n × Fin n)),
    {τ | (planeMat (U τ) (H τ) t.1 t.2.1 t.2.2.1 t.2.2.2).det = 0}
  have hB3 : B3.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun t ht => ?_
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
    obtain ⟨a, b, c⟩ := t
    obtain ⟨hab, hac, hbc⟩ := ht
    have e : ∀ τ, det3 (U τ a) (U τ b) (U τ c) =
        (Matrix.of ![R.u a, R.u b, R.u c] + τ • vandermonde ![(a : ℝ), b, c]).det := by
      intro τ
      rw [det3, triple_product_eq_det]
      congr 1
      ext r k; fin_cases r <;> fin_cases k <;> simp [U, mom, vandermonde_apply, Matrix.vecHead, Matrix.vecTail]
    simp only [e]
    exact finite_det_eq_zero _ _ (det_vandermonde_ne_zero (cast_inj3 hab hac hbc))
  have hB4 : B4.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun t ht => ?_
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
    obtain ⟨a, b, c, d⟩ := t
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := ht
    have e : ∀ τ, (planeMat (U τ) (H τ) a b c d).det =
        (planeMat R.u R.h a b c d + τ • vandermonde ![(a : ℝ), b, c, d]).det := by
      intro τ
      congr 1
      ext r k; fin_cases r <;> fin_cases k <;> simp [planeMat, U, H, mom, vandermonde_apply, Matrix.vecHead, Matrix.vecTail] <;>
        try ring
    simp only [e]
    exact finite_det_eq_zero _ _ (det_vandermonde_ne_zero (cast_inj4 hab hac had hbc hbd hcd))
  obtain ⟨τ, ⟨hτ0, hτδ⟩, hτbad⟩ := ((Set.Ioo_infinite hδ).sdiff (hB3.union hB4)).nonempty
  obtain ⟨pt', hR'⟩ := hrep τ hτ0.le hτδ
  refine ⟨⟨U τ, H τ, pt', R.sgn, hR'⟩, ?_, ?_⟩
  · intro a b c hab hac hbc h0
    apply hτbad
    left
    simp only [B3, Set.mem_iUnion]
    exact ⟨(a, b, c), by simp [hab, hac, hbc], h0⟩
  · intro a b c d hab hac had hbc hbd hcd p ha hb hc hd
    apply hτbad
    right
    simp only [B4, Set.mem_iUnion]
    exact ⟨(a, b, c, d), by simp [hab, hac, had, hbc, hbd, hcd],
      planeMat_det_eq_zero ha hb hc hd⟩

end CircleRep

end Pca.Circ
