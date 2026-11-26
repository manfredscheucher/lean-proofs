/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: more genericity (`doc/pca/circ.md`, decision C-D4)

For the outward sweep (Theorem 16) two more degeneracies are excluded
(`CircleRep.exists_generic2`): no plane `E_b` passes through the center `c_a` of another circle
(`h_b ⟨u_a, u_a⟩ ≠ h_a ⟨u_a, u_b⟩`), and no plane `E_l` passes through the foot point of the line
`E_a ∩ E_b` (`⟨u_l, foot⟩ ≠ h_l`). Proof: perturb only the offsets, `h + τ g` with
`g_a = L^a` for a suitable natural number `L`; every condition is affine in `τ` with a slope that
is a nonzero polynomial in `L`.
-/
import Pca.Circ.Generic
import Mathlib.Topology.Instances.Matrix

open Equiv Finset Matrix Set Polynomial Filter Topology

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

theorem foot_add (ui uj : V) (a b c d : ℝ) :
    foot ui uj (a + c) (b + d) = foot ui uj a b + foot ui uj c d := by
  unfold foot; ext k; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring

/-- Polynomials with a nonzero coefficient have finitely many roots. -/
theorem finite_roots_of_coeff {p : ℝ[X]} {k : ℕ} (hk : p.coeff k ≠ 0) :
    {x : ℝ | p.eval x = 0}.Finite :=
  finite_setOfPred_isRoot (fun h0 => hk (by rw [h0, coeff_zero]))

/-- Planes in general position (independent normals) without a common point have a
nonsingular plane matrix. -/
theorem planeMat_det_ne_zero {u : Fin n → V} {h : Fin n → ℝ} {a b c d : Fin n}
    (hd : det3 (u a) (u b) (u c) ≠ 0)
    (hno : ∀ p : V, u a ⬝ᵥ p = h a → u b ⬝ᵥ p = h b → u c ⬝ᵥ p = h c → u d ⬝ᵥ p = h d → False) :
    (planeMat u h a b c d).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := exists_mulVec_eq_zero_iff.2 h0
  have row : ∀ r : Fin 4, (planeMat u h a b c d *ᵥ v) r = 0 := fun r => by rw [hMv]; rfl
  have r0 := row 0; have r1 := row 1; have r2 := row 2; have r3 := row 3
  simp [planeMat, mulVec, dotProduct, Fin.sum_univ_four] at r0 r1 r2 r3
  set x : V := ![v 0, v 1, v 2]
  by_cases ht : v 3 = 0
  · apply hv
    have hx : x = 0 := by
      have e1 : u a ⬝ᵥ x = u a ⬝ᵥ 0 := by
        rw [dotProduct_zero, dot_eq]; simp [x]; rw [ht] at r0; linarith
      have e2 : u b ⬝ᵥ x = u b ⬝ᵥ 0 := by
        rw [dotProduct_zero, dot_eq]; simp [x]; rw [ht] at r1; linarith
      have e3 : u c ⬝ᵥ x = u c ⬝ᵥ 0 := by
        rw [dotProduct_zero, dot_eq]; simp [x]; rw [ht] at r2; linarith
      exact eq_of_three_planes hd e1 e2 e3
    ext r; fin_cases r
    · exact congrFun hx 0
    · exact congrFun hx 1
    · exact congrFun hx 2
    · exact ht
  · apply hno ((-1 / v 3) • x) <;>
      · rw [dotProduct_smul, smul_eq_mul, dot_eq]; simp [x]; field_simp; linarith

namespace CircleRep

/-- **Generic representations for the outward sweep** (C-D4). -/
theorem exists_generic2 (R : CircleRep A) :
    ∃ R' : CircleRep A, (∀ a b c : Fin n, a ≠ b → a ≠ c → b ≠ c →
      det3 (R'.u a) (R'.u b) (R'.u c) ≠ 0) ∧
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → ∀ p : V,
        R'.u a ⬝ᵥ p = R'.h a → R'.u b ⬝ᵥ p = R'.h b → R'.u c ⬝ᵥ p = R'.h c →
        R'.u d ⬝ᵥ p = R'.h d → False) ∧
      (∀ a b : Fin n, a ≠ b → R'.h b * (R'.u a ⬝ᵥ R'.u a) ≠ R'.h a * (R'.u a ⬝ᵥ R'.u b)) ∧
      (∀ a b l : Fin n, a ≠ b → a ≠ l → b ≠ l →
        R'.u l ⬝ᵥ foot (R'.u a) (R'.u b) (R'.h a) (R'.h b) ≠ R'.h l) := by
  obtain ⟨R1, hG1, hG2⟩ := R.exists_generic
  set u := R1.u
  set h := R1.h
  -- choose the direction `g a = L ^ a`
  let pD : Fin n × Fin n → ℝ[X] := fun t =>
    C (u t.1 ⬝ᵥ u t.1) * X ^ (t.2 : ℕ) - C (u t.1 ⬝ᵥ u t.2) * X ^ (t.1 : ℕ)
  let α : Fin n × Fin n × Fin n → ℝ := fun t =>
    (1 / ((u t.1 ⨯₃ u t.2.1) ⬝ᵥ (u t.1 ⨯₃ u t.2.1))) * (u t.2.2 ⬝ᵥ (u t.2.1 ⨯₃ (u t.1 ⨯₃ u t.2.1)))
  let β : Fin n × Fin n × Fin n → ℝ := fun t =>
    (1 / ((u t.1 ⨯₃ u t.2.1) ⬝ᵥ (u t.1 ⨯₃ u t.2.1))) * (u t.2.2 ⬝ᵥ ((u t.1 ⨯₃ u t.2.1) ⨯₃ u t.1))
  let pF : Fin n × Fin n × Fin n → ℝ[X] := fun t =>
    C (α t) * X ^ (t.1 : ℕ) + C (β t) * X ^ (t.2.1 : ℕ) - X ^ (t.2.2 : ℕ)
  have hfootL : ∀ (t : Fin n × Fin n × Fin n) (x : ℝ), u t.2.2 ⬝ᵥ foot (u t.1) (u t.2.1)
      (x ^ (t.1 : ℕ)) (x ^ (t.2.1 : ℕ)) - x ^ (t.2.2 : ℕ) = (pF t).eval x := by
    intro t x
    simp only [pF, α, β, foot, eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X,
      dotProduct_smul, dotProduct_add, smul_eq_mul]
    ring
  set BL : Set ℝ := (⋃ t ∈ (univ.filter (fun t : Fin n × Fin n => t.1 ≠ t.2) :
      Set (Fin n × Fin n)), {x | (pD t).eval x = 0}) ∪
    ⋃ t ∈ (univ.filter (fun t : Fin n × Fin n × Fin n => t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧
      t.2.1 ≠ t.2.2) : Set (Fin n × Fin n × Fin n)), {x | (pF t).eval x = 0}
  have hBL : BL.Finite := by
    refine Set.Finite.union (Set.Finite.biUnion (Finset.finite_toSet _) fun t ht => ?_)
      (Set.Finite.biUnion (Finset.finite_toSet _) fun t ht => ?_)
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
      refine finite_roots_of_coeff (k := (t.2 : ℕ)) ?_
      have hne : (t.2 : ℕ) ≠ (t.1 : ℕ) := fun e => ht (Fin.ext e).symm
      simp only [pD, coeff_sub, coeff_C_mul, coeff_X_pow, if_neg hne, if_true, mul_one,
        mul_zero, sub_zero]
      exact (dot_self_pos (R1.isRep.u_ne_zero t.1)).ne'
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
      obtain ⟨h1, h2, h3⟩ := ht
      refine finite_roots_of_coeff (k := (t.2.2 : ℕ)) ?_
      have e1 : (t.2.2 : ℕ) ≠ (t.1 : ℕ) := fun e => h2 (Fin.ext e).symm
      have e2 : (t.2.2 : ℕ) ≠ (t.2.1 : ℕ) := fun e => h3 (Fin.ext e).symm
      simp only [pF, coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, if_neg e1, if_neg e2,
        if_true, mul_zero, zero_add]
      norm_num
  obtain ⟨L, hL⟩ : ∃ L : ℕ, (L : ℝ) ∉ BL := by
    by_contra hc
    push_neg at hc
    exact Set.infinite_range_of_injective Nat.cast_injective
      (hBL.subset (by rintro _ ⟨m, rfl⟩; exact hc m))
  set g : Fin n → ℝ := fun a => (L : ℝ) ^ (a : ℕ)
  have hgD : ∀ a b : Fin n, a ≠ b → g b * (u a ⬝ᵥ u a) - g a * (u a ⬝ᵥ u b) ≠ 0 := by
    intro a b hab e
    apply hL; left
    simp only [Set.mem_iUnion]
    refine ⟨(a, b), by simp [hab], ?_⟩
    simp only [Set.mem_ofPred_eq, pD, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    simp only [g] at e; linarith
  have hgF : ∀ a b l : Fin n, a ≠ b → a ≠ l → b ≠ l →
      u l ⬝ᵥ foot (u a) (u b) (g a) (g b) - g l ≠ 0 := by
    intro a b l hab hal hbl e
    apply hL; right
    simp only [Set.mem_iUnion]
    refine ⟨(a, b, l), by simp [hab, hal, hbl], ?_⟩
    simp only [Set.mem_ofPred_eq]
    rw [← hfootL (a, b, l) (L : ℝ)]; exact e
  -- perturb the offsets
  set H : ℝ → Fin n → ℝ := fun τ i => h i + τ * g i
  obtain ⟨δ, hδ, hrep⟩ := R1.isRep.perturb (U := fun _ => u) (H := H)
    (fun i => continuous_const) (fun i => by simp only [H]; fun_prop) rfl
    (by funext i; simp [H, h])
  -- `G2` persists near `0` (nonsingular plane matrices)
  have hdet : ∀ t : Fin n × Fin n × Fin n × Fin n, ∀ᶠ τ in 𝓝 (0 : ℝ),
      (t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧ t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧
        t.2.2.1 ≠ t.2.2.2) → (planeMat u (H τ) t.1 t.2.1 t.2.2.1 t.2.2.2).det ≠ 0 := by
    intro t
    by_cases ht : t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧ t.2.1 ≠ t.2.2.1 ∧
        t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
      have hc : Continuous (fun τ => (planeMat u (H τ) t.1 t.2.1 t.2.2.1 t.2.2.2).det) := by
        refine Continuous.matrix_det ?_
        refine continuous_pi fun r => continuous_pi fun k => ?_
        fin_cases r <;> fin_cases k <;> simp only [planeMat, H, of_apply] <;> simp <;>
          fun_prop
      have h0 : (planeMat u (H 0) t.1 t.2.1 t.2.2.1 t.2.2.2).det ≠ 0 := by
        have e : H 0 = h := by funext i; simp [H]
        rw [e]
        exact planeMat_det_ne_zero (hG1 _ _ _ h1 h2 h4)
          (fun p ha hb hc hd => hG2 _ _ _ _ h1 h2 h3 h4 h5 h6 p ha hb hc hd)
      exact (hc.continuousAt.eventually_ne h0).mono fun τ hτ _ => hτ
    · exact Eventually.of_forall fun _ h' => absurd h' ht
  obtain ⟨δ', hδ', hδ'all⟩ := Metric.eventually_nhds_iff.1 (eventually_all.2 hdet)
  -- the bad parameters of `G3`, `G4`: one root each
  set B3 : Set ℝ := ⋃ t ∈ (univ.filter (fun t : Fin n × Fin n => t.1 ≠ t.2) :
      Set (Fin n × Fin n)),
    {τ | H τ t.2 * (u t.1 ⬝ᵥ u t.1) = H τ t.1 * (u t.1 ⬝ᵥ u t.2)}
  set B4 : Set ℝ := ⋃ t ∈ (univ.filter (fun t : Fin n × Fin n × Fin n => t.1 ≠ t.2.1 ∧
      t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2) : Set (Fin n × Fin n × Fin n)),
    {τ | u t.2.2 ⬝ᵥ foot (u t.1) (u t.2.1) (H τ t.1) (H τ t.2.1) = H τ t.2.2}
  have aff : ∀ c₀ c₁ : ℝ, c₁ ≠ 0 → {τ : ℝ | c₀ + τ * c₁ = 0}.Finite := by
    intro c₀ c₁ hc
    refine (Set.finite_singleton (-c₀ / c₁)).subset fun τ hτ => ?_
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff] at hτ ⊢
    field_simp; linarith
  have hB3 : B3.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun t ht => ?_
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
    refine (aff (h t.2 * (u t.1 ⬝ᵥ u t.1) - h t.1 * (u t.1 ⬝ᵥ u t.2))
      (g t.2 * (u t.1 ⬝ᵥ u t.1) - g t.1 * (u t.1 ⬝ᵥ u t.2)) (hgD _ _ ht)).subset fun τ hτ => ?_
    simp only [Set.mem_ofPred_eq, H] at hτ ⊢; linarith
  have hB4 : B4.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun t ht => ?_
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht
    obtain ⟨h1, h2, h3⟩ := ht
    refine (aff (u t.2.2 ⬝ᵥ foot (u t.1) (u t.2.1) (h t.1) (h t.2.1) - h t.2.2)
      (u t.2.2 ⬝ᵥ foot (u t.1) (u t.2.1) (g t.1) (g t.2.1) - g t.2.2)
      (hgF _ _ _ h1 h2 h3)).subset fun τ hτ => ?_
    simp only [Set.mem_ofPred_eq, H] at hτ ⊢
    rw [foot_add, foot_smul, dotProduct_add, dotProduct_smul, smul_eq_mul] at hτ
    linarith
  obtain ⟨τ, ⟨hτ0, hτδ⟩, hτbad⟩ :=
    ((Set.Ioo_infinite (lt_min hδ hδ')).sdiff (hB3.union hB4)).nonempty
  obtain ⟨pt', hR'⟩ := hrep τ hτ0.le (lt_of_lt_of_le hτδ (min_le_left _ _))
  have hτ' : dist τ 0 < δ' := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hτ0]; exact lt_of_lt_of_le hτδ (min_le_right _ _)
  refine ⟨⟨u, H τ, pt', R1.sgn, hR'⟩, hG1, ?_, ?_, ?_⟩
  · intro a b c d hab hac had hbc hbd hcd p ha hb hc hd
    exact hδ'all hτ' (a, b, c, d) ⟨hab, hac, had, hbc, hbd, hcd⟩
      (planeMat_det_eq_zero ha hb hc hd)
  · intro a b hab e
    apply hτbad; left
    simp only [B3, Set.mem_iUnion]
    exact ⟨(a, b), by simp [hab], e⟩
  · intro a b l hab hal hbl e
    apply hτbad; right
    simp only [B4, Set.mem_iUnion]
    exact ⟨(a, b, l), by simp [hab, hal, hbl], e⟩

end CircleRep

end Pca.Circ
