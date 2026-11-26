/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Coordinates of darts and an isomorphism criterion (package C, `doc/pca/great.md` section 3.4)

Fix a base dart `β c` on every curve `c`. Every dart is `code c k b`: the dart `straight^k (β c)`
(`b = false`) or its reverse at the same crossing `σ² (straight^k (β c))` (`b = true`), with
`k < 2 (n - 1)`, in a unique way. In these coordinates `α` is the same map for every arrangement
(`α (straight^k β) = σ² (straight^(k+1) β)`), so an arrangement is determined by its **rotation
table**: the coordinates of `σ (code c k false)`. Two arrangements with the same table are
isomorphic (`iso_of_table`).
-/
import Pca.Great.Basic

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

/-- The dart with coordinates `(c, k, b)`. -/
def code (A : Arrangement n D) (β : Fin n → D) (c : Fin n) (k : ℕ) (b : Bool) : D :=
  if b then A.σ (A.σ ((A.straight ^ k) (β c))) else (A.straight ^ k) (β c)

theorem code_σσ (A : Arrangement n D) (β : Fin n → D) (c : Fin n) (k : ℕ) (b : Bool) :
    A.σ (A.σ (code A β c k b)) = code A β c k (!b) := by
  cases b <;> simp [code, A.σ_σ_σ_σ]

theorem code_add_period (A : Arrangement n D) (β : Fin n → D) (c : Fin n) (k : ℕ) (b : Bool) :
    code A β c (k + 2 * (n - 1)) b = code A β c k b := by
  simp only [code, pow_add, Perm.mul_apply, straight_pow_period]

theorem code_mod (A : Arrangement n D) (β : Fin n → D) (c : Fin n) (k : ℕ) (b : Bool) :
    code A β c (k % (2 * (n - 1))) b = code A β c k b := by
  conv_rhs => rw [← Nat.mod_add_div k (2 * (n - 1))]
  generalize k % (2 * (n - 1)) = r
  induction k / (2 * (n - 1)) with
  | zero => rfl
  | succ q ih => rw [Nat.mul_succ, ← add_assoc, code_add_period, ih]

theorem curve_code (A : Arrangement n D) (β : Fin n → D) (c : Fin n) (k : ℕ) (b : Bool) :
    A.curve (code A β c k b) = A.curve (β c) := by
  cases b <;> simp [code, A.isArrangement.curve_σσ, curve_straight_pow]

theorem α_code_false (A : Arrangement n D) (β : Fin n → D) (c : Fin n) (k : ℕ) :
    A.α (code A β c k false) = code A β c (k + 1) true := by
  simp only [code, pow_succ', Perm.mul_apply, Arrangement.straight_apply, A.σ_σ_σ_σ,
    Bool.false_eq_true, if_false, if_true]

theorem α_code_true (A : Arrangement n D) (β : Fin n → D) (c : Fin n) (k : ℕ) :
    A.α (code A β c (k + 1) true) = code A β c k false := by
  simp only [code, pow_succ', Perm.mul_apply, Arrangement.straight_apply, A.σ_σ_σ_σ,
    Bool.false_eq_true, if_false, if_true, A.isArrangement.α_α]

/-- Every dart has coordinates. -/
theorem exists_code (A : Arrangement n D) (β : Fin n → D) (hβ : ∀ c, A.curve (β c) = c) (d : D) :
    ∃ c k b, k < 2 * (n - 1) ∧ code A β c k b = d := by
  have hn := A.two_le_n
  have hc : A.curve (β (A.curve d)) = A.curve d := hβ _
  rcases A.isArrangement.straight _ _ hc with h | h
  · obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨A.curve d, k % (2 * (n - 1)), false, Nat.mod_lt _ (by omega), ?_⟩
    rw [code_mod]; exact hk
  · obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨A.curve d, k % (2 * (n - 1)), true, Nat.mod_lt _ (by omega), ?_⟩
    rw [code_mod]
    simp only [code, if_true]
    have hk' : (A.straight ^ k) (β (A.curve d)) = A.σ (A.σ d) := hk
    rw [hk', A.σ_σ_σ_σ]

/-- Coordinates are unique. -/
theorem code_inj (A : Arrangement n D) (β : Fin n → D) (hβ : ∀ c, A.curve (β c) = c)
    {c c' : Fin n} {k k' : ℕ} {b b' : Bool} (hk : k < 2 * (n - 1)) (hk' : k' < 2 * (n - 1))
    (h : code A β c k b = code A β c' k' b') : c = c' ∧ k = k' ∧ b = b' := by
  have hcc : c = c' := by
    have := congrArg A.curve h
    rwa [curve_code, curve_code, hβ, hβ] at this
  subst hcc
  have hfalse : ∀ {i j : ℕ}, i < 2 * (n - 1) → j < 2 * (n - 1) →
      code A β c i false = code A β c j false → i = j := fun hi hj h => by
    apply straight_pow_inj (A := A) (d := β c) hi hj
    simp only [code, Bool.false_eq_true, if_false] at h
    rw [h]
  have hmix : ∀ i j : ℕ, code A β c i false ≠ code A β c j true := fun i j h => by
    simp only [code, Bool.false_eq_true, if_false, if_true] at h
    apply A.not_sameCycle_straight_σσ ((A.straight ^ j) (β c))
    rw [← h]
    exact Perm.sameCycle_pow_left.2 (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ _))
  refine ⟨rfl, ?_⟩
  cases b <;> cases b'
  · exact ⟨hfalse hk hk' h, rfl⟩
  · exact absurd h (hmix _ _)
  · exact absurd h.symm (hmix _ _)
  · refine ⟨hfalse hk hk' ?_, rfl⟩
    have := congrArg (fun z => A.σ (A.σ z)) h
    simpa [code_σσ] using this

/-- **Isomorphism criterion.** If `A` and `B` (with base darts `βA c`, `βB c` on the curves `c`
and `π c`) have the same rotation table `T`, they are isomorphic. -/
theorem iso_of_table {D' : Type*} [Fintype D'] [DecidableEq D'] (A : Arrangement n D)
    (B : Arrangement n D') (π : Perm (Fin n)) (βA : Fin n → D) (βB : Fin n → D')
    (hβA : ∀ c, A.curve (βA c) = c) (hβB : ∀ c, B.curve (βB c) = π c)
    (T : Fin n → ℕ → Fin n × ℕ × Bool)
    (hA : ∀ c k, k < 2 * (n - 1) →
      A.σ (code A βA c k false) = code A βA (T c k).1 (T c k).2.1 (T c k).2.2)
    (hB : ∀ c k, k < 2 * (n - 1) →
      B.σ (code B βB c k false) = code B βB (T c k).1 (T c k).2.1 (T c k).2.2) :
    Nonempty (Iso A B) := by
  classical
  have hn := A.two_le_n
  -- the base darts of `B` indexed by the curves of `B`
  set βB' : Fin n → D' := fun c => βB (π.symm c) with hβB'def
  have hβB' : ∀ c, B.curve (βB' c) = c := fun c => by
    simp only [hβB'def, hβB, Equiv.apply_symm_apply]
  have hcodeB : ∀ c k b, code B βB c k b = code B βB' (π c) k b := fun c k b => by
    simp [code, hβB'def]
  choose cA kA bA hkA hA' using exists_code A βA hβA
  have exB : ∀ d', ∃ c k b, k < 2 * (n - 1) ∧ code B βB c k b = d' := by
    intro d'
    obtain ⟨c, k, b, hk, h⟩ := exists_code B βB' hβB' d'
    exact ⟨π.symm c, k, b, hk, by rw [hcodeB, Equiv.apply_symm_apply]; exact h⟩
  choose cB kB bB hkB hB' using exB
  have injB : ∀ {c c' k k' b b'}, k < 2 * (n - 1) → k' < 2 * (n - 1) →
      code B βB c k b = code B βB c' k' b' → c = c' ∧ k = k' ∧ b = b' := by
    intro c c' k k' b b' hk hk' h
    rw [hcodeB, hcodeB] at h
    obtain ⟨h1, h2, h3⟩ := code_inj B βB' hβB' hk hk' h
    exact ⟨π.injective h1, h2, h3⟩
  let F : D → D' := fun d => code B βB (cA d) (kA d) (bA d)
  let G : D' → D := fun d' => code A βA (cB d') (kB d') (bB d')
  -- `F` on all coordinates
  have hF : ∀ c k b, F (code A βA c k b) = code B βB c k b := by
    intro c k b
    have h1 := (hA' (code A βA c k b)).trans (code_mod A βA c k b).symm
    obtain ⟨h1c, h2, h3⟩ := code_inj A βA hβA (hkA _) (Nat.mod_lt _ (by omega)) h1
    show code B βB (cA _) (kA _) (bA _) = _
    rw [h1c, h2, h3, code_mod]
  have hG : ∀ c k b, G (code B βB c k b) = code A βA c k b := by
    intro c k b
    have h1 := (hB' (code B βB c k b)).trans (code_mod B βB c k b).symm
    obtain ⟨h1c, h2, h3⟩ := injB (hkB _) (Nat.mod_lt _ (by omega)) h1
    show code A βA (cB _) (kB _) (bB _) = _
    rw [h1c, h2, h3, code_mod]
  have hGF : ∀ d, G (F d) = d := fun d => by
    show G (code B βB _ _ _) = d
    rw [hG]; exact hA' d
  have hFG : ∀ d', F (G d') = d' := fun d' => by
    show F (code A βA _ _ _) = d'
    rw [hF]; exact hB' d'
  -- `σ` and `α` in coordinates
  have hσ : ∀ c k b, F (A.σ (code A βA c k b)) = B.σ (code B βB c k b) := by
    intro c k b
    rw [← code_mod A βA c k b, ← code_mod B βB c k b]
    have hk := Nat.mod_lt k (show 0 < 2 * (n - 1) by omega)
    cases b
    · rw [hA c _ hk, hF, hB c _ hk]
    · have e1 : code A βA c (k % (2 * (n - 1))) true =
          A.σ (A.σ (code A βA c (k % (2 * (n - 1))) false)) := by rw [code_σσ]; rfl
      have e2 : code B βB c (k % (2 * (n - 1))) true =
          B.σ (B.σ (code B βB c (k % (2 * (n - 1))) false)) := by rw [code_σσ]; rfl
      rw [e1, e2]
      change F (A.σ (A.σ (A.σ (code A βA c _ false)))) = B.σ (B.σ (B.σ (code B βB c _ false)))
      rw [hA c _ hk, hB c _ hk, code_σσ, code_σσ, hF]
  have hα : ∀ c k b, F (A.α (code A βA c k b)) = B.α (code B βB c k b) := by
    intro c k b
    cases b
    · rw [α_code_false, α_code_false, hF]
    · rcases k with _ | k
      · rw [← code_add_period A βA c 0 true, ← code_add_period B βB c 0 true, zero_add]
        obtain ⟨m, hm⟩ : ∃ m, 2 * (n - 1) = m + 1 := ⟨2 * (n - 1) - 1, by omega⟩
        rw [hm, α_code_true, α_code_true, hF]
      · rw [α_code_true, α_code_true, hF]
  refine ⟨Iso.mk ⟨F, G, hGF, hFG⟩ π ?_ ?_ ?_⟩
  · intro d
    change F (A.σ d) = B.σ (F d)
    conv_lhs => rw [← hA' d]
    rw [hσ]
  · intro d
    change F (A.α d) = B.α (F d)
    conv_lhs => rw [← hA' d]
    rw [hα]
  · intro d
    change B.curve (code B βB _ _ _) = π (A.curve d)
    rw [curve_code, hβB]
    conv_rhs => rw [← hA' d]
    rw [curve_code, hβA]

end Pca.Great
