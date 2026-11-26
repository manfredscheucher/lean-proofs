/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# The relation on 2-subsets of a 3-signotope and its behaviour under rotation

BFS = Bergold, Felsner, Scheucher, *An extension theorem for signotopes*,
https://arxiv.org/abs/2303.04079, sections 2, 3 and Appendix B, specialized to rank `r = 3`.

All statements here are about a ground type `α` that is linearly ordered by an injective **key**
`p : α → ℕ` (instead of the order of `Fin n`). This is how rotations are formalized without
relabeling: the clockwise rotation of BFS section 2 moves the first element to the end and changes
the sign of every 3-subset containing it (`IsRot`), the sets themselves stay where they are. For the
key `Fin.val` this is BFS's setting (`Pca/Great/Sig_Twist.lean`).

* `IsSigOrd p τ`: the signotope axiom (BFS 1.1) for the order given by `p`.
* `Step p τ P Q`: the generating relation of BFS section 2 for `r = 3`: for `a < b < c` with
  `τ(a,b,c) = +` the steps `ab ≺ ac ≺ bc` (and `ab ≺ bc`), with `-` the reversed ones. `Prec` is its
  transitive closure.
* BFS Lemma B.2 (`U₁, Uₙ` up-sets, `D₁, Dₙ` down-sets): `step_uFirst`, `step_dFirst`,
  `step_uLast`, `step_dLast` and the `prec_*` versions.
* BFS Lemma 2.1 (rotation gives a signotope): `isSigOrd_rot`.
* BFS Lemma B.1 (rotation keeps a step unless both sets contain the rotated element): `step_rot`,
  and for chains in `U₁` resp. `D₁`: `prec_rot_of_uFirst`, `prec_rot_of_dFirst`.
* Acyclicity on `H₁` (sets containing the first element): `not_prec_self_of_first_mem`. The
  relation restricted to `H₁` is the order of the crossings along the first line, transitive by the
  4-packet condition (`lineRel_trans`). Not in BFS (they cite Felsner-Weil [9, Lemma 10] for the
  partial order), see `doc/pca/great.md` section 5.
* BFS Proposition 3.3: `prop33`.
* BFS Proposition 3.1 (extension by a last element for a down-set), the sign part:
  `validExt_downSet`, `validExt_toggle`.
-/
import Pca.Great.SigDefs
import Mathlib.Logic.Relation

open Finset Relation Function

namespace Pca.Great.Sig

/-- Close a goal about finitely many signs: case split on the listed Bool terms and decide. -/
syntax "bool_cases " "[" term,* "]" : tactic
macro_rules
  | `(tactic| bool_cases [$ts,*]) => do
    let mut tac ← `(tactic| decide)
    for t in ts.getElems.reverse do
      tac ← `(tactic| (cases $t:term <;> $tac))
    return tac

variable {α : Type*} [DecidableEq α]

/-- The signotope axiom (BFS 1.1, rank 3) for the linear order on `α` given by the key `p`:
for `x₁ < x₂ < x₃ < x₄` the signs of `X \ x₁, …, X \ x₄` have at most one sign change. -/
def IsSigOrd (p : α → ℕ) (τ : Finset α → Bool) : Prop :=
  ∀ x₁ x₂ x₃ x₄ : α, p x₁ < p x₂ → p x₂ < p x₃ → p x₃ < p x₄ →
    AtMostOneChange [τ {x₂, x₃, x₄}, τ {x₁, x₃, x₄}, τ {x₁, x₂, x₄}, τ {x₁, x₂, x₃}]

/-- The relations of a triple `a < b < c` with sign `+` (BFS section 2): `ab ≺ ac`, `ac ≺ bc`,
`ab ≺ bc`. -/
def PlusSteps (a b c : α) (P Q : Finset α) : Prop :=
  (P = {a, b} ∧ Q = {a, c}) ∨ (P = {a, c} ∧ Q = {b, c}) ∨ (P = {a, b} ∧ Q = {b, c})

/-- The generating relation on 2-subsets (BFS section 2, `r = 3`): `P ≺ Q` is given by a triple
`a < b < c`, with `ab ≺ ac ≺ bc` if `τ(a,b,c) = +` and `bc ≺ ac ≺ ab` if `τ(a,b,c) = -`. -/
def Step (p : α → ℕ) (τ : Finset α → Bool) (P Q : Finset α) : Prop :=
  ∃ a b c : α, p a < p b ∧ p b < p c ∧
    ((τ {a, b, c} = true ∧ PlusSteps a b c P Q) ∨ (τ {a, b, c} = false ∧ PlusSteps a b c Q P))

/-- The relation `≺` of BFS section 2: the transitive closure of `Step`. -/
abbrev Prec (p : α → ℕ) (τ : Finset α → Bool) : Finset α → Finset α → Prop :=
  TransGen (Step p τ)

/-- `f` is the first element for the key `p`. -/
def IsFirst (p : α → ℕ) (f : α) : Prop := ∀ x, x ≠ f → p f < p x

/-- `g` is the last element for the key `p`. -/
def IsLast (p : α → ℕ) (g : α) : Prop := ∀ x, x ≠ g → p x < p g

/-- `𝒰₁` of BFS Appendix B (for the first element `f`): `f ∉ P` and `τ(P ∪ f) = +`. -/
def UFirst (τ : Finset α → Bool) (f : α) (P : Finset α) : Prop := f ∉ P ∧ τ (insert f P) = true

/-- `𝒟₁` of BFS Appendix B (for the first element `f`): `f ∉ P` and `τ(P ∪ f) = -`. -/
def DFirst (τ : Finset α → Bool) (f : α) (P : Finset α) : Prop := f ∉ P ∧ τ (insert f P) = false

/-- `𝒰ₙ` of BFS Appendix B (for the last element `g`): `g ∉ P` and `τ(P ∪ g) = -`. -/
def ULast (τ : Finset α → Bool) (g : α) (P : Finset α) : Prop := g ∉ P ∧ τ (insert g P) = false

/-- `𝒟ₙ` of BFS Appendix B (for the last element `g`): `g ∉ P` and `τ(P ∪ g) = +`. -/
def DLast (τ : Finset α → Bool) (g : α) (P : Finset α) : Prop := g ∉ P ∧ τ (insert g P) = true

/-- The clockwise rotation of BFS section 2 in key form: the first element `f` of `p` becomes the
last element of `p'`, the other keys are unchanged, and the sign of a set changes iff it
contains `f` (`σ_rot(X_rot) = -σ(X)` iff `1 ∈ X`). -/
structure IsRot (p : α → ℕ) (τ : Finset α → Bool) (p' : α → ℕ) (τ' : Finset α → Bool) (f : α) :
    Prop where
  first : IsFirst p f
  last : IsLast p' f
  key_eq : ∀ x, x ≠ f → p' x = p x
  sign_eq : ∀ T, τ' T = (τ T ^^ decide (f ∈ T))

variable {p p' : α → ℕ} {τ τ' : Finset α → Bool} {f : α} {P Q : Finset α}

section Basic

lemma ne_of_key_lt {a b : α} (h : p a < p b) : a ≠ b := by
  rintro rfl
  exact lt_irrefl _ h

/-- The first element lies in a triple `a < b < c` only as `a`. -/
lemma eq_of_isFirst_mem {a b c : α} (hf : IsFirst p f) (hab : p a < p b) (hbc : p b < p c)
    (h : f ∈ ({a, b, c} : Finset α)) : f = a := by
  simp only [mem_insert, mem_singleton] at h
  rcases h with rfl | rfl | rfl
  · rfl
  · exact absurd (hf a (ne_of_key_lt hab)) (by omega)
  · exact absurd (hf a (ne_of_key_lt (hab.trans hbc))) (by omega)

/-- The last element lies in a triple `a < b < c` only as `c`. -/
lemma eq_of_isLast_mem {a b c : α} (hg : IsLast p f) (hab : p a < p b) (hbc : p b < p c)
    (h : f ∈ ({a, b, c} : Finset α)) : f = c := by
  simp only [mem_insert, mem_singleton] at h
  rcases h with rfl | rfl | rfl
  · exact absurd (hg c (ne_of_key_lt (hab.trans hbc)).symm) (by omega)
  · exact absurd (hg c (ne_of_key_lt hbc).symm) (by omega)
  · rfl

lemma insert_pair_comm (x a b : α) : (insert x {a, b} : Finset α) = {a, b, x} := by
  ext y
  simp only [mem_insert, mem_singleton]
  tauto

lemma eq_of_pair_eq_pair {x y y' : α} (h : ({x, y} : Finset α) = {x, y'}) (hy : y ≠ x) :
    y = y' := by
  have : y ∈ ({x, y'} : Finset α) := h ▸ by simp
  simp only [mem_insert, mem_singleton] at this
  tauto

lemma step_nonempty (h : Step p τ P Q) : ∃ x, x ∈ P := by
  obtain ⟨a, b, c, -, -, hs⟩ := h
  rcases hs with ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ | ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ <;>
    exact ⟨_, mem_insert_self _ _⟩

/-- Reversing all signs (with the same order) reverses the relation. Used for the `n`-fold
rotation (BFS proof of Proposition 3.4). -/
theorem step_swap_of_neg (hp : ∀ x y, p x < p y → p' x < p' y)
    (hτ : ∀ a b c, p a < p b → p b < p c → τ' {a, b, c} = !τ {a, b, c}) (h : Step p τ P Q) :
    Step p' τ' Q P := by
  obtain ⟨a, b, c, hab, hbc, hs⟩ := h
  refine ⟨a, b, c, hp _ _ hab, hp _ _ hbc, ?_⟩
  rw [hτ a b c hab hbc]
  rcases hs with ⟨hs, h⟩ | ⟨hs, h⟩
  · exact Or.inr ⟨by simp [hs], h⟩
  · exact Or.inl ⟨by simp [hs], h⟩

end Basic

section LemmaB2

variable (hτ : IsSigOrd p τ)
include hτ

/-- BFS Lemma B.2, `𝒰₁` is an up-set (one generating step). -/
theorem step_uFirst (hf : IsFirst p f) (h : Step p τ P Q) (hP : UFirst τ f P) :
    UFirst τ f Q := by
  obtain ⟨a, b, c, hab, hbc, hs⟩ := h
  obtain ⟨hfP, hτP⟩ := hP
  by_cases hfT : f ∈ ({a, b, c} : Finset α)
  · obtain rfl := eq_of_isFirst_mem hf hab hbc hfT
    rcases hs with ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> simp_all
  · simp only [mem_insert, mem_singleton, not_or] at hfT
    obtain ⟨hfa, hfb, hfc⟩ := hfT
    have hX := hτ f a b c (hf a (Ne.symm hfa)) hab hbc
    rcases hs with ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      refine ⟨by simp [hfa, hfb, hfc], ?_⟩ <;> revert hX hs hτP <;>
      bool_cases [τ {a, b, c}, τ {f, b, c}, τ {f, a, c}, τ {f, a, b}]

/-- BFS Lemma B.2, `𝒟₁` is a down-set (one generating step). -/
theorem step_dFirst (hf : IsFirst p f) (h : Step p τ P Q) (hQ : DFirst τ f Q) :
    DFirst τ f P := by
  obtain ⟨a, b, c, hab, hbc, hs⟩ := h
  obtain ⟨hfQ, hτQ⟩ := hQ
  by_cases hfT : f ∈ ({a, b, c} : Finset α)
  · obtain rfl := eq_of_isFirst_mem hf hab hbc hfT
    rcases hs with ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> simp_all
  · simp only [mem_insert, mem_singleton, not_or] at hfT
    obtain ⟨hfa, hfb, hfc⟩ := hfT
    have hX := hτ f a b c (hf a (Ne.symm hfa)) hab hbc
    rcases hs with ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      refine ⟨by simp [hfa, hfb, hfc], ?_⟩ <;> revert hX hs hτQ <;>
      bool_cases [τ {a, b, c}, τ {f, b, c}, τ {f, a, c}, τ {f, a, b}]

/-- BFS Lemma B.2, `𝒰ₙ` is an up-set (one generating step). -/
theorem step_uLast (hg : IsLast p f) (h : Step p τ P Q) (hP : ULast τ f P) :
    ULast τ f Q := by
  obtain ⟨a, b, c, hab, hbc, hs⟩ := h
  obtain ⟨hfP, hτP⟩ := hP
  by_cases hfT : f ∈ ({a, b, c} : Finset α)
  · obtain rfl := eq_of_isLast_mem hg hab hbc hfT
    have e := insert_pair_comm f a b
    rcases hs with ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> simp_all
  · simp only [mem_insert, mem_singleton, not_or] at hfT
    obtain ⟨hfa, hfb, hfc⟩ := hfT
    have hX := hτ a b c f hab hbc (hg c (Ne.symm hfc))
    rcases hs with ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      refine ⟨by simp [hfa, hfb, hfc], ?_⟩ <;> rw [insert_pair_comm] at hτP ⊢ <;>
      revert hX hs hτP <;> bool_cases [τ {a, b, c}, τ {b, c, f}, τ {a, c, f}, τ {a, b, f}]

/-- BFS Lemma B.2, `𝒟ₙ` is a down-set (one generating step). -/
theorem step_dLast (hg : IsLast p f) (h : Step p τ P Q) (hQ : DLast τ f Q) :
    DLast τ f P := by
  obtain ⟨a, b, c, hab, hbc, hs⟩ := h
  obtain ⟨hfQ, hτQ⟩ := hQ
  by_cases hfT : f ∈ ({a, b, c} : Finset α)
  · obtain rfl := eq_of_isLast_mem hg hab hbc hfT
    have e := insert_pair_comm f a b
    rcases hs with ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> simp_all
  · simp only [mem_insert, mem_singleton, not_or] at hfT
    obtain ⟨hfa, hfb, hfc⟩ := hfT
    have hX := hτ a b c f hab hbc (hg c (Ne.symm hfc))
    rcases hs with ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;>
      refine ⟨by simp [hfa, hfb, hfc], ?_⟩ <;> rw [insert_pair_comm] at hτQ ⊢ <;>
      revert hX hs hτQ <;> bool_cases [τ {a, b, c}, τ {b, c, f}, τ {a, c, f}, τ {a, b, f}]

/-- BFS Lemma B.2 for `≺`: `𝒰₁` is an up-set. -/
theorem prec_uFirst (hf : IsFirst p f) (h : Prec p τ P Q) (hP : UFirst τ f P) : UFirst τ f Q := by
  induction h with
  | single h => exact step_uFirst hτ hf h hP
  | tail _ h ih => exact step_uFirst hτ hf h ih

/-- BFS Lemma B.2 for `≺`: `𝒟₁` is a down-set. -/
theorem prec_dFirst (hf : IsFirst p f) (h : Prec p τ P Q) (hQ : DFirst τ f Q) : DFirst τ f P := by
  induction h with
  | single h => exact step_dFirst hτ hf h hQ
  | tail _ h ih => exact ih (step_dFirst hτ hf h hQ)

/-- BFS Lemma B.2 for `≺`: `𝒰ₙ` is an up-set. -/
theorem prec_uLast (hg : IsLast p f) (h : Prec p τ P Q) (hP : ULast τ f P) : ULast τ f Q := by
  induction h with
  | single h => exact step_uLast hτ hg h hP
  | tail _ h ih => exact step_uLast hτ hg h ih

/-- BFS Lemma B.2 for `≺`: `𝒟ₙ` is a down-set. -/
theorem prec_dLast (hg : IsLast p f) (h : Prec p τ P Q) (hQ : DLast τ f Q) : DLast τ f P := by
  induction h with
  | single h => exact step_dLast hτ hg h hQ
  | tail _ h ih => exact ih (step_dLast hτ hg h hQ)

end LemmaB2

section Rotation

/-- BFS Lemma 2.1: the clockwise rotation of a signotope is a signotope. -/
theorem isSigOrd_rot (hτ : IsSigOrd p τ) (hr : IsRot p τ p' τ' f) : IsSigOrd p' τ' := by
  intro x₁ x₂ x₃ x₄ h12 h23 h34
  have nf : ∀ x, p' x < p' x₄ → x ≠ f := by
    rintro x hx rfl
    exact absurd (hr.last x₄ (ne_of_key_lt hx).symm) (by omega)
  have n1 := nf x₁ (by omega)
  have n2 := nf x₂ (by omega)
  have n3 := nf x₃ h34
  rw [hr.key_eq _ n1, hr.key_eq _ n2] at h12
  rw [hr.key_eq _ n2, hr.key_eq _ n3] at h23
  simp only [hr.sign_eq]
  by_cases h4 : x₄ = f
  · subst h4
    have e : ∀ a b : α, ({a, b, x₄} : Finset α) = {x₄, a, b} := fun a b => by
      ext; simp only [mem_insert, mem_singleton]; tauto
    have hX := hτ x₄ x₁ x₂ x₃ (hr.first x₁ n1) h12 h23
    simp only [e, mem_insert_self, decide_true, Bool.xor_true, mem_insert, mem_singleton,
      n1.symm, n2.symm, n3.symm, or_self, decide_false, Bool.xor_false]
    revert hX
    bool_cases [τ {x₁, x₂, x₃}, τ {x₄, x₂, x₃}, τ {x₄, x₁, x₃}, τ {x₄, x₁, x₂}]
  · rw [hr.key_eq _ n3, hr.key_eq _ h4] at h34
    have hX := hτ x₁ x₂ x₃ x₄ h12 h23 h34
    simpa [Ne.symm n1, Ne.symm n2, Ne.symm n3, Ne.symm h4] using hX

/-- BFS Lemma B.1 (for `r = 3`, one generating step): a clockwise rotation keeps the step
`P ≺ Q` unless both `P` and `Q` contain the rotated element. -/
theorem step_rot (hr : IsRot p τ p' τ' f) (h : Step p τ P Q) (hPQ : ¬ (f ∈ P ∧ f ∈ Q)) :
    Step p' τ' P Q := by
  obtain ⟨a, b, c, hab, hbc, hs⟩ := h
  by_cases hfT : f ∈ ({a, b, c} : Finset α)
  · obtain rfl := eq_of_isFirst_mem hr.first hab hbc hfT
    have hb : b ≠ f := (ne_of_key_lt hab).symm
    have hc : c ≠ f := (ne_of_key_lt (hab.trans hbc)).symm
    have h1 : p' b < p' c := by rw [hr.key_eq b hb, hr.key_eq c hc]; exact hbc
    have hT : ({b, c, f} : Finset α) = {f, b, c} := by
      ext; simp only [mem_insert, mem_singleton]; tauto
    have hτ' : τ' {b, c, f} = !τ {f, b, c} := by rw [hr.sign_eq, hT]; simp
    refine ⟨b, c, f, h1, hr.last c hc, ?_⟩
    have e1 : ({f, c} : Finset α) = {c, f} := pair_comm _ _
    have e2 : ({f, b} : Finset α) = {b, f} := pair_comm _ _
    rcases hs with ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp at hPQ
    · exact Or.inr ⟨by simp [hτ', hs], Or.inr (Or.inr ⟨rfl, e1⟩)⟩
    · exact Or.inr ⟨by simp [hτ', hs], Or.inl ⟨rfl, e2⟩⟩
    · simp at hPQ
    · exact Or.inl ⟨by simp [hτ', hs], Or.inr (Or.inr ⟨rfl, e1⟩)⟩
    · exact Or.inl ⟨by simp [hτ', hs], Or.inl ⟨rfl, e2⟩⟩
  · simp only [mem_insert, mem_singleton, not_or] at hfT
    obtain ⟨hfa, hfb, hfc⟩ := hfT
    refine ⟨a, b, c, ?_, ?_, ?_⟩
    · rw [hr.key_eq a (Ne.symm hfa), hr.key_eq b (Ne.symm hfb)]; exact hab
    · rw [hr.key_eq b (Ne.symm hfb), hr.key_eq c (Ne.symm hfc)]; exact hbc
    · have : τ' {a, b, c} = τ {a, b, c} := by
        rw [hr.sign_eq]; simp [hfa, hfb, hfc]
      rw [this]; exact hs

/-- BFS proof of Proposition 3.3, case `I ∈ 𝒰₁`: a chain starting in `𝒰₁` stays in `𝒰₁` (Lemma
B.2) and is kept by the rotation (Lemma B.1). -/
theorem prec_rot_of_uFirst (hτ : IsSigOrd p τ) (hr : IsRot p τ p' τ' f) (h : Prec p τ P Q)
    (hP : UFirst τ f P) : Prec p' τ' P Q := by
  induction h with
  | single h => exact .single (step_rot hr h fun h' => hP.1 h'.1)
  | tail hPB h ih =>
    exact .tail ih (step_rot hr h fun h' => (prec_uFirst hτ hr.first hPB hP).1 h'.1)

/-- BFS proof of Proposition 3.3, case `J ∈ 𝒟₁`: a chain ending in `𝒟₁` lies in `𝒟₁` (Lemma B.2)
and is kept by the rotation (Lemma B.1). -/
theorem prec_rot_of_dFirst (hτ : IsSigOrd p τ) (hr : IsRot p τ p' τ' f) (h : Prec p τ P Q)
    (hQ : DFirst τ f Q) : Prec p' τ' P Q := by
  induction h with
  | single h => exact .single (step_rot hr h fun h' => (step_dFirst hτ hr.first h hQ).1 h'.1)
  | tail _ h ih =>
    have hB := step_dFirst hτ hr.first h hQ
    exact .tail (ih hB) (step_rot hr h fun h' => hB.1 h'.1)

end Rotation

section Line

/-- The order of the crossings on the line `f` (BFS 1.1 picture): `x` before `y` on `f` if
`x < y` and `τ(f,x,y) = +`, or `y < x` and `τ(f,y,x) = -`. For a first element `f` this is the
relation `Step` between `{f, x}` and `{f, y}` (`step_lineRel`). -/
def LineRel (p : α → ℕ) (τ : Finset α → Bool) (f x y : α) : Prop :=
  x ≠ f ∧ y ≠ f ∧ ((p x < p y ∧ τ {f, x, y} = true) ∨ (p y < p x ∧ τ {f, y, x} = false))

lemma lineRel_irrefl {x : α} : ¬ LineRel p τ f x x := by
  rintro ⟨-, -, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> exact lt_irrefl _ h

/-- The order along the first line is transitive (4-packet condition on `f, x, y, z`). -/
theorem lineRel_trans (hτ : IsSigOrd p τ) (hf : IsFirst p f) (hp : Injective p) {x y z : α}
    (hxy : LineRel p τ f x y) (hyz : LineRel p τ f y z) : LineRel p τ f x z := by
  obtain ⟨hx, hy, h1⟩ := hxy
  obtain ⟨-, hz, h2⟩ := hyz
  refine ⟨hx, hz, ?_⟩
  have pfx := hf x hx
  have pfy := hf y hy
  have pfz := hf z hz
  rcases h1 with ⟨o1, s1⟩ | ⟨o1, s1⟩ <;> rcases h2 with ⟨o2, s2⟩ | ⟨o2, s2⟩
  · refine Or.inl ⟨o1.trans o2, ?_⟩
    have hX := hτ f x y z pfx o1 o2
    revert hX s1 s2
    bool_cases [τ {x, y, z}, τ {f, y, z}, τ {f, x, z}, τ {f, x, y}]
  · rcases lt_trichotomy (p x) (p z) with o3 | o3 | o3
    · refine Or.inl ⟨o3, ?_⟩
      have hX := hτ f x z y pfx o3 o2
      revert hX s1 s2
      bool_cases [τ {x, z, y}, τ {f, z, y}, τ {f, x, y}, τ {f, x, z}]
    · obtain rfl := hp o3
      simp_all
    · refine Or.inr ⟨o3, ?_⟩
      have hX := hτ f z x y pfz o3 o1
      revert hX s1 s2
      bool_cases [τ {z, x, y}, τ {f, x, y}, τ {f, z, y}, τ {f, z, x}]
  · rcases lt_trichotomy (p x) (p z) with o3 | o3 | o3
    · refine Or.inl ⟨o3, ?_⟩
      have hX := hτ f y x z pfy o1 o3
      revert hX s1 s2
      bool_cases [τ {y, x, z}, τ {f, x, z}, τ {f, y, z}, τ {f, y, x}]
    · obtain rfl := hp o3
      simp_all
    · refine Or.inr ⟨o3, ?_⟩
      have hX := hτ f y z x pfy o2 o3
      revert hX s1 s2
      bool_cases [τ {y, z, x}, τ {f, z, x}, τ {f, y, x}, τ {f, y, z}]
  · refine Or.inr ⟨o2.trans o1, ?_⟩
    have hX := hτ f z y x pfz o2 o1
    revert hX s1 s2
    bool_cases [τ {z, y, x}, τ {f, y, x}, τ {f, z, x}, τ {f, z, y}]

/-- A step between two sets containing the first element `f` is a step along the line `f`. -/
theorem step_lineRel (hf : IsFirst p f) (h : Step p τ P Q) (hP : f ∈ P) (hQ : f ∈ Q) :
    ∃ x y, P = {f, x} ∧ Q = {f, y} ∧ LineRel p τ f x y := by
  obtain ⟨a, b, c, hab, hbc, hs⟩ := h
  have hba : b ≠ a := (ne_of_key_lt hab).symm
  have hca : c ≠ a := (ne_of_key_lt (hab.trans hbc)).symm
  have hfa : f ∈ ({a, b, c} : Finset α) → f = a := eq_of_isFirst_mem hf hab hbc
  have na : a ∉ ({b, c} : Finset α) := by simp [Ne.symm hba, Ne.symm hca]
  have mem : ∀ x y : α, f ∈ ({x, y} : Finset α) → x ∈ ({a, b, c} : Finset α) →
      y ∈ ({a, b, c} : Finset α) → f = a := fun x y h hx hy => hfa (by
    simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl <;> assumption)
  rcases hs with ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
    ⟨hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · obtain rfl := mem a b hP (by simp) (by simp)
    exact ⟨b, c, rfl, rfl, hba, hca, Or.inl ⟨hbc, hs⟩⟩
  · obtain rfl := mem a c hP (by simp) (by simp)
    exact absurd hQ na
  · obtain rfl := mem a b hP (by simp) (by simp)
    exact absurd hQ na
  · obtain rfl := mem a b hQ (by simp) (by simp)
    exact ⟨c, b, rfl, rfl, hca, hba, Or.inr ⟨hbc, hs⟩⟩
  · obtain rfl := mem a c hQ (by simp) (by simp)
    exact absurd hP na
  · obtain rfl := mem a b hQ (by simp) (by simp)
    exact absurd hP na

/-- Along a chain between two sets containing the first element `f`, every set contains `f`
(`𝒰₁` up-set, `𝒟₁` down-set: BFS Lemma B.2), so the chain runs along the line `f`. -/
theorem prec_lineRel (hτ : IsSigOrd p τ) (hf : IsFirst p f) (hp : Injective p) (h : Prec p τ P Q)
    (hP : f ∈ P) (hQ : f ∈ Q) : ∃ x y, P = {f, x} ∧ Q = {f, y} ∧ LineRel p τ f x y := by
  induction h with
  | single h => exact step_lineRel hf h hP hQ
  | @tail B C hPB h ih =>
    have hB : f ∈ B := by
      by_contra hB
      cases hs : τ (insert f B)
      · exact (prec_dFirst hτ hf hPB ⟨hB, hs⟩).1 hP
      · exact (step_uFirst hτ hf h ⟨hB, hs⟩).1 hQ
    obtain ⟨x, y, rfl, rfl, hxy⟩ := ih hB
    obtain ⟨y', z, hy', rfl, hyz⟩ := step_lineRel hf h hB hQ
    obtain rfl := eq_of_pair_eq_pair hy' hxy.2.1
    exact ⟨x, z, rfl, rfl, lineRel_trans hτ hf hp hxy hyz⟩

/-- No cycle of `≺` through a set containing the first element (acyclicity on `𝓗₁`). -/
theorem not_prec_self_of_first_mem (hτ : IsSigOrd p τ) (hf : IsFirst p f) (hp : Injective p)
    (hP : f ∈ P) : ¬ Prec p τ P P := by
  intro h
  obtain ⟨x, y, hx, hy, hxy⟩ := prec_lineRel hτ hf hp h hP hP
  obtain rfl := eq_of_pair_eq_pair (hx.symm.trans hy) hxy.1
  exact lineRel_irrefl hxy

/-- A cycle of `≺` avoiding the first element survives the rotation (BFS Lemmas B.1, B.2). -/
theorem prec_self_rot (hτ : IsSigOrd p τ) (hr : IsRot p τ p' τ' f) (hP : f ∉ P)
    (h : Prec p τ P P) : Prec p' τ' P P := by
  cases hs : τ (insert f P)
  · exact prec_rot_of_dFirst hτ hr h ⟨hP, hs⟩
  · exact prec_rot_of_uFirst hτ hr h ⟨hP, hs⟩

end Line

section Prop33

/-- BFS Proposition 3.3 (`r = 3`): if `I ≺ J` and the rotated element `f` is not in both, then
after the rotation `J ≺ I` does not hold (`I`, `J` are incomparable or `I ≺ J`). As in BFS, this
uses that the rotated relation is acyclic (`hacyc`). -/
theorem prop33 (hτ : IsSigOrd p τ) (hr : IsRot p τ p' τ' f) (hacyc : ∀ P, ¬ Prec p' τ' P P)
    {I J : Finset α} (hIJ : Prec p τ I J) (hf : ¬ (f ∈ I ∧ f ∈ J)) : ¬ Prec p' τ' J I := by
  intro hJI
  have hτ' := isSigOrd_rot hτ hr
  have hsign : ∀ X, τ' (insert f X) = !τ (insert f X) := fun X => by simp [hr.sign_eq]
  by_cases hI : f ∈ I
  · have hJ : f ∉ J := fun hJ => hf ⟨hI, hJ⟩
    cases hs : τ (insert f J)
    · exact (prec_dFirst hτ hr.first hIJ ⟨hJ, hs⟩).1 hI
    · exact (prec_uLast hτ' hr.last hJI ⟨hJ, by simp [hsign, hs]⟩).1 hI
  · cases hs : τ (insert f I)
    · obtain ⟨hJ, hsJ⟩ := prec_dLast hτ' hr.last hJI ⟨hI, by simp [hsign, hs]⟩
      have hDJ : DFirst τ f J := ⟨hJ, by simpa [hsign] using hsJ⟩
      exact hacyc I (.trans (prec_rot_of_dFirst hτ hr hIJ hDJ) hJI)
    · exact hacyc I (.trans (prec_rot_of_uFirst hτ hr hIJ ⟨hI, hs⟩) hJI)

end Prop33

section Prop31

/-- The sign condition of BFS Proposition 3.1 for an extension by a new last element with signs
`g P` on `P ∪ {new}`: for every triple `a < b < c` the 4-packet `(a, b, c, new)` has at most one
sign change. -/
def ValidExt (p : α → ℕ) (τ : Finset α → Bool) (g : Finset α → Bool) : Prop :=
  ∀ a b c : α, p a < p b → p b < p c → AtMostOneChange [g {b, c}, g {a, c}, g {a, b}, τ {a, b, c}]

/-- BFS Proposition 3.1, signotope part: a down-set gives a valid extension (sign `+` on the
down-set). -/
theorem validExt_downSet (D : Finset α → Prop) [DecidablePred D]
    (hD : ∀ P Q, Step p τ P Q → D Q → D P) : ValidExt p τ (fun P => decide (D P)) := by
  intro a b c hab hbc
  have st : ∀ P Q, (τ {a, b, c} = true ∧ PlusSteps a b c P Q) ∨
      (τ {a, b, c} = false ∧ PlusSteps a b c Q P) → D Q → D P :=
    fun P Q h => hD P Q ⟨a, b, c, hab, hbc, h⟩
  cases hs : τ {a, b, c}
  · have h1 := st {a, c} {a, b} (Or.inr ⟨hs, Or.inl ⟨rfl, rfl⟩⟩)
    have h2 := st {b, c} {a, c} (Or.inr ⟨hs, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
    by_cases d1 : D {b, c} <;> by_cases d2 : D {a, c} <;> by_cases d3 : D {a, b} <;>
      simp_all [AtMostOneChange]
  · have h1 := st {a, b} {a, c} (Or.inl ⟨hs, Or.inl ⟨rfl, rfl⟩⟩)
    have h2 := st {a, c} {b, c} (Or.inl ⟨hs, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
    by_cases d1 : D {b, c} <;> by_cases d2 : D {a, c} <;> by_cases d3 : D {a, b} <;>
      simp_all [AtMostOneChange]

/-- BFS Proposition 3.1, fliple part: changing the sign of a maximal element `M` of the down-set
still gives a valid extension, so `M ∪ {new}` is a fliple. -/
theorem validExt_toggle (D : Finset α → Prop) [DecidablePred D]
    (hD : ∀ P Q, Step p τ P Q → D Q → D P) {M : Finset α} (hM : D M)
    (hmax : ∀ Q, Step p τ M Q → ¬ D Q) :
    ValidExt p τ (update (fun P => decide (D P)) M false) := by
  intro a b c hab hbc
  have hD' := validExt_downSet D hD a b c hab hbc
  have hab' := ne_of_key_lt hab
  have hbc' := ne_of_key_lt hbc
  have hac' := ne_of_key_lt (hab.trans hbc)
  have n1 : ({a, b} : Finset α) ≠ {a, c} := fun h => hbc' (eq_of_pair_eq_pair h hab'.symm)
  have n2 : ({a, b} : Finset α) ≠ {b, c} := fun h => by
    have : a ∈ ({b, c} : Finset α) := h ▸ by simp
    simp only [mem_insert, mem_singleton] at this; tauto
  have n3 : ({a, c} : Finset α) ≠ {b, c} := fun h => by
    have : a ∈ ({b, c} : Finset α) := h ▸ by simp
    simp only [mem_insert, mem_singleton] at this; tauto
  have st : ∀ Q, (τ {a, b, c} = true ∧ PlusSteps a b c M Q) ∨
      (τ {a, b, c} = false ∧ PlusSteps a b c Q M) → ¬ D Q :=
    fun Q h => hmax Q ⟨a, b, c, hab, hbc, h⟩
  simp only [update_apply]
  by_cases e1 : ({b, c} : Finset α) = M
  · subst e1
    simp only [if_neg n3, if_neg n2]
    cases hs : τ {a, b, c}
    · have := st {a, c} (Or.inr ⟨hs, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
      have := st {a, b} (Or.inr ⟨hs, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)
      by_cases d1 : D {b, c} <;> by_cases d2 : D {a, c} <;> by_cases d3 : D {a, b} <;>
        simp_all [AtMostOneChange]
    · by_cases d1 : D {b, c} <;> by_cases d2 : D {a, c} <;> by_cases d3 : D {a, b} <;>
        simp_all [AtMostOneChange]
  by_cases e2 : ({a, c} : Finset α) = M
  · subst e2
    simp only [if_neg e1, if_neg n1]
    cases hs : τ {a, b, c}
    · have := st {a, b} (Or.inr ⟨hs, Or.inl ⟨rfl, rfl⟩⟩)
      by_cases d1 : D {b, c} <;> by_cases d2 : D {a, c} <;> by_cases d3 : D {a, b} <;>
        simp_all [AtMostOneChange]
    · have := st {b, c} (Or.inl ⟨hs, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩)
      by_cases d1 : D {b, c} <;> by_cases d2 : D {a, c} <;> by_cases d3 : D {a, b} <;>
        simp_all [AtMostOneChange]
  by_cases e3 : ({a, b} : Finset α) = M
  · subst e3
    simp only [if_neg e1, if_neg e2]
    cases hs : τ {a, b, c}
    · by_cases d1 : D {b, c} <;> by_cases d2 : D {a, c} <;> by_cases d3 : D {a, b} <;>
        simp_all [AtMostOneChange]
    · have := st {a, c} (Or.inl ⟨hs, Or.inl ⟨rfl, rfl⟩⟩)
      have := st {b, c} (Or.inl ⟨hs, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)
      by_cases d1 : D {b, c} <;> by_cases d2 : D {a, c} <;> by_cases d3 : D {a, b} <;>
        simp_all [AtMostOneChange]
  simp only [if_neg e1, if_neg e2, if_neg e3]
  exact hD'

end Prop31

end Pca.Great.Sig
