/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Iterated rotations of a 3-signotope on `Fin n` (BFS section 2, Propositions 3.3, 3.4)

BFS = Bergold, Felsner, Scheucher, https://arxiv.org/abs/2303.04079.

After `j` clockwise rotations (BFS section 2) the elements `0, …, j-1` have moved, in this order,
behind `j, …, n-1`, and the sign of a 3-subset `X` has changed once for each element of `X` among
`0, …, j-1`. Instead of relabeling the elements (`X ↦ X_rot`) we keep the sets and change the
order: `key n j` is the order after `j` rotations, `twist j σ` the signs. One rotation from `j` to
`j + 1` is an `IsRot` with rotated element `j` (`isRot_twist`); for `j = n` the order is the
original one and all signs are reversed (`r = 3` is odd).

* BFS Lemma 2.1 iterated: `isSigOrd_twist`, and back: `isSig_of_isSigOrd_twist`.
* Acyclicity of `≺` (BFS section 2, cited there from Felsner-Weil [9, Lemma 10]; proved here from
  BFS Lemmas B.1, B.2, see `doc/pca/great.md` section 5): `prec_irrefl`.
* BFS Proposition 3.4: `prop34`.
-/
import Pca.Great.Sig_Order

open Finset Relation Function

namespace Pca.Great.Sig

variable {n : ℕ}

/-- The order after `j` clockwise rotations: the elements `0, …, j-1` come after all others. -/
def key (n j : ℕ) (x : Fin n) : ℕ := if x.val < j then x.val + n else x.val

/-- The signs after `j` clockwise rotations (BFS section 2, `σ_rot(X_rot) = -σ(X)` iff the rotated
element is in `X`, iterated): the sign of `T` changes once for each element of `T` below `j`. -/
def twist (j : ℕ) (σ : Finset (Fin n) → Bool) (T : Finset (Fin n)) : Bool :=
  σ T ^^ decide ((T.filter (fun x => x.val < j)).card % 2 = 1)

lemma key_injective (j : ℕ) : Injective (key n j) := by
  intro x y h
  have := x.isLt
  have := y.isLt
  unfold key at h
  apply Fin.ext
  split_ifs at h <;> omega

lemma key_zero (x : Fin n) : key n 0 x = x.val := by simp [key]

lemma key_full (x : Fin n) : key n n x = x.val + n := by simp [key, x.isLt]

lemma twist_zero (σ : Finset (Fin n) → Bool) : twist 0 σ = σ := by
  funext T
  simp [twist]

lemma twist_twist (j : ℕ) (σ : Finset (Fin n) → Bool) : twist j (twist j σ) = σ := by
  funext T
  simp only [twist]
  cases σ T <;> cases decide ((T.filter (fun x => x.val < j)).card % 2 = 1) <;> rfl

lemma card_triple {a b c : Fin n} (hab : a < b) (hbc : b < c) : ({a, b, c} : Finset _).card = 3 :=
  card_eq_three.2 ⟨a, b, c, hab.ne, (hab.trans hbc).ne, hbc.ne, rfl⟩

/-- After `n` rotations every sign of a 3-subset is reversed (BFS proof of Proposition 3.4). -/
lemma twist_full (σ : Finset (Fin n) → Bool) {T : Finset (Fin n)} (hT : T.card = 3) :
    twist n σ T = !σ T := by
  simp [twist, filter_true_of_mem (fun (x : Fin n) _ => x.isLt), hT]

lemma parity_succ (c : ℕ) : decide ((c + 1) % 2 = 1) = !decide (c % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [Nat.add_mod, h]

/-- The rotation from `j` to `j + 1` rotates the element `j` (BFS section 2). -/
theorem isRot_twist (σ : Finset (Fin n) → Bool) {j : ℕ} (hj : j < n) :
    IsRot (key n j) (twist j σ) (key n (j + 1)) (twist (j + 1) σ) ⟨j, hj⟩ where
  first x hx := by
    have : x.val ≠ j := fun h => hx (Fin.ext h)
    have := x.isLt
    have e : (⟨j, hj⟩ : Fin n).val = j := rfl
    unfold key
    split_ifs <;> omega
  last x hx := by
    have : x.val ≠ j := fun h => hx (Fin.ext h)
    have := x.isLt
    have e : (⟨j, hj⟩ : Fin n).val = j := rfl
    unfold key
    split_ifs <;> omega
  key_eq x hx := by
    have : x.val ≠ j := fun h => hx (Fin.ext h)
    unfold key
    split_ifs <;> omega
  sign_eq T := by
    by_cases hT : (⟨j, hj⟩ : Fin n) ∈ T
    · have hu : T.filter (fun x => x.val < j + 1) =
          insert ⟨j, hj⟩ (T.filter (fun x => x.val < j)) := by
        ext x
        by_cases hx : x ∈ T
        · simp only [mem_filter, mem_insert, hx, true_and, Fin.ext_iff]
          omega
        · simp only [mem_filter, mem_insert, hx, false_and, or_false, Fin.ext_iff]
          exact ⟨False.elim, fun h => hx (by rwa [show x = ⟨j, hj⟩ from Fin.ext h])⟩
      have hn : (⟨j, hj⟩ : Fin n) ∉ T.filter (fun x => x.val < j) := by simp
      simp only [twist, hu, card_insert_of_notMem hn, parity_succ, hT, decide_true]
      cases σ T <;> cases decide ((T.filter (fun x => x.val < j)).card % 2 = 1) <;> rfl
    · have hu : T.filter (fun x => x.val < j + 1) = T.filter (fun x => x.val < j) := by
        ext x
        simp only [mem_filter]
        constructor
        · rintro ⟨hx, h⟩
          refine ⟨hx, ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
          · exact h
          · exact absurd (by rw [show x = ⟨j, hj⟩ from Fin.ext h] at hx; exact hx) hT
        · rintro ⟨hx, h⟩
          exact ⟨hx, by omega⟩
      simp only [twist, hu, hT, decide_false, Bool.xor_false]

/-- BFS Lemma 2.1, iterated: after `j ≤ n` rotations the signotope is a signotope. -/
theorem isSigOrd_twist {σ : Finset (Fin n) → Bool} (hσ : IsSig σ) :
    ∀ j, j ≤ n → IsSigOrd (key n j) (twist j σ)
  | 0, _ => by
    rw [twist_zero]
    intro x₁ x₂ x₃ x₄ h12 h23 h34
    simp only [key_zero] at h12 h23 h34
    exact hσ _ _ _ _ h12 h23 h34
  | j + 1, hj => isSigOrd_rot (isSigOrd_twist hσ j (by omega)) (isRot_twist σ (by omega))

lemma amoc_of_not {a b c d : Bool} (h : AtMostOneChange [!a, !b, !c, !d]) :
    AtMostOneChange [a, b, c, d] := by
  revert h
  bool_cases [a, b, c, d]

/-- Conversely, a signotope after `j` rotations comes from a signotope: rotate on to `n`
rotations, where all signs are reversed. -/
theorem isSig_of_isSigOrd_twist {σ : Finset (Fin n) → Bool} {j : ℕ} (hj : j ≤ n)
    (h : IsSigOrd (key n j) (twist j σ)) : IsSig σ := by
  have hm : ∀ m, j + m ≤ n → IsSigOrd (key n (j + m)) (twist (j + m) σ) := by
    intro m
    induction m with
    | zero => intro _; exact h
    | succ m ih => intro hm; exact isSigOrd_rot (ih (by omega)) (isRot_twist σ (by omega))
  have hn := hm (n - j) (by omega)
  rw [Nat.add_sub_cancel' hj] at hn
  intro x₁ x₂ x₃ x₄ h12 h23 h34
  have := Fin.lt_iff_val_lt_val.1 h12
  have := Fin.lt_iff_val_lt_val.1 h23
  have := Fin.lt_iff_val_lt_val.1 h34
  have hX := hn x₁ x₂ x₃ x₄ (by simp only [key_full]; omega) (by simp only [key_full]; omega)
    (by simp only [key_full]; omega)
  rw [twist_full σ (card_triple h23 h34), twist_full σ (card_triple (h12.trans h23) h34),
    twist_full σ (card_triple h12 (h23.trans h34)), twist_full σ (card_triple h12 h23)] at hX
  exact amoc_of_not hX

lemma step_full_of_zero {σ : Finset (Fin n) → Bool} {P Q : Finset (Fin n)}
    (h : Step (key n 0) (twist 0 σ) P Q) : Step (key n n) (twist n σ) Q P :=
  step_swap_of_neg (fun x y hxy => by simp only [key_zero, key_full] at *; omega)
    (fun a b c hab hbc => by
      simp only [key_zero] at hab hbc
      rw [twist_full σ (card_triple hab hbc), twist_zero]) h

lemma step_zero_of_full {σ : Finset (Fin n) → Bool} {P Q : Finset (Fin n)}
    (h : Step (key n n) (twist n σ) P Q) : Step (key n 0) (twist 0 σ) Q P :=
  step_swap_of_neg (fun x y hxy => by simp only [key_zero, key_full] at *; omega)
    (fun a b c hab hbc => by
      simp only [key_full] at hab hbc
      rw [twist_full σ (card_triple (Fin.lt_iff_val_lt_val.2 (by omega))
        (Fin.lt_iff_val_lt_val.2 (by omega))),
        twist_zero, Bool.not_not]) h

section Acyclic

variable {σ : Finset (Fin n) → Bool} (hσ : IsSig σ)
include hσ

/-- A cycle through a set containing the element `j` is impossible after `j` rotations (`j` is
then the first element). -/
lemma not_prec_self_of_mem {j : ℕ} (hj : j < n) {P : Finset (Fin n)} (hP : ⟨j, hj⟩ ∈ P) :
    ¬ Prec (key n j) (twist j σ) P P :=
  not_prec_self_of_first_mem (isSigOrd_twist hσ j hj.le) (isRot_twist σ hj).first
    (key_injective j) hP

/-- A cycle survives further rotations (or there was none). -/
lemma prec_self_fwd {j : ℕ} {P : Finset (Fin n)} :
    ∀ m, j + m ≤ n → Prec (key n j) (twist j σ) P P → Prec (key n (j + m)) (twist (j + m) σ) P P
  | 0, _, h => h
  | m + 1, hm, h => by
    have h' := prec_self_fwd m (by omega) h
    by_cases hP : (⟨j + m, by omega⟩ : Fin n) ∈ P
    · exact absurd h' (not_prec_self_of_mem hσ (by omega) hP)
    · exact prec_self_rot (isSigOrd_twist hσ (j + m) (by omega)) (isRot_twist σ (by omega)) hP h'

/-- The relation `≺` after `j ≤ n` rotations is acyclic, hence a strict partial order (BFS section
2, which cites Felsner-Weil [9, Lemma 10]). Proof (not from BFS): a cycle survives each rotation
whose rotated element is in none of its sets (BFS Lemmas B.1, B.2), is impossible when the rotated
element is in one of its sets (order along the first line), and after `n` rotations it is a cycle of
the original relation reversed. Starting from `0` rotations, the element `x ∈ P` is rotated
after `x` steps. -/
theorem prec_irrefl {j : ℕ} (hj : j ≤ n) (P : Finset (Fin n)) :
    ¬ Prec (key n j) (twist j σ) P P := by
  intro h
  have hn := prec_self_fwd hσ (n - j) (by omega) h
  rw [Nat.add_sub_cancel' hj] at hn
  have h0 : Prec (key n 0) (twist 0 σ) P P :=
    (TransGen.swap _ _ hn).lift id fun _ _ hab => step_zero_of_full hab
  obtain ⟨Q, hPQ, -⟩ := TransGen.head'_iff.1 h0
  obtain ⟨x, hx⟩ := step_nonempty hPQ
  have hx' := prec_self_fwd hσ x.val (by omega) h0
  rw [Nat.zero_add] at hx'
  exact not_prec_self_of_mem hσ x.isLt hx hx'

/-- BFS Proposition 3.3 for the rotation from `j` to `j + 1`. -/
theorem prop33_twist {j : ℕ} (hj : j < n) {I J : Finset (Fin n)}
    (hIJ : Prec (key n j) (twist j σ) I J) (hf : ¬ ((⟨j, hj⟩ : Fin n) ∈ I ∧ ⟨j, hj⟩ ∈ J)) :
    ¬ Prec (key n (j + 1)) (twist (j + 1) σ) J I :=
  prop33 (isSigOrd_twist hσ j hj.le) (isRot_twist σ hj) (prec_irrefl hσ (by omega)) hIJ hf

/-- BFS Proposition 3.4, the case `I ≺ J` at the start: some rotation `k < n` makes `I`, `J`
incomparable. -/
lemma prop34_aux {I J : Finset (Fin n)} (hIJ : Disjoint I J) (hn : 0 < n)
    (h0 : Prec (key n 0) (twist 0 σ) I J)
    (hcomp : ∀ k < n, Prec (key n k) (twist k σ) I J ∨ Prec (key n k) (twist k σ) J I) : False := by
  have hdisj : ∀ x, ¬ (x ∈ I ∧ x ∈ J) := fun x h => disjoint_left.1 hIJ h.1 h.2
  have hall : ∀ k, k < n → Prec (key n k) (twist k σ) I J := by
    intro k
    induction k with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hk
      rcases hcomp (k + 1) hk with h | h
      · exact h
      · exact absurd h (prop33_twist hσ (by omega) (ih (by omega)) (hdisj _))
  have hrev : Prec (key n n) (twist n σ) J I :=
    (TransGen.swap _ _ h0).lift id fun _ _ hab => step_full_of_zero hab
  have e : n - 1 + 1 = n := by omega
  have := prop33_twist hσ (j := n - 1) (by omega) (hall (n - 1) (by omega)) (hdisj _)
  rw [e] at this
  exact this hrev

/-- BFS Proposition 3.4 (`r = 3`): for disjoint `I`, `J` there is `k < n` such that `I` and `J`
are incomparable after `k` clockwise rotations. -/
theorem prop34 {I J : Finset (Fin n)} (hIJ : Disjoint I J) (hn : 0 < n) :
    ∃ k < n, ¬ Prec (key n k) (twist k σ) I J ∧ ¬ Prec (key n k) (twist k σ) J I := by
  by_contra hc
  have hcomp : ∀ k < n, Prec (key n k) (twist k σ) I J ∨ Prec (key n k) (twist k σ) J I := by
    intro k hk
    by_contra h
    exact hc ⟨k, hk, not_or.1 h⟩
  by_cases h0 : Prec (key n 0) (twist 0 σ) I J
  · exact prop34_aux hσ hIJ hn h0 hcomp
  · have h0' := (hcomp 0 hn).resolve_left h0
    exact prop34_aux hσ hIJ.symm hn h0' fun k hk => (hcomp k hk).symm

end Acyclic

end Pca.Great.Sig
