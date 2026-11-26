/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Extension of a rotated 3-signotope by a new last element (BFS Proposition 3.1, Lemma 3.5)

BFS = Bergold, Felsner, Scheucher, https://arxiv.org/abs/2303.04079.

BFS section 3.1 extends the `k`-fold rotated signotope `σ_rot(k)` by a last element `n + 1`
(Proposition 3.1) and rotates back `k + 1` times; by Lemma 3.5 the new element is then `k + 1`
and deleting it gives `σ`, by Lemma 2.2 the fliples are kept. In the key form of
`Pca/Great/Sig_Twist.lean` this is one explicit map: the new element is `k : Fin (n + 1)`, the old
elements are `k.succAbove y`, the signs after `k + 1` rotations of the extension (`extT`) are
those of `σ_rot(k)` on old sets and `g P` on `P ∪ {k}`, and `ext k σ g` is the extension itself
(`twist (k + 1)` undone). Lemma 3.5 becomes `del_ext` (no rotation needed), Lemma 2.2 the fact
that the twist does not move sets (`ext_update`).
-/
import Pca.Great.Sig_Twist

open Finset Function

namespace Pca.Great.Sig

variable {n : ℕ}

/-- The old elements of a subset of `Fin (n + 1)`, as a subset of `Fin n` (`X↓k` of BFS 1.2). -/
def pull (k : Fin (n + 1)) (X : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter (fun y => k.succAbove y ∈ X)

@[simp] lemma mem_pull {k : Fin (n + 1)} {X : Finset (Fin (n + 1))} {y : Fin n} :
    y ∈ pull k X ↔ k.succAbove y ∈ X := by
  simp [pull]

lemma pull_map (k : Fin (n + 1)) (Y : Finset (Fin n)) : pull k (Y.map k.succAboveEmb) = Y := by
  ext y
  simp

lemma pull_lift (k : Fin (n + 1)) (P : Finset (Fin n)) : pull k (lift k P) = P := by
  ext y
  simp [lift]

lemma eq_lift_pull {k : Fin (n + 1)} {X : Finset (Fin (n + 1))} (hk : k ∈ X) :
    X = lift k (pull k X) := by
  ext x
  by_cases hx : x = k
  · subst hx
    simp [lift, hk]
  · obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq hx
    simp [lift]

lemma val_succAbove (k : Fin (n + 1)) (y : Fin n) :
    (k.succAbove y).val = if y.val < k.val then y.val else y.val + 1 := by
  unfold Fin.succAbove
  split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_iff_val_lt_val]

lemma key_succAbove (k : Fin (n + 1)) (y : Fin n) :
    key (n + 1) (k.val + 1) (k.succAbove y) = key n k.val y + 1 := by
  unfold key
  rw [val_succAbove]
  split_ifs <;> omega

lemma isLast_key_ext (k : Fin (n + 1)) : IsLast (key (n + 1) (k.val + 1)) k := by
  intro x hx
  have : x.val ≠ k.val := fun h => hx (Fin.ext h)
  have := x.isLt
  unfold key
  split_ifs <;> omega

/-- The signs after `k + 1` rotations of the extension: `g P` on `P ∪ {k}`, `τ` (the signs of
`σ_rot(k)`) on the old sets (BFS proof of Proposition 3.1, with `g` the indicator of the
down-set). -/
def extT (k : Fin (n + 1)) (τ g : Finset (Fin n) → Bool) (X : Finset (Fin (n + 1))) : Bool :=
  if k ∈ X then g (pull k X) else τ (pull k X)

/-- The extension `σ*` of `σ` by the new element `k` (BFS section 3.1). -/
def ext (k : Fin (n + 1)) (σ g : Finset (Fin n) → Bool) : Finset (Fin (n + 1)) → Bool :=
  twist (k.val + 1) (extT k (twist k.val σ) g)

/-- BFS Proposition 3.1 (signotope part), after `k` rotations: the extension by a new last element
is a signotope if the signs `g` satisfy the 4-packet condition with the new element. -/
theorem isSigOrd_extT (k : Fin (n + 1)) {τ g : Finset (Fin n) → Bool}
    (hτ : IsSigOrd (key n k.val) τ) (hg : ValidExt (key n k.val) τ g) :
    IsSigOrd (key (n + 1) (k.val + 1)) (extT k τ g) := by
  intro x₁ x₂ x₃ x₄ h12 h23 h34
  have hl := isLast_key_ext k
  have nk : ∀ x, key (n + 1) (k.val + 1) x < key (n + 1) (k.val + 1) x₄ → x ≠ k := by
    rintro x hx rfl
    exact absurd (hl x₄ (ne_of_key_lt hx).symm) (by omega)
  have pmap : ∀ a b c : Fin n,
      extT k τ g {k.succAbove a, k.succAbove b, k.succAbove c} = τ {a, b, c} := by
    intro a b c
    have : pull k {k.succAbove a, k.succAbove b, k.succAbove c} = {a, b, c} := by
      ext; simp [Fin.succAbove_right_inj]
    simp [extT, this]
  have pins : ∀ a b : Fin n, extT k τ g {k.succAbove a, k.succAbove b, k} = g {a, b} := by
    intro a b
    have : pull k {k.succAbove a, k.succAbove b, k} = {a, b} := by
      ext; simp [Fin.succAbove_right_inj]
    simp [extT, this]
  obtain ⟨y₁, rfl⟩ := Fin.exists_succAbove_eq (nk x₁ (by omega))
  obtain ⟨y₂, rfl⟩ := Fin.exists_succAbove_eq (nk x₂ (by omega))
  obtain ⟨y₃, rfl⟩ := Fin.exists_succAbove_eq (nk x₃ h34)
  rw [key_succAbove, key_succAbove] at h12 h23
  by_cases h4 : x₄ = k
  · subst h4
    rw [pins, pins, pins, pmap]
    exact hg y₁ y₂ y₃ (by omega) (by omega)
  · obtain ⟨y₄, rfl⟩ := Fin.exists_succAbove_eq h4
    rw [key_succAbove, key_succAbove] at h34
    rw [pmap, pmap, pmap, pmap]
    exact hτ y₁ y₂ y₃ y₄ (by omega) (by omega) (by omega)

/-- BFS Lemma 3.5 / section 3.1: deleting the new element `k` gives back `σ`. -/
theorem del_ext (k : Fin (n + 1)) (σ g : Finset (Fin n) → Bool) (Y : Finset (Fin n)) :
    del (ext k σ g) k Y = σ Y := by
  have hk : k ∉ Y.map k.succAboveEmb := by simp
  have hc : ((Y.map k.succAboveEmb).filter (fun x => x.val < k.val + 1)).card =
      (Y.filter (fun y => y.val < k.val)).card := by
    rw [filter_map, card_map]
    congr 1
    apply filter_congr
    intro y _
    simp only [comp_apply, Fin.coe_succAboveEmb, val_succAbove]
    split_ifs <;> omega
  simp only [del, ext, twist, extT, if_neg hk, pull_map, hc]
  cases σ Y <;> cases decide ((Y.filter (fun y => y.val < k.val)).card % 2 = 1) <;> rfl

/-- The extension is a signotope (BFS Proposition 3.1 and Lemma 2.1). -/
theorem isSig_ext {σ g : Finset (Fin n) → Bool} (hσ : IsSig σ) (k : Fin (n + 1))
    (hg : ValidExt (key n k.val) (twist k.val σ) g) : IsSig (ext k σ g) := by
  apply isSig_of_isSigOrd_twist (j := k.val + 1) (by omega)
  rw [ext, twist_twist]
  exact isSigOrd_extT k (isSigOrd_twist hσ k.val (by omega)) hg

/-- Changing the sign of `M ∪ {k}` in the extension is changing `g M`. -/
lemma ext_update (k : Fin (n + 1)) (σ g : Finset (Fin n) → Bool) (M : Finset (Fin n)) :
    update (ext k σ g) (lift k M) (!ext k σ g (lift k M)) = ext k σ (update g M (!g M)) := by
  funext X
  by_cases hX : X = lift k M
  · subst hX
    have hk : k ∈ lift k M := mem_insert_self _ _
    simp only [update_self, ext, twist, extT, if_pos hk, pull_lift]
    cases g M <;> cases decide (((lift k M).filter (fun x => x.val < k.val + 1)).card % 2 = 1) <;>
      rfl
  · rw [update_of_ne hX]
    simp only [ext, twist, extT]
    split_ifs with hk
    · have : pull k X ≠ M := fun h => hX (h ▸ eq_lift_pull hk)
      rw [update_of_ne this]
    · rfl

lemma card_lift (k : Fin (n + 1)) {M : Finset (Fin n)} (hM : M.card = 2) :
    (lift k M).card = 3 := by
  rw [lift, card_insert_of_notMem (by simp), card_map, hM]

/-- BFS Proposition 3.1 (fliple part) and Lemma 2.2: if changing `g M` keeps the 4-packet
condition, then `M ∪ {k}` is a fliple of the extension. -/
theorem isFliple_ext {σ g : Finset (Fin n) → Bool} (hσ : IsSig σ) (k : Fin (n + 1))
    {M : Finset (Fin n)} (hM : M.card = 2) (hg : ValidExt (key n k.val) (twist k.val σ) g)
    (hg' : ValidExt (key n k.val) (twist k.val σ) (update g M (!g M))) :
    IsFliple (ext k σ g) (lift k M) :=
  ⟨card_lift k hM, isSig_ext hσ k hg, by rw [ext_update]; exact isSig_ext hσ k hg'⟩

end Pca.Great.Sig
