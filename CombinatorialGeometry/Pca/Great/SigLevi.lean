/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Levi's extension lemma for 3-signotopes (P4', BFS Theorem 1.2 for `r = 3`)

BFS (https://arxiv.org/abs/2303.04079), Theorem 1.2: "For every odd rank `r ≥ 3`, every
`r`-signotope is 2-extendable", with 2-extendable (BFS 1.2): for pairwise disjoint
`(r-1)`-subsets `I₁, I₂` there are `k ∈ [n+1]` and an `r`-signotope `σ*` on `[n+1]` with fliples
`I₁*, I₂*`, `σ*↓k = σ` and `Iⱼ*↓k = Iⱼ`. Here `r = 3`: `I`, `J` are disjoint 2-subsets (two
crossings without a common pseudoline: Levi's lemma for crossing points in general position, the
non-degenerate case, BFS 1.2). Proof plan: `doc/pca/great.md` section 5.
-/
import Pca.Great.Sig_Ext

open Finset Relation Function

namespace Pca.Great.Sig

/-- **Levi's extension lemma, signotope version** (BFS Theorem 1.2, rank 3). -/
theorem levi {n : ℕ} (σ : Finset (Fin n) → Bool) (hσ : IsSig σ) (I J : Finset (Fin n))
    (hI : I.card = 2) (hJ : J.card = 2) (hIJ : Disjoint I J) :
    ∃ (k : Fin (n + 1)) (σ' : Finset (Fin (n + 1)) → Bool), IsSig σ' ∧ Extends σ' k σ ∧
      IsFliple σ' (lift k I) ∧ IsFliple σ' (lift k J) := by
  classical
  have hn : 0 < n := by
    have := card_le_univ I
    simp only [Fintype.card_fin] at this
    omega
  -- BFS Proposition 3.4: after `kk < n` rotations `I` and `J` are incomparable.
  obtain ⟨kk, hkn, hIJ', hJI'⟩ := prop34 hσ hIJ hn
  -- BFS section 3.1: the down-set of `I` and `J`, in which both are maximal.
  let D : Finset (Fin n) → Prop := fun P =>
    ReflTransGen (Step (key n kk) (twist kk σ)) P I ∨ ReflTransGen (Step (key n kk) (twist kk σ)) P J
  have hD : ∀ P Q, Step (key n kk) (twist kk σ) P Q → D Q → D P :=
    fun P Q h hQ => hQ.imp (fun h' => .head h h') (fun h' => .head h h')
  have hacyc := prec_irrefl hσ (j := kk) hkn.le
  have hmax : ∀ {M M'}, ¬ Prec (key n kk) (twist kk σ) M M' → (M = I ∧ M' = J ∨ M = J ∧ M' = I) →
      ∀ Q, Step (key n kk) (twist kk σ) M Q → ¬ D Q := by
    rintro M M' hMM' hM Q h (hQ | hQ)
    · rcases hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hacyc M (TransGen.head' h hQ)
      · exact hMM' (TransGen.head' h hQ)
    · rcases hM with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hMM' (TransGen.head' h hQ)
      · exact hacyc M (TransGen.head' h hQ)
  let g : Finset (Fin n) → Bool := fun P => decide (D P)
  have hg : ValidExt (key n kk) (twist kk σ) g := validExt_downSet D hD
  have hgI : ValidExt (key n kk) (twist kk σ) (update g I (!g I)) := by
    have : g I = true := decide_eq_true (Or.inl .refl)
    rw [this]
    exact validExt_toggle D hD (Or.inl .refl) (hmax hIJ' (Or.inl ⟨rfl, rfl⟩))
  have hgJ : ValidExt (key n kk) (twist kk σ) (update g J (!g J)) := by
    have : g J = true := decide_eq_true (Or.inr .refl)
    rw [this]
    exact validExt_toggle D hD (Or.inr .refl) (hmax hJI' (Or.inr ⟨rfl, rfl⟩))
  -- The new element is `kk` (BFS: `k + 1`, 1-based).
  let k : Fin (n + 1) := ⟨kk, by omega⟩
  exact ⟨k, ext k σ g, isSig_ext hσ k hg, fun X _ => del_ext k σ g X,
    isFliple_ext hσ k hI hg hgI, isFliple_ext hσ k hJ hg hgJ⟩

end Pca.Great.Sig
