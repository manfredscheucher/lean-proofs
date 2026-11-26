/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Track P: the final statements (`doc/pca/flipgraph.md`, Track P; `doc/pca/great.md`)

* P2: `exists_antipodalTri`, `aflip_isGreat` (from `Pca/Great/AFlip.lean`),
* P3: `ringel` (`Pca/Great/Ringel.lean`), Ringel's theorem: the antipodal-flip graph of
  great-pseudocircle arrangements on `n` curves is connected up to isomorphism,
* P4: `levi` (`Pca/Great/GreatLevi.lean`), Levi's extension lemma: through two given cells a
  new great pseudocircle can be inserted (signotope variant: `SigLevi.lean`).
-/
import Pca.Great.Ringel
import Pca.Great.GreatLevi

open Equiv Finset

namespace Pca.Great

universe u v

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

/-- P2 (a): every triangle of a great-pseudocircle arrangement has an antipodal triangle. -/
theorem exists_antipodalTri {A : Arrangement n D} (hA : A.IsGreat) {T : A.Cell}
    (hT : A.IsTriangle T) : ∃ T', A.IsAntipodalTri T T' := by
  obtain ⟨d, rfl⟩ := Pca.Orbit.exists_mk T
  exact ⟨_, isAntipodalTri_ant hA hT⟩

/-- P2 (c): an antipodal flip of a great-pseudocircle arrangement is great. -/
theorem aflip_isGreat {A B : Arrangement n D} (hA : A.IsGreat) (h : A.AFlip B) : B.IsGreat :=
  AFlip.isGreat hA h

-- P3, Ringel's theorem: `Pca.Great.ringel` (`Pca/Great/Ringel.lean`).

/-- A one-curve extension of `A`, bundled with its dart type. -/
structure Extension (A : Arrangement n D) where
  D' : Type u
  [fin : Fintype D']
  [dec : DecidableEq D']
  A' : Arrangement (n + 1) D'
  ι : D → D'
  isDeletion : IsDeletion A' A ι

attribute [instance] Extension.fin Extension.dec

/-- **Levi's extension lemma** (P4, great-pseudocircle version): for a great-pseudocircle
arrangement and two cells there is a great-pseudocircle arrangement with one more curve that
passes through both cells and whose deletion gives back the original arrangement. Proof:
`levi_core` (`Pca/Great/GreatLevi.lean`), plan in `doc/pca/great.md` section 4. The signotope
version (BFS Theorem 1.2, rank 3) is `Pca.Great.Sig.levi`. -/
theorem levi (A : Arrangement n D) (hA : A.IsGreat)
    (f₁ f₂ : A.Cell) :
    ∃ X : Extension A, X.A'.IsGreat ∧ Passes X.A' X.ι f₁ ∧ Passes X.A' X.ι f₂ := by
  obtain ⟨B, hB, hD, h1, h2⟩ := levi_core hA f₁ f₂
  exact ⟨⟨D ⊕ (Fin (2 * n) × Fin 4), B, Sum.inl, hD⟩, hB, h1, h2⟩

end Pca.Great
