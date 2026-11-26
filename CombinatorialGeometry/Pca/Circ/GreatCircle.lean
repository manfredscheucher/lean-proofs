/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Circularizability: the Great-Circle Theorem and Corollary 9 (`doc/pca/circ.md`)

Source: arXiv:1712.02149 (v6).

* Theorem 1 (Great-Circle Theorem): "An arrangement of great-pseudocircles is circularizable
  (i.e., has a circle representation) if and only if it has a great-circle representation."
  Proof as in the paper: every triple is a Krupp, so its planes meet inside the sphere (Fact 1);
  scaling the planes by `1 - s`, `s ∈ [0, 1]`, no three circles ever pass through a point of the
  sphere (the triple points `(1 - s) P` stay inside), so the type is constant (C-D2), and at
  `s = 1` all planes pass through the origin.
* Corollary 9: "An arrangement of pseudolines is stretchable if and only if the corresponding
  arrangement of great-pseudocircles is circularizable." With `IsStretchable` (C-D3) this is
  Theorem 1.
-/
import Pca.Circ.Scaling

open Equiv Finset Matrix Set

namespace Pca.Circ

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- Inward scaling of a representation whose triples all meet inside: the type is constant. -/
theorem IsCircleRep.scale_of_meetInside {u : Fin n → V} {h : Fin n → ℝ} {pt : A.Crossing → V}
    {sgn : D → ℝ} (R : IsCircleRep A u h pt sgn)
    (hm : ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → MeetInside u h i j k) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ pt' : A.Crossing → V, IsCircleRep A u (fun i => t * h i) pt' sgn := by
  have := R.scale_in (c := fun s => 1 - s * (1 - t)) (by fun_prop) (by simp) ?_ ?_
  · simpa using this
  · intro s hs
    obtain ⟨a, b⟩ := hs
    constructor <;> nlinarith
  · intro s hs i j k hij hik hjk p hp hpi hpj hpk
    obtain ⟨hd, P, hPi, hPj, hPk, hPin⟩ := hm i j k hij hik hjk
    set c := 1 - s * (1 - t)
    have hc : 0 ≤ c ∧ c ≤ 1 := by obtain ⟨a, b⟩ := hs; constructor <;> nlinarith
    have e : p = c • P := eq_of_three_planes hd
      (by rw [hpi, dotProduct_smul, hPi, smul_eq_mul])
      (by rw [hpj, dotProduct_smul, hPj, smul_eq_mul])
      (by rw [hpk, dotProduct_smul, hPk, smul_eq_mul])
    rw [e, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at hp
    have h0 := dot_self_nonneg P
    have hcc : c * c ≤ 1 := by nlinarith
    have : c * (c * (P ⬝ᵥ P)) ≤ P ⬝ᵥ P := by
      rw [← mul_assoc]; exact mul_le_of_le_one_left h0 hcc
    linarith

/-- **Theorem 1 (Great-Circle Theorem).** An arrangement of great-pseudocircles is circularizable
iff it has a great-circle representation. -/
theorem greatCircle_theorem (hA : A.IsGreat) : Circularizable A ↔ Nonempty (GreatRep A) := by
  constructor
  · rintro ⟨R⟩
    have hm : ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → MeetInside R.u R.h i j k :=
      fun i j k hij hik hjk => (R.isRep.fact1 hij hik hjk).1 ((isGreat_iff A).1 hA i j k hij hik hjk)
    obtain ⟨pt', hR'⟩ := R.isRep.scale_of_meetInside hm 0 le_rfl zero_le_one
    exact ⟨⟨⟨R.u, fun i => 0 * R.h i, pt', R.sgn, hR'⟩, fun i => zero_mul _⟩⟩
  · rintro ⟨G⟩
    exact ⟨G.toCircleRep⟩

/-- **Corollary 9.** An arrangement of pseudolines is stretchable iff the corresponding arrangement
of great-pseudocircles is circularizable. -/
theorem stretchable_iff_circularizable (hA : A.IsGreat) : IsStretchable A ↔ Circularizable A :=
  ⟨fun h => (greatCircle_theorem hA).2 h.2, fun h => ⟨hA, (greatCircle_theorem hA).1 h⟩⟩

end Pca.Circ
