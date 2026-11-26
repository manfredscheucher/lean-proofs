/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Inserting a new curve along a walk: the arrangement (`doc/pca/great.md` 4.1)

`InsWalk.ins`: the new arrangement with `n + 1` curves; deleting the new curve gives back `A`
(`ins_isDeletion`), and the new curve passes every visited cell (`ins_passes`).
-/
import Pca.Great.Ins_Cell

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ}

namespace InsWalk

variable {A : Arrangement n D} {K : ℕ} (W : InsWalk A K)

theorem euler' : (Fintype.card (Orbit W.σ') : ℤ) - Fintype.card (Orbit W.α') +
    Fintype.card (Orbit (W.σ' * W.α')) = 2 := by
  have hle := MapFacts.euler_le_two (σ := W.σ') (α := W.α') (fun x => W.αfun_αfun x) W.α'_ne W.conn
  have hA := A.isArrangement.euler
  have hF := W.card_F'
  have hV := W.card_V'
  have hE := W.card_E'
  change (Fintype.card (Orbit A.σ) : ℤ) - Fintype.card (Orbit A.α) +
    Fintype.card (Orbit A.φ) = 2 at hA
  change Fintype.card (Orbit A.φ) + K ≤ Fintype.card (Orbit (W.σ' * W.α')) at hF
  push_cast [hV, hE] at hle ⊢
  have : ((Fintype.card (Orbit A.φ) : ℕ) : ℤ) + K ≤ Fintype.card (Orbit (W.σ' * W.α')) := by
    exact_mod_cast hF
  omega

theorem isArrangement' : IsArrangement (n + 1) W.σ' W.α' W.curve' where
  card_crossing := W.card_crossing'
  α_ne := W.α'_ne
  α_α x := W.αfun_αfun x
  curve_α := W.curve'_α
  curve_σ := W.curve'_σ
  curve_σσ := W.curve'_σσ
  straight := W.straight'
  intersecting := W.intersecting'
  euler := W.euler'

/-- **Insertion** of a new curve along the walk `W`. -/
noncomputable def ins : Arrangement (n + 1) (D ⊕ (Fin K × Fin 4)) :=
  ⟨W.σ', W.α', W.curve', W.isArrangement'⟩

theorem ins_σ : W.ins.σ = W.σ' := rfl
theorem ins_α : W.ins.α = W.α' := rfl
theorem ins_curve : W.ins.curve = W.curve' := rfl
theorem ins_straight : W.ins.straight = W.st := rfl

theorem last_mem_inr (i : Fin K) (r : Fin 4) :
    Fin.last n ∈ Arrangement.Crossing.curves W.ins (W.ins.crossingOf (.inr (i, r))) := by
  show Fin.last n ∈ crossingCurves W.σ' W.curve' (Orbit.mk W.σ' (.inr (i, r)))
  rw [W.crossCurves_inr]; simp

theorem last_not_mem_inl (d : D) :
    Fin.last n ∉ Arrangement.Crossing.curves W.ins (W.ins.crossingOf (.inl d)) := by
  show Fin.last n ∉ crossingCurves W.σ' W.curve' (Orbit.mk W.σ' (.inl d))
  rw [W.crossCurves_inl]
  simp only [mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
  exact fun a _ => Fin.castSucc_ne_last a

theorem ins_isDeletion : IsDeletion W.ins A Sum.inl where
  inj := Sum.inl_injective
  range y := by
    rcases y with d | ⟨i, r⟩
    · exact ⟨fun _ => W.last_not_mem_inl d, fun _ => ⟨d, rfl⟩⟩
    · exact ⟨fun ⟨d, hd⟩ => absurd hd (by simp), fun h => absurd (W.last_mem_inr i r) h⟩
  curve _ := rfl
  σ _ := rfl
  α d := by
    by_cases h1 : ∃ i, W.t i = d
    · obtain ⟨i, rfl⟩ := h1
      refine ⟨1, fun j hj => ?_, ?_⟩
      · obtain rfl : j = 0 := by omega
        show Fin.last n ∈ Arrangement.Crossing.curves W.ins
          (W.ins.crossingOf (W.αfun (.inl (W.t i))))
        rw [W.αfun_t]; exact W.last_mem_inr i 0
      · show _ = W.αfun (W.st (.inl (W.t i)))
        rw [W.st_t, W.αfun_v]
    by_cases h2 : ∃ i, A.α (W.t i) = d
    · obtain ⟨i, rfl⟩ := h2
      refine ⟨1, fun j hj => ?_, ?_⟩
      · obtain rfl : j = 0 := by omega
        show Fin.last n ∈ Arrangement.Crossing.curves W.ins
          (W.ins.crossingOf (W.αfun (.inl (A.α (W.t i)))))
        rw [W.αfun_αt]; exact W.last_mem_inr i 1
      · show _ = W.αfun (W.st (.inl (A.α (W.t i))))
        rw [W.st_αt, W.αfun_u, A.isArrangement.α_α]
    push Not at h1 h2
    exact ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _), (W.α'_free ⟨h1, h2⟩).symm⟩

theorem ins_passes (i : Fin K) : Passes W.ins Sum.inl (A.cellOf (W.t i)) := by
  refine ⟨W.t i, Orbit.mem_darts.2 rfl, ?_⟩
  show Fin.last n ∈ Arrangement.Crossing.curves W.ins (W.ins.crossingOf (W.αfun (.inl (W.t i))))
  rw [W.αfun_t]; exact W.last_mem_inr i 0

end InsWalk

end Pca.Great
