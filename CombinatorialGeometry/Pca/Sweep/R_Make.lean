/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package R (removal), the sweep configuration of the removal

Helper file for `Pca/Sweep/Removal.lean`: the axioms of a sweep configuration for the removal
(`r_isSConf`), the configuration `rConf`, and the removal itself (`r_exists_removal`).
-/
import Pca.Sweep.R_Arc

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}


namespace SConf

variable {Γ : SConf n D} {R : Finset (Fin n)}

theorem r_isSConf : IsSConf n (Γ.rσ R) (Γ.rα R) (fun d => Γ.curve d.1) Γ.S where
  card_crossing d := by
    rw [← card_map ⟨Subtype.val, r_hinj⟩, r_map_orbitFinset_σ]
    exact Γ.isSConf.card_crossing d.1
  α_ne := r_rα_ne
  α_α := r_rα_α
  curve_α d := r_curve_hit d.2.1
  curve_σ d := Γ.isSConf.curve_σ d.1
  curve_σσ d := Γ.isSConf.curve_σσ d.1
  straight d e h := r_straight' d e h
  two_int c c' hne := by
    refine le_trans ?_ (Γ.isSConf.two_int c c' hne)
    refine card_le_card_of_injOn rCr ?_ (fun a _ b _ h => r_rCr_inj h)
    intro x hx
    obtain ⟨d, rfl⟩ := x.exists_mk
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    rw [r_rCr_mk]
    rw [r_crossingCurves] at hx
    exact hx
  connected := r_connected
  euler hne := by have := hne; exact r_euler
  S_mem hne := by
    obtain ⟨d⟩ := hne
    obtain ⟨e, he, hde⟩ := d.2.2
    exact ⟨⟨e, r_keep_of_eqvGen d.2 hde⟩, he⟩

theorem r_isSide (hS : Γ.S ∉ R) (y : Γ.RD R) :
    rCellFun Γ.side (r_side_R hS) (Orbit.mk _ y) +
        rCellFun Γ.side (r_side_R hS) (Orbit.mk _ (Γ.rα R y)) =
      if Γ.curve y.1 = Γ.S then 1 else 0 := by
  refine (r_cellFun_add (r_side_R hS) y).trans ?_
  have := Γ.isSide ((Γ.straight ^ Γ.rJ R y.1) y.1)
  rw [r_curve_pow] at this
  exact this

/-- The removal as a sweep configuration, with a given ∞-arc. -/
noncomputable def rConf (hS : Γ.S ∉ R) (zs : Option (Γ.RD R)) (L : ℕ)
    (h1 : Nonempty (Γ.RD R) → zs.isSome)
    (h2 : ∀ z ∈ zs, L ≤ period (straightPerm (Γ.rσ R) (Γ.rα R)) z)
    (h3 : ∀ d ∈ arcOf (Γ.rσ R) (Γ.rα R) zs L, Γ.curve d.1 = Γ.S ∧
      rCellFun Γ.side (r_side_R hS) (Orbit.mk _ (Γ.rα R d)) = 1) : SConf n (Γ.RD R) where
  σ := Γ.rσ R
  α := Γ.rα R
  curve d := Γ.curve d.1
  S := Γ.S
  isSConf := r_isSConf
  side := rCellFun Γ.side (r_side_R hS)
  isSide := r_isSide hS
  infStart := zs
  infLen := L
  infStart_isSome := h1
  infLen_le := h2
  infArc_sweep := h3

theorem r_isRemoval (hS : Γ.S ∉ R) (zs : Option (Γ.RD R)) (L : ℕ) (h1) (h2) (h3)
    (h4 : ∀ z' ∈ zs, ∃ z ∈ Γ.infStart, Γ.Piece R z'.1 z)
    (h5 : ∀ d', (rConf hS zs L h1 h2 h3).IsInfVertex ((rConf hS zs L h1 h2 h3).crossingOf d') ↔
      Γ.IsInfVertex (Γ.crossingOf d'.1)) :
    Γ.IsRemoval R (rConf hS zs L h1 h2 h3) Subtype.val where
  inj := Subtype.val_injective
  range d := ⟨fun ⟨d', h⟩ => h ▸ d'.2, fun h => ⟨⟨d, h⟩, rfl⟩⟩
  curve _ := rfl
  S := rfl
  σ _ := rfl
  α d := ⟨_, r_piece_J d.2.1, r_K_end d.2.1, r_hit_eq d.2.1⟩
  side _ := rfl
  infStart := h4
  infVertex := h5

theorem r_exists_removal (hS : Γ.S ∉ R) : Nonempty (Γ.Removal R) := by
  by_cases hne : Nonempty (Γ.RD R)
  · refine ⟨⟨Γ.RD R, rConf hS (some (Γ.rOwn R)) (Γ.rL R) (fun _ => rfl) ?_ ?_, Subtype.val,
      r_isRemoval hS _ _ _ _ _ ?_ ?_⟩⟩
    · intro z hz
      obtain rfl : Γ.rOwn R = z := Option.some_inj.1 hz
      exact r_rL_le
    · intro d hd
      unfold arcOf at hd
      obtain ⟨i, -, rfl⟩ := mem_image.1 hd
      exact r_arc_sweep i
    · intro z hz
      obtain rfl : Γ.rOwn R = z := Option.some_inj.1 hz
      exact ⟨Γ.rZ R, r_rZ_eq, r_piece_own⟩
    · intro d
      rw [← r_infVertex]
      unfold IsInfVertex
      constructor
      · rintro ⟨z, hz, i, hi, he⟩
        obtain rfl : Γ.rOwn R = z := Option.some_inj.1 hz
        exact ⟨i, hi, (congrArg rCr he).trans (r_rCr_mk d)⟩
      · rintro ⟨i, hi, he⟩
        exact ⟨_, rfl, i, hi, r_rCr_inj (he.trans (r_rCr_mk d).symm)⟩
  · refine ⟨⟨Γ.RD R, rConf hS none 0 (fun h => absurd h hne) (fun z hz => by cases hz)
      (fun d hd => by simp [arcOf] at hd), Subtype.val,
      r_isRemoval hS _ _ _ _ _ (fun z hz => by cases hz) (fun d => absurd ⟨d⟩ hne)⟩⟩

end SConf

end Pca.Sweep
