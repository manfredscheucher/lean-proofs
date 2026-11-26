/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package M, helpers: the flip passes the apex

For any sweep configuration `Γ'` that is the triangle flip of `Γ` at the empty triangle above
the finite edge of `d` (stated with the data of `IsTriFlip`, unbundled), the vertices on the
sweep stay, the ∞-arc vertices stay, and the apex `v` is the only vertex above the sweep that is
lost (`m_flip_numVertices`).
-/
import Pca.Sweep.M_FlipConf

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {d : D} (hd : Γ.EmptyTriAt d)
include hd

/-- An arc dart that is followed by an arc dart does not end at a corner of the triangle. -/
theorem m_arc_not_corner {a : D} (ha : a ∈ Γ.infArc) (hs : Γ.straight a ∈ Γ.infArc) :
    ¬ Γ.MCorner (Γ.α d) (Γ.α a) := by
  intro hc
  obtain ⟨haS, hup⟩ := Γ.infArc_sweep a ha
  have hne : a ≠ d := fun h => hd.1.2 (h ▸ ha)
  have h := m_sweep_corner hd haS hup hne hc
  have : Γ.straight a = d := by
    rw [m_straight_apply, h, Γ.m_σσ_straight, m_α_α]
  exact hd.1.2 (this ▸ hs)

/-- The apex `v = crossingOf (φ² (α d))` is not on the sweep. -/
theorem m_apex_not_onSweep : ¬ Γ.OnSweep (Γ.crossingOf (Γ.φ (Γ.φ (Γ.α d)))) := by
  have hT := m_mTri hd
  intro h
  obtain ⟨z, hz, hzS⟩ := mem_image.1 h
  have hz' : Γ.crossingOf z = Γ.crossingOf (Γ.φ (Γ.φ (Γ.α d))) := by
    rw [← Orbit.mem_darts.1 hz]; rfl
  exact m_tri_curve_ne_at_φφ hT rfl hz' (hzS.trans hT.curve_t.symm)

theorem m_apex_above : Γ.IsAboveVertex (Γ.crossingOf (Γ.φ (Γ.φ (Γ.α d)))) := by
  have hT := m_mTri hd
  refine ⟨m_apex_not_onSweep hd, Γ.φ (Γ.φ (Γ.α d)), Orbit.mem_darts.2 rfl, ?_, ?_⟩
  · intro h
    exact m_tri_curve_φφ_ne hT rfl (h.trans hT.curve_t.symm)
  · show Γ.side (Γ.cellOf (Γ.φ (Γ.φ (Γ.α d)))) = 1
    rw [m_tri_φφ rfl]; exact m_side_upper hd

open Classical in
/-- **The flip passes the apex** (unbundled form of `IsTriFlip.numVertices`). -/
theorem m_flip_numVertices (Γ' : SConf n D) (hσ : Γ'.σ = Γ.σ) (hcurve : Γ'.curve = Γ.curve)
    (hS : Γ'.S = Γ.S) (hα : ∀ y, Γ'.α y = mα (m_mTri hd) y)
    (hinf : Γ'.infStart = Γ.infStart.map (mρ (m_mTri hd)) ∧ Γ'.infLen = Γ.infLen)
    (hside_tri : Γ'.side (Orbit.mk (Γ'.σ * Γ'.α) (Γ.σ (Γ.σ (Γ.α d)))) = 0)
    (hside_far : ∀ y, ¬ Γ.MCorner (Γ.α d) y →
      Γ'.side (Orbit.mk (Γ'.σ * Γ'.α) y) = Γ.side (Γ.cellOf y)) :
    Γ'.numVertices + 1 = Γ.numVertices := by
  have hT := m_mTri hd
  obtain ⟨σ', α', curve', S', hconf, side', hside, start', len', hsome, hle, hsweep⟩ := Γ'
  dsimp only at hσ hcurve hS hα hinf hside_tri hside_far
  obtain ⟨hinf1, hinf2⟩ := hinf
  subst hσ hcurve hS hinf1 hinf2
  obtain rfl : α' = mα hT := Equiv.ext hα
  set Γ' : SConf n D := ⟨Γ.σ, mα hT, Γ.curve, Γ.S, hconf, side', hside,
    Γ.infStart.map (mρ hT), Γ.infLen, hsome, hle, hsweep⟩ with hΓ'
  set v := Γ.crossingOf (Γ.φ (Γ.φ (Γ.α d))) with hv
  -- the side after the flip
  have hside'_eq : ∀ y, Γ'.mSide y = side' (Orbit.mk _ y) := fun _ => rfl
  -- crossings with `S` and ∞-arc vertices do not change
  have hOn : ∀ x : Γ.Crossing, Γ'.OnSweep x ↔ Γ.OnSweep x := fun _ => Iff.rfl
  have hkey : ∀ z ∈ Γ.infStart, ∀ i < Γ.infLen,
      Γ.crossingOf (mα hT ((Γ'.straight ^ i) (mρ hT z))) =
        Γ.crossingOf (Γ.α ((Γ.straight ^ i) z)) := by
    intro z hz i hi
    have hmem : ∀ j ≤ Γ.infLen, (Γ.straight ^ j) z ∈ Γ.infArc := by
      intro j hj
      unfold infArc
      rw [Option.mem_def.1 hz]
      simp only [arcOf, Option.elim_some, mem_image, mem_range]
      exact ⟨j, by omega, rfl⟩
    have hs : Γ.straight ((Γ.straight ^ i) z) ∈ Γ.infArc := by
      rw [← Perm.mul_apply, ← pow_succ']; exact hmem (i + 1) hi
    rw [show (Γ'.straight ^ i) (mρ hT z) = mρ hT ((Γ.straight ^ i) z) from
      m_flip_straight_pow hd z i, mα_apply, mρ_mρ,
      mρ_of_not_corner hT (m_arc_not_corner hd (hmem i hi.le) hs)]
  have hInf : ∀ x : Γ.Crossing, Γ'.IsInfVertex x ↔ Γ.IsInfVertex x := by
    intro x
    constructor
    · rintro ⟨z', hz', i, hi, hx⟩
      obtain ⟨z, hz, rfl⟩ := Option.mem_map.1 hz'
      exact ⟨z, hz, i, hi, (hkey z hz i hi).symm.trans hx⟩
    · rintro ⟨z, hz, i, hi, hx⟩
      exact ⟨mρ hT z, Option.mem_map.2 ⟨z, hz, rfl⟩, i, hi, (hkey z hz i hi).trans hx⟩
  have hFin : ∀ x : Γ.Crossing, Γ'.IsFinVertex x ↔ Γ.IsFinVertex x := fun x => by
    rw [IsFinVertex, IsFinVertex, hOn, hInf]
  -- above the sweep: unchanged away from the apex
  have hAbove : ∀ x : Γ.Crossing, x ≠ v → (Γ'.IsAboveVertex x ↔ Γ.IsAboveVertex x) := by
    intro x hxv
    obtain ⟨y0, rfl⟩ := x.exists_mk
    by_cases hc : Γ.MCorner (Γ.α d) y0
    · -- a corner other than the apex is on the sweep
      have hon : Γ.OnSweep (Orbit.mk Γ.σ y0) := by
        obtain ⟨e, he, hey⟩ := hc
        rcases (m_tri_mem_iff hT rfl).1 he with rfl | rfl | rfl
        · exact mem_image.2 ⟨Γ.α d, Orbit.mem_darts.2 hey, hT.curve_t⟩
        · refine mem_image.2 ⟨Γ.α (Γ.α d), Orbit.mem_darts.2 ?_, ?_⟩
          · show Γ.crossingOf (Γ.α (Γ.α d)) = Γ.crossingOf y0
            rw [← hey]; exact (Γ.m_crossingOf_φ _).symm
          · rw [m_curve_α]; exact hT.curve_t
        · exact absurd hey.symm hxv
      exact ⟨fun h => absurd ((hOn _).2 hon) h.1, fun h => absurd hon h.1⟩
    · have hfar : ∀ y ∈ (Orbit.mk Γ.σ y0).darts, ¬ Γ.MCorner (Γ.α d) y := by
        intro y hy hcy
        apply hc
        obtain ⟨e, he, hey⟩ := hcy
        exact ⟨e, he, hey.trans (Orbit.mem_darts.1 hy)⟩
      constructor
      · rintro ⟨hon, y, hy, hyS, hyU⟩
        refine ⟨fun h => hon ((hOn _).2 h), y, hy, hyS, ?_⟩
        have := hside_far y (hfar y hy)
        show Γ.side (Γ.cellOf y) = 1
        rw [← this]; exact hyU
      · rintro ⟨hon, y, hy, hyS, hyU⟩
        refine ⟨fun h => hon ((hOn _).1 h), y, hy, hyS, ?_⟩
        show side' (Orbit.mk _ y) = 1
        rw [hside_far y (hfar y hy)]; exact hyU
  -- the apex is no longer above
  have hv' : ¬ Γ'.IsAboveVertex v := by
    rintro ⟨-, y, hy, hyS, hyU⟩
    have hyv : Γ.crossingOf y = v := Orbit.mem_darts.1 hy
    -- `σ² (φ² t)` is a dart of the flipped triangle
    set w := Γ.σ (Γ.σ (Γ.φ (Γ.φ (Γ.α d)))) with hw
    have hcell : Γ'.cellOf w = Γ'.cellOf (Γ.σ (Γ.σ (Γ.α d))) := by
      have h1 : Γ'.φ (Γ.σ (Γ.σ (Γ.α d))) = Γ.σ (Γ.σ (Γ.φ (Γ.α d))) := m_φ'_σσ hT rfl
      have h2 : Γ'.φ (Γ.σ (Γ.σ (Γ.φ (Γ.α d)))) = w := m_φ'_σσ hT (m_tri_φ rfl)
      rw [← h2, Γ'.m_cellOf_φ, ← h1, Γ'.m_cellOf_φ]
    have hw0 : Γ'.mSide w = 0 := by
      show Γ'.side (Γ'.cellOf w) = 0
      rw [hcell]; exact hside_tri
    have hnS : ∀ z, Γ.crossingOf z = v → Γ'.mS z = 0 := by
      intro z hz
      rw [mS, if_neg]
      intro h
      exact m_tri_curve_ne_at_φφ hT rfl hz (h.trans hT.curve_t.symm)
    have hwv : Γ.crossingOf w = v := Γ.m_crossingOf_σσ _
    have h0 := (Γ.m_crossingOf_eq_iff).1 (hwv.trans hyv.symm)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
    have hσw : Γ'.mSide (Γ.σ w) = 0 := by
      rw [show Γ.σ w = Γ'.σ w from rfl, Γ'.m_side_σ, hw0, hnS w hwv]; rfl
    have hσσw : Γ'.mSide (Γ.σ (Γ.σ w)) = 0 := by
      rw [show Γ.σ (Γ.σ w) = Γ'.σ (Γ.σ w) from rfl, Γ'.m_side_σ, hσw,
        hnS _ ((Γ.m_crossingOf_σ w).trans hwv)]; rfl
    have hσσσw : Γ'.mSide (Γ.σ (Γ.σ (Γ.σ w))) = 0 := by
      rw [show Γ.σ (Γ.σ (Γ.σ w)) = Γ'.σ (Γ.σ (Γ.σ w)) from rfl, Γ'.m_side_σ, hσσw,
        hnS _ ((Γ.m_crossingOf_σσ w).trans hwv)]; rfl
    have hy0 : Γ'.mSide y = 0 := by
      rcases h0 with h | h | h | h <;> rw [h]
      · exact hw0
      · exact hσw
      · exact hσσw
      · exact hσσσw
    have : Γ'.mSide y = 1 := hyU
    rw [hy0] at this
    exact absurd this (by decide)
  -- count
  have hset : univ.filter (fun x : Γ'.Crossing => Γ'.IsFinVertex x ∨ Γ'.IsAboveVertex x) =
      (univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∨ Γ.IsAboveVertex x)).erase v := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    by_cases hxv : x = v
    · subst hxv
      simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_or]
      exact ⟨fun h => m_apex_not_onSweep hd ((hOn _).1 h.1), hv'⟩
    · rw [hFin, hAbove x hxv]
      exact ⟨fun h => ⟨hxv, h⟩, fun h => h.2⟩
  have hmem : v ∈ univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∨ Γ.IsAboveVertex x) := by
    simp only [mem_filter, mem_univ, true_and]
    exact Or.inr (m_apex_above hd)
  unfold numVertices
  rw [hset, card_erase_of_mem hmem]
  have := card_pos.2 ⟨v, hmem⟩
  omega

end SConf

end Pca.Sweep
