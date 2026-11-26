/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Gap lemma G1 (not in SH): a removal from a minimal counterexample is not finished (package A)

SH conclude from Lemma 3.3 that after a removal "some operation applies" (pp. 319, 322, 325).
Minimality only gives "not stuck" (finished or progress). Proof: if only nonintersecting rays
remain, every vertex above the sweep of `Γ` lies on `γ`; `γ` crossing a ray forms a triangle with
it (Lemma 3.6), `γ` crossing nothing is a ray (then `Γ` is finished), a hump (Lemma 3.6) or does
not meet the sweep (Lemma 3.4).
-/
import Pca.Sweep.L36
import Pca.Sweep.AB_Tri

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- After removing a curve from a minimal counterexample the sweep is not finished. -/
theorem MinCE.removal_not_terminal (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ)
    (X : Γ.Removal {γ}) : ¬ X.Γ'.Terminal := by
  classical
  intro hT
  obtain ⟨hHump, hTri⟩ := hΓ.lemma_3_6
  have hMeet : ∀ c, Γ.Present c → Γ.MeetsSweep c := fun c hc => hΓ.lemma_3_4 hc
  have hSR : Γ.S ∉ ({γ} : Finset (Fin n)) := fun h => hγ.1 (mem_singleton.1 h).symm
  -- a curve other than `γ` that meets the sweep meets it in `Γ − γ`, at a kept dart
  have hmeet' : ∀ c, c ≠ γ → Γ.Present c →
      ∃ x', X.Γ'.IsFinVertex x' ∧ c ∈ X.Γ'.curves x' := fun c hcγ hc =>
    X.r_meetsSweep_of hc.1 (fun h => hcγ (mem_singleton.1 h)) hSR (hMeet c hc)
  -- (1) every vertex above the sweep lies on `γ`
  have hab : ∀ x, Γ.IsAboveVertex x → Γ.OnCurve γ x := by
    intro x hx
    by_contra hxγ
    obtain ⟨a, ha, hA⟩ := hx.2
    have hax := ab_mem_darts ha
    have hcγ : Γ.curve a ≠ γ := fun h => hxγ (by rw [← hax, ← h]; exact ab_mem_curves_self a)
    have hK : Γ.rK {γ} a := by
      rintro ⟨c, hc, hcx⟩
      rw [mem_singleton.1 hc, hax] at hcx
      exact hxγ hcx
    obtain ⟨x', -, hx'c⟩ := hmeet' _ hcγ ⟨hA.1, a, rfl, hA⟩
    obtain ⟨e', he', he'c⟩ := mem_image.1 hx'c
    have he'c' : Γ.curve (X.ι e') = Γ.curve a := by rw [← X.isRemoval.curve]; exact he'c
    have hkeep : Γ.Keep {γ} a := by
      rcases Γ.isSConf.straight (X.ι e') a he'c' with h | h
      · obtain ⟨t, ht⟩ := h.exists_nat_pow_eq
        rw [← ht] at hK ⊢
        exact r_keep_pow (X.r_keep e') hK
      · obtain ⟨t, ht⟩ : ∃ t : ℕ, (Γ.straight ^ t) (X.ι e') = Γ.σ (Γ.σ a) :=
          h.exists_nat_pow_eq
        have hK' : Γ.rK {γ} ((Γ.straight ^ t) (X.ι e')) := by rw [ht, Γ.r_rK_σσ {γ} a]; exact hK
        have := r_keep_pow (X.r_keep e') hK'
        rwa [ht, r_keep_σ_iff, r_keep_σ_iff] at this
    obtain ⟨a', rfl⟩ := (X.isRemoval.range a).2 hkeep
    refine hT.1 (X.Γ'.crossingOf a') ⟨fun h => hx.1 ?_, a', ab_self_mem_darts a', ?_, ?_⟩
    · rw [← hax]; exact (X.r_onSweep _).1 h
    · rw [X.isRemoval.curve, X.isRemoval.S]; exact hA.1
    · exact (X.isRemoval.side a').trans hA.2
  -- (2) every other curve reaches the ∞-arc (it is a ray of `Γ − γ`)
  have hray : ∀ c, c ≠ γ → Γ.Present c → ∃ x, Γ.IsInfVertex x ∧ c ∈ Γ.curves x := by
    intro c hcγ hc
    obtain ⟨x', hx'f, hx'c⟩ := hmeet' c hcγ hc
    have hcS' : c ≠ X.Γ'.S := by rw [X.isRemoval.S]; exact hc.1
    obtain ⟨y', -, hy'c, hy'A, -, -⟩ := ab_up_dart hx'f.1 hx'c hcS'
    obtain ⟨-, x'', hinf, hx''⟩ := hT.2 c ⟨hcS', y', hy'c, hy'A⟩
    exact ⟨X.rΨ x'', (X.r_inf x'').1 hinf, by rw [← X.r_curves_Ψ]; exact hx''⟩
  -- (3) there is a vertex above the sweep (else `Γ` is finished)
  have hex : ∃ x, Γ.IsAboveVertex x := by
    by_contra hno
    push Not at hno
    refine hΓ.1.1 ⟨hno, fun c hc => ?_⟩
    obtain ⟨k, hkf, hkc⟩ := hMeet c hc
    obtain ⟨y, hyx, hyc, hyA, -, -⟩ := ab_up_dart hkf.1 hkc hc.1
    have hqS : Γ.OnSweep (Γ.crossingOf (Γ.α y)) := by
      by_contra h; exact hno _ (ab_aboveVertex_of (ab_above_α hyA) h)
    have hqc : c ∈ Γ.curves (Γ.crossingOf (Γ.α y)) := by
      rw [← hyc, ← j_curve_α Γ y]; exact ab_mem_curves_self _
    have hqinf : Γ.IsInfVertex (Γ.crossingOf (Γ.α y)) := by
      by_contra h
      exact hHump y ⟨hyA, by rw [hyx]; exact hkf, hqS, h⟩
    refine ⟨?_, _, hqinf, hqc⟩
    set F := univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∧ Γ.OnCurve c x)
    set G := univ.filter (fun x : Γ.Crossing => Γ.curves x = {c, Γ.S})
    change F.card = 1
    have hkF : k ∈ F := mem_filter.2 ⟨mem_univ _, hkf, hkc⟩
    have hFG : F ⊆ G.erase (Γ.crossingOf (Γ.α y)) := by
      intro x hx
      obtain ⟨hxf, hxc⟩ := (mem_filter.1 hx).2
      refine mem_erase.2 ⟨fun e => hxf.2 (by rw [e]; exact hqinf), ?_⟩
      exact mem_filter.2 ⟨mem_univ _, no_mem_curves hxf.1 hxc hc.1⟩
    have hqG : Γ.crossingOf (Γ.α y) ∈ G := mem_filter.2 ⟨mem_univ _, no_mem_curves hqS hqc hc.1⟩
    have hG : G.card = 2 := by
      have hc2 : G.card = 0 ∨ G.card = 2 := by convert card_sweep_crossings c hc.1
      rcases hc2 with h | h
      · exact absurd (card_pos.2 ⟨_, hqG⟩) (by omega)
      · exact h
    have h1 := card_le_card hFG
    rw [card_erase_of_mem hqG, hG] at h1
    have h2 := card_pos.2 ⟨k, hkF⟩
    omega
  -- (4) a triangle whose first curve is not `γ` reaches the ∞-arc, so it is convex
  have hTri' : ∀ a b, Γ.IsTri a b → Γ.curve a ≠ γ → False := by
    intro a b hT haγ
    rcases ab_tri_convex hT (Or.inl rfl) (hray _ haγ ⟨hT.1.1, a, rfl, hT.1⟩) with h | h
    · exact hTri a b h
    · exact hTri b a h
  exact ab_g1_core hTri' hMeet hγ hab hex hray

end SConf

end Pca.Sweep
