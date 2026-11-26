/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Reflex triangles, case (ii): directing the last vertex to infinity

SH Lemma 3.9, Case 1 (p. 321): "Now we can direct `γ(j)` to infinity without causing any more
intersections or allowing `c` to make progress ... But this gives a smaller unsweepable
arrangement, violating the minimality of `Γ`." Here in the form needed for reflex triangles
(`doc/pca/sweep.md`, case (ii)): if the ∞-arc is one segment (`infLen = 0`) and some vertex lies
above the sweep, extending the ∞-arc by the last finite edge (`x_redir`, the construction of
`exists_redirect` as a definition, so that all other fields stay definitionally equal) gives a
smaller stuck configuration. The curve through the last vertex still meets the sweep: it crosses
`S` twice, and with `infLen = 0` no crossing lies inside the ∞-arc.
-/
import Pca.Sweep.Jordan
import Pca.Sweep.NO_Sweep

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

variable (Γ) in
/-- `exists_redirect` as a definition: the ∞-arc extended by the last finite edge `d`. -/
def x_redir (d : D) (hd : Γ.IsFinSeg d) (hlast : Γ.straight d ∈ Γ.infArc) : SConf n D :=
  { Γ with
    infStart := some d
    infLen := Γ.infLen + 1
    infStart_isSome := fun _ => rfl
    infLen_le := by
      obtain ⟨⟨hdS, hdUp⟩, hdA⟩ := hd
      obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z := by
        cases h : Γ.infStart with
        | none => simp [infArc, arcOf, h] at hlast
        | some z => exact ⟨z, rfl⟩
      have hmem : ∀ e, e ∈ Γ.infArc ↔ ∃ i ≤ Γ.infLen, (Γ.straight ^ i) z = e := by
        intro e
        simp [infArc, arcOf, hz, straight]
      have hzd : z = Γ.straight d := by
        obtain ⟨i, hi, hie⟩ := (hmem _).1 hlast
        rcases i with _ | i
        · simpa using hie
        · exfalso; apply hdA
          refine (hmem _).2 ⟨i, by omega, ?_⟩
          apply Γ.straight.injective
          rw [← hie, pow_succ', Perm.mul_apply]
      have hpow : ∀ i, (Γ.straight ^ (i + 1)) d = (Γ.straight ^ i) z := by
        intro i; rw [hzd, pow_succ, Perm.mul_apply]
      intro z' hz'
      obtain rfl : z' = d := (Option.mem_some_iff.1 hz').symm
      have hp := period_pos (straightPerm Γ.σ Γ.α) z'
      by_contra hk
      apply hdA
      refine (hmem _).2 ⟨period (straightPerm Γ.σ Γ.α) z' - 1, by omega, ?_⟩
      rw [← hpow, Nat.sub_add_cancel hp]
      change (straightPerm Γ.σ Γ.α ^ period (straightPerm Γ.σ Γ.α) z') z' = z'
      rw [Perm.coe_pow]; exact iterate_period _ _
    infArc_sweep := by
      obtain ⟨⟨hdS, hdUp⟩, hdA⟩ := hd
      obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z := by
        cases h : Γ.infStart with
        | none => simp [infArc, arcOf, h] at hlast
        | some z => exact ⟨z, rfl⟩
      have hmem : ∀ e, e ∈ Γ.infArc ↔ ∃ i ≤ Γ.infLen, (Γ.straight ^ i) z = e := by
        intro e
        simp [infArc, arcOf, hz, straight]
      have hzd : z = Γ.straight d := by
        obtain ⟨i, hi, hie⟩ := (hmem _).1 hlast
        rcases i with _ | i
        · simpa using hie
        · exfalso; apply hdA
          refine (hmem _).2 ⟨i, by omega, ?_⟩
          apply Γ.straight.injective
          rw [← hie, pow_succ', Perm.mul_apply]
      have hpow : ∀ i, (Γ.straight ^ (i + 1)) d = (Γ.straight ^ i) z := by
        intro i; rw [hzd, pow_succ, Perm.mul_apply]
      intro e he
      simp only [arcOf, Option.elim, mem_image, mem_range] at he
      obtain ⟨j, hj, rfl⟩ := he
      rcases j with _ | j
      · exact ⟨hdS, hdUp⟩
      · have h := Γ.infArc_sweep ((Γ.straight ^ j) z) ((hmem _).2 ⟨j, by omega, rfl⟩)
        rw [← hpow] at h
        exact h }

/-- **Case (ii)**: with a one-segment ∞-arc and a vertex above the sweep, a minimal counterexample
is contradicted by directing the last vertex `l` (position `tl + 1`, the last one) to infinity. -/
theorem x_redirect_false (hΓ : Γ.MinCE) {z : D} (hz : Γ.infStart = some z)
    (h0 : Γ.infLen = 0) {tl : ℕ} (htl : tl + 1 = period Γ.straight z) (h1 : 0 < tl)
    (habove : ∃ x, Γ.IsAboveVertex x) : False := by
  classical
  set d := Γ.noC z (tl - 1) with hd_def
  have hd : Γ.IsFinSeg d := ⟨no_noC_sweep hz _, fun hm => by
    have := (no_noC_arc hz (by omega)).1 hm
    omega⟩
  have hsd : Γ.straight d = Γ.noC z tl := by
    rw [hd_def, no_noC_straight, Nat.sub_add_cancel h1]
  have hlast : Γ.straight d ∈ Γ.infArc := by
    rw [hsd]; exact (no_noC_arc hz (by omega)).2 (by omega)
  set Γ' := Γ.x_redir d hd hlast with hΓ'
  set m := Γ.crossingOf (Γ.noC z tl) with hm_def
  have hmα : Γ.crossingOf (Γ.α d) = m := by rw [← no_crossingOf_α_straight, hsd]
  -- vertices of `Γ'`
  have hinf : ∀ x, ¬ Γ.IsInfVertex x := by
    rintro x ⟨z', -, i, hi, -⟩
    omega
  have hinf' : ∀ x : Γ.Crossing, Γ'.IsInfVertex x ↔ x = m := by
    intro x
    constructor
    · rintro ⟨z', hz', i, hi, hx⟩
      obtain rfl : z' = d := (Option.mem_some_iff.1 hz').symm
      have hi0 : i = 0 := by
        have : Γ'.infLen = Γ.infLen + 1 := rfl
        omega
      subst hi0
      rw [← hx, ← hmα]
      rfl
    · rintro rfl
      exact ⟨d, rfl, 0, by show 0 < Γ.infLen + 1; omega, hmα⟩
  have hfin' : ∀ x : Γ.Crossing, Γ'.IsFinVertex x ↔ Γ.OnSweep x ∧ x ≠ m := by
    intro x
    show Γ.OnSweep x ∧ ¬ Γ'.IsInfVertex x ↔ _
    rw [hinf' x]
  have hfin : ∀ x : Γ.Crossing, Γ.IsFinVertex x ↔ Γ.OnSweep x := fun x =>
    ⟨fun h => h.1, fun h => ⟨h, hinf x⟩⟩
  have hmS : Γ.OnSweep m := no_S_mem_noC hz tl
  -- smaller
  have hlt : Γ'.numVertices < Γ.numVertices := by
    unfold numVertices
    apply card_lt_card
    refine ⟨fun x hx => ?_, fun hsub => ?_⟩
    · have hx2 := (mem_filter.1 hx).2
      refine (mem_filter (s := (univ : Finset Γ.Crossing))).2 ⟨mem_univ _, ?_⟩
      rcases hx2 with h | h
      · exact Or.inl ((hfin x).2 ((hfin' x).1 h).1)
      · exact Or.inr h
    · have hm : m ∈ univ.filter (fun x : Γ.Crossing => Γ.IsFinVertex x ∨ Γ.IsAboveVertex x) :=
        mem_filter.2 ⟨mem_univ _, Or.inl ((hfin m).2 hmS)⟩
      have := (mem_filter.1 (hsub hm)).2
      rcases this with h | h
      · exact ((hfin' m).1 h).2 rfl
      · exact h.1 hmS
  -- stuck
  have harc : ∀ e, e ∈ Γ.infArc → e ∈ Γ'.infArc := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := (no_mem_infArc hz).1 he
    have hi0 : i = 0 := by omega
    subst hi0
    have hz' : Γ'.infStart = some d := rfl
    refine (no_mem_infArc hz').2 ⟨1, by show 1 ≤ Γ.infLen + 1; omega, ?_⟩
    have hz1 : z = Γ.straight d := by
      obtain ⟨i, hi, hie⟩ := (no_mem_infArc hz).1 hlast
      have hi0 : i = 0 := by omega
      subst hi0
      exact hie
    rw [pow_one, pow_zero, Perm.one_apply, hz1]
    rfl
  have hstuck : Γ'.Stuck := by
    refine ⟨fun hT => ?_, ?_⟩
    · obtain ⟨x, hx⟩ := habove
      exact hT.1 x hx
    rintro (⟨e, he, hsz⟩ | ⟨e, he, hsz⟩ | ⟨d1, e, hd1, he, hcS, hnm⟩)
    · exact hΓ.1.2 (Or.inl ⟨e, ⟨he.1, fun h => he.2 (harc e h)⟩, hsz⟩)
    · exact hΓ.1.2 (Or.inr (Or.inl ⟨e, ⟨he.1, fun h => he.2 (harc e h)⟩, hsz⟩))
    · by_cases hms : Γ.MeetsSweep (Γ.curve e)
      · obtain ⟨x, hxf, hxo⟩ := hms
        by_cases hxm : x = m
        · subst hxm
          -- the curve through the last vertex crosses `S` once more
          set B := Γ.curve e
          have hBS : B ≠ Γ.S := hcS
          have hmB : Γ.curves m = {B, Γ.S} := by
            have hc := hxo
            unfold OnCurve at hc
            rw [hm_def, j_curves_crossingOf, (no_noC_sweep hz tl).1, mem_insert,
              mem_singleton] at hc
            rw [hm_def, j_curves_crossingOf, (no_noC_sweep hz tl).1]
            rcases hc with hc | hc
            · exact absurd hc hBS
            · rw [hc, pair_comm]
          set F := univ.filter (fun x : Γ.Crossing => Γ.curves x = {B, Γ.S})
          have hmF : m ∈ F := mem_filter.2 ⟨mem_univ _, hmB⟩
          have hF2 : F.card = 2 := by
            have hpos : 0 < F.card := card_pos.2 ⟨m, hmF⟩
            rcases card_sweep_crossings B hBS with h | h
            · change F.card = 0 at h; omega
            · exact h
          obtain ⟨x', hx'⟩ : (F.erase m).Nonempty := by
            rw [← card_pos, card_erase_of_mem hmF, hF2]; norm_num
          obtain ⟨hx'm, hx'F⟩ := mem_erase.1 hx'
          have hx'c := (mem_filter.1 hx'F).2
          apply hnm
          refine ⟨x', (hfin' x').2 ⟨?_, hx'm⟩, ?_⟩
          · show Γ.S ∈ Γ.curves x'
            rw [hx'c]; exact mem_insert_of_mem (mem_singleton_self _)
          · show B ∈ Γ.curves x'
            rw [hx'c]; exact mem_insert_self _ _
        · exact hnm ⟨x, (hfin' x).2 ⟨hxf.1, hxm⟩, hxo⟩
      · exact hΓ.1.2 (Or.inr (Or.inr ⟨d1, e, hd1, he, hcS, hms⟩))
  exact hΓ.2 n ⟨D, Γ'⟩ (Or.inl hlt) hstuck

end SConf

end Pca.Sweep
