/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package P: the surgery of Lemma 3.11 from its hypotheses

`p_l311_surgery`: `doc/pca/sweep.md`, step 1 (`j < k` or `j > l`, else `δ = γ(j)` is a loop
inside `γ`), step 2 (the cut of the bounded component, two mirror cases), then `PSurg.surgery`.
-/
import Pca.Sweep.P_Setup

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-- Step 1: the foot `j` of the leg hit twice is not between the ends of `γ`. -/
theorem p_step1 {z : D} (hz : Γ.infStart = some z) {γ : Fin n} (hγS : γ ≠ Γ.S)
    (hin : ∀ γ', ¬ Γ.Inside γ' γ) {tk tl : ℕ} (hkl : tk < tl)
    (htlf : tl + Γ.infLen < period Γ.straight z) (hγl : Γ.LoopEnds γ (tk + 1) (tl + 1))
    (hiff : ∀ t < period Γ.straight z, γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) ↔
      t = tk ∨ t = tl)
    {rγ : Γ.Cell → ZMod 2} {Lγ : Finset D} (cγ : CCut Γ z tk tl rγ Lγ)
    (hLγ : ∀ y ∈ Lγ, Γ.curve y = γ) (hLγ' : ∀ y, Γ.Above y → Γ.curve y = γ → y ∈ Lγ)
    {tj : ℕ} (htj : tj < period Γ.straight z) {a0 : D} (ha0 : a0 = Γ.σ (Γ.noC z tj))
    (ha0A : Γ.Above a0) (hδγ : Γ.curve a0 ≠ γ)
    (hu1 : Γ.curve (Γ.σ (Γ.α a0)) = γ) (huS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α a0)))
    (hu1' : Γ.curve (Γ.σ (Γ.α (Γ.straight a0))) = γ)
    (huS' : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α (Γ.straight a0))))
    (hγj : ¬ (tj = tk ∨ tj = tl)) : tj < tk ∨ tl < tj := by
  classical
  by_contra hmid
  push Not at hmid
  have hk : tk < tj := lt_of_le_of_ne hmid.1 (fun h => hγj (Or.inl h.symm))
  have hl : tj < tl := lt_of_le_of_ne hmid.2 (fun h => hγj (Or.inr h))
  have hδS : Γ.curve a0 ≠ Γ.S := ha0A.1
  have hδj : Γ.curve a0 ∈ Γ.curves (Γ.crossingOf (Γ.noC z tj)) := by
    rw [← j_crossingOf_σ, ← ha0]; exact ab_mem_curves_self a0
  apply hin (Γ.curve a0)
  obtain ⟨L, t2, A, -, hc2⟩ := p_arc_exists hz hδS htj hδj
  rw [← ha0] at A
  have hL0 : L ≠ 0 := by
    intro h0
    have := A.hL
    rw [h0, pow_zero, Perm.one_apply] at this
    apply huS
    rw [this, j_α_α, j_crossingOf_σ]; exact no_S_mem_noC hz t2
  have hL1 : L ≠ 1 := by
    intro h1
    have := A.hL
    rw [h1, pow_one] at this
    apply huS'
    rw [this, j_α_α, j_crossingOf_σ]; exact no_S_mem_noC hz t2
  set G := (range L).filter (fun q => Γ.σ (Γ.α ((Γ.straight ^ q) a0)) ∈ Lγ)
  have hmemG : ∀ q, q < L → Γ.Above ((Γ.straight ^ q) a0) →
      Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ q) a0))) = γ → q ∈ G := by
    intro q hq hA hc
    refine mem_filter.2 ⟨mem_range.2 hq, hLγ' _ ⟨by rw [hc]; exact hγS, ?_⟩ hc⟩
    unfold Up; rw [gk_cell_σα]; exact hA.2
  have h0G : 0 ∈ G := hmemG 0 (by omega) (A.hall 0 (Nat.zero_le _)) (by simpa using hu1)
  have h1G : 1 ∈ G := hmemG 1 (by omega) (A.hall 1 (by omega)) (by simpa using hu1')
  have hG2 : G.card = 2 := by
    have hle : G.card ≤ 2 := A.count_le (Ne.symm hδγ) hLγ
    have hge : 2 ≤ G.card := by
      have := card_le_card (show ({0, 1} : Finset ℕ) ⊆ G by
        intro q hq; simp only [mem_insert, mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact h0G
        · exact h1G)
      simpa using this
    omega
  have hend := A.walk_end (g := rγ) (F := Lγ) (fun y hy => cγ.cut y hy)
    (fun hm => hδγ (A.curve_end ▸ hLγ _ hm))
  rw [show (range L).filter (fun q => Γ.σ (Γ.α ((Γ.straight ^ q) a0)) ∈ Lγ) = G from rfl,
    hG2, c_sweep cγ htj, if_pos ⟨hk.le, hl⟩, c_sweep cγ A.t2P] at hend
  have e2 : tk ≤ t2 ∧ t2 < tl := by
    by_contra h; rw [if_neg h] at hend; exact absurd hend (by decide)
  have hnk : t2 ≠ tk := by
    rintro rfl
    have hγk := (hiff t2 A.t2P).2 (Or.inl rfl)
    have := no_mem_curves (no_S_mem_noC hz _) hγk hγS
    rw [this, mem_insert, mem_singleton] at hc2
    rcases hc2 with h | h
    · exact hδγ h
    · exact hδS h
  exact p_inside_of_ends hz hδS hγl htlf ⟨hk, hl⟩ ⟨by omega, e2.2⟩ A.ne hδj hc2

/-- Step 2, `j < k`: the bounded component cut out by `S[j, k]`, `β` (from `k` to `u`) and
`⟨u, j⟩`. -/
theorem p_case_left {z : D} (hz : Γ.infStart = some z) {γ : Fin n} (hγS : γ ≠ Γ.S)
    {tk tl : ℕ} (hkl : tk < tl) (htlf : tl + Γ.infLen < period Γ.straight z)
    (hγl : Γ.LoopEnds γ (tk + 1) (tl + 1))
    (hiff : ∀ t < period Γ.straight z, γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) ↔
      t = tk ∨ t = tl)
    {rγ : Γ.Cell → ZMod 2} {Lγ : Finset D} (cγ : CCut Γ z tk tl rγ Lγ)
    (hLγ : ∀ y ∈ Lγ, Γ.curve y = γ) (hLγ' : ∀ y, Γ.Above y → Γ.curve y = γ → y ∈ Lγ)
    {tj : ℕ} (hjk : tj < tk) {a0 : D} (ha0 : a0 = Γ.σ (Γ.noC z tj))
    (ha0A : Γ.Above a0) (hδγ : Γ.curve a0 ≠ γ)
    (hu1 : Γ.curve (Γ.σ (Γ.α a0)) = γ) (huS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α a0))) :
    ∃ m r Lid, PSurg Γ γ (Γ.curve a0) z tk tl tj tk tj tk m rγ r Lγ Lid a0
      (Γ.σ (Γ.noC z tk)) := by
  have htk : tk < period Γ.straight z := by omega
  have hγk := (hiff tk htk).2 (Or.inl rfl)
  obtain ⟨m, hm0, hmP, hβA, hu⟩ := p_beta hz hγS htk hγk ha0A hu1 huS
  set b0 := Γ.σ (Γ.noC z tk) with hb0
  have hγb : Γ.curve b0 = γ := (p_curve_σ_iff (no_noC_sweep hz tk) hγS).2 hγk
  have hβS := fun {i} (hi : i < m) => p_beta_not_S hβA hu huS hi
  set ret : ℕ → D := fun i => if i < m then (Γ.straight ^ i) b0 else Γ.α a0 with hret
  have hr1 : ∀ i < m, ret i = (Γ.straight ^ i) b0 := fun i hi => if_pos hi
  have hr2 : ret m = Γ.α a0 := if_neg (lt_irrefl m)
  have hcases : ∀ i < m + 1, i < m ∨ i = m := fun i hi => by omega
  obtain ⟨r, Lid, cR, hL⟩ := p_ccut hz hjk (by omega) (q := m + 1) (Nat.succ_pos _) ret
    (fun j hj => by
      rcases hcases j hj with h | rfl
      · rw [hr1 j h]; exact (hβA j h).1
      · rw [hr2, j_curve_α]; exact ha0A.1)
    (by rw [hr1 0 hm0, pow_zero, Perm.one_apply])
    (fun j hj => by
      rw [hr1 j (by omega)]
      by_cases h : j + 1 < m
      · rw [hr1 _ h, no_pow_succ, no_crossingOf_α_straight]
      · rw [show j + 1 = m by omega, hr2, ← hu, show j = m - 1 by omega])
    (by rw [Nat.add_sub_cancel, hr2, j_α_α, ha0])
    (fun j hj0 hj => by
      rcases hcases j hj with h | rfl
      · rw [hr1 j h, show j = (j - 1) + 1 by omega, no_pow_succ, no_crossingOf_α_straight]
        exact hβS (by omega)
      · rw [hr2]; exact huS)
    (fun i hi j hj h => by
      rcases hcases i hi with h1 | rfl <;> rcases hcases j hj with h2 | rfl
      · rw [hr1 i h1, hr1 j h2] at h; exact gk_seg_pow_inj (by omega) (by omega) h
      · rw [hr1 i h1, hr2] at h
        have := c_curve_seg h
        rw [j_curve_α, no_curve_pow, hγb] at this
        exact absurd this hδγ
      · rw [hr2, hr1 j h2] at h
        have := c_curve_seg h
        rw [j_curve_α, no_curve_pow, hγb] at this
        exact absurd this.symm hδγ
      · rfl)
  refine ⟨m, r, Lid, ⟨hz, hγl, cγ, hLγ, hLγ', cR, Or.inl ⟨rfl, rfl⟩, ha0, rfl, rfl, hγb, hδγ,
    hm0, hmP, hβA, hu, fun y hy => ?_, fun i hi => (hL _).2 ⟨i, by omega, Or.inl (hr1 i hi).symm⟩,
    ?_⟩⟩
  · obtain ⟨j, hj, h | h⟩ := (hL y).1 hy <;> rcases hcases j hj with h' | rfl
    · exact Or.inr (Or.inr ⟨j, h', Or.inl (h.trans (hr1 j h'))⟩)
    · exact Or.inr (Or.inl (h.trans hr2))
    · exact Or.inr (Or.inr ⟨j, h', Or.inr (by rw [h, hr1 j h'])⟩)
    · exact Or.inl (by rw [h, hr2, j_α_α])
  · have h1 := c_sweep cR (t := tk) htk
    have h2 := c_sweep cγ (t := tk) htk
    rw [if_neg (by omega)] at h1
    rw [if_pos ⟨le_rfl, hkl⟩] at h2
    rw [hb0, p_cell_σ_noC, h1, h2, zero_add]

/-- Step 2, `j > l`: the bounded component cut out by `S[l, j]`, `⟨j, u⟩` and `β` (from `u` back
to `l`). -/
theorem p_case_right {z : D} (hz : Γ.infStart = some z) {γ : Fin n} (hγS : γ ≠ Γ.S)
    {tk tl : ℕ} (htlf : tl + Γ.infLen < period Γ.straight z)
    (hγl : Γ.LoopEnds γ (tk + 1) (tl + 1))
    (hiff : ∀ t < period Γ.straight z, γ ∈ Γ.curves (Γ.crossingOf (Γ.noC z t)) ↔
      t = tk ∨ t = tl)
    {rγ : Γ.Cell → ZMod 2} {Lγ : Finset D} (cγ : CCut Γ z tk tl rγ Lγ)
    (hLγ : ∀ y ∈ Lγ, Γ.curve y = γ) (hLγ' : ∀ y, Γ.Above y → Γ.curve y = γ → y ∈ Lγ)
    {tj : ℕ} (hlj : tl < tj) (hjf : tj + Γ.infLen < period Γ.straight z) {a0 : D}
    (ha0 : a0 = Γ.σ (Γ.noC z tj)) (ha0A : Γ.Above a0) (hδγ : Γ.curve a0 ≠ γ)
    (hu1 : Γ.curve (Γ.σ (Γ.α a0)) = γ) (huS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α a0))) :
    ∃ m r Lid, PSurg Γ γ (Γ.curve a0) z tk tl tl tj tj tl m rγ r Lγ Lid a0
      (Γ.σ (Γ.noC z tl)) := by
  have htl : tl < period Γ.straight z := by omega
  have hγl' := (hiff tl htl).2 (Or.inr rfl)
  obtain ⟨m, hm0, hmP, hβA, hu⟩ := p_beta hz hγS htl hγl' ha0A hu1 huS
  set b0 := Γ.σ (Γ.noC z tl) with hb0
  have hγb : Γ.curve b0 = γ := (p_curve_σ_iff (no_noC_sweep hz tl) hγS).2 hγl'
  have hβS := fun {i} (hi : i < m) => p_beta_not_S hβA hu huS hi
  set ret : ℕ → D := fun i => if i = 0 then a0 else Γ.α ((Γ.straight ^ (m - i)) b0) with hret
  have hr1 : ret 0 = a0 := if_pos rfl
  have hr2 : ∀ i, 0 < i → ret i = Γ.α ((Γ.straight ^ (m - i)) b0) :=
    fun i hi => if_neg (by omega)
  obtain ⟨r, Lid, cR, hL⟩ := p_ccut hz hlj hjf (q := m + 1) (Nat.succ_pos _) ret
    (fun j hj => by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · rw [hr1]; exact ha0A.1
      · rw [hr2 j h, j_curve_α]; exact (hβA _ (by omega)).1)
    (by rw [hr1, ha0])
    (fun j hj => by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · rw [hr1, hr2 1 one_pos, ← hu]
      · rw [hr2 j h, j_α_α, hr2 (j + 1) (by omega),
          show m - j = (m - (j + 1)) + 1 by omega, no_pow_succ, no_crossingOf_α_straight])
    (by rw [Nat.add_sub_cancel, hr2 m hm0, Nat.sub_self, pow_zero, Perm.one_apply, j_α_α])
    (fun j hj0 hj => by
      rw [hr2 j hj0]; exact hβS (by omega))
    (fun i hi j hj h => by
      rcases Nat.eq_zero_or_pos i with rfl | h1 <;> rcases Nat.eq_zero_or_pos j with rfl | h2
      · rfl
      · rw [hr1, hr2 j h2] at h
        have := c_curve_seg h
        rw [j_curve_α, no_curve_pow, hγb] at this
        exact absurd this.symm hδγ
      · rw [hr2 i h1, hr1] at h
        have := c_curve_seg h
        rw [j_curve_α, no_curve_pow, hγb] at this
        exact absurd this hδγ
      · rw [hr2 i h1, hr2 j h2, j_segmentOf_α, j_segmentOf_α] at h
        have := gk_seg_pow_inj (by omega) (by omega) h
        omega)
  refine ⟨m, r, Lid, ⟨hz, hγl, cγ, hLγ, hLγ', cR, Or.inr ⟨rfl, rfl⟩, ha0, rfl, rfl, hγb, hδγ,
    hm0, hmP, hβA, hu, fun y hy => ?_, fun i hi => (hL _).2 ⟨m - i, by omega, Or.inr ?_⟩, ?_⟩⟩
  · obtain ⟨j, hj, h | h⟩ := (hL y).1 hy <;> rcases Nat.eq_zero_or_pos j with rfl | h'
    · exact Or.inl (h.trans hr1)
    · exact Or.inr (Or.inr ⟨m - j, by omega, Or.inr (h.trans (hr2 j h'))⟩)
    · exact Or.inr (Or.inl (by rw [h, hr1]))
    · exact Or.inr (Or.inr ⟨m - j, by omega, Or.inl (by rw [h, hr2 j h', j_α_α])⟩)
  · rw [hr2 (m - i) (by omega), Nat.sub_sub_self hi.le, j_α_α]
  · have h1 := c_sweep cR (t := tl) htl
    have h2 := c_sweep cγ (t := tl) htl
    rw [if_pos ⟨le_rfl, hlj⟩] at h1
    rw [if_neg (by omega)] at h2
    rw [hb0, p_cell_σ_noC, h1, h2, add_zero]

/-- **The surgery of Lemma 3.11** (SH pp. 324-325, `doc/pca/sweep.md`). -/
theorem p_l311_surgery (hΓ : Γ.MinCE) {γ : Fin n} (hγ : Γ.Present γ) (hloop : Γ.IsLoop γ)
    (hin : ∀ γ', ¬ Γ.Inside γ' γ) (X : Γ.Removal {γ}) {d' : X.D'} (ht : X.Γ'.EmptyTriAt d') :
    ∃ (n' : ℕ) (K : Conf.{u} n'), SizeLT K.Γ Γ ∧ ¬ K.Γ.Terminal ∧
      (∀ d, ¬ K.Γ.EmptyHumpAt d) ∧ (∀ d, ¬ K.Γ.EmptyTriAt d) ∧
      (K.Γ.CanTakeLoop → ∃ α, Γ.Inside α γ) := by
  obtain ⟨a0, ha0A, ha0f, hδγ, hγu, hγu'⟩ := p_tri_a0 hΓ hγ X ht
  obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z :=
    Option.isSome_iff_exists.1 (Γ.infStart_isSome ⟨a0⟩)
  have hγS : γ ≠ Γ.S := hγ.1
  obtain ⟨tk, tl, hkl, htlf, hγl, hiff⟩ := p_loop_data hz hγS hloop
  obtain ⟨rγ, Lγ, cγ, hLγ, hLγ'⟩ := p_gamma_cut hz hγS hkl htlf hiff
  -- the foot `j` of the leg
  obtain ⟨tj, htj, hxj⟩ := no_onSweep_noC hz ha0f.1
  have hjf : tj + Γ.infLen < period Γ.straight z := (no_noC_fin hz htj).1 (hxj ▸ ha0f)
  have ha0 : a0 = Γ.σ (Γ.noC z tj) := c_eq_σ_noC hz ha0A hxj.symm
  have hδS : Γ.curve a0 ≠ Γ.S := ha0A.1
  have hδj : Γ.curve a0 ∈ Γ.curves (Γ.crossingOf (Γ.noC z tj)) := by
    rw [hxj]; exact ab_mem_curves_self a0
  have hγj : ¬ (tj = tk ∨ tj = tl) := fun h => by
    have := (hiff tj htj).2 h
    rw [no_mem_curves (no_S_mem_noC hz tj) hδj hδS, mem_insert, mem_singleton] at this
    rcases this with h' | h'
    · exact hδγ h'.symm
    · exact hγS h'
  -- the first two crossings of `δ` after `j` are with `γ`
  have hu1 : Γ.curve (Γ.σ (Γ.α a0)) = γ := p_other hγu (by rw [j_curve_α]; exact hδγ)
  have hu1' : Γ.curve (Γ.σ (Γ.α (Γ.straight a0))) = γ :=
    p_other hγu' (by rw [j_curve_α, j_curve_straight]; exact hδγ)
  have hnS : ∀ y, Γ.curve y = Γ.curve a0 → Γ.curve (Γ.σ (Γ.α y)) = γ →
      ¬ Γ.OnSweep (Γ.crossingOf (Γ.α y)) := by
    intro y hy hσ hS
    change Γ.S ∈ _ at hS
    rw [j_curves_crossingOf, j_curve_α, hy, hσ, mem_insert, mem_singleton] at hS
    rcases hS with h | h
    · exact hδS h.symm
    · exact hγS h.symm
  have huS := hnS a0 rfl hu1
  have huS' := hnS (Γ.straight a0) (j_curve_straight _ _) hu1'
  -- step 1 and step 2
  rcases p_step1 hz hγS hin hkl htlf hγl hiff cγ hLγ hLγ' htj ha0 ha0A hδγ hu1 huS hu1' huS'
    hγj with hjk | hlj
  · obtain ⟨m, r, Lid, H⟩ := p_case_left hz hγS hkl htlf hγl hiff cγ hLγ hLγ' hjk ha0 ha0A hδγ
      hu1 huS
    exact H.surgery hΓ htlf (Or.inr hkl)
  · obtain ⟨m, r, Lid, H⟩ := p_case_right hz hγS htlf hγl hiff cγ hLγ hLγ' hlj hjf ha0 ha0A
      hδγ hu1 huS
    exact H.surgery hΓ (tO := tk) (by omega) (Or.inl hkl)

end SConf

end Pca.Sweep
