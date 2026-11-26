/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package E (SH Lemma 3.7), the case analysis

`X` removes `γ`, `d'` is a finite edge of `Γ − γ` with an empty hump or triangle above it,
`b' = α' d'` (from `K` to `I`), `F'` its cell: `eC b' 0 = b'`, `eC b' 1 = σ' d'` (the leg `L` from
`I`), and for a triangle `eC b' 2` (the leg `T` into `K`). If the joined segment of `d'` had a
crossing with `γ`, the boundary walk of `F'` would have a port at position `0` (the vertex `j` of
`γ` on the sweep next to `K`), and Step 3 of `doc/pca/sweep.md` gives a contradiction with SH
Lemma 3.6 (a hump or a triangle at `K` or at `I`), with two-intersection (three ports on one leg)
or with the noncrossing lemma.
-/
import Pca.Sweep.E_Chord

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {γ : Fin n}

/-- The crossing at the end of a dart above the sweep, where the other curve is not `S`, is a
vertex above the sweep. -/
theorem e_aboveVertex {a : D} (ha : Γ.Above a) (hc : Γ.curve (Γ.σ (Γ.α a)) ≠ Γ.S) :
    Γ.IsAboveVertex (Γ.crossingOf (Γ.α a)) := by
  refine ⟨?_, Γ.α a, Orbit.mem_darts.2 rfl, ?_⟩
  · show Γ.S ∉ Γ.curves _
    rw [j_curves_crossingOf, mem_insert, mem_singleton, j_curve_α]
    rintro (h | h)
    · exact ha.1 h.symm
    · exact hc h.symm
  · exact ⟨by rw [j_curve_α]; exact ha.1, by unfold Up; rw [no_side_α ha.1]; exact ha.2⟩

/-- Crossings along one straight walk are distinct within a period. -/
theorem e_cross_ne {h : D} {i j : ℕ} (hij : i < j) (hj : j < period Γ.straight h) :
    Γ.crossingOf (Γ.α ((Γ.straight ^ i) h)) ≠ Γ.crossingOf (Γ.α ((Γ.straight ^ j) h)) := by
  intro hx
  have hc : Γ.curve (Γ.α ((Γ.straight ^ i) h)) = Γ.curve (Γ.α ((Γ.straight ^ j) h)) := by
    rw [j_curve_α, j_curve_α, no_curve_pow, no_curve_pow]
  rcases e_eq_or_eq_σσ hx hc with h1 | h1
  · have h2 := congrArg Γ.α h1
    rw [j_α_α, j_α_α] at h2
    have := no_pow_inj hj (by omega) h2
    omega
  · have ha : Γ.α ((Γ.straight ^ j) h) = (Γ.straight ^ (i + 1)) h := by
      rw [h1, no_pow_succ]; rfl
    have hb : Γ.σ (Γ.σ ((Γ.straight ^ (i + 1)) h)) = (Γ.straight ^ (j + 1)) h := by
      rw [show (Γ.straight ^ (j + 1)) h = Γ.straight ((Γ.straight ^ j) h) from no_pow_succ _ _,
        j_straight_apply, ha]
    apply no_not_sameCycle_straight_σσ ((Γ.straight ^ (i + 1)) h)
    rw [hb]
    exact Perm.sameCycle_pow_left.2 (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ h))

theorem e_isTri_symm {a b : D} (h : Γ.IsTri a b) : Γ.IsTri b a := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h2, h1, h4, h3, Ne.symm h5, h6.symm, h6 ▸ h7, Ne.symm h8⟩

namespace Removal

variable {X : Γ.Removal {γ}}

theorem e_J_lt_period (e' : X.D') : X.eJ e' < period Γ.straight (X.ι e') := by
  by_contra h
  have := r_notK_pow (e_rK e') (t := period Γ.straight (X.ι e')) (period_pos _ _)
    (by unfold eJ at h; omega)
  rw [e_pow_period] at this
  exact this (e_rK e')

/-- `γ` crosses the curve of a dart of `Γ − γ` at most twice along it. -/
theorem e_three_ports (e' : X.D') {t1 t2 t3 : ℕ} (h12 : t1 < t2) (h23 : t2 < t3)
    (h3 : t3 < X.eJ e') : False := by
  classical
  set c := X.Γ'.curve e'
  have hcγ : c ≠ γ := by
    intro h
    have := e_curve_pc_nmem (X := X) e' 0
    rw [e_curve_pc, mem_singleton] at this
    exact this h
  have hlt := e_J_lt_period e'
  set x : ℕ → Γ.Crossing := fun t => Γ.crossingOf (Γ.α (X.ePc e' t))
  have hcur : ∀ t < X.eJ e', Γ.curves (x t) = {c, γ} := by
    intro t ht
    have hd : Γ.Deleted {γ} (x t) := not_not.1 (fun h => by
      have := (e_pc_rK ht.le).1 h; omega)
    show Γ.curves (Γ.crossingOf (Γ.α (X.ePc e' t))) = _
    rw [j_curves_crossingOf, j_curve_α, e_curve_pc]
    rw [r_deleted_iff, j_curve_α, e_curve_pc] at hd
    rcases hd with h | h
    · exact absurd (mem_singleton.1 h) hcγ
    · rw [mem_singleton.1 h]
  have hne : ∀ {s t : ℕ}, s < t → t < X.eJ e' → x s ≠ x t := fun hst ht =>
    e_cross_ne hst (by omega)
  have hsub : ({x t1, x t2, x t3} : Finset Γ.Crossing) ⊆
      univ.filter (fun y : Orbit Γ.σ => crossingCurves Γ.σ Γ.curve y = {c, γ}) := by
    intro y hy
    simp only [mem_insert, mem_singleton] at hy
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rcases hy with rfl | rfl | rfl
    · exact hcur t1 (by omega)
    · exact hcur t2 (by omega)
    · exact hcur t3 h3
  have h3card : ({x t1, x t2, x t3} : Finset Γ.Crossing).card = 3 :=
    card_eq_three.2 ⟨_, _, _, hne h12 (by omega), hne (by omega : t1 < t3) h3, hne h23 h3, rfl⟩
  have := le_trans (h3card ▸ card_le_card hsub) (Γ.isSConf.two_int c γ hcγ)
  omega

/-- The ports on a finite edge of `Γ − γ` are vertices on the sweep. -/
theorem e_base_fin {d' : X.D'} (hd : X.Γ'.IsFinSeg d') {t : ℕ}
    (ht : t < X.eJ (X.Γ'.α d')) :
    Γ.IsFinVertex (Γ.crossingOf (Γ.α (X.ePc (X.Γ'.α d') t))) := by
  rw [e_eJ_α] at ht
  have h1 : Γ.α (X.ePc (X.Γ'.α d') t) = X.ePc d' (X.eJ d' - t) := by
    rw [e_α_pc _ (by rw [e_eJ_α]; omega), j_α_α, e_eJ_α]
  obtain ⟨s, hs⟩ : ∃ s, X.eJ d' - t = s + 1 := ⟨X.eJ d' - t - 1, by omega⟩
  rw [h1, hs, e_crossing_pc_succ]
  refine ⟨?_, e_port_not_inf hd (by omega)⟩
  show Γ.S ∈ Γ.curves _
  rw [j_curves_crossingOf, j_curve_α, e_curve_pc, ← X.isRemoval.S, hd.1.1]
  exact mem_insert_self _ _

theorem e_base_cr {d' : X.D'} {t : ℕ} (ht : t < X.eJ (X.Γ'.α d')) :
    Γ.crossingOf (Γ.α (X.ePc (X.Γ'.α d') t)) = Γ.crossingOf (X.ePc d' (X.eJ d' - t)) := by
  rw [e_eJ_α] at ht
  rw [e_α_pc _ (by rw [e_eJ_α]; omega), j_α_α, e_eJ_α]

/-- A piece of a finite edge of `Γ − γ` is not the start of the ∞-arc of `Γ`. -/
theorem e_not_z {d' : X.D'} (hd : X.Γ'.IsFinSeg d') {z : D} (hz : Γ.infStart = some z) {s : ℕ}
    (hs : s ≤ X.eJ d') : X.ePc d' s ≠ z := by
  intro h
  obtain ⟨z', hz'm⟩ : ∃ z', X.Γ'.infStart = some z' :=
    Option.isSome_iff_exists.1 (X.Γ'.infStart_isSome ⟨d'⟩)
  obtain ⟨z0, hz0, hp⟩ := X.isRemoval.infStart z' (by rw [hz'm]; rfl)
  have hz0' : z0 = z := by rw [hz] at hz0; exact (Option.some_inj.1 hz0).symm
  subst hz0'
  obtain ⟨k, hk, hkz⟩ := (Γ.r_piece_iff {γ}).1 hp
  have hkJ : k ≤ X.eJ z' := by
    by_contra hlt
    exact hk _ (show Γ.rJ {γ} (X.ι z') < k by unfold eJ at hlt; omega) (r_K_end (e_rK z'))
  have heq : d' = z' := e_pc_unique (a := s) (b := k) hs hkJ (by rw [h]; exact hkz.symm)
  subst heq
  apply hd.2
  show d' ∈ arcOf X.Γ'.σ X.Γ'.α X.Γ'.infStart X.Γ'.infLen
  rw [hz'm]
  exact mem_image.2 ⟨0, mem_range.2 (Nat.succ_pos _), rfl⟩

/-- Along a finite edge of `Γ − γ`, the positions in `Γ` of the crossings increase by one per
piece (the joined segment does not run through the ∞-arc). -/
theorem e_pos_pc {d' : X.D'} (hd : X.Γ'.IsFinSeg d') :
    ∃ p0, ∀ s ≤ X.eJ d' + 1, Γ.pos (Γ.crossingOf (X.ePc d' s)) = p0 + s := by
  obtain ⟨z, hz⟩ : ∃ z, Γ.infStart = some z :=
    Option.isSome_iff_exists.1 (Γ.infStart_isSome ⟨X.ι d'⟩)
  obtain ⟨t0, ht0, he⟩ := no_noC_surj hz (e_sweep_ι hd.1)
  have hL := no_infLen_le hz
  set P := period Γ.straight z
  have hLt : t0 + Γ.infLen < P := by
    have hf := (Removal.r_finVertex X (X.Γ'.crossingOf d')).1 (e_finSeg_fin hd).1
    rw [Removal.r_rΨ_mk, ← he] at hf
    exact (no_noC_fin hz ht0).1 hf
  have hpc : ∀ s, X.ePc d' s = Γ.noC z (t0 + s) := by
    intro s; unfold ePc; rw [← he]; unfold noC; rw [← no_pow_add, add_comm]
  have hzP : ∀ s, t0 + s = P - Γ.infLen - 1 → X.ePc d' s = z := by
    intro s hs
    rw [hpc, no_noC_eq, hs, show P - Γ.infLen - 1 + (Γ.infLen + 1) = 0 + P by omega,
      no_pow_period, pow_zero, Perm.one_apply]
  have h1 : t0 + Γ.infLen + 1 < P := by
    by_contra hlt
    rcases Nat.lt_or_ge (t0 + Γ.infLen) P with h2 | h2
    · exact e_not_z hd hz (Nat.zero_le _) (hzP 0 (by omega))
    · have hinf : Γ.IsInfVertex (Γ.crossingOf (X.ι d')) := by
        rw [← he]; exact (no_noC_inner hz ht0).2 h2
      exact (e_finSeg_fin hd).1.2 ((X.isRemoval.infVertex d').2 hinf)
  have h2 : t0 + X.eJ d' + 1 < P := by
    by_contra hlt
    exact e_not_z hd hz (s := P - Γ.infLen - 1 - t0) (by omega) (hzP _ (by omega))
  refine ⟨t0 + 1, fun s hs => ?_⟩
  rw [hpc, no_noC_pos hz (by omega)]
  omega

section Main

variable {d' : X.D'}

theorem e_port_classify {b' : X.D'} {u : ℕ} (hu : u < X.eN b') (hp : X.EPort b' u) :
    ∃ i < X.eM b', ∃ t < X.eJ (X.eC b' i), u = X.eP b' i + t := by
  obtain ⟨i, hi, t, ht, rfl⟩ := e_decomp hu
  refine ⟨i, hi, t, ?_, rfl⟩
  rcases Nat.lt_or_ge t (X.eJ (X.eC b' i)) with h | h
  · exact h
  · exfalso
    apply hp
    rw [e_W_pos i ht]
    exact (e_pc_rK ht).2 (le_antisymm ht h)

theorem e_port_of {b' : X.D'} {i t : ℕ} (hi : i < X.eM b') (ht : t < X.eJ (X.eC b' i)) :
    X.EPort b' (X.eP b' i + t) ∧ X.eP b' i + t < X.eN b' := by
  refine ⟨?_, lt_of_lt_of_le (by omega) (e_P_last_lt hi).le⟩
  unfold EPort
  rw [e_W_pos i ht.le]
  intro h
  have := (e_pc_rK ht.le).1 h
  omega

theorem e_P_zero (b' : X.D') : X.eP b' 0 = 0 := rfl

theorem e_P_one (b' : X.D') : X.eP b' 1 = X.eJ b' + 1 := by
  rw [e_P_succ, e_P_zero, zero_add]; rfl

/-- **The case analysis** (Step 3 of `doc/pca/sweep.md`): the finite edge under an empty hump or
triangle of `Γ − γ` is a single segment of `Γ`. -/
theorem e_main (h34 : ∀ δ, Γ.Present δ → Γ.MeetsSweep δ)
    (h36 : (∀ a, ¬ Γ.IsHump a) ∧ ∀ a b, ¬ (Γ.IsTri a b ∧
      Γ.pos (Γ.crossingOf a) < Γ.pos (Γ.crossingOf b) ∧ Γ.φ a = Γ.α b))
    (h : X.Γ'.EmptyHumpAt d' ∨ X.Γ'.EmptyTriAt d') : X.ι (X.Γ'.α d') = Γ.α (X.ι d') := by
  have hfin : X.Γ'.IsFinSeg d' := by rcases h with h | h <;> exact h.1
  rw [e_ι_α']
  by_cases hJ0 : X.eJ d' = 0
  · rw [hJ0]; rfl
  exfalso
  set b' := X.Γ'.α d' with hb'
  have hSd : X.Γ'.curve d' = Γ.S := by rw [hfin.1.1, X.isRemoval.S]
  have hγS : γ ≠ Γ.S := fun h' => r_S_not_mem X d' (by rw [← h']; exact mem_singleton_self _)
  have hup : X.Γ'.side (X.Γ'.cellOf b') = 1 := hfin.1.2
  have hM : X.eM b' = 2 ∨ X.eM b' = 3 := by
    have hsz : (X.Γ'.upperCell d').size = X.eM b' := by
      unfold upperCell eM
      rw [Orbit.size, cellOf, Orbit.darts_mk, card_orbitFinset]
    rcases h with h | h
    · exact Or.inl (hsz ▸ h.2)
    · exact Or.inr (hsz ▸ h.2)
  have hC0 : X.eC b' 0 = b' := rfl
  have hC1 : X.eC b' 1 = X.Γ'.σ d' := by
    show X.Γ'.φ b' = _
    rw [j_φ_apply, hb', j_α_α]
  have hCsucc : ∀ i, X.eC b' (i + 1) = X.Γ'.φ (X.eC b' i) := by
    intro i; unfold eC; rw [pow_succ', Perm.mul_apply]
  have hCM : X.eC b' (X.eM b') = b' := e_pow_period _ _
  have hJb : X.eJ b' = X.eJ d' := e_eJ_α d'
  have hJb0 : 0 < X.eJ (X.eC b' 0) := by rw [hC0, hJb]; omega
  -- notation
  set N := X.eN b' with hN
  have hP1 : X.eP b' 1 = X.eJ b' + 1 := e_P_one b'
  have hP2 : X.eP b' 2 = X.eP b' 1 + X.eJ (X.eC b' 1) + 1 := e_P_succ 1
  obtain ⟨p0, hpos⟩ := e_pos_pc hfin
  have hposG : ∀ t < X.eJ b', Γ.pos (Γ.crossingOf (X.eG b' t)) = p0 + (X.eJ d' - t) := by
    intro t ht
    have hw : X.eW b' t = X.ePc b' t := by
      have := e_W_pos (X := X) (b' := b') 0 (t := t) (by rw [hC0]; omega)
      rwa [e_P_zero, zero_add] at this
    rw [e_crossing_G, hw, e_base_cr ht, hpos _ (by omega)]
  -- facts on chords
  have hGabove : ∀ u < N, X.EPort b' u → Γ.Above (X.eG b' u) := by
    intro u hu hp
    refine ⟨by rw [e_G_curve hu hp]; exact hγS, ?_⟩
    unfold Up; rw [e_cell_G, e_W_side hu, hup]
  have hbase : ∀ t < X.eJ b', Γ.IsFinVertex (Γ.crossingOf (X.eG b' t)) := by
    intro t ht
    rw [e_crossing_G, show t = X.eP b' 0 + t from (zero_add t).symm, e_W_pos 0 (by rw [hC0]; omega),
      hC0]
    exact e_base_fin hfin ht
  have hbaseN : ∀ t < X.eJ b', t < N := fun t ht => by
    have := (e_port_of (b' := b') (i := 0) (by rcases hM with h' | h' <;> omega)
      (by rw [hC0]; exact ht)).2
    rw [e_P_zero] at this; omega
  have hbaseP : ∀ t < X.eJ b', X.EPort b' t := fun t ht => by
    have := (e_port_of (b' := b') (i := 0) (by rcases hM with h' | h' <;> omega)
      (by rw [hC0]; exact ht)).1
    rw [e_P_zero, zero_add] at this; exact this
  have hdel : ∀ u, X.EPort b' u → ∀ e' : X.D',
      Γ.crossingOf (X.eG b' u) ≠ Γ.crossingOf (X.ι e') := by
    intro u hp e' he
    apply hp
    have := e_rK e'
    unfold rK at this ⊢
    rw [← e_crossing_G, he]; exact this
  -- a hump in `Γ`
  have hump : ∀ t s, t < X.eJ b' → s < X.eJ b' → X.ECh b' t s → False := by
    intro t s ht hs hch
    refine h36.1 (X.eG b' t) ⟨hGabove t (hbaseN t ht) (hbaseP t ht), hbase t ht, ?_⟩
    unfold ECh at hch; rw [hch]; exact hbase s hs
  -- the triangle at `I`
  have triI : ∀ t, t < X.eJ b' → 0 < X.eJ (X.eC b' 1) → 2 ≤ X.eM b' →
      X.ECh b' t (X.eP b' 1) → False := by
    intro t ht hJL hM2 hch
    have hP1N : X.eP b' 1 < N := lt_of_le_of_lt (Nat.le_add_right _ _) (e_P_last_lt (by omega))
    set L := X.eW b' (X.eP b' 1) with hL
    have hLι : L = X.ι (X.Γ'.σ d') := by rw [hL, e_W_P, hC1]
    have hLS : Γ.curve L ≠ Γ.S := by
      rw [hLι, ← X.isRemoval.curve, ← hSd]; exact no_curve_σ_ne d'
    have hLab : Γ.Above L := ⟨hLS, by unfold Up; rw [e_W_side hP1N, hup]⟩
    have hp1 : X.EPort b' (X.eP b' 1) := by
      have := (e_port_of (b' := b') (i := 1) (by omega) hJL).1; rwa [add_zero] at this
    have hcrL : Γ.crossingOf L = Γ.crossingOf (X.ePc d' 0) := by
      rw [hLι, X.isRemoval.σ, j_crossingOf_σ]; rfl
    refine h36.2 L (X.eG b' t) ⟨e_isTri_symm ⟨hGabove t (hbaseN t ht) (hbaseP t ht), hLab,
      hbase t ht, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hLι, X.isRemoval.σ, j_crossingOf_σ]
      exact (Removal.r_finVertex X (X.Γ'.crossingOf d')).1 (e_finSeg_fin hfin).1
    · rw [hLι]; exact hdel t (hbaseP t ht) _
    · unfold ECh at hch; rw [hch, e_crossing_G]
    · unfold ECh at hch; rw [hch, e_crossing_G]
      refine e_aboveVertex hLab ?_
      show Γ.curve (X.eG b' (X.eP b' 1)) ≠ Γ.S
      rw [e_G_curve hP1N hp1]; exact hγS
    · rw [e_G_curve (hbaseN t ht) (hbaseP t ht)]
      exact fun h' => e_W_ne_γ hP1N h'.symm
    · rw [hcrL, hpos 0 (by omega), hposG t ht]
      omega
    · unfold ECh at hch; rw [hch]; rfl
  -- the triangle at `K`
  have triK : ∀ k t, k + 1 = X.eM b' → 0 < X.eJ (X.eC b' k) → t < X.eJ b' →
      X.ECh b' t (X.eP b' k + X.eJ (X.eC b' k) - 1) → False := by
    intro k t hk hJk ht hch
    set z := X.eP b' k + X.eJ (X.eC b' k) - 1 with hz
    have hzN : z + 1 < N := by
      have := e_P_last_lt (X := X) (b' := b') (i := k) (by omega)
      omega
    have hzp : X.EPort b' z := by
      have := (e_port_of (b' := b') (i := k) (t := X.eJ (X.eC b' k) - 1) (by omega)
        (by omega)).1
      rwa [show X.eP b' k + (X.eJ (X.eC b' k) - 1) = z by omega] at this
    set B := X.eW b' (z + 1) with hB
    have hBpc : B = X.ePc (X.eC b' k) (X.eJ (X.eC b' k)) := by
      rw [hB, show z + 1 = X.eP b' k + X.eJ (X.eC b' k) by omega, e_W_pos k le_rfl]
    have hφ : X.Γ'.φ (X.eC b' k) = b' := by rw [← hCsucc, hk, hCM]
    have hcurk : X.Γ'.curve (X.eC b' k) ≠ Γ.S := by
      intro h'
      have h2 := no_curve_σ_ne (Γ := X.Γ') (X.Γ'.α (X.eC b' k))
      rw [← j_φ_apply, hφ, hb', j_curve_α, j_curve_α, hSd, h'] at h2
      exact h2 rfl
    have hBS : Γ.curve B ≠ Γ.S := by rw [hBpc, e_curve_pc]; exact hcurk
    have hBup : Γ.Up (Γ.cellOf B) := by unfold Up; rw [e_W_side (by omega), hup]
    have hαB : Γ.α B = X.ι (X.Γ'.α (X.eC b' k)) := by rw [hBpc, e_ι_α']
    have hcrB : Γ.crossingOf (Γ.α B) = Γ.crossingOf (X.ePc d' (X.eJ d' + 1)) := by
      rw [hαB, ← Removal.r_rΨ_mk]
      have : X.Γ'.crossingOf (X.Γ'.α (X.eC b' k)) = X.Γ'.crossingOf (X.Γ'.α d') := by
        rw [← j_crossingOf_σ, ← j_φ_apply, hφ]
      rw [this, Removal.r_rΨ_mk, e_ι_α', e_crossing_pc_succ]
    have hchz := hch
    refine h36.2 (X.eG b' t) (Γ.α B) ⟨⟨hGabove t (hbaseN t ht) (hbaseP t ht),
      ⟨by rw [j_curve_α]; exact hBS, by unfold Up; rw [no_side_α hBS]; exact hBup⟩,
      hbase t ht, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [hαB, ← Removal.r_rΨ_mk, ← Removal.r_finVertex]
      have : X.Γ'.crossingOf (X.Γ'.α (X.eC b' k)) = X.Γ'.crossingOf (X.Γ'.α d') := by
        rw [← j_crossingOf_σ, ← j_φ_apply, hφ]
      rw [this]; exact (e_finSeg_fin hfin).2
    · rw [hαB]; exact hdel t (hbaseP t ht) _
    · unfold ECh at hch; rw [hch, e_crossing_G, j_α_α, hB, e_crossing_W]
    · unfold ECh at hch; rw [hch, e_crossing_G]
      refine e_aboveVertex ⟨?_, ?_⟩ ?_
      · rw [show z = X.eP b' k + (X.eJ (X.eC b' k) - 1) by omega, e_W_pos k (by omega),
          e_curve_pc]
        exact hcurk
      · unfold Up; rw [e_W_side (by omega), hup]
      · show Γ.curve (X.eG b' z) ≠ Γ.S
        rw [e_G_curve (by omega) hzp]; exact hγS
    · rw [e_G_curve (hbaseN t ht) (hbaseP t ht), j_curve_α]
      exact fun h' => e_W_ne_γ (b' := b') (u := z + 1) hzN h'.symm
    · rw [hcrB, hposG t ht, hpos _ le_rfl]
      omega
    · unfold ECh at hchz
      rw [j_α_α, j_φ_apply, hchz, hB, e_W_port_succ hzp]
  -- three ports on one leg
  have three : ∀ (e' : X.D') (a b c : ℕ), a < X.eJ e' → b < X.eJ e' → c < X.eJ e' → a ≠ b →
      a ≠ c → b ≠ c → False := by
    intro e' a b c ha hb hc hab hac hbc
    rcases (by omega : (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨ (b < a ∧ a < c) ∨
        (b < c ∧ c < a) ∨ (c < a ∧ a < b) ∨ (c < b ∧ b < a)) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      exact e_three_ports e' h1 h2 (by omega)
  have hP0 : X.eP b' 0 = 0 := rfl
  have hJbC : X.eJ (X.eC b' 0) = X.eJ b' := rfl
  -- the first port `j` (next to `K`) and its chord
  have hp0 : X.EPort b' 0 := hbaseP 0 (by omega)
  obtain ⟨p, hpN, hpp, hch0⟩ := e_chord h34 hup e_N_pos hp0
  obtain ⟨i, hi, t, ht, rfl⟩ := e_port_classify hpN hpp
  -- a chord between the leg `eC b' 1` and the leg `eC b' i'` meets the first chord only at the end
  have hpos1 : 1 ≤ X.eP b' 1 := by rw [hP1]; omega
  rcases hM with hM | hM
  · -- hump: one leg `eC b' 1`, from `I` to `K`
    rw [hM] at hi
    interval_cases i
    · rw [hP0, zero_add] at hch0; rw [hJbC] at ht
      exact hump 0 t (by omega) ht hch0
    · set J1 := X.eJ (X.eC b' 1) with hJ1
      by_cases hz : t = J1 - 1
      · rw [hz, show X.eP b' 1 + (J1 - 1) = X.eP b' 1 + J1 - 1 by omega] at hch0
        exact triK 1 0 (by omega) (by omega) (by omega) hch0
      obtain ⟨hzp, hzN⟩ := e_port_of (b' := b') (i := 1) (t := J1 - 1) (by omega) (by omega)
      obtain ⟨q, hqN, hqp, hchz⟩ := e_chord h34 hup hzN hzp
      obtain ⟨i', hi', t', ht', rfl⟩ := e_port_classify hqN hqp
      rw [hM] at hi'
      interval_cases i'
      · rw [hP0, zero_add] at hchz; rw [hJbC] at ht'
        refine triK 1 t' (by omega) (by omega) ht' ?_
        rw [show X.eP b' 1 + J1 - 1 = X.eP b' 1 + (J1 - 1) by omega]
        exact e_ch_symm hchz
      · refine three (X.eC b' 1) t (J1 - 1) t' ht (by omega) ht' hz ?_ ?_
        · rintro rfl
          have := e_ch_unique e_N_pos hzN (e_ch_symm hch0) (e_ch_symm hchz)
          omega
        · rintro rfl
          exact e_ch_ne hchz
  · -- triangle: legs `L = eC b' 1` (from `I`) and `T = eC b' 2` (into `K`)
    rw [hM] at hi
    set J1 := X.eJ (X.eC b' 1) with hJ1
    set J2 := X.eJ (X.eC b' 2) with hJ2
    have hNv : N = X.eP b' 2 + J2 + 1 := by
      rw [hN]; unfold eN; rw [hM, e_P_succ]
    interval_cases i
    · rw [hP0, zero_add] at hch0; rw [hJbC] at ht
      exact hump 0 t (by omega) ht hch0
    · -- `j` is joined to the leg `L`
      by_cases ht0 : t = 0
      · rw [ht0, add_zero] at hch0
        exact triI 0 (by omega) (by omega) (by omega) hch0
      obtain ⟨hyp, hyN⟩ := e_port_of (b' := b') (i := 1) (t := 0) (by omega) (by omega)
      rw [add_zero] at hyp hyN
      obtain ⟨q, hqN, hqp, hchy⟩ := e_chord h34 hup hyN hyp
      obtain ⟨i', hi', t', ht', rfl⟩ := e_port_classify hqN hqp
      rw [hM] at hi'
      interval_cases i'
      · rw [hP0, zero_add] at hchy; rw [hJbC] at ht'
        exact triI t' ht' (by omega) (by omega) (e_ch_symm hchy)
      · refine three (X.eC b' 1) 0 t t' (by omega) ht ht' (Ne.symm ht0) ?_ ?_
        · rintro rfl
          exact e_ch_ne (by rw [add_zero] at hchy; exact hchy)
        · rintro rfl
          have := e_ch_unique e_N_pos hyN (e_ch_symm hch0) (e_ch_symm hchy)
          omega
      · exact e_noncross (a2 := X.eP b' 1 + t) (b := X.eP b' 1) (b2 := X.eP b' 2 + t')
          (by omega) (by omega) (by omega) hqN hp0 hpp hyp hch0 hchy
    · -- `j` is joined to the leg `T`
      by_cases hz : t = J2 - 1
      · rw [hz, show X.eP b' 2 + (J2 - 1) = X.eP b' 2 + J2 - 1 by omega] at hch0
        exact triK 2 0 (by omega) (by omega) (by omega) hch0
      obtain ⟨hzp, hzN⟩ := e_port_of (b' := b') (i := 2) (t := J2 - 1) (by omega) (by omega)
      obtain ⟨q, hqN, hqp, hchz⟩ := e_chord h34 hup hzN hzp
      obtain ⟨i', hi', t', ht', rfl⟩ := e_port_classify hqN hqp
      rw [hM] at hi'
      interval_cases i'
      · rw [hP0, zero_add] at hchz; rw [hJbC] at ht'
        refine triK 2 t' (by omega) (by omega) ht' ?_
        rw [show X.eP b' 2 + J2 - 1 = X.eP b' 2 + (J2 - 1) by omega]
        exact e_ch_symm hchz
      · exact e_noncross (a2 := X.eP b' 2 + t) (b := X.eP b' 1 + t')
          (b2 := X.eP b' 2 + (J2 - 1)) (by omega) (by omega) (by omega) hzN hp0 hpp hqp hch0
          (e_ch_symm hchz)
      · refine three (X.eC b' 2) t (J2 - 1) t' ht (by omega) ht' hz ?_ ?_
        · rintro rfl
          have := e_ch_unique e_N_pos hzN (e_ch_symm hch0) (e_ch_symm hchz)
          omega
        · rintro rfl
          exact e_ch_ne hchz

end Main

end Removal

end SConf

end Pca.Sweep
