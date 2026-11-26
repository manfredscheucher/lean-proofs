/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package E (SH Lemma 3.7), chords of `γ` inside a cell of `Γ − γ`

`X` removes one curve `γ`; `b'` is a dart of `Γ − γ` whose cell `F'` lies above the sweep. A
**port** is a position `u` of the boundary walk `eW b'` whose piece ends at a crossing with `γ`;
`eG b' u = σ (α (eW b' u))` is the dart of `γ` there that points into `F'`.

* **chord lemma** (`e_chord`, Step 2 of `doc/pca/sweep.md`): the edge of `γ` entering `F'` at a
  port leaves it at another port: `α (eG u) = eG v`. Uses the cut `e_inside` and, for the dart at
  the far end of the chord, that it is a piece of a dart of `Γ − γ` (`e_piece_exists`, from SH
  Lemma 3.4);
* **noncrossing lemma** (`e_noncross`): two chords `0 – a2` and `b – b2` with
  `0 < b < a2 < b2` do not exist (a second Jordan cut, along the chord `eG 0` and the boundary from
  `a2` back to `0`).
-/
import Pca.Sweep.E_Face

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D} {γ : Fin n}

namespace Removal

variable {X : Γ.Removal {γ}} {b' : X.D'}

variable (X b') in
/-- The dart of `γ` at the end of the piece at position `u`, pointing into the cell. -/
noncomputable def eG (u : ℕ) : D := Γ.σ (Γ.α (X.eW b' u))

variable (X b') in
/-- Position `u` is a port: its piece ends at a crossing with `γ`. -/
def EPort (u : ℕ) : Prop := ¬ Γ.rK {γ} (Γ.α (X.eW b' u))

variable (X b') in
/-- A chord from port `u` to port `v`. -/
def ECh (u v : ℕ) : Prop := Γ.α (X.eG b' u) = X.eG b' v

theorem e_ch_symm {u v : ℕ} (h : X.ECh b' u v) : X.ECh b' v u := by
  unfold ECh at *; rw [← h, j_α_α]

theorem e_G_inj {u v : ℕ} (hu : u < X.eN b') (hv : v < X.eN b') (h : X.eG b' u = X.eG b' v) :
    u = v := by
  unfold eG at h
  exact e_W_inj hu hv (Γ.α.injective (Γ.σ.injective h))

theorem e_ch_unique {u v w : ℕ} (hv : v < X.eN b') (hw : w < X.eN b') (h1 : X.ECh b' u v)
    (h2 : X.ECh b' u w) : v = w := by
  unfold ECh at h1 h2; exact e_G_inj hv hw (h1.symm.trans h2)

theorem e_ch_ne {u : ℕ} (h : X.ECh b' u u) : False := Γ.isSConf.α_ne _ h

theorem e_G_curve {u : ℕ} (hu : u < X.eN b') (hp : X.EPort b' u) : Γ.curve (X.eG b' u) = γ := by
  have hd : Γ.Deleted {γ} (Γ.crossingOf (Γ.α (X.eW b' u))) := not_not.1 hp
  rw [r_deleted_iff, j_curve_α] at hd
  rcases hd with h | h
  · exact absurd h (e_W_curve hu)
  · exact mem_singleton.1 h

theorem e_W_ne_γ {u : ℕ} (hu : u < X.eN b') : Γ.curve (X.eW b' u) ≠ γ := fun h =>
  e_W_curve hu (mem_singleton.2 h)

theorem e_cell_G (u : ℕ) : Γ.cellOf (X.eG b' u) = Γ.cellOf (X.eW b' u) := Γ.j_cellOf_φ _

theorem e_crossing_G (u : ℕ) : Γ.crossingOf (X.eG b' u) = Γ.crossingOf (Γ.α (X.eW b' u)) :=
  j_crossingOf_σ _ _

theorem e_W_port_succ {u : ℕ} (hp : X.EPort b' u) : X.eW b' (u + 1) = Γ.σ (X.eG b' u) := by
  rw [e_W_succ_port hp]; rfl

theorem e_N_pos : 0 < X.eN b' := by
  have h := e_P_mono (X := X) (b' := b') (show 1 ≤ X.eM b' from period_pos _ _)
  unfold eN; simp only [eP] at h; omega

theorem e_W_norm {p : ℕ} (hp : p ≤ X.eN b') : ∃ q < X.eN b', X.eW b' p = X.eW b' q := by
  rcases Nat.lt_or_ge p (X.eN b') with h | h
  · exact ⟨p, h, rfl⟩
  · exact ⟨0, e_N_pos, by rw [show p = X.eN b' by omega, e_W_N]⟩

theorem e_W_inj1 {p q : ℕ} (hp0 : 0 < p) (hp : p ≤ X.eN b') (hq0 : 0 < q) (hq : q ≤ X.eN b')
    (h : X.eW b' p = X.eW b' q) : p = q := by
  have key : ∀ {p q : ℕ}, 0 < p → p ≤ X.eN b' → 0 < q → q < X.eN b' →
      X.eW b' p = X.eW b' q → p = q := by
    intro p q hp0 hp hq0 hq h
    rcases Nat.lt_or_ge p (X.eN b') with h1 | h1
    · exact e_W_inj h1 hq h
    · rw [show p = X.eN b' by omega, e_W_N] at h
      have := e_W_inj e_N_pos hq h; omega
  rcases Nat.lt_or_ge q (X.eN b') with h2 | h2
  · exact key hp0 hp hq0 h2 h
  · rcases Nat.lt_or_ge p (X.eN b') with h1 | h1
    · exact (key hq0 hq hp0 h1 h.symm).symm
    · omega

/-! ## The chord lemma -/

/-- **Chord lemma.** -/
theorem e_chord (h34 : ∀ δ, Γ.Present δ → Γ.MeetsSweep δ)
    (hup : X.Γ'.side (X.Γ'.cellOf b') = 1) {u : ℕ} (hu : u < X.eN b') (hp : X.EPort b' u) :
    ∃ v < X.eN b', X.EPort b' v ∧ X.ECh b' u v := by
  classical
  obtain ⟨r, hcut, hind⟩ := e_inside (X := X) (b' := b')
  have hrR : ∀ w, Γ.curve w ∈ ({γ} : Finset (Fin n)) →
      r (Γ.cellOf (Γ.α w)) = r (Γ.cellOf w) := by
    intro w hw
    have h := hcut w
    rw [if_neg] at h
    · exact (j_zmod2_eq_add_of_add_eq h).trans (add_zero _)
    · rw [e_mem_E]
      rintro ⟨u, hu, h1 | h1⟩
      · exact e_W_curve hu (h1 ▸ hw)
      · exact e_W_curve hu (by rw [← j_curve_α, ← h1]; exact hw)
  set g := X.eG b' u with hgdef
  set e := Γ.σ (Γ.α g) with hedef
  have hg : Γ.curve g = γ := e_G_curve hu hp
  have heR : Γ.curve e ∉ ({γ} : Finset (Fin n)) := by
    rw [mem_singleton, hedef]
    intro h
    exact no_curve_σ_ne (Γ := Γ) (Γ.α g) (by rw [h, j_curve_α, hg])
  have hce : Γ.cellOf e = Γ.cellOf (X.eW b' u) := by
    rw [hedef, ← j_φ_apply, Γ.j_cellOf_φ, hgdef, e_cell_G]
  have hupe : Γ.Up (Γ.cellOf e) := by
    unfold Up; rw [hce, e_W_side hu, hup]
  have : Nonempty X.D' := ⟨b'⟩
  obtain ⟨e'', t, ht, hpe⟩ := e_piece_exists (X := X) h34 heR hupe
  -- `e''` is in the cell
  have hr1 : r (Γ.cellOf (X.eW b' u)) = 1 := by
    obtain ⟨i, -, t0, ht0, rfl⟩ := e_decomp hu
    rw [e_W_pos i ht0, e_cell_pc r hrR _ ht0, hind, if_pos (e_C_cell i)]
  have hin : X.Γ'.cellOf e'' = X.Γ'.cellOf b' := by
    have h := hind e''
    rw [← e_cell_pc r hrR e'' ht, hpe, hce, hr1] at h
    by_contra hne
    rw [if_neg hne] at h
    exact absurd h (by decide)
  obtain ⟨k, hk, rfl⟩ := e_C_of_cell hin
  -- `e` starts at a crossing with `γ`, so it is not a first piece
  have ht0 : t ≠ 0 := by
    rintro rfl
    have hK : Γ.rK {γ} (X.ePc (X.eC b' k) 0) := e_rK _
    rw [hpe] at hK
    apply hK
    refine ⟨γ, mem_singleton_self _, ?_⟩
    show γ ∈ Γ.curves (Γ.crossingOf e)
    rw [hedef, j_crossingOf_σ, j_curves_crossingOf, j_curve_α, hg]
    exact mem_insert_self _ _
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  refine ⟨X.eP b' k + s, lt_of_lt_of_le (by omega) (e_P_last_lt hk).le, ?_, ?_⟩
  · unfold EPort
    rw [e_W_pos k (by omega)]
    intro h
    have := (e_pc_rK (by omega)).1 h
    omega
  · unfold ECh eG
    rw [e_W_pos k (by omega)]
    rw [e_pc_succ, j_straight_apply] at hpe
    exact (Γ.σ.injective hpe).symm

/-! ## The noncrossing lemma -/

/-- A function on positions that does not change in a range is constant there. -/
theorem e_const_of_step (F : ℕ → ZMod 2) {lo hi : ℕ} (h : ∀ u, lo ≤ u → u < hi → F (u + 1) = F u) :
    ∀ u, lo ≤ u → u ≤ hi → F u = F lo := by
  intro u hlo hhi
  induction u with
  | zero => rw [Nat.le_zero.1 hlo]
  | succ u ih =>
    rcases Nat.eq_or_lt_of_le hlo with h0 | h0
    · rw [h0]
    · rw [h u (by omega) (by omega), ih (by omega) (by omega)]

/-- **Noncrossing lemma.** Chords `0 – a2` and `b – b2` with `0 < b < a2 < b2` cross; they do not
exist. -/
theorem e_noncross {a2 b b2 : ℕ} (hb0 : 0 < b) (hba : b < a2) (hab : a2 < b2)
    (hb2 : b2 < X.eN b') (hp0 : X.EPort b' 0) (hpa : X.EPort b' a2) (hpb : X.EPort b' b)
    (h1 : X.ECh b' 0 a2) (h2 : X.ECh b' b b2) : False := by
  classical
  set N := X.eN b' with hN
  set K := N - a2 with hK
  set M2 := K + 1 with hM2
  set c := X.eG b' 0 with hc
  have hcγ : Γ.curve c = γ := e_G_curve e_N_pos hp0
  set w2 : ℕ → D := fun i => if i % M2 < K then X.eW b' (a2 + 1 + i % M2) else c with hw2
  have hw2lt : ∀ i, i < K → w2 i = X.eW b' (a2 + 1 + i) := by
    intro i hi
    simp only [hw2, Nat.mod_eq_of_lt (show i < M2 by omega), if_pos hi]
  have hw2K : w2 K = c := by
    simp only [hw2, Nat.mod_eq_of_lt (show K < M2 by omega), lt_irrefl, if_false]
  have hw2M : w2 M2 = w2 0 := by
    show (if M2 % M2 < K then _ else c) = (if 0 % M2 < K then _ else c)
    rw [Nat.mod_self, Nat.zero_mod]
  have hcases : ∀ i, i < M2 → (i < K ∧ w2 i = X.eW b' (a2 + 1 + i)) ∨ (i = K ∧ w2 i = c) := by
    intro i hi
    rcases Nat.lt_or_ge i K with h | h
    · exact Or.inl ⟨h, hw2lt i h⟩
    · exact Or.inr ⟨by omega, by rw [show i = K by omega]; exact hw2K⟩
  have hWcurve : ∀ p, p ≤ N → Γ.curve (X.eW b' p) ≠ γ := by
    intro p hp
    obtain ⟨q, hq, he⟩ := e_W_norm hp
    rw [he]; exact e_W_ne_γ hq
  -- the walk is closed and even
  have hcross : ∀ t < M2, Γ.crossingOf (w2 (t + 1)) = Γ.crossingOf (Γ.α (w2 t)) := by
    intro t ht
    rcases Nat.lt_or_ge (t + 1) K with h | h
    · rw [hw2lt _ h, hw2lt _ (by omega), show a2 + 1 + (t + 1) = (a2 + 1 + t) + 1 by omega]
      exact e_crossing_W _
    · rcases Nat.eq_or_lt_of_le h with h' | h'
      · rw [← h', hw2K, hw2lt _ (by omega), show a2 + 1 + t = N by omega, e_W_N, hc,
          e_crossing_G]
      · rw [show t + 1 = M2 by omega, hw2M, show t = K by omega, hw2K, hw2lt _ (by omega),
          add_zero]
        unfold ECh at h1
        rw [h1, e_crossing_G, e_crossing_W]
  have hinj : ∀ s < M2, ∀ t < M2, w2 s = w2 t → s = t := by
    intro s hs t ht h
    rcases hcases s hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩ <;>
      rcases hcases t ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
    · rw [hs2, ht2] at h
      have := e_W_inj1 (by omega) (by omega) (by omega) (by omega) h
      omega
    · rw [hs2, ht2] at h
      exact absurd (h ▸ hcγ) (hWcurve _ (by omega))
    · rw [hs2, ht2] at h
      exact absurd (h.symm ▸ hcγ) (hWcurve _ (by omega))
    · omega
  have hαne : ∀ s < M2, ∀ t < M2, Γ.α (w2 s) ≠ w2 t := by
    intro s hs t ht h
    rcases hcases s hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩ <;>
      rcases hcases t ht with ⟨ht1, ht2⟩ | ⟨ht1, ht2⟩
    · rw [hs2, ht2] at h
      obtain ⟨p, hp, hpe⟩ := e_W_norm (b' := b') (show a2 + 1 + s ≤ N by omega)
      obtain ⟨q, hq, hqe⟩ := e_W_norm (b' := b') (show a2 + 1 + t ≤ N by omega)
      rw [hpe, hqe] at h
      exact e_W_α hp hq h
    · rw [hs2, ht2] at h
      apply hWcurve (a2 + 1 + s) (by omega)
      rw [← j_curve_α, h, hcγ]
    · rw [hs2, ht2] at h
      apply hWcurve (a2 + 1 + t) (by omega)
      rw [← h, j_curve_α, hcγ]
    · rw [hs2, ht2] at h
      exact Γ.isSConf.α_ne _ h
  have heven := e_even w2 M2 hcross hw2M hinj hαne
  obtain ⟨r, hr⟩ := Γ.exists_cut _ heven
  set E2 := (range M2).image (fun t => Γ.segmentOf (w2 t))
  -- which chords are on the walk
  have hmem : ∀ u < N, X.EPort b' u → (Γ.segmentOf (X.eG b' u) ∈ E2 ↔ u = 0 ∨ u = a2) := by
    intro u hu hpu
    have hgu := e_G_curve hu hpu
    constructor
    · intro hm
      obtain ⟨i, hi, he⟩ := mem_image.1 hm
      rw [j_segmentOf_eq_iff] at he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases hcases i (mem_range.1 hi) with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩
      · rw [hi2] at he
        rcases he with he | he
        · exact absurd (he ▸ hgu) (hWcurve _ (by omega))
        · exact absurd (by rw [← j_curve_α, ← he, hgu]) (hWcurve (a2 + 1 + i) (by omega))
      · rw [hi2] at he
        rcases he with he | he
        · exact Or.inl (e_G_inj hu e_N_pos he)
        · unfold ECh at h1
          rw [h1] at he
          exact Or.inr (e_G_inj hu (by omega) he)
    · rintro (rfl | rfl)
      · exact mem_image.2 ⟨K, mem_range.2 (by omega), by rw [hw2K]⟩
      · refine mem_image.2 ⟨K, mem_range.2 (by omega), ?_⟩
        rw [hw2K, hc, ← h1, j_segmentOf_α]
  set F : ℕ → ZMod 2 := fun u => r (Γ.cellOf (X.eW b' u)) with hF
  have hstep : ∀ u < N, F (u + 1) = F u +
      if X.EPort b' u ∧ Γ.segmentOf (X.eG b' u) ∈ E2 then 1 else 0 := by
    intro u hu
    by_cases hpu : X.EPort b' u
    · simp only [hF]
      rw [e_W_port_succ hpu, j_cellOf_σ, ← e_cell_G u]
      have := hr (X.eG b' u)
      rw [j_zmod2_eq_add_of_add_eq this]
      by_cases hm : Γ.segmentOf (X.eG b' u) ∈ E2
      · rw [if_pos hm, if_pos ⟨hpu, hm⟩]
      · rw [if_neg hm, if_neg (fun h => hm h.2)]
    · simp only [hF]
      rw [e_W_succ_corner (not_not.1 hpu), Γ.j_cellOf_φ, if_neg (fun h => hpu h.1), add_zero]
  have hflat : ∀ u < N, u ≠ 0 → u ≠ a2 → F (u + 1) = F u := by
    intro u hu h0 ha
    rw [hstep u hu, if_neg, add_zero]
    rintro ⟨hpu, hm⟩
    rcases (hmem u hu hpu).1 hm with h | h <;> contradiction
  have hc1 : F b = F a2 := by
    have := e_const_of_step F (lo := b) (hi := a2) (fun u h1 h2 => hflat u (by omega) (by omega)
      (by omega)) a2 hba.le le_rfl
    exact this.symm
  have hc2 : F b2 = F (a2 + 1) :=
    e_const_of_step F (lo := a2 + 1) (hi := b2) (fun u h1 h2 => hflat u (by omega) (by omega)
      (by omega)) b2 (by omega) le_rfl
  have hc3 : F (a2 + 1) = F a2 + 1 := by
    rw [hstep a2 (by omega), if_pos ⟨hpa, (hmem a2 (by omega) hpa).2 (Or.inr rfl)⟩]
  have hc4 : F b = F b2 := by
    have := hr (X.eG b' b)
    rw [if_neg (fun hm => by
      rcases (hmem b (by omega) hpb).1 hm with h | h <;> omega), e_cell_G] at this
    unfold ECh at h2
    rw [h2, e_cell_G] at this
    simp only [hF]
    exact ((j_zmod2_eq_add_of_add_eq this).trans (add_zero _)).symm
  have : F a2 = F a2 + 1 := by rw [← hc3, ← hc2, ← hc4, hc1]
  exact absurd (add_left_cancel (a := F a2) (b := 0) (c := 1) (by rw [add_zero]; exact this))
    (by decide)

end Removal

end SConf

end Pca.Sweep
