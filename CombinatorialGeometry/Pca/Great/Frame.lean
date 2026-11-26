/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Frames and chords in great arrangements (`doc/pca/great.md` section 3.2)

A **frame** is a curve `c0` with a dart `β0` on it. `H` is the side of `c0` left of `β0`
(`s0 = 1`). Every other curve `e` meets `c0` first at position `p e < n - 1` along `β0` (and again
at `p e + (n - 1)`); its **chord** starts there with the dart `β e` into `H`, runs through
positions `0 < k < n - 1` in `H`, crosses `c0` at position `n - 1` and runs through `H'`. Two chords
`e ≠ f` cross once in `H`, at position `hpos e f` on `e` and `hpos f e` on `f`. `sR e` is the side
function of `e` with the cell right of `β e` on side `1`.
-/
import Pca.Great.Walk

open Equiv Finset

namespace Pca.Great

variable {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} {A : Arrangement n D}

/-- A frame: a curve `c0` and a dart `β0` on it. -/
structure Frame (A : Arrangement n D) where
  c0 : Fin n
  β0 : D
  curve_β0 : A.curve β0 = c0

/-- The positions property: `e` is met by the walk of `d` exactly at `k₁` and `k₁ + (n - 1)`. -/
def PosOf (A : Arrangement n D) (d : D) (e : Fin n) (k₁ : ℕ) : Prop :=
  k₁ < n - 1 ∧ ∀ j < 2 * (n - 1),
    e ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ j) d)) ↔
      j = k₁ ∨ j = k₁ + (n - 1)

open Classical in
/-- The first position of `e` along the walk of `d` (junk `0` if there is none). -/
noncomputable def firstPos (A : Arrangement n D) (d : D) (e : Fin n) : ℕ :=
  if h : ∃ k₁, PosOf A d e k₁ then Classical.choose h else 0

theorem posOf_firstPos (hA : A.IsGreat) (d : D) {e : Fin n} (he : e ≠ A.curve d) :
    PosOf A d e (firstPos A d e) := by
  have h : ∃ k₁, PosOf A d e k₁ := by
    obtain ⟨k, hk, h⟩ := pos_two hA d he
    exact ⟨k, hk, h⟩
  rw [firstPos, dif_pos h]
  exact Classical.choose_spec h

theorem PosOf.unique {d : D} {e : Fin n} {k k' : ℕ} (h : PosOf A d e k) (h' : PosOf A d e k') :
    k = k' := by
  have h1 := h.1
  have h2 := h'.1
  have := (h'.2 k (by omega)).1 ((h.2 k (by omega)).2 (Or.inl rfl))
  omega

/-- A side function of `C` normalized to be `1` on the cell `f`. -/
noncomputable def normSide (A : Arrangement n D) (C : Fin n) (f : A.Cell) : A.Cell → ZMod 2 :=
  let s := Classical.choose (Arrangement.exists_isSide (A := A) C)
  fun g => s g + s f + 1

theorem isSide_normSide (C : Fin n) (f : A.Cell) : A.IsSide C (normSide A C f) := by
  have hs := Classical.choose_spec (Arrangement.exists_isSide (A := A) C)
  intro y
  have h := hs y
  simp only [normSide]
  rw [← h]
  have : ∀ a b c : ZMod 2, a + c + 1 + (b + c + 1) = a + b := by decide
  exact this _ _ _

theorem normSide_self (C : Fin n) (f : A.Cell) : normSide A C f f = 1 := by
  simp only [normSide]
  have : ∀ a : ZMod 2, a + a + 1 = 1 := by decide
  exact this _

namespace Frame

variable (F : Frame A)

/-- The side function of `c0` with `H` (the side left of `β0`) on side `1`. -/
noncomputable def s0 : A.Cell → ZMod 2 := normSide A F.c0 (A.cellOf (A.α F.β0))

theorem isSide_s0 : A.IsSide F.c0 F.s0 := isSide_normSide _ _
theorem s0_left : F.s0 (A.cellOf (A.α F.β0)) = 1 := normSide_self _ _

/-- The first position of `e` on `c0`. -/
noncomputable def p (e : Fin n) : ℕ := firstPos A F.β0 e

/-- The start dart of the chord of `e`: at position `p e` of `c0`, on `e`, into `H`. -/
noncomputable def β (e : Fin n) : D := A.σ ((A.straight ^ F.p e) F.β0)

/-- The position of the `H`-crossing with `f` on the chord of `e`. -/
noncomputable def hpos (e f : Fin n) : ℕ := firstPos A (F.β e) f

/-- The side function of `e` with the cell right of `β e` on side `1`. -/
noncomputable def sR (e : Fin n) : A.Cell → ZMod 2 := normSide A e (A.cellOf (F.β e))

theorem isSide_sR (e : Fin n) : A.IsSide e (F.sR e) := isSide_normSide _ _
theorem sR_β (e : Fin n) : F.sR e (A.cellOf (F.β e)) = 1 := normSide_self _ _

variable (hA : A.IsGreat)
include hA

theorem posOf_p {e : Fin n} (he : e ≠ F.c0) : PosOf A F.β0 e (F.p e) :=
  posOf_firstPos hA F.β0 (by rw [F.curve_β0]; exact he)

theorem p_lt {e : Fin n} (he : e ≠ F.c0) : F.p e < n - 1 := (F.posOf_p hA he).1

theorem mem_curves_c0_iff {e : Fin n} (he : e ≠ F.c0) {k : ℕ} (hk : k < 2 * (n - 1)) :
    e ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ k) F.β0)) ↔
      k = F.p e ∨ k = F.p e + (n - 1) := (F.posOf_p hA he).2 k hk

theorem p_inj {e f : Fin n} (he : e ≠ F.c0) (hf : f ≠ F.c0) (h : F.p e = F.p f) : e = f := by
  have hn := A.two_le_n
  have h1 := (F.mem_curves_c0_iff hA he (k := F.p e) (by have := F.p_lt hA he; omega)).2
    (Or.inl rfl)
  have h2 := (F.mem_curves_c0_iff hA hf (k := F.p e) (by have := F.p_lt hA he; omega)).2
    (Or.inl h)
  have hc : F.c0 ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ F.p e) F.β0)) := by
    rw [← F.curve_β0, ← curve_straight_pow (F.p e) F.β0]; exact A.mem_curves_crossingOf _
  rw [A.curves_eq_pair hc h1 (Ne.symm he)] at h2
  simp only [mem_insert, mem_singleton] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 hf
  · exact h2.symm

theorem curve_β {e : Fin n} (he : e ≠ F.c0) : A.curve (F.β e) = e := by
  have hn := A.two_le_n
  have h1 := (F.mem_curves_c0_iff hA he (k := F.p e) (by have := F.p_lt hA he; omega)).2
    (Or.inl rfl)
  rw [A.curves_crossingOf, mem_insert, mem_singleton, curve_straight_pow, F.curve_β0] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 he
  · exact h1.symm

theorem mem_curves_chord {e : Fin n} (he : e ≠ F.c0) (k : ℕ) :
    e ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ k) (F.β e))) := by
  have := A.mem_curves_crossingOf ((A.straight ^ k) (F.β e))
  rwa [curve_straight_pow, F.curve_β hA he] at this

/-- The chord of `e` meets `c0` exactly at positions `0` and `n - 1`. -/
theorem posOf_c0 {e : Fin n} (he : e ≠ F.c0) : PosOf A (F.β e) F.c0 0 := by
  have hn := A.two_le_n
  have hpos := posOf_firstPos hA (F.β e) (e := F.c0) (by rw [F.curve_β hA he]; exact Ne.symm he)
  have h0 : F.c0 ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ 0) (F.β e))) := by
    rw [pow_zero, Perm.one_apply, β, A.crossingOf_σ, ← F.curve_β0,
      ← curve_straight_pow (F.p e) F.β0]
    exact A.mem_curves_crossingOf _
  have := (hpos.2 0 (by omega)).1 h0
  have hz : firstPos A (F.β e) F.c0 = 0 := by omega
  rw [hz] at hpos
  exact hpos

theorem c0_mem_chord_iff {e : Fin n} (he : e ≠ F.c0) {k : ℕ} (hk : k < 2 * (n - 1)) :
    F.c0 ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ k) (F.β e))) ↔
      k = 0 ∨ k = n - 1 := by
  rw [(F.posOf_c0 hA he).2 k hk, zero_add]

theorem posOf_hpos {e f : Fin n} (he : e ≠ F.c0) (hef : e ≠ f) :
    PosOf A (F.β e) f (F.hpos e f) :=
  posOf_firstPos hA (F.β e) (by rw [F.curve_β hA he]; exact Ne.symm hef)

/-- The `H`-crossing of two chords. -/
theorem hpos_spec {e f : Fin n} (he : e ≠ F.c0) (hf : f ≠ F.c0) (hef : e ≠ f) :
    0 < F.hpos e f ∧ F.hpos e f < n - 1 ∧
      f ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ F.hpos e f) (F.β e))) := by
  have hn := A.two_le_n
  have h := F.posOf_hpos hA he hef
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, h.1, (h.2 _ (by have := h.1; omega)).2 (Or.inl rfl)⟩
  have h1 := (h.2 0 (by omega)).2 (Or.inl h0.symm)
  have h2 := (F.c0_mem_chord_iff hA he (k := 0) (by omega)).2 (Or.inl rfl)
  have h3 := F.mem_curves_chord hA he 0
  rw [A.curves_eq_pair h3 h2 he] at h1
  simp only [mem_insert, mem_singleton] at h1
  rcases h1 with h1 | h1
  · exact hef h1.symm
  · exact hf h1

theorem hpos_unique {e f : Fin n} (he : e ≠ F.c0) (hef : e ≠ f) {k : ℕ} (hk : k < n - 1)
    (h : f ∈ Arrangement.Crossing.curves A (A.crossingOf ((A.straight ^ k) (F.β e)))) :
    k = F.hpos e f := by
  have hp := F.posOf_hpos hA he hef
  have := (hp.2 k (by omega)).1 h
  have := hp.1
  omega

/-- The chord of `e` runs in `H` for positions `k < n - 1` and in `H'` for the second half. -/
theorem s0_chord {e : Fin n} (he : e ≠ F.c0) {k : ℕ} (hk : k < 2 * (n - 1)) :
    F.s0 (A.cellOf ((A.straight ^ k) (F.β e))) = if k < n - 1 then 1 else 0 := by
  have hn := A.two_le_n
  rw [side_walk hA (F.β e) (by rw [F.curve_β hA he]; exact Ne.symm he) F.isSide_s0
    (F.posOf_c0 hA he).2 (by omega) hk]
  have hβ : F.s0 (A.cellOf (F.β e)) = 1 := by
    have h1 := F.isSide_s0 ((A.straight ^ F.p e) F.β0)
    have h2 := F.isSide_s0 F.β0
    rw [curve_straight_pow, F.curve_β0, if_pos rfl] at h1
    rw [F.curve_β0, if_pos rfl, F.s0_left] at h2
    rw [β, A.cellOf_σ, Arrangement.zmod2_eq_add_of_add_eq h1,
      side_straight_pow_self F.isSide_s0 F.curve_β0]
    exact h2
  rw [hβ, if_neg (by omega : ¬ (0 < 0 ∧ 0 ≤ k)), zero_add]
  by_cases h : k < n - 1
  · rw [if_neg (by omega), if_pos h]; norm_num
  · rw [if_pos (by omega), if_neg h]; decide

/-- The chords of `e` and `f` meet in `H` at the same crossing. -/
theorem crossingOf_hpos {e f : Fin n} (he : e ≠ F.c0) (hf : f ≠ F.c0) (hef : e ≠ f) :
    A.crossingOf ((A.straight ^ F.hpos e f) (F.β e)) =
      A.crossingOf ((A.straight ^ F.hpos f e) (F.β f)) := by
  have hn := A.two_le_n
  obtain ⟨h0, h1, h2⟩ := F.hpos_spec hA he hf hef
  obtain ⟨h0', h1', h2'⟩ := F.hpos_spec hA hf he (Ne.symm hef)
  have hce := F.mem_curves_chord hA he (F.hpos e f)
  have hcf := F.mem_curves_chord hA hf (F.hpos f e)
  by_contra hne
  have hs1 := F.s0_chord hA he (k := F.hpos e f) (by omega)
  have hs2 := F.s0_chord hA hf (k := F.hpos f e) (by omega)
  rw [if_pos h1] at hs1
  rw [if_pos h1'] at hs2
  have := hA e f F.c0 hef he hf F.s0 F.isSide_s0 _ _ hne
    (A.curves_eq_pair hce h2 hef) (A.curves_eq_pair h2' hcf hef)
    _ (Orbit.mem_darts.2 rfl) _ (Orbit.mem_darts.2 rfl)
  exact this (hs1.trans hs2.symm)

/-- The side of `e` along `c0`: the cells along `β0` lie right of `e` (side `1`) exactly between
the two crossings with `e` after `p e`. -/
theorem sR_c0 {e : Fin n} (he : e ≠ F.c0) {k : ℕ} (hk : k < n - 1) :
    F.sR e (A.cellOf ((A.straight ^ k) F.β0)) = if F.p e ≤ k then 1 else 0 := by
  have hn := A.two_le_n
  have hp := F.posOf_p hA he
  have hw := fun j (hj : j < 2 * (n - 1)) => side_walk hA F.β0 (by rw [F.curve_β0]; exact he)
    (F.isSide_sR e) hp.2 hp.1 hj
  -- at position `p e` the cell right of the `c0`-dart is the cell right of `β e`
  have hpe : F.sR e (A.cellOf ((A.straight ^ F.p e) F.β0)) = 1 := by
    have h1 := F.isSide_sR e ((A.straight ^ F.p e) F.β0)
    rw [curve_straight_pow, F.curve_β0, if_neg (Ne.symm he)] at h1
    have key : ∀ a b : ZMod 2, a + b = 0 → b = 1 → a = 1 := by decide
    exact key _ _ h1 (by rw [← A.cellOf_σ]; exact F.sR_β e)
  have hp1 := hp.1
  have h1 := hw k (by omega)
  have h2 := hw (F.p e) (by omega)
  rw [hpe] at h2
  rw [h1]
  by_cases h0 : 0 < F.p e
  · rw [if_pos ⟨h0, le_rfl⟩, if_neg (by omega)] at h2
    by_cases hle : F.p e ≤ k
    · rw [if_pos ⟨h0, hle⟩, if_neg (by omega), if_pos hle]
      have : ∀ a : ZMod 2, 1 = a + (1 + 0) → a + (1 + 0) = 1 := fun a h => h.symm
      exact this _ h2
    · rw [if_neg (fun h => hle h.2), if_neg (by omega), if_neg hle]
      have : ∀ a : ZMod 2, 1 = a + (1 + 0) → a + (0 + 0) = 0 := by decide
      exact this _ h2
  · rw [if_neg (fun h => h0 h.1), if_neg (by omega)] at h2
    rw [if_neg (fun h => h0 h.1), if_neg (by omega), if_pos (by omega)]
    have : ∀ a : ZMod 2, 1 = a + (0 + 0) → a + (0 + 0) = 1 := fun a h => h.symm
    exact this _ h2

/-- **Side along a chord**: walking along the chord of `f` in `H`, the side of `e` starts right of
`e` iff `p e < p f` and changes once, at the crossing with `e`. -/
theorem sR_chord {e f : Fin n} (he : e ≠ F.c0) (hf : f ≠ F.c0) (hef : e ≠ f) {k : ℕ}
    (hk : k < n - 1) :
    F.sR e (A.cellOf ((A.straight ^ k) (F.β f))) =
      (if F.p e < F.p f then 1 else 0) + (if F.hpos f e ≤ k then 1 else 0) := by
  have hn := A.two_le_n
  have hp := F.posOf_hpos hA hf (Ne.symm hef)
  obtain ⟨h0, -, -⟩ := F.hpos_spec hA hf he (Ne.symm hef)
  rw [side_walk hA (F.β f) (by rw [F.curve_β hA hf]; exact hef) (F.isSide_sR e) hp.2 hp.1
    (by omega : k < 2 * (n - 1))]
  have hstart : F.sR e (A.cellOf (F.β f)) = if F.p e < F.p f then 1 else 0 := by
    have h1 := F.isSide_sR e ((A.straight ^ F.p f) F.β0)
    rw [curve_straight_pow, F.curve_β0, if_neg (Ne.symm he)] at h1
    have key : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
    rw [β, A.cellOf_σ, key _ _ h1, F.sR_c0 hA he (F.p_lt hA hf)]
    have hne : F.p e ≠ F.p f := fun h => hef (F.p_inj hA he hf h)
    by_cases h : F.p e < F.p f
    · rw [if_pos h.le, if_pos h]
    · rw [if_neg (by omega), if_neg h]
  rw [hstart, if_neg (show ¬ (F.hpos f e + (n - 1) ≤ k) by omega), add_zero]
  congr 1
  by_cases h : F.hpos f e ≤ k
  · rw [if_pos ⟨h0, h⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2), if_neg h]

/-- **Sign lemma**: at their `H`-crossing, `f` crosses `e` from right to left iff `p e < p f`. -/
theorem σ_hpos {e f : Fin n} (he : e ≠ F.c0) (hf : f ≠ F.c0) (hef : e ≠ f) :
    A.σ ((A.straight ^ F.hpos e f) (F.β e)) =
      if F.p e < F.p f then (A.straight ^ F.hpos f e) (F.β f)
      else A.σ (A.σ ((A.straight ^ F.hpos f e) (F.β f))) := by
  have hn := A.two_le_n
  set z := (A.straight ^ F.hpos e f) (F.β e)
  set w := (A.straight ^ F.hpos f e) (F.β f)
  obtain ⟨-, h1', -⟩ := F.hpos_spec hA hf he (Ne.symm hef)
  have hx : A.crossingOf z = A.crossingOf w := F.crossingOf_hpos hA he hf hef
  have hcz : A.curve z = e := by rw [curve_straight_pow, F.curve_β hA he]
  have hcw : A.curve w = f := by rw [curve_straight_pow, F.curve_β hA hf]
  -- sides of `e`
  have hz : F.sR e (A.cellOf (A.σ z)) = 0 := by
    have h1 := F.isSide_sR e z
    rw [hcz, if_pos rfl] at h1
    rw [A.cellOf_σ, Arrangement.zmod2_eq_add_of_add_eq h1,
      side_straight_pow_self (F.isSide_sR e) (F.curve_β hA he), F.sR_β]
    decide
  have hw : F.sR e (A.cellOf w) = (if F.p e < F.p f then 1 else 0) + 1 := by
    rw [F.sR_chord hA he hf hef h1', if_pos le_rfl]
  -- `σ w` is on `e`
  have hσw : A.curve (A.σ w) = e := by
    have hm : e ∈ Arrangement.Crossing.curves A (A.crossingOf w) := by
      rw [← hx, ← hcz]; exact A.mem_curves_crossingOf z
    rw [A.curves_crossingOf, mem_insert, mem_singleton, hcw] at hm
    rcases hm with hm | hm
    · exact absurd hm hef
    · exact hm.symm
  have hww : F.sR e (A.cellOf (A.σ (A.σ w))) = F.sR e (A.cellOf w) + 1 := by
    rw [A.side_σσ (F.isSide_sR e), hcw, if_neg (Ne.symm hef), hσw, if_pos rfl, add_zero]
  have hσz : A.curve (A.σ z) = f := by
    have hm : f ∈ Arrangement.Crossing.curves A (A.crossingOf z) := by
      rw [hx, ← hcw]; exact A.mem_curves_crossingOf w
    rw [A.curves_crossingOf, mem_insert, mem_singleton, hcz] at hm
    rcases hm with hm | hm
    · exact absurd hm.symm hef
    · exact hm.symm
  have hcases : A.σ z = w ∨ A.σ z = A.σ (A.σ w) := by
    have hl := A.crossingOf_eq_iff.1 hx.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with h | h | h | h
    · exact absurd (hcz.symm.trans (h ▸ hcw)) hef
    · right; rw [h]
    · exact absurd (hcz.symm.trans (by rw [h, A.isArrangement.curve_σσ, hcw])) hef
    · left; rw [h, A.σ_σ_σ_σ]
  by_cases hp : F.p e < F.p f
  · rw [if_pos hp]
    rcases hcases with h | h
    · exact h
    · exfalso
      rw [h, hww, hw, if_pos hp] at hz
      exact absurd hz (by decide)
  · rw [if_neg hp]
    rcases hcases with h | h
    · exfalso
      rw [h, hw, if_neg hp] at hz
      exact absurd hz (by decide)
    · exact h

end Frame

end Pca.Great
