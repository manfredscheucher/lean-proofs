/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Package C: the region of a hump or of a convex triangle (Lemma 3.6)

The region is cut out by the closed walk `S[k, l]` followed by the hump (from `l` back to `k`) or
by the legs `⟨l, v⟩`, `⟨v, k⟩` (`c_even_walk`, `c_lid_cut`, Jordan `exists_cut`). The data
`CLid` of `Pca/Sweep/C_Core.lean` is checked for both (`c_hump_core`, `c_tri_core`); for the
triangle, "convex" (`φ a = α b`: the region at `v` is the angle between the legs) is what makes
the curves of the legs leave the region at `v` (`c_leg`). If no vertex lies strictly between `k`
and `l`, the hump or triangle is itself the cell above `[k, k + 1]`.
-/
import Pca.Sweep.C_Trans

open Equiv Finset

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-! ## Small facts -/

theorem c_period_two (f : Perm D) (x : D) (h1 : f x ≠ x) (h2 : f (f x) = x) :
    period f x = 2 := by
  show Nat.find (exists_iterate_eq f x) = 2
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, h2⟩, ?_⟩
  rintro m hm ⟨hm0, hfm⟩
  interval_cases m
  exact h1 hfm

theorem c_period_three (f : Perm D) (x : D) (h1 : f x ≠ x) (h2 : f (f x) ≠ x)
    (h3 : f (f (f x)) = x) : period f x = 3 := by
  show Nat.find (exists_iterate_eq f x) = 3
  rw [Nat.find_eq_iff]
  refine ⟨⟨by norm_num, h3⟩, ?_⟩
  rintro m hm ⟨hm0, hfm⟩
  interval_cases m
  · exact h1 hfm
  · exact h2 hfm

theorem c_curve_seg {a b : D} (h : Γ.segmentOf a = Γ.segmentOf b) : Γ.curve b = Γ.curve a := by
  have := (j_segmentOf_eq_iff Γ).1 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl
  · rfl
  · exact j_curve_α Γ a

theorem c_not_sweep_α {s : D} (hs : Γ.IsSweepDart s) : ¬ Γ.IsSweepDart (Γ.α s) := by
  intro h
  have h0 := (no_sweep_iff hs.1).1 hs
  have h1 : Γ.side (Γ.cellOf (Γ.α (Γ.α s))) = 1 := h.2
  rw [j_α_α, h0] at h1
  exact absurd h1 (by decide)

theorem c_crossing_α_noC (z : D) (t : ℕ) :
    Γ.crossingOf (Γ.α (Γ.noC z t)) = Γ.crossingOf (Γ.noC z (t + 1)) := by
  rw [← no_crossingOf_α_straight, no_noC_straight]

theorem c_S_mem_σ_noC {z : D} (hz : Γ.infStart = some z) (t : ℕ) :
    Γ.S ∈ Γ.curves (Γ.crossingOf (Γ.σ (Γ.noC z t))) := by
  rw [j_crossingOf_σ]; exact no_S_mem_noC hz t

theorem c_σ_noC_inj {z : D} {t s : ℕ} (ht : t < period Γ.straight z)
    (hs : s < period Γ.straight z) (h : Γ.σ (Γ.noC z t) = Γ.σ (Γ.noC z s)) : t = s :=
  no_noC_inj' ht hs (Γ.σ.injective h)

/-- The above dart at a vertex on the sweep. -/
theorem c_eq_σ_noC {z : D} (hz : Γ.infStart = some z) {y : D} (hy : Γ.Above y) {t : ℕ}
    (hc : Γ.crossingOf y = Γ.crossingOf (Γ.noC z t)) : y = Γ.σ (Γ.noC z t) := by
  have hS : Γ.S ∈ Γ.curves (Γ.crossingOf y) := by rw [hc]; exact no_S_mem_noC hz t
  obtain ⟨hsw, hσ⟩ := no_sweep_of_above hy hS
  have := no_sweep_unique (no_noC_sweep hz t) hsw
    (by rw [j_crossingOf_σ, j_crossingOf_σ, j_crossingOf_σ, hc])
  rw [← hσ, this]

/-- `lidX` at a lid dart starting on `S`. -/
theorem c_lidX_S {z : D} (hz : Γ.infStart = some z) {Lid : Finset D} {t : ℕ}
    (hy : Γ.σ (Γ.noC z t) ∈ Lid) (w : D)
    (hw : Γ.crossingOf w = Γ.crossingOf (Γ.σ (Γ.noC z t))) :
    Γ.curve w = Γ.S ∨ ∃ y' ∈ Lid, Γ.curve y' = Γ.curve w := by
  have hm : Γ.curve w ∈ Γ.curves (Γ.crossingOf w) := by
    rw [j_curves_crossingOf]; exact mem_insert_self _ _
  rw [hw, j_curves_crossingOf, mem_insert, mem_singleton, j_curve_σσ,
    (no_noC_sweep hz t).1] at hm
  rcases hm with hm | hm
  · exact Or.inr ⟨_, hy, hm.symm⟩
  · exact Or.inl hm

/-! ## Jordan: the segments of a closed walk -/

/-- The segments of a closed walk with distinct segments form an even set. -/
theorem c_even_walk {m : ℕ} (hm : 0 < m) (w : ℕ → D)
    (hw : ∀ i < m, Γ.crossingOf (Γ.α (w i)) = Γ.crossingOf (w ((i + 1) % m)))
    (hinj : ∀ i < m, ∀ j < m, Γ.segmentOf (w i) = Γ.segmentOf (w j) → i = j) :
    Γ.IsEven ((range m).image (fun i => Γ.segmentOf (w i))) := by
  intro x
  set E := (range m).image (fun i => Γ.segmentOf (w i))
  set A := (range m).filter (fun i => Γ.crossingOf (w i) = x)
  set B := (range m).filter (fun i => Γ.crossingOf (Γ.α (w i)) = x)
  have hmem : ∀ y, y ∈ x.darts ↔ Γ.crossingOf y = x := fun y => Orbit.mem_darts
  have hmod : ∀ i < m, (i + 1) % m = if i + 1 = m then 0 else i + 1 := by
    intro i hi
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  have hF : x.darts.filter (fun y => Γ.segmentOf y ∈ E) =
      A.image w ∪ B.image (fun i => Γ.α (w i)) := by
    ext y
    simp only [mem_filter, hmem, E, mem_image, mem_range, mem_union, A, B]
    constructor
    · rintro ⟨hy, i, hi, hs⟩
      have := (j_segmentOf_eq_iff Γ).1 hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with rfl | rfl
      · exact Or.inl ⟨i, ⟨hi, hy⟩, rfl⟩
      · exact Or.inr ⟨i, ⟨hi, hy⟩, rfl⟩
    · rintro (⟨i, ⟨hi, hy⟩, rfl⟩ | ⟨i, ⟨hi, hy⟩, rfl⟩)
      · exact ⟨hy, i, hi, rfl⟩
      · exact ⟨hy, i, hi, (j_segmentOf_α Γ _).symm⟩
  have hdisj : Disjoint (A.image w) (B.image (fun i => Γ.α (w i))) := by
    rw [disjoint_left]
    intro y hyA hyB
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hyA
    obtain ⟨j, hj, he⟩ := mem_image.1 hyB
    have hij := hinj j (mem_range.1 (mem_filter.1 hj).1) i (mem_range.1 (mem_filter.1 hi).1)
      (by rw [← he, j_segmentOf_α])
    subst hij
    exact Γ.isSConf.α_ne _ he
  have hcA : (A.image w).card = A.card := by
    refine card_image_of_injOn fun i hi j hj he => ?_
    exact hinj i (mem_range.1 (mem_filter.1 hi).1) j (mem_range.1 (mem_filter.1 hj).1)
      (congrArg Γ.segmentOf he)
  have hcB : (B.image (fun i => Γ.α (w i))).card = B.card := by
    refine card_image_of_injOn fun i hi j hj he => ?_
    exact hinj i (mem_range.1 (mem_filter.1 hi).1) j (mem_range.1 (mem_filter.1 hj).1)
      (congrArg Γ.segmentOf (Γ.α.injective he))
  have hBA : B.card = A.card := by
    refine card_nbij' (fun i => (i + 1) % m) (fun i => if i = 0 then m - 1 else i - 1)
      ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨hi, hc⟩ := mem_filter.1 hi
      rw [mem_range] at hi
      exact mem_filter.2 ⟨mem_range.2 (Nat.mod_lt _ hm), by rw [← hw i hi]; exact hc⟩
    · intro i hi
      obtain ⟨hi, hc⟩ := mem_filter.1 hi
      rw [mem_range] at hi
      have hlt : (if i = 0 then m - 1 else i - 1) < m := by split_ifs <;> omega
      refine mem_filter.2 ⟨mem_range.2 hlt, ?_⟩
      rw [hw _ hlt, hmod _ hlt]
      convert hc using 3
      split_ifs <;> omega
    · intro i hi
      have hi' := mem_range.1 (mem_filter.1 hi).1
      simp only
      rw [hmod i hi']
      rcases Nat.lt_or_ge (i + 1) m with h | h
      · rw [if_neg (show ¬ (i + 1 = m) by omega), if_neg (show ¬ (i + 1 = 0) by omega)]
        omega
      · rw [if_pos (show i + 1 = m by omega), if_pos rfl]; omega
    · intro i hi
      have hi' := mem_range.1 (mem_filter.1 hi).1
      have hlt : (if i = 0 then m - 1 else i - 1) < m := by split_ifs <;> omega
      simp only
      rw [hmod _ hlt]
      split_ifs <;> omega
  rw [hF, card_union_of_disjoint hdisj, hcA, hcB, hBA]
  exact ⟨A.card, rfl⟩

/-- The cut of the region bounded by `S[k, l]` and a walk `ret 0, …, ret (q - 1)` from `l` back
to `k` (above `S`), normalised to `1` above `[k, k + 1]`. -/
theorem c_lid_cut {z : D} (hz : Γ.infStart = some z) {tk tl : ℕ} (hlt : tk < tl)
    (hP : tl < period Γ.straight z) {q : ℕ} (hq : 0 < q) (ret : ℕ → D)
    (hS : ∀ j < q, Γ.curve (ret j) ≠ Γ.S)
    (h0 : Γ.crossingOf (ret 0) = Γ.crossingOf (Γ.noC z tl))
    (hstep : ∀ j, j + 1 < q → Γ.crossingOf (Γ.α (ret j)) = Γ.crossingOf (ret (j + 1)))
    (hlast : Γ.crossingOf (Γ.α (ret (q - 1))) = Γ.crossingOf (Γ.noC z tk))
    (hdist : ∀ i < q, ∀ j < q, Γ.segmentOf (ret i) = Γ.segmentOf (ret j) → i = j)
    (Lid : Finset D)
    (hLid : ∀ y, y ∈ Lid ↔ ∃ j < q, y = ret j ∨ y = Γ.α (ret j)) :
    ∃ r : Γ.Cell → ZMod 2, (∀ y, Γ.curve y ≠ Γ.S →
      r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if y ∈ Lid then 1 else 0) ∧
      r (Γ.upperCell (Γ.noC z tk)) = 1 := by
  classical
  set p := tl - tk with hp
  set m := p + q
  set w : ℕ → D := fun i => if i < p then Γ.noC z (tk + i) else ret (i - p) with hwdef
  have hw1 : ∀ i < p, w i = Γ.noC z (tk + i) := fun i hi => if_pos hi
  have hw2 : ∀ i, p ≤ i → w i = ret (i - p) := fun i hi => if_neg (by omega)
  have hwalk : ∀ i < m, Γ.crossingOf (Γ.α (w i)) = Γ.crossingOf (w ((i + 1) % m)) := by
    intro i hi
    by_cases h1 : i < p
    · rw [hw1 i h1, c_crossing_α_noC]
      by_cases h2 : i + 1 < p
      · rw [Nat.mod_eq_of_lt (by omega), hw1 _ h2, add_assoc]
      · rw [Nat.mod_eq_of_lt (by omega), hw2 _ (by omega), show i + 1 - p = 0 by omega, h0,
          show tk + i + 1 = tl by omega]
    · rw [hw2 i (by omega)]
      by_cases h3 : i + 1 < m
      · rw [Nat.mod_eq_of_lt h3, hw2 _ (by omega), show i + 1 - p = i - p + 1 by omega]
        exact hstep _ (by omega)
      · rw [show i + 1 = m by omega, Nat.mod_self, hw1 0 (by omega), add_zero,
          show i - p = q - 1 by omega]
        exact hlast
  have hinj : ∀ i < m, ∀ j < m, Γ.segmentOf (w i) = Γ.segmentOf (w j) → i = j := by
    intro i hi j hj he
    by_cases h1 : i < p <;> by_cases h2 : j < p
    · rw [hw1 i h1, hw1 j h2] at he
      have := (j_segmentOf_eq_iff Γ).1 he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h
      · have := no_noC_inj' (z := z) (by omega) (by omega) h
        omega
      · exact absurd (h ▸ no_noC_sweep hz _) (c_not_sweep_α (no_noC_sweep hz _))
    · rw [hw1 i h1, hw2 j (by omega)] at he
      exact absurd ((c_curve_seg he).trans (no_noC_sweep hz _).1) (hS _ (by omega))
    · rw [hw2 i (by omega), hw1 j h2] at he
      exact absurd ((c_curve_seg he.symm).trans (no_noC_sweep hz _).1) (hS _ (by omega))
    · rw [hw2 i (by omega), hw2 j (by omega)] at he
      have := hdist _ (by omega) _ (by omega) he
      omega
  obtain ⟨r0, hr0⟩ := exists_cut _ (c_even_walk (by omega) w hwalk hinj)
  refine ⟨fun c => r0 c + (r0 (Γ.upperCell (Γ.noC z tk)) + 1), fun y hy => ?_, ?_⟩
  · show r0 _ + _ + (r0 _ + _) = _
    rw [add_add_add_comm, j_zmod2_add_self, add_zero, hr0 y]
    refine if_congr ?_ rfl rfl
    rw [mem_image, hLid]
    constructor
    · rintro ⟨i, hi, he⟩
      rw [mem_range] at hi
      by_cases h1 : i < p
      · rw [hw1 i h1] at he
        exact absurd ((c_curve_seg he).trans (no_noC_sweep hz _).1) hy
      · rw [hw2 i (by omega)] at he
        have := (j_segmentOf_eq_iff Γ).1 he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        exact ⟨i - p, by omega, this⟩
    · rintro ⟨j, hj, he⟩
      refine ⟨p + j, mem_range.2 (by omega), ?_⟩
      rw [hw2 _ (by omega), show p + j - p = j by omega]
      rcases he with rfl | rfl
      · rfl
      · exact (j_segmentOf_α Γ _).symm
  · show r0 _ + (r0 _ + 1) = 1
    rw [← add_assoc, j_zmod2_add_self, zero_add]

/-! ## The curve of a leg leaves the region -/

/-- Along the curve of a leg `g` (starting on `S`, with the lid crossings off `S` at the end of
`g`), every dart above `S` off the lid has the value of `r` just after `g`. -/
theorem c_leg {z : D} {tk tl : ℕ} {r : Γ.Cell → ZMod 2} {Lid : Finset D}
    (h : CCut Γ z tk tl r Lid) {g : D} (hg : Γ.Above g)
    (hgS : Γ.S ∈ Γ.curves (Γ.crossingOf g)) (hgl : g ∈ Lid) (hgαl : Γ.α g ∈ Lid)
    (hX : ∀ y, Γ.σ (Γ.α y) ∈ Lid → ¬ Γ.OnSweep (Γ.crossingOf (Γ.α y)) →
      Γ.crossingOf (Γ.α y) = Γ.crossingOf (Γ.α g))
    {w : D} (hw : Γ.curve w = Γ.curve g) (hwa : Γ.Above w) (hwl : w ∉ Lid) :
    r (Γ.cellOf w) = r (Γ.cellOf (Γ.straight g)) := by
  have hα : r (Γ.cellOf (Γ.α w)) = r (Γ.cellOf w) := by
    have := h.cut w hwa.1
    rw [if_neg hwl] at this
    exact c_zmod2_eq_of_add this
  have key : ∀ k, (∀ i ≤ k + 1, Γ.Above ((Γ.straight ^ i) g)) →
      r (Γ.cellOf ((Γ.straight ^ (k + 1)) g)) = r (Γ.cellOf (Γ.straight g)) := by
    intro k hk
    have hpw : ∀ i, (Γ.straight ^ (i + 1)) g = (Γ.straight ^ i) (Γ.straight g) := by
      intro i; rw [pow_succ, Perm.mul_apply]
    rw [hpw]
    refine c_walk_of h (fun i hi => by rw [← hpw]; exact hk _ (by omega)) (fun i hi hl => ?_)
    rw [← hpw] at hl
    set y := (Γ.straight ^ (i + 1)) g
    have hy : Γ.Above y := hk _ (by omega)
    have hy1 : Γ.Above (Γ.straight y) := by rw [← no_pow_succ]; exact hk _ (by omega)
    have hnS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α y)) := fun hS => no_exit hy hS hy1
    have hc := hX y hl hnS
    have hcy : Γ.curve (Γ.α y) = Γ.curve (Γ.α g) := by
      rw [j_curve_α, j_curve_α, no_curve_pow]
    rcases no_mem_crossing hc with he | he | he | he
    · -- `y = g`: the walk would re-enter `g`, which starts on `S`
      have hyg : y = g := by rw [← j_α_α Γ y, he, j_α_α]
      have h1 : Γ.straight ((Γ.straight ^ i) g) = g := by rw [← no_pow_succ]; exact hyg
      exact no_enter hg hgS (hk i (by omega)) h1
    · exact no_curve_σ_ne (Γ.α g) (he ▸ hcy)
    · -- `α y = straight g`: then `σ² g` would be on the straight walk of `g`
      have h1 : Γ.straight y = Γ.α g := by
        rw [j_straight_apply, he, Γ.j_σ4]
      apply no_not_sameCycle_straight_σσ (Γ := Γ) g
      refine ⟨((i + 3 : ℕ) : ℤ), ?_⟩
      have h2 : (Γ.straight ^ (i + 3)) g = Γ.straight (Γ.straight y) := by
        rw [show i + 3 = i + 1 + 1 + 1 by omega, no_pow_succ, no_pow_succ]
      rw [zpow_natCast, h2, h1, j_straight_apply, j_α_α]
    · have := no_curve_σ_ne (Γ := Γ) (Γ.α g)
      rw [← j_curve_σσ Γ (Γ.σ (Γ.α g)), ← he] at this
      exact this hcy
  have hgS' : ∀ e, Γ.UpperWalk e g → e = g := fun e he => no_upperWalk_to hg hgS he
  rcases upper_arc hg hwa hw.symm with ⟨k, hk, hkw⟩ | hk | ⟨k, hk, hkw⟩ | hk
  · cases k with
    | zero => exact absurd (hkw ▸ hgl) hwl
    | succ k => rw [← hkw]; exact key k hk
  · exact absurd (hgS' w hk ▸ hgl) hwl
  · cases k with
    | zero =>
      have : w = Γ.α g := by rw [← j_α_α Γ w, ← hkw]; rfl
      exact absurd (this ▸ hgαl) hwl
    | succ k => rw [← hα, ← hkw]; exact key k hk
  · have := hgS' _ hk
    have : w = Γ.α g := by rw [← j_α_α Γ w, this]
    exact absurd (this ▸ hgαl) hwl

/-! ## Humps -/

/-- **Lemma 3.6, humps**: a hump `⟨k, l⟩`, `k < l`, contradicts minimality. -/
theorem c_hump_core (hΓ : Γ.MinCE) {z : D} (hz : Γ.infStart = some z) {tk tl : ℕ}
    (hlt : tk < tl) (hfin : tl + Γ.infLen < period Γ.straight z) {a : D}
    (ha : a = Γ.σ (Γ.noC z tk)) (hαa : Γ.α a = Γ.σ (Γ.noC z tl)) : False := by
  have hA : Γ.Above a := ha ▸ no_above_σ (no_noC_sweep hz tk)
  have hαA : Γ.Above (Γ.α a) := hαa ▸ no_above_σ (no_noC_sweep hz tl)
  by_cases h1 : tk + 1 = tl
  · -- the hump is the cell above `[k, k + 1]`
    apply hΓ.1.2
    left
    refine ⟨Γ.noC z tk, ⟨no_noC_sweep hz tk, fun hm => ?_⟩, ?_⟩
    · have := (no_noC_arc hz (by omega)).1 hm
      omega
    · unfold upperCell
      rw [c_size]
      have e1 : Γ.φ (Γ.α (Γ.noC z tk)) = a := by rw [j_φ_apply, j_α_α, ha]
      have e2 : Γ.φ a = Γ.α (Γ.noC z tk) := by
        rw [j_φ_apply, hαa]
        have := no_pred (Γ := Γ) (no_noC_straight z tk)
        rw [← h1, ← this, j_α_α]
      refine c_period_two _ _ (fun he => ?_) (by rw [e1, e2])
      rw [e1] at he
      have := congrArg Γ.curve he
      rw [j_curve_α, (no_noC_sweep hz tk).1] at this
      exact hA.1 this
  have h2 : tk + 1 < tl := by omega
  set Lid : Finset D := {Γ.α a, a}
  have hmem : ∀ y, y ∈ Lid ↔ y = Γ.α a ∨ y = a := by
    intro y; simp only [Lid, mem_insert, mem_singleton]
  obtain ⟨r, hcut, hbase⟩ := c_lid_cut hz hlt (by omega) (q := 1) one_pos (fun _ => Γ.α a)
    (fun _ _ => hαA.1) (by rw [hαa, j_crossingOf_σ]) (fun j hj => by omega)
    (by rw [j_α_α, ha, j_crossingOf_σ]) (fun i hi j hj _ => by omega) Lid
    (fun y => by
      rw [hmem, j_α_α]
      exact ⟨fun hy => ⟨0, one_pos, hy⟩, fun ⟨_, _, hy⟩ => hy⟩)
  have hSa : Γ.S ∈ Γ.curves (Γ.crossingOf (Γ.α a)) := hαa ▸ c_S_mem_σ_noC hz tl
  have hSa' : Γ.S ∈ Γ.curves (Γ.crossingOf a) := ha ▸ c_S_mem_σ_noC hz tk
  refine c_core hΓ ⟨⟨hz, hlt, hfin, hcut, hbase, fun t ht => ?_⟩, ?_, ?_, ?_⟩ h2
  · rw [hmem, hαa, ha]
    constructor
    · rintro (he | he)
      · exact Or.inr (c_σ_noC_inj ht (by omega) he)
      · exact Or.inl (c_σ_noC_inj ht (by omega) he)
    · rintro (rfl | rfl)
      · exact Or.inr rfl
      · exact Or.inl rfl
  · intro y hy
    rcases (hmem y).1 hy with rfl | rfl
    · exact hαA
    · exact hA
  · -- the curve of the hump has no other dart above `S`
    intro y hy w hw hwa hwl
    exfalso
    have hcw : Γ.curve a = Γ.curve w := by
      rcases (hmem y).1 hy with rfl | rfl
      · rw [hw, j_curve_α]
      · exact hw.symm
    have hno : ¬ Γ.Above (Γ.straight a) := no_exit hA hSa
    rcases upper_arc hA hwa hcw with ⟨k, hk, hkw⟩ | hk | ⟨k, hk, hkw⟩ | hk
    · cases k with
      | zero => exact hwl ((hmem w).2 (Or.inr hkw.symm))
      | succ k => exact hno (by simpa using hk 1 (by omega))
    · exact hwl ((hmem w).2 (Or.inr (no_upperWalk_to hA hSa' hk)))
    · cases k with
      | zero =>
        refine hwl ((hmem w).2 (Or.inl ?_))
        rw [← j_α_α Γ w, ← hkw]; rfl
      | succ k => exact hno (by simpa using hk 1 (by omega))
    · refine hwl ((hmem w).2 (Or.inl ?_))
      rw [← j_α_α Γ w, no_upperWalk_to hA hSa' hk]
  · intro y hy w hcw
    rcases (hmem y).1 hy with rfl | rfl
    · rw [hαa] at hcw; exact c_lidX_S hz (hαa ▸ hy) w hcw
    · rw [ha] at hcw; exact c_lidX_S hz (ha ▸ hy) w hcw

/-! ## Convex triangles -/

/-- **Lemma 3.6, convex triangles**: legs `a = ⟨k, v⟩`, `b = ⟨l, v⟩`, `k < l`, with the region
at `v` the angle between the legs (`φ a = α b`), contradict minimality. -/
theorem c_tri_core (hΓ : Γ.MinCE) {z : D} (hz : Γ.infStart = some z) {tk tl : ℕ}
    (hlt : tk < tl) (hfin : tl + Γ.infLen < period Γ.straight z) {a b : D}
    (ha : a = Γ.σ (Γ.noC z tk)) (hb : b = Γ.σ (Γ.noC z tl))
    (hv : Γ.crossingOf (Γ.α a) = Γ.crossingOf (Γ.α b))
    (hvS : ¬ Γ.OnSweep (Γ.crossingOf (Γ.α a))) (hab : Γ.curve a ≠ Γ.curve b)
    (hconv : Γ.φ a = Γ.α b) : False := by
  have hA : Γ.Above a := ha ▸ no_above_σ (no_noC_sweep hz tk)
  have hB : Γ.Above b := hb ▸ no_above_σ (no_noC_sweep hz tl)
  have hconv' : Γ.σ (Γ.α a) = Γ.α b := hconv
  have hSa : Γ.S ∈ Γ.curves (Γ.crossingOf a) := ha ▸ c_S_mem_σ_noC hz tk
  have hSb : Γ.S ∈ Γ.curves (Γ.crossingOf b) := hb ▸ c_S_mem_σ_noC hz tl
  by_cases h1 : tk + 1 = tl
  · -- the triangle is the cell above `[k, k + 1]`
    apply hΓ.1.2
    right; left
    refine ⟨Γ.noC z tk, ⟨no_noC_sweep hz tk, fun hm => ?_⟩, ?_⟩
    · have := (no_noC_arc hz (by omega)).1 hm
      omega
    · unfold upperCell
      rw [c_size]
      have e1 : Γ.φ (Γ.α (Γ.noC z tk)) = a := by rw [j_φ_apply, j_α_α, ha]
      have e3 : Γ.φ (Γ.α b) = Γ.α (Γ.noC z tk) := by
        rw [j_φ_apply, j_α_α, hb]
        have := no_pred (Γ := Γ) (no_noC_straight z tk)
        rw [← h1, ← this, j_α_α]
      have hS0 : Γ.curve (Γ.α (Γ.noC z tk)) = Γ.S := by
        rw [j_curve_α, (no_noC_sweep hz tk).1]
      refine c_period_three _ _ (fun he => ?_) (fun he => ?_) (by rw [e1, hconv, e3])
      · rw [e1] at he
        exact hA.1 (by rw [he, hS0])
      · rw [e1, hconv] at he
        have := congrArg Γ.curve he
        rw [j_curve_α, hS0] at this
        exact hB.1 this
  have h2 : tk + 1 < tl := by omega
  set Lid : Finset D := {b, Γ.α a, Γ.α b, a}
  have hmem : ∀ y, y ∈ Lid ↔ y = b ∨ y = Γ.α a ∨ y = Γ.α b ∨ y = a := by
    intro y; simp only [Lid, mem_insert, mem_singleton]
  set ret : ℕ → D := fun j => if j = 0 then b else Γ.α a
  obtain ⟨r, hcut, hbase⟩ := c_lid_cut hz hlt (by omega) (q := 2) two_pos ret
    (fun j _ => by
      simp only [ret]
      split_ifs
      · exact hB.1
      · rw [j_curve_α]; exact hA.1)
    (by simp only [ret, if_pos rfl]; rw [hb, j_crossingOf_σ])
    (fun j hj => by
      have : j = 0 := by omega
      subst this
      simp only [ret, if_pos rfl, show (0 + 1 = 0) = False by simp, if_false]
      exact hv.symm)
    (by simp only [ret, show (2 - 1 = 0) = False by simp, if_false]
        rw [j_α_α, ha, j_crossingOf_σ])
    (fun i hi j hj he => by
      by_contra hne
      have : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp only [ret, if_pos rfl, show (1 = 0) = False by simp, if_false] at he
        have := c_curve_seg he
        rw [j_curve_α] at this
        exact hab this
      · simp only [ret, if_pos rfl, show (1 = 0) = False by simp, if_false] at he
        have := c_curve_seg he
        rw [j_curve_α] at this
        exact hab this.symm)
    Lid
    (fun y => by
      rw [hmem]
      constructor
      · rintro (h | h | h | h)
        · exact ⟨0, two_pos, Or.inl h⟩
        · exact ⟨1, one_lt_two, Or.inl h⟩
        · exact ⟨0, two_pos, Or.inr h⟩
        · refine ⟨1, one_lt_two, Or.inr ?_⟩
          simp only [ret, show (1 = 0) = False by simp, if_false, j_α_α]
          exact h
      · rintro ⟨j, hj, h⟩
        have : j = 0 ∨ j = 1 := by omega
        rcases this with rfl | rfl
        · simp only [ret, if_pos rfl] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inl h))
        · simp only [ret, show (1 = 0) = False by simp, if_false] at h
          rcases h with h | h
          · exact Or.inr (Or.inl h)
          · rw [j_α_α] at h; exact Or.inr (Or.inr (Or.inr h)))
  -- the apex is off `S`; lid darts at `S` are `a` and `b` only
  have hnS : ∀ t, Γ.σ (Γ.noC z t) ≠ Γ.α a ∧ Γ.σ (Γ.noC z t) ≠ Γ.α b := by
    intro t
    constructor
    · intro he
      apply hvS
      rw [← he, j_crossingOf_σ]; exact no_S_mem_noC hz t
    · intro he
      apply hvS
      rw [hv, ← he, j_crossingOf_σ]; exact no_S_mem_noC hz t
  have hσ : ∀ t < period Γ.straight z, (Γ.σ (Γ.noC z t) ∈ Lid ↔ t = tk ∨ t = tl) := by
    intro t ht
    rw [hmem, ha, hb]
    constructor
    · rintro (he | he | he | he)
      · exact Or.inr (c_σ_noC_inj ht (by omega) he)
      · exact absurd (by rw [ha]; exact he) (hnS t).1
      · exact absurd (by rw [hb]; exact he) (hnS t).2
      · exact Or.inl (c_σ_noC_inj ht (by omega) he)
    · rintro (rfl | rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl rfl
  have hcc : CCut Γ z tk tl r Lid := ⟨hz, hlt, hfin, hcut, hbase, hσ⟩
  -- lid darts off `S` are at the apex
  have hX : ∀ y, Γ.σ (Γ.α y) ∈ Lid → ¬ Γ.OnSweep (Γ.crossingOf (Γ.α y)) →
      Γ.crossingOf (Γ.α y) = Γ.crossingOf (Γ.α a) := by
    intro y hl hn
    rw [← j_crossingOf_σ Γ (Γ.α y)]
    rcases (hmem _).1 hl with he | he | he | he
    · exact absurd (by rw [← j_crossingOf_σ Γ (Γ.α y), he]; exact hSb) hn
    · rw [he]
    · rw [he, hv]
    · exact absurd (by rw [← j_crossingOf_σ Γ (Γ.α y), he]; exact hSa) hn
  have hal : a ∈ Lid := (hmem a).2 (Or.inr (Or.inr (Or.inr rfl)))
  have hbl : b ∈ Lid := (hmem b).2 (Or.inl rfl)
  have hαal : Γ.α a ∈ Lid := (hmem _).2 (Or.inr (Or.inl rfl))
  have hαbl : Γ.α b ∈ Lid := (hmem _).2 (Or.inr (Or.inr (Or.inl rfl)))
  -- `r` just after the legs
  have hra : r (Γ.cellOf (Γ.straight a)) = 0 := by
    have hw := no_walk_straight (Γ := Γ) (r := r)
      (f := fun y => r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y))) (fun y => rfl) a
    rw [hw]
    rw [hcut _ (by rw [hconv']; rw [j_curve_α]; exact hB.1), hconv', if_pos hαbl]
    have : r (Γ.cellOf a) = 1 := by
      rw [ha, j_cellOf_σ]; exact hbase
    rw [this]; decide
  have hrb : r (Γ.cellOf (Γ.straight b)) = 0 := by
    have hw := no_walk_straight (Γ := Γ) (r := r)
      (f := fun y => r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y))) (fun y => rfl) b
    rw [hw]
    have hσb : Γ.σ (Γ.α b) = Γ.σ (Γ.σ (Γ.α a)) := by rw [hconv']
    have hσbS : Γ.curve (Γ.σ (Γ.α b)) ≠ Γ.S := by
      rw [hσb, j_curve_σσ, j_curve_α]; exact hA.1
    rw [hcut _ hσbS, if_neg]
    · have : r (Γ.cellOf b) = 0 := by
        rw [hb, j_cellOf_σ]
        have := c_sweep hcc (t := tl) (by omega)
        unfold upperCell at this
        rw [this, if_neg (by omega)]
      rw [this]; decide
    · rw [hσb, hmem]
      rintro (he | he | he | he)
      · apply hvS
        rw [← r_crossingOf_σσ Γ (Γ.α a), he]; exact hSb
      · exact Γ.j_σσ_ne _ he
      · rw [← hconv'] at he
        exact no_curve_σ_ne (Γ.α a) (by rw [Γ.σ.injective he])
      · apply hvS
        rw [← r_crossingOf_σσ Γ (Γ.α a), he]; exact hSa
  refine c_core hΓ ⟨hcc, ?_, ?_, ?_⟩ h2
  · intro y hy
    rcases (hmem y).1 hy with rfl | rfl | rfl | rfl
    · exact hB
    · exact ⟨by rw [j_curve_α]; exact hA.1, by unfold Up; rw [no_side_α hA.1]; exact hA.2⟩
    · exact ⟨by rw [j_curve_α]; exact hB.1, by unfold Up; rw [no_side_α hB.1]; exact hB.2⟩
    · exact hA
  · intro y hy w hw hwa hwl
    rcases (hmem y).1 hy with rfl | rfl | rfl | rfl
    · rw [c_leg hcc hB hSb hbl hαbl (fun y h1 h2 => (hX y h1 h2).trans hv) hw hwa hwl, hrb]
    · rw [j_curve_α] at hw
      rw [c_leg hcc hA hSa hal hαal hX hw hwa hwl, hra]
    · rw [j_curve_α] at hw
      rw [c_leg hcc hB hSb hbl hαbl (fun y h1 h2 => (hX y h1 h2).trans hv) hw hwa hwl, hrb]
    · rw [c_leg hcc hA hSa hal hαal hX hw hwa hwl, hra]
  · intro y hy w hcw
    rcases (hmem y).1 hy with rfl | rfl | rfl | rfl
    · rw [hb] at hcw; exact c_lidX_S hz (hb ▸ hbl) w hcw
    · -- at the apex: the curves of the legs
      have hm : Γ.curve w ∈ Γ.curves (Γ.crossingOf w) := by
        rw [j_curves_crossingOf]; exact mem_insert_self _ _
      rw [hcw, j_curves_crossingOf, mem_insert, mem_singleton, hconv', j_curve_α,
        j_curve_α] at hm
      rcases hm with hm | hm
      · exact Or.inr ⟨_, hal, hm.symm⟩
      · exact Or.inr ⟨_, hbl, hm.symm⟩
    · have hm : Γ.curve w ∈ Γ.curves (Γ.crossingOf w) := by
        rw [j_curves_crossingOf]; exact mem_insert_self _ _
      rw [hcw, j_curves_crossingOf, mem_insert, mem_singleton, ← hconv', j_curve_σσ,
        j_curve_α] at hm
      rcases hm with hm | hm
      · exact Or.inr ⟨_, hbl, by rw [hm, hconv', j_curve_α]⟩
      · exact Or.inr ⟨_, hal, hm.symm⟩
    · rw [ha] at hcw; exact c_lidX_S hz (ha ▸ hal) w hcw

end SConf

end Pca.Sweep
