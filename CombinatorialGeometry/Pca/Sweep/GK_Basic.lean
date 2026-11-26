/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Packages G and K (Lemma 3.9 hiding step, p. 322), generic helpers

* `gk_curve_cut`: the side function of an arbitrary curve (Jordan, as `cellOf_α_ne`).
* `gkInst`: the same map with an arbitrary curve `c` as sweeping curve and its side function as
  upper side (∞-arc: one segment). Through it every lemma about `S` (in particular
  `no_upper_arc`) applies to `c`.
* walks along a curve against a cut, `gk_even_walk` (the segments of a closed walk form an even
  set, a copy of `c_even_walk` of package C), injectivity of segments along a straight walk;
* the joined segments of a removal (`gk_hits_spec`, `gk_hits_lt_period`, `gk_hits_le_two`).
-/
import Pca.Sweep.Removal
import Pca.Sweep.F_Basic

open Equiv Finset

set_option linter.unusedSectionVars false

namespace Pca.Sweep

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {n : ℕ}

namespace SConf

variable {Γ : SConf n D}

/-! ## The side of an arbitrary curve -/

/-- Jordan for one curve: its segments form a cut. -/
theorem gk_curve_cut (c : Fin n) : ∃ r : Γ.Cell → ZMod 2, ∀ y,
    r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if Γ.curve y = c then 1 else 0 := by
  have hh : ∀ z, (if ∃ w ∈ (Γ.segmentOf z).darts, Γ.curve w = c then (1 : ZMod 2) else 0) =
      if Γ.curve z = c then 1 else 0 := by
    intro z
    simp only [j_darts_segmentOf, mem_insert, mem_singleton, exists_eq_or_imp, exists_eq_left,
      j_curve_α, or_self]
  obtain ⟨g, hg⟩ := Γ.j_mem_range_of_mem_ker
    (fun s => if ∃ w ∈ s.darts, Γ.curve w = c then 1 else 0) (by
      funext x
      obtain ⟨z, rfl⟩ := x.exists_mk
      change Γ.jSegBdry _ (Γ.crossingOf z) = 0
      rw [j_segBdry_crossingOf, hh, hh, hh, hh, j_curve_σσ, j_curve_σσ]
      split_ifs <;> decide)
  refine ⟨g, fun y => ?_⟩
  rw [← j_cellBdry_segmentOf, hg]
  exact hh y

/-- A cut can be normalised to `1` at a given cell. -/
theorem gk_cut_norm {f : D → ZMod 2} {r : Γ.Cell → ZMod 2}
    (hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = f y) (c₀ : Γ.Cell) :
    ∃ r' : Γ.Cell → ZMod 2, (∀ y, r' (Γ.cellOf y) + r' (Γ.cellOf (Γ.α y)) = f y) ∧ r' c₀ = 1 := by
  refine ⟨fun c => r c + (r c₀ + 1), fun y => ?_, ?_⟩
  · show r _ + _ + (r _ + _) = _
    rw [add_add_add_comm, j_zmod2_add_self, add_zero, hr y]
  · show r c₀ + (r c₀ + 1) = 1
    rw [← add_assoc, j_zmod2_add_self, zero_add]

/-- The side of the curve `c`, normalised to `1` at the cell `c₀`. -/
theorem gk_curve_cut' (c : Fin n) (c₀ : Γ.Cell) : ∃ r : Γ.Cell → ZMod 2, (∀ y,
    r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if Γ.curve y = c then 1 else 0) ∧ r c₀ = 1 := by
  obtain ⟨r, hr⟩ := gk_curve_cut (Γ := Γ) c
  exact gk_cut_norm hr c₀

theorem gk_zmod2_ne_add_one (a : ZMod 2) : a ≠ a + 1 := by
  revert a; decide

/-! ## Walks against a cut -/

/-- Along a straight walk the cut does not change if no crossing passed is on `c`. -/
theorem gk_walk {r : Γ.Cell → ZMod 2} {c : Fin n}
    (hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if Γ.curve y = c then 1 else 0)
    (y : D) (k : ℕ) (hk : ∀ t < k, Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ t) y))) ≠ c) :
    r (Γ.cellOf ((Γ.straight ^ k) y)) = r (Γ.cellOf y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [no_pow_succ, no_walk_straight hr, ih (fun t ht => hk t (by omega)),
      if_neg (hk k (by omega)), add_zero]

/-- Along a straight walk all of whose passed crossings are on `c`, the cut changes `k` times. -/
theorem gk_walk_flip {r : Γ.Cell → ZMod 2} {c : Fin n}
    (hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if Γ.curve y = c then 1 else 0)
    (y : D) (k : ℕ) (hk : ∀ t < k, Γ.curve (Γ.σ (Γ.α ((Γ.straight ^ t) y))) = c) :
    r (Γ.cellOf ((Γ.straight ^ k) y)) = r (Γ.cellOf y) + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [no_pow_succ, no_walk_straight hr, ih (fun t ht => hk t (by omega)),
      if_pos (hk k (by omega))]
    push_cast; ring

/-- Along a curve `c`, its own cut does not change on the right side. -/
theorem gk_walk_own {r : Γ.Cell → ZMod 2} {c : Fin n}
    (hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if Γ.curve y = c then 1 else 0)
    (y : D) (hy : Γ.curve y = c) (k : ℕ) :
    r (Γ.cellOf ((Γ.straight ^ k) y)) = r (Γ.cellOf y) := by
  refine gk_walk hr y k fun t _ h => ?_
  apply no_curve_σ_ne (Γ := Γ) (Γ.α ((Γ.straight ^ t) y))
  rw [h, j_curve_α, no_curve_pow, hy]

/-! ## Segments along a straight walk -/

theorem gk_curve_seg {a b : D} (h : Γ.segmentOf a = Γ.segmentOf b) : Γ.curve b = Γ.curve a := by
  have := (j_segmentOf_eq_iff Γ).1 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl
  · rfl
  · exact j_curve_α Γ a

/-- A dart and the reverse of a dart of its straight walk are different. -/
theorem gk_pow_ne_α_pow (x : D) (i j : ℕ) :
    (Γ.straight ^ j) x ≠ Γ.α ((Γ.straight ^ i) x) := by
  intro h
  apply no_not_sameCycle_straight_σσ (Γ := Γ) ((Γ.straight ^ (i + 1)) x)
  have h1 : Γ.σ (Γ.σ ((Γ.straight ^ (i + 1)) x)) = (Γ.straight ^ j) x := by
    rw [h, no_pow_succ, j_straight_apply, Γ.j_σ4]
  rw [h1]
  exact Perm.sameCycle_pow_left.2 (Perm.sameCycle_pow_right.2 (Perm.SameCycle.refl _ x))

/-- Segments along one straight walk are distinct within a period. -/
theorem gk_seg_pow_inj {x : D} {i j : ℕ} (hi : i < period Γ.straight x)
    (hj : j < period Γ.straight x)
    (h : Γ.segmentOf ((Γ.straight ^ i) x) = Γ.segmentOf ((Γ.straight ^ j) x)) : i = j := by
  have := (j_segmentOf_eq_iff Γ).1 h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with h1 | h1
  · exact (no_pow_inj hj hi h1).symm
  · exact absurd h1 (gk_pow_ne_α_pow x i j)

/-! ## Jordan: the segments of a closed walk (copy of `c_even_walk`, package C) -/

/-- The segments of a closed walk with distinct segments form an even set. -/
theorem gk_even_walk {m : ℕ} (hm : 0 < m) (w : ℕ → D)
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

/-! ## Another curve as sweeping curve -/

variable (Γ) in
/-- The map of `Γ` with the curve `c` as sweeping curve, the cut `r` of `c` as its side
function (`r = 1` above) and the one segment of `z` as ∞-arc. -/
def gkInst (c : Fin n) (r : Γ.Cell → ZMod 2)
    (hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if Γ.curve y = c then 1 else 0)
    (z : D) (hz : Γ.curve z = c) (hz' : r (Γ.cellOf (Γ.α z)) = 1) : SConf n D where
  σ := Γ.σ
  α := Γ.α
  curve := Γ.curve
  S := c
  isSConf :=
    { card_crossing := Γ.isSConf.card_crossing
      α_ne := Γ.isSConf.α_ne
      α_α := Γ.isSConf.α_α
      curve_α := Γ.isSConf.curve_α
      curve_σ := Γ.isSConf.curve_σ
      curve_σσ := Γ.isSConf.curve_σσ
      straight := Γ.isSConf.straight
      two_int := Γ.isSConf.two_int
      connected := Γ.isSConf.connected
      euler := Γ.isSConf.euler
      S_mem := fun _ => ⟨z, hz⟩ }
  side := r
  isSide := hr
  infStart := some z
  infLen := 0
  infStart_isSome := fun _ => rfl
  infLen_le := fun _ _ => Nat.zero_le _
  infArc_sweep := by
    intro d hd
    simp only [arcOf, Option.elim, zero_add, range_one, image_singleton, pow_zero,
      Perm.one_apply, mem_singleton] at hd
    subst hd
    exact ⟨hz, hz'⟩

/-- Above the curve `c` in `gkInst`: a dart of another curve on the side `r = 1`. -/
theorem gkInst_above {c : Fin n} {r : Γ.Cell → ZMod 2}
    {hr : ∀ y, r (Γ.cellOf y) + r (Γ.cellOf (Γ.α y)) = if Γ.curve y = c then 1 else 0}
    {z : D} {hz : Γ.curve z = c} {hz' : r (Γ.cellOf (Γ.α z)) = 1} {y : D} :
    (Γ.gkInst c r hr z hz hz').Above y ↔ Γ.curve y ≠ c ∧ r (Γ.cellOf y) = 1 := Iff.rfl

/-! ## The joined segments of a removal -/

/-- The pieces of the joined segment of `x'`: `hits x'` pieces, the crossings passed are deleted,
the last one ends at a kept crossing, at `ι (α' x')`. -/
theorem gk_hits_spec {R : Finset (Fin n)} (X : Γ.Removal R) (x' : X.D') :
    (∀ i < X.hits x', Γ.Deleted R (Γ.crossingOf (Γ.α ((Γ.straight ^ i) (X.ι x'))))) ∧
    ¬ Γ.Deleted R (Γ.crossingOf (Γ.α ((Γ.straight ^ X.hits x') (X.ι x')))) ∧
    X.ι (X.Γ'.α x') = Γ.α ((Γ.straight ^ X.hits x') (X.ι x')) := by
  classical
  obtain ⟨e, ⟨k, hdel, rfl⟩, hnd, hα⟩ := X.isRemoval.α x'
  have hk : X.hits x' = k := by
    unfold Removal.hits
    rw [Nat.find_eq_iff]
    exact ⟨hnd, fun m hm h => h (hdel m hm)⟩
  rw [hk]
  exact ⟨hdel, hnd, hα⟩

/-- A joined segment has fewer pieces than the period of its curve. -/
theorem gk_hits_lt_period {R : Finset (Fin n)} (X : Γ.Removal R) (x' : X.D') :
    X.hits x' < period Γ.straight (X.ι x') := by
  obtain ⟨hdel, hnd, -⟩ := gk_hits_spec X x'
  by_contra hc
  push Not at hc
  apply hnd
  have := hdel (X.hits x' - period Γ.straight (X.ι x')) (by
    have := period_pos Γ.straight (X.ι x'); omega)
  rwa [← no_pow_period, Nat.sub_add_cancel hc] at this

theorem gk_deleted_singleton {γ : Fin n} {x : Γ.Crossing} :
    Γ.Deleted {γ} x ↔ γ ∈ Γ.curves x := by
  unfold Deleted OnCurve
  simp only [mem_singleton, exists_eq_left]

/-- The other curve at a deleted crossing on a joined segment (of a curve `≠ γ`) is `γ`. -/
theorem gk_del_curve {γ : Fin n} {y : D} (hy : Γ.curve y ≠ γ)
    (h : Γ.Deleted {γ} (Γ.crossingOf (Γ.α y))) : Γ.curve (Γ.σ (Γ.α y)) = γ := by
  rw [gk_deleted_singleton, j_curves_crossingOf, mem_insert, mem_singleton, j_curve_α] at h
  rcases h with h | h
  · exact absurd h.symm hy
  · exact h.symm

/-- The curve of a kept dart is not the removed curve. -/
theorem gk_curve_ne {γ : Fin n} (X : Γ.Removal {γ}) (x' : X.D') : Γ.curve (X.ι x') ≠ γ := by
  intro h
  apply (X.r_keep x').1
  rw [gk_deleted_singleton, j_curves_crossingOf, h]
  exact mem_insert_self _ _

/-- Removing one curve: a joined segment has at most `2` pieces more than one (two-intersection
property). -/
theorem gk_hits_le_two {γ : Fin n} (X : Γ.Removal {γ}) (x' : X.D') : X.hits x' ≤ 2 := by
  obtain ⟨hdel, -, -⟩ := gk_hits_spec X x'
  have hP := gk_hits_lt_period X x'
  have hc := gk_curve_ne X x'
  set h₀ := X.ι x'
  by_contra hlt
  push Not at hlt
  have hcurves : ∀ t < X.hits x', Γ.curves (Γ.crossingOf (Γ.α ((Γ.straight ^ t) h₀))) =
      {Γ.curve h₀, γ} := by
    intro t ht
    have hon := (gk_deleted_singleton).1 (hdel t ht)
    refine no_mem_curves hon ?_ hc
    rw [j_curves_crossingOf, j_curve_α, no_curve_pow]; exact mem_insert_self _ _
  have h2 := Γ.isSConf.two_int (Γ.curve h₀) γ hc
  have hsub : ({Γ.crossingOf (Γ.α ((Γ.straight ^ 0) h₀)),
      Γ.crossingOf (Γ.α ((Γ.straight ^ 1) h₀)), Γ.crossingOf (Γ.α ((Γ.straight ^ 2) h₀))} :
        Finset Γ.Crossing) ⊆
      univ.filter (fun x : Orbit Γ.σ => crossingCurves Γ.σ Γ.curve x = {Γ.curve h₀, γ}) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl
    · exact hcurves 0 (by omega)
    · exact hcurves 1 (by omega)
    · exact hcurves 2 (by omega)
  have h3 := card_le_card hsub
  rw [card_eq_three.2 ⟨_, _, _, f_cross_ne (by omega) (by omega),
    f_cross_ne (by omega) (by omega), f_cross_ne (by omega) (by omega), rfl⟩] at h3
  omega

end SConf

end Pca.Sweep
