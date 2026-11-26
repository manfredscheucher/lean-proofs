/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import NonCirc.Encode

/-! # Soundness of the encoding

`encode_sound`: for a circle realization of `F`, the actual signs of all quantities satisfy every
clause of `encode F tags`, for every list of tags.
-/

namespace NonCirc

noncomputable section Semantics

variable (c : ℕ → ℝ × ℝ) (r ε : ℕ → ℝ) (P : ℕ → ℕ → ℤ → ℝ × ℝ)

/-- The Lorentz vector of an index. -/
def ival : Idx → Vec
  | .circ i => circVec (c i) (r i) (ε i)
  | .pt j k s => liftPt (P j k s)

/-- The value of a quantity. -/
def qval : Q → ℝ
  | .br a b c' d => br (ival c r ε P a) (ival c r ε P b) (ival c r ε P c') (ival c r ε P d)
  | .ip x y => ip (ival c r ε P x) (ival c r ε P y)
  | .mul u w => qval u * qval w

/-- The actual sign assignment. -/
def assign : Q × Bool → Bool
  | (q, true) => decide (0 < qval c r ε P q)
  | (q, false) => decide (qval c r ε P q < 0)

/-- A literal is true under the actual signs. -/
def litTrue (l : Lit) : Bool := assign c r ε P l.1 == l.2

/-- A clause is true under the actual signs. -/
def clauseTrue (cl : Clause) : Bool := cl.any (litTrue c r ε P)

end Semantics

variable {c : ℕ → ℝ × ℝ} {r ε : ℕ → ℝ} {P : ℕ → ℕ → ℤ → ℝ × ℝ}

local notation "sgn" q => SignType.sign (qval c r ε P q)

/-! ## Generic clause shapes -/

lemma notIs_true (q : Q) (s : SignType) (h : (sgn q) ≠ s) :
    clauseTrue c r ε P (notIs q s) = true := by
  rcases lt_trichotomy (qval c r ε P q) 0 with hq | hq | hq
  · cases s <;> simp_all [notIs, clauseTrue, litTrue, assign, sign_neg hq, not_lt_of_gt hq]
  · cases s <;> simp_all [notIs, clauseTrue, litTrue, assign]
  · cases s <;> simp_all [notIs, clauseTrue, litTrue, assign, sign_pos hq, not_lt_of_gt hq]

lemma consistent_true (q : Q) : clauseTrue c r ε P (consistent q) = true := by
  by_cases h : 0 < qval c r ε P q
  · simp [consistent, clauseTrue, litTrue, assign, h, not_lt_of_gt h]
  · simp [consistent, clauseTrue, litTrue, assign, h]

lemma length_of_mem_tuples : ∀ (k : ℕ) (t : List SignType), t ∈ tuples k → t.length = k
  | 0, t, h => by simp [tuples] at h; simp [h]
  | k + 1, t, h => by
    simp only [tuples, List.mem_flatMap, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at h
    obtain ⟨t', ht', s, -, rfl⟩ := h
    simp [length_of_mem_tuples k t' ht']

lemma exists_ne_of_ne : ∀ (qs : List Q) (t : List SignType), t.length = qs.length →
    t ≠ qs.map (fun q => sgn q) → ∃ p ∈ qs.zip t, (sgn p.1) ≠ p.2
  | [], [], _, h => absurd rfl h
  | q :: qs, s :: t, hl, h => by
    by_cases hs : (sgn q) = s
    · have : t ≠ qs.map (fun q => sgn q) := by
        intro ht; apply h; simp [ht, hs]
      obtain ⟨p, hp, hne⟩ := exists_ne_of_ne qs t (by simpa using hl) this
      exact ⟨p, by simp [hp], hne⟩
    · exact ⟨(q, s), by simp, hs⟩
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

lemma forbid_true (rel : List SignType → Bool) (qs : List Q)
    (h : rel (qs.map fun q => sgn q) = true) :
    ∀ cl ∈ forbid rel qs, clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [forbid, List.mem_map, List.mem_filter] at hcl
  obtain ⟨t, ⟨ht, hrel⟩, rfl⟩ := hcl
  have hne : t ≠ qs.map (fun q => sgn q) := by
    intro e; rw [e] at hrel; simp [h] at hrel
  obtain ⟨p, hp, hpne⟩ := exists_ne_of_ne qs t (length_of_mem_tuples _ _ ht) hne
  have := notIs_true (c := c) (r := r) (ε := ε) (P := P) p.1 p.2 hpne
  simp only [clauseTrue, List.any_eq_true, List.mem_flatMap] at this ⊢
  obtain ⟨l, hl, hlt⟩ := this
  exact ⟨l, ⟨p, hp, hl⟩, hlt⟩

lemma mulDef_true (u w : Q) : ∀ cl ∈ mulDef u w, clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [mulDef, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with (rfl | rfl | rfl) | hcl
  · exact consistent_true _
  · exact consistent_true _
  · exact consistent_true _
  · refine forbid_true _ _ ?_ cl hcl
    simp [qval, sign_mul]

lemma eqRel_true (σ : SignType) (t u : Q) (h : (sgn t) = σ * sgn u) :
    ∀ cl ∈ eqRel σ t u, clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [eqRel, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with (rfl | rfl) | hcl
  · exact consistent_true _
  · exact consistent_true _
  · exact forbid_true _ _ (by simp [h]) cl hcl

lemma factRel_true (s : SignType) (q : Q) (h : (sgn q) = s) :
    ∀ cl ∈ factRel s q, clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [factRel, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | hcl
  · exact consistent_true _
  · exact forbid_true _ _ (by simp [h]) cl hcl

lemma nzRel_true (q : Q) (h : qval c r ε P q ≠ 0) :
    ∀ cl ∈ nzRel q, clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [nzRel, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · exact consistent_true _
  · rcases lt_or_gt_of_ne h with hq | hq <;> simp [clauseTrue, litTrue, assign, hq]

lemma sgn_beq_one_neg : ((-1 : SignType) == 1) = false := by decide
lemma sgn_bne_one_neg : ((-1 : SignType) != 1) = true := by decide

lemma litTrue_pos (σ : SignType) (q : Q) (hσ : σ = 1 ∨ σ = -1) :
    litTrue c r ε P ((q, σ == 1), true) = true ↔ σ * (sgn q) = 1 := by
  rcases lt_trichotomy (qval c r ε P q) 0 with hq | hq | hq <;>
    rcases hσ with rfl | rfl <;>
    simp [litTrue, assign, hq, sign_neg, sign_pos, not_lt_of_gt, sgn_beq_one_neg]

lemma litTrue_neg (σ : SignType) (q : Q) (hσ : σ = 1 ∨ σ = -1) :
    litTrue c r ε P ((q, σ != 1), true) = true ↔ σ * (sgn q) = -1 := by
  rcases lt_trichotomy (qval c r ε P q) 0 with hq | hq | hq <;>
    rcases hσ with rfl | rfl <;>
    simp [litTrue, assign, hq, sign_neg, sign_pos, not_lt_of_gt, sgn_bne_one_neg]

lemma litTrue_not (v : Q × Bool) (b : Bool) :
    litTrue c r ε P (v, !b) = true ↔ ¬ litTrue c r ε P (v, b) = true := by
  cases b <;> simp [litTrue]

lemma naeRel_true (ts : List (SignType × Q)) (hσ : ∀ t ∈ ts, t.1 = 1 ∨ t.1 = -1)
    (h : NAE (ts.map fun t => t.1 * sgn t.2)) :
    ∀ cl ∈ naeRel ts, clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [naeRel, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at hcl
  rcases hcl with ⟨t, -, rfl⟩ | ⟨t, ht, rfl | rfl⟩
  · exact consistent_true _
  · -- if `σ_t sign q_t = 1` then some term is `-1`
    by_cases hp : litTrue c r ε P ((t.2, t.1 == 1), true) = true
    · have h1 := (litTrue_pos t.1 t.2 (hσ t ht)).1 hp
      rcases h with h0 | ⟨-, hm⟩
      · exact absurd (h0 _ (List.mem_map.2 ⟨t, ht, rfl⟩)) (by rw [h1]; decide)
      · obtain ⟨t', ht', e⟩ := List.mem_map.1 hm
        simp only [clauseTrue, List.any_cons, List.any_map, Bool.or_eq_true, List.any_eq_true,
          Function.comp]
        exact Or.inr ⟨t', ht', (litTrue_neg t'.1 t'.2 (hσ t' ht')).2 e⟩
    · simp only [clauseTrue, List.any_cons, Bool.or_eq_true]
      left
      exact (litTrue_not _ true).2 hp
  · by_cases hp : litTrue c r ε P ((t.2, t.1 != 1), true) = true
    · have h1 := (litTrue_neg t.1 t.2 (hσ t ht)).1 hp
      rcases h with h0 | ⟨hm, -⟩
      · exact absurd (h0 _ (List.mem_map.2 ⟨t, ht, rfl⟩)) (by rw [h1]; decide)
      · obtain ⟨t', ht', e⟩ := List.mem_map.1 hm
        simp only [clauseTrue, List.any_cons, List.any_map, Bool.or_eq_true, List.any_eq_true,
          Function.comp]
        exact Or.inr ⟨t', ht', (litTrue_pos t'.1 t'.2 (hσ t' ht')).2 e⟩
    · simp only [clauseTrue, List.any_cons, Bool.or_eq_true]
      left
      exact (litTrue_not _ true).2 hp


/-! ## Geometric facts of a realization -/

lemma sign_eq_of_int_mul_pos {z : ℤ} {x : ℝ} (h : 0 < (z : ℝ) * x) :
    SignType.sign x = SignType.sign z := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have hz' : (z : ℝ) < 0 := by exact_mod_cast hz
    have : x < 0 := by nlinarith
    rw [sign_neg this, sign_neg hz]
  · subst hz; simp at h
  · have hz' : (0 : ℝ) < z := by exact_mod_cast hz
    have : 0 < x := by nlinarith
    rw [sign_pos this, sign_pos hz]

lemma sign_eq_of_mul_pos {x y : ℝ} (h : 0 < x * y) : SignType.sign x = SignType.sign y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : y < 0 := by nlinarith
    rw [sign_neg hx, sign_neg this]
  · subst hx; simp at h
  · have : 0 < y := by nlinarith
    rw [sign_pos hx, sign_pos this]

/-- `t π = -y` with `π < 0`: `t` has the sign of `y`. -/
lemma sign_eq_of_mul_neg_eq {t y π : ℝ} (h : t * π = -y) (hπ : π < 0) :
    SignType.sign t = SignType.sign y := by
  have ht : t = y * (-π)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ (by linarith)]; linarith
  rw [ht, sign_mul, sign_pos (inv_pos.mpr (neg_pos.mpr hπ)), mul_one]

/-- `t π = y` with `π < 0`: `t` has the sign of `-y`. -/
lemma sign_eq_neg_of_mul_eq {t y π : ℝ} (h : t * π = y) (hπ : π < 0) :
    SignType.sign t = -SignType.sign y := by
  have := sign_eq_of_mul_neg_eq (t := t) (y := -y) (π := π) (by rw [h, neg_neg]) hπ
  rw [this, Left.sign_neg]

namespace Fingerprint.IsCircleRealization

variable {F : Fingerprint} (R : F.IsCircleRealization c r ε P)
include R

omit R in
lemma ip_circ_pt (m j k : ℕ) (s : ℤ) :
    ip (ival c r ε P (.circ m)) (ival c r ε P (.pt j k s)) =
      2 * (ε m * (r m ^ 2 - dist2 (P j k s) (c m))) := by
  simp only [ival, ip_circVec_liftPt]

lemma side_pos {j k m : ℕ} {s : ℤ} (hl : F.IsLabel j k s) (hm1 : 1 ≤ m) (hm2 : m ≤ F.n)
    (hmj : m ≠ j) (hmk : m ≠ k) :
    0 < (F.side j k s m : ℝ) * ip (ival c r ε P (.circ m)) (ival c r ε P (.pt j k s)) := by
  have := R.sides j k s m hl hm1 hm2 hmj hmk
  rw [ip_circ_pt]; nlinarith

lemma on_zero {j k m : ℕ} {s : ℤ} (hl : F.IsLabel j k s) (hm : m = j ∨ m = k) :
    ip (ival c r ε P (.circ m)) (ival c r ε P (.pt j k s)) = 0 := by
  have h := R.on_circles j k s hl
  rw [ip_circ_pt]
  rcases hm with rfl | rfl
  · rw [h.1]; ring
  · rw [h.2]; ring

omit R in
lemma isPoint_pt (j k : ℕ) (s : ℤ) : IsPoint (ival c r ε P (.pt j k s)) := isPoint_liftPt _

/-- A circle with opposite sides at two crossings separates them. -/
lemma ip_prod_neg {l l' : ℕ × ℕ × ℤ} {m : ℕ} (hl : F.IsLabel l.1 l.2.1 l.2.2)
    (hl' : F.IsLabel l'.1 l'.2.1 l'.2.2) (hm1 : 1 ≤ m) (hm2 : m ≤ F.n) (h1 : m ≠ l.1)
    (h2 : m ≠ l.2.1) (h3 : m ≠ l'.1) (h4 : m ≠ l'.2.1)
    (hs : F.side l.1 l.2.1 l.2.2 m * F.side l'.1 l'.2.1 l'.2.2 m = -1) :
    ip (ival c r ε P (.circ m)) (ival c r ε P (.pt l.1 l.2.1 l.2.2)) *
      ip (ival c r ε P (.circ m)) (ival c r ε P (.pt l'.1 l'.2.1 l'.2.2)) < 0 := by
  have a := R.side_pos hl hm1 hm2 h1 h2
  have b := R.side_pos hl' hm1 hm2 h3 h4
  have hs' : (F.side l.1 l.2.1 l.2.2 m : ℝ) * (F.side l'.1 l'.2.1 l'.2.2 m : ℝ) = -1 := by
    exact_mod_cast hs
  nlinarith [mul_pos a b]

lemma sep_neg {l l' : ℕ × ℕ × ℤ} {w : ℕ} (hl : F.IsLabel l.1 l.2.1 l.2.2)
    (hl' : F.IsLabel l'.1 l'.2.1 l'.2.2) (h : F.separates l l' w = true) :
    ip (ival c r ε P (.pt l.1 l.2.1 l.2.2)) (ival c r ε P (.pt l'.1 l'.2.1 l'.2.2)) < 0 := by
  simp only [separates, isCirc, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hw1, hw2⟩, h1⟩, h2⟩, h3⟩, h4⟩, hs⟩ := h
  exact ip_points_neg (isPoint_pt _ _ _) (isPoint_pt _ _ _)
    (R.ip_prod_neg hl hl' hw1 hw2 h1 h2 h3 h4 hs)

lemma ip_ne_of_off {l : ℕ × ℕ × ℤ} {m : ℕ} (hl : F.IsLabel l.1 l.2.1 l.2.2) (hm1 : 1 ≤ m)
    (hm2 : m ≤ F.n) (h1 : m ≠ l.1) (h2 : m ≠ l.2.1) :
    ip (ival c r ε P (.circ m)) (ival c r ε P (.pt l.1 l.2.1 l.2.2)) ≠ 0 := by
  intro h0
  have := R.side_pos hl hm1 hm2 h1 h2
  rw [h0, mul_zero] at this
  exact lt_irrefl 0 this

/-- Two crossings distinguished by a circle have `<p, q> < 0`. -/
lemma dist_neg {l l' : ℕ × ℕ × ℤ} {w : ℕ} (hl : F.IsLabel l.1 l.2.1 l.2.2)
    (hl' : F.IsLabel l'.1 l'.2.1 l'.2.2) (h : F.distinct l l' w = true) :
    ip (ival c r ε P (.pt l.1 l.2.1 l.2.2)) (ival c r ε P (.pt l'.1 l'.2.1 l'.2.2)) < 0 := by
  unfold distinct at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact R.sep_neg hl hl' h
  · simp only [isCirc, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
      bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨hw1, hw2⟩, hon⟩, h3⟩, h4⟩ := h
    have h0 : ip (ival c r ε P (.circ w)) (ival c r ε P (.pt l.1 l.2.1 l.2.2)) = 0 :=
      R.on_zero hl (by rcases hon with e | e <;> simp [e])
    exact ip_points_neg' (isPoint_pt _ _ _) (isPoint_pt _ _ _) h0 (R.ip_ne_of_off hl' hw1 hw2 h3 h4)
  · simp only [isCirc, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
      bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨hw1, hw2⟩, hon⟩, h3⟩, h4⟩ := h
    have h0 : ip (ival c r ε P (.circ w)) (ival c r ε P (.pt l'.1 l'.2.1 l'.2.2)) = 0 :=
      R.on_zero hl' (by rcases hon with e | e <;> simp [e])
    rw [ip_comm]
    exact ip_points_neg' (isPoint_pt _ _ _) (isPoint_pt _ _ _) h0 (R.ip_ne_of_off hl hw1 hw2 h3 h4)

lemma distW_neg {l l' : ℕ × ℕ × ℤ} {w : Wit} (hl : F.IsLabel l.1 l.2.1 l.2.2)
    (hl' : F.IsLabel l'.1 l'.2.1 l'.2.2) (h : F.distinctW l l' w = true) :
    ip (ival c r ε P (.pt l.1 l.2.1 l.2.2)) (ival c r ε P (.pt l'.1 l'.2.1 l'.2.2)) < 0 := by
  cases w with
  | circ w => exact R.dist_neg hl hl' h
  | cyc m i j k =>
    simp only [distinctW, isCirc, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hm1, hm2⟩, hij⟩, hjk⟩, hk⟩, hne⟩, h1⟩, h2⟩ := h
    have hdet := R.cyclic m i j k hm1 hm2 hij hjk hk
    have hd : det3 (Fingerprint.pt P ((F.order m).getD i (0, 0, 0)))
        (Fingerprint.pt P ((F.order m).getD j (0, 0, 0)))
        (Fingerprint.pt P ((F.order m).getD k (0, 0, 0))) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hdet; exact lt_irrefl 0 hdet
    obtain ⟨d1, d2, d3⟩ := ne_of_det3_ne_zero hd
    have hne' : Fingerprint.pt P l ≠ Fingerprint.pt P l' := by
      rcases h1 with e1 | e1 | e1 <;> rcases h2 with e2 | e2 | e2 <;>
        rw [e1, e2] <;> first
          | exact d1 | exact d2 | exact d3 | exact d1.symm | exact d2.symm | exact d3.symm
          | exact absurd (e1.trans e2.symm) hne
    simp only [ival]
    rw [ip_liftPt_liftPt]
    have := dist2_pos hne'
    simp only [Fingerprint.pt] at this
    linarith

lemma D2_pos' {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) (hk : k ≤ F.n) :
    0 < D2 (ival c r ε P (.circ j)) (ival c r ε P (.circ k)) := by
  have hc := R.cross j k hj hjk hk
  have hεi : (ε j) ^ 2 = 1 := by
    rcases R.orientation j hj (by omega) with h | h <;> rw [h] <;> norm_num
  have hεj : (ε k) ^ 2 = 1 := by
    rcases R.orientation k (by omega) hk with h | h <;> rw [h] <;> norm_num
  simp only [ival]
  rw [D2_circVec, mul_pow, hεi, hεj]
  have := mul_pos (sub_pos.mpr hc.1) (sub_pos.mpr hc.2)
  linarith

lemma pair' {j k : ℕ} (hl : F.IsLabel j k 1) :
    Pair (ival c r ε P (.circ j)) (ival c r ε P (.circ k)) (ival c r ε P (.pt j k 1))
      (ival c r ε P (.pt j k (-1))) := by
  have hl' : F.IsLabel j k (-1) := ⟨hl.1, hl.2.1, hl.2.2.1, Or.inr rfl⟩
  exact ⟨R.on_zero hl (Or.inl rfl), R.on_zero hl (Or.inr rfl), R.on_zero hl' (Or.inl rfl),
    R.on_zero hl' (Or.inr rfl), (isPoint_pt j k 1).1, (isPoint_pt j k (-1)).1⟩

/-- Validated crossing pair: `<p⁺, p⁻> < 0` and `K ≠ 0`. -/
lemma pair_facts {j k : ℕ} {w : Wit} (hl : F.IsLabel j k 1)
    (hw : F.distinctW (j, k, 1) (j, k, -1) w = true) :
    ip (ival c r ε P (.pt j k 1)) (ival c r ε P (.pt j k (-1))) < 0 ∧
      br (ival c r ε P (.circ j)) (ival c r ε P (.circ k)) (ival c r ε P (.pt j k 1))
        (ival c r ε P (.pt j k (-1))) ≠ 0 := by
  have hl' : F.IsLabel j k (-1) := ⟨hl.1, hl.2.1, hl.2.2.1, Or.inr rfl⟩
  have hπ := R.distW_neg (l := (j, k, 1)) (l' := (j, k, -1)) hl hl' hw
  exact ⟨hπ, (R.pair' hl).K_ne (R.D2_pos' hl.1 hl.2.1 hl.2.2.1) hπ.ne⟩

lemma ipSign_circ_pt {m j k : ℕ} {t : ℤ} {s : SignType}
    (h : (if (decide (F.IsLabel j k t) && F.isCirc m) = true then
      (if (m == j || m == k) = true then some 0 else some (SignType.sign (F.side j k t m)))
      else none) = some s) :
    SignType.sign (ip (ival c r ε P (.circ m)) (ival c r ε P (.pt j k t))) = s := by
  by_cases h1 : (decide (F.IsLabel j k t) && F.isCirc m) = true
  · rw [if_pos h1] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, isCirc] at h1
    by_cases h2 : (m == j || m == k) = true
    · rw [if_pos h2] at h
      cases h
      rw [R.on_zero h1.1 (by simpa using h2), sign_zero]
    · rw [if_neg h2] at h
      cases h
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at h2
      exact sign_eq_of_int_mul_pos (R.side_pos h1.1 h1.2.1 h1.2.2 h2.1 h2.2)
  · rw [if_neg h1] at h
    cases h

lemma ipSign_sound {x y : Idx} {w : Wit} {s : SignType} (h : F.ipSign x y w = some s) :
    SignType.sign (ip (ival c r ε P x) (ival c r ε P y)) = s := by
  cases x with
  | circ m =>
    cases y with
    | circ _ => simp [ipSign] at h
    | pt j k t => exact R.ipSign_circ_pt h
  | pt j k t =>
    cases y with
    | circ m =>
      rw [ip_comm]
      exact R.ipSign_circ_pt h
    | pt j' k' t' =>
      simp only [ipSign] at h
      by_cases h1 : ((j, k, t) == (j', k', t')) = true
      · rw [if_pos h1] at h
        cases h
        simp only [beq_iff_eq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl, rfl⟩ := h1
        rw [(isPoint_pt (c := c) (r := r) (ε := ε) j k t).1, sign_zero]
      · rw [if_neg h1] at h
        by_cases h2 : (decide (F.IsLabel j k t) && decide (F.IsLabel j' k' t') &&
            F.distinctW (j, k, t) (j', k', t') w) = true
        · rw [if_pos h2] at h
          cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
          exact sign_neg (R.distW_neg (l := (j, k, t)) (l' := (j', k', t')) h2.1.1 h2.1.2 h2.2)
        · rw [if_neg h2] at h
          cases h


/-! ## Soundness of each tag -/

omit R in
lemma dep_true (x0 x1 x2 x3 x4 y : Idx) :
    ∀ cl ∈ F.encodeTag (.dep x0 x1 x2 x3 x4 y), clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [encodeTag, List.mem_append, List.mem_flatMap] at hcl
  rcases hcl with ⟨t, -, hcl⟩ | hcl
  · exact mulDef_true _ _ cl hcl
  · refine naeRel_true _ (by simp) ?_ cl hcl
    have h := nae_of_sum
      [-(qval c r ε P (.br x1 x2 x3 x4) * qval c r ε P (.ip x0 y)),
        qval c r ε P (.br x0 x2 x3 x4) * qval c r ε P (.ip x1 y),
        -(qval c r ε P (.br x0 x1 x3 x4) * qval c r ε P (.ip x2 y)),
        qval c r ε P (.br x0 x1 x2 x4) * qval c r ε P (.ip x3 y),
        -(qval c r ε P (.br x0 x1 x2 x3) * qval c r ε P (.ip x4 y))] (by
      simp only [List.sum_cons, List.sum_nil, qval]
      linear_combination dep5 (ival c r ε P x0) (ival c r ε P x1) (ival c r ε P x2)
        (ival c r ε P x3) (ival c r ε P x4) (ival c r ε P y))
    simpa [qval, Left.sign_neg] using h

omit R in
lemma gp_true (a b c' d e f : Idx) :
    ∀ cl ∈ F.encodeTag (.gp a b c' d e f), clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [encodeTag, List.mem_append, List.mem_flatMap] at hcl
  rcases hcl with ⟨t, -, hcl⟩ | hcl
  · exact mulDef_true _ _ cl hcl
  · refine naeRel_true _ (by simp) ?_ cl hcl
    have h := nae_of_sum
      [qval c r ε P (.br a b c' d) * qval c r ε P (.br a b e f),
        -(qval c r ε P (.br a b c' e) * qval c r ε P (.br a b d f)),
        qval c r ε P (.br a b c' f) * qval c r ε P (.br a b d e)] (by
      simp only [List.sum_cons, List.sum_nil, qval]
      linear_combination gp3 (ival c r ε P a) (ival c r ε P b) (ival c r ε P c')
        (ival c r ε P d) (ival c r ε P e) (ival c r ε P f))
    simpa [qval, Left.sign_neg] using h

lemma on_circle_of_order {m : ℕ} {l : ℕ × ℕ × ℤ} (hl : F.IsLabel l.1 l.2.1 l.2.2)
    (hm : l.1 = m ∨ l.2.1 = m) : dist2 (Fingerprint.pt P l) (c m) = r m ^ 2 := by
  have h := R.on_circles l.1 l.2.1 l.2.2 hl
  rcases hm with rfl | rfl
  · exact h.1
  · exact h.2

lemma f1_true (x y z : Idx) (m i1 i2 i3 i4 : ℕ) :
    ∀ cl ∈ F.encodeTag (.f1 x y z m i1 i2 i3 i4), clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [encodeTag] at hcl
  split_ifs at hcl with h
  · simp only [isCirc, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
      Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hm1, hm2⟩, h12⟩, h23⟩, h34⟩, h4⟩, ⟨hl1, o1⟩, ⟨hl2, o2⟩, ⟨hl3, o3⟩, ⟨hl4, o4⟩, -⟩ := h
    refine naeRel_true _ (by simp) ?_ cl hcl
    have key := f1_nae (hodge (ival c r ε P x) (ival c r ε P y) (ival c r ε P z)) (c m) (r m) (ε m)
      (R.on_circle_of_order hl1 o1) (R.on_circle_of_order hl2 o2) (R.on_circle_of_order hl3 o3)
      (R.on_circle_of_order hl4 o4)
      (R.cyclic m i1 i2 i3 hm1 hm2 h12 h23 (by omega)) (R.cyclic m i1 i2 i4 hm1 hm2 h12 (by omega) h4)
      (R.cyclic m i1 i3 i4 hm1 hm2 (by omega) h34 h4) (R.cyclic m i2 i3 i4 hm1 hm2 h23 h34 h4)
    simpa [qval, Pi, ival, br_eq_ip_hodge, Fingerprint.pt] using key
  · simp at hcl

omit R in
lemma perm_true (a b c' d : Idx) (k : ℕ) :
    ∀ cl ∈ F.encodeTag (.perm a b c' d k), clauseTrue c r ε P cl = true := by
  intro cl hcl
  match k, hcl with
  | 0, hcl => exact eqRel_true _ _ _ (by simp only [qval]; rw [br_swap01, Left.sign_neg]; simp) cl hcl
  | 1, hcl => exact eqRel_true _ _ _ (by simp only [qval]; rw [br_swap12, Left.sign_neg]; simp) cl hcl
  | 2, hcl => exact eqRel_true _ _ _ (by simp only [qval]; rw [br_swap23, Left.sign_neg]; simp) cl hcl
  | _ + 3, hcl => simp [encodeTag] at hcl

lemma ipFact_true (x y : Idx) (w : Wit) :
    ∀ cl ∈ F.encodeTag (.ipFact x y w), clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [encodeTag] at hcl
  split at hcl
  · next s hs => exact factRel_true _ _ (by simpa [qval] using R.ipSign_sound hs) cl hcl
  · simp at hcl

lemma knz_true (j k : ℕ) (w : Wit) :
    ∀ cl ∈ F.encodeTag (.knz j k w), clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [encodeTag] at hcl
  split_ifs at hcl with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact nzRel_true _ (by simpa [qval, C] using (R.pair_facts h.1 h.2).2) cl hcl
  · simp at hcl

lemma type3_true (j k : ℕ) (x : Idx) (plus : Bool) (w : Wit) :
    ∀ cl ∈ F.encodeTag (.type3 j k x plus w), clauseTrue c r ε P cl = true := by
  intro cl hcl
  simp only [encodeTag] at hcl
  by_cases h : (decide (F.IsLabel j k 1) && F.distinctW (j, k, 1) (j, k, -1) w) = true
  · rw [if_pos h] at hcl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hπ, -⟩ := R.pair_facts h.1 h.2
    have hp := R.pair' h.1
    cases plus
    · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append] at hcl
      rcases hcl with hcl | hcl
      · exact mulDef_true _ _ cl hcl
      · refine eqRel_true _ _ _ ?_ cl hcl
        have e := sign_eq_neg_of_mul_eq (hp.tieQ (ival c r ε P x)) hπ
        simpa [qval, C, sign_mul] using e
    · simp only [↓reduceIte, List.mem_append] at hcl
      rcases hcl with hcl | hcl
      · exact mulDef_true _ _ cl hcl
      · refine eqRel_true _ _ _ ?_ cl hcl
        have e := sign_eq_of_mul_neg_eq (hp.tieP (ival c r ε P x)) hπ
        simpa [qval, C, sign_mul] using e
  · rw [if_neg h] at hcl
    simp at hcl

lemma krupp_core {j k m a b : ℕ} {w wq : Wit} {s : ℤ} {useP : Bool}
    (h : (decide (F.IsLabel j k 1) && F.distinctW (j, k, 1) (j, k, -1) w && F.isCirc m &&
      m != j && m != k && F.side j k 1 m * F.side j k (-1) m == -1 && decide (F.IsLabel a b s) &&
      F.distinctW (a, b, s) (j, k, if useP then 1 else -1) wq) = true) :
    SignType.sign (qval c r ε P (.br (C j) (C k) (C m) (.pt a b s))) =
      1 * SignType.sign (qval c r ε P (.br (C j) (C k) (C m) (.pt j k 1))) := by
  simp only [isCirc, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hl, hw⟩, hm1, hm2⟩, hmj⟩, hmk⟩, hs⟩, hq⟩, hwq⟩ := h
  obtain ⟨hπ, hK⟩ := R.pair_facts hl hw
  have hl' : F.IsLabel j k (-1) := ⟨hl.1, hl.2.1, hl.2.2.1, Or.inr rfl⟩
  have hkr := R.ip_prod_neg (l := (j, k, 1)) (l' := (j, k, -1)) hl hl' hm1 hm2 hmj hmk hmj hmk hs
  have hst : ip (ival c r ε P (.pt a b s)) (ival c r ε P (.pt j k 1)) < 0 ∨
      ip (ival c r ε P (.pt a b s)) (ival c r ε P (.pt j k (-1))) < 0 := by
    cases useP
    · exact Or.inr (R.distW_neg (l := (a, b, s)) (l' := (j, k, -1)) hq hl' (by simpa using hwq))
    · exact Or.inl (R.distW_neg (l := (a, b, s)) (l' := (j, k, 1)) hq hl (by simpa using hwq))
  have kr := (R.pair' hl).krupp_sign hK hπ (c := ival c r ε P (.circ m))
    (q := ival c r ε P (.pt a b s)) hkr (ip_points_nonpos (isPoint_pt _ _ _) (isPoint_pt _ _ _))
    (ip_points_nonpos (isPoint_pt _ _ _) (isPoint_pt _ _ _)) hst
  simpa [qval, C] using sign_eq_of_mul_pos kr

lemma krupp_true (j k m : ℕ) (q : Idx) (w wq : Wit) (useP : Bool) :
    ∀ cl ∈ F.encodeTag (.krupp j k m q w wq useP), clauseTrue c r ε P cl = true := by
  intro cl hcl
  cases q with
  | circ _ => simp [encodeTag] at hcl
  | pt a b s =>
    simp only [encodeTag] at hcl
    by_cases h : (decide (F.IsLabel j k 1) && F.distinctW (j, k, 1) (j, k, -1) w && F.isCirc m &&
      m != j && m != k && F.side j k 1 m * F.side j k (-1) m == -1 && decide (F.IsLabel a b s) &&
      F.distinctW (a, b, s) (j, k, if useP then 1 else -1) wq) = true
    · rw [if_pos h] at hcl
      exact eqRel_true _ _ _ (R.krupp_core h) cl hcl
    · rw [if_neg h] at hcl
      simp at hcl

theorem encodeTag_sound (t : Tag) : ∀ cl ∈ F.encodeTag t, clauseTrue c r ε P cl = true := by
  cases t with
  | dep x0 x1 x2 x3 x4 y => exact dep_true x0 x1 x2 x3 x4 y
  | gp a b c' d e f => exact gp_true a b c' d e f
  | f1 x y z m i1 i2 i3 i4 => exact R.f1_true x y z m i1 i2 i3 i4
  | perm a b c' d k => exact perm_true a b c' d k
  | ipFact x y w => exact R.ipFact_true x y w
  | knz j k w => exact R.knz_true j k w
  | type3 j k x plus w => exact R.type3_true j k x plus w
  | krupp j k m q w wq useP => exact R.krupp_true j k m q w wq useP

/-- **Soundness of the encoding**: the actual signs of a circle realization satisfy every
clause of `encode F tags`. -/
theorem encode_sound (tags : List Tag) : ∀ cl ∈ F.encode tags, clauseTrue c r ε P cl = true := by
  intro cl hcl
  obtain ⟨t, -, hcl⟩ := List.mem_flatMap.1 hcl
  exact R.encodeTag_sound t cl hcl

end Fingerprint.IsCircleRealization

end NonCirc
