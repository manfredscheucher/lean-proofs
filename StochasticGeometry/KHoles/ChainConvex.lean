/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import KHoles.ChainSlopes

/-!
# Convex position of padded chains

Step 5b of `doc/kholes/kholes.md` (second part). For sorted abscissae
`0 < x 0 < … < x n < 1` and positive heights `Y`, the configuration
`baseCfg (zip2 x Y) = (0,0), (1,0), (x 0, Y 0), …, (x n, Y n)` is in convex position iff the
chain `P_0 = (0,0), P_1, …, P_{n+1}, P_{n+2} = (1,0)` (`P_j = (xpad x j, ypad Y j)`) is
strictly concave, i.e. `Y ∈ Admissible x` (`convexIndependent_iff_admissible`).

* `⇐`: every `P_j` is strictly separated from the other vertices by an affine functional:
  `-t` for `P_0`, `t - 1` for `P_{n+2}`, and `y - (ℓ_{j-1}(t) + ℓ_j(t)) / 2` for an interior
  vertex (`ypad_le_edge`, `ypad_lt_edge` of `ChainSlopes.lean`).
* `⇒`: if `slope (i+1) ≥ slope i`, the vertex `P_{i+1}` lies on or below the chord
  `[P_i, P_{i+2}]` and above the base `[(0,0),(1,0)]`, hence in the hull of the other points.

Used by `UpperCap.lean`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace KHoles

/-- An open half-plane `{p | a p.1 + b p.2 + c < 0}` is convex. -/
private lemma convex_affHalf (a b c : ℝ) : Convex ℝ {p : ℝ × ℝ | a * p.1 + b * p.2 + c < 0} := by
  intro p hp q hq s t hs ht hst
  simp only [mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hp hq ⊢
  have e : a * (s * p.1 + t * q.1) + b * (s * p.2 + t * q.2) + c =
      s * (a * p.1 + b * p.2 + c) + t * (a * q.1 + b * q.2 + c) := by
    linear_combination (-c) * hst
  rw [e]
  rcases hs.lt_or_eq with hs | rfl
  · nlinarith [mul_neg_of_pos_of_neg hs hp, mul_nonpos_of_nonneg_of_nonpos ht hq.le]
  · simp only [zero_add] at hst; subst hst; simpa using hq

/-- Convex independence from strict separating affine functionals. -/
private lemma convexIndependent_of_separating {ι : Type*} (q : ι → ℝ × ℝ)
    (h : ∀ i, ∃ a b c : ℝ, a * (q i).1 + b * (q i).2 + c = 0 ∧
      ∀ j, j ≠ i → a * (q j).1 + b * (q j).2 + c < 0) : ConvexIndependent ℝ q := by
  rw [convexIndependent_iff_notMem_convexHull_sdiff]
  intro i s hi
  obtain ⟨a, b, c, h0, hlt⟩ := h i
  have hsub : convexHull ℝ (q '' (s \ {i})) ⊆ {p : ℝ × ℝ | a * p.1 + b * p.2 + c < 0} := by
    refine convexHull_min ?_ (convex_affHalf a b c)
    rintro _ ⟨j, hj, rfl⟩
    exact hlt j (by simpa using hj.2)
  have := hsub hi
  simp only [mem_ofPred_eq] at this
  linarith

/-- The point `(xb, yb)` lies in every convex set containing `(xa, ya)`, `(xc, yc)`,
`(0,0)` and `(1,0)` if it is on or below the chord and above the base. -/
private lemma mem_of_below_chord {S : Set (ℝ × ℝ)} (hS : Convex ℝ S) {xa xb xc ya yb yc : ℝ}
    (hA : (xa, ya) ∈ S) (hC : (xc, yc) ∈ S) (hO : ((0 : ℝ), (0 : ℝ)) ∈ S)
    (hE : ((1 : ℝ), (0 : ℝ)) ∈ S) (hab : xa < xb) (hbc : xb < xc) (hb0 : 0 ≤ xb)
    (hb1 : xb ≤ 1) (hyb : 0 ≤ yb)
    (hchord : yb * (xc - xa) ≤ ya * (xc - xb) + yc * (xb - xa)) : (xb, yb) ∈ S := by
  have hca : 0 < xc - xa := by linarith
  set lam := (xb - xa) / (xc - xa) with hlam
  have hl0 : 0 ≤ lam := div_nonneg (by linarith) hca.le
  have hl1 : lam ≤ 1 := (div_le_one hca).mpr (by linarith)
  set h := (1 - lam) * ya + lam * yc with hh
  have hxchord : (1 - lam) * xa + lam * xc = xb := by
    rw [hlam]; field_simp; ring
  have hyh : yb ≤ h := by
    rw [hh, hlam, ← mul_le_mul_iff_of_pos_right hca]
    have : ((1 - (xb - xa) / (xc - xa)) * ya + (xb - xa) / (xc - xa) * yc) * (xc - xa) =
        ya * (xc - xb) + yc * (xb - xa) := by field_simp; ring
    rw [this]; exact hchord
  have hC' : (xb, h) ∈ S := by
    have := hS hA hC (by linarith : (0 : ℝ) ≤ 1 - lam) hl0 (by ring)
    convert this using 1
    ext <;> simp [hxchord, hh]
  have hB' : (xb, (0 : ℝ)) ∈ S := by
    have := hS hO hE (by linarith : (0 : ℝ) ≤ 1 - xb) hb0 (by ring)
    convert this using 1
    ext <;> simp
  rcases (hyb.trans hyh).lt_or_eq with hpos | hzero
  · set s := yb / h
    have hs0 : 0 ≤ s := div_nonneg hyb hpos.le
    have hs1 : s ≤ 1 := (div_le_one hpos).mpr hyh
    have := hS hC' hB' hs0 (by linarith : (0 : ℝ) ≤ 1 - s) (by ring)
    convert this using 1
    ext
    · simp; ring
    · simp [s]; field_simp
  · have : yb = 0 := le_antisymm (hzero ▸ hyh) hyb
    rw [this]; exact hB'


/-! ### Indexing `baseCfg (zip2 x Y)` by padded indices -/

/-- Padded index of the points of `baseCfg (zip2 x Y)`: `0 ↦ 0`, `1 ↦ n + 2`,
`i + 2 ↦ i + 1`. -/
def chainIdx (n : ℕ) : Fin (n + 1 + 2) → ℕ :=
  Fin.cons 0 (Fin.cons (n + 2) fun i : Fin (n + 1) => (i : ℕ) + 1)

variable {n : ℕ}

@[simp] lemma chainIdx_zero : chainIdx n 0 = 0 := rfl

@[simp] lemma chainIdx_one : chainIdx n 1 = n + 2 := rfl

@[simp] lemma chainIdx_succ_succ (i : Fin (n + 1)) : chainIdx n i.succ.succ = (i : ℕ) + 1 := rfl

private lemma fin_cases3 (i : Fin (n + 1 + 2)) : i = 0 ∨ i = 1 ∨ ∃ k : Fin (n + 1), i = k.succ.succ :=
  Fin.cases (Or.inl rfl) (fun i => Fin.cases (Or.inr (Or.inl rfl))
    (fun k => Or.inr (Or.inr ⟨k, rfl⟩)) i) i

lemma chainIdx_le (i : Fin (n + 1 + 2)) : chainIdx n i ≤ n + 2 := by
  rcases fin_cases3 i with rfl | rfl | ⟨k, rfl⟩
  · simp
  · simp
  · simp only [chainIdx_succ_succ]; omega

lemma chainIdx_injective : Function.Injective (chainIdx n) := by
  intro i j h
  rcases fin_cases3 i with rfl | rfl | ⟨k, rfl⟩ <;>
    rcases fin_cases3 j with rfl | rfl | ⟨l, rfl⟩ <;>
    simp only [chainIdx_zero, chainIdx_one, chainIdx_succ_succ] at h <;>
    first | rfl | omega | (congr 2; exact Fin.ext (by omega))

lemma chainIdx_surj {j : ℕ} (hj : j ≤ n + 2) : ∃ i, chainIdx n i = j := by
  rcases j with _ | k
  · exact ⟨0, rfl⟩
  · by_cases hk : k < n + 1
    · exact ⟨(⟨k, hk⟩ : Fin (n + 1)).succ.succ, rfl⟩
    · exact ⟨1, by simp; omega⟩

lemma baseCfg_zip2_apply (x Y : Fin (n + 1) → ℝ) (i : Fin (n + 1 + 2)) :
    baseCfg (zip2 x Y) i = (xpad x (chainIdx n i), ypad Y (chainIdx n i)) := by
  rcases fin_cases3 i with rfl | rfl | ⟨k, rfl⟩
  · simp [xpad, ypad]
  · rw [baseCfg_one, chainIdx_one, xpad_last, ypad_last]
  · rw [baseCfg_succ_succ, zip2_apply, chainIdx_succ_succ, xpad_succ_fin, ypad_succ_fin]

/-! ### `⇐`: separating functionals -/

variable {x Y : Fin (n + 1) → ℝ}

/-- Every vertex `P_j` of an admissible chain is strictly separated from the other vertices
by an affine functional. -/
lemma chain_separating (hx : StrictMono x) (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1)
    (hY : Y ∈ Admissible x) {j : ℕ} (hj : j ≤ n + 2) :
    ∃ a b c : ℝ, a * xpad x j + b * ypad Y j + c = 0 ∧
      ∀ j', j' ≤ n + 2 → j' ≠ j → a * xpad x j' + b * ypad Y j' + c < 0 := by
  have hmono := xpad_mono hx h0 h1
  rcases j with _ | k
  · -- `P_0 = (0,0)`: the functional `-t`
    refine ⟨-1, 0, 0, by simp [xpad], fun j' _ hj' => ?_⟩
    have h01 : xpad x 0 < xpad x 1 := xpad_lt_succ hx h0 h1 (by omega)
    have h1j : xpad x 1 ≤ xpad x j' := hmono (by omega)
    have : xpad x 0 = 0 := rfl
    linarith
  by_cases hk : k = n + 1
  · -- `P_{n+2} = (1,0)`: the functional `t - 1`
    subst hk
    refine ⟨1, 0, -1, by rw [xpad_last]; ring, fun j' hj'1 hj' => ?_⟩
    have h1 : xpad x (n + 1) < xpad x (n + 1 + 1) := xpad_lt_succ hx h0 h1 (by omega)
    have h2 : xpad x j' ≤ xpad x (n + 1) := hmono (by omega)
    have : xpad x (n + 1 + 1) = 1 := xpad_last x
    linarith
  · -- interior vertex `P_{k+1}`: the functional `y - (ℓ_k(t) + ℓ_{k+1}(t)) / 2`
    have hkn : k ≤ n := by omega
    refine ⟨-(slope x Y k + slope x Y (k + 1)) / 2, 1,
      -(ypad Y k - slope x Y k * xpad x k + ypad Y (k + 1) - slope x Y (k + 1) * xpad x (k + 1))
        / 2, ?_, fun j' hj'1 hj' => ?_⟩
    · have hs := ypad_succ_eq (Y := Y) hx h0 h1 (k := k) (by omega)
      linear_combination (1 / 2 : ℝ) * hs
    · by_cases hj2 : j' = k + 2
      · have hs := ypad_lt_edge hx h0 h1 hY (j := j') (k := k) hj'1 (by omega) (by omega)
          (by omega)
        have hw := ypad_le_edge hx h0 h1 hY (j := j') (k := k + 1) hj'1 (by omega)
        linear_combination (1 / 2 : ℝ) * hs + (1 / 2 : ℝ) * hw
      · have hs := ypad_lt_edge hx h0 h1 hY (j := j') (k := k + 1) hj'1 (by omega) hj'
          (by omega)
        have hw := ypad_le_edge hx h0 h1 hY (j := j') (k := k) hj'1 (by omega)
        linear_combination (1 / 2 : ℝ) * hs + (1 / 2 : ℝ) * hw

/-! ### The main equivalence -/

/-- For sorted abscissae in `(0,1)` and positive heights, the points `(0,0), (1,0),
(x i, Y i)` are in convex position iff the chain is strictly concave. -/
theorem convexIndependent_iff_admissible {n : ℕ} {x Y : Fin (n + 1) → ℝ} (hx : StrictMono x)
    (h0 : 0 < x 0) (h1 : x (Fin.last n) < 1) (hY : ∀ i, 0 < Y i) :
    ConvexIndependent ℝ (baseCfg (zip2 x Y)) ↔ Y ∈ Admissible x := by
  constructor
  · intro hci
    by_contra hadm
    obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), slope x Y i ≤ slope x Y ((i : ℕ) + 1) := by
      by_contra h
      exact hadm fun i => lt_of_not_ge fun hi => h ⟨i, hi⟩
    rw [convexIndependent_iff_notMem_convexHull_sdiff] at hci
    apply hci i.succ.succ univ
    have hmem : ∀ j, j ≤ n + 2 → j ≠ (i : ℕ) + 1 → (xpad x j, ypad Y j) ∈
        convexHull ℝ (baseCfg (zip2 x Y) '' (univ \ {i.succ.succ})) := by
      intro j hj hji
      obtain ⟨k, hk⟩ := chainIdx_surj hj
      apply subset_convexHull
      refine ⟨k, ⟨mem_univ _, ?_⟩, ?_⟩
      · rintro rfl
        rw [chainIdx_succ_succ] at hk
        exact hji hk.symm
      · rw [baseCfg_zip2_apply, hk]
    rw [baseCfg_zip2_apply, chainIdx_succ_succ]
    have hO := hmem 0 (by omega) (by omega)
    have hE := hmem (n + 2) le_rfl (by omega)
    rw [xpad_last, ypad_last] at hE
    have hab : xpad x i < xpad x ((i : ℕ) + 1) := xpad_lt_succ hx h0 h1 (by omega)
    have hbc : xpad x ((i : ℕ) + 1) < xpad x ((i : ℕ) + 1 + 1) :=
      xpad_lt_succ hx h0 h1 (by omega)
    rw [slope, slope, div_le_div_iff₀ (by linarith) (by linarith)] at hi
    refine mem_of_below_chord (convex_convexHull ℝ _) (hmem i (by omega) (by omega))
      (hmem ((i : ℕ) + 1 + 1) (by omega) (by omega)) hO hE hab hbc ?_ ?_ ?_ ?_
    · rw [xpad_succ_fin]; exact (x_pos hx h0 i).le
    · rw [xpad_succ_fin]; exact (x_lt_one hx h1 i).le
    · rw [ypad_succ_fin]; exact (hY i).le
    · linear_combination hi
  · intro hadm
    apply convexIndependent_of_separating
    intro i
    obtain ⟨a, b, c, h0', hlt⟩ := chain_separating hx h0 h1 hadm (chainIdx_le i)
    refine ⟨a, b, c, ?_, fun i' hi' => ?_⟩
    · rw [baseCfg_zip2_apply]; exact h0'
    · rw [baseCfg_zip2_apply]
      exact hlt _ (chainIdx_le i') fun h => hi' (chainIdx_injective h)

end KHoles
