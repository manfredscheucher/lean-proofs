/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): processing the next curve (proof of `process_step`)

With `c 0, …, c (k-1)` processed (`CanonUpTo c k`), the lens `Q = int (c k) ∩ ext (c (k-1))` is
transversal (`twoTransversal_of_canon`: the unprocessed curves cross `c k` outside `c (k-1)` and
`c (k-1)` inside `c k`; the processed ones do not meet `Q`). Its vertices are crossings of two
unprocessed curves (`idx_ge_of_vertex`), so a lens flip changes the interior status only for
triples of curves whose smallest index is `≥ k`: the invariant is kept. After the zipping, `Q`
has no vertex, which gives the triples with smallest index `k`.
-/
import Pca.FlipGraph.Canon
import Pca.FlipGraph.Zip
import Pca.FlipGraph.FlipCross

open Equiv Finset

namespace Pca.FlipGraph

universe u

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- The invariant with the pair of curves in either order. -/
theorem canon_cross {M : Marked n D} {c : Fin n ≃ Fin n} {k : ℕ} (hinv : M.CanonUpTo c k)
    {i u v : Fin n} (hiu : i ≠ u) (hiv : i ≠ v) (huv : u ≠ v)
    (hmin : i.val < k ∨ u.val < k ∨ v.val < k) {x : M.A.Crossing}
    (hx : Arrangement.Crossing.curves M.A x = {c u, c v}) :
    M.CrossInside (c i) x ↔ (u < i ∧ i < v) ∨ (v < i ∧ i < u) := by
  rcases lt_or_gt_of_ne huv with h | h
  · rw [hinv i u v hiu hiv h (by rcases hmin with h' | h' | h' <;> [left; right; right] <;>
      first | exact h' | (have : u.val < v.val := h; omega)) x hx]
    constructor
    · exact Or.inl
    · rintro (h' | ⟨h1, h2⟩)
      · exact h'
      · exact absurd (h1.trans h2) (lt_asymm h)
  · rw [Finset.pair_comm] at hx
    rw [hinv i v u hiv hiu h (by rcases hmin with h' | h' | h' <;> [left; right; right] <;>
      first | exact h' | (have : v.val < u.val := h; omega)) x hx]
    constructor
    · exact Or.inr
    · rintro (⟨h1, h2⟩ | h')
      · exact absurd (h1.trans h2) (lt_asymm h)
      · exact h'

/-- **The lens `int (c k) ∩ ext (c (k-1))` is transversal** (crossing form). -/
theorem twoTransversal_of_canon {M : Marked n D} {c : Fin n ≃ Fin n} {k : ℕ}
    (hinv : M.CanonUpTo c k) (hk : 1 ≤ k) (hkn : k < n) :
    M.TwoTransversal (c ⟨k, hkn⟩) (c ⟨k - 1, by omega⟩) True False := by
  intro c' h1 h2
  obtain ⟨u, rfl⟩ := c.surjective c'
  have hu1 : u ≠ ⟨k, hkn⟩ := fun h => h1 (by rw [h])
  have hu2 : u ≠ ⟨k - 1, by omega⟩ := fun h => h2 (by rw [h])
  have hu1' : u.val ≠ k := fun h => hu1 (Fin.ext h)
  have hu2' : u.val ≠ k - 1 := fun h => hu2 (Fin.ext h)
  have hLR : (⟨k - 1, by omega⟩ : Fin n) ≠ ⟨k, hkn⟩ := fun h => by
    have := congrArg Fin.val h; simp at this; omega
  have hR : (⟨k - 1, by omega⟩ : Fin n).val < k := by show k - 1 < k; omega
  have hL : (⟨k, hkn⟩ : Fin n).val < k + 1 := by show k < k + 1; omega
  by_cases hgt : k < u.val
  · left
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [canon_cross hinv (Ne.symm hu2) hLR hu1 (Or.inl hR) hx, iff_false]
      simp only [Fin.lt_def]; omega
    · rw [canon_cross hinv (Ne.symm hu1) hLR.symm hu2 (Or.inr (Or.inr hR)) hx, iff_true]
      simp only [Fin.lt_def]; omega
  · right
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [canon_cross hinv (Ne.symm hu2) hLR hu1 (Or.inl hR) hx, iff_false, not_not]
      simp only [Fin.lt_def]; omega
    · rw [canon_cross hinv (Ne.symm hu1) hLR.symm hu2 (Or.inr (Or.inr hR)) hx, iff_true]
      simp only [Fin.lt_def]; omega

/-- A crossing inside `c k` and outside `c (k-1)`, not on them, is a crossing of two unprocessed
curves (indices `> k`). -/
theorem idx_gt_of_lens {M : Marked n D} {c : Fin n ≃ Fin n} {k : ℕ} (hinv : M.CanonUpTo c k)
    (hk : 1 ≤ k) (hkn : k < n) {u v : Fin n} (huv : u ≠ v) {x : M.A.Crossing}
    (hx : Arrangement.Crossing.curves M.A x = {c u, c v})
    (hL : u ≠ ⟨k, hkn⟩) (hL' : v ≠ ⟨k, hkn⟩) (hR : u ≠ ⟨k - 1, by omega⟩)
    (hR' : v ≠ ⟨k - 1, by omega⟩)
    (hin : M.CrossInside (c ⟨k, hkn⟩) x) (hout : ¬ M.CrossInside (c ⟨k - 1, by omega⟩) x) :
    k < u.val := by
  have hu1 : u.val ≠ k := fun h => hL (Fin.ext h)
  have hv1 : v.val ≠ k := fun h => hL' (Fin.ext h)
  have hu2 : u.val ≠ k - 1 := fun h => hR (Fin.ext h)
  have hv2 : v.val ≠ k - 1 := fun h => hR' (Fin.ext h)
  have hrk : (⟨k - 1, by omega⟩ : Fin n).val < k := by show k - 1 < k; omega
  have hlk : ¬ (⟨k, hkn⟩ : Fin n).val < k := by show ¬ k < k; omega
  by_contra hu
  by_cases hv : k < v.val
  · -- `u` processed, `v` not: the crossing is inside `c (k-1)`
    apply hout
    rw [canon_cross hinv (Ne.symm hR) (Ne.symm hR') huv (Or.inl hrk) hx]
    simp only [Fin.lt_def]; omega
  · -- both processed: the crossing is outside `c k`
    have := (canon_cross hinv (Ne.symm hL) (Ne.symm hL') huv
      (Or.inr (Or.inl (by omega))) hx).1 hin
    simp only [Fin.lt_def] at this; omega

/-- The curves of a source triangle of the lens `int (c k) ∩ ext (c (k-1))` have index `≥ k`. -/
theorem tri_idx {M : Marked n D} {c : Fin n ≃ Fin n} {k : ℕ} (hinv : M.CanonUpTo c k)
    (hk : 1 ≤ k) (hkn : k < n) (hne : c ⟨k, hkn⟩ ≠ c ⟨k - 1, by omega⟩) {d : D}
    (hT : M.A.IsTriangle (M.A.cellOf d)) (hsrc : (M.twoLens hne True False).SourceTri d)
    {b : D} (hb : M.A.cellOf b = M.A.cellOf d) : k ≤ (c.symm (M.A.curve b)).val := by
  obtain ⟨⟨hdL, hdQ⟩, -, hv⟩ := hsrc
  set Λ := M.twoLens hne True False
  have hchord : ∀ y, Λ.Chord y → M.A.curve y ≠ c ⟨k, hkn⟩ ∧ M.A.curve y ≠ c ⟨k - 1, by omega⟩ := by
    rintro y ⟨h1, h2⟩
    exact ⟨fun hy => M.not_twoQ_α_of_L y hy h1 h2, fun hy => M.not_twoQ_α_of_R y hy h1 h2⟩
  set w := M.A.φ (M.A.φ d)
  have hw : M.A.cellOf w = M.A.cellOf d := by rw [M.A.cellOf_φ, M.A.cellOf_φ]
  have hcw : Λ.Chord w := hv w (Orbit.mem_darts.2 rfl)
  have hcσw : Λ.Chord (M.A.σ w) := hv _ (Orbit.mem_darts.2 (M.A.crossingOf_σ w))
  have hcurves : Arrangement.Crossing.curves M.A (M.A.crossingOf w) =
      {M.A.curve w, M.A.curve (M.A.φ d)} := by
    have hTw : M.A.IsTriangle (M.A.cellOf w) := by rw [hw]; exact hT
    rw [M.A.curves_crossingOf, Arrangement.curve_σ_tri hTw]
    rw [show M.A.φ (M.A.φ w) = M.A.φ d by
      show M.A.φ (M.A.φ (M.A.φ (M.A.φ d))) = M.A.φ d; rw [Arrangement.tri_φφφ hT]]
  have hnotL : c ⟨k, hkn⟩ ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf w) := by
    rw [M.A.curves_crossingOf, mem_insert, mem_singleton, not_or]
    exact ⟨fun h => (hchord w hcw).1 h.symm, fun h => (hchord _ hcσw).1 h.symm⟩
  have hnotR : c ⟨k - 1, by omega⟩ ∉ Arrangement.Crossing.curves M.A (M.A.crossingOf w) := by
    rw [M.A.curves_crossingOf, mem_insert, mem_singleton, not_or]
    exact ⟨fun h => (hchord w hcw).2 h.symm, fun h => (hchord _ hcσw).2 h.symm⟩
  have hin : M.CrossInside (c ⟨k, hkn⟩) (M.A.crossingOf w) := by
    rw [M.crossInside_iff hnotL, hw]; exact hdQ.1.2 trivial
  have hout : ¬ M.CrossInside (c ⟨k - 1, by omega⟩) (M.A.crossingOf w) := by
    rw [M.crossInside_iff hnotR, hw]; exact fun h => hdQ.2.1 h
  have hne' : M.A.curve w ≠ M.A.curve (M.A.φ d) := by
    have := M.A.curve_φ_ne (M.A.φ d); exact this
  have key : ∀ e₁ e₂ : Fin n, e₁ ≠ e₂ →
      Arrangement.Crossing.curves M.A (M.A.crossingOf w) = {e₁, e₂} → k < (c.symm e₁).val := by
    intro e₁ e₂ he hx
    have hx' : Arrangement.Crossing.curves M.A (M.A.crossingOf w) =
        {c (c.symm e₁), c (c.symm e₂)} := by simpa using hx
    have hm₁ : e₁ ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf w) := by rw [hx]; simp
    have hm₂ : e₂ ∈ Arrangement.Crossing.curves M.A (M.A.crossingOf w) := by rw [hx]; simp
    refine idx_gt_of_lens hinv hk hkn (fun h => he (by simpa using congrArg c h)) hx'
      ?_ ?_ ?_ ?_ hin hout
    · intro h; apply hnotL; rw [← h]; simpa using hm₁
    · intro h; apply hnotL; rw [← h]; simpa using hm₂
    · intro h; apply hnotR; rw [← h]; simpa using hm₁
    · intro h; apply hnotR; rw [← h]; simpa using hm₂
  rcases (Arrangement.tri_mem_iff hT).1 hb with rfl | rfl | rfl
  · rw [hdL, Equiv.symm_apply_apply]
  · exact (key _ _ hne'.symm (by rw [hcurves, Finset.pair_comm])).le
  · exact (key _ _ hne' hcurves).le

/-- **One lens flip keeps the invariant** (and cylindricity, and the side of the marked cell on
the first curve). -/
theorem lensFlip_step {N N' : Marked n D} {c : Fin n ≃ Fin n} {k : ℕ} (hinv : N.CanonUpTo c k)
    (hmark : N.MarkOnFirst c) (hcyl : N.Cylindrical) (hk : 1 ≤ k) (hkn : k < n)
    (hne : c ⟨k, hkn⟩ ≠ c ⟨k - 1, by omega⟩) (hf : Marked.LensFlip hne True False N N') :
    CylStep N N' ∧ N'.CanonUpTo c k ∧ N'.MarkOnFirst c := by
  obtain ⟨d, hT, hsrc, rfl⟩ := hf
  have hdQ := hsrc.1.2
  have hdin : N.Inside (c ⟨k, hkn⟩) (N.A.cellOf d) := hdQ.1.2 trivial
  have hz : N.A.cellOf d ≠ N.z := fun e => N.not_inside_z _ (e ▸ hdin)
  -- the curves at the corners of the triangle have index `≥ k`
  have hcorner : ∀ y, N.A.IsCorner d y → ∀ e ∈ Arrangement.Crossing.curves N.A (N.A.crossingOf y),
      k ≤ (c.symm e).val := by
    intro y hy e he
    obtain ⟨b, hb, hby⟩ := mem_image.1 hy
    rw [Orbit.mem_darts] at hb
    change N.A.cellOf b = N.A.cellOf d at hb
    rw [← hby, N.A.curves_crossingOf, mem_insert, mem_singleton] at he
    have hTb : N.A.IsTriangle (N.A.cellOf b) := by rw [hb]; exact hT
    rcases he with rfl | rfl
    · exact tri_idx hinv hk hkn hne hT hsrc hb
    · rw [Arrangement.curve_σ_tri hTb]
      exact tri_idx hinv hk hkn hne hT hsrc (by rw [N.A.cellOf_φ, N.A.cellOf_φ, hb])
  have hside : ∀ C, N.HasSideOn C (N.A.cellOf d) → k ≤ (c.symm C).val := by
    rintro C ⟨b, hb, rfl⟩
    rw [Orbit.mem_darts] at hb
    exact tri_idx hinv hk hkn hne hT hsrc hb
  refine ⟨⟨⟨d, hT, hz, rfl⟩, hcyl, ?_⟩, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hcyl
    have hpT : p ≠ N.A.cellOf d := fun e => hdQ.2.1 (e ▸ hp _)
    refine ⟨Arrangement.flipCellEquiv hT p, fun C => ?_⟩
    rw [flip_inside N hT hz]
    exact iff_of_true (hp C) (fun h => hpT h.1)
  · intro i j l hij hil hjl hmin x hx
    obtain ⟨y, rfl⟩ := x.exists_mk
    change Arrangement.Crossing.curves N.A (N.A.crossingOf y) = _ at hx
    have hnot : c i ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf y) := by
      rw [hx, mem_insert, mem_singleton, not_or]
      exact ⟨fun h => hij (c.injective h), fun h => hil (c.injective h)⟩
    change (N.flip d hT).CrossInside (c i) (N.A.crossingOf y) ↔ _
    rw [crossInside_flip N hT hz y hnot, hinv i j l hij hil hjl hmin _ hx]
    have : ¬ (N.A.IsCorner d y ∧ N.HasSideOn (c i) (N.A.cellOf d)) := by
      rintro ⟨hc, hs⟩
      have h1 := hside _ hs
      have h2 := hcorner y hc (c j) (by rw [hx]; simp)
      have h3 := hcorner y hc (c l) (by rw [hx]; simp)
      simp only [Equiv.symm_apply_apply] at h1 h2 h3
      omega
    tauto
  · obtain ⟨y, hy, hy0⟩ := hmark
    have hyc : ¬ N.A.IsCorner d y := fun hc => by
      have := hcorner y hc _ (N.A.mem_curves_crossingOf y); omega
    refine ⟨y, ?_, hy0⟩
    change (N.A.flip d hT).cellOf y = Arrangement.flipCellEquiv hT N.z
    rw [Arrangement.flip_cellOf_of_not_corner hT hyc, hy]

/-- **After the zipping** (no vertex in the lens) the curve `c k` is processed. -/
theorem canon_succ {N : Marked n D} {c : Fin n ≃ Fin n} {k : ℕ} (hinv : N.CanonUpTo c k)
    (hk : 1 ≤ k) (hkn : k < n) (hne : c ⟨k, hkn⟩ ≠ c ⟨k - 1, by omega⟩)
    (hv : ∀ x, ¬ (N.twoLens hne True False).IsVertex x)
    (htr : (N.twoLens hne True False).Transversal) : N.CanonUpTo c (k + 1) := by
  set kL : Fin n := ⟨k, hkn⟩
  set kR : Fin n := ⟨k - 1, by omega⟩
  set Λ := N.twoLens hne True False
  have hRk : kR.val < k := by show k - 1 < k; omega
  -- a crossing not on `c k`, `c (k-1)` with the sides of the lens is a vertex
  have vertex_of : ∀ y, c kL ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf y) →
      c kR ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf y) →
      N.Inside (c kL) (N.A.cellOf y) → ¬ N.Inside (c kR) (N.A.cellOf y) →
      Λ.IsVertex (N.A.crossingOf y) := by
    intro y hL hR hin hout w hw
    rw [Orbit.mem_darts] at hw
    change N.A.crossingOf w = N.A.crossingOf y at hw
    have hq : ∀ w', N.A.crossingOf w' = N.A.crossingOf y → N.TwoQ (c kL) (c kR) True False
        (N.A.cellOf w') := fun w' hw' => by
      have hL' : c kL ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf w') := by rw [hw']; exact hL
      have hR' : c kR ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf w') := by rw [hw']; exact hR
      have e1 : N.Inside (c kL) (N.A.cellOf w') ↔ N.Inside (c kL) (N.A.cellOf y) := by
        rw [← N.crossInside_iff hL', ← N.crossInside_iff hL, hw']
      have e2 : N.Inside (c kR) (N.A.cellOf w') ↔ N.Inside (c kR) (N.A.cellOf y) := by
        rw [← N.crossInside_iff hR', ← N.crossInside_iff hR, hw']
      exact ⟨iff_true_intro (e1.2 hin), iff_false_intro (fun h => hout (e2.1 h))⟩
    exact ⟨hq w hw, by rw [← N.A.cellOf_σ]; exact hq _ (by rw [N.A.crossingOf_σ, hw])⟩
  intro i j l hij hil hjl hmin x hx
  by_cases hold : i.val < k ∨ j.val < k
  · exact hinv i j l hij hil hjl hold x hx
  push Not at hold
  obtain ⟨y, rfl⟩ := x.exists_mk
  change Arrangement.Crossing.curves N.A (N.A.crossingOf y) = _ at hx
  change N.CrossInside (c i) (N.A.crossingOf y) ↔ _
  have hjl' : j.val < l.val := hjl
  rcases hmin with hi | hj
  · -- `i = k`: no crossing of two later curves lies inside `c k`
    have hi' : i = kL := Fin.ext (by show i.val = k; omega)
    have hjk : k < j.val := by
      have : j.val ≠ k := fun h => hij (Fin.ext (by rw [h]; omega)); omega
    subst hi'
    have hrhs : ¬ (j < kL ∧ kL < l) := fun h => by have h' : j.val < k := h.1; omega
    rw [iff_false_intro hrhs, iff_false]
    have hLx : c kL ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf y) := by
      rw [hx, mem_insert, mem_singleton, not_or]
      exact ⟨fun h => hij (c.injective h), fun h => hil (c.injective h)⟩
    have hRx : c kR ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf y) := by
      rw [hx, mem_insert, mem_singleton, not_or]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · have := congrArg Fin.val (c.injective h); simp [kR] at this; omega
      · have := congrArg Fin.val (c.injective h); simp [kR] at this; omega
    have hout : ¬ N.CrossInside (c kR) (N.A.crossingOf y) := by
      rw [canon_cross hinv (i := kR) (u := j) (v := l)
        (fun h => by have := congrArg Fin.val h; simp [kR] at this; omega)
        (fun h => by have := congrArg Fin.val h; simp [kR] at this; omega)
        (fun h => by rw [h] at hjl'; omega) (Or.inl hRk) hx]
      simp only [Fin.lt_def]; omega
    intro hin
    change N.CrossInside (c kL) (N.A.crossingOf y) at hin
    rw [N.crossInside_iff hLx] at hin
    rw [N.crossInside_iff hRx] at hout
    exact hv _ (vertex_of y hLx hRx hin hout)
  · -- `j = k`: the crossings of `c k` and a later `c l` lie inside exactly the `c i`, `i < l`
    have hj' : j = kL := Fin.ext (by show j.val = k; omega)
    subst hj'
    have hik : k < i.val := by
      have : i.val ≠ k := fun h => hij (Fin.ext h); omega
    have hlk : k < l.val := hjl'
    have hkLi : kL < i := by show k < i.val; omega
    rw [and_iff_right hkLi]
    have hlne : c l ≠ c kL := fun h => by
      have := congrArg Fin.val (c.injective h); simp [kL] at this; omega
    have hlneR : c l ≠ c kR := fun h => by
      have := congrArg Fin.val (c.injective h); simp [kR] at this; omega
    -- the dart `w` of `c l` at `x` going into the interior of `c k`
    obtain ⟨w₀, hw₀, hw₀x⟩ : ∃ w₀, N.A.curve w₀ = c l ∧ N.A.crossingOf w₀ = N.A.crossingOf y := by
      rw [N.A.curves_crossingOf] at hx
      by_cases h0 : N.A.curve y = c l
      · exact ⟨y, h0, rfl⟩
      · refine ⟨N.A.σ y, ?_, N.A.crossingOf_σ y⟩
        have h1 : N.A.curve (N.A.σ y) ∈ ({c kL, c l} : Finset (Fin n)) := by rw [← hx]; simp
        have h2 : N.A.curve y ∈ ({c kL, c l} : Finset (Fin n)) := by rw [← hx]; simp
        rcases mem_insert.1 h1 with h' | h'
        · rcases mem_insert.1 h2 with h'' | h''
          · exact absurd (h'.trans h''.symm) (N.A.isArrangement.curve_σ y)
          · exact absurd (mem_singleton.1 h'') h0
        · exact mem_singleton.1 h'
    have hσw₀ : N.A.curve (N.A.σ w₀) = c kL := by
      have h1 : N.A.curve (N.A.σ w₀) ∈ Arrangement.Crossing.curves N.A (N.A.crossingOf y) := by
        rw [← hw₀x, ← N.A.crossingOf_σ]; exact N.A.mem_curves_crossingOf _
      rw [hx, mem_insert, mem_singleton] at h1
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd (h1.trans hw₀.symm) (N.A.isArrangement.curve_σ w₀)
    have hflip₀ : N.Inside (c kL) (N.A.cellOf (N.A.σ (N.A.σ w₀))) ↔
        ¬ N.Inside (c kL) (N.A.cellOf w₀) := by
      rw [N.A.cellOf_σ, N.inside_α _ (N.A.σ w₀), N.A.cellOf_σ, N.inside_α _ w₀]
      simp only [hσw₀, hw₀, hlne, ne_eq, not_true_eq_false, iff_false, not_false_eq_true, iff_true]
    obtain ⟨w, hw, hwx, hwin, hσσw⟩ : ∃ w, N.A.curve w = c l ∧
        N.A.crossingOf w = N.A.crossingOf y ∧ N.Inside (c kL) (N.A.cellOf w) ∧
        ¬ N.Inside (c kL) (N.A.cellOf (N.A.σ (N.A.σ w))) := by
      by_cases h : N.Inside (c kL) (N.A.cellOf w₀)
      · exact ⟨w₀, hw₀, hw₀x, h, fun h' => (hflip₀.1 h') h⟩
      · refine ⟨N.A.σ (N.A.σ w₀), by rw [N.A.curve_σσ, hw₀],
          by rw [N.A.crossingOf_σσ, hw₀x], hflip₀.2 h, ?_⟩
        rw [N.A.σ_σ_σ_σ]; exact h
    have hRx : c kR ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf w) := by
      rw [hwx, hx, mem_insert, mem_singleton, not_or]; exact ⟨Ne.symm hne, Ne.symm hlneR⟩
    have hwout : ¬ N.Inside (c kR) (N.A.cellOf w) := by
      rw [← N.crossInside_iff hRx, hwx, canon_cross hinv (i := kR) (u := kL) (v := l)
        (fun h => by have := congrArg Fin.val h; simp [kR, kL] at this; omega)
        (fun h => by have := congrArg Fin.val h; simp [kR] at this; omega)
        (fun h => by have := congrArg Fin.val h; simp [kL] at this; omega) (Or.inl hRk) hx]
      simp only [Fin.lt_def]; omega
    have hq : N.TwoQ (c kL) (c kR) True False (N.A.cellOf w) :=
      ⟨iff_true_intro hwin, iff_false_intro hwout⟩
    have hcw : Λ.Chord w :=
      ⟨hq, (N.twoQ_α_of_ne w (by rw [hw]; exact hlne) (by rw [hw]; exact hlneR)).2 hq⟩
    have hφw : N.A.cellOf (N.A.φ w) = N.A.cellOf w := N.A.cellOf_φ w
    have hφx : N.A.crossingOf (N.A.φ w) = N.A.crossingOf (N.A.α w) := by
      rw [N.A.φ_apply, N.A.crossingOf_σ]
    have hαw : N.A.curve (N.A.α w) = c l := by rw [N.A.curve_α, hw]
    have hcur' : Arrangement.Crossing.curves N.A (N.A.crossingOf (N.A.α w)) =
        {c l, N.A.curve (N.A.σ (N.A.α w))} := by rw [N.A.curves_crossingOf, hαw]
    -- the chord of `c l` from `x` ends on `c (k-1)`
    have hσαw : N.A.curve (N.A.σ (N.A.α w)) = c kR := by
      by_contra hR'
      by_cases hL' : N.A.curve (N.A.σ (N.A.α w)) = c kL
      · -- a chord from `L` to `L`: not transversal
        have hEL : Λ.EndsOn Λ.L w := ⟨0, fun i hi => by
          rw [Nat.le_zero.1 hi, pow_zero]; exact hcw, by
          rw [pow_zero]
          exact ⟨hL', by
            show N.TwoQ _ _ _ _ (N.A.cellOf (N.A.σ (N.A.α w)))
            rw [← N.A.φ_apply, hφw]; exact hq⟩⟩
        obtain ⟨m, hm1, hm2⟩ := (htr w hcw).1 hEL
        rcases m with _ | m
        · rw [pow_zero] at hm2
          have hR2 : N.A.curve (N.A.σ (N.A.α (N.A.α w))) = c kR := hm2.1
          rw [N.A.α_α] at hR2
          have : N.A.curve (N.A.σ w) ∈ Arrangement.Crossing.curves N.A (N.A.crossingOf y) := by
            rw [← hwx, ← N.A.crossingOf_σ]; exact N.A.mem_curves_crossingOf _
          rw [hx, mem_insert, mem_singleton, hR2] at this
          rcases this with h | h
          · exact hne h.symm
          · exact hlneR h.symm
        · have := hm1 1 (by omega)
          rw [pow_one, Arrangement.straight_α] at this
          exact hσσw (this.1.1.2 trivial)
      · -- otherwise the end of the segment would be a vertex of the lens
        have hL2 : c kL ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf (N.A.φ w)) := by
          rw [hφx, hcur', mem_insert, mem_singleton, not_or]
          exact ⟨Ne.symm hlne, fun h => hL' h.symm⟩
        have hR2 : c kR ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf (N.A.φ w)) := by
          rw [hφx, hcur', mem_insert, mem_singleton, not_or]
          exact ⟨Ne.symm hlneR, fun h => hR' h.symm⟩
        exact hv _ (vertex_of _ hL2 hR2 (by rw [hφw]; exact hwin) (by rw [hφw]; exact hwout))
    have hx' : Arrangement.Crossing.curves N.A (N.A.crossingOf (N.A.α w)) = {c kR, c l} := by
      rw [hcur', hσαw, Finset.pair_comm]
    have hiR : i ≠ kR := fun h => by rw [h] at hik; simp [kR] at hik; omega
    have hinot : c i ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf y) := by
      rw [hx, mem_insert, mem_singleton, not_or]
      exact ⟨fun h => hij (c.injective h), fun h => hil (c.injective h)⟩
    have hinot' : c i ∉ Arrangement.Crossing.curves N.A (N.A.crossingOf (N.A.φ w)) := by
      rw [hφx, hx', mem_insert, mem_singleton, not_or]
      exact ⟨fun h => hiR (c.injective h), fun h => hil (c.injective h)⟩
    have e := canon_cross hinv hiR hil
      (fun h => by have := congrArg Fin.val h; simp [kR] at this; omega)
      (Or.inr (Or.inl hRk)) hx'
    rw [← hφx, N.crossInside_iff hinot', hφw] at e
    rw [← hwx, N.crossInside_iff (by rwa [hwx]), e]
    simp only [Fin.lt_def]
    constructor
    · rintro (⟨-, h⟩ | ⟨h1, h2⟩)
      · exact h
      · have : i.val < k - 1 := h2; omega
    · intro h; left; exact ⟨by show k - 1 < i.val; omega, h⟩

end Pca.FlipGraph
