/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher

# Flip graphs (Track F): uniqueness of the canonical arrangement `𝒜_n^-`

`canon_iso`: two canonical arrangements are isomorphic. By `walk_canon` the crossing sequence along
every curve is fixed (`labF`, `flagF`); at a crossing the dart `σ w` of a walk dart `w` is the dart
of the other curve pointing into the interior of `curve w`, i.e. the forward dart of the other curve
iff the walk is outside the other curve afterwards, and its position on the other curve is the
unique one with label `curve w` and the opposite flag (`sPos`). So both arrangements have the same
rotation table in the coordinates of `Pca/Great/Coord.lean` (base darts from `walk_canon`); the
isomorphism of `Great.iso_of_table` (re-proved here as `iso_of_table_code`, which also states that
coordinates are kept) maps the marked cell to the marked cell: it is the cell right of the dart of
`c 0` at position `2 n - 3` (height `0`, inside no curve).
-/
import Pca.FlipGraph.CanonWalk
import Pca.FlipGraph.IsoMap
import Pca.Great.Coord

open Equiv Finset

namespace Pca.FlipGraph

universe u v

variable {n : ℕ} {D : Type u} [Fintype D] [DecidableEq D]

/-- The position of the crossing with the curve of index `i` along the curve of index `j` with the
flag `f`. -/
def sPos (n j i : ℕ) (f : Bool) : ℕ :=
  if j < i then (if f then i - 1 else 2 * n - 2 - i) else (if f then 2 * n - 3 - i else i)

theorem sPos_unique {i j s : ℕ} {f : Bool} (hi : i < n) (hj : j < n) (hij : i ≠ j)
    (hs : s < 2 * (n - 1)) (h1 : labF n j s = i) (h2 : flagF n j s = f) : s = sPos n j i f := by
  subst h2
  unfold flagF at *
  unfold sPos
  unfold labF at *
  split_ifs at * <;> simp_all <;> omega

/-- The cell to the left of a forward dart is inside its curve. -/
theorem Marked.inside_σσ (M : Marked n D) {u : D} (hu : ¬ M.Inside (M.A.curve u) (M.A.cellOf u)) :
    M.Inside (M.A.curve u) (M.A.cellOf (M.A.σ (M.A.σ u))) := by
  rw [M.A.cellOf_σ, M.inside_α, M.A.cellOf_σ, M.inside_α]
  have := M.A.isArrangement.curve_σ u
  simp only [ne_eq, this, not_false_eq_true, iff_true, not_true_eq_false, iff_false]
  exact hu

/-- **The rotation table of `𝒜_n^-`**. -/
theorem table (M : Marked n D) (c : Fin n ≃ Fin n) (hC : M.CanonUpTo c n) :
    ∃ yb : Fin n → D, (∀ i, M.A.curve (yb i) = c i) ∧
      (∀ i k, ¬ M.Inside (c i) (M.A.cellOf ((M.A.straight ^ k) (yb i)))) ∧
      (∀ (i : Fin n) s, s < 2 * (n - 1) →
        M.hgt c i (M.A.cellOf ((M.A.straight ^ s) (yb i))) = hgtF n i (s + 1)) ∧
      ∀ (i : Fin n) s, s < 2 * (n - 1) → ∃ h : labF n i s < n,
        M.A.σ ((M.A.straight ^ s) (yb i)) = Great.code M.A (fun a => yb (c.symm a))
          (c ⟨labF n i s, h⟩) (sPos n (labF n i s) i (!flagF n i s)) (flagF n i s) := by
  choose yb hyb hout hw using walk_canon M c hC
  refine ⟨yb, hyb, hout, fun i s hs => (hw i s hs).2.2, fun i s hs => ?_⟩
  have hβ : ∀ a, M.A.curve (yb (c.symm a)) = a := fun a => by
    rw [hyb, Equiv.apply_symm_apply]
  set w := (M.A.straight ^ s) (yb i) with hwdef
  have hwc : M.A.curve w = c i := by rw [hwdef, Walk.curve_pow, hyb]
  obtain ⟨hlab, hflag, -⟩ := hw i s hs
  rw [← hwdef] at hlab hflag
  obtain ⟨a, s'', b, hs'', hv⟩ := Great.exists_code M.A _ hβ (M.A.σ w)
  have ha : a = M.A.curve (M.A.σ w) := by
    rw [← hv, Great.curve_code, hβ]
  set j := c.symm a with hj
  have hcj : c j = a := by rw [hj, Equiv.apply_symm_apply]
  have hjv : (j : ℕ) = labF n i s := by rw [hj, ha]; exact hlab
  have hlt : labF n i s < n := hjv ▸ j.isLt
  refine ⟨hlt, ?_⟩
  have hjeq : (⟨labF n i s, hlt⟩ : Fin n) = j := Fin.ext hjv.symm
  rw [hjeq, hcj]
  have hai : a ≠ c i := by
    rw [ha, ← hwc]; exact M.A.isArrangement.curve_σ w
  set u := (M.A.straight ^ s'') (yb j) with hudef
  have hcode : ∀ b', Great.code M.A (fun a => yb (c.symm a)) a s'' b' =
      if b' then M.A.σ (M.A.σ u) else u := fun b' => by
    cases b' <;> simp [Great.code, hudef, hj]
  rw [hcode] at hv
  have huc : M.A.curve u = a := by rw [hudef, Walk.curve_pow, hyb, hcj]
  have hout_u : ¬ M.Inside a (M.A.cellOf u) := by rw [← hcj]; exact hout j s''
  obtain ⟨hlab', hflag', -⟩ := hw j s'' hs''
  rw [← hudef] at hlab' hflag'
  have hin_w : ¬ M.Inside (c i) (M.A.cellOf w) := hout i s
  have hb : b = flagF n i s := by
    cases b
    · simp only [Bool.false_eq_true, if_false] at hv
      have : ¬ M.Inside (M.A.curve (M.A.σ w)) (M.A.cellOf w) := by
        rw [← ha]
        have e := M.inside_α a w
        rw [← M.A.cellOf_σ, ← hv, hwc] at e
        have hne : c i ≠ a := Ne.symm hai
        tauto
      cases h : flagF n i s
      · rfl
      · exact absurd (hflag.2 h) this
    · simp only [if_true] at hv
      have : M.Inside (M.A.curve (M.A.σ w)) (M.A.cellOf w) := by
        rw [← ha]
        have e1 := M.inside_σσ (u := u) (by rw [huc]; exact hout_u)
        rw [hv, huc, M.A.cellOf_σ, M.inside_α, hwc] at e1
        have hne : c i ≠ a := Ne.symm hai
        tauto
      exact (hflag.1 this).symm
  subst hb
  have hσu : M.A.curve (M.A.σ u) = c i ∧ (M.Inside (c i) (M.A.cellOf u) ↔ flagF n i s = false) := by
    cases hf : flagF n i s
    · rw [hf] at hv
      simp only [Bool.false_eq_true, if_false] at hv
      rw [hv]
      refine ⟨by rw [M.A.isArrangement.curve_σσ, hwc], ?_⟩
      simp only [iff_true]
      rw [M.A.cellOf_σ, M.inside_α, hwc]
      simp only [ne_eq, not_true_eq_false, iff_false]
      exact hin_w
    · rw [hf] at hv
      simp only [if_true] at hv
      have hwu : w = M.A.σ u := (M.A.σ.injective hv).symm
      refine ⟨by rw [← hwu, hwc], ?_⟩
      simp only [Bool.true_eq_false, iff_false]
      have e1 := M.inside_σσ (u := w) (by rw [hwc]; exact hin_w)
      have hu3 : u = M.A.σ (M.A.σ (M.A.σ w)) := by rw [hwu, M.A.σ_σ_σ_σ]
      rw [hu3, M.A.cellOf_σ, M.inside_α, M.A.isArrangement.curve_σσ, hwc]
      rw [hwc] at e1
      simp only [ne_eq, not_true_eq_false, iff_false, not_not]
      exact e1
  obtain ⟨h1, h2⟩ := hσu
  rw [h1, Equiv.symm_apply_apply] at hlab'
  rw [h1] at hflag'
  have hs' : s'' = sPos n j i (!flagF n i s) := by
    rw [hjv] at hlab' ⊢
    refine sPos_unique i.isLt hlt (fun h => ?_) hs'' hlab'.symm ?_
    · exact absurd (Fin.ext (hjv.trans h.symm)) (fun h' => hai (by rw [← hcj, h']))
    · rw [← hjv]
      have := hflag'.symm.trans h2
      revert this
      cases flagF n j s'' <;> cases flagF n i s <;> decide
  rw [← hjv, ← hs', hcode]
  exact hv.symm

/-! ## The isomorphism criterion, keeping coordinates

`Great.iso_of_table` (`Pca/Great/Coord.lean`, Track P) with the same proof, also stating that the
isomorphism keeps coordinates (needed for the marked cell). -/

section Table

open Great

theorem iso_of_table_code {D : Type*} [Fintype D] [DecidableEq D] {D' : Type*} [Fintype D']
    [DecidableEq D'] (A : Arrangement n D)
    (B : Arrangement n D') (π : Perm (Fin n)) (βA : Fin n → D) (βB : Fin n → D')
    (hβA : ∀ c, A.curve (βA c) = c) (hβB : ∀ c, B.curve (βB c) = π c)
    (T : Fin n → ℕ → Fin n × ℕ × Bool)
    (hA : ∀ c k, k < 2 * (n - 1) →
      A.σ (code A βA c k false) = code A βA (T c k).1 (T c k).2.1 (T c k).2.2)
    (hB : ∀ c k, k < 2 * (n - 1) →
      B.σ (code B βB c k false) = code B βB (T c k).1 (T c k).2.1 (T c k).2.2) :
    ∃ I : Great.Iso A B, ∀ c k b, I.toEquiv (code A βA c k b) = code B βB c k b := by
  classical
  have hn := A.two_le_n
  -- the base darts of `B` indexed by the curves of `B`
  set βB' : Fin n → D' := fun c => βB (π.symm c) with hβB'def
  have hβB' : ∀ c, B.curve (βB' c) = c := fun c => by
    simp only [hβB'def, hβB, Equiv.apply_symm_apply]
  have hcodeB : ∀ c k b, code B βB c k b = code B βB' (π c) k b := fun c k b => by
    simp [code, hβB'def]
  choose cA kA bA hkA hA' using exists_code A βA hβA
  have exB : ∀ d', ∃ c k b, k < 2 * (n - 1) ∧ code B βB c k b = d' := by
    intro d'
    obtain ⟨c, k, b, hk, h⟩ := exists_code B βB' hβB' d'
    exact ⟨π.symm c, k, b, hk, by rw [hcodeB, Equiv.apply_symm_apply]; exact h⟩
  choose cB kB bB hkB hB' using exB
  have injB : ∀ {c c' k k' b b'}, k < 2 * (n - 1) → k' < 2 * (n - 1) →
      code B βB c k b = code B βB c' k' b' → c = c' ∧ k = k' ∧ b = b' := by
    intro c c' k k' b b' hk hk' h
    rw [hcodeB, hcodeB] at h
    obtain ⟨h1, h2, h3⟩ := code_inj B βB' hβB' hk hk' h
    exact ⟨π.injective h1, h2, h3⟩
  let F : D → D' := fun d => code B βB (cA d) (kA d) (bA d)
  let G : D' → D := fun d' => code A βA (cB d') (kB d') (bB d')
  -- `F` on all coordinates
  have hF : ∀ c k b, F (code A βA c k b) = code B βB c k b := by
    intro c k b
    have h1 := (hA' (code A βA c k b)).trans (code_mod A βA c k b).symm
    obtain ⟨h1c, h2, h3⟩ := code_inj A βA hβA (hkA _) (Nat.mod_lt _ (by omega)) h1
    show code B βB (cA _) (kA _) (bA _) = _
    rw [h1c, h2, h3, code_mod]
  have hG : ∀ c k b, G (code B βB c k b) = code A βA c k b := by
    intro c k b
    have h1 := (hB' (code B βB c k b)).trans (code_mod B βB c k b).symm
    obtain ⟨h1c, h2, h3⟩ := injB (hkB _) (Nat.mod_lt _ (by omega)) h1
    show code A βA (cB _) (kB _) (bB _) = _
    rw [h1c, h2, h3, code_mod]
  have hGF : ∀ d, G (F d) = d := fun d => by
    show G (code B βB _ _ _) = d
    rw [hG]; exact hA' d
  have hFG : ∀ d', F (G d') = d' := fun d' => by
    show F (code A βA _ _ _) = d'
    rw [hF]; exact hB' d'
  -- `σ` and `α` in coordinates
  have hσ : ∀ c k b, F (A.σ (code A βA c k b)) = B.σ (code B βB c k b) := by
    intro c k b
    rw [← code_mod A βA c k b, ← code_mod B βB c k b]
    have hk := Nat.mod_lt k (show 0 < 2 * (n - 1) by omega)
    cases b
    · rw [hA c _ hk, hF, hB c _ hk]
    · have e1 : code A βA c (k % (2 * (n - 1))) true =
          A.σ (A.σ (code A βA c (k % (2 * (n - 1))) false)) := by rw [code_σσ]; rfl
      have e2 : code B βB c (k % (2 * (n - 1))) true =
          B.σ (B.σ (code B βB c (k % (2 * (n - 1))) false)) := by rw [code_σσ]; rfl
      rw [e1, e2]
      change F (A.σ (A.σ (A.σ (code A βA c _ false)))) = B.σ (B.σ (B.σ (code B βB c _ false)))
      rw [hA c _ hk, hB c _ hk, code_σσ, code_σσ, hF]
  have hα : ∀ c k b, F (A.α (code A βA c k b)) = B.α (code B βB c k b) := by
    intro c k b
    cases b
    · rw [α_code_false, α_code_false, hF]
    · rcases k with _ | k
      · rw [← code_add_period A βA c 0 true, ← code_add_period B βB c 0 true, zero_add]
        obtain ⟨m, hm⟩ : ∃ m, 2 * (n - 1) = m + 1 := ⟨2 * (n - 1) - 1, by omega⟩
        rw [hm, α_code_true, α_code_true, hF]
      · rw [α_code_true, α_code_true, hF]
  refine ⟨Great.Iso.mk ⟨F, G, hGF, hFG⟩ π ?_ ?_ ?_, hF⟩
  · intro d
    change F (A.σ d) = B.σ (F d)
    conv_lhs => rw [← hA' d]
    rw [hσ]
  · intro d
    change F (A.α d) = B.α (F d)
    conv_lhs => rw [← hA' d]
    rw [hα]
  · intro d
    change B.curve (code B βB _ _ _) = π (A.curve d)
    rw [curve_code, hβB]
    conv_rhs => rw [← hA' d]
    rw [curve_code, hβA]

end Table

/-- The marked cell of `𝒜_n^-` is to the right of the dart of `c 0` at position `2 n - 3`. -/
theorem canon_z (M : Marked n D) (c : Fin n ≃ Fin n) (hC : M.Canon c) (yb : Fin n → D)
    (hyb : ∀ i, M.A.curve (yb i) = c i)
    (hout : ∀ i k, ¬ M.Inside (c i) (M.A.cellOf ((M.A.straight ^ k) (yb i))))
    (hg : ∀ (i : Fin n) s, s < 2 * (n - 1) →
      M.hgt c i (M.A.cellOf ((M.A.straight ^ s) (yb i))) = hgtF n i (s + 1))
    (h0 : 0 < n) :
    M.A.cellOf ((M.A.straight ^ (2 * n - 3)) (yb ⟨0, h0⟩)) = M.z := by
  classical
  have hn := M.A.two_le_n
  obtain ⟨y, hyz, hy0⟩ := hC.2
  have hβ : ∀ a, M.A.curve (yb (c.symm a)) = a := fun a => by
    rw [hyb, Equiv.apply_symm_apply]
  obtain ⟨a, s, b, hs, hv⟩ := Great.exists_code M.A _ hβ y
  have ha : a = c ⟨0, h0⟩ := by
    have : M.A.curve y = a := by rw [← hv, Great.curve_code, hβ]
    rw [← this, ← Equiv.apply_symm_apply c (M.A.curve y)]
    exact congrArg c (Fin.ext hy0)
  subst ha
  have hcode : ∀ b', Great.code M.A (fun a => yb (c.symm a)) (c ⟨0, h0⟩) s b' =
      if b' then M.A.σ (M.A.σ ((M.A.straight ^ s) (yb ⟨0, h0⟩)))
      else (M.A.straight ^ s) (yb ⟨0, h0⟩) := fun b' => by
    cases b' <;> simp [Great.code]
  rw [hcode] at hv
  cases b
  · simp only [Bool.false_eq_true, if_false] at hv
    have hz : M.hgt c ⟨0, h0⟩ M.z = 0 := by
      unfold Marked.hgt
      rw [show univ.filter (fun l : Fin n => (⟨0, h0⟩ : Fin n) < l ∧ M.Inside (c l) M.z) = ∅ by
          ext l; simp [M.not_inside_z],
        show univ.filter (fun l : Fin n => l < (⟨0, h0⟩ : Fin n) ∧ M.Inside (c l) M.z) = ∅ by
          ext l; simp [M.not_inside_z]]
      simp
    have e := hg ⟨0, h0⟩ s hs
    rw [hv, hyz, hz] at e
    unfold hgtF at e
    have hs3 : s = 2 * n - 3 := by split_ifs at e <;> push_cast at e <;> omega
    rw [← hs3, ← hyz, ← hv]
  · simp only [if_true] at hv
    exfalso
    have e := M.inside_σσ (u := (M.A.straight ^ s) (yb ⟨0, h0⟩))
      (by rw [Walk.curve_pow, hyb]; exact hout _ s)
    rw [hv, hyz] at e
    exact M.not_inside_z _ e

/-- **Uniqueness of `𝒜_n^-`**: two canonical arrangements are isomorphic. -/
theorem canon_iso {D' : Type v} [Fintype D'] [DecidableEq D'] {M : Marked n D}
    {M' : Marked n D'} {c c' : Fin n ≃ Fin n} (h : M.Canon c) (h' : M'.Canon c') :
    IsIso M M' := by
  have hn := M.A.two_le_n
  obtain ⟨yA, hyA, outA, hgA, tA⟩ := table M c h.1
  obtain ⟨yB, hyB, outB, hgB, tB⟩ := table M' c' h'.1
  set βA : Fin n → D := fun a => yA (c.symm a) with hβAdef
  set βB : Fin n → D' := fun a => yB (c.symm a) with hβBdef
  have hβA : ∀ a, M.A.curve (βA a) = a := fun a => by
    simp only [hβAdef, hyA, Equiv.apply_symm_apply]
  have hβB : ∀ a, M'.A.curve (βB a) = (c.symm.trans c') a := fun a => by
    simp only [hβBdef, hyB, Equiv.trans_apply]
  let T : Fin n → ℕ → Fin n × ℕ × Bool := fun a k =>
    if hl : labF n (c.symm a) k < n then
      (c ⟨labF n (c.symm a) k, hl⟩, sPos n (labF n (c.symm a) k) (c.symm a)
        (!flagF n (c.symm a) k), flagF n (c.symm a) k)
    else (a, 0, false)
  have hA : ∀ a k, k < 2 * (n - 1) →
      M.A.σ (Great.code M.A βA a k false) =
        Great.code M.A βA (T a k).1 (T a k).2.1 (T a k).2.2 := by
    intro a k hk
    obtain ⟨hl, e⟩ := tA (c.symm a) k hk
    simp only [T, dif_pos hl]
    simpa [Great.code, hβAdef] using e
  have hB : ∀ a k, k < 2 * (n - 1) →
      M'.A.σ (Great.code M'.A βB a k false) =
        Great.code M'.A βB (T a k).1 (T a k).2.1 (T a k).2.2 := by
    intro a k hk
    obtain ⟨hl, e⟩ := tB (c.symm a) k hk
    simp only [T, dif_pos hl]
    simpa [Great.code, hβBdef] using e
  obtain ⟨I, hI⟩ := iso_of_table_code M.A M'.A (c.symm.trans c') βA βB hβA hβB T hA hB
  refine ⟨⟨I.toEquiv, I.curveEquiv, I.map_σ, I.map_α, I.map_curve, fun d hd => ?_⟩⟩
  have h0 : 0 < n := by omega
  have zA := canon_z M c h yA hyA outA hgA h0
  have zB := canon_z M' c' h' yB hyB outB hgB h0
  have eA : (M.A.straight ^ (2 * n - 3)) (yA ⟨0, h0⟩) =
      Great.code M.A βA (c ⟨0, h0⟩) (2 * n - 3) false := by simp [Great.code, hβAdef]
  have eB : (M'.A.straight ^ (2 * n - 3)) (yB ⟨0, h0⟩) =
      Great.code M'.A βB (c ⟨0, h0⟩) (2 * n - 3) false := by simp [Great.code, hβBdef]
  rw [eA] at zA
  rw [eB, ← hI] at zB
  rw [← zB]
  exact (map_cellOf_eq_iff I.toEquiv I.map_σ I.map_α).2 (hd.trans zA.symm)

end Pca.FlipGraph
