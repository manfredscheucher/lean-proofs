/-
Copyright (c) 2026 Manfred Scheucher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manfred Scheucher
-/
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Stage 4 shared definitions: k-holes of uniform random points

Shared definitions for the formalisation of Theorem 7 of arXiv:2111.12533 (Theorem 2.1 of the draft)
(`lim n^{-2} E[#k-holes] = C k`), see `doc/kholes/kholes.md`. This file contains only
definitions and trivial lemmas, so that the stage-4 files can be written in parallel.

The plane is `ℝ × ℝ` with `volume` (product Lebesgue measure, an additive Haar measure).
`n` points are i.i.d. uniform in `K` (`volume K = 1`), i.e. distributed by `ptLaw K n`.

* `IsHole k p T`: the points `p i`, `i ∈ T`, form a `k`-hole (convex position, no other
  point in their convex hull); `holeCount k p`; `EH K n k` (expected number of `k`-holes).
* `hullArea q`: area of the convex hull of a finite family of points; `ciSet ι`: convex
  independent families.
* `emptyProb K k N = ∫_{K^k} 1[q convex independent] (1 - area conv q)^N`: probability that
  `k` given points form a hole among `k + N` points (Step 2 of the plan).
* `sqDist c a b = (a.1-b.1)^2 + c (a.2-b.2)^2`; `IsDiamLE`, `IsDiamLT`: weak and strict
  diameter pair; `diamProb K m D N`: `emptyProb` restricted to the event `D` (Step 3).
* `cons2 p₁ p₂ r = (p₁, p₂, r 0, …)`, `baseCfg z = cons2 (0,0) (1,0) z`, `vscale s z`,
  `zip2 x Y`.
* `pairMap p₁ p₂ ε w = p₁ + w.1 (p₂-p₁) + ε w.2 (p₂-p₁)^⊥` (Step 4 change of variables),
  `pairEps p₁ p₂ n = 1 / (n |p₂-p₁|^2)`, `pairSection` (inner integral in the original
  coordinates), `scaledIntegrand` (its integrand in the scaled coordinates).
* `limSet m`, `limInt m` (the limit integral `J` of Step 4); `upperSet m`, `upperInt m`
  (labelled upper caps, Step 5).
-/

open MeasureTheory Set
open scoped ENNReal

namespace KHoles

/-! ### The probability model -/

/-- `volume` on `ℝ × ℝ` is an additive Haar measure (Mathlib has this instance only in
`Mathlib.Analysis.SpecialFunctions.PolarCoord`; repeated here to keep imports light). -/
instance isAddHaarMeasure_volume_prod : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The law of `n` i.i.d. uniform points in `K` (a probability measure when `volume K = 1`). -/
noncomputable def ptLaw (K : Set (ℝ × ℝ)) (n : ℕ) : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi fun _ => volume.restrict K

/-- `T` is a `k`-hole of the point family `p`: `T` has `k` elements, the points `p i`, `i ∈ T`,
are in convex position, and no other point of the family lies in their convex hull. -/
def IsHole {n : ℕ} (k : ℕ) (p : Fin n → ℝ × ℝ) (T : Finset (Fin n)) : Prop :=
  T.card = k ∧ ConvexIndependent ℝ (fun i : T => p i) ∧
    ∀ j, j ∉ T → p j ∉ convexHull ℝ (p '' (T : Set (Fin n)))

open Classical in
/-- The number of `k`-holes of the point family `p`. -/
noncomputable def holeCount {n : ℕ} (k : ℕ) (p : Fin n → ℝ × ℝ) : ℕ :=
  (Finset.univ.filter fun T : Finset (Fin n) => IsHole k p T).card

/-- Expected number of `k`-holes among `n` i.i.d. uniform points in `K`. -/
noncomputable def EH (K : Set (ℝ × ℝ)) (n k : ℕ) : ℝ≥0∞ :=
  ∫⁻ p, (holeCount k p : ℝ≥0∞) ∂ptLaw K n

/-! ### Convex hulls of finite families -/

/-- Area of the convex hull of the points of a family. -/
noncomputable def hullArea {ι : Type*} (q : ι → ℝ × ℝ) : ℝ≥0∞ :=
  volume (convexHull ℝ (range q))

/-- Convex independent (convex position, pairwise distinct) families indexed by `ι`. -/
def ciSet (ι : Type*) : Set (ι → ℝ × ℝ) :=
  {q | ConvexIndependent ℝ q}

/-- `∫_{K^k} 1[q convex independent] (1 - area conv q)^N dq`: the probability that `k` given
points of a sample of `k + N` uniform points form a `k`-hole (Step 2 of the plan). -/
noncomputable def emptyProb (K : Set (ℝ × ℝ)) (k N : ℕ) : ℝ≥0∞ :=
  ∫⁻ q, (ciSet (Fin k)).indicator (fun q => (1 - hullArea q) ^ N) q ∂ptLaw K k

/-! ### Diameter pairs -/

/-- Squared distance with the vertical direction weighted by `c`:
`(a.1 - b.1)^2 + c * (a.2 - b.2)^2`. `sqDist 1` is the squared Euclidean distance. -/
def sqDist (c : ℝ) (a b : ℝ × ℝ) : ℝ :=
  (a.1 - b.1) ^ 2 + c * (a.2 - b.2) ^ 2

/-- `(i, j)` is a (weak) diameter pair of `q` for `sqDist c`. -/
def IsDiamLE {k : ℕ} (c : ℝ) (q : Fin k → ℝ × ℝ) (i j : Fin k) : Prop :=
  ∀ a b, sqDist c (q a) (q b) ≤ sqDist c (q i) (q j)

/-- `(i, j)` is the strict diameter pair of `q` for `sqDist c`: every pair of distinct indices
other than `(i, j)` and `(j, i)` is strictly shorter. -/
def IsDiamLT {k : ℕ} (c : ℝ) (q : Fin k → ℝ × ℝ) (i j : Fin k) : Prop :=
  ∀ a b, a ≠ b → (a, b) ≠ (i, j) → (a, b) ≠ (j, i) → sqDist c (q a) (q b) < sqDist c (q i) (q j)

/-- `emptyProb` restricted to the event `D` (used with `D q = IsDiamLE 1 q 0 1` and
`D q = IsDiamLT 1 q 0 1`). -/
noncomputable def diamProb (K : Set (ℝ × ℝ)) (m : ℕ) (D : (Fin (m + 2) → ℝ × ℝ) → Prop)
    (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ q, {q | q ∈ ciSet (Fin (m + 2)) ∧ D q}.indicator (fun q => (1 - hullArea q) ^ N) q
    ∂ptLaw K (m + 2)

/-! ### Configurations with two fixed points -/

/-- The configuration `p₁, p₂, r 0, …, r (m-1)`. -/
def cons2 {m : ℕ} (p₁ p₂ : ℝ × ℝ) (r : Fin m → ℝ × ℝ) : Fin (m + 2) → ℝ × ℝ :=
  Fin.cons p₁ (Fin.cons p₂ r)

/-- The configuration `(0,0), (1,0), z 0, …, z (m-1)`. -/
def baseCfg {m : ℕ} (z : Fin m → ℝ × ℝ) : Fin (m + 2) → ℝ × ℝ :=
  cons2 (0, 0) (1, 0) z

/-- Vertical scaling `(x, y) ↦ (x, s y)`, pointwise (`s = -1`: reflection in the `x`-axis). -/
def vscale {m : ℕ} (s : ℝ) (z : Fin m → ℝ × ℝ) : Fin m → ℝ × ℝ :=
  fun i => ((z i).1, s * (z i).2)

/-- The family `i ↦ (x i, Y i)`. -/
def zip2 {m : ℕ} (x Y : Fin m → ℝ) : Fin m → ℝ × ℝ :=
  fun i => (x i, Y i)

/-! ### The per-pair change of variables (Steps 3 and 4) -/

/-- Rotation by `+90°`: `perp (a, b) = (-b, a)`. -/
def perp (u : ℝ × ℝ) : ℝ × ℝ :=
  (-u.2, u.1)

/-- `pairMap p₁ p₂ ε w = p₁ + w.1 • (p₂ - p₁) + (ε * w.2) • perp (p₂ - p₁)`. -/
def pairMap (p₁ p₂ : ℝ × ℝ) (ε : ℝ) (w : ℝ × ℝ) : ℝ × ℝ :=
  p₁ + w.1 • (p₂ - p₁) + (ε * w.2) • perp (p₂ - p₁)

/-- The linear part of `pairMap`: `w ↦ w.1 • (p₂ - p₁) + (ε * w.2) • perp (p₂ - p₁)`.
Its determinant is `ε * sqDist 1 p₁ p₂` (`= 1 / n` for `ε = pairEps p₁ p₂ n`). -/
noncomputable def pairLin (p₁ p₂ : ℝ × ℝ) (ε : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight (p₂ - p₁) + (ε • LinearMap.snd ℝ ℝ ℝ).smulRight (perp (p₂ - p₁))

/-- The linear map `(x, y) ↦ (x, s * y)` (determinant `s`). -/
noncomputable def vscaleLin (s : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  LinearMap.prodMap LinearMap.id (s • LinearMap.id)

/-- The vertical scale of Step 4: `1 / (n * |p₂ - p₁|^2)`. -/
noncomputable def pairEps (p₁ p₂ : ℝ × ℝ) (n : ℕ) : ℝ :=
  1 / (n * sqDist 1 p₁ p₂)

/-- Section of the integrand of `diamProb` at the first two points `p₁, p₂` (original
coordinates): `∫_{K^m} 1[cons2 p₁ p₂ r convex independent, D] (1 - area)^N dr`. -/
noncomputable def pairSection (K : Set (ℝ × ℝ)) {m : ℕ} (D : (Fin (m + 2) → ℝ × ℝ) → Prop)
    (p₁ p₂ : ℝ × ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ r, {r | cons2 p₁ p₂ r ∈ ciSet (Fin (m + 2)) ∧ D (cons2 p₁ p₂ r)}.indicator
    (fun r => (1 - hullArea (cons2 p₁ p₂ r)) ^ N) r ∂ptLaw K m

/-- The integrand of `n^m * pairSection` after the substitution `r i = pairMap p₁ p₂ ε (z i)`,
`ε = pairEps p₁ p₂ n`. `D c` is the diameter event for `sqDist c`; in the new coordinates
the event `D 1` becomes `D (ε^2)`, and the hull area becomes `hullArea (baseCfg z) / n`. -/
noncomputable def scaledIntegrand (K : Set (ℝ × ℝ)) {m : ℕ}
    (D : ℝ → (Fin (m + 2) → ℝ × ℝ) → Prop) (p₁ p₂ : ℝ × ℝ) (n N : ℕ)
    (z : Fin m → ℝ × ℝ) : ℝ≥0∞ :=
  {z : Fin m → ℝ × ℝ | (∀ i, pairMap p₁ p₂ (pairEps p₁ p₂ n) (z i) ∈ K) ∧
      baseCfg z ∈ ciSet (Fin (m + 2)) ∧ D (pairEps p₁ p₂ n ^ 2) (baseCfg z)}.indicator
    (fun z => (1 - hullArea (baseCfg z) / n) ^ N) z

/-! ### The limit integral and the cap integrals -/

/-- Event `C₁` of the plan: `(0,0), (1,0), z i` in convex position and `0 < (z i).1 < 1`. -/
def limSet (m : ℕ) : Set (Fin m → ℝ × ℝ) :=
  {z | ConvexIndependent ℝ (baseCfg z) ∧ ∀ i, 0 < (z i).1 ∧ (z i).1 < 1}

/-- The limit integral `J = ∫ 1[C₁ z] exp(-B z) dz`, `B z` = area of the convex hull. -/
noncomputable def limInt (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ z in limSet m, ENNReal.ofReal (Real.exp (-(hullArea (baseCfg z)).toReal))

/-- Labelled upper caps: `limSet` with all points strictly above the base. -/
def upperSet (m : ℕ) : Set (Fin m → ℝ × ℝ) :=
  {w | ConvexIndependent ℝ (baseCfg w) ∧ ∀ i, 0 < (w i).1 ∧ (w i).1 < 1 ∧ 0 < (w i).2}

/-- The labelled upper-cap integral (`m! a_m` by Step 5). -/
noncomputable def upperInt (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ w in upperSet m, ENNReal.ofReal (Real.exp (-(hullArea (baseCfg w)).toReal))

/-! ### Trivial lemmas -/

@[simp] lemma mem_ciSet {ι : Type*} (q : ι → ℝ × ℝ) : q ∈ ciSet ι ↔ ConvexIndependent ℝ q :=
  Iff.rfl

@[simp] lemma cons2_zero {m : ℕ} (p₁ p₂ : ℝ × ℝ) (r : Fin m → ℝ × ℝ) : cons2 p₁ p₂ r 0 = p₁ :=
  rfl

@[simp] lemma cons2_one {m : ℕ} (p₁ p₂ : ℝ × ℝ) (r : Fin m → ℝ × ℝ) : cons2 p₁ p₂ r 1 = p₂ :=
  rfl

@[simp] lemma cons2_succ_succ {m : ℕ} (p₁ p₂ : ℝ × ℝ) (r : Fin m → ℝ × ℝ) (i : Fin m) :
    cons2 p₁ p₂ r i.succ.succ = r i := rfl

lemma range_cons2 {m : ℕ} (p₁ p₂ : ℝ × ℝ) (r : Fin m → ℝ × ℝ) :
    range (cons2 p₁ p₂ r) = insert p₁ (insert p₂ (range r)) := by
  simp [cons2, Fin.range_cons]

lemma range_baseCfg {m : ℕ} (z : Fin m → ℝ × ℝ) :
    range (baseCfg z) = insert (0, 0) (insert (1, 0) (range z)) :=
  range_cons2 _ _ z

@[simp] lemma baseCfg_zero {m : ℕ} (z : Fin m → ℝ × ℝ) : baseCfg z 0 = (0, 0) := rfl

@[simp] lemma baseCfg_one {m : ℕ} (z : Fin m → ℝ × ℝ) : baseCfg z 1 = (1, 0) := rfl

@[simp] lemma baseCfg_succ_succ {m : ℕ} (z : Fin m → ℝ × ℝ) (i : Fin m) :
    baseCfg z i.succ.succ = z i := rfl

@[simp] lemma sqDist_self (c : ℝ) (a : ℝ × ℝ) : sqDist c a a = 0 := by
  simp [sqDist]

lemma sqDist_comm (c : ℝ) (a b : ℝ × ℝ) : sqDist c a b = sqDist c b a := by
  simp only [sqDist]; ring

lemma sqDist_nonneg {c : ℝ} (hc : 0 ≤ c) (a b : ℝ × ℝ) : 0 ≤ sqDist c a b := by
  unfold sqDist; positivity

@[simp] lemma pairMap_zero (p₁ p₂ : ℝ × ℝ) (ε : ℝ) : pairMap p₁ p₂ ε (0, 0) = p₁ := by
  simp [pairMap]

@[simp] lemma pairMap_one (p₁ p₂ : ℝ × ℝ) (ε : ℝ) : pairMap p₁ p₂ ε (1, 0) = p₂ := by
  simp [pairMap]

lemma pairLin_apply (p₁ p₂ : ℝ × ℝ) (ε : ℝ) (w : ℝ × ℝ) :
    pairLin p₁ p₂ ε w = w.1 • (p₂ - p₁) + (ε * w.2) • perp (p₂ - p₁) := by
  simp [pairLin, mul_smul]

lemma pairMap_eq_add_pairLin (p₁ p₂ : ℝ × ℝ) (ε : ℝ) (w : ℝ × ℝ) :
    pairMap p₁ p₂ ε w = p₁ + pairLin p₁ p₂ ε w := by
  rw [pairLin_apply, pairMap, add_assoc]

lemma vscaleLin_apply (s : ℝ) (w : ℝ × ℝ) : vscaleLin s w = (w.1, s * w.2) := by
  simp [vscaleLin]

lemma vscale_eq (s : ℝ) {m : ℕ} (z : Fin m → ℝ × ℝ) : vscale s z = fun i => vscaleLin s (z i) := by
  funext i
  rw [vscaleLin_apply]
  rfl

@[simp] lemma zip2_apply {m : ℕ} (x Y : Fin m → ℝ) (i : Fin m) : zip2 x Y i = (x i, Y i) := rfl

@[simp] lemma vscale_apply {m : ℕ} (s : ℝ) (z : Fin m → ℝ × ℝ) (i : Fin m) :
    vscale s z i = ((z i).1, s * (z i).2) := rfl

example (ι : Type*) [Fintype ι] : Measure.IsAddHaarMeasure (volume : Measure (ι → ℝ × ℝ)) :=
  inferInstance

lemma ptLaw_def (K : Set (ℝ × ℝ)) (n : ℕ) :
    ptLaw K n = Measure.pi fun _ => volume.restrict K := rfl

end KHoles
