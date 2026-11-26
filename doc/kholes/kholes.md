# KHoles: k-holes in random point sets

Library `KHoles`, files `StochasticGeometry/KHoles/`. Not yet rebuilt in this repository
(`lake build KHoles`).

## What is proved

Let `K ⊆ ℝ²` be convex with area 1, and let `n` points be chosen independently and uniformly in
`K`. A `k`-hole is a set of `k` of the points in convex position whose convex hull contains no
other point. `EH K n k` is the expected number of `k`-holes.

* `KHoles.tendsto_EH_div_sq` (`Theorem7.lean`): for `k ≥ 3`, `EH K n k / n² → C k`. No
  boundedness, closedness or measurability of `K` is assumed.
* The constants in closed form (`Constants.lean`):
  * `a m = 2^m/(m+1) · ∑_{j ≤ m/2} (−1)^j π^{2j}/(2j)! · C(2m−2j, m)` (cap numbers),
  * `C k = 2^{k−2}/k · ∑_{1 ≤ j ≤ k/2} (−1)^{j+1} (2π)^{2j−2}/(2j−1)! · C(2k−2j−1, k−1)`,
  * `C k = ½ ∑_m a_m a_{k−2−m}` for all `k` (`Cconv_eq_C_all`, `Convolution.lean`), with the
    generating function of `a` (`genfun_a`) and explicit values `C 3, …, C 10`.
* The steps in between:
  * `EH_eq_choose_mul` (`Exchange.lean`): `EH = C(n,k) · P(the other n − k points miss the hull)`,
  * `DiamSqueeze.lean`, `PairLimit.lean`: squeeze by the pair of points at maximal distance, and
    the scaled limit `limInt m`,
  * `limInt_eq` (`LimitIntegral.lean`): `limInt m = m! · 2 · C(m+2)`, by splitting into upper and
    lower caps,
  * `capInt_toReal` (`CapClosedForm.lean`): the cap integral over the simplex is `a m / 2^m`.

## Axioms

None beyond `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.

## Source

Theorem 7 of M. Balko, M. Scheucher, P. Valtr, https://arxiv.org/abs/2111.12533. The closed
form of `C k` is new (M. Scheucher), not yet published.

## Deviations from the paper

The limit is proved with one dominated convergence per pair of points and the single bound
`e^{−B/2}`, which is integrable because of the closed form, instead of the paper's estimates over
pairs.

## Proof of the closed form

The closed form of the cap numbers uses a telescoping series and Euler's sine product
(`EulerTelescope.lean`), so no hypergeometric functions or Gauss summation are needed (Mathlib has
neither). Coefficients of powers of the Catalan series are computed by a recursion
(`CatalanPower.lean`), and the convolution identity uses `2 sin²(πα) + cos(2πα) = 1`
(`Convolution.lean`).
