# BrightnessLogisticRawLowerBound: an all-stepsize first-fit lower bound for constant-step logistic GD

The [theorem](../../LongTails/Theorems/BrightnessLogisticRawLowerBound.lean) shows the following for every valid dataset with rows `(R dᵢ, zᵢ)` in the [setup](../../LongTails/Setups/BrightnessLogisticRaw.lean). Full-batch logistic GD with any constant step `η > 0`, started at `(t/R, w)` and stopped at the first fit, has no iterate with all signed scores positive within the budget below. The setup's `family` forces this algorithm exactly. There is no separate `Algorithms/` module, and the iterates are defined in [the dynamics proof](../../LongTails/Proofs/BrightnessLogisticRawDynamics.lean).

**Bound.** Each oracle call returns the full-batch gradient and a fit flag. GD fails to fit within

  `K = Ω( (R² m δ / H²) · min{1, s / ((1 + |t|D + H‖w‖) log R)} )` calls.

The parameters are:
- `R`: brightness contrast.
- `m, D`: lower and upper bounds on the nonzero `|dᵢ|`.
- `H`: a bound on `‖zᵢ‖`.
- `s`: the initial deficit of a zero-brightness convex combination of two opposite-brightness rows.
- `δ`: the distance from `b = mean dᵢ σ(−scoreᵢ(w₀))` to the lattice `LZ`.

Validity requires:
- `log R ≥ 1`;
- `16D(1 + mδ/(8H²)) ≤ δR²`;
- both signed brightness masses are integer multiples of `L`.

**Nonempty example (checked by hand).** Take `n = 2`, `d₁ = 1`, `d₂ = −1`, `z₁ = z₂ = 1`, `w = −1`, `t = 1/2` and `L = 1/2`. Then `b ≈ −0.0976`, so `δ ≈ 0.0976`, `s = 1`, and the data is separable by `(0, 1)`. The normalized margin is `γ = 1/√(R²+1)`, so `K ≍ 1/(γ² log(1/γ))`. In this example the deficit forces `w₀ ≠ 0`; in general, the theorem never covers zero initialization.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Crawshaw–Liu, [arXiv 2602.12471](https://arxiv.org/abs/2602.12471) (v1 Feb 2026, COLT 2026), Lemma 3.11 / Thm 3.10 (prior; applies only to large steps) | Steps to separate: `Ω(n/γ)` for `η ≥ max{n, 32γ⁻² log(3/γ)}`. Steps to the stable phase: `Ω(n/γ + 1/γ²)`. Both with `w₀ = 0` and `‖xᵢ‖ ≤ 1` → `Ω(1/(γ² log(1/γ)))` steps to separate, for every `η > 0`, at fixed `n` | For first fit at fixed `n`: `1/γ → 1/(γ² log(1/γ))` (normalized example above). The new bound also covers the stepsizes `η < η₁`, where they prove nothing | Stepsize range `η ≥ Ω̃(n + γ⁻²)` → all `η > 0`. The instance classes are incomparable | None (same first-fit criterion) | Needs a nonzero adversarial initialization with deficit `s`, plus lattice/clearance conditions. Loses `log R`. Has no `n/γ` term |
| Zhang–Wu–Lin–Bartlett, [arXiv 2504.04105](https://arxiv.org/abs/2504.04105) (v2 Apr 2025), Thm 3.2 (prior) | Steps to find a separator: `Ω(min{log n, 1/γ²})` for every batch first-order method, in dimension `d ≈ 1/(5γ²)` → `Ω(1/(γ² log(1/γ)))` for constant-step GD only, in fixed dimension | For GD when `log n ≪ 1/γ²`, e.g. `n = 2`: `O(1) → R²/log R` | Dimension `≈ 1/γ²` → any `d`; worst case → every valid dataset | None | Much narrower algorithm class. Their adaptive GD (Thm 2.1) reaches loss below `log 2/n` within `O(1/γ²)` steps (normalized), i.e. order `R²` here. So this result does not separate GD from other methods |
| Tyurin, [AAAI 2025 / arXiv 2412.08424](https://arxiv.org/abs/2412.08424), Thm 5.1 (prior; covers only the `η → ∞` batch-perceptron limit) | `Ω(n)` iterations, `w₀ = 0` → `Ω(R²/log R)` for finite `η` | Larger at fixed `n` | Perceptron limit → finite-step GD | None | Same as above |
| GD upper bound with step `1/L`, `L ≤ (R²D² + H²)/4` (standard smooth-convex bound, applied as in the companion note; not formalized) | Upper bound `O(n(R²D² + H²)(|t|/R + ‖w‖ + γ_z⁻¹ log n)²)` versus lower bound `Ω(R²/log R)`. Here `γ_z` is the spatial margin of the `zᵢ` | Lower bound: the step-`1/L` rate is optimal among constant steps up to `log R` in `R`. Gaps in `n`, `γ_z` and `δ` remain | — | — | The two bounds are matched only in their dependence on `R` |

**Standard-reduction check.** The theorem does not follow from combining known results:
- The small-step case is an elementary one-line bound: the deficit falls by at most `ηH²` per call.
- The large-step case compares soft-sigmoid GD with a hard-sign (perceptron-like) orbit that stays on a shifted lattice. It sums the exponentially small soft–hard errors.
- Balancing the two cases gives the `log R`. That regime boundary, at a normalized step of about `log(1/γ)`, is far below Crawshaw–Liu's `η₁ ≈ γ⁻²`. The lattice-clearance device is the new mechanism.
- Proof ancestry: Novikoff/perceptron-type oscillation arguments and Tyurin's reduction of large-step GD to the perceptron.

**Search coverage (2026-11-28).** Searched arXiv/HTML versions of the large-step logistic GD literature, including Wen–Wen–Teng 2610.01459 (as `η → ∞`), Gong–Li 2610.06675 (no lower bounds) and Musat–Boumal 2610.26748 (large-`η` counterexample only). None proves a first-fit lower bound that holds for all stepsizes on a fixed dataset.
- Some theorem statements were read from HTML renderings, partly through summaries.
- I did not read Tyurin 2512.11587 (cited in the note) or Wu et al. (COLT 2024) directly.
- The companion note omits the Crawshaw–Liu and Zhang et al. lower bounds. Its `O(R²)` upper bound is informal. The result entered the repository in commit `09e4fb3d` (2026-11-28), after all the cited works.

**Conclusion**

**This is a new GD-specific lower bound that holds for every stepsize at once, but it shows no gap between GD and better methods.** The closest prior work is Crawshaw–Liu (COLT 2026). Its separation lower bound holds only for steps `η ≳ γ⁻²` and is linear in `1/γ`. The selected theorem covers every `η > 0` on the same fixed dataset:

| | Steps to first fit (`n` fixed, normalized margin `γ`) |
|---|---|
| Crawshaw–Liu, `η ≥ η₁` only | `Ω(n/γ)` |
| This result, all `η > 0` | `Ω(1/(γ² log(1/γ)))` |
| Known upper bounds (step `1/L`; Zhang et al.'s adaptive GD) | order `1/γ²` (order `R²` here) |

So no constant step can make raw GD fit much faster than order `R²`. That bound is already reached by standard methods, so the result improves no problem-class guarantee. It also requires conditions that look engineered: a nonzero initialization with a negative balanced deficit (`w₀ = 0` is excluded), lattice commensurability, and a clearance `δ` that enters linearly. The note itself measures `δ ≈ 10⁻⁸` on CIFAR. A `log R` gap remains.

The comparison establishes a stronger stepsize range and a stronger fixed-`n` exponent than the checked lower bounds. My search found no prior all-stepsize result, but that does not prove priority. What can be claimed is a correct-looking, all-stepsize, fixed-dataset `Ω(R²/log R)` first-fit lower bound for constant-step logistic GD. Its main value is as one half of the repository's raw-versus-learned-filter separation.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
