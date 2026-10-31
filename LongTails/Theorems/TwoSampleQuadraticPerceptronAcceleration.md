# Deterministic implicit acceleration of the two-sample quadratic perceptron

Lean theorem: [`TwoSampleQuadraticPerceptronAcceleration.lean`](TwoSampleQuadraticPerceptronAcceleration.lean)
(`OracleTemplate.TwoSampleQuadraticPerceptron.result`).
Setup: [`../Setups/TwoSampleQuadraticPerceptron.lean`](../Setups/TwoSampleQuadraticPerceptron.lean).
Algorithm: [`../Algorithms/TwoSampleQuadraticPerceptron.lean`](../Algorithms/TwoSampleQuadraticPerceptron.lean).
Proof modules: `LongTails/Proofs/QuadraticPerceptron{Cone,Phases,Potential,Stopping,Budget}.lean`
(the abstract switched system) and
`LongTails/Proofs/TwoSampleQuadraticPerceptron{Embedding,Bridge,Moves,Spectrum,Execution}.lean`
(the reduction of both network models to that system).

## Background: Theorem 5.1 of Tyurin

A. Tyurin, *Gradient Descent as a Perceptron Algorithm: Understanding Dynamics and Implicit
Acceleration*, [arXiv:2512.11587](https://arxiv.org/abs/2512.11587) (v2, May 2026; ICML 2026)
studies logistic-loss gradient descent (GD) on reparameterized linear models
`m(b; θ) = ½ θᵀ A(b) θ`.

- **Large-norm limit.** In the large-norm limit, normalized GD becomes the *quadratic
  perceptron algorithm* (QPA): `θ ← θ + γ Σ_{i : θᵀA_iθ ≤ 0} A_i θ` (Thm 2.1, batch version).
- **Dataset (5).** It uses the two-point dataset (5): `b₁ = 1_d` with label +1 and
  `b₂ = 1_d + µ e₁` with label −1. On this dataset, the batch perceptron on the linear model
  needs `Ω(d/µ)` steps for every initialization `z₀ ∈ B(0, ϕε)`, including `z₀ = 0`
  (Thm 5.2).
- **Theorem 5.1.** Theorem 5.1 analyses the *non-batch* two-sample QPA on the convolutional
  model `m(b; c, v) = ⟨c₁ b + c₂ Pb, v⟩` (kernel size 2, `P` the cyclic shift):
  - the rule is: update with `A₁` if sample 1 is misclassified, otherwise with `A₂` if sample 2
    is misclassified, otherwise stop;
  - fresh Gaussian noise `ξ_t ~ N(0, σ²I)` is added at every step, with a tiny `σ` that depends
    on `T` and `⟨θ₀, v_{µ,+}⟩`;
  - the step size is `γ = 1/(4√d)` and `µ ≤ 1/10`;
  - with probability `≥ 1 − ρ`, a separator is found within
    `T = ⌈A log(√d A/µ)·√d/µ⌉` steps, where `A = 2²⁷ log(·) log(·)`.

  This is the paper's *implicit acceleration*: `Õ(√d/µ)` versus `Ω(d/µ)`.
- **Proof and open directions.** The proof (App. C, ≈30 pages) conditions on a high-probability
  noise event. The noise is used only to keep the trajectory away from bad subspaces where the
  noiseless dynamics stall. The paper lists directions it leaves open (end of Sec. 5.1,
  Sec. 6 and Sec. 8):
  - larger convolution kernels `k`;
  - more general two-layer models, and multi-layer models;
  - nonlinear activations;
  - the small-norm regime of GD;
  - a simpler proof.

## Setup (`LongTails/Setups/TwoSampleQuadraticPerceptron.lean`)

**Data and labels.** The data are two samples `D = (b₁, b₂)` in `ℝ^d`, with label `+1` for
`b₁` and `−1` for `b₂`.

**Models.** There are two models (`Model.twoLayer`, `Model.conv`):

- **Two-layer linear network of width 1:** `m(b; c, v) = v⟨c, b⟩`, with `θ = (c, v) ∈ ℝ^d × ℝ`.
  - Data class (`InClass`): `⟨b₁, b₂⟩ > 0` and `b₂ ∦ b₁`. This is arbitrary two-point data whose
    linear separator is non-trivial.
  - This covers the two-layer analogue of dataset (5).
  - The excluded case `⟨b₁, b₂⟩ ≤ 0` is easy: the linear perceptron already has
    `⟨a₁, a₂⟩ ≥ 0` for the signed samples `a_i = y_i b_i`, so from zero initialization it
    separates in one batch step. No acceleration question arises there.
- **Convolutional model with kernel size 2** (the model of Thm 5.1): `m(b; c, v) = c₁⟨b, v⟩ +
  c₂⟨Pb, v⟩`.
  - Data class: `b₁ = s₁ 1_d` with `s₁ > 0`; `b₂` has positive mean `s₂ > 0`; and
    `w + Pw ≠ 0`, where `w = b₂ − s₂ 1_d`.
  - Dataset (5) is the instance `s₁ = 1`, `s₂ = 1 + µ/d`, `w = µ(e₁ − 1_d/d)`.

**Oracle.** At a query `θ`, the oracle returns both margins `y_i m(b_i; θ)` and their gradients
`y_i ∇_θ m(b_i; θ)`, exactly (`answer`). That is a first-order oracle on both samples. Every
iteration makes one call, and the budget counts calls.

**Algorithm (`family`, enforced through `allowedAlgorithm`).** The non-batch two-sample QPA of
Thm 5.1, without noise:

```
θ ← θ + γ ∇(y₁m₁)   if y₁ m(b₁;θ) ≤ 0
θ ← θ + γ ∇(y₂m₂)   else if y₂ m(b₂;θ) ≤ 0
θ ← θ               otherwise,
```

Here `γ > 0` is the step size and the output is the last iterate. The constructed algorithm
uses `γ = 1/(2R)`, with `R ≥ max(‖b₁‖, ‖b₂‖)`. Freezing at a separator is the paper's stopping
rule.

**Accuracy criterion (`successful`).** The output separates both samples:
`m(b₁; θ) > 0` and `m(b₂; θ) < 0`.

**Initialization.** Let `σ = −sign(z₀)`. The initialization is described by five scalar
coordinates of `θ₀`, defined in `coordinates`:

- `p, q, z` are the coordinates on which `A₁` and `A₂` act through the "fast" eigenvalues;
- `r, y` carry the slow `±µ` eigenvalues (conv only).

The admissible starts form the cone

- `σ(p₀ + q₀) ≥ aLo > 0`;
- `σ(p₀ − q₀) ≥ 0`;
- `|z₀| ≥ zLo > 0`;

together with:

- the size bound `2σp₀ + 2|z₀| ≤ S`;
- the conv-only ratio `|r₀ + y₀| ≤ ρ |r₀ − y₀|`.

The last condition is the deterministic counterpart of the paper's assumption
`⟨θ₀, v_{µ,+}⟩ ≠ 0`.

For an isotropic Gaussian `θ₀`, the sign conditions on `(p₀, q₀)` hold with probability exactly
1/4, and `z₀ ≠ 0` holds almost surely.

**The cone depends on the unknown data.** The sign `σ = −sign(z₀)` and the coordinates
`p, q, z, r, y` are defined through the data, so the algorithm cannot choose a start inside the
cone. The guarantee applies to whichever starts happen to lie in it; for a Gaussian `θ₀` that is
probability 1/4. The budget then also depends on the realized margins `aLo` and `zLo`.

**Spectral parameters.** These are known bounds on four data-dependent eigenvalues (`eigenvalues`),
written as `λ₁, λ₂, β, µ'` below:

- `gain ≤ λ₁, λ₂`;
- `βLo ≤ β ≤ βHi`;
- `µLo ≤ µ'` (conv only).

On dataset (5): `λ₁ = √(2d)`, `λ₂ ≈ √(2d)`, `β ≈ µ`, `µ' ≈ µ`.

## Main result

`result : Convergence spec budget`, with the one-line budget

```
⌈24·(R log ρ/µLo + 1)·(R/gain + 1)²·(3 + 2 βHi log ρ/µLo + log(S·(1/aLo + 8R³/(βLo³ zLo))))⌉₊
```

Starting from any admissible initialization, the noise-free non-batch QPA with `γ = 1/(2R)` is
**deterministically** at a separator after this many oracle calls (and at every later call).

What this gives on dataset (5), and on the two-layer model in general:

- **Conv model, dataset (5)**, with `R ≈ √d`, `gain ≈ √(2d)`, `β, µ' ≈ µ`. The bound is
  `O(√d/µ · log ρ · (log ρ + log(dS/(µ aLo zLo))))`, plus lower-order terms. This recovers
  the `Õ(√d/µ)` upper bound of Thm 5.1, up to logarithmic factors, and with it the gap to the
  `Ω(d/µ)` lower bound for the linear-model perceptron in Thm 5.2.
- **Two-layer model.** Here `µ' = 0` and `r = y = 0`, so we can take `ρ = 1`. The bound becomes
  `O((R/gain)² · log(S·(1/aLo + R³/(β³ zLo))))`.
  - On the two-layer analogue of dataset (5) (`β ≈ µ`, `R/gain = O(1)`) this is
    `O(log(d/µ))` (for `S/aLo` and `S/zLo` bounded).
  - That is an *exponential* implicit acceleration over the `Ω(d/µ)` of the linear-model batch
    perceptron, in the iteration count.

## What is new

1. **A deterministic, noise-free proof replacing the noise.**
   - Thm 5.1 needs injected Gaussian noise, a high-probability event and constants like `2²⁷`.
   - We prove that on the invariant cone `{a > 0, b ≥ 0, z ≠ 0}` no stall can occur.
   - The resulting guarantee is deterministic, with explicit constant 24, for every start in
     that cone. The cone contains a quarter of the Gaussian initializations.
   - The mechanism is two Lyapunov arguments for the switched linear system:
     - **Phase 2.** A potential `Ψ = c₂ min(c₁, c₂)(a + b) − 2eZ`:
       - is monotone under both modes;
       - contracts by `(1 − min(c₁, c₂)²)` over any two consecutive steps, *for any switching
         pattern*;
       - drops by `≥ 2e³Z₀` at every step with sample 2;
       - forces stopping within `2K + 2` steps once it is negative.
     - **Phase 1 (obstacle count).** At most `N = O(log ρ/(γµ))` steps with sample 2 happen
       while the slow `±µ` block blocks separation (`r² − y²` sign). During this phase the run
       lengths stay bounded by `K` because `a ≥ eZ₀` after every step with sample 2.

   No interpolation between the noisy and noiseless dynamics is needed. This is the
   "significantly simpler proof" the paper asks for, at the cost of restricting to the cone.
2. **Generalization beyond dataset (5).**
   - The same theorem covers arbitrary conv-model data with constant `b₁` and positive-mean
     `b₂`, with explicit dependence on the spectrum `(λ₁, λ₂, β, µ')`.
   - It also covers *arbitrary* two-point data in the two-layer width-1 linear network
     (`⟨b₁, b₂⟩ > 0`). There it shows logarithmic-time separation (`µ' = 0`: no slow block).
   - The paper lists general two-layer models as open (Sec. 6 and 8). Width 1 is the first step
     of that direction.
3. **Explicit dependence on the initialization.** The `√d/µ` factor appears only through
   `log ρ`, where `ρ = |r₀ + y₀|/|r₀ − y₀|`.
   - When the slow block already favours separation (`ρ = 1`, i.e.
     `|r₀ + y₀| ≤ |r₀ − y₀|`), the conv model is also logarithmic-time.
   - Simulations confirm this dichotomy. They are not part of the proof.

## Comparison with the closest results

| Result | Model / data | Algorithm | Guarantee |
|---|---|---|---|
| Tyurin 2026, [Thm 5.1](https://arxiv.org/abs/2512.11587) | conv k=2, dataset (5), `µ ≤ 1/10` | non-batch QPA + Gaussian noise, `γ = 1/(4√d)` | w.p. `1−ρ`, `Õ(√d/µ)` with constants `2²⁷`, any `θ₀` with `⟨θ₀, v_{µ,+}⟩ ≠ 0` |
| Tyurin 2026, Thm 5.2 | linear model, dataset (5) | batch perceptron | `Ω(d/µ)` for every init in `B(0, ϕε)`, including zero |
| Tyurin 2026, Thm 4.2 | conv, `n < (d+2)/4` | noiseless batch QPA | fails from a subspace |
| **This result** | conv k=2 (general constant/positive-mean data) and two-layer width 1 (any data with `⟨b₁,b₂⟩>0`) | non-batch QPA, **no noise**, `γ = 1/(2R)` | deterministic; budget above; cone inits (1/4 of Gaussian mass) |

Related large-step and two-layer logistic GD results:

- Wu–Bartlett–Telgarsky–Yu, COLT 2024;
- Zhang–Wu–Bartlett, ICML 2025;
- Zhang–Wu–Lin–Bartlett, JMLR 2026;
- Frei et al., JMLR 2021, on wide two-layer leaky-ReLU networks.

These analyse linear models, or two-layer networks with a fixed outer layer, under
margin-based assumptions. They do not study the factorized two-sample QPA.

## Limitations (stated honestly)

- **Cone only.** Outside the cone the noiseless dynamics can stall:
  - `a = 0` freezes option 1 forever;
  - with `b < 0`, runs follow the stable manifold of an option-2 saddle.

  So no deterministic bound in terms of `θ₀` statistics is possible there. Thm 5.1 covers almost
  every start, using noise; we do not.
- **Non-batch rule.** We analyse the non-batch rule, as Thm 5.1 does.
  - The batch QPA, which is the exact large-norm limit of GD (Thm 2.1), is not covered.
  - Simulations (observed, not proved) show heavy-tailed slow trajectories for 0.3–1% of
    starts.
- **Limit dynamics.** The theorem concerns the QPA, the large-norm limit of normalized logistic
  GD. It makes no quantitative claim about finite-norm GD.
- **A method-vs-method statement.** As with Thm 5.1, the comparison is between the factorized
  perceptron and the linear-model perceptron. Two-point data can be separated in `O(1)` steps by
  methods that search the span of the gradients, and by normalized or adaptive linear GD. So
  this is not a problem-class complexity improvement.
- **Scope of models and data.**
  - Width `f ≥ 2` two-layer models, kernels `k > 2`, and `n > 2` data points remain open.
  - Conv data with a non-constant `b₁` are not covered.
- **Comparison at matched initialization (observed, not proved).** Thm 5.2's `Ω(d/µ)` holds
  for `z₀ ∈ B(0, ϕε)`. In simulations from random initializations with the best fixed step, the
  linear-model perceptron's median is still `Θ(d/µ)` (1848 / 6900 / 25414 steps at
  `d = 16 / 64 / 256`, `µ = 0.01`). A constant fraction of random starts, however, finish in
  `O(√d/µ)` steps (about half at `d = 1024`). So the `d` versus `√d` separation describes
  typical behaviour, not every start.
- **No tightness claims.** We prove upper bounds only. We do not claim the `√d/µ` or `log(d/µ)`
  rates are tight for this algorithm.

## How the requirement to reprove or generalize Thm 5.1 is met

- **Same family.** The algorithm is the paper's non-batch two-sample QPA (perceptron limit of
  GD), enforced through `allowedAlgorithm`.
- **Same task and scaling.** The task is to separate the data, and the result recovers the
  `Õ(√d/µ)` implicit acceleration on dataset (5).
- **Generalization.** It extends the theorem to general data for the conv model and to the
  two-layer width-1 model, where the acceleration becomes logarithmic.
- **Trade-off.** It removes the injected noise and the high-probability event, at the price of
  the cone restriction on `θ₀`.
