# Restarted accelerated gradient descent under strong growth and Lipschitz Hessians

**Theorem.** `OracleTemplate.StrongGrowthRestartedAgd.result` in
[`StrongGrowthRestartedAgd.lean`](StrongGrowthRestartedAgd.lean) proves
`Convergence LongTails.Setups.StrongGrowthHessianLipschitz.spec budget`.

## Setup

[`LongTails/Setups/StrongGrowthHessianLipschitz.lean`](../Setups/StrongGrowthHessianLipschitz.lean).
The instance is a function `f : E → ℝ` on a finite-dimensional real inner-product space with

- `f` twice continuously differentiable, `∇f` `L`-Lipschitz, `∇²f` `ρ`-Lipschitz (in operator norm);
- bounded initial gap: `f x0 - f x ≤ Δ` for all `x`;
- a stochastic gradient oracle `g x ω` with i.i.d. samples `ω ~ P0`, jointly measurable, unbiased
  (`∫ g x ω = ∇f x`) and satisfying the **strong growth condition**
  `∫ ‖g x ω - ∇f x‖² ≤ (κ - 1) ‖∇f x‖²` with `κ ≥ 1`.

The oracle returns one sample `g x ω_k` per call (`Seed := Ω`, law `P`, the i.i.d. stream law
`LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID`). The output must satisfy
`∫ ‖∇f (output ω)‖ ∂P ≤ ε` (expected gradient norm), and the public validity condition is
`0 < L, 0 < ρ, 1 ≤ κ, 0 ≤ Δ, 0 < ε` and `4^8 ρ ε ≤ L²` (the regime where `ε ≪ L²/ρ`, i.e. where the
`ε^{-7/4}` rate is meaningful; outside it the budget is dominated by one epoch).

The strong growth condition is the standard interpolation-type noise model of Vaswani, Bach and
Schmidt (AISTATS 2019; `arXiv:1810.07288`) and Schmidt–Le Roux (`arXiv:1308.6370`). In the
nonconvex case it forces every sample gradient to vanish at every stationary point of `f`
(interpolation of all stationary points). Concrete nonconvex families satisfying all assumptions:

- *masked gradients*: `g(x, ξ) = ∇f(x) · 1{ξ = 1} / p` with `ξ ~ Bernoulli(p)`, for any `C²` function
  with `L`-Lipschitz gradient and `ρ`-Lipschitz Hessian (so including functions with saddle points);
  then `κ = 1/p`;
- *multiplicative noise*: `g(x, ζ) = (1 + ζ) ∇f(x)` with `E ζ = 0`, `E ζ² < ∞`, so `κ = 1 + Var ζ`,
  again for any such `f`;
- *realizable over-parameterised generalised linear models* `f(x) = (1/n) ∑_i φ(a_iᵀ x − b_i)`, where
  `g` is one uniformly random summand's gradient, with a nonconvex `C^{2,1}` link `φ` whose derivative
  vanishes only at `0` (`φ'(t) = 0 ⇔ t = 0`), a data matrix `A` of full row rank (`n ≤ d`) and a
  realizable target (`b = A x⋆`). Then `∇f(x) = (1/n) Aᵀ φ'(Ax − b)` vanishes only where `Ax = b`, so
  every stationary point is global, and
  `E_i ‖∇f_i‖² ≤ (max_i ‖a_i‖² / n) ‖φ'‖² ≤ n · max_i ‖a_i‖² / σ_min(A)² · ‖∇f‖²`
  gives `κ ≤ n · max_i ‖a_i‖² / σ_min(A)²`.

Over-parameterised least squares is also covered but is convex; the point of the result is that no
convexity, PL or dispersive-noise condition is used.

## Algorithm

[`LongTails/Algorithms/StrongGrowthRestartedAgd.lean`](../Algorithms/StrongGrowthRestartedAgd.lean),
`method cfg x0`. All oracle calls are grouped into mini-batches of `b = ⌈800 κ⌉` samples. An epoch
consists of `K + 1 + m` batches:

1. `K` accelerated steps `y_k = x_k + (1-θ)(x_k - x_{k-1})`, `x_{k+1} = y_k - η ḡ(y_k)` with
   `η = 1/(8L)` and `θ = (ρ ε / L²)^{1/4}`, each followed by the **movement test**
   `(k+1) ∑_{i≤k} ‖x_{i+1} - x_i‖² > B²` (`B = √(ε/ρ)/1024`); after a trigger the remaining
   accelerated batches of the epoch are skipped (frozen);
2. one gradient step `x ← x - (1/L) ḡ(x)` from the current point;
3. `m` validation batches at the parabolically weighted average
   `ȳ = ∑_k w_k y_k`, `w_k ∝ k (K-k)`; the candidate is accepted iff the epoch was untriggered and a
   majority of validation batch means satisfy `‖ḡ(ȳ)‖ ≤ 3ε/8`.

An accepted candidate is returned. Otherwise the next epoch restarts from the current point;
after `N1` epochs a new trial restarts from `x0`; there are `R` trials. The output is the accepted
candidate, or `x0` if no trial accepts. The algorithm is deterministic given the samples
(`Seed = Unit`).

## Guarantee and cost

For every valid parameter tuple and admissible instance,
`∫ ‖∇f(output)‖ ≤ ε`, after exactly

`budget = R · N1 · (K + 1 + m) · b`

oracle calls, where (as one explicit formula in the theorem file)
`b = ⌈800 κ⌉`, `K = ⌈(L²/(ρ ε))^{1/4}⌉`, `N1 = ⌈2^28 Δ √ρ / ε^{3/2}⌉ + 1`,
`R = ⌈log(1 + 8√(2LΔ)/ε)⌉ + 1`, and `m = 8 + ⌈2 log(1 + 8 R̄ N̄ Ḡ / ε)⌉` with
`R̄ = log(1 + 8√(2LΔ)/ε) + 2`, `N̄ = 2^28 Δ √ρ/ε^{3/2} + 2`,
`Ḡ = √(8LΔ + L ε √(ε/ρ) + ε²) + L √(ε/ρ)`.

Hence the oracle complexity is

`O( κ · L^{1/2} ρ^{1/4} Δ ε^{-7/4} · log(LΔ/ε) · (1 + log(LΔ/ε)) )`

up to the additive one-epoch term `O(κ (L²/(ρε))^{1/4} log(·))`; i.e. `Õ(κ L^{1/2} ρ^{1/4} Δ ε^{-7/4})`.
Frozen and ignored blocks after a trigger are pure budget waste that the accounting keeps
(every epoch has exactly `K + 1 + m` batches).

## What is new

The closest prior results are:

- **SGD under strong growth** (Vaswani–Bach–Schmidt 2019, Theorem 3; Schmidt–Le Roux 2013):
  `O(κ L Δ ε^{-2})` calls on `L`-smooth nonconvex functions. Their statement bounds the squared
  gradient norm of the best iterate (`min_k E‖∇f(x_k)‖² ≤ ε²`); the random-iterate version implies
  our criterion `E‖∇f(out)‖ ≤ ε` by Jensen's inequality, so the two are comparable. This is the
  baseline we improve: our rate is faster by the factor `(ρ ε / L²)^{1/4}` whenever
  `ε ≤ L²/4^8 ρ`, at the price of the additional Hessian-Lipschitz assumption and polylogarithmic
  factors.
- **Deterministic restarted AGD** (Li and Lin, "Restarted nonconvex accelerated gradient descent:
  no more polylogarithmic factor in the O(ε^{-7/4}) complexity", ICML 2022, PMLR 162, and JMLR
  24(157):1–37, 2023; main restarted-AGD theorem, Theorem 1 in the arXiv/ICML version):
  `O(L^{1/2} ρ^{1/4} Δ ε^{-7/4})` exact gradient evaluations. Our algorithm is a stochastic
  mini-batch variant of this method and our rate recovers theirs at `κ = 1` up to logarithms.
- **Inexact restarted AGD** (Yang, Luo, Li and Jordan, `arXiv:2307.00126`, Theorem 3.4 and
  Lemmas B.1–B.5): restarted AGD with *deterministic absolute* gradient errors of tolerance
  `O(ε²)`. Our oracle has a *constant relative* stochastic error (`E‖g − ∇f‖² ≤ (κ−1)‖∇f‖²`);
  reducing it to an absolute `ε²` error by batching would cost `(κ−1)‖∇f(x)‖²/ε⁴` samples per
  step, so their analysis does not transfer, and the martingale structure (noise cancels in
  expectation) is what the present proof exploits instead.
- **Stochastic acceleration with bounded variance**: Cutkosky–Mehta (ICML 2020, Theorem 3) obtain
  `O(ε^{-7/2})` (with an `ε^{-2}`-type deterministic part) under `E‖g − ∇f‖² ≤ σ²`; Fang–Lin–Zhang
  (COLT 2019) obtain `Õ(ε^{-7/2})` to second-order stationarity under dispersive noise;
  Cutkosky–Mehta–Orabona (2023) give `O(ε^{-7/4} log(1/ε) + ε^{-7/2})`, and the unified
  `O(ε^{-7/4} + σ² ε^{-7/2})` bound interpolating the deterministic and the optimal stochastic
  rates is due to Patitucci, Jiang and Mokhtari (`arXiv:2510.03167`, double-optimistic
  online-to-nonconvex conversion). The strong growth model is not covered by any of these: the
  noise is relative and unbounded (`σ = ∞`), and plugging a worst-case `σ² ≤ 2(κ-1)LΔ` yields
  `κ L Δ ε^{-7/2}`, far slower than ours.
- **Perturbed SGD under strong growth + Hessian Lipschitz** (Roy et al., NeurIPS 2020 "Escaping
  saddle-points faster under interpolation-like conditions", which additionally assumes
  sub-Gaussian noise): `Õ(κ ε^{-2})` to second-order stationarity, a different (stronger) output
  criterion but no `ε^{-7/4}` acceleration.

To our knowledge, no prior work establishes an `ε^{-7/4}` first-order oracle complexity for
nonconvex optimisation with stochastic gradients under the strong growth condition. A `κ`-linear
dependence is natural for this oracle family (a gradient revealed with probability `1/κ` and zero
otherwise satisfies strong growth, and a zero-respecting algorithm then sees a deterministic oracle
only every `κ` calls on average); this is an informal heuristic, not a proved lower bound.

## Technical mechanism

The analysis replaces Li–Lin's unrolled per-coordinate recursion (which is incompatible with a
data-dependent stopping time in the presence of noise) by a **quadratic Lyapunov function per
eigen-coordinate of the Hessian at the epoch start**,
`Q_j(z,d) = g_j(z) + c_j g_j'(z) d + d²/(2η)` with `c_j = 3/5` on strongly concave coordinates and
`c_j = 2/5` otherwise. A linear-matrix-inequality (verified as polynomial inequalities in
[`StrongGrowthAgdLmi.lean`](../Proofs/StrongGrowthAgdLmi.lean)) gives a *pathwise* one-step
inequality with an explicit martingale term, so that only second moments of the noise are needed
and the movement-based restart can be analysed with ordinary telescoping over blocks of fixed
length. The certificate at an untriggered epoch is the parabolically weighted average: its
model gradient telescopes to a sum of `O(θ²)`-weighted displacements, and the weighted noise
average has second moment controlled by the accumulated Lyapunov decrease of the same epoch, so
bad candidates are themselves rare without any energy test or hiding argument. Validation uses a
base-4 Chernoff bound (`((1 + 3·4δ²)/2)^m` with `δ² = (κ-1)/b ≤ 1/800`) and the final
expectation bound is obtained by a drift lemma on three nested time scales (blocks, epochs,
trials), all formalised generically in
[`StrongGrowthAgdDrift.lean`](../Proofs/StrongGrowthAgdDrift.lean).

## Constants used by the proof

All internal constants are explicit functions of the public parameters (`cfgOf` in
[`StrongGrowthAgdBudget.lean`](../Proofs/StrongGrowthAgdBudget.lean)); the public budget inlines them.

| quantity | value | role |
|---|---|---|
| `η` | `1/(8L)` | accelerated step size |
| `θ` | `(ρε/L²)^{1/4}` | momentum parameter; `θ ≤ 1/16` under `4^8 ρε ≤ L²` |
| `K` | `⌈1/θ⌉` | accelerated batches per epoch (`1 ≤ θK ≤ 2`) |
| `B` | `√(ε/ρ)/1024` | movement radius (`ρB² = ε/2^20`) |
| `b` | `⌈800κ⌉` | batch size, so the batch-mean relative variance is `δ² = (κ-1)/b ≤ 1/800` |
| `η_f` | `1/L` | final gradient step of an epoch |
| `thr` | `3ε/8` | validation threshold (`= 3ε_i/2`, `ε_i = ε/4`) |
| `D_m` | `4ρB² = ε/2^18` | model-error radius |
| `A_0` | `θ²B²/(32η) = ε√(ε/ρ)/2^22` | guaranteed Lyapunov decrease of a triggered epoch |
| `c_epoch` | `K(58/25·η/θ + 8η)D_m² + 8ρB³ + 18ηD_m² ≤ A_0/25` | expected Lyapunov inflation per epoch |
| `N1` | `⌈2^28 Δ√ρ/ε^{3/2}⌉ + 1 = ⌈64Δ/A_0⌉ + 1` | epochs per trial |
| `R` | `⌈log(1 + 8√(2LΔ)/ε)⌉ + 1` | trials |
| `m` | `8 + ⌈2 log(1 + 8 R̄ N̄ Ḡ/ε)⌉` | validation batches per epoch |

The proof shows: a triggered epoch decreases the Lyapunov function by at least `A_0` in expectation
(minus `c_epoch`), so at most `Δ/A_0 + …` epochs per trial can trigger; an untriggered epoch returns a
candidate `ȳ` with `‖∇f(ȳ)‖ ≤ cert + ‖N_K‖`, `cert ≤ 0.0711 ε < ε_i`, where the weighted noise `N_K`
has second moment bounded by the epoch's own Lyapunov decrease; validation rejects a candidate with
`‖∇f(ȳ)‖ > 3ε_i` with probability at least `1 - r^m` and accepts a good one with probability at least
`1 - r^m`, `r = (1 + 12δ²)/2 ≤ 203/400`. Each trial fails with probability at most `1/4`, giving the
`(1/4)^R` term, and the final bound is
`E‖∇f(out)‖ ≤ ‖∇f(x0)‖(1/4)^R + 3ε_i + R N1 r^m (τ/2 + L(Δ + N1 c_epoch)/τ + 2LB) ≤ ε/8 + 3ε/4 + ε/8`.

## Limitations

- **The universal constant is enormous.** The leading constant of the budget is
  `800 · 2^28 ≈ 2·10^11` (times the two logarithmic factors). Compared with the SGD bound
  `O(κ L Δ ε^{-2})` (Vaswani–Bach–Schmidt 2019, Theorem 3, whose constant is a small number), our
  bound is numerically smaller only when `(L²/(ρε))^{1/4}` exceeds roughly `10^{11}`–`10^{12}` times
  polylogarithmic factors, i.e. (ignoring logarithms) when `ε ≲ L² / (10^{45} ρ)`: an asymptotic
  improvement regime, not a practical one. The contribution is the improved rate
  exponent `ε^{-7/4}` (and the proof technique), not a practically tuned method. No attempt was made
  to optimise constants; the batch size `800κ`, radius `√(ε/ρ)/1024` and the epoch count
  `2^28 Δ√ρ/ε^{3/2}` are what the current Lyapunov and Chernoff estimates require.
- Two logarithmic factors (`R` trials and `m` validation batches) remain; removing them as Li–Lin
  did in the deterministic case is open.
- The guarantee is `E‖∇f(out)‖ ≤ ε` (first-order stationarity); second-order stationarity is not
  claimed.
- The regime `4^8 ρ ε ≤ L²` is assumed; otherwise the single-epoch SGD-type bound applies.
- The improvement over SGD is in the `ε`-exponent only when `Δ`, `L`, `ρ`, `κ` are held fixed; the
  `κ` dependence is linear in both bounds and the `Δ` dependence is linear in both.
