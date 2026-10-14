# Parameter-free residual complexity for monotone equations with Hölder continuous operators

Lean files: theorem [`UniversalHolderMonotone.lean`](UniversalHolderMonotone.lean), setup
[`../Setups/HolderMonotone.lean`](../Setups/HolderMonotone.lean), algorithm
[`../Algorithms/UniversalRegularizedExtragradient.lean`](../Algorithms/UniversalRegularizedExtragradient.lean),
proofs `../Proofs/StronglyMonotoneZero.lean` and `../Proofs/UniversalRegularized{Step,Run,Convergence,Holder}.lean`.

## Setup

`E` is a finite-dimensional real inner product space and `F : E → E` satisfies

- monotonicity: `⟨F x − F y, x − y⟩ ≥ 0`;
- Lipschitz-plus-Hölder continuity: `‖F x − F y‖ ≤ L‖x − y‖ + H‖x − y‖^α` with `L, H ≥ 0`, `α ∈ (0, 1]`;
- a zero `x*` with `‖x0 − x*‖ ≤ R`.

The oracle returns `F(x)` at a queried point; the cost is the number of queries. The goal is a point with
`‖F(x̂)‖ ≤ ε`. The algorithm receives only `x0`, `ε` and a guess `r0 > 0` of the distance to a solution
(`Public` in the setup). It does **not** receive `L`, `H`, `α` or `R`; these appear only in the budget
(`Params`). The theorem is stated for `r0 ≤ R`; since `R` is only an upper bound on `‖x0 − x*‖`, an
overestimate `r0` is covered by applying the theorem with `R = r0`.

The Hölder class is the classical non-Lipschitz class for variational inequalities (Nemirovski 2004,
Dang–Lan 2015, Stonyakin et al. 2022); the sum form is the two-term case of Zhang's "sum of Hölder
operators" and is needed because a globally `α`-Hölder operator with `α < 1` cannot contain a bilinear
coupling. Typical instances, with interacting coordinates in any dimension, are the saddle operators of
`min_u max_v (1/p)‖Au‖_p^p + ⟨Bu, v⟩ − (1/q)‖Cv‖_q^q` with `p, q ∈ (1, 2]` (the gradient of `‖·‖_p^p` is
`(p−1)`-Hölder and not Lipschitz) and discretised `p`-Laplacian-type operators with `1 < p < 2`.

## Algorithm (universal regularised extragradient)

Stages `j = 0, 1, …` use the radius guess `ρ = r0·2^j`, the Tikhonov operator
`G_ρ(x) = F(x) + (ε/(4ρ))(x − x0)` and start from `x = x0`, `s = ρ/(2ε)`.

1. Query `F(x)`. If `‖F(x)‖ ≤ ε`, stop and return `x`.
2. If `‖G_ρ(x)‖ ≤ ε/2`, the guess `ρ` was too small: double `ρ` and restart the stage from `x0`.
3. Otherwise query `F(y)` at `y = x − s G_ρ(x)`. If `‖G_ρ(y) − G_ρ(x)‖ ≤ ‖G_ρ(x)‖/2`, set
   `x ← x − s G_ρ(y)` and go to 1; else halve `s` and repeat 3 (reusing `G_ρ(x)`).

Every query is counted: one per test point, one per accepted point, and the restart query at `x0`.
The returned point is the first queried point whose residual is at most `ε` (a stopped iterate, not
an average); after stopping the state machine idles.

## Guarantee

For every valid instance the algorithm returns `x̂` with `‖F(x̂)‖ ≤ ε` within

```
budget = ⌈40 (16 L R/ε + 2 (8 H R^α/ε)^{1/α} + log₂(R/r0) + 2) · log((32 L R/ε + 4 (8 H R^α/ε)^{1/α} + 4) R/r0)⌉
```

oracle calls (`theorem result : Convergence spec budget`), i.e.
`O((LR/ε + (HR^α/ε)^{1/α}) · log)` calls, with no knowledge of `L`, `H`, `α`, `R`.

## What is new

For the residual criterion the best previous bounds we found for Hölder continuous monotone operators are

| source | calls for `‖F‖ ≤ ε` (pure Hölder, constants dropped) | needs |
|---|---|---|
| Dang–Lan 2015 ([arXiv:1311.2776](https://arxiv.org/abs/1311.2776)), Thm 4.4, non-Euclidean extragradient for constrained generalised-monotone problems, best iterate | `ε^{-2/α}` | `H`, `α`, horizon `k` fixed in advance |
| Zhang 2026 ([arXiv:2606.22392v1](https://arxiv.org/abs/2606.22392v1)), Thm 1 (Tseng) | `ε^{-2/α}` (rate carries an extra `ln K`) | `H`, `α` |
| Zhang 2026, Thms 2 and 5 (anchored / symplectic extragradient) | `ε^{-2/(3α−1)}` (extra `ln K`), only `α > 1/3` | `H`, `α` |
| reduction: Tikhonov + universal restarted mirror-prox of Stonyakin et al. ([arXiv:1806.05140](https://arxiv.org/abs/1806.05140), Cor. 3, distance criterion) + Hölder conversion | `ε^{-2/(α(1+α))}·log` | `R` |
| **this theorem** | `ε^{-1/α}·log` | `ε` only |

So the exponent improves from `min{2/α, 2/(3α−1), 2/(α(1+α))}` to `1/α` for every `α ∈ (0, 1)`
(`α = 1/2`: `ε^{-2}` instead of `ε^{-8/3}`), it covers `α ≤ 1/3` where no accelerated-type bound was
available, and the method is parameter-free. At `α = 1` (or `H = 0`) the bound is `O((LR/ε) log)`, which
is the known optimal rate of anchored extragradient methods (Yoon–Ryu 2021, Lee–Kim 2021) up to the
logarithm: there is **no improvement in the Lipschitz case**. Recent work on non-Lipschitz monotone
inclusions with line search (Sun–Zhang–Zhao, [arXiv:2607.07585](https://arxiv.org/abs/2607.07585)) proves
convergence without a rate; parameter-free extragradient methods (Shen–Kılınç-Karzan,
[arXiv:2604.07662](https://arxiv.org/abs/2604.07662); Diakonikolas 2020,
[arXiv:2002.08872](https://arxiv.org/abs/2002.08872)) assume (local) Lipschitz continuity; universal
mirror-prox methods (Bach–Levy 2019, Stonyakin et al. 2022) bound the gap on a bounded set, and the gap
does not control the residual. Nguyen–Gasnikov ([arXiv:2608.03846](https://arxiv.org/abs/2608.03846)) study the
same instance family (Hölder-smooth `f`, `g` with bilinear coupling) with sliding methods, but with
separate oracles for `f`, `g` and the coupling and a gap criterion; they give no residual bound and are
not comparable with the single-oracle residual guarantee here.

**Mechanism.** Previous analyses replace Hölder continuity by an inexact Lipschitz model
`‖Fx − Fy‖ ≤ L_δ‖x − y‖ + δ` and pay `δ²` in every step; in anchored potentials these charges carry
weights `k²` (hence Zhang's exponents), in distance analyses they leave a floor. Here the Fejér analysis
of an extragradient step on the strongly monotone `G_ρ` uses continuity only for the pair
`(x, x − sG_ρ(x))`, whose separation is `s‖G_ρ(x)‖`, a computable residual. At separation `t` a Hölder
operator is Lipschitz with constant `L + H t^{α−1}`, so the acceptance test of step 3 can fail for a
step `s ≤ s̄ ≍ min{1/L, ε^{(1−α)/α}/H^{1/α}}` only if `‖G_ρ(x)‖ ≤ ε/2`, which is itself the stage's
success certificate (`pass_test`, `small_of_close` in `UniversalRegularizedStep.lean`). Hence the
non-Lipschitz error never enters the recursion: every accepted step contracts
`‖x − x_ρ‖²` by `1 − s·ε/(4ρ)` (`fejer_step`), `s` never drops below `s̄/2`, and a stage ends after
`O(κ_ρ log)` calls with `κ_ρ = 16Lρ/ε + 4 + 2(8Hρ^α/ε)^{1/α}`, which is linear in `ρ`, so the doubling
stages sum to a constant multiple of the last one. A stage with `ρ ≥ ‖x0 − x*‖` cannot end in a restart
because `‖F(x)‖ ≤ ‖G_ρ(x)‖ + (ε/(4ρ))·2‖x0 − x*‖ ≤ ε`. The regularised solution `x_ρ` is an analysis
device; its existence (Minty–Browder in finite dimension) is proved in `StronglyMonotoneZero.lean` by
induction along an orthonormal basis with the intermediate value theorem, so no solvability hypothesis
for the regularised problem is assumed.

## Limitations and open points

- The bound has a logarithmic factor and the output is a stopped iterate; a log-free anchored
  (Halpern-type) universal method for this class is not known to us. Anchored potentials use continuity
  on a pair whose separation is not a residual, which is where the argument above stops applying.
- Optimality in `ε` for `α < 1` is open. The only lower bound we can state for this class is
  `Ω(LR/ε)` (Lipschitz instances). The classical gap lower bound with exponent `2/(1+α)` is a
  bounded-domain result; it would transfer through `gap ≤ R·residual`, but we have not verified that
  transfer for this unconstrained class. We do not claim that `1/α` is optimal.
- Unconstrained equations only; no constraint set or set-valued part. The theorem is stated in finite
  dimension (used only for the existence of `x_ρ`).
- If `r0` is much smaller than `‖x0 − x*‖` the budget pays the additive `log₂(R/r0)` stages inside the
  first factor.
- For the distance criterion under strong monotonicity the bound of Stonyakin et al. is better than what
  this method gives; the improvement here is specific to the residual criterion.
