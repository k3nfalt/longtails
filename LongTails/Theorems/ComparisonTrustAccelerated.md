# Accelerated nonconvex optimization from comparisons only: Õ(n·L^{1/2}ρ^{1/4}Δ·ε^{-7/4}) comparisons

## Lean files

- Main theorem: [`ComparisonTrustAccelerated.lean`](ComparisonTrustAccelerated.lean). It defines `OracleTemplate.ComparisonTrustAccelerated.result : Convergence spec budget`.
- Setup: [`../Setups/ComparisonHessianLipschitz.lean`](../Setups/ComparisonHessianLipschitz.lean).
- Algorithm: [`../Algorithms/ComparisonTrustRegion.lean`](../Algorithms/ComparisonTrustRegion.lean), with `outerPlan`, `epochPlan`, `guessPlan`, `hvpPlan`, `dirPlan`, `ternaryPlan` and the explicit `tuning`.
- Proofs: `../Proofs/ComparisonTrust{Plans,Direction,Taylor,Hvp,Agd,Quadratic,Line,Guess,Epoch,Outer,Bounds,Tuning,Execution,Visits}.lean`.

## Setup and assumptions

**Problem.** `E` is a real inner-product space of arbitrary finite dimension `n = dim E`. The objective `f : E → ℝ` satisfies:

- `f` is C²;
- `∇f` is `L`-Lipschitz;
- the Hessian `∇²f = D(∇f)` is `ρ`-Lipschitz in operator norm;
- `f(x₀) − f(x) ≤ Δ` for every `x`.

These are exactly the assumptions of the comparison-oracle papers we compare with: Tao–Zhang–Wang–Zhang–Li and Wang–Zhang–Tao–Zhang–Li, both below. They are also the standard class for ε^{-7/4} first-order methods (Carmon–Duchi–Hinder–Sidford; Jin–Netrapalli–Jordan; Li–Lin). No assumption is added.

**Oracle.** A query is a pair `(x, y)`. The answer is the single bit `decide (f x ≤ f y)`, which is exact and deterministic. The algorithm never sees function values, gradients or Hessians. It may use `n, L, ρ, Δ, ε`.

**Accuracy criterion.** The output is a list of points, and the theorem states, for every run, `∃ x ∈ output, ‖∇f x‖ ≤ ε`. This is the "visits an ε-stationary point" criterion used by the comparison baseline 2606.27082.

**Admissible algorithms (`allowedAlgorithm`).** The setup restricts the output to visited points: for every oracle, budget and seed, every point in the output of `executeWithTrace` must be `x₀` or a component of some query `(x, y)` in the execution trace. Without this condition the criterion would be vacuous. A fixed ε/(2L)-net of the ball around `x₀` reachable by gradient descent contains an ε-stationary point of every admissible `f`, and such a net needs no queries. The theorem proves this restriction for the algorithm (`trace_visits`, `outer_cov` in `ComparisonTrustVisits`). It holds for every oracle, not only the comparison oracle, and also for truncated budgets.

**Why the criterion cannot be a certified single point.** Comparisons cannot certify which visited point is ε-stationary. Suppose `f` is admissible with constants `(L/2, ρ/2, Δ/2)`. Then `1.5 f` is admissible with constants `(L, ρ, Δ)`, and it produces exactly the same comparison answers. A visited point with `‖∇f‖ ∈ (2ε/3, ε]` is ε-stationary for `f` but not for `1.5 f`.

## Algorithm (`outerPlan`)

The algorithm runs `T` epochs. Each epoch starts at the current centre `x`, writes `c = ‖∇f(x)‖` for the unknown gradient norm, and uses the trust radius `r = √(ε/ρ)/4` and the level `γ = √(ρε)`.

1. **Normalized gradient (`dirPlan`).** This uses `n(m+2)` comparisons. Each query is a symmetric sign test `f(y − τw) ≤ f(y + τw)`; it determines `sign⟨∇f(y), w⟩` up to an additive error `9ρτ²/2`. The estimator then finds a champion coordinate by a tournament and bisects all ratios `g_i/g_j*`.
2. **Radial curvature (`ternaryPlan`).** A ternary search along `x − tû` for `t ∈ [0, r]` returns `κ̂ = 1/t̂`. This is the only Hessian entry not identifiable from directions: replacing `f` by `ψ∘f` shifts `H/‖∇f‖` by `(ψ''/ψ')‖∇f‖·uuᵀ`.
3. **Scale-free Hessian-vector products (`hvpPlan`).** For a vector `v`, set
   `Ã(v) = τ_v⁻¹(I − ûûᵀ)Dir(x + τ_v v) + (⟨T(û), v⟩ + κ̂⟨û, v⟩)û`, with `τ_v = τ₀/‖v‖`.
   This estimates `H v/‖∇f(x)‖` (Lemma `hvp_bound`). The magnitude ratio `‖∇f(y)‖/‖∇f(x)‖` is never solved for, so there is no angle or degeneracy condition.
4. **Scale guesses.** For `j < J`, set `ĉ_j = 2^j ε`. Since `‖∇f(x)‖ ≤ G = √(2LΔ)` whenever `f(x) ≤ f(x₀)`, exactly one guess satisfies `ĉ_j ∈ [c, 2c)`, and `J = ⌈log₂(G/ε)⌉ + 1`.

   For each guess (`guessPlan`), run `N` steps of the CDHS-type accelerated scheme on the computed regularized quadratic model with gradient `ĉû + ĉÃ(s) + 2γs`. Then run `4N` Rayleigh checks `⟨d, ĉÃ(d) + 2γd⟩ ≥ (γ + 12η)‖d‖²`.

   The guess contributes four candidates:
   - `x ± r·d/‖d‖` for the first failing check (negative curvature);
   - `x + x_N`;
   - `x + min(1, r/‖x_N‖)·x_N`.
5. **Short normalized step.** Add the candidate `x − (r/8)û`.
6. **Selection.** The next centre is the best candidate, found by a comparison tournament. All candidates are appended to the output list.

The algorithm takes the same actions in every case. It never tests an absolute quantity it cannot observe.

## Guarantee and cost

`result` proves that every run returns a list containing an ε-stationary point within the budget

`budget = (⌊400 Δ √ρ / ε^{3/2}⌋₊ + 1) · ⌈250000 (n+1) √(2L/√(ρε) + 4) · log(2 + n + L/√(ρε) + √(2LΔ)/ε)³⌉₊`

comparisons. Writing `Λ = log(2 + n + L/√(ρε) + √(2LΔ)/ε)`, this is

`O( n · Δ L^{1/2} ρ^{1/4} ε^{-7/4} · Λ³ )`.

That holds in the meaningful regime `L/√(ρε) ≳ 1`. In general the bound is `O((Δ√ρ ε^{-3/2} + 1)·n·(√(L/√(ρε)) + 1)·Λ³)`.

**Accounting.** The budget counts every comparison the plan issues: sign tests, tournaments, bisections, ternary search, all Hessian-vector probes for every guess, every Rayleigh check, and the final tournament. The Lean proof bounds the exact plan length `epochLen · T` by this expression (`epochLen_real`). The constants are crude.

## What is new

| Work | Oracle | Guarantee (ε-stationary point, Lipschitz gradient and Hessian) |
|---|---|---|
| Tao–Zhang–Wang–Zhang–Li, [arXiv:2405.11454](https://arxiv.org/abs/2405.11454) (v1 optimization results; v3 at ICML 2026) | comparisons | `Õ(n L Δ / ε²)` (normalized GD); `Õ(n^{1.5}/ε^{2.5})` to an approximate SOSP |
| Wang–Zhang–Tao–Zhang–Li, [arXiv:2606.27082](https://arxiv.org/abs/2606.27082) v1 (ICML 2026), main classical theorem | comparisons | `Õ(n² ε^{-3/2})`, visits an ε-stationary point with probability ≥ 2/3 |
| **This result** | comparisons, deterministic | `Õ(n L^{1/2} ρ^{1/4} Δ ε^{-7/4})` |
| Exact value oracle: finite-difference gradients and Hessian-vector products combined with Li–Lin 2022 | function values | `Õ(n·ε^{-7/4})` value queries |
| Carmon–Duchi–Hinder–Sidford 2017; Li–Lin 2022; Royer–O'Neill–Wright 2020 | values + gradients / gradients / gradients + Hvp | `O(ε^{-7/4})` oracle calls (this rate is optimal for first-order methods by [arXiv:2606.05438](https://arxiv.org/abs/2606.05438)) |

So, up to logarithmic factors, single-bit comparisons match exact function values in this class.

In this repository, `ComparisonSmoothConvex` (PR #95) gives accelerated comparison complexity `Õ(n√(LR²/ε))` for smooth *convex* problems. The present result is complementary: it covers the nonconvex class with Lipschitz Hessian. Its direction estimator was developed independently, because #95 was not on the recorded base of this work.

**Improvement regimes.** The bound is never worse than `n/ε²` up to logarithms. That covers every `n` once `ε ≲ L²/ρ`.

Against the `n²ε^{-3/2}` bound of 2606.27082 it improves exactly when `n ≳ (L²/(ρε))^{1/4}` up to logarithms, which is the high-dimensional regime. It answers negatively, in that regime, the question raised there of whether the `n²` dependence is necessary. For small `n` the `n²ε^{-3/2}` bound remains better; we do not claim uniform improvement.

Our guarantee is deterministic, while the baseline's holds with probability 2/3. Both use the same "visits" criterion. We have no matching lower bound in the comparison model.

**Why the obvious reduction does not apply.** Combining the `O(n log(1/δ))` comparison estimator of normalized gradients with an `ε^{-7/4}` Hessian-vector method fails for two reasons:

- comparisons reveal only the scaled quantities `∇f/‖∇f‖` and `H/‖∇f‖` (up to the radial ambiguity above);
- every known `ε^{-7/4}` Hvp method uses absolute quantities: the damping `2√(ρε)I` in capped CG, the regularizer `γ‖x − y‖²` in CDHS, and absolute descent or Armijo tests.

The new mechanisms are:

1. **A scale-free Hessian-vector product.** It needs no magnitude ratios and no angle condition, and the only non-identifiable entry is obtained by a line search exactly when it matters. This is in contrast with the direction-only `ComparisonHessVec` of 2606.27082.
2. **A logarithmic scale-guess grid with comparison selection.** It makes absolute regularization usable at a `log(G/ε)` cost.
3. **An inexact guarded AGD on the model quadratic.** The certificates are computable Rayleigh checks with a margin. The analysis includes an explicit radius induction, so all Hvp errors stay additive (`ComparisonTrustAgd`, `ComparisonTrustQuadratic`).

**Example instances.** For example `f(x) = Σ_j φ(⟨a_j, x⟩) + ½xᵀQx`, with indefinite `Q` and smooth sigmoidal or log-cosh `φ`, in any dimension, or the Carmon et al. hard chains. The comparison oracle models preference or ranking feedback, as in RLHF-style or human-in-the-loop optimization.

## Limitations

- The criterion is "visits" (an existential over the output list), not a certified output. As explained above, this is unavoidable with comparisons.
- There are three logarithmic factors and very large explicit constants.
- The method uses a single global scale bound `G = √(2LΔ)`, which enters only logarithmically.
- The result is first-order stationarity only. The negative-curvature branch suggests an approximate second-order version, but we do not prove one.
- Comparisons are exact. Noisy (Bradley–Terry) comparisons are not covered.
- We prove no lower bound, so whether `n·ε^{-7/4}` is optimal for comparison oracles remains open.
