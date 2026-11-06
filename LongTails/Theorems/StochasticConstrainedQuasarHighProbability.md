# Finite-variance, gradient-only quasar optimization with constraints and high confidence

The [main theorem](StochasticConstrainedQuasarHighProbability.lean) proves a high-probability objective guarantee for smooth quasar-convex optimization over a compact convex set, using fresh stochastic gradients and exact Euclidean projections. Its contribution is the combination of accelerated low-noise complexity, finite variance, logarithmic confidence dependence, and a deterministic oracle budget, without objective values, quadratic growth, bounded gradients, or samplewise smoothness.

## Specification and guarantee

The [setup](../Setups/StochasticConstrainedQuasar.lean) is in an arbitrary finite-dimensional real Hilbert space. The feasible set `X` is nonempty, compact, convex, and has diameter at most `D`; the supplied initial point is feasible. There is a constrained minimizer `xstar`. On `X`, the objective is differentiable, its gradient is `L`-Lipschitz, and

\[
\gamma(f(x)-f(x_\star))\leq\langle\nabla f(x),x-x_\star\rangle,
\qquad 0<\gamma\leq1.
\]

Differentiability is ambient differentiability at each feasible point. Neither the Lipschitz nor quasar inequality is required outside `X`. In particular, a boundary minimizer need not have zero gradient. The oracle has two channels: an unbiased gradient with central second moment at most `σ²`, and exact Euclidean projection onto `X`. The gradient oracle is jointly measurable; its vector and squared-error integrability are explicit. Samples are fresh IID under an abstract probability law. The proof derives the product representation internally rather than assuming a product sample space in the setup. The algorithm uses known upper bounds `L,D,σ`, the quasar parameter `γ`, and requested `ε>0`, `0<δ<1`; it never uses `xstar`, `f(xstar)`, or objective values.

Write

\[
p=2+\lceil8\log(8/\delta)\rceil,\quad
b=\operatorname{clog}_2\!\left\lceil2+\frac{LD^2}{\gamma^2\epsilon}\right\rceil,
\quad
S=1+\frac{\sqrt{LD^2/\epsilon}}\gamma+
\frac{\sigma^2D^2}{\gamma^2\epsilon^2}.
\]

Here `clog₂ n` is the ceiling binary logarithm, the least natural `k` with `n≤2^k`. The public Lean budget substitutes all these expressions directly:

\[
B=\left\lceil2^{96}p(1+b)^2S\right\rceil.
\]

With `B` calls available to **each** channel, the actual `execute` output satisfies

\[
\Pr\{\widehat x\in X,\ f(\widehat x)-f(x_\star)\leq\epsilon\}\geq1-\delta.
\]

Thus the framework execution uses at most **`2B` total oracle calls**, including projection calls and padding after a query plan terminates. The algorithm's unpadded plan is itself bounded by `B`. This is a hard budget, not an expected-work guarantee. The constant `2^96` is deliberately conservative; no practical constant claim is made. The rate is

\[
O\!\left(\log(8/\delta)
\left[1+\log\!\left(2+\frac{LD^2}{\gamma^2\epsilon}\right)\right]^2
\left[1+\frac{\sqrt{LD^2/\epsilon}}\gamma+
\frac{\sigma^2D^2}{\gamma^2\epsilon^2}\right]\right).
\]

The two logarithmic factors and both channels matter in comparisons. In the low-noise regime `σ² ≲ γ sqrt(L) ε^(3/2)/D`, the accelerated term dominates; otherwise the variance term dominates. This is not a claim of optimal dependence on `γ`, logarithms, dimension through the parameters, or universal superiority to deterministic/value-oracle results. In particular the construction retains logarithmic overhead even at `σ=0`. When `ε≥4LD²`, it uses a simpler robust projected step and does not charge unused outer iterations.

## Algorithm and proof mechanism

The [program and returned output](../Algorithms/StochasticQuasarProgram.lean) implement a query plan, then run it through `Template.execute`. [Parameters](../Algorithms/StochasticQuasarParameters.lean), [inner solver](../Algorithms/StochasticQuasarInner.lean), [finite MLMC estimator](../Algorithms/StochasticQuasarMlmc.lean), [accelerated transitions](../Algorithms/StochasticQuasarAcceleration.lean), and [cleanup](../Algorithms/StochasticQuasarCleanup.lean) specify every tuning and output choice.

1. Form the constrained envelope `M(c)=min_{u∈X}{f(u)+L‖u-c‖²}` in the analysis. The regularized problem is `L`-strongly convex on `X`; its minimizer defines a globally `2L`-smooth envelope preserving the quasar inequality. Projection optimality supplies the boundary terms. The algorithm does not receive an exact envelope or proximal oracle.
2. Approximate its gradient using projected stochastic inner iterations and a finite multilevel telescope. The inner solver has variance-dependent cost and squared-distance contraction even when the constrained optimum has a large normal gradient. Finite levels give a biased estimator; that bias is retained throughout the outer analysis. Expected and maximal level costs are both bounded.
3. Run a confidence-damped continuized accelerated process, with a projected auxiliary iterate, a smooth finite-time weight, clipped multilevel gradients, and a fixed number of random holding times. The central proof is a **noisy projected power-barrier bound**. For energy `Φ=A(M-M*)+‖z-xstar‖²/2`, the negative gradient drift absorbs jump variation; clipping bias and multilevel bias contribute explicit remaining drift. A bounded barrier and compensation control failure without assuming bounded trajectories, sub-Gaussian noise, or higher noise moments. This is the substantive step beyond the expected Moreau/MLMC reduction. See [energy moments](../Proofs/StochasticQuasarEnergyMoments.lean), [barrier](../Proofs/StochasticQuasarBarrier.lean), [process](../Proofs/StochasticQuasarProcess.lean), and [run moments](../Proofs/StochasticQuasarRunMoments.lean).
4. Cap total multilevel work using the internally sampled levels before querying the stochastic oracle. Over-budget seeds return the initial point. Analysis uses the uncapped process and a separate cap-failure bound, not a conditional IID claim. Two clock tails and the compensated barrier control the remaining outer failure.
5. Return a feasible point using replicated proximal estimates, a medoid, a fresh robust gradient estimate, and a projected regularized step. Distance to a boundary proximal minimizer alone does **not** imply a small objective gap; the final projected step proves the needed objective inequality without bounding its normal gradient. Freshness is proved across the actual seed-dependent query prefix. See [cleanup geometry](../Proofs/StochasticQuasarCleanupGeometry.lean), [program cleanup](../Proofs/StochasticQuasarProgramCleanup.lean), and [specification assembly](../Proofs/StochasticQuasarSpecification.lean).

All gradient queries are feasible. The main theorem is existential over algorithms with the specified oracle access, with the concrete program as witness; it imposes no artificial algorithm-family restriction. The supporting formalization handles the random output, its measurability, IID transport, projection feasibility, every batch and level, random prefix offsets, clock tails, and actual execution. [Budget scales](../Proofs/StochasticQuasarBudgetScales.lean) and [cost](../Proofs/StochasticQuasarBudgetCost.lean) prove the simplified formula, including cleanup and rounding.

## Prior results and the remaining gap

Literature checking was performed independently by the Researcher and Reviewer on November 5–6, 2026, covering the recent ICML, ICLR, NeurIPS proceedings/OpenReview editions, recent arXiv submissions and revisions, and older foundational results. Accepted conference papers and unreviewed preprints are distinguished below. The claim concerns the combined guarantee above; neither the envelope construction, MLMC, robust mean estimation, exact-gradient high-probability acceleration, nor a Lean formalization alone constitutes the novelty.

| Primary result | Applicable comparison and limitation |
|---|---|
| [Martínez-Rubio, AISTATS 2026](https://proceedings.mlr.press/v300/martinez-rubio26a.html), [2510.01943v3](https://arxiv.org/abs/2510.01943v3), July 14, Theorem 5 | Constrained smooth quasar acceleration is already known with deterministic value-and-gradient access. The objective geometry is an established class. The present change is stochastic finite-variance gradient-only access with a high-confidence hard budget; it is not a new deterministic constrained acceleration claim. |
| [Fu, Xu, Wilson, ICML 2023](https://proceedings.mlr.press/v202/fu23e.html), [2305.04736v2](https://arxiv.org/abs/2305.04736v2), Theorem 3.2 | Accelerated stochastic quasar optimization with expected objective accuracy, component value/gradient access and bounded-gradient assumptions. Its high-probability work accounting is distinct from logarithmic-confidence objective accuracy. |
| [Wang and Wibisono, ICLR 2023](https://openreview.net/forum?id=yYbhKqdi7Hz), [2302.07851v1](https://arxiv.org/abs/2302.07851v1), Corollary 1 | Continuized quasar acceleration and random-clock analysis are established. Its probability conversion has polynomial confidence dependence. Exact-gradient high-confidence acceleration also already exists in this repository and is not claimed here as new. |
| [Gbaguidi–Hermant, 2607.19965v1](https://arxiv.org/abs/2607.19965v1), July 22, Theorem 11, §4.2.2, Eq. (44), preprint | Already provides a noisy high-probability result. Its comparison uses polynomial confidence dependence, global geometry, paired same-sample values and samplewise/strong-growth conditions. The present theorem is not the first noisy high-probability quasar result; it changes these oracle/assumption requirements and the confidence dependence. |
| [Kuruzov, 2611.04597v1](https://arxiv.org/abs/2611.04597v1), November 3, Theorem 4.3, preprint | Expected accelerated bounds with biased and variable-variance gradients are a strong baseline for the envelope estimator. Applying such an expected theorem is not by itself the contribution. |
| [Asi et al., 2106.09481v2](https://arxiv.org/abs/2106.09481v2), multilevel proximal estimation | The multilevel debiasing idea is prior work. A full stochastic-gradient second-moment bound cannot simply be replaced by central variance at a constrained boundary. The variance-only inner extension here is a supporting component, not an independent novelty claim. |
| [Bonnerjee–Ramdas, 2610.23570v1](https://arxiv.org/abs/2610.23570v1), §§9.5.1 and 10.3, preprint; [Liu et al., ICML 2023](https://proceedings.mlr.press/v202/liu23aa.html) | The inspected quasar module concerns SGD; the momentum module assumes convexity and gives a different rate. Liu et al. use stronger noise assumptions for the relevant concentration guarantees. These tools do not directly provide the constrained biased-MLMC execution bound proved here. |

Additional checks included [Kovalev 2605.15522v2](https://arxiv.org/abs/2605.15522v2), May 26 (expected accuracy), and [Hermant 2512.16533v2](https://arxiv.org/abs/2512.16533v2), January 6, Proposition 14/Corollary 15 (clock-tail versus objective-confidence distinctions). None of these comparisons establishes a lower bound against their algorithms.

The expected-rate composition of constrained Moreau smoothing, a variance-only proximal solver, MLMC, and a biased-gradient acceleration theorem is an obvious baseline. A work cap alone also does not make that composition novel. Markov conversion from expected objective error loses polynomial factors in `1/δ`. Independent repetitions require a reliable way to select an objective-good output; ordinary distance-based boosting needs strong convexity or error-bound geometry absent here. Per-step accurate proximal solves also replace the multilevel average-work benefit by paying the finest required accuracy repeatedly. The proved barrier controls biased noisy acceleration directly and retains the averaged multilevel cost. Standard pieces remain standard; the claim rests on this complete connection and the resulting oracle guarantee.

Quantitatively, the strongest standard expected-rate composition checked in screening has, up to logarithmic factors, `χ+N` cost, where `χ=sqrt(LD²/ε)/γ` and `N=σ²D²/(γ²ε²)`. Converting such an expected-gap guarantee to failure probability `δ` by running it at expected error `εδ` gives

\[
\widetilde O(\delta^{-1/2}\chi+\delta^{-2}N),
\]

whereas the proved bound is `O(log(8/δ) · [1+log(2+LD²/(γ²ε))]² · (1+χ+N))`. Thus confidence dependence improves from polynomial to logarithmic in this direct expected-to-probability reduction, while the objective-accuracy and variance powers are preserved. This is a comparison with a reduction, **not a lower bound** for expected-rate algorithms or a claim that their best possible confidence amplification must pay these factors. Fu–Xu–Wilson and Gbaguidi–Hermant retain the distinct value-oracle and assumption requirements listed above; their bounds cannot be relabeled as the same stochastic-gradient-only oracle model. At fixed confidence, no improvement over the expected baseline's parameter powers is claimed.

One comparison is incomplete: the full [Valdivia Viscarra–Stonyakin OPTIMA 2025 chapter, published April 2026](https://doi.org/10.1007/978-3-032-15791-1_7) was inaccessible. [Alkousa 2607.22551v1](https://arxiv.org/abs/2607.22551v1), §3.3, Theorem 3.5 and reference 36, attributes both deterministic and stochastic switching algorithms to that chapter and reproduces a value-dependent stochastic method with expected `ε⁻²` analysis under bounded stochastic gradients. This is evidence against direct subsumption, not a verified reading of every chapter theorem. Exhaustive priority over its unexamined contents is not asserted.

## Motivation, nonlinear scope, and limitations

A recognized source of nonlinear quasar objectives is monotone single-index regression; see [Foster, Sekhari, Sridharan, NeurIPS 2018, 1810.11059v2](https://arxiv.org/abs/1810.11059v2), §3, Assumption 1 and Appendix C.1, Lemma 5, Eq. (18). For a logistic link `s`, bounded features `‖a‖≤A`, parameters in a radius-`R` ball, and response `y=s(aᵀxstar)+ζ` with conditional mean-zero noise and conditional variance at most `s₀²`, the population squared loss differs from the realizable loss by a constant. On the ball the link derivative is at least `m=1/(4 cosh²(AR/2))`. Bounds `D=2R`, `L=5A²/16`, `γ=min(1,8m)`, and `σ²=A²(1+s₀²)/16` suffice for the normalization `f(x)=E[(s(aᵀx)-y)²]/2`. Features may interact across coordinates, and response noise may be heavy-tailed. No independence of response noise and features is needed beyond the stated conditional moments. This supplies a practical source of the assumptions, not a regression-specific state-of-the-art claim or a separately formalized statistical theorem.

For an explicit nonconvex interacting family in every dimension `d≥2`, take the radius-3 Euclidean ball, `xstar=−2e₁`, and features uniform on `a₁=e₁` and `aᵢ=(e₁+eᵢ)/sqrt(2)` for `2≤i≤d`. Use the conditional response model above and the half squared logistic loss. These features span the space and couple the first coordinate to every other coordinate. At the interior point `x=2e₁`, the feature arguments are `t=2` or `t=sqrt(2)`, while the target arguments are `−t`. The Hessian coefficient multiplying each `aaᵀ` is

\[
\frac{s'(t)}4\left[1-5\tanh^2(t/2)\right]<0.
\]

Hence the Hessian there is negative definite, despite the quasar inequality holding throughout the ball. This is a nonlinear, nonseparable family with interacting coordinates, not a scalar or quadratic proxy. Here `A=1`, so the preceding bounds give dimension-independent `L,γ,D,σ` when the conditional noise variance is fixed. This example is explanatory mathematics; the Lean theorem proves the general class rather than separately formalizing this regression construction.

The formal result is dimension-independent only in its explicit formula: dimension can enter `L,D,σ,γ` and the cost of a vector operation or projection. It counts oracle calls, not runtime, bit complexity, the cost of sampling real holding times, or implementing exact projections. Compactness, known parameter bounds, exact projection, finite dimensionality, ambient differentiability at feasible points, and fresh IID sampling remain restrictions. It does not cover Markov noise, merely relative differentiability, unknown-parameter adaptation, or inexact projection. No bounded full gradient, zero normal gradient at the optimum, quadratic growth, samplewise smoothness, bounded noise, or finite sample-space restriction is added.
