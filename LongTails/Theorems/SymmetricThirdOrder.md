# Stochastic second-order optimization under third-order smoothness

[The Lean result](SymmetricThirdOrder.lean) proves a constant-confidence oracle-complexity guarantee for the [stochastic third-derivative convex setup](../Setups/StochasticThirdDerivativeConvex.lean). The [algorithm](../Algorithms/SymmetricThirdOrder.lean) uses stochastic gradients and Hessians, exploiting Lipschitz continuity of the third derivative without querying that derivative.

## Statement and oracle model

Let $f:\mathbb R^d\to\mathbb R$ be globally convex and $C^3$, with

$$
\|D^2\nabla f(x)-D^2\nabla f(y)\|\le L_3\|x-y\|.
$$

There is a global minimizer $x_\star$ with $\|x_0-x_\star\|\le R$ and $f(x_0)-f(x_\star)\le\Delta$. The algorithm knows positive upper bounds $L_3,R,\Delta$, the requested accuracy $\epsilon>0$, and nonnegative noise bounds $\sigma_g,\sigma_h$. These are upper bounds; zero noise and objectives with zero third-derivative Lipschitz seminorm are included.

One oracle call at $x$ returns the pair $(g(x,\omega),H(x,\omega))$. Both maps are jointly measurable, with

$$
\int g(x,\omega)\,dp(\omega)=\nabla f(x),\qquad
\int\|g(x,\omega)-\nabla f(x)\|^2dp(\omega)\le\sigma_g^2,
$$
$$
\int\|H(x,\omega)-\nabla^2f(x)\|^2dp(\omega)\le\sigma_h^2.
$$

The setup explicitly requires the integrability in these formulas. Hessian error is measured in operator norm. Hessians need not be unbiased, symmetric, or positive semidefinite. The two reply components may be correlated. Calls use fresh IID samples under an abstract probability law $P$; the setup uses the repository's shared IID structure and does not require a prescribed product probability space, a finite sample space, sample-function access, or evaluation at several points with the same sample. No objective values are queried.

Write

$$
G=\frac{\sigma_g^2R^2}{\epsilon^2},\quad H=\frac{\sigma_hR^2}{\epsilon},\quad
K=\frac{L_3R^4}{\epsilon},\quad Z=2+\frac\Delta\epsilon+H+K.
$$

The theorem constructs an algorithm whose returned point $\widehat x$ is measurable, lies in $\overline B(x_0,R)$ on every transcript, and satisfies

$$
P\{f(\widehat x)-f(x_\star)\le\epsilon\}\ge\frac23
$$

after at most the explicitly formalized budget

$$
\left\lceil2^{100}(1+G+\sqrt H+K^{1/5})(1+\log Z)^4\right\rceil
$$

joint gradient–Hessian calls. This is a probability guarantee, not an expected-error bound. The output is the accelerated outer point after the prescribed number of rounds; its weight and point freeze once the stopping threshold is reached. It is not the last inner Newton point or an unspecified best iterate.

## Algorithm and proof mechanism

The construction confines outer states and model minimizations to the known ball. Reflected endpoint queries can leave this ball, which is why regularity and oracle assumptions are global. Each round robustly estimates the center Hessian, symmetrizes it, and adds a known positive shift. A finite sequence of Bregman proximal steps approximately minimizes a symmetric surrogate built from the odd part of $f(c+s)$, a center quadratic, and a quartic regularizer. Its gradient is evaluated through paired stochastic gradients. The surrogate's function values are used only in the analysis.

The symmetric-surrogate idea and its third-order Taylor cancellation are established tools. The technical contribution is a stochastic implementation that supplies the accelerated method's Euclidean residual certificate at additive statistical cost. Relative conditioning of a Bregman model alone does not supply such a certificate when quadratic curvature is arbitrarily large. The construction therefore performs a constrained noisy Newton cleanup, using endpoint Hessian pilots, PSD clipping, and a normal-cone correction. The proved certificate has residual at most $(3/16)\lambda r+35a$, where $a$ is the gradient-pilot tolerance, $r$ is the outer displacement, and $\lambda=\delta+8L_3r^2$. Its cleanup condition is $262144L_3a^2\le\delta^3$.

A fresh mean-gradient batch is queried only after the cleanup point and normal have been selected. This preserves conditional unbiasedness for the momentum correction. The proof kills the complete energy, including accumulated dissipation, on pilot failure; the survival flag depends only on samples preceding that fresh batch. It then integrates over the fresh block using the IID law. It never conditions the correction on future good events.

For $S=1+\sqrt H+K^{1/5}$, the algorithm uses
$T=\lceil2^{24}S(1+\log Z)^2\rceil$,
$\delta=(\epsilon/R^2)(T^2/2^{24}+288H)$,
$a^2=\epsilon\delta/(2^{24}T)$, and stopping weight $X=6R^2/\epsilon$.
These choices jointly satisfy the cleanup condition, control stochastic energy, and yield total mean/pilot batching cost proportional to $T+G$, up to logarithms. The inner round count, robust repetition count, batch size, and clamped geometric grid are explicit in `tunedConfig`; every rounding and positivity condition is proved in [the budget module](../Proofs/SymmetricThirdOrderBudget.lean).

A pathwise grid/weight argument bounds rounds before stopping using accumulated dissipation. The initial round is counted separately; the proof does not assume that a full-horizon bound applies unchanged to every prefix. Markov's inequality for the killed energy and a union bound for pilot failures each consume probability at most $1/6$.

For $J$ inner steps, $k$ robust groups and batch size $m$, each actual round uses exactly
$k(3+2m(J+1))+m$ calls. This includes the center Hessian, both gradient endpoints for every inner step and cleanup, both cleanup Hessians, and fresh correction. Frozen rounds still execute these calls. The `execute` connection also counts dummy calls used to pad the completed query plan to the public budget. No batching, endpoint, or discarded reply component is free.

## Closest results and the remaining gap

The primary comparisons below use the versions checked on 2026-11-04. The 2026 arXiv papers cited here are treated as preprints; no conference acceptance is inferred from their arXiv availability.

* Chen et al., [Optimal Convex Optimization with Inexact Second-Order Oracles, v3](https://arxiv.org/abs/2607.24520v3), Assumptions 2.1–2.3, Theorem 3.1 and Corollary 4.1, already obtain the deterministic terms $\widetilde O(\sqrt H+K^{1/5})$ with exact gradients and uniformly bounded Hessian errors. Those exponents and the deterministic third-order acceleration are not new here. The present guarantee replaces exact gradients by finite-variance unbiased samples and uniform Hessian error by a pointwise second-moment bound, retaining an additive $G$ term. Its confidence guarantee, explicit initialization bound, and logarithms differ from that deterministic theorem.
* Agafonov et al., [Matching the Lower Bounds: Stochastic Contracting Cubic Newton and Its Optimal Acceleration, v2](https://arxiv.org/abs/2610.11693v2), Assumptions 3.1, 3.3–3.5 and Theorem 5.1, obtain expected error of order $\sigma_gD/\sqrt T+\sigma_hD^2/T^2+L_2D^3/T^{7/2}$. Their Hessian samples are PSD and symmetric and their objective has Lipschitz Hessian on the domain. Expected error gives constant-confidence accuracy by Markov with constant rescaling. The present result retains the statistical terms while exploiting third-order smoothness to obtain $K^{1/5}$, and handles general matrix replies. PSD processing alone is a routine reduction and is not the claimed advance.
* Nesterov, [Superfast Second-Order Methods for Unconstrained Convex Optimization](https://doi.org/10.1007/s10957-021-01930-y), in particular the symmetric approximations around equations (48) and (50), supplies foundational second-order implementation ideas. Neither symmetric differences nor replacing exact derivatives by pilots alone establishes the new stochastic complexity.
* [Near-Optimal Second-Order Convex Finite-Sum Optimization under Individual Smoothness, v1](https://arxiv.org/abs/2610.42040v1), uses an individually convex finite-sum model and Taylor-corrected lazy Newton machinery. Its component access and dependence structure are different from fresh stochastic point queries here. Its restricted periodic uniform-index lower bound does not establish an unrestricted minimax claim for this setup.

The [sample-average approximation preprint, v1](https://arxiv.org/abs/2609.21878v1), uses empirical/sample-function access and statistical similarity to obtain communication guarantees. Those assumptions and that cost model do not provide the fresh marginal-oracle total-call guarantee here: sample functions cannot be retained and queried at further points under this setup.

A direct uniform-accuracy gradient simulation illustrates the missing reduction: making each of $T$ calls accurate to order $\epsilon/R$ requires order $G$ samples per call under finite variance, giving a multiplicative $TG$ cost, up to robust logarithms. The adaptive tolerance, regularization, cleanup, and fresh correction above instead give $T+G$. This calculation does not claim that every conceivable reduction must pay $TG$; the novelty claim rests on comparison with the applicable proved algorithms, not on a lower bound for batching.

On instances admitting both regularity bounds, the deterministic polynomial term improves over the cubic baseline when
$(L_3R^4/\epsilon)^{1/5}<(L_2R^3/\epsilon)^{2/7}$, equivalently $L_3^7\epsilon^3<L_2^{10}R^2$, before logarithms and constants. A total-complexity gain also requires that the common noise terms not dominate. There is no universal comparison between the two objective classes: global Lipschitz third derivative does not imply global Lipschitz Hessian. No new minimax lower bound or optimal logarithmic factor is proved.

## Naturalness, scope, and limitations

The smoothness and convexity assumptions are those used in the third-order branch of AINE; the gradient moment conditions and Hessian second-moment model follow the stochastic cubic literature above. Joint measurability and integrability make the adaptive probability statements explicit. The radius and gap are initialization upper bounds, not assumptions about the algorithm's eventual convergence. No artificial `allowedAlgorithm` restriction is imposed.

A nonlinear interacting family is
$f(x)=\sum_i w_i(a_i^Tx-b_i)^4+\tfrac12x^TQx+c^Tx$,
with $w_i\ge0$, $Q\succeq0$, nonorthogonal $a_i$, and parameters ensuring a minimizer. Its third derivative is globally Lipschitz with an upper bound $24\sum_iw_i\|a_i\|^4$; mixed-coordinate interactions are unrestricted. Positive-definite $Q$ ensures existence, but strong convexity is not assumed by the theorem. Hessian and third-derivative magnitudes may be unbounded. Additive finite-second-moment vector and matrix measurement errors realize the oracle, with a mean-zero vector error and a possibly biased, nonsymmetric matrix error. These examples explain the model rather than restrict the formal result to polynomials or additive noise.

The result covers arbitrary finite dimension and general nonlinear objectives. Dimension can enter $L_3,\sigma_g,\sigma_h,R,\Delta$; there is no additional explicit dimension factor in the oracle count. A full matrix reply is one oracle call. Arithmetic, storage, spectral processing, and exact solution of known-data convex subproblems are outside this cost model. The proof does not supply a competitive arithmetic bound or practical constants: $2^{100}$ is deliberately conservative. Confidence is fixed at $2/3$, all tuning bounds are known, and no adaptivity to unknown smoothness/noise levels is claimed. The contribution concerns second-order oracle access and third-order regularity together; it is not a third-derivative-query algorithm.
