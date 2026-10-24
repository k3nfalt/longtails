# Split robust acceleration under a relative finite-moment oracle

The [Lean result](SplitRobustHeavyTailedAcceleration.lean) concerns smooth convex minimization with an unbiased stochastic gradient whose central moment of order `1 < p ≤ 2` is bounded by `ρ ‖∇f(x)‖^p`. It combines a robust descent direction with a separately clipped mirror direction. For fixed `p` and positive `ρ`, its expected-error oracle complexity is

\[
 O_p\!\left((1+\rho^{1/(p-1)})
       H^{p/(3p-2)}(1+\log H)\right),
 \qquad H=\max\{1,LR^2/\varepsilon\}.
\]

The constants hidden by this notation depend strongly on `p`; the public Lean budget retains them explicitly. This is an upper bound, not an optimality claim. At `ρ=0` the construction uses `130 ceil(128 sqrt(H))` calls. For noisy `p=2` it retains a logarithmic overhead relative to established finite-variance accelerated bounds.

## Problem, information, and output

The [setup](../Setups/HeavyTailedStrongGrowthConvex.lean) assumes a differentiable, globally `L`-smooth convex objective on a separable complete real Hilbert space, a minimizer `xstar`, and `‖x0-xstar‖ ≤ R`. It includes arbitrary finite-dimensional Euclidean objectives. The parameters satisfy `L>0`, `R≥0`, `ρ≥0`, and `ε>0`. The algorithm knows these parameters and `p`, but neither the minimizer nor its objective value nor the true gradient.

For a probability measure `μ`, the fixed oracle map `g(x,ω)` is jointly measurable. At every point it is integrable, has mean `∇f(x)`, and has an integrable central `p`th power satisfying

\[
 \int\|g(x,\omega)-\nabla f(x)\|^p\,d\mu(\omega)
 \le \rho\|\nabla f(x)\|^p.
\]

The public sampling law is an arbitrary probability measure `P` on seed sequences, with the repository's IID structure bundling measurable coordinates, independence, and common marginal `μ`. The proof derives the required finite product laws internally. It does not cover arbitrary history-dependent oracle kernels or dependent sampling. It imposes no raw second moment, symmetric-noise, finite-support, or coordinate-independence assumption. Oracle exactness at a stationary point or when `ρ=0` holds pointwise almost surely; the proof does not assume a uniform null set across query points.

The pure relative moment condition excludes additive residual noise and forces the oracle to be exact almost surely at minimizers. Global smooth convexity and fresh IID sampling are established assumptions, and all are used by this proof: smooth descent controls the pilot step, convexity gives the coupling inequality, and fresh independence gives the conditional estimator bounds. No extension to nonsmooth, nonconvex, additive-noise, or dependent-sampling problems is claimed.

The named [output `lastIterate`](../Algorithms/SplitRobustAcceleration.lean) is the last **planned descent iterate**, and the guarantee is its integrable expected objective error:

\[
 \int [f(\mathrm{lastIterate}(\xi))-f(x_\star)]\,dP(\xi)\le\varepsilon.
\]

The setup describes the problem and oracle access, with no artificial restriction to the constructed method. A concrete nonlinear family is `f(x)=Σ_i log cosh(a_iᵀx)`, with nonorthogonal spanning vectors `a_i`. Its Hessian couples coordinates and is bounded by `Σ_i a_i a_iᵀ`; zero is a minimizer. A random linear compression oracle `g(x,ω)=M(ω)∇f(x)` meets the moment model when `E M=I` and `E‖M-I‖op^p≤ρ`. This gives a mechanism for the assumption, including heavy-tailed multipliers, without claiming that infinite-variance compression is ubiquitous in applications. Neither the bound nor the normalization constants introduce explicit dimension factors; instance parameters such as `L`, `R`, and `ρ` can depend on dimension.

## Algorithm and explicit cost

For positive `ρ`, put

\[
 b=\left\lceil(2^{34}\rho)^{1/(p-1)}\right\rceil,\quad
 k=128+\lceil2\log H\rceil,\quad
 \Lambda=H^{1/(3p-2)},\quad
 V=32\Lambda^{2-p},\quad
 N=\left\lceil128H^{p/(3p-2)}\right\rceil.
\]

At each query point, form `k+2` independent block means, each using `b+1` raw calls. The [estimator](../Algorithms/MultiplicativeRobustEstimator.lean) selects a sum-distance medoid `d` of the first `k+1` means. It clips the fresh final mean to the ball of radius `4Λ‖d‖`, obtaining `v`. No known gradient norm or minimizer radius is used in this estimator.

With `A_t=t(t+1)/(64LV)` and `a_t=(t+1)/(32LV)`, query
`y_t=(A_t x_t+a_t z_t)/(A_t+a_t)` and update

\[
 x_{t+1}=y_t-d_t/L,\qquad z_{t+1}=z_t-a_t v_t.
\]

Both initial states are `x0`. The descent and mirror directions share the pilot and need not be independent of each other. The final raw block is independent of the pilot. For `ρ=0`, use `Λ=1`, `V=32`, `k=128`, `b=0`, and `N=ceil(128 sqrt(H))`.

The public budget is the following single formula, also written explicitly in Lean:

\[
 130\lceil128\sqrt H\rceil+
 2\left\lceil(2^{34}\rho)^{1/(p-1)}\right\rceil
 (130+\lceil2\log H\rceil)
 \left\lceil128H^{p/(3p-2)}\right\rceil.
\]

The planned run uses exactly `(k+2)(b+1)N` raw oracle calls. The algorithm freezes its state after those calls and discards any replies needed to fill the public budget. Every such padding call is counted. The special `ρ=0` branch avoids the heavy-tail exponent but does not make the budget continuous as `ρ` decreases to zero. When `R=0` or the requested accuracy is large, the same formulas remain valid and can spend unnecessary constant calls.

## Mathematical mechanism

The proof first obtains a dimension-free central-moment bound for block means by Hilbert-space symmetrization. A sum-distance medoid has a finite second moment even when individual block means do not: a deterministic pair-product domination bounds its squared error by products of errors of distinct independent blocks. Confidence amplification supplies the small probability of an undersized clipping radius. Consequently, conditionally on each query point,

\[
 E\|d-\nabla f(y)\|^2\le\|\nabla f(y)\|^2/64,\quad
 E\|v\|^2\le V\|\nabla f(y)\|^2,\quad
 \|Ev-\nabla f(y)\|\le\alpha\|\nabla f(y)\|,
 \quad\alpha=\Lambda^{1-p}/16.
\]

No unbiasedness of the medoid or clipped direction is assumed. The energy
`A_t(f(x_t)-f(xstar))+‖z_t-xstar‖²/2` grows in expectation by at most `1+α²/(2V)` per step. The low-error descent direction permits the physical step `1/L`, while only the mirror weight pays `V`. Thus iteration complexity is proportional to `sqrt(VH)`, rather than `V sqrt(H)` for the checked shared-estimator reduction. Balancing the multiplicative bias growth yields the exponent `p/(3p-2)`. The distinction between the two directions, and its effect on the coupling condition, is the claimed new mechanism; relative-bias absorption by itself is not claimed new.

The supporting modules derive the estimator bounds, nonlinear smooth-convex energy inequality, integrability, stochastic recursion, IID execution identity, and tuning. These are not assumptions in the setup.

## Closest comparisons, regimes, and limitations

The relative finite-`p` moment model is explicitly considered in [Lobanov, Dvinskikh, and Gasnikov, arXiv:2609.33415v1](https://arxiv.org/html/2609.33415v1), Appendix F, equation (58). Equations (59)–(60) discuss thinning lower bounds and a conservative acceleration reduction. Their generic affine model also permits additive noise, which this result excludes. Their discussion motivates the pure multiplicative question independently of the present proof.

For the high-accuracy comparison, write `T=LR²/ε≥1`. The strongest checked baseline here is not just that paper's displayed generic bound. Combining relative robust estimation with the mixed-bias/variance accelerated analysis in [Beznosikov et al., arXiv:2305.15938v2, Appendix B.3](https://arxiv.org/html/2305.15938v2), and regularizing at scale `ε/R²`, gives the reconstructed exponent `p/[4(p-1)]`. Regularized robust descent supplies exponent `1`. This is a standard-reduction calculation from their analysis, not a finite-`p` theorem explicitly stated in that paper. To make this reduction explicit, a normalized pilot-clipped common estimator has `α ≍ λ^(1-p)` and `V ≍ λ^(2-p)`, up to constants depending on `p` and logarithmic confidence costs. Appendix B.3, Lemmas 5–6 and the proof of Theorem 6, give the common-estimator scaling, suppressing logarithmic factors (including the regularized strongly convex convergence factor),

\[
 N_{\rm common}\asymp V\sqrt T,\qquad
 (\alpha^2/V)N_{\rm common}\lesssim1
 \quad\Longrightarrow\quad \alpha^2\sqrt T\lesssim1.
\]

Thus choose `λ ≍ T^[1/(4(p-1))]`; then

\[
 V\sqrt T\asymp T^{1/2+(2-p)/(4(p-1))}
   =T^{p/[4(p-1)]}.
\]

Each estimator evaluation costs `O_p((1+ρ^[1/(p-1)]) log T)` raw samples. The regularized objective is `h(x)=f(x)+(μ/2)‖x-x0‖²`, with `μ` proportional to `ε/R²`. Its oracle is obtained by adding the known deterministic vector `μ(x-x0)` to the original reply, so this step grants no new oracle. Relative errors with respect to `∇f` become an affine error model for `∇h`, using `‖∇f(x)‖≤2‖∇h(x)‖+μR`; the regularization error and associated bias/variance floors are retained at the target scale. This is also why the fallback exponent `1` is justified by regularized robust descent, rather than by an unproved unregularized biased-GD rate. This reduction rules out the shared-estimator exponent as a novelty claim.

The comparison exponent is therefore

\[
 \min\{1,p/[4(p-1)]\}.
\]

For each fixed `1<p<2`, the present exponent is strictly smaller: the improvement is `2(p-1)/(3p-2)` for `p≤4/3`, and `p(2-p)/[4(p-1)(3p-2)]` for `p>4/3`. With fixed model parameters and sufficiently small `ε`, this is a polynomial improvement that survives logarithmic overhead. Constants prevent a claim of improvement at every finite accuracy. In particular, acceleration was already available from the standard reduction for `p>4/3`; the result must not be described as the first acceleration throughout the whole finite-moment range.

The thinning benchmark leaves a square-root accuracy exponent, so the remaining exponent gap is `(2-p)/[2(3p-2)]`. Matching the full lower bound remains open. The `p=2` baseline includes [AGNES, NeurIPS 2024](https://arxiv.org/abs/2302.05515); the present pilot logarithm is a loss at that endpoint.

[Clipped accelerated methods under weak-`Lp` affine tails, arXiv:2610.28107v1](https://arxiv.org/html/2610.28107v1), Theorem 5.2 and Table 1, cover a broader noise model and high-probability accuracy. Those distinctions prohibit presenting the present expected-error guarantee as a universal replacement. [Biased AccSGD, arXiv:2310.02371v2](https://arxiv.org/html/2310.02371v2), Theorem 3.1, uses an additive bias bound and a common estimator; its bias terms do not directly imply the split relative-moment rate.

A particularly relevant conceptual prior is [Mishkin, Pilanci, and Schmidt, arXiv:2404.02378v2](https://arxiv.org/html/2404.02378v2). Its abstract and Section 9 retract the original claimed fully stochastic square-root strong-growth improvement; equation (5) uses a true-gradient dual direction. The surviving semistochastic result does not supply the present noisy, biased mirror direction. The retracted claim is not used as a valid baseline. [Bollapragada and Gupta, COAP 2026](https://doi.org/10.1007/s10589-026-00788-y), Theorem 3.8(2), instead uses a common estimator and summability of a weighted relative-error sequence.

Literature checks used the UTC date October 24, 2026, surveyed publicly available ICML 2025–2026, ICLR 2025–2026, and NeurIPS 2025–2026 material (with NeurIPS 2024 among the foundational comparisons) and approximately two years of arXiv activity, and followed stronger older analyses and corrections. This was not an exhaustive theorem database search. One access limitation remains: the full text of the accepted NeurIPS 2026 paper [Median-of-Means under Structured Heavy-Tailed Noise](https://neurips.cc/virtual/2026/poster/148757), OpenReview `vGEUrQdO7l`, could not be retrieved through the attempted proceedings, OpenReview, author, and arXiv routes. Its abstract describes a different structured-noise model, but an abstract alone does not rule out a relevant theorem or reduction. The novelty assessment must retain this limitation rather than treating inaccessible full text as evidence of absence.
