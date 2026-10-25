# Second-order stationarity from directional heavy-tailed Hessian-vector products

[The theorem](DirectionalHeavyTailedSecondOrder.lean) constructs an algorithm for general smooth nonconvex objectives in arbitrary positive finite dimension. It returns an `(ε, √(ρε))` second-order stationary point with probability at least `2/3`, using fresh stochastic gradients and Hessian-vector products (HVPs) with bounded central `p`-moments, `1 < p ≤ 2`. The Hessian assumption controls each direction, rather than the random matrix's operator norm. For fixed positive smoothness, gap, and noise parameters and fixed `p`, the oracle complexity is `Õ_p(ε^{-(1+p/(p−1))})`, with only polylogarithmic dimension dependence. The principal contribution is extending negative-curvature search, and hence second-order stationarity, to directional infinite-variance noise. The first-order accuracy exponent itself is already known under other second-order oracle assumptions.

The [setup](../Setups/HeavyTailedHessianVector.lean) specifies the problem and oracle access without restricting admissible algorithms to this construction. The [algorithm](../Algorithms/HeavyTailedSosp.lean) and its [explicit tuning](../Algorithms/HeavyTailedSospTuned.lean) implement the witness. No objective values, sample reuse, full Hessian matrices, eigenvectors, minimizers, or lower-bound values are available to the algorithm.

The objective `f : ℝᵈ → ℝ` has an everywhere differentiable gradient, an `L`-Lipschitz gradient, and a `ρ`-Lipschitz Hessian. There is a lower bound `m` with `f(x₀)−m ≤ Δ`. Public parameters satisfy `d ≥ 1`, `L,ρ,ε > 0`, `Δ,σg,σh ≥ 0`, and `1 < p ≤ 2`. A positive upper bound may be supplied for an actual zero smoothness modulus. These are the usual lower-bounded, Hessian-Lipschitz nonconvex assumptions; no convexity, PL inequality, strict-saddle condition, interpolation, bounded gradient, or eigengap is imposed.

At a point `x`, one query requests either `g(x,ξ)` or `H(x,ξ)v`. The stochastic field `H(x,ξ)` is linear in `v`; it need not be symmetric or positive semidefinite for individual samples. The assumptions are

\[
\mathbb E g(x,\xi)=\nabla f(x),\qquad
\mathbb E\|g(x,\xi)-\nabla f(x)\|^p\le\sigma_g^p,
\]
\[
\mathbb E H(x,\xi)v=\nabla^2 f(x)v,\qquad
\mathbb E\|(H(x,\xi)-\nabla^2 f(x))v\|^p
 \le\sigma_h^p\|v\|^p\quad\text{for every }x,v.
\]

Joint measurability and the requisite Bochner integrability are explicit. The oracle has an abstract probability law and coordinate samples satisfying the repository's IID structure. The proof derives a product representation internally. Algorithmic path positions, Rademacher starts, iterate selections, escape signs, and final cycle selection are independent auxiliary randomness. A nonlinear-in-direction response oracle, a dependent sample stream, or merely marginal unbiasedness without the stated joint model is not covered.

For a compact display of the exact budget, define

\[
r=\frac p{p-1},\quad \Gamma=\sqrt{\rho\varepsilon},\quad S=L+\Gamma,
\quad A=1+\frac{\sigma_g}{\varepsilon},\quad
Z=\frac{\sigma_h}{S}+\frac{\rho\varepsilon}{S^2},
\]
\[
U=1+\frac{\Delta S}{\varepsilon^2},\quad
D=\log(2+d),\quad J=\log\!\left(2+\frac{S^2}{\rho\varepsilon}\right).
\]

The main theorem's `budget` expands these quantities in one line and allows

\[
C=\left\lceil 2^{64r^2}\left\{
A^r+U\left[1+A^{r-1}Z+Z^r
 +JD\frac S\Gamma
 +JD^r\left(\frac{\sigma_h}{\Gamma}\right)^r
 +J^2\left(1+\left(\frac{\sigma_h}{\Gamma}\right)^r\right)
\right]\right\}\right\rceil
\]

oracle calls. Each gradient or HVP counts as one call. This is a query bound, not an arithmetic-time bound or a practical numerical prescription. The factor `2^{64r²}` is explicit and conservative; it diverges as `p ↓ 1`. Constants are not uniform in `p`. Initial estimation, short epochs, deterministic curvature search, validation, path variation, and rounding are all retained. In particular, `σh=0` does not erase `ρε/S²`: random path positions still introduce transport variation for nonlinear Hessians.

For fixed positive `L,ρ,Δ,σg,σh`, the leading estimator term is `ε^{-(r+1)}`. Curvature work is at most `Õ_p(ε^{-(2+r/2)})`; since `r ≥ 2`, it does not increase the leading accuracy exponent. At `p=2` this gives `Õ(ε⁻³)`; for `1<p<2` it covers infinite variance. The displayed formula, rather than this asymptotic summary, governs zero-noise, zero-gap, large-noise, and varying-dimension regimes. It is not a claim of superiority over the best deterministic or low-noise algorithms in every regime, nor a bound for independently prescribed gradient and curvature tolerances.

The output satisfies

\[
\mathbb P\!\left(\|\nabla f(\widehat x)\|\le\varepsilon,
\quad v^\top\nabla^2 f(\widehat x)v\ge-\Gamma\|v\|^2
\text{ for all }v\right)\ge\frac23.
\]

The algorithm selects a cycle uniformly in advance and stores that cycle's start point when reached. It returns this stored point at the fixed query cap; an unreached selection has the defined initialized fallback. The guarantee is for this random cycle-start output, not a last iterate or an objective minimizer. Completed executions are padded by the framework's remaining queries, and all of those calls lie within `C`.

The construction uses internal accuracy `ε₀=ε/25`, curvature threshold `γ=√(ρε₀)`, normalized-gradient step `h=ε₀/[100(L+γ)]`, escape length `s=γ/ρ`, and `T=max{1,⌈100Δ/(hε₀)⌉}` cycles. Each cycle performs a normalized step, then runs all curvature trials and validations at its endpoint. A validated negative direction triggers a fresh random-sign step of length `s`, transported in `⌈s/h⌉` pieces. The gradient estimator periodically resets to a fresh batch mean. Between resets it estimates the gradient difference along a segment `v` by fresh samples of `H(x+Uv,ξ)v`, with `U` uniform on `(0,1]`. The fundamental theorem of calculus makes this transport unbiased; its central moment is bounded by `(ρ‖v‖²)^p+6σh^p‖v‖^p`.

The reset and transport batches are explicit. Writing `e=ε₀/10000`, `Kp=144r`, `τ=7(σh+ρh)`, `a=1+Kpσg/e`, and `z=Kpτh/e`, they are `B=⌈a^r⌉`, `q=max{1,⌊Ta/(a+Tz)⌋}`, and `b=1+⌈q^{r−1}z^r⌉`. The proof bounds estimator errors on the actual virtual-time trajectory, including transport after accepted escape steps. The total virtual work is controlled in expectation, rather than treating the maximum possible number of escape segments as typical. This yields reset/transport cost proportional to `a^r+T(1+a^{r−1}z+z^r)`.

At a fixed point, curvature search applies a normalized stochastic product to the shifted mean `(L+γ)I−∇²f(x)`, whose spectrum lies in `[γ,2L+γ]`. It uses a Rademacher start and returns a uniformly selected normalized iterate. With `c=4^{-r}/16` and `D₀=4[log(2√(2d))+2]`, the step is

\[
\eta=\left[2L+\gamma+
 \left(\frac{256D_0\sigma_h^p}{c\gamma}\right)^{1/(p-1)}\right]^{-1},
\qquad t=\left\lceil\frac{2D_0}{\eta\gamma}\right\rceil.
\]

If curvature is at most `−4γ`, one trial produces curvature at most `−3γ` with probability at least `4^{-r}/64`. Independent repetitions and fresh median-of-means Rayleigh validation amplify this guarantee. All trials run, even after a candidate is accepted. Their exact cost is `R(t+nm)` HVP calls, including every validation group and sample. The tuning file supplies `R,n,m` and handles zero noise without dividing by it.

The nonroutine spectral step uses independence to amplify the mean of an unnormalized linear product, a directional `p`-moment bound on its norm, and random-sign anti-concentration conditional on that product. A centered log-increment estimate with a `p`-order remainder converts growth into an average Rayleigh deficit. A uniformly sampled iterate then has the required energy with constant probability depending on `p`. Individual sample matrices need neither common eigenvectors nor symmetry. The fourth moment used for the random signs is not a fourth-moment assumption on oracle noise. Zero products are handled by a defined unit-vector fallback, and the product coupling is used only on the appropriate nonzero event.

The outer proof charges accepted escapes against descent and uses separate bounds for false acceptance and missed negative curvature. Under the explicit tuning, the completed trajectory has average marked gradient norm at most `ε/500`, and average accepted-step count at most `h/(5s)`. Expected unpadded work is at most

\[
W=(2T/q+1)B+2Tb+TR(t+nm).
\]

The public budget is proved to dominate `10W`. Cap failure is at most `1/10`; gradient failure is at most `1/500`; curvature failure is at most `21/100`. Their sum is `39/125<1/3`. The proof derives trajectory integrability and completion, rather than assuming descent, error bounds, or successful stopping. [Configured execution](../Proofs/HeavyTailedSospConfigured.lean) connects these facts to `Template.execute` and the setup's actual probability law. [Budget assembly](../Proofs/HeavyTailedSospBudget.lean) connects the simplified public formula to the complete call ledger.

The closest comparisons are:

| Primary result | Applicable guarantee and restriction | Difference here |
| --- | --- | --- |
| Arjevani et al., [COLT 2020, Theorem 5 and Algorithm 4](https://proceedings.mlr.press/v125/arjevani20a/arjevani20a.pdf) | Fresh-HVP second-order stationarity with finite-variance gradients and bounded Hessian error; the paper also studies a full-matrix variant. | Retains the established Hessian-Lipschitz objective class and random-path/escape framework, while allowing only directional `p`-moments, including infinite variance. The `p=2` accuracy exponent is not new. |
| Sadiev, Richtárik, Fatkhullin, [NeurIPS 2025](https://papers.nips.cc/paper_files/paper/2025/hash/be7b70477c8fca697f14b1dbb1c086d1-Abstract-Conference.html), [arXiv 2510.10690 v1, Theorem 4 and footnote 1](https://arxiv.org/html/2510.10690v1) | Heavy-tailed second-order information yields first-order stationarity with exponent `r+1`; operator-norm Hessian moments are assumed. Second-order stationarity is explicitly left for future work. | Adds the curvature criterion with the same leading fixed-parameter accuracy exponent, under directional HVP moments. This is an accuracy-criterion and oracle-assumption extension, not an improved FOSP exponent. |
| Fradin et al., [AISTATS 2026, PMLR 300](https://proceedings.mlr.press/v300/fradin26a.html), arXiv 2512.18713 v2, Sections 3–4 | First-order stationarity with potentially distinct gradient/Hessian tail exponents; upper and lower bounds use the paper's operator-moment oracle model. | The present theorem treats a common exponent and second-order stationarity. It does not subsume their mixed-exponent result or establish unrestricted minimax optimality. |
| Gu et al., [arXiv 2609.26508 v1, Model 1, Theorem 4 and Corollary 1](https://arxiv.org/html/2609.26508v1) | Gap-free energy PCA for symmetric samples with directional second moments; last-iterate accuracy and independent holdout amplification. This is a preprint, without verified conference acceptance. | The new spectral proof covers directional `p<2` moments and potentially nonsymmetric samples, but uses a random iterate. At finite variance, known energy-PCA machinery is a strong baseline, not a source of novelty by itself. |
| Garber, [Operations Research Letters 63 (2025), Theorem 3](https://doi.org/10.1016/j.orl.2025.107356) | Log-product-norm comparison gives Oja regret for bounded symmetric samples sharing a comparator eigenvector. | The log-growth potential is prior work. The new ingredient is making energy extraction work with independent, noncommuting, infinite-variance directional samples without a common sample eigenvector. |

The usual reductions do not directly establish the claimed result. Finite batching of `p<2` samples need not produce a finite second moment. Clipping the returned HVP vector direction by direction changes its mean and generally destroys the common linear sample operator used by the product argument; applying an unbiased finite-variance PCA theorem to those clipped responses is unjustified. Full-matrix clipping requires information absent from a single fresh-HVP call. Reconstructing or estimating a matrix has to charge its directional queries and control the resulting dimension dependence. These observations identify missing hypotheses in standard compositions, not impossibility results for all alternative robust algorithms. In particular, no claim is made that every matrix-based method must lose a polynomial dimension factor.

A nontrivial covered objective family is

\[
f(x)=\frac\lambda2\|x\|^2+\sum_{j=1}^m\alpha_j(1-\cos(a_j^\top x)),
\]

with nonorthogonal `a_j`, positive `α_j`, and sufficiently small positive `λ`. It has interacting coordinates, can be nonconvex, and has global bounds `L≤λ+Σα_j‖a_j‖²` and `ρ≤Σα_j‖a_j‖³`. This is illustrative, not a restriction in the setup.

A compatible stochastic-loss mechanism illustrates why directional moments matter. Take an independent uniform unit vector `u`, uniform phase `θ`, and centered scalar `Z₀` with finite `p`-moment and, when `p<2`, potentially infinite variance. Set `a=√d Z₀`, `ω=1+|a|`, and add `(a/ω²)cos(ωuᵀx+θ)` to `f`. Its gradient noise is bounded by one. Its Hessian noise is `−a cos(ωuᵀx+θ)uuᵀ`, and `E|⟨u,v⟩|^p≤d^{−p/2}‖v‖^p` gives a dimension-independent directional moment bound. Its operator-norm `p`-moment can scale as `d^{p/2}`. The field is jointly measurable and unbiased by the independent phase. These examples justify the model's usefulness; the formal theorem applies to every oracle satisfying the specification, not only stochastic losses of this form.

The literature assessment covered official ICML 2025–2026, ICLR 2025–2026, NeurIPS 2025–2026 public listings and approximately October 2024–October 2026 arXiv submissions and revisions, with independent Researcher and Reviewer searches and follow-up checks through 25 October 2026 UTC. Key checked versions include 2510.10690 v1 (12 October 2025), 2512.18713 v2 (31 March 2026), and 2609.26508 v1 (22 September 2026). Older Oja, streaming-PCA, and stochastic second-order results were followed rather than excluded by date. The NeurIPS 2026 official Downloads listing was accessible at neurips.cc; its dev.neurips.cc route returned HTTP 410. A NeurIPS 2025 virtual-page route was robot-blocked, so the proceedings route was used. This was a targeted survey, not an exhaustive reading of either conference edition. Garber's publisher route returned access errors on direct opens; indexed primary text exposed the relevant theorem and discussion, but unavailable typesetting remains a literature-access limitation. No duplicate directional infinite-variance HVP energy guarantee was found in this scoped search; this is not proof that no inaccessible or unpublished duplicate exists.

The result does not assert adaptivity to unknown `p` or noise/smoothness parameters, arbitrary-confidence optimality, last-iterate convergence, optimal deterministic complexity, or a matching lower bound for all algorithms. Formal verification establishes the stated theorem, not its research significance. The substantive claim is the dimension-logarithmic second-order guarantee under directional heavy tails, supported by the new spectral argument and its complete integration with adaptive oracle execution.
