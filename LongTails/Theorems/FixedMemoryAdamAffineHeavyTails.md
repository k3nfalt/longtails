# Fixed-memory Adam with affine heavy-tailed noise

[The Lean theorem](FixedMemoryAdamAffineHeavyTails.lean) proves an expected ordinary-stationarity guarantee for canonical coordinatewise Adam with arithmetic minibatches, bias correction, zero initial moments, and fixed memories `(0.9, 0.999)`. The [specification](../Setups/AffineHeavyTailedAdam.lean) and [algorithm and output](../Algorithms/AffineHeavyTailedAdam.lean) make the oracle, update family, returned iterate, and oracle cost explicit.

## Problem and guarantee

Let `f : R^d → R` be differentiable, with `f(x0) − f(x) ≤ Δ` for every `x`. Assume the anchored generalized-smoothness condition

\[
\|\nabla f(y)-\nabla f(x)\|_1
\le (L_0+L_1\|\nabla f(x)\|_1)\|y-x\|_\infty,
\qquad L_1\|y-x\|_\infty\le1.
\]

Here `L0,L1 ≥ 0`, `L0+L1 > 0`, `Δ ≥ 0`, and the target `ε > 0`. Convexity, bounded gradients, bounded iterates, and samplewise smoothness are not assumed. The geometry is explicit: these constants cannot be identified with Euclidean smoothness constants without accounting for dimension.

The jointly measurable oracle uses fresh IID samples from an abstract probability law. For each fixed query `x` it is integrable and unbiased, and, for every coordinate,

\[
\mathbb E|g_i(x,\xi)-\nabla_i f(x)|^p
\le \sigma_{0,i}^p+\sigma_1^p|\nabla_i f(x)|^p,
\qquad 1<p\le2.
\]

The corresponding powers are integrable. No symmetry, tail density, independence between coordinates, or finite second moment is required when `p<2`. The scalar `σ1` can be the maximum of heterogeneous multiplicative coordinate scales. This is an established affine moment model, not a proposed new tail assumption.

Write `s0 = Σ_i σ0,i` and `q = p/(p−1)`. Use

\[
\eta=\frac{\varepsilon}{2^{29}(L_0+L_1\varepsilon)},\qquad
\delta=\frac{\varepsilon}{8(d+1)},\qquad
B=1+\left\lceil[2^{17}(\sigma_1+s_0/\varepsilon)]^q\right\rceil,
\]
\[
T=1+\left\lceil\frac{2^{32}\Delta(L_0+L_1\varepsilon)}{\varepsilon^2}\right\rceil.
\]

At each of `T` updates, average `B` oracle replies at the current point, apply standard Adam to that average, and use the denominator `sqrt(vhat)+δ`. Return `xI`, where `I` is independently uniform on `0,…,T−1`. All parameters used for tuning are public setup parameters; the algorithm does not know the objective, minimizer, or oracle distribution. The specification's `allowedAlgorithm` enforces this Adam update and output family while leaving tuning choices free.

The result is

\[
\mathbb E\|\nabla f(x_I)\|_1\le\varepsilon
\]

with exactly `BT` oracle calls, including the final update. The Lean statement uses explicit integrals against the product of the algorithm's uniform seed law and the supplied IID stream law; product sampling is derived internally from IID rather than prescribed to the user. The displayed public budget is the single explicit product `BT`, with the powers of two evaluated. The `+1` terms cover zero noise and zero initial gap.

Up to numerical constants, the oracle bound is

\[
O\!\left(
[1+\Delta(L_0/\varepsilon^2+L_1/\varepsilon)]
[1+(\sigma_1+s_0/\varepsilon)^{p/(p-1)}]
\right).
\]

For globally smooth bounded additive `p`-moment noise this matches the standard heavy-tail accuracy exponent `2+p/(p−1)`. This is not a claim of minimax optimal dependence on all geometry, dimension, curvature, or affine-noise parameters. In a regime `L1 ε ≥ L0`, the displayed deterministic curvature factor is governed by `Δ L1/ε`; no matching lower bound for that factor is asserted. The explicit numerical constants are conservative and are not practical tuning recommendations.

## Mathematical mechanism

The new guarantee rests on a pathwise first-absolute-error stability analysis of Adam's squared-gradient history. A finite expectation of the squared-gradient accumulator `v_t` is never used; that expectation can be infinite. A standard algebraic invariant gives `m_t² ≤ 64 v_t` coordinatewise; with bias correction this bounds each normalized update by `80`.

Let `g_t` denote the true gradient and `ζ_t` the minibatch error. Track the numerator residual and the **normalizer residual**

\[
E_t=|\widehat m_t-g_{t-1}|,\qquad
R_t=|\sqrt{\widehat v_t}-|g_{t-1}||.
\]

After initialization, the effective bias-corrected memory is at most its fixed memory parameter. A two-dimensional reverse triangle inequality gives

\[
E_{t+1}\le .9 E_t+.9|g_t-g_{t-1}|+|\zeta_t|,
\quad
R_{t+1}\le r R_t+r|g_t-g_{t-1}|+|\zeta_t|,
\quad r=1999/2000>\sqrt{.999}.
\]

The first update has both residuals bounded by the first absolute error. The scalar alignment inequality proved in [AffineAdamHistory](../Proofs/AffineAdamHistory.lean) converts these residuals into descent in the ordinary gradient norm. Summing their contracting recurrences and controlling gradient transport by generalized smoothness yields

\[
\sum_{t<T}\|g_t\|_1
\le \Delta/\eta+4096\sum_{t<T}\|\zeta_t\|_1
 +2^{26}\eta\sum_{t<T}(L_0+L_1\|g_t\|_1)+Td\delta.
\]

Scalar IID moment bounds give `E||ζt||1 ≤ 4 B^{−(p−1)/p}(s0+σ1 E||gt||1)`. Fresh-block independence at the adaptive query and integrability are proved before integrating descent. Finite-time gradient bounds follow from the bounded moves and local smoothness; bounded iterates or gradients are not added as assumptions. The affine terms are then absorbed using the displayed tuning. The moment inequality and batching concentration are established ingredients; the contribution is their use through an Adam stability argument that survives infinite-variance squared accumulators.

## Closest results and the remaining gap

The literature comparison was checked through 25 October 2026 UTC, including primary statements, relevant proof steps, and revised preprints.

- [Yu et al., *Open Problem: Is AdamW Effective Under Heavy-Tailed Noise?*, arXiv:2606.23676v1, 22 June 2026](https://arxiv.org/html/2606.23676v1), Sections 2–3 and Proposition 2, motivates ordinary `l1` stationarity under affine heavy tails and generalized coordinate curvature. Its positive benchmark uses a weighted stationarity measure. The present result concerns the zero-weight-decay Adam case, with a batch size growing with accuracy. It does **not** resolve their requested rate for arbitrary fixed batch sizes, nor their nonzero-weight-decay question. Their coordinate generalized-gradient condition implies the anchored norm condition with summed base curvature and maximal growth curvature; the formulations are not literally identical.
- [Li, Dong and Lin, *On the Convergence Rate of AdamW Measured by l1 Norm*, arXiv:2505.11840v4, 27 September 2026](https://arxiv.org/html/2505.11840v4), Theorem 1, Corollary 1, and the normalizer estimates in the proof, supplies a strong finite-variance baseline. The conference version was NeurIPS 2025; v4 is a later revision. Its finite-variance normalizer/momentum controls cannot be applied to arbitrary finite arithmetic batches of infinite-variance noise. We replace that step with first-absolute residual transport and cover affine heavy tails and generalized curvature. This is a scope extension with explicit batching and damping tradeoffs, not a uniform rate improvement over its finite-variance guarantee.
- [Zaheer et al., *Adaptive Methods for Nonconvex Optimization*, NeurIPS 2018](https://proceedings.neurips.cc/paper/2018/file/90365351ccc7437a1309dc64e4db32a3-Paper.pdf), Theorem 1 and Corollaries 2–3, already establishes the value of growing arithmetic minibatches for Adam-type analysis. Its stated analysis uses samplewise smoothness, bounded coordinate stochastic gradients, zero first momentum, and a second-memory/damping/bounded-gradient relation. Batching itself is therefore not new here. Unbounded asymmetric infinite-variance samples and accuracy-vanishing damping with fixed default memories fall outside those hypotheses.
- [Pang, *The Convergence Behavior of Adam under Heavy-Tailed Noise*, arXiv:2607.27383v2, 2 August 2026](https://arxiv.org/html/2607.27383v2), accepted at [UAI 2026](https://proceedings.mlr.press/v337/pang26a.html), studies vector-form Adam in a randomized online-to-nonconvex conversion. The plain learner guarantee uses `p>4/3`, bounded true gradients, random step multipliers, and relaxed `(ρ,ε)` stationarity; output clipping using a known radius gives its stronger all-`p` result. Those rates and accuracy criteria are not directly comparable to an ordinary gradient norm. Our coordinatewise, unmodified arithmetic-batch Adam result covers every `p>1` under the stated smooth model without those output controls or random step multipliers.

The repository already contains [AdamHeavyTailedFixedMomentum](AdamHeavyTailedFixedMomentum.md), with the same smooth additive-noise accuracy exponent, fixed first momentum, tuned second momentum, and a damping choice that diverges as accuracy improves when `p<2`. It also contains [HeterogeneousAdamFirstMoment](HeterogeneousAdamFirstMoment.md), with fixed default memories but symmetry and samplewise regularity assumptions. The present result is not the first heavy-tail Adam guarantee or first optimal-exponent Adam result. Its new combination is ordinary stationarity for canonical fixed-memory Adam with small accuracy-tuned damping, asymmetric affine infinite-variance noise, and generalized nonlinear curvature.

There is a direct unrestricted-algorithm baseline on this exact setup. Arithmetic-batch signSGD has

\[
\langle g,\operatorname{sign}(g+e)\rangle\ge\|g\|_1-2\|e\|_1,
\qquad \|\eta\operatorname{sign}(g+e)\|_\infty\le\eta.
\]

Combining local descent with the same batch first-moment inequality, taking `η` proportional to `ε/(L0+L1 ε)` and `B` proportional to `1+(σ1+s0/ε)^q`, and absorbing the affine error gives the same product oracle rate as above, with smaller numerical constants. The sign methodology originates with [Bernstein et al., ICML 2018](https://proceedings.mlr.press/v80/bernstein18a.html), whose original finite-variance theorem is not being transferred unchanged. For related generalized-smooth sign/normalized methodology, see [Yu et al., arXiv:2602.07425v2](https://arxiv.org/html/2602.07425v2). The displayed calculation is a reduction on our exact anchored norm setup, rather than an assertion that their differently formulated theorem applies unchanged. Thus this is an independently meaningful Adam-family result, not a new best complexity for unrestricted algorithms: fixed-memory Adam reaches that baseline while retaining its canonical momentum and squared-gradient normalization. Substituting batches into a finite-variance theorem does not work: a finite arithmetic batch can still have infinite variance. Replacing Adam by a normalized method changes the claimed update family. No existing first-absolute-error Adam theorem covering this scope was identified in the checked primary analyses.

The generalized norm assumption has independent provenance in [*Mirror Descent Under Generalized Smoothness*, arXiv:2502.00753v4, 30 May 2026](https://arxiv.org/html/2502.00753v4), Definitions 2.1 and 2.4 and Proposition 2.6. Its two-point local-ball condition is stronger than the anchored condition used here. The function-remainder condition in [Yu et al., arXiv:2602.07425v2, 8 May 2026](https://arxiv.org/html/2602.07425v2), Assumption 2a and Appendix C.4/C.9, is another related formulation, not an interchangeable definition.

## Nonlinear instances and limitations

A genuinely coupled, nonglobally-smooth family is

\[
f(x)=\sum_{i=1}^d\cosh(a_i^\top x)+h(x),
\]

where the rows `ai` form an invertible dense matrix `A`, and `h` is a bounded smooth periodic dense-feature perturbation. Let `||∇h||1 ≤ H`, `||∇²h||∞→1 ≤ J`, `K=max_i ||ai||1²`, and `Q=||A^{−T}||1→1`. Then

\[
\|\nabla^2f(x)\|_{\infty\to1}
\le Kd+KQH+J+KQ\|\nabla f(x)\|_1.
\]

Integration along a segment gives the setup condition with `L0=2(Kd+KQH+J)` and `L1=2KQ`. A sufficiently large cosine perturbation creates negative curvature while the objective remains bounded below. This family has arbitrary finite dimension and interacting coordinates; it is not a quadratic or separable diagnostic.

For `p<2`, choose a centered asymmetric Pareto variable with tail index strictly between `p` and `2`, normalized to have `p`-moment at most one. Multiplying its coordinate copies, which may be correlated, by `(σ0,i^p+σ1^p |∇i f(x)|^p)^{1/p}` gives the exact affine moment model and genuinely infinite variance. The objective/scale maps are jointly measurable. These examples certify meaningful coverage; the formal theorem itself quantifies over all instances of the specification.

The model requires known moment and curvature bounds for tuning, fresh IID batches, and unbiased gradients. Biased or dependent oracles, unknown-tail adaptivity, arbitrary fixed batch size, arbitrary fixed damping at vanishing accuracy, and nonzero weight decay remain outside the result. The constants depend strongly on the fixed memory choices; no uniform claim as a memory tends to one is made.

The initial survey covered the two most recent publicly available ICML, ICLR, and NeurIPS editions (2025–2026), roughly two years of arXiv submissions/revisions, relevant earlier foundations, and repository PRs. A structured median-of-means NeurIPS 2026 OpenReview full text was inaccessible; it was not used to assert an Adam novelty claim. The comparison above rests on accessible Adam and generalized-smoothness primary sources. Formal verification establishes the stated guarantee, not an exhaustive literature theorem or conference acceptance.
