# Fixed-momentum coordinate Adam with asymmetric heavy-tailed gradients

The [main theorem](AdamHeavyTailedFixedMomentum.lean) constructs canonical coordinate Adam with first-moment coefficient \(0.9\), one fresh gradient call per update, and an independently uniform pre-update output. It proves expected **ordinary Euclidean gradient norm** at most ε for every finite dimension and every globally smooth, lower-bounded nonlinear objective satisfying the [setup](../Setups/HeavyTailedAdam.lean). The essential [execution accuracy lemma](../Proofs/AdamHeavyTailedRate.lean) explicitly names `Adam.output`, the coefficient \(0.9\), the tuning below, and the abstract IID sampling law.

This is a method-specific guarantee, not an improvement in the best known complexity of the problem class. Clipped and normalized stochastic methods already attain the same heavy-tail exponent. The contribution is obtaining that exponent for the specified no-bias-correction Adam variant, with its historical coordinate denominator and fixed positive momentum, without symmetry, bounded true gradients, or a relaxed stationarity criterion. The proof does not establish an adaptive-preconditioning advantage.

## Problem, oracle, and algorithm

Let \(f:\mathbb R^d\to\mathbb R\) have an \(L\)-Lipschitz gradient, \(L>0\), and \(f(x_0)-f(x)\le\Delta\) for every \(x\). The jointly measurable oracle satisfies, for every \(x\),

\[
\mathbb E g(x,\xi)=\nabla f(x),\qquad
\mathbb E\sum_{i=1}^d|g_i(x,\xi)-\nabla_i f(x)|^p\le\sigma^p,
\quad 1<p\le2.
\]

The specification includes the Bochner integrability needed for these assertions. Samples are IID under an abstract probability measure; the proof derives a product representation internally. Coordinates of a sample may be dependent, noise may be asymmetric and state dependent, and the sample space need not be finite. There is no convexity, PL, interpolation, bounded-gradient, or bounded-support assumption. \(L,\Delta,\sigma,p,\varepsilon\) are available for tuning.

The [algorithm](../Algorithms/Adam.lean) starts with \(m_0=v_0=0\) and uses

\[
m_{t+1}=0.9m_t+0.1g_t,\quad
v_{t+1}=(1-\rho)v_t+\rho g_t^{\odot2},\quad
x_{t+1}=x_t-\eta\,m_{t+1}/(\sqrt{v_{t+1}}+\tau).
\]

All division and square roots in the update are coordinatewise. There is no bias correction, weight decay, clipping operation, extra normalization, batch enlargement, or restart. The positive scalar damping is outside the square root. The output is \(x_I\), where \(I\) is independent and uniform on \(\{0,\ldots,K-1\}\). `execute` performs exactly \(K\) calls, including the last call although the selected point is a pre-update iterate. The setup's `allowedAlgorithm` enforces this update/output family but permits every valid constant momentum and tuning; it does not artificially restrict the problem to the particular construction \(0.9\).

## Explicit guarantee and cost

For ε>0, set

\[
\rho=\frac1{10^{12}+(10^5\sigma/\varepsilon)^{p/(p-1)}},\qquad
\tau=\frac{\varepsilon}{10^5\sqrt\rho},\qquad
\eta=\frac{\tau\rho}{10^5L},
\]
\[
K=1+\left\lceil\frac{4\cdot10^8\Delta L}{\varepsilon^2}
\left[10^{12}+(10^5\sigma/\varepsilon)^{p/(p-1)}\right]\right\rceil.
\]

The result is \(\mathbb E\|\nabla f(x_I)\|_2\le\varepsilon\), with output measurability and gradient-norm integrability proved. It includes σ=0, Δ=0, and the zero-dimensional space. For fixed \(p\), the oracle cost is

\[
O\!\left(1+\frac{\Delta L}{\varepsilon^2}
+\frac{\Delta L\sigma^{p/(p-1)}}{\varepsilon^{(3p-2)/(p-1)}}\right).
\]

The explicit constants are large and are not practical tuning recommendations. In the displayed budget the noise term dominates when
\(\varepsilon\le10^5\sigma\,10^{-12(p-1)/p}\).
The exponent match concerns this noise-dominated asymptotic regime; there is no constant-factor superiority claim. As ε decreases with σ>0 and \(p<2\), the damping grows like \(\varepsilon^{(p-2)/(2(p-1))}\) and can suppress useful coordinate adaptation.

The noise geometry matters. The assumption implies \(\mathbb E\|g-\nabla f\|_2^p\le\sigma^p\). Conversely a Euclidean moment scale \(\sigma_2\) supplies the coordinate scale \(d^{1/p-1/2}\sigma_2\). On that common Euclidean scale, this Adam bound has an extra factor \(d^{(2-p)/(2(p-1))}\) in its noise-dependent cost relative to dimension-free normalized-SGD results. The factor disappears at \(p=2\). No matching lower bound for the exact coordinate-moment class, or necessity of this dimension penalty for Adam, is claimed.

## What the proof adds

The difficulty is that a past noisy gradient enters both the current momentum numerator and many future adaptive denominators. Treating the denominator as predictable or replacing it by a constant is invalid. A pointwise lower bound after freezing future mean gradients is also false: noisy gradients can cancel the mean.

The [window proof](../Proofs/AdamHeavyTailedWindow.lean) freezes future **mean** gradients while retaining the actual adaptive noise trajectory. A derivative-free Taylor remainder of order \(p\), followed by backward conditional integration, controls asymmetric noise bias. The [cancellation argument](../Proofs/AdamHeavyTailedCancellation.lean) uses two distinct fresh samples: a small frozen denominator requires two large cancellation errors. Sequential conditional moment bounds control that joint event without assuming independent noise coordinates or independent adaptive errors.

The [trajectory and descent bounds](../Proofs/AdamHeavyTailedDescent.lean) then transport both numerator and denominator through overlapping windows. The [history proof](../Proofs/AdamHeavyTailedHistory.lean) sums them with geometric momentum weights, treats zero lag separately, and bounds normalized update energy without assuming a raw second moment. A weighted signal/noise history decomposition converts the resulting denominator-weighted estimate into ordinary gradient norm. The total transport and smoothness constants are \(200+9600+16<10000\); [tuning algebra](../Proofs/AdamHeavyTailedTuning.lean) proves that the simplified public budget suffices. These steps are dependencies of the proved rate, not separate unused calculations.

Batching, clipping, and composition with an existing normalized-SGD theorem already recover the problem-class exponent, but change the algorithm. Directly applying a normalized-preconditioned theorem requires its extra normalization and condition-number hypothesis. Large damping as a bias-control device is already known; the new claim concerns the finite-window historical coupling with fixed positive momentum and exponential forgetting.

## Closest primary comparisons

Literature checks were made independently by Researcher and Reviewer as of 19 October 2026, including the recent ICML, ICLR, NeurIPS and arXiv literature and stronger older references. Absence of a matching search result is not a proof that no prior result exists.

- **Strongest clean problem-class baseline:** Hübler, Fatkhullin and He, [AISTATS 2025](https://proceedings.mlr.press/v258/hubler25a.html), [arXiv v3, 9 July 2025, Appendix D.2, Corollary 19](https://arxiv.org/html/2410.13849v3#A4.SS2), prove a one-sample normalized-momentum bound
  \(6\sqrt{\Delta L/T}+6(\Delta L\sigma_2^{p/(p-1)}/T)^{(p-1)/(3p-2)}\).
  It has no logarithmic loss and uses the weaker Euclidean moment assumption. Their momentum is horizon tuned and their update is normalized. Our result matches the exponent at fixed coordinate scale, with the dimension and constant limitations above; it is not a class-level advance.
- **Another one-sample baseline:** Liu and Zhou, ICLR 2025, [v4, 29 May 2025, Theorem 3.2](https://arxiv.org/html/2412.19529v4#S3.SS1), cover generalized smoothness and additive heavy-tailed noise with \(B=1\), despite the method's “Batched NSGDM” name. Their theorem includes an additional transient term. We neither improve their broader assumptions nor claim a new single-sample capability for the problem class.
- **Closest explicit open question:** Yu et al., [v1, 22 June 2026](https://arxiv.org/html/2606.23676v1), discuss heavy-tailed AdamW under generalized coordinate smoothness/noise and give weighted-stationarity analysis. Our guarantee addresses the globally smooth, additive-noise, zero-weight-decay subcase with ordinary stationarity and deliberately tuned damping. Their ordinary target is the \(L_1\) gradient norm, whereas ours is Euclidean: for \(d>0\), an \(L_1\) target requires substituting \(\varepsilon/\sqrt d\), with the resulting dimension-dependent cost. This does not resolve their dimension-sensitive ordinary-\(L_1\) subcase, broader AdamW question, fixed tiny damping, or arbitrary tunings. This source is an unreviewed preprint.
- **Existing coordinate Adam heavy-tail result:** Liu, [v1, 21 June 2026, Assumptions 1–5, Algorithm 1, Theorem 1/Corollary 2](https://arxiv.org/html/2606.22326v1), studies bias-corrected Adam with exponential random step multipliers, bounded true coordinate gradients, tied horizon-dependent moment coefficients, and relaxed \((\lambda,\varepsilon)\)-\(L_1\) stationarity. Its vanishing guarantee requires \(p>4/3\). Those algorithm, assumptions and output criterion differ; there is no claim here to be the first heavy-tailed coordinate-Adam analysis. No conference acceptance was verified for this preprint.
- Pang's [UAI 2026 paper](https://proceedings.mlr.press/v337/pang26a.html), [v2, 2 August 2026](https://arxiv.org/abs/2607.27383), uses vector-form Adam and randomized online-to-nonconvex conversion with a different relaxed stationarity criterion. Its optimal-rate variant requires bounded outputs. It does not supply the present coordinate-Adam ordinary-gradient guarantee.
- Liu's [ICML 2026 AdaGrad paper](https://proceedings.mlr.press/v306/liu26f.html), [v2](https://arxiv.org/abs/2605.18694), offers tail-index adaptation with cumulative denominators; the stated smooth-case rate is meaningful for \(p>4/3\). Our theorem knows \(p,\sigma\) and makes no adaptation improvement. Hanyu Yang's [8 October 2026 preprint, Theorem 5.1 and Corollary 5.2](https://severinvisionary.github.io/adagrad-heavy-tailed-noise/) explicitly analyzes damping against asymmetric noise for cumulative AdaGrad without momentum. Both agents read that proof after resolving initial PDF access failure. Its damping mechanism is prior art; its lower-bound claims were not fully audited here.
- Fang, Demmel and Lavaei, [v1, 13 February 2026, Theorem 4.5](https://arxiv.org/html/2602.13413v1), obtain the heavy-tail exponent for normalized preconditioned momentum under bounded preconditioner condition number and Euclidean moments. Their extra normalization/conditioning assumptions prevent a direct application to this update. Generic nonlinear-SGD results such as [Armacki et al., v2](https://arxiv.org/abs/2410.13954) also do not directly remove the evolving-history dependence; their exact-convergence noise symmetry requirements differ.

Global smoothness, lower boundedness, unbiased sampling and finite \(p\)-moments are established assumptions in these comparisons. The coordinate aggregate condition is explicitly stronger than the Euclidean version, not a renamed equivalent assumption. Attempting to remove its dimension dependence breaks the normalized update-energy bound for a dense rare-spike oracle; that diagnoses this proof's limitation, not an impossibility theorem for Adam. No additional structural restriction was introduced to repair the nonlinear proof.

## LLM-pretraining motivation and numerical limits

The motivation is the combination of fixed positive momentum, exponentially forgetting coordinate scales, and heterogeneous gradient spikes used or observed in language-model training. Smooth interacting nonlinear instances include dense-feature bounded sinusoidal sums plus a positive quadratic regularizer; finite-sum stochastic gradients on these objectives satisfy uniform coordinate moments because the fluctuating sinusoidal gradients are bounded. More directly, finite-corpus cross-entropy models with coordinatewise tanh parameter reparameterizations, a finite smooth network on the compact closure of the parameter image, and positive normalization stabilizers have globally bounded Hessians and nonseparable nonlinear interactions. These examples explain nontrivial scope; they do not assert global smoothness of unrestricted transformer training.

Before formalization, two 2,114,816-parameter transformers were trained on WikiText-2 (four blocks, width 128, four heads, RMSNorm/SwiGLU, BPE vocabulary 4096; seeds 19 and 37). The initial 300-step runs used AdamW, batch 16, sequence length 128. At each trained checkpoint, 64 reference batches and 128 fresh batches of size 4 probed gradient noise. Empirical coordinate kurtosis had median about 4.1 and upper quantiles near the finite-sample ceiling; this supports heterogeneous spikes, not a verified infinite-variance law. At \(p=1.5\), estimated aggregate coordinate scales were about 5.33 and 5.40, versus maximum individual-coordinate scales 0.01614 and 0.01544.

An exploratory damping proxy used the **maximum individual-coordinate** estimate and ρ=0.02, not the aggregate scale or conservative constants of this theorem. Even that smaller proxy dominated coordinate RMS by median factors about 132 and 128. An 80-step retuned pilot used momentum \(1/64\), not the theorem's \(0.9\): validation losses were 6.165387/6.159538, versus 6.166082/6.161943 for a soft-clipped momentum comparator. These small differences establish neither statistical significance nor an adaptive-Adam advantage. The exact theorem tuning, including ρ≤10⁻¹², was not empirically validated.

These are small-model, finite-trajectory diagnostics. They do not verify a uniform global moment bound, global smoothness of a full LLM, asymptotic tails, or full-scale pretraining performance. The result is a theoretical guarantee for the stated model, with an explicit gap between its conservative tuning and practice. Extending it to generalized smoothness, nonzero weight decay, unknown tail parameters, smaller damping, or a dimension-free Euclidean moment model remains outside the proved claim.
