# Curvature-sensitive compressed downlink training

The [main theorem](DistributedCurvatureNormalized.lean) constructs an event-driven distributed algorithm with a deterministic elapsed-time deadline and proves
\(\mathbb E\|\nabla f(X)\|\le\varepsilon\).
The [setup](../Setups/DistributedHessianLipschitzNonconvex.lean) specifies the problem and oracle access; it does not restrict competitors to the constructed algorithm. The implementation is selected by [DistributedNormalizedTraining](../Algorithms/DistributedNormalizedTraining.lean), with positive-dimensional execution in [DistributedNormalizedProtocol](../Algorithms/DistributedNormalizedProtocol.lean).

## Problem and assumptions

There are \(n\ge1\) gradient workers and a coordinator. The objective is a general, possibly nonconvex function on \(\mathbb R^d\), bounded below by \(f_*\), with \(f(x_0)-f_*\le\Delta\), \(L\)-Lipschitz gradient, and differentiable gradient whose derivative is \(Q\)-Lipschitz in operator norm. Here \(L,\varepsilon>0\), \(\Delta,\sigma,Q\ge0\). No minimizer, bounded domain, bounded gradients, or convexity is assumed. Dimension zero is included separately in the implementation.

Each worker has a jointly measurable unbiased stochastic gradient oracle with central second moment at most \(\sigma^2\). Worker noise laws may differ, but their mean gradient is the same \(\nabla f\). Streams are IID within each worker and independent across workers, on an abstract probability space; a product representation is derived internally. Samples cannot be reused at different query points. There is no samplewise Hessian regularity, fourth-moment assumption, Hessian oracle, or common-random-number oracle.

These objective and noise assumptions are those used for normalized implicit-gradient transport in [Cutkosky and Mehta, ICML 2020, Theorem 3](https://proceedings.mlr.press/v119/cutkosky20b.html). Homogeneous objectives are essential to the cancellation below; this is not a theorem for arbitrary heterogeneous client objectives. Hessian Lipschitzness is an additional restriction relative to general smooth distributed training, not a free improvement for that broader class.

An illustrative nonlinear family is
\[
f(x)=\sum_j(1-\cos x_j)+\alpha\sum_{\{j,k\}\in E}(1-\cos(x_j-x_k)),
\]
with fixed \(\alpha\ge0\) and bounded-degree graphs. Coordinates interact, the Hessian changes globally by order one, and gradient and Hessian Lipschitz constants can be bounded independently of dimension. Initializations supported on finitely many coordinates have bounded initial gap. Additive independent vector noise with finite total variance supplies admissible stochastic gradients. This example illustrates scope; the motivation for the assumptions is the established smooth nonconvex stochastic optimization problem, not this particular family.

The network is a star. A gradient query at worker \(i\) takes deterministic time \(h_i>0\). A packet of \(q\) bits on either direction of a star edge takes \(\ell+bq\), with \(\ell,b\ge0\). Directed links operate independently. There is at most one pending computation per worker and one pending packet per directed link. The starting point and parameters are public. The returned point is available at the coordinator; a final broadcast is not required.

## Explicit guarantee and implementation

The Lean `budget` expands the following expression in the setup parameters, with no tuning helpers. Write
\[
 A=1+L\Delta/\varepsilon^2,\quad R=\sigma^2/\varepsilon^2,\quad H=\max_i h_i,
\]
\[
 M_s=2^{20}(1+A\sqrt d),\qquad
 M_u=2^{20}\left(1+\frac{d^2A+d\min(R,n)}{\sqrt n}\right).
\]
For the binary bit length `size`, let
\(B_s=\operatorname{size}(\lceil M_s\rceil)+66\),
\(B_u=\operatorname{size}(\lceil M_u\rceil)+66\), and
\(c_s=bB_s,\ c_u=bB_u\). Define
\[
 F=\max\left\{H,c_u,c_s,\frac{dc_u}{n},\frac{dc_s}{\sqrt n},
 \left(\frac{d^3c_uc_s^2}{n}\right)^{1/3},
 \frac{\sigma^2H}{n\varepsilon^2},
 \sqrt{\frac{d\sigma^2Hc_u}{n\varepsilon^2}},
 dc_s\min\left(1,\frac{\sqrt{Q\varepsilon}}L\right)\right\}.
\]
The deadline is exactly \(2^{25}A(\ell+F)\), embedded in nonnegative real time. All precision logarithms remain explicit; the uplink and downlink widths are different. The large universal constant is a proof convenience, not a claim of practical tuning quality or optimal constants.

Set \(t=256F\), \(\eta=\varepsilon/(128L)\), and \(K=\max\{1,\lceil1024L\Delta/\varepsilon^2\rceil\}\). The coordinator takes normalized gradient steps of length at most \(\eta\). Workers compute fresh minibatches at their current local models, clip their batch means using a deterministic range bound, and send unbiased coordinate compression with randomized finite-grid rounding. Repeating compression of a batch mean reduces compression variance, not the intrinsic variance of that shared batch. The coordinator sends independent unbiased compressed increments to workers and periodically refreshes their models. Full-vector branches handle cheap communication and zero bit costs. Coordinate choices come from independent worker-indexed public random streams, so their indices need not be transmitted.

The selected output is a uniform pre-update coordinator iterate among \(x_0,\ldots,x_{K-1}\). The positive-dimensional algorithm completes exactly \(K b_0\) gradient queries at each worker, where
\[
 b_0=\max\{1,\lceil16384\sigma^2(1+\omega)/(n\varepsilon^2)\rceil\},
\]
and \(\omega=0\) for full uplinks and \((d-1)/m\) for \(m=\max\{1,\lfloor t/c_u\rfloor\}\) repeated coordinate compressions. The last downlink is omitted. Every packet includes the template's 64 padding bits in its cost. The proof bounds actual completion time by \(K(69t+2\ell)\), then by the public deadline. It also proves `FiniteEvents` at every deadline up to that budget, including zero-duration communication, and identifies `DistributedTemplate.execute` with the analyzed output under `DistributedTemplate.law`. This is an elapsed-time theorem, not a claim of an improved total gradient-query count.

## Mathematical contribution

The mechanism is curvature-sensitive control of adaptive model discrepancies using only second moments. If \(e_i\) is worker \(i\)'s discrepancy from the coordinator, independent fresh downlink errors yield both a bound on \(\mathbb E n^{-1}\sum_i\|e_i\|^2\) and a factor-\(n\) smaller bound on \(\mathbb E\|n^{-1}\sum_i e_i\|^2\). Entire worker trajectories are not independent. Common-objective Taylor expansion gives
\[
 \left\|\frac1n\sum_i\nabla f(x+e_i)-\nabla f(x)\right\|
 \le L\left\|\frac1n\sum_i e_i\right\|
       +Q\frac1n\sum_i\|e_i\|^2.
\]
Normalized descent uses expected estimator norm error, so this quadratic Taylor remainder needs no fourth moment. Together with a Lipschitz fallback, it produces the term
\(dc_s\min\{1,\sqrt{Q\varepsilon}/L\}\) in the time frontier. Taking the conditional norm bound before integrating over history preserves a small multiple of \(\mathbb E\|\nabla f(x)\|\), which can be absorbed in descent. Replacing this with a global RMS bound would lose that argument.

The obstruction is not visible in a scalar quadratic calculation. Shared adaptive history prevents treating worker trajectories as independent. Directly squaring the quadratic Taylor remainder introduces fourth powers of model errors, unsupported by the admitted noise model. Substituting a Hessian-diameter bound from a bounded region into a global-variation theorem also does not give this rate: no bounded region is assumed, and the available path-length bound grows with the iteration horizon. The proof instead combines fresh conditional cancellation with norm-error descent.

Normalization, Taylor expansion, martingale second-moment cancellation, clipping, and finite-grid encoding are individually established tools. The proposed research contribution is their combination into this downlink curvature-sensitive frontier under objective Hessian regularity and finite-variance gradients, with complete adaptive stochastic and event-execution proofs. Formalization alone is not the novelty claim.

## Prior guarantees, reductions, and improvement regime

The closest communication frontier is [Begunov and Tyurin, Inkheart, arXiv:2605.07795v2, October 19, 2026](https://arxiv.org/abs/2605.07795v2), Theorems 2.1–2.2 and Proposition 1.9; its NeurIPS 2026 status was checked in the official conference listing linking [poster 150535](https://neurips.cc/virtual/2026/poster/150535). Its bound contains a downlink term \(d\kappa L_A\Delta/\varepsilon^2\), where favorable global gradient variation requires a small \(L_A\). General smooth objectives admit \(L_A=L\). The present theorem instead uses local Hessian regularity to obtain a curvature term proportional to \(dc_s\sqrt Q\Delta/\varepsilon^{3/2}\) in the small-accuracy regime. It does not dominate Inkheart when its global variation parameter is especially favorable. Inkheart bounds expected elapsed time and expected squared gradient norm; this theorem gives a fixed deadline and expected gradient norm. Squared-norm accuracy \(\mathbb E\|\nabla f\|^2\le\varepsilon^2\) implies our target by Jensen, but the converse is not claimed. This is a guarantee tradeoff.

The comparison also includes stronger smoothness-based methods, not just unaccelerated distributed SGD:

* [Cutkosky–Mehta, ICML 2020, Theorem 3](https://proceedings.mlr.press/v119/cutkosky20b.html) gives normalized implicit-gradient transport under matching objective smoothness and finite variance, with serial leading accuracy exponent \(7/2\). Its full-vector minibatch implementation must pay for model communication.
* [Li–Lin, JMLR 24 (2023), Algorithm 1 and Theorem 1](https://www.jmlr.org/papers/v24/22-0522.html) provides gradient-only restarted nonconvex acceleration with \(O(\Delta\sqrt L Q^{1/4}\varepsilon^{-7/4})\) deterministic gradients. Its nonadaptive restart does not require function values; noisy simulation and full-vector exchanges cannot be omitted from a matched comparison.
* [Chayti–Jaggi–Doikov, arXiv:2302.11962v7, October 9, 2026](https://arxiv.org/abs/2302.11962v7), Appendix C and Appendix E.2, equation (39), supports a stronger lazy-Hessian cubic reduction. Fresh-gradient spherical finite differences have bias \(O(Q\delta)\) and Frobenius variance \(O(d^2L^2+d^2\sigma^2/\delta^2)\). Robust batching handles the third-moment requirement without assuming fourth moments of gradients. Optimizing the Hessian refresh period must be included; comparing only to a fresh Hessian at every step overstates the gain.

For an explicit separation of the checked upper guarantees, take fixed positive \(L,Q,\Delta,\sigma,H,\ell,b\), \(d\asymp\varepsilon^{-7/4}\), and \(n\asymp\varepsilon^{-3/2}\). Integer rounding does not affect the exponents. Here \(B_u,B_s=\Theta(\log(1/\varepsilon))\), and the proved deadline is
\(O(\varepsilon^{-13/4}\log(1/\varepsilon))\).
Serial NIGT and full-vector accelerated-gradient communication have exponent \(7/2\). The optimized spherical finite-difference lazy-cubic reduction has exponent \(29/8\); even granting a hypothetical dimension-\(d\), rather than dimension-\(d^2\), Hessian noise cost in that reduction gives exponent \(10/3\). These polynomial gaps survive the explicit precision logarithms. The comparisons grant competing cubic methods free coordinator arithmetic too.

For clarity, the lazy-cubic comparison is a gradient-oracle reduction, not a direct quotation of a distributed theorem. With unit smoothness/noise constants and refresh period \(p\ge1\), allow regularization \(M\asymp p\). The leading optimistic elapsed expression is
\[
 \varepsilon^{-3/2}\min_{p\ge1}\{a\sqrt p+c p^{-5/2}\},\qquad
 a=d+\frac1{n\varepsilon^2},\quad c=\frac{d^2}{n\varepsilon^2}.
\]
It charges fresh gradient batches every step and a Hessian batch every \(p\) steps. Optimizing gives \(p\asymp(c/a)^{1/3}\) when \(c\ge a\). In the stated regime, \(a\asymp\varepsilon^{-7/4}\), \(c\asymp\varepsilon^{-4}\), and \(p\asymp\varepsilon^{-3/4}\), yielding exponent \(29/8\). Replacing \(d^2\) by \(d\) gives \(p\asymp\varepsilon^{-1/6}\) and exponent \(10/3\). Initial snapshots, ceilings, deterministic finite-difference variance, latency, and precision costs are not negative; omitting them makes this screen favorable to the comparator. It is not a complete formal finite-bit implementation of cubic Newton. Robust batches use independent fresh samples, and full-vector exchanges must still be counted. No same-sample gradient differences are available under the present oracle.

These are comparisons of sufficient upper guarantees, not complexity lower bounds or proofs that the competing algorithms cannot do better. No universal optimality is asserted. Improved anisotropic Hessian estimation or a compressed accelerated method could narrow the gap. Total gradient work can be worse than serial methods; the gain is parallel elapsed time under the stated network.

Related local-SGD results do not automatically supply this guarantee. [Glasgow–Yuan–Ma, AISTATS 2022](https://proceedings.mlr.press/v151/glasgow22a.html), Assumption 2 and Appendix C, require samplewise Hessian regularity and fourth moments in the relevant analysis. [Luo et al., AISTATS 2025](https://proceedings.mlr.press/v258/luo25c.html), Theorem 3, retains the smoothness communication term in its homogeneous specialization. Uplink compression with an exact shared model, including [Gradient Normalization Enables Communication-Efficient Distributed Learning under Initialization/Data Heterogeneity](https://doi.org/10.1109/TPAMI.2026.3689520), does not establish the downlink discrepancy bound here.

The literature screening covered the publicly available ICML 2025/2026, ICLR 2025/2026, and NeurIPS 2025/2026 conference catalogs, approximately November 2024–November 2026 arXiv submissions and revisions, and older foundational results. Conference status and preprint status were checked separately. Some OpenReview/virtual-conference routes were inaccessible; official listings and accessible primary manuscripts supplied alternatives. Absence from a search is not evidence of novelty, and unchecked inaccessible manuscripts are not treated as verified baselines.

## Distributed-training scope

The result addresses distributed stochastic training of general nonlinear objectives in arbitrary finite dimension. Its algorithm uses the existing computation and communication oracles, and its public statement is `DistributedTemplate.TimedConvergence` with a scalar nonnegative-real budget. Accuracy and finite-event termination concern actual template execution. Thus the contribution meets the requested distributed-training scope without changing the frozen template or replacing elapsed time by an idealized round count.

## Fairness, limitations, and realism of TemplateDistributed

The template's strength is that the theorem concerns actual event-driven execution: computation and packet completion, local information, pending-resource restrictions, a scalar deadline, and finite-event termination are explicit. This prevents an idealized round count from silently becoming an elapsed-time guarantee. It is not evidence that the template is universally superior to other distributed models.

The present star oracle assumes independent directed links, so aggregate coordinator bandwidth scales with worker count. This is a property of this setup, not an unavoidable limitation of the generic communication-oracle interface. A shared network interface or switch bottleneck can change the comparison substantially. All comparisons above use matching communication assumptions.

Local arithmetic, coordinator aggregation, memory, serialization, and cubic-model solution for competitors are free. Gradient service times are known and deterministic; stragglers and correlated delays are absent. Perfect shared randomness and ideal real-valued local states are available. The finite alphabet is encoded using noncomputable finite equivalences; the proof is not an executable numerical codec. Routing/source identification is implicit. The template's appended 64 zero bits are charged, but should not be interpreted as a realistic timestamp protocol. Initial models are public and the final answer is coordinator-only. `FiniteEvents` excludes infinitely many events before a deadline; it does not charge for expensive finite local arithmetic.

In particular, the asymptotic example fixes per-query service time while dimension grows. Physical devices may have dimension-dependent service times and finite aggregate bandwidth, so the example is a model comparison rather than a hardware speedup prediction.

Useful future framework work would add costed local/coordinator computation, shared-bandwidth contention and queueing, random service times with explicit scheduling contracts, and implementable finite-precision/randomness interfaces. Such changes should be assessed separately and applied fairly to all competitors. This contribution leaves `TemplateDistributed.lean` and the other frozen framework files unchanged. Its realism is conditional on the stated oracle, while its finite-event and finite-packet accounting is a useful foundation for richer models.
