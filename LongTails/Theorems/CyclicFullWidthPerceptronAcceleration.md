# Cyclic full-width quadratic Perceptron on larger datasets

The [Lean theorem](CyclicFullWidthPerceptronAcceleration.lean) proves a contrast-independent separation bound for the ordinary cyclic, constant-step quadratic Perceptron, initialized with an identity first layer and a zero output layer. It covers arbitrarily many, potentially conflicting residual directions in arbitrary finite dimension. The improvement is over the constant-step linear Perceptron from zero, not over the best linear classification algorithm or the oracle complexity of the problem class.

## Statement and algorithm

The [setup](../Setups/CyclicFullWidthPerceptron.lean) has one positive signed example (e=(1,0)) and (N>0) negative signed examples
\[
q_i=(-(1+\nu_i),-\mu u_i)\in\mathbb R\times\mathbb R^d.
\]
Here “signed” means that the label has already been multiplied into the input. Assume
\[
\|u_i\|\le1,\qquad \exists w:\ \|w\|=1,\quad \langle w,u_i\rangle\ge\kappa,
\]
\[
0<\kappa\le1,\quad 0<\mu\le\kappa^4/2^{20},\quad
0\le\nu_i\le\bar\nu\le\kappa^{12}\mu^2/2^{56}.
\]
There is no restriction on pairwise residual inner products, residual rank, or the number of samples relative to dimension. The offsets may differ and may vanish. The narrow offset slab is an explicit additional restriction, not a consequence of ordinary linear separability. The residual norm and margin assumptions are the standard bounded separability conditions used in Perceptron analyses. The anchored near-opposition geometry and this quantitative slab are new restrictions, motivated by the small-contrast examples in Tyurin rather than asserted to be a standard general classification model. They isolate the established question of whether the two-point acceleration phenomenon survives arbitrary interacting latent directions. The particular powers and constants delimit the finite-error proof; they are not known to be necessary.

The [algorithm](../Algorithms/CyclicFullWidthPerceptron.lean) uses a square hidden layer (W\in\mathbb R^{(d+1)\times(d+1)}) and an output vector (v\in\mathbb R^{d+1}), with score (v^TWq). Thus the classifier is linear in its input, but quadratic in its trainable parameters. There is no change in representational capacity. Starting from (W=I,v=0), it queries (e,q_0,\ldots,q_{N-1}) cyclically. When (v^TWq\le0), it updates both layers simultaneously using their old values:
\[
W^+=W+\eta vq^T,\qquad v^+=v+\eta Wq,\qquad \eta=\kappa^6/2^{28}.
\]
Correctly classified queries leave the weights unchanged. There is no reference kick, artificial update on a correct sample, restart, separator advice, or data-dependent initialization. The setup's `allowedAlgorithm` captures the same-step update family, initialization, cyclic query order, and last-iterate output; it leaves the step size to the algorithm.

The algorithm returns its actual last parameter state after
\[
B=(N+1)\left\lceil\frac{256}{\kappa^4}\right\rceil
\]
queries. Every signed example then has strictly positive score. The guarantee is deterministic and applies to every seed allowed by the repository oracle interface. Each visit costs one oracle call, including correctly classified visits. The oracle returns the queried example's score and all parameter-gradient blocks; it is not a full-dataset gradient oracle. These quantities are computable from one signed example and the current parameters.

The result proves strict separation, not a fixed positive margin, maximum-margin convergence, a loss bound, or robustness to rounding or noise. The final margins can be very small. Dense matrix arithmetic and storage are not included in the formal oracle budget.

## Acceleration comparison and its limits

The [linear comparison](../Proofs/CyclicPerceptronLinearComparison.lean), with its [algorithm definition](../Algorithms/CyclicPerceptronLinearComparison.lean), proves that the ordinary linear Perceptron from zero, with any positive constant step size and any sample-query order, needs more than (1/(2\mu^2)) queries before its actual iterate strictly separates these same examples. The proof bounds negative updates and hence also queries; it does not depend on the chosen order. It uses the same strict-separation accuracy criterion as the main result.

After (a) positive and (b) negative updates, the linear predictor divided by its step size is
\[
(a-b-T)e-\mu U,\qquad T=\sum_{\text{negative updates}}\nu_i,
\quad \|U\|\le b,\quad 0\le T\le b\bar\nu.
\]
Strict reference accuracy forces the integer (a-b\ge1). If (b\mu^2\le1/2), then the reference coordinate is at least (1/2), whereas no negative example can have a positive score. This proves the lower bound. For the convention accepting a zero score on the positive example, the same mathematical argument holds on the strictly positive-offset subfamily: any successful history must contain a negative update, so (T>0) still forces (a-b\ge1). The Lean comparison states the common strict criterion; it does not claim this tie convention for zero-offset data.

The explicit oracle advantage holds when
\[
(N+1)\lceil256/\kappa^4\rceil<1/(2\mu^2).
\]
Asymptotically, fixed \(\kappa\) and \(N\mu^2\to0\) give an unbounded improvement. Increasing dataset size without controlling this relation does not give a universal advantage.

Stronger linear methods remain stronger baselines. A linear method can cancel the last selected negative example's background using a corresponding positive step, then add a small bias increment \(\sigma=\mu^2\kappa^2/8\). At balanced states its predictor is \(\sigma j e-\mu\sum_{r\le j}u_{i_r}\). A negative mistake implies
\(\langle\sum_{r\le j}u_{i_r},u_i\rangle\le2\sigma j/\mu^2\).
The usual Perceptron norm/projection argument gives \(O(\kappa^{-2})\) negative updates and \(O((N+1)\kappa^{-2})\) cyclic calls; the reference remains misclassified after a negative update in this regime. This uses unequal, history-dependent positive and negative step sizes. It shows both that the raw constant-step linear lower bound is not a problem-class lower bound and that our \(\kappa^{-4}\) dependence remains worse by a factor \(\kappa^{-2}\). The contribution is that simultaneous unperturbed factor updates generate the needed bias intrinsically.

Second-order and accelerated linear Perceptron methods also preclude a problem-class optimality claim. Cesa-Bianchi, Conconi and Gentile's [second-order Perceptron, Theorem 3.1, p. 648](https://cesa-bianchi.di.unimi.it/Pubblicazioni/J21.pdf) gives a spectral bound that specializes here to an upper bound of order \(r\kappa^{-2}\log(r/(\kappa\mu))\), with rank \(r\) and matrix computations. Its whitening discussion is another standard reduction. [Wang et al., ICLR 2023](https://arxiv.org/abs/2210.09371) give accelerated linear Perceptron guarantees using full-data operations; such iterations must not be counted as single indexed-example calls. Reading and preprocessing the entire finite dataset is itself a stronger oracle strategy than the raw online comparator.

## Nontrivial larger datasets

The [instance module](../Proofs/CyclicPerceptronInstances.lean) constructs the family
\[
u_{j,\pm}=\kappa w\pm\sqrt{1-\kappa^2}\,e_j,
\qquad j=1,\ldots,m,
\]
where \(w,e_1,\ldots,e_m\) are orthonormal. Their norms are one and their common latent margin is exactly \(\kappa\). The module proves the norm, margin, opposite-pair inner product, and pair sum/difference identities. For \(\kappa<1/\sqrt2\), each opposite pair has negative inner product \(2\kappa^2-1\); the residuals span dimension \(m+1\). This is not an acute cloud or a fixed-rank two-sample replication. All directions interact through the shared reference and jointly trained layers.

Choose distinct offsets \(\nu_i=\bar\nu(i+1)/(2m+1)\), and, for example, fixed \(\kappa=1/2\), \(\mu=\kappa^4/[2^{20}(m+1)^2]\), and \(\bar\nu=\kappa^{12}\mu^2/2^{56}\). These are strictly positive offsets satisfying the specification. The nonlinear query bound is \(O(m)\), whereas the raw linear lower bound is \(\Omega(m^4)\). Full width is \(m+2\). A naive dense implementation uses \(O(m^3)\) arithmetic for the nonlinear upper bound versus \(\Omega(m^5)\) for dense linear updates in this example; this last comparison is an implementation-cost calculation, not a formally verified arithmetic theorem.

## New mechanism and formal proof

The proof pairs mistakes according to their genuine cyclic occurrence. Every reference mistake is followed immediately by the first negative mistake; after a negative mistake, all remaining negatives are correct until the next reference visit. The [pairing module](../Proofs/CyclicPerceptronPairing.lean) proves these signs for the actual finite-step network, including different offsets on the selected and tested negatives.

In normalized balanced coordinates, let \(U\) sum all residual updates, \(V\) sum negative-first residual updates, and \(C\) be the comparison reference bias. A positive-first pair changes \(C\) by \(\langle U,u_0\rangle-\beta_i\); a negative-first pair changes it by \(2\langle U,u_i\rangle+\|u_i\|^2-\beta_i\), with \(0\le\beta_i\le1\). Consequently \(E=\|U\|^2-C\) has asymmetric increments. The cumulative offset loss is bounded by the number of pairs; it is not assumed constant across samples.

Before a balanced reference mistake, each negative has been checked since the last completed pair, except \(u_0\) after a positive-first pair; its cone inequality is retained from that pair's \(u_0\) update. At initialization all inequalities hold with \(U=0\). These facts place \(U\) in an approximate dual cone. Projecting \(u_0\) onto that cone yields a vector of norm at least \(\kappa\). A cone-based energy estimate, followed by square completion, makes the reference bias grow quadratically in the number of positive-first pairs. It eventually contradicts the reference-mistake condition. This handles negative residual correlations that invalidate a pairwise acute-angle argument.

The [finite-error induction](../Proofs/CyclicPerceptronBootstrap.lean) derives all coordinate bounds from the exact simultaneous updates. For horizon \(H=\lceil128/\kappa^4\rceil\), the normalized negative-score error is at most \(256\eta^2H^3\), and the reference-bias error at most \(256\eta^2H^4\). The first layer stays close to identity: the mechanism is higher-order reference-bias generation, not improved conditioning of the learned representation. The [certificate](../Proofs/CyclicPerceptronCertificate.lean) and [scanner induction](../Proofs/CyclicPerceptronScanner.lean) prove at most \(68\kappa^{-4}\) completed pairs, and allow one unfinished pair. A nonseparating full scan must contain a mistake. The [execution proof](../Proofs/CyclicPerceptronExecution.lean) connects this count to `execute` and the public budget, including absorption after separation. No convergence premise is included in the setup.

## Relation to prior work and scope of novelty

The primary starting point is Tyurin, [arXiv:2512.11587v2, 21 May 2026](https://arxiv.org/abs/2512.11587v2), [accepted at ICML 2026](https://proceedings.mlr.press/v306/tyurin26a.html). Its Theorem 2.1 concerns a large-norm, fixed-time limiting relation; Theorem 5.1 gives a high-probability upper bound of \(\widetilde O(\sqrt d/\mu_{\mathrm{paper}})\) for its two-sample convolutional QPA, with tuned noise, step size, and nonzero initialization projection onto a specified eigendirection. Theorem 5.2 gives \(\Omega(d/\mu_{\mathrm{paper}})\) steps for the batch linear Perceptron from a sufficiently small initialization. Both concern finding a separator; with two samples, the per-step sample cost is constant. The present result supplies an unperturbed, finite-step, cyclic full-width guarantee for arbitrarily many interacting residual directions. It is a generalization of the implicit-acceleration phenomenon and dataset arity, not a theorem containing all of Tyurin's parameter regimes or his convolutional architecture.

The repository's [TwoSampleQuadraticPerceptronAcceleration](TwoSampleQuadraticPerceptronAcceleration.md) retains its existing two-sample cases. [NoisyBatchQuadraticPerceptronGlobal](NoisyBatchQuadraticPerceptronGlobal.md) already handles arbitrary finite separable datasets, arbitrary initialization, and fixed Gaussian noise, but supplies a global convergence guarantee rather than a larger-dataset acceleration rate. We trade that breadth and noisy batch model for a deterministic acceleration theorem in the stated structured slab. [ManySampleConvolutionalPerceptronAcceleration](ManySampleConvolutionalPerceptronAcceleration.md) uses a two-coefficient convolution, derivative-separable defects, a restarting scan, and a directed reference perturbation. Such an externally supplied bias correction must be compared with its linear analogue; its presence does not by itself establish intrinsic nonlinear acceleration. Our proof uses unperturbed updates and a genuine cyclic scan, at the cost of full width and different geometry. These are separate scope and mechanism changes, not a uniform improvement over every existing repository result.

In particular, the paper's normalized two-point example has background mismatch of order \(\mu_{\mathrm{paper}}/d\) and squared residual scale of order \(\mu_{\mathrm{paper}}^2/d\). Their ratio is of order \(1/\mu_{\mathrm{paper}}\), outside our small-offset slab. We do not claim to resolve that broader regime, noisy large-dataset acceleration, short-width convolutional acceleration, or an optimal dependence on \(\kappa\). The explicit powers and constants are conservative sufficient conditions.

Identity/zero initialization and optimization benefits of factorization are not new. Relevant foundational comparisons include [Arora, Cohen and Hazan, ICML 2018](https://proceedings.mlr.press/v80/arora18a.html), and [Wu et al., NeurIPS 2019, Eq. (3.1) and Theorem 4.3](https://arxiv.org/abs/1911.00645), which studies identity/zero initialization for whitened squared regression. [Yun, Krishnan and Mobahi, arXiv:2010.02501v3](https://arxiv.org/abs/2010.02501v3) concerns gradient-flow implicit bias, including single-sample short-filter and squared-regression results. These do not provide the discrete, margin-gated cyclic bound above. The new step is the cone amortization plus finite-error and scan control needed for an arbitrary conflicting cloud; a formalization of factorization identities alone would not establish the contribution.

## Literature coverage and limitations of the search

Both research and review independently surveyed the latest publicly available ICML 2025/2026, ICLR 2025/2026, and NeurIPS 2025/2026 material, and roughly October 2024–October 2026 arXiv submissions and revisions, then followed earlier primary references. The comparison above uses the strongest applicable baseline regardless of date. Search date: 24 October 2026 UTC.

Additional checks included [Tinaz, Xie and Soltanolkotabi, arXiv:2606.04476v1](https://arxiv.org/abs/2606.04476v1), concerning discrete imbalance in ReLU regression; [Gusev, Golikov and Yarotsky, arXiv:2610.20439v1](https://arxiv.org/abs/2610.20439v1), an ICLR 2027 submission rather than an accepted paper; and [Diederen, Rauhut and Terstiege, arXiv:2601.08547v1](https://arxiv.org/abs/2601.08547v1), on short convolutional gradient flow. None supplied the finite cyclic classification result used here. The original hyperbolic Perceptron fast bound was not treated as a reliable baseline without its [published correction](https://melanie-weber.com/static/errata.pdf).

A relevant NeurIPS 2026 item, “Classification at the Edge of Stability: Unifying Self-Stabilization and Convergence Rates,” [OpenReview VpiPrv9CUK](https://openreview.net/forum?id=VpiPrv9CUK), was visible at title/abstract level, but its full manuscript could not be accessed during repeated checks. No theorem-level exclusion of that source is claimed. This is a literature-access limitation, not evidence that it cannot contain related results.
