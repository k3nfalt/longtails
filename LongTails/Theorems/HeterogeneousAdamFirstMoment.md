# Fixed-memory Adam with first-moment noise and a coupled AdaGrad head

The [main theorem](HeterogeneousAdamFirstMoment.lean) proves an expected stationarity guarantee for bias-corrected Adam with the fixed defaults `(β₁, β₂) = (0.9, 0.999)` on a coordinate-symmetric body, coupled to coordinate AdaGrad on a possibly asymmetric head. The contribution is a guarantee for this update family under finite-first-moment body noise, including atomic and degenerate distributions, with constants that do not involve inverse powers of Adam's supplied stabilizer. It is not an improvement in the best oracle complexity of the underlying problem class, a new ε exponent, or a claim that the hybrid optimizer itself is new.

The [setup](../Setups/HeterogeneousSymmetricFirstMoment.lean) and [algorithm](../Algorithms/HeterogeneousAdam.lean) specify the following model. Write `x=(x_body,x_head)`, with dimensions `b,h`, and `d=b+h≥1`. The objective is differentiable on the full Euclidean space, its gradient is globally L-Lipschitz, and `f(x₀)−f(x)≤Δ` for every x, with known positive L and Δ. Nonconvex objectives and interacting coordinates and blocks are allowed. There is no assumed bound on gradients or iterates.

A jointly measurable oracle `g(x,ω)` is integrable and unbiased under a probability law p. For each x, every body coordinate of `ζ(x,ω)=g(x,ω)−∇f(x)` has a distribution invariant under negation, and

\[
 \mathbb E_p\sum_{j\in\mathrm{body}}|\zeta_j(x,\omega)|\leq\sigma_b,
 \qquad \mathbb E_p\|\zeta_{\mathrm{head}}(x,\omega)\|^2\leq\sigma_h^2.
\]

The head squared norm is integrable. Body coordinates need not be independent, nor need body and head noise be independent. A nonnegative integrable random modulus K satisfies, on one common probability-one event, for all x,y and every body coordinate j,

\[
 |\zeta_j(x,\omega)-\zeta_j(y,\omega)|\leq K(\omega)\|x-y\|,
 \qquad \mathbb E_p K\leq M.
\]

Only the first moment of K is required. This global samplewise condition is stronger than an averaged Lipschitz condition and is essential to the present history proof. The sample stream has an abstract probability law P, with measurable IID coordinates of marginal law p. P is not prescribed as a product measure; product representations used in proofs are derived from independence. There is no finite-sample-space restriction.

These assumptions adapt two established lines of analysis: symmetry of the Adam field ([Dereich et al., v2, Lemma 4.4](https://arxiv.org/abs/2511.06675v2)), and stochastic regularity of state-dependent Adam observations ([Adam ODE analysis, v1](https://arxiv.org/abs/2511.04622v1), [earlier local convergence analysis, Theorem 2.5](https://arxiv.org/abs/2407.21078v1)). The integrable *global samplewise* modulus used here is a first-moment replacement for their stronger local moment regularity, not a claim that their hypotheses already imply our full setup. Exact coordinate symmetry and the global modulus are substantive restrictions. Bounded variance and unbiasedness on the head are standard stochastic-oracle assumptions; the AdaGrad potential argument builds on [Wang et al., COLT 2023, Lemma 4 and Theorem 2](https://arxiv.org/abs/2305.18471v2). No assumption states a descent or convergence conclusion.

For any positive horizon T, let

\[
 a=\sqrt{\frac{\Delta}{Ld}},\qquad
 \eta_b=\frac a{\sqrt T},\qquad \eta_h=a,\qquad
 r_0=1+2L\Delta+h\sigma_h^2.
\]

The body starts with zero moments and uses the usual bias-corrected Adam update, with a supplied δ>0 outside the square root. The head uses `r_{t+1,j}²=r_{t,j}²+g_{t,j}²`, initially `r_{0,j}=r₀`, and update `−a g_{t,j}/r_{t+1,j}`. The factor h in r₀ is retained: the setup bounds the head's total variance and does not assume a fixed coordinatewise variance allocation. The output is `x_J`, where J is uniform on `{0,…,T−1}` and independent of the sample stream. The implementation runs `execute` for exactly T oracle calls. Selecting this pre-update iterate requires no extra gradient query. There is no batching, clipping, projection, weight decay, or skipped transition.

The setup's `allowedAlgorithm` enforces this Adam/AdaGrad family, its fixed memory parameters and supplied δ, and uniform output selection. It leaves horizon, positive steps, and positive head initialization to the algorithm. This restriction identifies a method-specific claim; it does not confer problem-class optimality.

The supporting proofs give, with

\[
 R=1+d(L+M)\sqrt{\Delta/L},\quad
 N=b\delta+66\sigma_b+\sqrt h\,\sigma_h,\quad
 \ell=\log(10(1+\sigma_b)T),
\]

\[
 \mathbb E\|\nabla f(x_J)\|
 \leq 10^{19}\left[
 \frac{\sqrt{NR}\,\ell}{T^{1/4}}+
 \frac{\sqrt{R^2+hr_0R}\,\ell^2}{\sqrt T}\right].
\]

All expectations mean explicit integrals under the independent algorithm seed and original stream law. The claim concerns the expected norm, not its square, a high-probability event, or the last iterate. To obtain accuracy ε>0, define

\[
 A=1+d^2(L+M)^2\Delta/L,\qquad
 N_0=b\delta+\sigma_b+\sqrt h\,\sigma_h,
\]
\[
 Q=1+\frac{A N_0^2}{\varepsilon^4}
       +\frac{A+hr_0\sqrt A}{\varepsilon^2},\qquad
 T=\left\lceil10^{84}Q\,[\log(10^{84}(1+\sigma_b)Q)]^4\right\rceil.
\]

The public Lean `budget` expands these quantities in the setup parameters on one line. The proof retains the initialization and noise terms, uses `N≤66N₀`, and verifies the ceiling and logarithmic inversion. The constants are deliberately conservative and do not predict practical training horizons. There is no inverse-δ blowup, but δ appears directly in N₀: a fixed positive δ leaves an ε⁻⁴ term even in the noiseless case. No parameter-optimality or deterministic acceleration claim is made.

The new proof step controls the discrepancy between an adaptive Adam history and its frozen symmetric reference using the gradient itself as the scale. A symmetric observation has magnitude at least half the reference gradient with probability at least one half. After deleting the innovation responsible for a particular discrepancy, the remaining reference history supplies an inverse-square bound on its success event. The samplewise modulus then factors using independence *before* Cauchy–Schwarz, requiring `E K` rather than `E K²`. Failure events are charged using bounded normalized directions, without dividing by δ. Old history is removed only after freezing recent observations; removing it first would introduce an unjustified adaptive inverse-denominator estimate. A two-amplitude exchange gives quantitative field coercivity for symmetric atoms using first moments. Symmetric sign alignment itself and inverse-moment methods themselves are prior ideas.

The coupled proof first bounds full-vector movement noncircularly through normalized updates and logarithmic head accumulators. This movement controls the Adam tracking error and the head gradient-change potential together. The sharper terminal head accumulator bound is used only after the objective energy estimate. Treating the head as a separate fixed objective would omit body-induced gradient changes. Initial windows, old moments, rare failures, bias corrections, and all output indices are retained, including horizons shorter than the proof's logarithmic window. The central modules are [history tracking](../Proofs/AdaptiveHistoryTracking.lean), [finite-field coercivity](../Proofs/AdaptiveHistoryFinite.lean), [execution](../Proofs/HeterogeneousAdamExecution.lean), and [coupled descent](../Proofs/HeterogeneousAdamDescent.lean).

The closest comparisons delimit the claim:

| Primary result | Difference relevant here |
|---|---|
| [Dereich et al., 2511.06675v2, Theorem 1.2; Lemma 4.4; Proposition 4.8](https://arxiv.org/abs/2511.06675v2) | Their full theorem includes general C² objectives, not only quadratics, but uses bounded IID data, strong convexity, and bounded iterates. This result covers globally smooth nonconvex objectives and unbounded first-moment noise/trajectories, with exact body symmetry and the stated samplewise modulus. The classes are not related by simply deleting one hypothesis. |
| [2608.30382v1, Definition 4.1 and Theorem 7.1](https://arxiv.org/abs/2608.30382v1) | Stabilizer-uniform inverse-moment analysis is already present for RMSprop with bounded innovations, absolute Laplace nondegeneracy, local PL structure, and a stopped residual involving `(1−β₂)²`. Here relative symmetry permits atoms and zero-noise laws, with fixed `.999` and vanishing stationarity error; the additional samplewise regularity is explicit. |
| [Adapt or Forget, 2605.04269v1, Theorem 4.1 and Corollary 4.1](https://arxiv.org/abs/2605.04269v1) | The theorem allows unprojected Euclidean space; the distinction is its bounded sample gradients and persistent `G⁴(1−β₂)/δ⁴` residual, not an alleged universal compact-domain restriction. |
| [Jin et al., 2603.03099v8, Theorem 1 and Appendix E](https://arxiv.org/abs/2603.03099v8); [2609.37787v2, Theorems 4.2/B.2](https://arxiv.org/html/2609.37787v2) | These analyze second-moment noise and localization/self-normalization, including horizon-dependent second-moment memory. The latter permits generalized smoothness and uses `β₂=1−1/T` for its expectation guarantee. Our smoothness class is narrower; the first-moment symmetric body and fixed practical memory are the different regime. |
| [Memoryless nonlinear SGD, 2507.09093v2](https://arxiv.org/abs/2507.09093v2) | Symmetry already gives robust rates without this Adam history problem. An ε⁻⁴ exponent is not new for symmetric-noise optimization. |
| [LiuAdam, 2606.22326v1](https://arxiv.org/abs/2606.22326v1) | Heavy-tailed Adam-related theory already exists; its smoothing/randomized-step and bounded-gradient, higher-than-first-moment setting does not establish the present fixed-memory, bias-corrected result. |

Standard reductions are an important limitation of significance. Two-sample normalized methods already achieve ε⁻⁴ under a comparable symmetric first-moment model. On the all-symmetric subclass, this repository's [paired-query median result](MedianFirstMomentNonconvex.lean) has ε⁻³ complexity with its stronger oracle access; coordinate noise Lipschitzness gives an Euclidean modulus at most `√b M` for that comparison. Thus the present result is slower in ε than that stronger-oracle guarantee. Batching, clipping, or replacing short memory by a horizon-dependent accumulator can yield other known guarantees, but they do not prove convergence of these fixed `.9/.999` updates. A direct global Lipschitz estimate of normalization gives inverse-stabilizer factors; it does not yield the present uniform bound. The substantive exception sought here is to explain a practical update family under a noise regime outside the strongest applicable fixed-memory analyses, rather than to outperform every optimizer.

A nonlinear family demonstrating scope is

\[
 f(x)=\tfrac12\|x\|^2+\lambda\sum_i(1-\cos((Bx)_i)),
\]

with λ≥0 and a dense matrix B coupling body and head. It is globally smooth with `L≤1+λ‖B‖²`, lower bounded, and can be nonconvex. Add to each sample loss `Z sin(uᵀx_body)+Wᵀx_head`, where u is dense, Z is symmetric with finite first moment, and W is bounded and centered but skew. Z and W may be dependent. Then `σ_b=‖u‖₁ E|Z|`, a valid coordinate modulus is `K=‖u‖∞‖u‖|Z|`, and the head has bounded variance. Choosing an eventual survival tail proportional to `1/[t(log t)²]` gives no moment of order `1+q`, for any q>0. This family has interacting coordinates and unbounded population gradients; it is not a scalar or quadratic substitute. For example, take b=2, h=1, λ=1, B=(1,1,1), and u=(1,1). At x=(π/3,π/3,π/3), the Hessian is I−BᵀB, with eigenvalue −2 along (1,1,1); f≥0 and L=4 suffices. It proves nontrivial scope, not that LLM noise follows this law.

Numerical motivation preceded formalization. On [Pythia-70m-deduped at step 100000](https://huggingface.co/EleutherAI/pythia-70m-deduped/tree/step100000) with [WikiText-2-raw-v1](https://huggingface.co/datasets/Salesforce/wikitext), diagnostics used 512 minibatches of size 32, sequence length 128, split-sample centering, and 300 matched symmetric bootstrap replicates. Among the tested randomly sampled body coordinates, 5.0% exceeded the matched 95% symmetric-null threshold (QKV modules ranged from 0% to 18.75%, MLP up-projections from 0% to 12.5%, and MLP down-projections were 0%); input-embedding and output-head fractions were 57.1% and 87.5%. These are selected coordinates, not an exhaustive coordinate test. Embeddings/output-head directions were substantially more skew; this led to the heterogeneous setup rather than full-network symmetry. These local tests neither certify exact symmetry at all parameter values nor establish infinite variance, the global modulus, or global smoothness.

A separate 200-step continued-pretraining check used batch size 16, sequence length 128, and three fresh seeds (91914–91916). Validation losses were:

| Optimizer | Three runs |
|---|---|
| Full Adam | 4.05559, 4.04890, 4.05049 |
| Adam body / AdaGrad head | 3.99470, 3.99086, 3.99532 |
| Adam body / SGD head | 4.00088, 4.00089, 4.00133 |

Experiments used FP32 and eager attention. Validation used the same 32 batches of 16 sequences (512 sequences, length 128) across runs, with seed 123417; the three training seeds vary minibatches, not the validation sample. The head partition contained the input and output embedding matrices; all other trainable parameters formed the body. Body/head learning rates were `3e-5/3e-5` for full Adam, `3e-5/1e-4` for Adam/AdaGrad, and `1e-4/1e-4` for Adam/SGD. The Adam defaults were `.9/.999` with stabilizer `10⁻⁸`; the AdaGrad head began with squared accumulator `10⁻¹⁶`, without an additional denominator offset. There was no clipping or weight decay. Tuning was limited and an unsuccessful initial SGD-head tuning was retained in the experiment record. These are feasibility diagnostics, not evidence of optimizer superiority or a test of the enormous theorem horizon. The practical head initialization and learning rates differ from the sufficient tuning above. Adverse evidence must also be retained: 2606.14259v1 reports that adapting the head accounts for 69% of its Adam–SGD gap, with full Adam strongest in that setting. Our small continued-training check does not overturn that result. Hybrid-head empirical motivation also predates this result ([2606.14259v1](https://arxiv.org/abs/2606.14259v1), [2609.37535v1](https://arxiv.org/abs/2609.37535v1)).

Working experimental artifacts are outside the repository at `/tmp/longtails-llm-20261019-0658/`: `pythia_allblocks_symmetry.py` (raw collection), `allblocks_symmetry_analysis.py`, `allblocks-symmetry-analysis.json`, `hybrid_pythia_replicates.py`, and `hybrid-pythia-replicates.json`. These local paths record this run and are not permanent public artifact hosting.

Literature screening began on 2026-10-19 UTC and independently targeted the publicly available 2025/2026 ICML, ICLR, and NeurIPS editions, approximately October 2024–October 2026 arXiv submissions/revisions, and stronger older references. This was a targeted search, not an exhaustive survey. Version-specific links above identify the mathematical baselines. The NeurIPS 2026 status of 2609.37787 is confirmed by the [official accepted-paper downloads list](https://neurips.cc/Downloads/2026); the other arXiv links alone are not claims of conference acceptance. The full text of [Median-of-Means under Structured Heavy-Tailed Noise, El Bajdali, Shamir, Horváth, and Gorbunov (NeurIPS 2026)](https://openreview.net/forum?id=vGEUrQdO7l) was inaccessible during screening (HTTP 403); its abstract was not used to support novelty of this Adam guarantee. The note's claim remains conditional on the stated exact model: approximate symmetry, Markov sampling, generalized smoothness, tail-adaptive unknown tuning, practical dimension constants, last-iterate accuracy, and sharper deterministic rates are not established here.
