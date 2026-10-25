# A full-Adam oracle separation for Muon

The [main theorem](MuonAdamSgdSeparation.lean) combines a dimension-free upper guarantee for batched exact-polar Muon with dimension-dependent lower bounds for full bias-corrected Adam and SGD on the same established nonlinear matrix objective class. The new mathematical contribution is the Adam lower bound. The Muon upper and SGD lower are existing repository results, reused with matched assumptions, criterion and oracle accounting; their relationship to the primary literature is detailed below.

This is a worst-case problem-class separation in an explicit regime. The Adam and SGD witnesses may differ. It does not assert that Muon beats both methods on every instance or in practical training runtime.

## Setup and exact algorithms

The [comparison setup](../Setups/SpectralSmoothAdamComparison.lean) reuses `BatchedSpectralSmooth` admissibility for square matrices, with noise scale equal to target accuracy. Public parameters are dimension $r\ge4$, $L>0$, $\Delta\ge0$, $\epsilon>0$, arbitrary initial matrix $X_0$, and $L\Delta\ge128\epsilon^2$.

Objectives are arbitrary differentiable, lower-bounded functions on $\mathbb R^{r\times r}$, with initial gap at most $\Delta$ and global spectral smoothness
\[
\|\nabla f(X)-\nabla f(Y)\|_*\le L\|X-Y\|_{\rm op}.
\]
The stochastic gradient oracle is jointly measurable, integrable and unbiased. In one fixed orthonormal basis $(b_i)$, its noise $Z_X=g(X,\xi)-\nabla f(X)$ satisfies square integrability and $\mathbb E\|Z_X^*b_i\|^2\le\sigma_i^2$, with $\sigma_i\ge0$ and $\sum_i\sigma_i\le s=\epsilon$, uniformly in $X$. This is an existential basis, not necessarily the coordinate-row basis. Sampling uses the shared abstract IID structure: measurability, independence and marginal laws are explicit. General probability spaces are permitted for the upper guarantee; a finite Rademacher oracle is used only for the lower witness. The class is not restricted to an invariant subspace or to two-feature objectives.

All compared methods return an independently selected uniform member of their queried iterates $X_0,\ldots,X_T$, with accuracy
\[
\mathbb E\|\nabla f(X_J)\|_*\le\epsilon.
\]
The probability measure is explicitly the product of the algorithm seed and oracle stream laws. Each method queries $B$ samples at each of the $T+1$ iterates, using exactly $N=B(T+1)$ calls. The final batch is queried and charged, although it is unnecessary for the returned iterates.

The constructed [Muon algorithm](../Algorithms/BatchedDirection.lean) uses the exact polar factor of the batch mean, zero momentum, batch size $65$, step $\eta=\epsilon/(2L)$, and $T=\lceil8L\Delta/\epsilon^2\rceil$. Its budget is
\[
K=65\bigl(\lceil8L\Delta/\epsilon^2\rceil+1\bigr).
\]
`allowedAlgorithm` enforces the batched polar update and uniform output family while leaving tuning to the algorithm and proof.

Adam uses both exponential moment histories, zero initial moments, bias corrections, and the entrywise update
\[
X_{t+1}=X_t-\eta\,\widehat m_{t+1}/(\sqrt{\widehat v_{t+1}}+\tau).
\]
Every constant $\eta>0$, $\tau\ge0$, integer $B\ge1$, and $0\le\beta_1,\beta_2<1$ satisfying $\beta_1^2\le\beta_2$ is allowed. Division by zero is zero; a zero second moment forces zero first moment in this regime. Tuning can depend on all public parameters and the horizon. `FollowsAdam` enforces the actual query and output rules for every reply history and seed. The [canonical implementation](../Algorithms/BatchedAdam.lean) and [compliance proof](../Proofs/AdamExecution.lean) establish nonvacuity. SGD permits every constant positive scalar step and positive constant batch size with the same output rule.

## Guarantee and strict improvement regime

Write $R=r-1$ and $Q=L\Delta/\epsilon^2$. The [new Adam lower proof](../Proofs/AdamSeparationLower.lean) shows that every permitted tuning and implementation has an admissible nonlinear instance on which success requires
\[
R\le64N^2\quad\text{or}\quad R L\Delta\le4096\epsilon^2N^3.
\]
Equivalently, $N\ge\min\{\sqrt{R/64},(RQ/4096)^{1/3}\}$. The disjunction is the exact roots-free Lean statement. The [reused SGD lower bound](../Proofs/AdamComparisonTuning.lean) requires $N\ge RQ/1728$. Muon succeeds throughout the class within $K$ calls.

Thus Muon's worst-case budget is strictly smaller than either comparator's necessary budget whenever
\[
R>\max\{64K^2,\ 4096K^3/Q,\ 1728K/Q\}.
\]
This regime is nonempty for each fixed $Q\ge128$, since dimension is unrestricted. At fixed $Q$, the proved dimension dependences are $O(1)$ for Muon, $\Omega(r^{1/3})$ for Adam and $\Omega(r)$ for SGD. The certified strict-comparison threshold is large. Neither the Adam exponent nor its joint accuracy/gap/noise dependence is claimed sharp; this is not an optimal Adam complexity theorem.

## New mathematical mechanism

Let $u=(1,\ldots,1)/\sqrt r$, $J=uu^\top$, $P=I-J$,
\[
a(X)=\langle J,X-X_0\rangle,\qquad b(X)=\langle P,X-X_0\rangle/(r-1).
\]
The hard objective and oracle are
\[
f(X)=\frac\ell2a(X)^2+c(r-1)\left(\sqrt{w^2+(b(X)-D)^2}-w\right),
\qquad g(X,\zeta)=\nabla f(X)+\epsilon\zeta J,
\]
with IID uniform signs $\zeta$, $\ell=L/2$, $c=4\epsilon/(r-1)$, $w=8\epsilon/L$, and $D=\Delta/(4\epsilon)$. The [instance proof](../Proofs/AdamSeparationInstance.lean) derives its gradient, smoothness, lower bound and initial gap; the [oracle proof](../Proofs/AdamSeparationModel.lean) establishes full admissibility. In a basis beginning with $u$, the noise profile has exactly one nonzero component, $\epsilon$.

This is a dense interacting-coordinate nonlinear family in arbitrary dimension. Adam preserves $X=X_0+aJ+bP$. The invariant slice is a lower-bound device, not a restriction of the upper class. A diagonal witness would fail: coordinate normalization could normalize its modes independently. Here rank-one noise enters both diagonal and off-diagonal histories, whose difference is the small quiet gradient.

The critical estimate controls the complete normalization history. At corrected history length $t\ge1$, $\beta_1^2\le\beta_2$ gives $|\widehat m|\le t\sqrt{\widehat v}$. If diagonal/off-diagonal observations differ by at most $c$, their normalized directions differ by $\delta$, with $|\delta|\le2t$ and $D_{\rm off}|\delta|\le c(1+t)$, including zero denominators.

Conditional on earlier samples, the current off-diagonal batch noise is symmetric, bounded by $\epsilon/r$, and has expected absolute value at least $\epsilon/(rB)$. A deterministic common denominator envelope yields
\[
\mathbb E_t|\delta_t|\le\frac{8crB(t+1)^2}{\epsilon}\,\mathbb E_t|U_t|,
\]
where $U_t$ is the off-diagonal Adam direction. This relates quiet movement to sustained noisy movement, without replacing Adam by SignGD or charging only its first update.

The exact updates are $a_{t+1}=a_t-\eta(rU_t+\delta_t)$ and $b_{t+1}=b_t-\eta\delta_t$. When $8cBT^2/\epsilon\le1/2$, absorption bounds quiet total variation by the full sum of stiff magnitudes. Uniform stationarity controls that sum, while the nonlinear valley requires expected quiet travel at least $D/4$. This gives the cubic cost alternative; failed absorption gives the quadratic alternative. [Finite-path bounds](../Proofs/AdamFinitePaths.lean), [execution correspondence](../Proofs/AdamSampledExecution.lean), and [law transport](../Proofs/AdamFiniteLaw.lean) connect this calculation to the actual matrix execution, independent selection seed and IID stream.

## Closest primary results and reduction checks

- Tao–Yu–Zhang, [arXiv:2605.06615v1](https://arxiv.org/abs/2605.06615v1), Theorem 4, supplies the closest known matrix Muon rate; it is publicly listed in [NeurIPS 2026](https://neurips.cc/Downloads/2026). Its Assumption 3b bounds the absolute spectral Bregman remainder. The Lean specification instead uses gradient nuclear Lipschitz continuity in spectral distance, a sufficient stronger formulation for that remainder inequality. Its Assumption 2b is a covariance PSD bound by a fixed matrix $\Sigma^2$; choosing an eigenbasis of $\Sigma$ implies the Lean row-profile condition with $s=\|\Sigma\|_*$. The row-profile formulation is not literally the same PSD assumption. Our fixed IID oracle stream is a specialization of the paper's conditional-oracle formulation. No novelty is claimed for these formulation differences or for the dimension-free Muon rate at $s=\epsilon$, which standard batching already yields. The paper's Theorem 3 is a vector SGD lower bound with batch size one. The matrix, all-constant-batch SGD guarantee used here comes from the existing repository [SeparationLower proof](../Proofs/SeparationLower.lean), rather than directly from that theorem, and is not a new contribution of this result.
- Hübler–Pethick–Sra, [arXiv:2606.14560v1](https://arxiv.org/abs/2606.14560v1), Theorems 3.5 and 3.7–3.8, and Shen et al., [arXiv:2505.23737v3](https://arxiv.org/abs/2505.23737v3), Sections 4.1–4.2, provide relevant stronger Muon and geometry-aware analyses, including heavy tails and spectral smoothness. Both are publicly listed for NeurIPS 2026. Their upper/minimax results do not provide the full-Adam lower bound here.
- Sun–Li–Lin, [arXiv:2609.24522v1](https://arxiv.org/abs/2609.24522v1), Section 3.3.2, gives an actual Adam nuclear-stationarity upper analysis of order $\sqrt{m+n}\max\{(\sigma^2 L\Delta/N)^{1/4},\sqrt{L\Delta/N}\}$ in its noise and smoothness parameters. Its stabilizer is inside the square root and tuned large. This is stronger than naive Frobenius-to-nuclear conversion, but an upper bound cannot establish an impossibility for Adam. We do not claim to improve that upper theorem.
- Wang et al., [ICLR 2026 associative-memory paper](https://proceedings.iclr.cc/paper_files/paper/2026/hash/3eec5006051d9544e717067de3220198-Abstract-Conference.html), Theorems 4.3–4.4 and Appendix I, compares first-step Muon/GD/SignGD and extends Muon alone to multiple steps. Ma et al., [arXiv:2601.13474v1](https://arxiv.org/abs/2601.13474v1), Theorems 1–2 and Appendix C, proves matrix-factorization Muon rates and a SignGD lower bound. Neither establishes the multistep, two-moment, batch-uniform Adam impossibility proved here. History-dependent leakage is the obstruction to simply transferring their sign-based arguments.

The strict moment regime $\beta_1^2<\beta_2$ appears in [arXiv:2407.08100, Theorem 1.2](https://arxiv.org/abs/2407.08100). No conditional-variance lemma from that paper is imported. Uniform selection over the whole trajectory is a standard convention, used for example in [Wang et al., NeurIPS 2023, Algorithm 1](https://proceedings.neurips.cc/paper_files/paper/2023/file/7ac19fdcdf4f311f3e3ef2e7ef4784d7-Paper-Conference.pdf). These precedents motivate the scope, but do not establish necessity for all Adam analyses.

Batching is optimized over in the lower bound and every sample is charged. Norm conversion, rescaling and composition with known Muon upper theorems yield only the known upper guarantee. They cannot yield this actual-Adam lower. Clipping or rotation-aware update changes would change the comparator family. The substantive extension is a lower bound for full Adam's evolving normalization beyond SignGD and first-step comparisons.

## Limitations and search coverage

The theorem meets the requested Muon-versus-Adam-and-SGD direction through the explicit strict regime above. It concerns exact-polar, zero-momentum batched Muon and constant-parameter Adam/SGD. Finite Newton–Schulz implementations, AdamW, nonzero moment initialization, $\beta_1^2>\beta_2$, learning-rate schedules, tail-only, last, best and averaged outputs are outside scope. Output averaging can cancel stiff noise on this witness, so that restriction is material. Oracle complexity excludes polar-factorization arithmetic cost. The specialization $s=\epsilon$ establishes a dimension separation, not a general noise-scaling theorem.

The Researcher and Reviewer independently surveyed primary ICML 2025–2026, ICLR 2025–2026, publicly available NeurIPS 2025–2026 material, roughly October 2024–October 2026 arXiv submissions/revisions, and foundational or stronger older work. Versions above were checked against those available on 25 October 2026 UTC. Coverage included practical Muon, matrix-factorization reassessments, curvature/river-valley models, rotation-based Adam analysis, spectral descent and counterexamples to broader Muon claims. Official proceedings verified ICML/ICLR status; the official NeurIPS 2026 Downloads listing was available before proceedings. Some individual NeurIPS virtual pages were blocked and an OpenReview endpoint required verification; accessible arXiv full texts and official ICLR proceedings supplied the theorem comparisons. This was a targeted search, not an exhaustive-literature or actual-conference-acceptance claim.
