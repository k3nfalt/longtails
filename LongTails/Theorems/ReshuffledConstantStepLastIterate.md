# Constant-step random reshuffling: a large-step last-iterate guarantee

The [main Lean theorem](ReshuffledConstantStepLastIterate.lean) proves expected objective accuracy for the **raw final iterate** of constant-step random reshuffling. It applies to general nonlinear smooth convex finite sums, without strong convexity, bounded gradients, bounded iterates, or a uniform variance assumption away from a minimizer. Its contribution is a last-iterate guarantee in a step-size and finite-horizon regime previously covered by an averaged-output guarantee.

## Setup and execution

Let
\[
F(x)=\frac1n\sum_{i=1}^n f_i(x),\qquad n\ge1,
\]
where each component is convex and has an \(L_i\)-Lipschitz gradient. Public bounds satisfy
\[
0<L_{\rm avg}\le L_{\max},\quad
0\le L_i\le L_{\max},\quad \frac1n\sum_i L_i\le L_{\rm avg}.
\]
Assume a minimizer \(x_*\) exists, \(\|x_0-x_*\|\le D\), and
\[
\frac1n\sum_i\|\nabla f_i(x_*)\|^2\le\sigma^2.
\]
Here \(D,\sigma\ge0\) and the requested accuracy \(\varepsilon>0\) are public bounds. The algorithm receives component gradients at its queried points; it does not receive \(x_*\), component gradients at \(x_*\), or a function-value oracle.

These are the smooth-convex finite-sum assumptions of [Liu, COLT 2026, Theorem 1](https://proceedings.mlr.press/v336/liu26d.html), including heterogeneous component smoothness and variance at a minimizer. They are reused from the repository's existing reshuffling specification. The [chosen setup](../Setups/ConstantStepReshuffledSmoothConvex.lean) additionally makes the admissible algorithm family explicit: the frozen reshuffled-gradient execution with one positive constant step. This algorithm-family restriction is not a new objective assumption. The Lean statements hold in complete real inner-product spaces, hence in arbitrary finite dimension, with dimension-free constants.

Each epoch draws a fresh independent uniform permutation and performs all \(n\) component-gradient updates. The returned output is the point after the last update of epoch \(K\), with \(T=nK\) queries. There is no averaging, restart, regularization, batching, or skipped transition. The [algorithm definitions](../Algorithms/ConstantStepReshuffledGradient.lean) specify the step and epoch count; the [execution proof](../Proofs/ConstantStepReshuffledExecution.lean) identifies the output and proves the exact query count. Accuracy is the explicit integral of \(F(\mathrm{output})-F(x_*)\) under the algorithm's permutation law and the framework's oracle law. Exact-gradient replies make the latter irrelevant to the trajectory, and the proof establishes this rather than assuming it.

## Proved bound and explicit budget

Write \(H_m=\sum_{j=1}^m1/j\). The [finite-horizon supporting lemma `sum_gap`](../Proofs/ReshuffledHarmonicConvergence.lean) yields, for every \(K\ge1\),
\[
0<\eta,\quad \eta L_{\max}H_nH_T\le\frac1{536}
\quad\Longrightarrow\quad
\mathbb E[F(x_T)-F(x_*)]
\le \frac{2D^2}{\eta T}+66\eta H_nH_T\sigma^2.
\]
The finite permutation sum is converted into this expectation by the execution proof. In particular, the proof covers both interpolation \(\sigma=0\) and noninterpolation.

The public theorem uses the following concrete tuning:
\[
a=\frac{(L_{\max}\varepsilon+\sigma^2)D^2}{\varepsilon^2},\quad
h=1+\log n,\quad \ell=1+\log(n+2+a),
\]
\[
K=\left\lceil1+\frac{32768h a\ell}{n}\right\rceil,
\qquad
\eta=\frac1{12h\ell(536L_{\max}+132\sigma^2/\varepsilon)}.
\]
It proves \(\mathbb E[F(x_{nK})-F(x_*)]\le\varepsilon\) within exactly \(nK\) calls. The public Lean `budget` expands these quantities into one explicit line in setup parameters, combining the outer fractions. The [parameter proof](../Proofs/ReshuffledConstantStepParameters.lean) shows \(H_n\le h\), \(H_{nK}\le12\ell\), the required step cap, and an \(\varepsilon/2\) bound for each error term. It retains the rounding cost: \(nK\le2n+32768h a\ell\). Thus the oracle budget is
\[
O\!\left(n+
\left(\frac{L_{\max}D^2}{\varepsilon}+\frac{\sigma^2D^2}{\varepsilon^2}\right)
(1+\log n)\log\!\left(n+2+
\frac{(L_{\max}\varepsilon+\sigma^2)D^2}{\varepsilon^2}\right)\right).
\]
The additive full-epoch cost matters when \(n\) is large. The same formulas cover \(D=0\), \(\sigma=0\), and \(n=1\).

## Closest guarantees and improvement regimes

[Liu, COLT 2026](https://proceedings.mlr.press/v336/liu26d.html), latest checked [arXiv 2606.32005v1](https://arxiv.org/abs/2606.32005v1), Theorem 1 and Corollary 1, proves an **all-inner weighted average** bound at steps up to \(1/(6L_{\max})\). With constant steps its bound is
\[
\frac{6D^2}{\eta nK}+51\min\{\eta,nL_{\rm avg}\eta^2\}\sigma^2.
\]
Our theorem transfers the SGD-shaped branch to the unchanged algorithm's final iterate, with harmonic losses. It neither improves that averaged-output theorem nor recovers its sharper reshuffling noise branch.

[Liu and Zhou, ICML 2024](https://proceedings.mlr.press/v235/liu24cg.html), [arXiv 2403.07723v3](https://arxiv.org/abs/2403.07723v3), Theorem C.1, gives a smooth-convex raw-last bound under a component-step cap of order
\(1/[n\sqrt{L_{\rm avg}L_{\max}(1+\log K)}]\).
[Cai and Diakonikolas, ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/fea9f93f4cec99f65a8b4d575fc353a8-Paper-Conference.pdf), Theorem 1 and Corollary 2, develops a moving-anchor last-iterate analysis with a comparable small-step restriction. Heterogeneous refinements are already present in this literature; handling heterogeneous constants is not our novelty claim. The repository's existing [linear-decay last-iterate theorem](ReshuffledLinearDecayLastIterate.lean) also supplies a useful comparison, removing logarithmic losses while retaining the small-step scale and the rate
\[
O\!\left(\frac{\sqrt{L_{\rm avg}L_{\max}}D^2}{K}
+\left(\frac{L_{\rm avg}\sigma^2D^4}{nK^2}\right)^{1/3}\right).
\]

Our finite-horizon inequality, optimized over its permitted constant step, has the rate
\[
O\!\left(\frac{L_{\max}D^2 H_nH_{nK}}{nK}
+\sigma D\sqrt{\frac{H_nH_{nK}}{nK}}\right).
\]
Put \(A=H_nH_{nK}\). Relative to the displayed small-step bound, its deterministic term improves in the regime
\(n\gg A\sqrt{L_{\max}/L_{\rm avg}}\), and its noise term improves when
\(\sigma^2 K A^3\ll L_{\rm avg}^2D^2n\), up to universal constants. These are comparisons of proved upper bounds, not lower bounds on prior algorithms. For example, with common \(L=D=1\) and \(K\asymp\sqrt n\), interpolation gives \(\widetilde O(n^{-3/2})\) instead of \(O(n^{-1/2})\); with \(\sigma=1\), the new bound is \(\widetilde O(n^{-3/4})\) instead of \(O(n^{-1/2})\). Both use \(nK\) calls. For fixed \(n\) and sufficiently large \(K\), the older \(K^{-2/3}\) noise branch can be better. Geometry-dependent smoothness bounds can also be better on specially structured instances.

[Attia et al., NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/file/97335d45cab57ecb52727c4380ca14a4-Paper-Conference.pdf), Theorem 3 and Appendix H, already proves a one-pass interpolation last-iterate rate of order \(LD^2\log n/n\). Our novelty is therefore not a first one-pass interpolation improvement. That exchangeability argument does not extend directly across fresh epochs, and its conditional application epoch by epoch does not supply the \(1/K\) factor. [Vaidyan, Friedlander and Alacaoglu, ICML 2026](https://proceedings.mlr.press/v306/vaidyan26a.html), Theorem 3.1, treats IID proximal stochastic gradients; its conditional unbiasedness premise is unavailable inside a reshuffled epoch. Our unconstrained theorem does not resolve their full composite extension.

## Technical contribution and reduction checks

Position transpositions and nonexpansive gradient-map coupling are established tools. In particular, Liu 2026 Lemmas 2, 3, and 5 are direct antecedents; the reverse centered-loss estimate here is an elementary additional consequence of convex support. Moving convex-combination anchors are also established. The new contribution is their joint use with a terminally weighted, within-epoch history bound that closes the large-step raw-last analysis.

Use weights \(w_t=(H_T+H_{T-t})/(T-t)\), \(0\le t<T\), and adapted anchors satisfying
\[
w_tz_t=w_0x_*+\sum_{s=1}^t(w_s-w_{s-1})x_s.
\]
The permutation exchange simultaneously perturbs the iterate and its anchor. Its bias involves both sampled gradient moments and earlier moments from the same epoch. The proof controls the reverse centered loss
\(f_i(x)-f_i(x_*)-\langle\nabla f_i(x_*),x-x_*\rangle\), including the distinction between current-epoch and earlier-epoch labels. This makes the anchor's sampled moment controllable from population objective gaps.

The weighted history costs \(H_n\), rather than \(n\). The exact residual identity
\[
w_{s-1}-(T-s)(w_s-w_{s-1})=\frac1{T-s+1}
\]
absorbs the remaining population-gap terms. Keeping the negative Bregman remainder in the exact distance update is essential. The resulting coefficients are 134 in the gap absorption, 536 in the step cap, and 66 in the final noise term. Supporting modules prove the exchange, path and anchor stability, history sums, sampled moments, and telescoping from the actual update; none is a setup hypothesis.

Jensen only provides the averaged-output result in the easy direction. Substituting an adapted anchor for a minimizer in Liu's rooted argument invalidates its gradient cancellation. IID conversion does not apply to the conditional permutation law. Batching, averaging, regularization, or restart composition changes the output or the prescribed trajectory; those reductions do not establish this theorem for the unchanged constant-step method.

## Nonlinear instances and limitations

A concrete family is paired robust generalized-linear losses with heterogeneous quadratic terms:
\[
f_{j,\pm}(x)=\frac L4\langle w_j,x-x_*\rangle^2+
\frac L{2a^2}\log\cosh\!\left(a\langle v_j,x-x_*\rangle\pm b\right),
\qquad a>0.
\]
Take nonorthogonal unit \(v_j\) spanning \(\mathbb R^d\), \(d\ge2\), and \(\|w_j\|\le1\). Each component is convex and \(L\)-smooth, paired gradients cancel at \(x_*\), and root variance equals \((L/(2a))^2\tanh^2 b\). Choosing some \(w_j=e_1\) and others zero gives unbounded gradient variance along \(e_1\); the mean need not be globally strongly convex in orthogonal directions. The losses have interacting coordinates and varying Hessians. This family illustrates the standard class; it is not an additional restriction of the theorem.

No claim is made of minimax optimality, removal of the logarithms, admissibility of a horizon-independent constant multiple of \(1/L_{\max}\), acceleration, high-probability accuracy, or uniform superiority over every existing output rule. The theorem uses \(L_{\max}\) in its new bound, despite accepting the existing heterogeneous setup.

## Literature coverage and source limitations

Both Researcher and Reviewer independently surveyed the latest publicly available ICML/ICLR 2025–2026 and NeurIPS 2024–2025 editions, approximately October 2024–October 2026 arXiv submissions and revisions, and foundational citations before selecting this direction. The final targeted comparison was checked on 2026-10-05 UTC. Latest arXiv versions checked include Liu 2606.32005v1 (2026-06-30), Liu–Zhou 2403.07723v3 (2024-06-06), and Attia et al. 2507.11274v2 (2025-07-28); the accepted proceedings versions were separately checked.

Additional primary checks included Cai–Lin–Diakonikolas NeurIPS 2024 (epoch-averaged output with finer spectral constants), Liu–Zhou ICML 2025 (nonsmooth last iterates), Li 2609.04578v1 (strong convexity and additional Hessian conditions), and the author-hosted [The Missing Horizon in Random Reshuffling](https://andotheror.github.io/pdf/the-missing-horizon-in-random-reshuffling.pdf) (all-inner average; date and acceptance status unverified). None supplies the stated general-convex multi-epoch raw-last guarantee. The full manuscript of Kim–Cha–Yun's September 2026 *The Phase Transition in Random Reshuffling* was inaccessible; its [author description](https://chulheeyun.github.io/publication/kim2026phase/) concerns strong convexity and squared distance, but its exact theorem comparison remains unverified. Absence from a search or inaccessible work is not itself evidence of novelty.
