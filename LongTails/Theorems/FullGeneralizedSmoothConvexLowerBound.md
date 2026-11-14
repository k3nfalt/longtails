This result completes the randomized generalized-smooth lower bound from [PR #166](https://github.com/k3nfalt/longtails/pull/166) and [PR #168](https://github.com/k3nfalt/longtails/pull/168). It includes the classical accuracy term and removes their lower accuracy threshold and large-radius restriction. The square-root term, the combination of separate hard families, and the standard smoothing principle are not claimed as new discoveries. The initialization construction and its polynomial-dimension localization are credited to those earlier contributions.

The [main theorem](FullGeneralizedSmoothConvexLowerBound.lean) uses [GeneralizedSmoothConvexFull](../Setups/GeneralizedSmoothConvexFull.lean). Put

\[
s=\sqrt{L_0R^2/\varepsilon},\qquad q=L_1R.
\]

For \(L_0,R,\varepsilon>0\), \(L_1\ge0\), assume only the nontrivial accuracy range and sufficient dimension

\[
0<\varepsilon\le L_0R^2/16,\qquad
 d\ge\left\lceil2^{44}(1+q+s)^5\right\rceil.
\]

There is no lower bound on \(\varepsilon\) or \(q\); in particular \(L_1=0\) is included. For every adaptive randomized exact-gradient algorithm and every integer budget

\[
0\le b\le\left\lfloor\frac{s+q/\log(2+q)}{2^{23}}\right\rfloor,
\]

there is an admissible objective and oracle on which the actual `execute` output fails integrable expected objective accuracy \(\mathbb E[f(\hat x)-f(x^\star)]\le\varepsilon\). The instance may depend on the algorithm and budget, but not its realized seed. Queries and outputs are unrestricted. Every setup parameter is public, which strengthens the algorithms covered by the lower bound.

The objective assumptions are exactly convexity, a differentiable gradient with

\[
\|D\nabla f(x)\|\le L_0+L_1\|\nabla f(x)\|,
\qquad \|x^0-x^\star\|\le R.
\]

The admissibility predicate reuses [RadiusOnlyGeneralizedSmoothConvex](../Setups/RadiusOnlyGeneralizedSmoothConvex.lean) literally. There is no bound on the initial objective gap or gradient, no bounded-query or span assumption, and no prescribed update family. The oracle is an exact full gradient; the constructed hard oracles are deterministic. The public success criterion explicitly includes integrability; no measurability of arbitrary algorithm queries or output maps is silently imposed. Nonintegrable loss fails that criterion.

The matching upper comparison is retained in full. [FullGeneralizedSmoothUpper.expected_success](../Proofs/FullGeneralizedSmoothUpper.lean) proves that the existing [RadiusFreeSherpa algorithm](../Algorithms/RadiusFreeSherpa.lean), returning its accepted accelerated state, succeeds for the same expected criterion in

\[
\left\lceil64s+65536(1+q)\log(3+q)\right\rceil
\]

gradient calls. It invokes Sherpa with \(L_1^{\rm eff}=\max\{L_1,1/R\}\), a valid larger curvature parameter, so the existing positive-\(L_1\) analysis applies even when \(L_1=0\). This changes the upper rate only by universal constants. All trial and rejected queries are counted. Exact-gradient uniqueness makes the actual execution seed-independent, so its objective loss is integrable. This is a transfer of the known upper guarantee, not a new upper complexity result.

Consequently the full lower rate is

\[
\Omega\!\left(\sqrt{L_0R^2/\varepsilon}+\frac{L_1R}{\log(2+L_1R)}\right),
\]

against an upper rate \(O(s+(1+q)\log(3+q))\). The accuracy term has no logarithmic loss. The overall gap is at most two logarithmic factors in \(2+q\); when \(s\) dominates the upper initialization term, the rates match up to constants. The explicit constants are conservative, so this does not claim pointwise domination of the earlier integer budgets.

Three hard-instance branches prove the theorem. [FullGeneralizedSmoothTransient](../Proofs/FullGeneralizedSmoothTransient.lean) applies the inherited polynomial-dimension initialization construction at accuracy \(\max\{\varepsilon,L_0/L_1^2\}\) when \(q\ge2^{20}\). Its admissible objective class does not depend on accuracy, and success at a smaller accuracy implies success at the clamped one with the same integrability condition. This extends initialization hardness to arbitrarily small positive accuracy without changing that construction.

The accuracy branch is [MollifiedSmoothLowerBound](../Proofs/MollifiedSmoothLowerBound.lean). The repository's existing [smooth convex lower bound](SmoothConvexExpectedLowerBound.lean) cannot be imported directly: its squared dead-zone chain and wall have a Lipschitz gradient but need not have a differentiable gradient. [SmoothConvexMollification](../Proofs/SmoothConvexMollification.lean) and [MollifiedSmoothHardFamily](../Proofs/MollifiedSmoothHardFamily.lean) repair this regularity mismatch by compact convolution of the entire ambient hard objective. The result is smooth, remains convex, and preserves the global \(L_0\) gradient Lipschitz bound, hence belongs to the required class for every \(L_1\ge0\).

For a chain of length \(m=b+1\), the construction uses \(r=R/4\), \(a=r/\sqrt m\), dead-zone width \(\delta=a/(8m)\), and convolution radius \(\rho=\delta/64\). The smoothed minimum can be positive: its value is bounded by \(L_0\rho^2/2\), and a global quadratic-wall bound supplies an actual minimizer in the radius-\(R\) ball. This value is subtracted in every loss estimate. A coordinate threshold \(\delta/8\) preserves exact transcript equality under convolution. The same ambient kernel is used for every prefix and embedding. Auxiliary partial replies are total integrals used only for deterministic simulation; their integrands agree pointwise across matching prefixes and with the true integrable gradient on good histories. No probabilistic interpretation of partial replies on bad histories is assumed.

The hidden-coordinate count includes the final output as an observation. Its sufficient dimension is at most \(262144m^5\), which the public dimension formula dominates. [FinitePrefixExpectation](../Proofs/FinitePrefixExpectation.lean) integrates a finite-family inequality before selecting an instance, ensuring seed independence. For small parameters where the displayed budget is zero, [FullGeneralizedSmoothZeroQuery](../Proofs/FullGeneralizedSmoothZeroQuery.lean) uses opposite quadratic minimizers. Their pointwise average loss prevents simultaneous expected success, including when algorithm outputs are randomized. [FullGeneralizedSmoothParameters](../Proofs/FullGeneralizedSmoothParameters.lean) verifies the case split and a nonempty parameter regime.

The prior initialization family is nonlinear with interacting coordinates through its coupled conjugate regularizer. The accuracy family couples adjacent chain coordinates and a radial wall, with compact smoothing preserving the class. Quadratics serve only the zero-query boundary case; they are not a substitute for the general hard families.

| Comparison | What changes here |
| --- | --- |
| PR #166, research commit `0ed1e4a644756cf188d8f32e323bf2b8cb1f8ebd` | Its randomized initialization bound excluded small accuracy and required exponential dimension. The full theorem includes the accuracy term, all nonnegative \(L_1\), and polynomial sufficient dimension. Its initialization contribution is prior work. |
| PR #168, research commit `2c75d7f84bc9779b34405696dc43c610eae20a66` | The polynomial localization, chain, and hiding mechanism are reused. The new public statement removes \(q\ge2^{20}\) and \(\varepsilon\ge L_0/L_1^2\), and includes \(s\). Its auxiliary setup is preserved as a dependency, rather than weakening the reviewed prior assumptions. |
| [Descending Everest I, v2](https://arxiv.org/html/2610.21461v2), Theorems 3.7 and 4.10 | Gives the full deterministic radius-only complexity, with a stronger \(q/\sqrt{\log(2+q)}\) lower term and a value-and-gradient oracle. Here algorithms may be randomized, but access is gradient-only and the initialization lower term loses another square root of a logarithm. The classical accuracy term is already part of that prior theorem. |
| [Descending Everest II, v2](https://arxiv.org/html/2611.04171v2), Theorem 7.1 and Appendix D.2, Lemma D.4 | Supplies finite-sum randomized lower-bound and localization architecture. Its at-least-two-component, heterogeneity, and expected-stopping model is not the present single-objective fixed-budget model. The inherited polynomial localization comparison is unchanged. |
| [Garg, Kothari, Netrapalli and Sherif, NeurIPS 2021](https://proceedings.neurips.cc/paper_files/paper/2021/file/fa6c94460e902005a0b660266190c8ba-Paper.pdf), introduction, Theorem 1 and Lemma 1 | Credits the classical first-order square-root lower rate and studies randomized higher-order hardness using smoothing. Its radius-ball optimization criterion and higher-order guarantees are not identified with this setup. Compact smoothing and combining lower bounds are established techniques, not novelty claims here. |
| [Tyurin, ICML 2026](https://proceedings.mlr.press/v306/tyurin26b.html), [arXiv v2](https://arxiv.org/html/2508.06884v2), Theorem 4.3, Equation (13) | Its accelerated upper retains the same square-root accuracy term and an initialization bound involving supplied initial-gap and radius estimates. The present radius-only lower does not contradict that guarantee. |

Primary versions were refreshed on 14 November 2026: Everest I/II remain v2 of 5 November, and Tyurin remains v2 of 21 May. The earlier independent surveys covered recent ICML, ICLR, NeurIPS and arXiv results; this correction additionally checks the classical smooth branch and its exact regularity and oracle compatibility. The Everest papers are preprints, not claimed conference acceptances. The substantive generalized-smooth initialization novelty belongs to the earlier contributions; this PR completes their full-range statement and formal proof rather than claiming the elementary union of rates is a separate research breakthrough.

The result remains a fixed-budget, gradient-only lower bound. It does not prove hardness for value-and-gradient access, expected stopping cost, dimension-optimal constructions, or accuracies above the displayed nontrivial range. The polynomial dimension and numerical constants have considerable slack. No generic `Includes` assertion equates almost-sure and integrable expected success; the named Sherpa execution proof provides the upper comparison directly.
