This result addresses the initialization cost of minimizing a convex function whose curvature grows with its gradient. A distance bound to a minimizer does not bound the initial gradient polynomially under generalized smoothness. The question is whether randomization removes the nearly linear dependence on the dimensionless radius \(q=L_1R\), even when there is no stochastic gradient noise.

The [Lean theorem](RandomizedGeneralizedSmoothTransientLowerBound.lean) proves a lower bound for [GeneralizedSmoothConvexTransient](../Setups/GeneralizedSmoothConvexTransient.lean). Its admissible instances reuse exactly the objective and oracle conditions of [RadiusOnlyGeneralizedSmoothConvex](../Setups/RadiusOnlyGeneralizedSmoothConvex.lean): a convex function on Euclidean space, an exact gradient oracle, a differentiable gradient satisfying

\[
\|D\nabla f(x)\|\le L_0+L_1\|\nabla f(x)\|,
\qquad \|x^0-x^\star\|\le R.
\]

There is no bound on the initial objective gap, gradient, query radius, or algorithm span. The algorithm may know all setup parameters, including \(R\) and the target accuracy. No update family or output-selection restriction is imposed. Success means an integrable objective gap with expectation at most \(\varepsilon\), over the algorithm's random seed and the oracle seed law. The constructed oracle is deterministic.

For positive parameters, assume

\[
q\ge 2^{20},\qquad L_0/L_1^2\le\varepsilon\le L_0R^2/16,
\qquad d\ge\left\lceil2^{20}(1+q)^8e^{2\sqrt q}\right\rceil.
\]

For every randomized adaptive algorithm and every integer budget
\[
0\le b\le\left\lfloor\frac{q}{4096\log(2+q)}\right\rfloor,
\]
there is a fixed admissible instance on which its output after `execute` fails the expected-accuracy criterion. The hard instance can depend on the algorithm and budget, but not its realized seed. The proof supplies a finite family with mean loss at least \(3\varepsilon/2\) for every seed, then integrates this inequality before choosing a witness. It also covers nonintegrable loss, which fails the explicitly stated success criterion. Zero queries are included. `valid_nonempty` checks a concrete valid parameter choice.

The known [RadiusFreeSherpa algorithm](../Algorithms/RadiusFreeSherpa.lean), with its accepted accelerated iterate as output, uses at most
\[
\left\lceil64\sqrt{L_0R^2/\varepsilon}
 +32768(1+q)\log(2+q)\right\rceil
\]
gradient calls. The existing [upper theorem](RadiusFreeGeneralizedAccelerated.lean) is unchanged. [RadiusFreeSherpaExpected.expected_success](../Proofs/RadiusFreeSherpaExpected.lean) establishes its expected-accuracy guarantee for this precise setup by proving that exact gradients make the actual execution independent of all seeds. Every trial and rejected query remains counted. This is a transfer of a known upper bound, not a new upper-complexity claim. Since \(\sqrt{L_0R^2/\varepsilon}\le q\) in the stated regime, the upper and lower bounds differ by at most two logarithmic factors. No generic implication from an almost-sure guarantee to integrability is assumed.

The construction and its mechanism are in [HardDual](../Proofs/GeneralizedSmoothHardDual.lean), [HardChain](../Proofs/GeneralizedSmoothHardChain.lean), [SmoothedChain](../Proofs/GeneralizedSmoothSmoothedChain.lean), [Localization](../Proofs/GeneralizedSmoothLocalization.lean), and [HardOracle](../Proofs/GeneralizedSmoothHardOracle.lean). For each budget, a chain of length \(m=b+1\) is built by conjugating a coupled convex regularizer on a weighted simplex. Writing \(Z=\sum_i z_i\), the regularizer combines a nonlinear function of \(Z\) with a perspective term \(Z\sum_i r(z_i/Z)\). Its curvature controls every signed direction through the norm of the dual vector. Thus the construction is nonlinear and has interacting coordinates; scalar or quadratic calculations are not the theorem's scope.

A feasible mass-transfer argument gives exact inactivity of unrevealed coordinates. Compact convolution in a fixed chain space makes the gradient differentiable while retaining exact prefix identities and the objective gap. All prefixes retain the same chain length, regularizer, shifts, and convolution kernel. The construction is then embedded into the full ambient space and joined convexly to a common quadratic wall. The key localization estimate bounds the new gradient derivative by
\[
L_{0,\mathrm{sm}}+10a+2L_{1,\mathrm{sm}}\|\nabla F\|,
\]
using the minimizer's radius to control the angle between the original gradient and the radial wall gradient. Taking the original chain constants as \(L_0/4,L_1/4\), smoothing yields \(L_{0,\mathrm{sm}}=L_0/3,L_{1,\mathrm{sm}}=L_1/3\); with \(a=L_0/32\), the bound fits the required original constants. The exponentially large peak gradient affects the localization radius and required dimension, not the claimed curvature constants.

Outside that radius every embedding returns the same full-dimensional radial gradient. Inside, distinct coordinate embeddings and exact prefix coupling bound the bad fraction by one half. The final output is an observation in this count. [FinitePrefixExpectation](../Proofs/FinitePrefixExpectation.lean) integrates the finite-family inequality without assuming measurable algorithm queries or choosing the instance after observing a seed. [TransientLowerBound](../Proofs/GeneralizedSmoothTransientLowerBound.lean) connects the result to the repository's actual `execute`, oracle, and `NonConvergence` quantifiers.

The closest comparisons, checked against versions available on 13 November 2026, are:

| Primary result | Comparison |
| --- | --- |
| [Descending Everest, Part I, v2, 5 November 2026](https://arxiv.org/html/2610.21461v2), Theorems 3.7, 4.8, 4.10 and Section 5 | Establishes the initialization phenomenon and deterministic first-order lower bounds. Its lower oracle supplies values and gradients and therefore also implies deterministic gradient-only hardness. The present contribution extends initialization hardness to arbitrary randomized gradient-only algorithms. Its \(q/\log q\) term is weaker than the deterministic \(q/\sqrt{\log q}\) term; the improvement is algorithmic scope, not that numerical rate. |
| [Descending Everest, Part II, v2, 5 November 2026](https://arxiv.org/html/2611.04171v2), Theorem 7.1 and Appendix D.2, Lemma D.4 | Provides randomized finite-sum hardness, finite-family hiding, and radial localization architecture. The finite-sum theorem has \(n\ge2\), componentwise smoothness, heterogeneity, and a different stopping-cost model. Its global-Hessian localization estimate does not retain the desired generalized-curvature constants when the peak gradient is exponentially large. |
| [Tyurin, ICML 2026](https://proceedings.mlr.press/v306/tyurin26b.html), [arXiv v2, 21 May 2026](https://arxiv.org/html/2508.06884v2), Assumptions 2.1/2.3, Theorem 4.3, Equation (13), proof in E.2.1 | Uses the same Hessian-growth and convex-minimizer assumptions. Its accelerated upper bound has an initialization term depending on an initial-gap bound through \(\Gamma_0\ge2\Delta/R^2\) and a supplied radius bound. It is optimal in the small-accuracy regime. Our lower bound concerns initialization-dominated accuracy and does not improve or contradict that upper guarantee. |
| [Liang and Luo, arXiv v1, 15 October 2026](https://arxiv.org/html/2610.21692v1), Theorem 4.5 and Corollary 4.6 | Establishes randomized nonconvex lower bounds for expected gradient-norm stationarity, with an initial-gap bound and a gradient oracle having bounded central moments. Equation (10) starts with \(-\phi(t)=-1-\tanh(t)\); its second derivative \(2\operatorname{sech}^2(t)\tanh(t)\) is negative for \(t<0\). That construction therefore does not directly establish convex objective-gap hardness with a minimizer-radius bound. This observation does not rule out every modification of their construction. |
| [Chen et al., ICML 2023](https://proceedings.mlr.press/v202/chen23ar.html), Proposition 1(2), Equation (6) | The exponential local gradient-growth estimate already yields the small-radius smoothing control used here. That estimate and smoothing alone are not claimed as novel. |

Part I and Part II are cited as arXiv preprints, not verified conference acceptances. Tyurin's conference status is verified through the official ICML proceedings. The lower-bound claim is not inferred merely from an absent search hit or an earlier repository proposal.

Several standard reductions do not supply the claimed result. A globally smooth lower bound gives only the accuracy term \(\sqrt{L_0R^2/\varepsilon}\), which can remain constant in this regime while \(q\) grows. Full-gradient simulation from two finite-sum component queries is legitimate, but componentwise generalized smoothness need not survive averaging because gradients cancel. For Part II's Family X at \(n=2\), direct examination of the average exhibits either an extra \(\sqrt T\) factor in the generalized coefficient or an exponential additive smoothness cost at the relevant chain length. Shrinking its extra one-dimensional term does not remove the chain obstruction. This rules out the direct averaging reduction examined here; it is not a claim that every conceivable reduction is impossible. Compact smoothing alone also leaves unrestricted queries able to reveal the hidden coordinates. Preserving convexity, exact exterior replies, and gradient-dependent curvature simultaneously is the additional localization step.

The assumptions on the objective and oracle are established generalized-smooth convex assumptions, inherited without strengthening. The added numerical restrictions select the initialization-dominated regime and sufficient dimension for this lower construction. They are restrictions of the result, not claimed intrinsic necessities: constants and dimension have substantial proof slack. The accuracy lower bound is used to compare the upper and lower rates; the upper accuracy bound supplies a nontrivial target and the exterior-output gap. No initial-gap restriction or oracle-error hypothesis is added.

The result concerns fixed query budgets and a gradient-only oracle. It does not establish a randomized value-and-gradient lower bound, a bound for algorithms controlled only in expected stopping cost, dimension-optimal hardness, or matching constants. Its dimension requirement is very large, and it does not cover the small-accuracy regime outside the displayed interval. The new setup reuses the original admissibility definition directly; no `Includes` assertion equating its expected criterion with the original almost-sure criterion is made. The precise claim is randomized gradient-only initialization hardness, matching the existing fixed-budget upper bound up to logarithmic factors in the stated regime.
