# Near-accelerated oracle complexity at inverse-polylogarithmic relative precision

[Main Lean theorem](NearAcceleratedPolylogPrecisionRelativeErrorConvex.lean) · [reused setup](../Setups/SharpRelativeErrorSmoothConvex.lean) · [underlying oracle specification](../Setups/RelativeErrorSmoothConvex.lean) · [algorithm](../Algorithms/SharpDistanceEnvelope.lean)

## Result and scope

Let \(f\) be convex and globally \(L\)-smooth on an arbitrary finite-dimensional real inner-product space, with a global minimizer \(x_\star\) satisfying \(\|x_0-x_\star\|\le R\). The same proof supports the complete inner-product spaces permitted by the reused specification. The oracle returns only a vector \(v\) obeying

\[
\|v-\nabla f(x)\|\le\alpha\|\nabla f(x)\|.
\]

The condition holds for every query, call index, and oracle seed. Replies can be biased, discontinuous, and adversarial; no independence, moment bound, or function-value access is assumed. The public inputs include \(L,R,\varepsilon,\alpha,x_0\); the minimizer and its value are unavailable to the algorithm. No algorithm-family restriction is imposed. We reuse the existing specification exactly, without changing it or adding a duplicate.

Write

\[
T=LR^2/\varepsilon,\qquad s=1+\log(2+T),\qquad B=33s.
\]

For \(L,\varepsilon>0\), \(R\ge0\), and

\[
0\le\alpha\le\frac{1}{100B^{12}},
\]

`result` constructs `distanceEnvelopeOutput` and proves \(f(\mathrm{output})-f(x_\star)\le\varepsilon\), almost surely under the execution measure, within the following number of physical gradient-oracle calls:

\[
\left\lceil
32768B^{16}(1+\log B)(2+T)^{\frac12+
\frac{\log(16384(1+\log B))}{32\log(32s)}}
\right\rceil.
\]

The proof is pointwise in all oracle seeds, stronger than the specification's almost-sure criterion. There is no stochastic expectation interpretation or hidden sample-space restriction. The bound is

\[
\sqrt T\exp\!\left(O\!\left(\frac{\log T\,\log\log\log T}{\log\log T}\right)\right)
=T^{1/2+o(1)}
\]

as \(T\to\infty\), at fixed inverse-polylogarithmic relative precision. It is **not** a \(\sqrt T\operatorname{polylog}T\) bound. The oracle-call model does not charge arithmetic or representational bit complexity; the statement about \(O(\log\log T)\) relative-accuracy bits is only an interpretation of the tolerance's magnitude.

The setup is the standard relative-error smooth-convex problem, with a specified accuracy-dependent oracle tolerance. Its objective class is not narrowed to quadratics, separable functions, strong convexity, bounded gradients, or fixed dimension. For example, with nonorthogonal vectors \(a_j\), positive weights \(w_j\), and any matrix \(C\),

\[
f(x)=\sum_jw_j\log\cosh\langle a_j,x-x_\star\rangle
       +\frac{\lambda}{2}\|C(x-x_\star)\|^2,\qquad\lambda\ge0,
\]

has interacting nonlinear coordinates, a minimizer at \(x_\star\), and smoothness at most \(\sum_jw_j\|a_j\|^2+\lambda\|C\|_{\rm op}^2\). Rank deficiency and nonunique minimizers are allowed. This illustrates the already established problem class; no such representation is assumed in Lean. Dimension enters through supplied problem parameters such as \(L\), with no separate dimension factor in the call count.

## Algorithm and technical contribution

Set \(b=\lceil32s\rceil\), \(q=4b^{32}-1\), \(D=\lceil\log(2+T)/\log q\rceil\), and

\[
n=\lceil4096b^{16}(1+\log b)\rceil,\quad
\theta=\frac1{4b^{16}},\quad
\tau=\frac1{8(D+1)},\quad
\beta_i=\frac{1+i/(D+1)}{100b^{12}}.
\]

The algorithm recursively approximates gradients of Moreau envelopes with smoothness \(L/q^i\). Each simulated gradient calls a warm solver for \(n\) steps, resets its two states to the warm output, and runs \(n\) accelerated refinement steps. It returns the **last primal iterate** of the refinement, rather than its arithmetic average. The final output descends through \(D\) such approximate proximal solves to recover a point for the original objective. Exact proximal points and envelope values occur only in the analysis; they are not oracle operations.

The main new estimate is a nearly unit distance gain with logarithmic dependence on the permitted gain slack. For an inner objective \(f_i\), let

\[
h(x)=f_i(x)+\frac\mu2\|x-c\|^2,\quad p=\arg\min h,\quad
\phi(x)=h(x)-h(p)-\frac\mu2\|x-p\|^2.
\]

Convexity makes \(\phi\ge0\), and \(\nabla\phi(x)=\nabla f_i(x)-\nabla f_i(p)\). For the actual discrete accelerated update, the shifted storage

\[
V=\phi(x)+\frac\mu2\|z-p\|^2
\]

retains a negative \(\|\nabla\phi\|^2\) term. This absorbs the state-dependent part of the relative error and yields

\[
V_{k+1}\le(1-\theta)V_k+
 \frac{\theta\mu}{2}(1+\tau)^2\beta_i^2\|c-p\|^2.
\]

A positive linear recurrence connecting the primal and momentum states transfers this nearly unit radius gain to the last primal state. The reset makes \(V_0=h(x_{\rm warm})-h(p)\) exactly. With \((1-\theta)^n\le\tau^2/4096\), the proved inner guarantee is

\[
\|x_n-p\|\le(1+2\tau)\beta_i\|c-p\|,
\qquad h(x_n)-h(p)\le2\mu\beta_i^2\|c-p\|^2.
\]

The second inequality is proved from the shifted storage together with the distance bound. Converting distance to objective error using smoothness alone would introduce a harmful condition-number factor. The resulting recursive oracle precision increases from \(\beta_i\) to at most \(\beta_{i+1}\); recovery multiplies gaps by \(1+4\beta_{i+1}^2\), whose total product is at most two.

Each level costs exactly \((2n)^i\) physical calls per simulated gradient. All warm and refinement calls and all descending recovery solves are included: total recovery cost is at most \(2(2n)^D\). [Budget proofs](../Proofs/SharpDistanceBudget.lean) bound this by the displayed single public formula, including ceilings and the final extra depth factor. [Execution proofs](../Proofs/SharpDistanceExecution.lean) retain the physical call offset through every nested plan; [the guarantee](../Proofs/SharpDistanceGuarantee.lean) connects the calculation to `execute`. The framework executes the full public budget K: after the finite plan finishes, any remaining calls query the fallback point x0 and leave the returned output unchanged. These padding calls are included in K; they are not omitted from the oracle count.

## Closest comparisons and novelty boundary

The contribution is an improved precision–oracle-complexity tradeoff, not a new problem definition, fixed-method restriction, or formalization of a known rate.

* [Vasin–Gasnikov, arXiv:2603.12376v1](https://arxiv.org/abs/2603.12376v1), Theorems 7.2 and 9.3, gives regularization-based convex guarantees of order \(T^{1-\gamma}\log T\) with relative tolerance of order \(T^{-\gamma}\), \(0\le\gamma\le1/2\). This does not provide a near-half exponent at fixed inverse-polylogarithmic tolerance. Theorems 6.1 and the proofs in Sections 7 and 9 supply the relevant strongly convex and reduction comparisons. This is a preprint; conference acceptance is not asserted.
* [Vasin–Tyurin–Gasnikov, arXiv:2610.24863v1](https://arxiv.org/abs/2610.24863v1), Theorems 3.1–3.3, gives the strongly convex factor \(\max\{\sqrt\kappa,9\alpha^2\kappa\}\), with an additive-error floor when present. Its adaptive line search also uses function values. Ordinary regularization gives a substantially worse tolerance-dependent convex bound in the regime here. Remark 3.1 acknowledges stronger existing LongTails guarantees. This is also treated as a preprint.
* The stronger direct baseline is the existing [PolylogPrecisionRelativeErrorConvex](PolylogPrecisionRelativeErrorConvex.lean), under the **identical specification**, with displayed bound \(\widetilde O(T^{5/8})\). Comparing only to that displayed exponent would overstate novelty. Retuning its established averaged-transfer proof gives exponent **\(12/23\)**, up to logarithmic factors, at the same precision order. Indeed, with \(\beta\asymp b^{-p}\), \(q\asymp b^a\), \(\tau\asymp b^{-1}\), and inner length \(b^c\), that proof requires \(a\le4p-2\) and \(c\ge a/2+1\). At \(p=12\), the limiting ratio is \(c/a=12/23\). This is a standard-retuning calculation from the prior proof, not a separately formalized new theorem or a lower bound on all algorithms. The present logarithmic refinement cost removes this fixed polynomial overhead.
* The existing [RecursiveRelativeErrorConvex](RecursiveRelativeErrorConvex.lean) already obtains \(T^{1/2+o(1)}\), but its [specification](../Setups/RecursiveRelativeErrorSmoothConvex.lean) requires \(\alpha\le e^{-8(1+\sqrt{\log(2+T)})}/100\). The new theorem permits the much larger fixed inverse-polylogarithmic tolerance. This does not imply that its finite-call bound improves the earlier result when that stricter precision is available.
* [Gürbüzbalaban, arXiv:2309.11481v5](https://arxiv.org/abs/2309.11481v5), Proposition 5.3, Corollary 5.4, and Theorem 5.6, provides nonlinear accelerated robustness and cumulative/averaged objective-gain estimates. Those stated estimates do not yield the nearly unit last-distance gain with logarithmic slack cost needed here. The generic certificate uses a positive-semidefinite quadratic storage plus a nonnegative objective-gap term; the shifted storage above has an indefinite quadratic part whose nonnegativity comes instead from convex subtraction. This rules out direct substitution into that stated certificate, not every possible alternative control-theoretic derivation.

Batching arbitrary biased relative replies does not reduce their worst-case relative error. Clipping or regularization alone does not produce the nearly lossless recursive transfer. The old warm solver and Moreau recursion are reused; their novelty is not claimed. The new discrete distance/recovery certificate and its full recursive complexity consequence are the substantive step beyond those reductions.

## Limitations and literature audit

The explicit constants and crossover are enormous. Even ignoring polynomial-logarithmic prefactors, the excess exponent in the displayed bound falls below \(1/46=12/23-1/2\) only around \(\log s\approx14.7\); this is an indicative asymptotic scale, **not** a proved finite-runtime crossover. No practical improvement, uniform finite-parameter dominance, fixed-positive-\(\alpha\) acceleration, or optimality of the subpolynomial factor is claimed. The exact-gradient \(\sqrt T\) benchmark explains the polynomial exponent, but does not prove that the remaining overhead is necessary. Parameters are known; no adaptivity improvement is claimed.

The literature comparison was refreshed on 2026-11-04 UTC. Researcher and Reviewer independently searched ICML 2025/2026 proceedings, ICLR 2025/2026 official proceedings/OpenReview, NeurIPS 2025/2026 official programs/downloads, and roughly November 2024–November 2026 arXiv submissions and revisions, following older foundational references. This is recorded coverage, not an exhaustive-absence claim. The version-specific links above identify the primary statements used.

Additional checked distinctions include [arXiv:2509.13628v3](https://arxiv.org/abs/2509.13628v3) (biased sub-Gaussian risk-sensitive guarantees), [arXiv:2512.17598v1](https://arxiv.org/abs/2512.17598v1), Theorem 6 (existential input-to-state gain), and [arXiv:2610.24373v1](https://arxiv.org/abs/2610.24373v1), Theorem 6 (local input-to-state guarantees). Their stated assumptions or gain conclusions do not give the required uniform adversarial near-one transfer. The accepted [ICML 2026 error-feedback paper](https://proceedings.mlr.press/v306/thomsen26a.html) uses compression and exact residual updates involving exact gradients; that stronger information access is unavailable here.

The final journal text of the Mathematics of Operations Research paper associated with arXiv:2309.11481 was also inaccessible; the comparison above uses its public v5 manuscript. The final Springer full text of the JOTA paper associated with [arXiv:2310.00506v1](https://arxiv.org/abs/2310.00506v1) was inaccessible; the public arXiv version was checked. A claim that every detail of the final journal revision was verified would be unwarranted. Also, Appendix G of arXiv:2603.12376v1 embeds gradient errors into a larger inexact-model oracle class before invoking a lower bound for that larger class; this inclusion alone does not establish the reverse realization needed for the gradient-only lower bound. We do not treat that observation as a settled correction or as a proof that no relevant lower bound exists.
