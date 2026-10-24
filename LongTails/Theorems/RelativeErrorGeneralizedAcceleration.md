# Acceleration with relative gradient errors under generalized smoothness

The [convergence theorem](RelativeErrorGeneralizedAcceleration.lean) gives a pathwise objective-accuracy guarantee for convex generalized-smooth optimization with persistent relative gradient errors. Its contribution is an extension of accelerated relative-error guarantees to objectives with unbounded curvature, with polynomial dependence on the generalized-smoothness radius. It does not improve the strongest exact-gradient transient or establish an optimal complexity for this oracle model.

## Problem and information

The [setup](../Setups/RelativeGeneralizedSmoothConvex.lean) specifies a convex differentiable function on a real Hilbert space, a continuous gradient, and the segment form of generalized smoothness: if the gradient norm on the segment from x to y is at most M, then

\[
\|\nabla f(x)-\nabla f(y)\|\le (L_0+L_1M)\|x-y\|.
\]

For twice continuously differentiable finite-dimensional objectives, the familiar condition \(\|\nabla^2 f(x)\|\le L_0+L_1\|\nabla f(x)\|\) implies this segment condition by integration. The theorem includes arbitrary finite dimension and does not restrict the objective to a scalar, quadratic, or separable family.

The algorithm receives positive upper bounds R and Δ with a hidden minimizer u satisfying \(\|x_0-u\|\le R\) and \(f(x_0)-f(u)\le\Delta\), together with \(L_0>0\), \(L_1\ge0\), target \(\varepsilon>0\), and \(0\le\alpha\le1/100\). Each gradient reply v at x satisfies

\[
\|v-\nabla f(x)\|\le\alpha\|\nabla f(x)\|.
\]

This condition is quantified over every query, history, and oracle seed. Errors can be biased, discontinuous, and history dependent. There is no unbiasedness, independence, finite sample-space, or stochastic moment assumption. The objective, exact gradients, minimizer, and optimum value are unavailable to the algorithm. The setup does not restrict algorithms to the construction used in the proof.

Relative error is the established model in Vasin–Tyurin–Gasnikov, [arXiv:2610.24863v1](https://arxiv.org/html/2610.24863v1), equation (7) with zero additive error. It describes, for example, a gradient computation with a certified relative stopping tolerance or deterministic contractive compression. Such a mechanism must actually guarantee the stated norm bound; generic quantization or stochastic gradients need not do so. Known radius and gap bounds and generalized smoothness occur in the exact-gradient analysis of Tyurin, [ICML 2026](https://proceedings.mlr.press/v306/tyurin26b.html), [arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884v2), Sections 3–4. The fixed small relative-error range is an explicit restriction compared with results allowing larger errors.

## Algorithm, output, and cost

Write

\[
T=\frac{L_0R^2}{\varepsilon},\quad q=L_1R,\quad
H=1+\log\!\left(2+T+q+\frac{\Delta}{L_0R^2}\right).
\]

The proved oracle budget is

\[
N=\left\lceil2^{60}\left[\sqrt T+\alpha^2T+(1+q)H+\alpha^2q^2H^2\right]\right\rceil.
\]

The constant is conservative and is not a practical tuning recommendation. Its role is to give a single explicit formula with all parameter dependences and initialization terms retained.

The [algorithm](../Algorithms/RelativeGeneralizedAcceleration.lean) sets \(B=2+\alpha^2N\), \(A_0=R^2/\Delta\), and \(x_0=z_0\). At a state (A,x,z), it chooses

\[
a=\frac{A}{4096(1+q\sqrt B+\sqrt{L_0A})},\qquad
D=\frac{BR^2}{A},\qquad
\eta=\frac1{1024(L_0+L_1^2D)},\qquad
y=\frac{Ax+az}{A+a}.
\]

After one oracle query v at y, it projects \(y-\eta v\) and \(z-av\) onto the Euclidean ball \(\overline B(x_0,2R)\), obtaining the next primal and mirror points, and replaces A by A+a. The returned output is the last primal point after N steps, defined through the repository's `execute`. Every step consumes exactly one gradient reply. Projection and scalar arithmetic are not additional oracle calls; no line search, function evaluation, batch, or exact-gradient check is hidden in the cost.

For every admissible oracle seed sequence, the returned point satisfies \(f(x_N)-f(u)\le\varepsilon\). Consequently the setup's explicit almost-sure criterion holds for the algorithm/oracle product probability measure used by `Convergence`.

## New mechanism and comparison

The proof combines three controls that must hold simultaneously. Projection keeps the primal and mirror points within a known ball whose interior contains a minimizer with margin R. A normal-cone estimate then converts the projected gradient mapping into control of the full true gradient, even for transverse relative errors. This gives local descent without continuity of the oracle replies. Generalized smoothness and a short mixing displacement bound the curvature at the actual query using D. Finally the accelerated potential obeys

\[
A_{k+1}(f(x_{k+1})-f(u))+\tfrac12\|z_{k+1}-u\|^2
\le A_k(f(x_k)-f(u))+\tfrac12\|z_k-u\|^2+\alpha^2R^2.
\]

The horizon-dependent B closes this invariant. With \(s=\sqrt{L_0A}\) and \(Q=1+q\sqrt B\), the scalar potential \(s+2Q\log s\) grows by at least \(1/12288\) per step. Inverting this growth proves the explicit budget without a hidden logarithm of N. The geometry, local curvature, energy, tuning, growth, budget, and execution arguments are in the corresponding `RelativeGeneralized` [proof modules](../Proofs/RelativeGeneralizedConvergence.lean).

The closest comparisons are:

* **Exact generalized-smooth acceleration.** Tyurin's ICML 2026 result, Theorem 4.3 and Section 3.3 of the version above, uses exact gradients. The more recent unreviewed preprint Rudomanov–Fomin–Gasnikov–Stonyakin, [“Descending Everest,” arXiv:2610.21461v1](https://arxiv.org/html/2610.21461v1), Section 3, gives gradient-only complexity \(O(\sqrt T+(1+q)\log(2+q))\), without Δ. Its inexact line-search procedure still uses exact gradient information. Our exact-error limit has a worse logarithmic transient and requires a gap bound. The contribution is robustness to persistent relative gradient error, not a new exact-gradient state of the art.
* **Relative errors with global smoothness.** Vasin–Tyurin–Gasnikov, arXiv:2610.24863v1, Theorems 3.1–3.3, establishes the accelerated relative-error tradeoff for globally smooth problems, with a regularization-based convex result and logarithmic factors. Our leading accuracy terms are \(\sqrt T+\alpha^2T\), but the objective class allows globally unbounded curvature. We do not claim those leading terms are themselves new in the globally smooth case.
* **Approximate normalized directions.** Kovalev–Stonyakin, [arXiv:2607.26969v2](https://arxiv.org/html/2607.26969v2), Theorem 3.1, treats a normalized-direction oracle with an accuracy-dependent direction tolerance and a nonaccelerated best-iterate guarantee. That oracle supplies no gradient magnitude. A relative-norm reply gives approximate direction information; the converse does not hold. Our theorem neither solves that weaker-information problem nor claims superiority under its oracle model.

Freezing curvature on the radius-2R ball gives an effective global smoothness bound of order \(L_0e^{3q}\). Substitution into a global-smooth relative-error theorem thus gives accuracy terms of order \(e^{3q/2}\sqrt T+\alpha^2e^{3q}T\), even before addressing constrained output details. Our polynomial transient avoids this exponential localization cost. Repeating queries does not average away adversarial bias. A naive inexact lower-model conversion introduces an error of order \(\alpha R\|\nabla f\|\); it does not supply the coupled curvature and energy invariant above. These checks exclude the direct reductions, not every conceivable future improvement.

The leading accelerated term dominates when \(\alpha\lesssim T^{-1/4}\) and the displayed transient is at most order \(\sqrt T\). With fixed nonzero α and increasingly small ε, the \(\alpha^2T\) term eventually dominates. The polynomial advantage over global localization is meaningful when q is large enough that exponential curvature bounds dominate the displayed transient; no universal advantage over all prior algorithms or all parameter regimes is claimed.

## Nonlinear instances and limitations

For any invertible dense matrix \(M\in\mathbb R^{d\times d}\),

\[
f(x)=\sum_{i=1}^d(\cosh((Mx)_i)-1)
\]

has interacting coordinates, minimizer zero, and unbounded Hessian. It satisfies the Hessian condition with \(L_0=\|M\|_{\mathrm{op}}^2\) and \(L_1=\|M\|_{\mathrm{op}}^2/\sigma_{\min}(M)\): use \(\max_i\cosh((Mx)_i)\le1+\|\sinh(Mx)\|_2\) and \(\nabla f=M^\top\sinh(Mx)\). These parameters make any dimension or conditioning dependence explicit. The example illustrates the standard objective class; the theorem does not add a special assumption requiring this family.

The guarantee requires known valid bounds, a prescribed horizon and accuracy, α at most 1/100, and a minimizer. It is not parameter free, does not cover additive noise, and does not establish optimality of the generalized-smooth transient. The algorithm's ball is a device it constructs; the problem itself is unconstrained. The mathematical proof uses Hilbert geometry, so it does not assert the same result for arbitrary norms.

Literature checks used UTC 2026-10-24. Both Researcher and Reviewer independently surveyed the two latest publicly available ICML, ICLR, and NeurIPS catalogues (2026 and 2025), recent arXiv submissions/revisions, and relevant older references before selecting the direction. This was targeted primary-source screening, not exhaustive reading of every paper. Official ICML proceedings verified Tyurin's acceptance; the October and July arXiv results cited above are treated as preprints. Some conference virtual pages were inaccessible to automated browsing; official proceedings, OpenReview records, and primary arXiv texts were used where available. Novelty here means the stated combination of objective class, adversarial relative oracle, and parameter-dependent guarantee survived those comparisons; missing search results alone are not evidence of novelty.
