# Initial-gap-dependent oracle complexity of generalized-smooth convex optimization

The new result is a lower bound for exact-gradient optimization of general convex functions satisfying the standard affine generalized-smoothness condition. Together with existing upper guarantees, it determines the dependence on a known initial objective gap, up to logarithms in the generalized-smoothness radius. The upper algorithms and their rates are prior work; this contribution adds the missing intermediate-gap lower bound and proves it for arbitrary randomized algorithms.

## Specification and guarantee

The [Lean theorem](GapGeneralizedSmoothConvexLowerBound.lean) proves `NonConvergence` for [GapGeneralizedSmoothConvex.spec](../Setups/GapGeneralizedSmoothConvex.lean). Its objective and oracle assumptions are reused verbatim from [GeneralizedSmoothAndConvex](../Setups/GeneralizedSmoothAndConvex.lean): convexity on all of Euclidean space, a differentiable gradient with

\[
\|D\nabla f(x)\|\le L_0+L_1\|\nabla f(x)\|,
\]

and a minimizer satisfying both \(\|x_0-x_*\|\le R\) and \(f(x_0)-f(x_*)\le\Delta\). A query returns the exact full gradient. Function values, a minimizer, and the optimal value are not supplied. All parameters, including the dimension, accuracy, radius, and gap bounds, are public. There is no restriction to span methods, zero-respecting methods, GD, or any other update family.

Write

\[
s=\sqrt{L_0R^2/\varepsilon},\quad q=L_1R,\quad
h=\log(\Delta/(8\varepsilon)),\quad w=1+\log(2+q).
\]

For every valid parameter choice and every randomized algorithm, at every integer query budget

\[
0\le N\le \left\lfloor 2^{-24}\left[s+
\min\left\{q/w,(qh/w)^{2/3}\right\}\right]\right\rfloor,
\]

there is a fixed admissible objective and exact-gradient oracle for which the output fails the specified expected-accuracy guarantee. Success explicitly requires integrability and
\(\int(f(\mathrm{output}(\omega))-f(x_*))\,dP(\omega)\le\varepsilon\), under the algorithm/oracle execution law. The hard instance may depend on the algorithm and budget, but not its realized seed. The proof handles zero calls separately and covers the stated budget inclusively.

The valid regime is \(L_0,R,\varepsilon>0\), \(L_1\ge0\), \(s\ge4\), \(\Delta\ge16\varepsilon\), and

\[
d\ge\left\lceil 2^{80}(1+q+s)^{10}\right\rceil.
\]

The dimension is an explicit sufficient polynomial threshold, not an optimal dimension claim. The regime is nonempty, including \(L_1=0\); `GapBudget.valid_nonempty` supplies a witness. The theorem does not settle accuracy arbitrarily close to the initial gap or low fixed dimension.

## Why this is a natural problem

A known radius and initial gap are the standard inputs of gap-sensitive accelerated guarantees. Generalized smoothness permits exponential growth away from a minimizer, so a radius bound does not make the gap parameter redundant. The question is how much the initial gap changes the number of queries needed by the best algorithm, rather than the behavior of a prescribed implementation.

The setup includes interacting nonlinear objectives. For example, for invertible nonorthogonal \(A\), the convex function \(c\sum_j[\cosh((A(x-x_*))_j)-1]\) satisfies a bound with \(L_0=c\|A\|^2\) and \(L_1=\|A\|^2/\sigma_{\min}(A)\): use \(\cosh u\le1+|\sinh u|\) and \(\|A^T\sinh(A(x-x_*))\|\ge\sigma_{\min}(A)\|\sinh(A(x-x_*))\|\). Choosing a nearby starting point provides the radius and gap bounds. This example illustrates scope; the formal specification imposes no representation, separability, spectral, or finite-family restriction on objectives.

Convexity, the gradient-dependent curvature bound, and the radius/gap conditions have the provenance of Definition 2.1 and the classes in Section 2 of the primary paper below. Differentiability of the gradient is the repository's existing formulation; the lower construction is smooth and therefore also establishes hardness for the broader symmetric-smoothness class used there. The dimension threshold and nontrivial accuracy regime are explicit restrictions of this lower-bound theorem. No new structural assumption is imposed to produce the interpolation.

## Closest results and the remaining logarithms

[Rudomanov, Fomin, Gasnikov, and Stonyakin, *Descending Everest, Part I*, arXiv:2610.21461v2, November 5, 2026](https://arxiv.org/html/2610.21461v2) proves the radius-only deterministic lower bound in Theorem 4.10 and the constant-gap endpoint in Theorem B.3. Theorem B.7(b) supplies the general-gap upper bound; Section 5 leaves the intermediate-gap lower bound open. These are preprint results, not claims of conference acceptance. Their deterministic lower oracle can also supply values; the present randomized theorem claims only the exact-gradient oracle.

The new term is \(\min\{q,(q\log(\Delta/\varepsilon))^{2/3}\}\), up to powers of \(w\), throughout the stated regime. Endpoint lower bounds alone do not establish this dependence. The existing repository's [full radius lower bound](FullGeneralizedSmoothConvexLowerBound.lean) is also prior work and is not claimed as new here. Neither is the classical smooth contribution \(s\).

[GapGeneralizedSmoothUpper](../Proofs/GapGeneralizedSmoothUpper.lean) transfers existing algorithms to this exact expected-accuracy specification. The gap-sensitive [accelerated algorithm](../Algorithms/DampedGeneralizedAccelerated.lean) uses \(2K\) gradient calls, where

\[
K=\left\lceil4096\left[1+s+\min\left\{
\lceil q^{2/3}\rceil\ell,\ \ell+(q\ell)^{2/3}\right\}\right]\right\rceil,
\qquad \ell=\log(4+4\Delta/\varepsilon).
\]

The [radius-only algorithm](../Algorithms/RadiusFreeSherpa.lean), with the existing effective parameter \(L_1'=\max(L_1,1/R)\), uses
\(\lceil64s+65536(1+q)\log(3+q)\rceil\) calls. Both output the point specified by their actual `execute` run. Their output is pointwise deterministic under every admissible exact-gradient oracle, which proves integrability as well as expected accuracy. Initial and trial queries are included. Selecting the cheaper algorithm uses public parameters; it does not execute both algorithms and charge only one.

For \(q\ge1\), if \(h\le\sqrt q\), then \(\ell\le7h\) and \(h\le(qh)^{2/3}\), giving upper cost \(O(s+(qh)^{2/3})\). If \(h\ge\sqrt q\), the radius upper cost is \(O(s+qw)\). For \(q<1\), it is \(O(s)\). Hence the upper/lower ratio, allowing one for rounding, is \(O(w^2)\) uniformly in \(h\). No logarithm of \(\Delta/\varepsilon\) is hidden in that comparison. The intermediate improvement in the lower bound matters when the transient term dominates \(s\); if \(s\) dominates, the classical smooth difficulty already governs complexity. For example, when \(h=q^\beta\) with \(0<\beta<1/2\) and \(s\) below the transient scale, the new lower term is \(q^{2(1+\beta)/3}/w^{2/3}\), improving the constant-gap endpoint by a polynomial factor \(q^{2\beta/3}\) up to logarithms. This regime corresponds to \(\Delta/\varepsilon=8e^{q^\beta}\); such gaps are allowed by generalized smoothness. When Δ/ε grows only polynomially in q, the extra dependence is logarithmic and does not give a new polynomial exponent in q. Exact logarithmic factors remain unresolved.

## Construction and technical mechanism

The [calibrated chain](../Proofs/GapTransientChain.lean) uses a conjugate on a weighted simplex with \(m=N+1\) coordinates. With internal curvature parameters \(L_0/4,L_1/4\), its geometric spacing is
\(t=\min\{m^{-1/2},h/(2m)\}\), its smallest slope is \(\varepsilon L_1t/(100w)\), and its additional common shift is \(400w/(L_1t)\). The common shift separates the desired objective obstruction from the adjacent-coordinate spacing needed for a robust chain. After smoothing, the origin value is at most \(8\varepsilon e^{mt}\le\Delta\), while a hidden coordinate forces value at least \(4\varepsilon\). Its minimizer lies within \(R/32\) when
\(16384mw\le q\) and \(32768m\sqrt m\,w\le qh\). These two constraints yield the interpolation rather than merely one endpoint.

The proof must preserve the gap, radius, curvature, and prefix indistinguishability simultaneously; scalar or quadratic calculations alone do not do this. Smooth convolution preserves a flat minimizer region and robust coordinate prefixes. Polynomial localization makes distant queries independent of hidden coordinates while keeping the curvature bound. A random coordinate embedding and the repository's finite-prefix argument then produce a single seed-independent hard instance against arbitrary randomized queries and output selection. The explicit dimension pays for this hiding argument.

A separate [bounded-gap smooth chain](../Proofs/GapSmoothLowerBound.lean) retains the full \(s\) contribution even when \(L_1=0\) or \(\Delta\) is small. Its localized curvature is at most \(L_0\), initial gap at most \(11\varepsilon\), and hidden-coordinate error at least \(3\varepsilon\). The public budget split chooses the applicable construction; it does not add query costs of independent blocks. Opposite quadratics handle zero queries.

## Reduction checks and limitations

Batching does not improve an exact deterministic gradient oracle. Clipping is an algorithmic operation and does not prove a lower bound against all algorithms. Restricting to a smooth subclass recovers only \(s\). Restarting a constant-gap upper method proves an upper guarantee, not an intermediate-gap lower bound. Direct sums of endpoint hard instances do not add rounds when a single full-gradient call observes all blocks. Rescaling endpoint chains preserves their dimensionless gap ratio and does not supply the missing curve. The construction instead tunes that ratio while retaining a robust nonlinear chain and seed-independent hardness.

The contribution is the lower interpolation and its match to existing upper bounds, not a new upper algorithm, improved constant, or Lean formalization alone. The very large constants and dimension exponent are not optimized. There is no claim for noisy, finite-sum, value-plus-gradient randomized, or low-dimensional oracles. Broader nonsmooth-gradient upper transfer is not formalized. The expected criterion is the same for both sides; no fixed-success probability is substituted for it.
