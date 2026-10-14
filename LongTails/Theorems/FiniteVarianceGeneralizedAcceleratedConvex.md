# Finite-variance acceleration under generalized smoothness

This note explains the contribution and scope of
[`OracleTemplate.RobustGeneralized.FiniteVarianceGeneralizedAcceleratedConvex.result`](FiniteVarianceGeneralizedAcceleratedConvex.lean).

## Setup and proved guarantee

The [setup](../Setups/FiniteVarianceGeneralizedSmoothAndConvex.lean) assumes a
convex objective on a separable real Hilbert space, with an everywhere
differentiable gradient satisfying

$$
\|D\nabla f(x)\|\le L_0+L_1\|\nabla f(x)\|.
$$

A minimizer exists with $\|x_0-x^\star\|\le R$ and
$f(x_0)-f(x^\star)\le\Delta$. The jointly measurable gradient oracle is vector
unbiased and has uniform variance at most $\sigma^2$, with IID samples from an
abstract probability law. The sample space need not be finite. The parameters
satisfy $L_0,R,\Delta,\varepsilon>0$, $L_1,\sigma\ge0$, and $0<\delta<1$.

The [algorithm](../Algorithms/RobustGeneralizedAccelerated.lean) uses acceleration
without restarts and [pilot-centered clipped estimates](../Algorithms/RobustGradientEstimator.lean).
It knows the public parameter bounds and observed oracle replies; it does not
query objective values or use the minimizer or exact gradients. Its returned
point $\hat x$ satisfies

$$
\Pr\bigl[f(\hat x)-f(x^\star)\le\varepsilon\bigr]\ge1-\delta.
$$

Write

$$
A=\frac{L_0R^2}{\varepsilon},\qquad q=L_1R,\qquad
V=\frac{\sigma^2R^2}{\varepsilon^2},\qquad
L=\log(4+4\Delta/\varepsilon),
$$

$$
W=1+\sqrt A+L+(qL)^{2/3},\qquad
\ell=\log(e/\delta),\qquad H=\log\bigl(e(1+A+q+L)/\delta\bigr).
$$

The explicit proved oracle-call budget is

$$
K=\left\lceil\left(2^{22}W+2^{47}V\ell^2\right)H\right\rceil.
$$

It counts all pilot and correction samples, as well as calls used to pad the
fixed-length execution after termination. It is an oracle-complexity guarantee,
not an arithmetic-runtime bound.

## Contribution and technical mechanism

The contribution is the simultaneous preservation of **polynomial additive
curvature dependence, accelerated optimization cost, and additive finite-variance
cost**. Heavy-tail acceleration and a curvature-free statistical term separately
are already known. The deterministic acceleration dynamics, their nominal-weight
accounting, inverse-weight clipping, pilot centering, and bounded-increment
concentration are not claimed as new.

A clipped replacement is biased, so it cannot simply be substituted into the
existing unbiased light-tail oracle theorem. The new analysis controls this bias
at both adaptive queries, including the dependence of the second query on the
first estimate. Its exponential-moment compensation is proportional to the
nominal acceleration weight chosen before the pilot. Correction work is linear
in this weight and pilot work is quadratic. A pathwise bound on the accumulated
attempted weights, including heavily damped attempts, charges both costs to $V$
without an additional iteration-count or polynomial-curvature multiplier.
The proof also couples the guarded analysis to the actual sampled execution;
exact-gradient substitutions occur only in the proof.

## Closest comparisons and improvement regimes

- [Nguyen, Ene, and Nguyen (NeurIPS 2023), Theorem 4.1](https://arxiv.org/html/2304.01119v2)
  already give robust acceleration under ordinary smoothness. Localizing their
  method to the radius-$R$ ball and using Hessian gradient growth yields effective
  smoothness $L_0e^{2q}$ and a finite-variance bound of order
  $e^q\sqrt A+V$, up to confidence factors. This is a reduction of their theorem,
  not a bound they state for the present class. The improvement here is polynomial
  curvature dependence together with additive $V$.
- [Chezhegov et al., Theorem 1 at moment exponent two](https://arxiv.org/html/2505.20817v2)
  give a large-$q$ sufficient bound of roughly
  $\widetilde O(A+q^2V+q^4/\delta)$ with a min-iterate criterion. The present
  theorem guarantees an actual returned point and avoids that statistical
  curvature multiplier; the output criteria must not be identified.
- [ARC-SG](https://arxiv.org/html/2609.06555v1) uses stronger exponential-moment
  noise assumptions and has leading factors $\sqrt{1+q}$ on $\sqrt A$ and
  $(1+q)^3$ on $V$, besides entry terms. Its Appendix H discusses the additive
  curvature question. The present guarantee concerns the Hessian formulation,
  rather than every finite-difference generalized-smoothness formulation.

For fixed confidence and a supplied gap ratio $\Delta/\varepsilon$ polynomial
in $A,q$, the bound is $\widetilde O(1+\sqrt A+q^{2/3}+V)$. With the general
radius-derived exponential gap certificate, its consequence is instead
$\widetilde O(1+\sqrt A+q^{4/3}+V)$. These are interpretations of the explicit
budget; the initial-gap logarithm must not be discarded.

The separation from exponential localization is meaningful for growing $q$ when
the optimization term matters. No universal improvement is claimed when $q$ is
bounded, when the prior statistical term already dominates, or when other entry
costs dominate. Constants and confidence logarithms are conservative. The result
does not establish optimal curvature dependence or a new deterministic rate.

Known clipping precedents include
[Gorbunov, Danilova, and Gasnikov (NeurIPS 2020)](https://proceedings.neurips.cc/paper_files/paper/2020/file/abd1c782880cc59759f4112fda0b8f98-Paper.pdf)
and [Ou and Wang, Section 4.3](https://arxiv.org/html/2609.03990v1#S4.SS3).
During the September 2026 review, the full
[SNAG appendix](https://openreview.net/pdf?id=AlYT0ZD51A) was inaccessible.
Indexed primary assumptions and the ARC-SG discussion distinguish its generalized
exponential-moment result from its ordinary-smooth finite-variance result, but an
exhaustive parameter-by-parameter comparison with that appendix was not verified.
