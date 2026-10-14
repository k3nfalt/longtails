# Contribution and scope: Markov quadratic last-iterate SGD

This note clarifies the contribution formalized in
[MarkovQuadraticLastIterate.lean](MarkovQuadraticLastIterate.lean).
The new guarantee concerns the last iterate of ordinary constant-step SGD
under correlated sampling. Averaging already achieves the same complexity
order under this setup; the existential oracle-complexity bound alone is
not the novelty claim.

## Setup and proved guarantee

Let $E$ be a real separable Hilbert space. A finite family of bounded
selfadjoint operators satisfies $0 \preceq H_i \preceq L I$, with a common
interpolating minimizer $u$, and

$$
f(x)-f(u)=\frac12\sum_i\pi_i\langle x-u,H_i(x-u)\rangle.
$$

The exogenous Markov chain has stationary distribution $\pi$, transition
matrix $P$, and arbitrary initial law. Assume
$P_{ij}\ge\alpha\pi_j$, where a valid $0<\alpha\le1$ is known.
The oracle returns $H_{s_t}(x-u)$; the algorithm receives neither state
identities nor refresh labels. Realizable finite-data least squares, with
$H_i=a_i a_i^\top$, is a concrete example. Noncollinear features can give
noncommuting Hessians, and a stationary refresh mixed with a directed
distribution-preserving walk can give a nonreversible sampling chain.

For $L>0$, $R\ge0$, and $\|x_0-u\|\le R$, the algorithm uses

$$
x_{t+1}=x_t-\eta H_{s_t}(x_t-u),\qquad
\eta=\frac{\alpha}{10000L}.
$$

For every integer $T\ge1$, its actual last iterate satisfies

$$
\mathbb E[f(x_T)-f(u)]\le\frac{5\cdot10^{15}LR^2}{\alpha T}.
$$

The expectation is over the Markov trajectory. Every observation is used
and counted: there is no thinning, averaging, or restart. For $\varepsilon>0$,
the public theorem proves epsilon accuracy with the explicit budget

$$
K=\left\lceil\frac{10^{16}LR^2}{\alpha\varepsilon}\right\rceil+1.
$$

## What the contribution adds

The rate is uniform in dimension, state count, and mean curvature. It does
not require a positive curvature lower bound, reversibility, commutativity,
or a lower bound on stationary atom masses.

The closest IID result is [Dereziński–Dong, Theorem 3.1 and Corollary 3.3](https://arxiv.org/html/2606.29593v1).
Its IID positive-contraction analysis does not directly apply to Markov
products: deleting an interior factor changes the transition law, while
regeneration produces nonselfadjoint blocks whose lengths correlate with
their actions. The new proof combines a geometric-block sector and source
estimate with source-weighted operator renewal analysis to obtain the bound
at a deterministic number of original oracle calls.

Relevant Markov analyses, including [Mou et al., Proposition 1](https://arxiv.org/html/2112.12770)
and [Even, Theorem 5.6](https://proceedings.mlr.press/v202/even23a/even23a.pdf),
retain positive-stability or component-strong-convexity requirements in the
compared guarantees. They do not give this curvature-uniform fixed-step
last-iterate result. This comparison does not assert superiority in their
well-conditioned or noisy regimes.

## Comparisons and limitations

Under the same assumptions, averaged full-step SGD already attains
$LR^2/[2\alpha(T-1)]$ after $T\ge2$ calls. Consequently, this result does
not improve the all-algorithm minimax complexity order.

A checked reduction to IID sampling by thinning gives the last-output bound
$[4.5\log(T+1)+3.5]LR^2/(\alpha T)$, counting discarded calls. The new
guarantee removes that logarithm asymptotically. Its literal bound beats
this displayed comparator only when

$$
\log(T+1)>\frac{5\cdot10^{15}-3.5}{4.5}.
$$

The constants are therefore far too conservative to establish practical
numerical superiority. The thinning comparator is a derived baseline,
not a claim about the best possible algorithm.

Finite support, Hilbert separability, pointwise Hessian boundedness, exact
quadratic interpolation, and known $\alpha$ are explicit scope restrictions.
Stationary refresh is stronger than generic geometric mixing or Doeblin
minorization by an arbitrary measure. The theorem does not establish a
noisy, nonlinear, or general-mixing extension, nor necessity of its step-size
scaling. The independent research review recommended NeurIPS theory
acceptance for the last-iterate contribution with these limitations; that
recommendation is not actual conference acceptance.

## Connection to the Lean declarations

- [MarkovQuadraticInterpolation.lean](../Setups/MarkovQuadraticInterpolation.lean)
  specifies the setup and success criterion.
- [MarkovQuadraticSgd.lean](../Algorithms/MarkovQuadraticSgd.lean)
  defines `lastSgd` and its concrete iterate recurrence.
- [MarkovQuadraticRisk.lean](../Proofs/MarkovQuadraticRisk.lean)
  contains `Model.iterate_risk_bound` and `Model.iterate_accuracy`.
  The stationary residual-kernel decomposition used by the risk lemma is
  derived from the setup's minorization in the accuracy proof.
- [MarkovQuadraticExecution.lean](../Proofs/MarkovQuadraticExecution.lean)
  proves `execute_lastSgd`, connecting the recurrence to actual execution
  and its exact oracle-call count.
- [MarkovQuadraticLastIterate.lean](MarkovQuadraticLastIterate.lean)
  exports `OracleTemplate.MarkovQuadratic.result : Convergence spec budget`
  with `lastSgd` as its explicit algorithm witness.

The framework's public `Convergence` proposition is existential. The
concrete last-iterate lemmas and execution witness, rather than that
existential proposition in isolation, carry the algorithm-specific
contribution.
