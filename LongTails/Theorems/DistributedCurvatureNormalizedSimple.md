# A constant-equivalent, shorter distributed-training budget

The [simplified theorem](DistributedCurvatureNormalizedSimple.lean) and the [original expanded theorem](DistributedCurvatureNormalized.lean) describe the same optimization guarantee. Both use [DistributedHessianLipschitzNonconvex.spec](../Setups/DistributedHessianLipschitzNonconvex.lean): a common lower-bounded, L-smooth nonconvex objective with Q-Lipschitz Hessian, independent unbiased finite-variance gradient streams, and a star network with explicit computation and finite-bit communication times. Their output satisfies expected gradient norm at most epsilon. General nonlinear objectives in arbitrary finite dimension, including dimension zero, remain covered.

This version simplifies the public time budget by spending universal constants. It makes no additional research novelty claim and does not improve the original numerical deadline. The original theorem, algorithm definitions, setup, and supporting research proofs are retained unchanged. The [original contribution note](DistributedCurvatureNormalized.md) gives the scientific contribution, primary literature comparisons, nonlinear examples, accuracy tradeoffs, and improvement regime.

## The shorter formula

For exposition, write
\[
 A=1+L\Delta/\varepsilon^2,\qquad R=\sigma^2/\varepsilon^2,\qquad H=\max_i h_i,
\]
\[
 x_s=A\sqrt d,\qquad x_u=\frac{d^2A+d\min(R,n)}{\sqrt n},\qquad
 w_s=1+\log(1+x_s),\quad w_u=1+\log(1+x_u),
\]
where logarithms are natural, and \(q=\min\{1,\sqrt{Q\varepsilon}/L\}\). If latency is \(\ell\) and time per bit is \(b\), the new deadline is
\[
 T_{\rm simple}=2^{32}A\left[
 \ell+H\left(1+\frac Rn\right)
 +b(w_u+w_s)\left(1+\frac d{n^{1/3}}\right)
 +dbw_s q
 +\sqrt{\frac{dHRbw_u}{n}}
 \right].
\]
The Lean `budget` expands these expressions directly in the setup parameters on one line. It contains no local tuning variables, opaque budget helpers, ceilings, or bit-length functions. The nine-term maximum becomes four grouped cost terms. Its definition is approximately half the length of the original.

The retained uplink/downlink distinction matters: their precision requirements can differ by an unbounded logarithmic factor. Neither the minimum in \(x_u\) nor its division by \(\sqrt n\) has been discarded.

## Pointwise equivalence, not just one asymptotic example

The supporting [budget comparison](../Proofs/DistributedBudgetSimplification.lean), `budget_bounds` together with `simplified_budget_explicit`, proves for every admissible parameter choice that
\[
 T_{\rm original}\le T_{\rm simple}\le2048\,T_{\rm original}.
\]
Thus the simplification changes only a universal constant. It preserves every dependence on accuracy, dimension, worker count, smoothness, Hessian regularity, variance, initial gap, computation times, latency, and bandwidth, including all logarithmic factors and joint parameter regimes. The factor 2048 is a conservative proof bound, not a claim of the best possible constant.

Two steps explain the reduction:

1. The old physical scalar-width bound is \(B(x)=\operatorname{size}(\lceil2^{20}(1+x)\rceil)+66\). For every \(x\ge0\), [DistributedBudgetPrecision](../Proofs/DistributedBudgetPrecision.lean) proves
   \[
   1+\log(1+x)\le B(x)\le128\,[1+\log(1+x)].
   \]
   The outer factor changes from \(2^{25}\) to \(2^{32}\), absorbing that 128 uniformly rather than repeating large precision constants throughout the formula.

2. [DistributedBudgetAlgebra](../Proofs/DistributedBudgetAlgebra.lean) compares the original maximum with the four-term sum. For the reverse inequality, [DistributedBudgetWidths](../Proofs/DistributedBudgetWidths.lean) uses the actual precision formulas. If \(n>d^3\), then \(d/n^{1/3}<1\), and the grouped communication term is controlled by the standalone width costs. If \(n\le d^3\), then \(x_s\le x_u\le2x_s^5\), so \(w_s\le w_u\le8w_s\); the old mixed cubic communication term controls the grouped one. The resulting sum is at most 16 times the corresponding maximum. This argument also covers dimension zero through the first case.

In particular, the original positive-cost regime \(d\asymp\varepsilon^{-7/4}\), \(n\asymp\varepsilon^{-3/2}\), with fixed remaining parameters, still gives \(O(\varepsilon^{-13/4}\log(1/\varepsilon))\) elapsed time. No logarithmic loss is hidden in soft-O notation.

## Connection to actual execution

The theorem constructs [DistributedNormalizedTraining.algorithm](../Algorithms/DistributedNormalizedTraining.lean) with the new deadline. All optimization tuning, minibatches, codecs, packet sizes, oracle calls, and output selection stay as in the original construction. The logarithmic widths above are accounting bounds; they do not replace the actual finite-bit encoder widths.

The algorithm's idle timer depends on its deadline, so the proof does not assume that the original algorithm can simply be observed at any later time. It invokes the actual execution and finite-event lemmas with the new deadline, uses the proved runtime domination, and proves expected accuracy of that execution under `DistributedTemplate.law`. Almost-sure `FiniteEvents` is established at every deadline up to the new budget. Zero noise, zero gap, zero bit cost, zero latency, and zero Hessian Lipschitz constant need no new restrictions.

## Fairness and limitations of TemplateDistributed

The simplification preserves the original distributed model exactly. Its strengths are explicit event execution, pending-resource constraints, finite packets, complete timing, and exclusion of infinitely many events before a deadline. These support a rigorous elapsed-time comparison rather than an idealized round count.

The model still gives local/coordinator arithmetic no cost and uses deterministic gradient service times and independent directed star links. Shared bandwidth contention, stragglers, finite-precision local arithmetic, and executable random-bit codecs are not modeled by this theorem. Public initial models and shared randomness are available, and only the coordinator must return the final output. These limitations matter for hardware interpretation; a growing worker count does not imply an unconditional physical speedup.

Future framework work could add costed coordinator computation, shared-bandwidth queueing, stochastic service times, and implementable numerical interfaces. The original note discusses these issues in more detail. No frozen template or oracle interface is changed here, and no claim of universal superiority or minimax optimality is added.
