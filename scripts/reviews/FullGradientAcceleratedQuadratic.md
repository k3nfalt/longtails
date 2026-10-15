# Full-gradient acceleration for quadratic finite sums: novelty assessment

[`FullGradientAccelerated.result`](../../LongTails/Theorems/FullGradientAcceleratedQuadratic.lean)
uses the unchanged
[`QuadraticFiniteSum.spec`](../../LongTails/Setups/QuadraticFiniteSum.lean).
The component quadratics have self-adjoint Hessians bounded by \(L\), their
average is \(\mu\)-strongly convex, and the initial distance is bounded by
\(R\). Components may be indefinite. The deterministic last-iterate method
forms each full gradient from exactly \(n\) component-gradient queries and has
budget

\[
 n\left\lceil8\sqrt{L/\mu}\,
 \log\left(1+2LR^2/\varepsilon\right)\right\rceil.
\]

The [companion note](../../LongTails/Theorems/FullGradientAcceleratedQuadratic.md)
specifies the conservative recurrence and compares it with the existing
reshuffling budget. The method does not use the optimum-gradient bound \(G\).
The Lean proof specializes the repository's inexact accelerated convergence
argument to exact full gradients, and connects it to component-query execution
through the existing batching lemmas.

| Comparison | Assessment |
| --- | --- |
| Classical accelerated gradient descent, [Bubeck 2015, Theorem 3.18](https://arxiv.org/pdf/1405.4980) | Same \(O(n+n\sqrt{L/\mu}\log(1+LR^2/\varepsilon))\) order after charging \(n\) calls per full gradient. The reference has different tuning; this formalization does not improve the classical rate. |
| [Katyusha X, Allen-Zhu 2018, Theorem 1](https://proceedings.mlr.press/v80/allen-zhu18a/allen-zhu18a.pdf) | Its finite-dimensional expected-call bound has better \(n\)-dependence, \(O((n+n^{3/4}\sqrt{L/\mu})\log(1/\varepsilon))\). This theorem instead gives an explicit deterministic call budget on the setup's Hilbert space. These qualifications do not establish an optimal finite-sum rate. |
| Existing [RandomReshufflingQuadratic](../../LongTails/Theorems/RandomReshufflingQuadratic.lean) | A strictly better certified order in accuracy for fixed positive \(G,R\), and a better transient condition-number dependence. The algorithm changes from reshuffling to full-gradient acceleration. It is not a sharper analysis of reshuffling. |

**Reduction check.** Averaging the exact component gradients gives the gradient
of an \(L\)-smooth, \(\mu\)-strongly convex function. Classical acceleration
therefore applies without component convexity or commutation. The added proof
formalizes this reduction, the exact oracle accounting, and the original
measurability and expectation contract. The setup and oracle model are unchanged.

**Coverage (2026-10-15 UTC).** The classical accelerated guarantee and the
Katyusha X comparison were checked in the linked primary texts. This is a
focused comparison, not an exhaustive priority search. The established
accelerated upper bound is already enough to rule out a new complexity claim.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**

**Confidence: high.** The contribution is a verified classical baseline with a
better budget than the existing theorem for this repository setup.
