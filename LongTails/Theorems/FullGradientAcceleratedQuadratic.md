# Full-gradient acceleration for quadratic finite sums

The [Lean theorem](FullGradientAcceleratedQuadratic.lean),
`OracleTemplate.FullGradientAccelerated.result`, adds a classical accelerated
guarantee to the existing [QuadraticFiniteSum setup](../Setups/QuadraticFiniteSum.lean).
It counts component-gradient queries and proves the setup's expected objective-gap
criterion. The constructed algorithm is deterministic, and its underlying accuracy
bound holds for every admissible oracle seed. This is a formalization of a standard
reduction to full-gradient acceleration, not a new accelerated complexity bound.

## Setup and algorithm

On the setup's real Hilbert space, write

\[
 F(x)=\frac1n\sum_{i=1}^n
 \left(\frac12\langle x,A_i x\rangle+\langle b_i,x\rangle\right),
 \qquad A_i=A_i^*,\quad \|A_i\|\le L,\quad \bar A\succeq\mu I.
\]

The original assumptions remain: \(n\ge1\), \(0<\mu\le L\),
\(R,G\ge0\), \(\varepsilon>0\), and a stationary minimizer \(x_*\)
with \(\|x_0-x_*\|\le R\) and \(\max_i\|A_i x_*+b_i\|\le G\).
Components may be indefinite and need not commute. One query at \((i,x)\)
returns exactly \(A_i x+b_i\). The setup permits arbitrary algorithms.

Set \(\kappa=L/\mu\), \(\theta=1/(4\sqrt\kappa)\), and
\(x_0=z_0\). The [algorithm](../Algorithms/FullGradientAccelerated.lean) performs

\[
 y_k=\frac{x_k+\theta z_k}{1+\theta},\qquad
 g_k=\frac1n\sum_i(A_i y_k+b_i),
\]
\[
 x_{k+1}=y_k-\frac{g_k}{L},\qquad
 z_{k+1}=(1-\theta)z_k+\theta y_k-\frac{2\theta}{\mu}g_k.
\]

Every component in a batch is queried at the same frozen point \(y_k\).
One update therefore costs exactly \(n\) component calls. The output is
the last completed \(x_K\); there are no restarts, line searches, or additional
function-value queries. Neither the recurrence nor its budget uses \(G\),
although that parameter and its assumption remain in the shared setup.

## Guarantee and proof organization

The public budget is

\[
 B_{\mathrm{acc}}=
 n\left\lceil8\sqrt{L/\mu}\,
 \log\left(1+\frac{2LR^2}{\varepsilon}\right)\right\rceil.
\]

After this many component calls, \(F(x_K)-F(x_*)\le\varepsilon\).
The public theorem also proves output measurability, gap integrability, and
the required expectation bound under the framework's algorithm and oracle laws.
When \(R=0\), the budget is zero and the output is \(x_0\).
The case \(L=\mu\) is included.

The proof reuses the exact-gradient specialization of
[`InexactAccelerated`](../Proofs/InexactAcceleratedConvergence.lean):

- [FullGradientQuadraticModel](../Proofs/FullGradientQuadraticModel.lean)
  derives the average gradient, smooth upper inequality, and strong-convexity
  lower inequality from the original component assumptions.
- [FullGradientQuadraticExecution](../Proofs/FullGradientQuadraticExecution.lean)
  uses the existing batching proof to identify the actual \(nK\)-query execution
  with the accelerated recurrence, then applies its accuracy theorem.
- [FullGradientAcceleratedQuadratic](FullGradientAcceleratedQuadratic.lean)
  exports one `result : Convergence LongTails.Setups.QuadraticFiniteSum.spec budget`.

## Comparison with the reshuffling theorem

The existing [RandomReshufflingQuadratic theorem](RandomReshufflingQuadratic.lean)
analyzes a different algorithm, with budget

\[
 B_{\mathrm{rr}}=n\left\lceil\left(64\kappa+
 \frac{128L^{3/2}G}{n\mu^2\sqrt\varepsilon}+
 8\left(\frac{L^3G^2}{n\mu^4\varepsilon}\right)^{1/3}\right)
 \log\left(1+\frac{LR^2}{\varepsilon}\right)\right\rceil.
\]

For fixed positive \(n,L,\mu,R,G\) and \(\varepsilon\to0\), these
explicit budgets have orders \(O(\log(1/\varepsilon))\) and
\(\Theta(\varepsilon^{-1/2}\log(1/\varepsilon))\), respectively.
For \(G=0\), fixed \(n,L,R>0\), and
\(\varepsilon=LR^2/\kappa^2\) as \(\kappa\to\infty\), they have
orders \(n\sqrt\kappa\log\kappa\) and \(n\kappa\log\kappa\).
In fact \(B_{\mathrm{acc}}\le B_{\mathrm{rr}}\) pointwise: for
\(t=LR^2/\varepsilon\ge0\), use
\(\log(1+2t)\le2\log(1+t)\), \(\sqrt\kappa\le\kappa\),
and monotonicity of the ceiling. This is a comparison of proved budgets,
not a lower bound on reshuffling's actual performance.

The improvement is over the repository's existing guarantee for this setup.
The classical accelerated order is recorded, for example, in
[Bubeck, Theorem 3.18](https://arxiv.org/pdf/1405.4980); its full gradients can be
implemented with \(n\) component calls. The present conservative coefficients
are obtained from the repository's existing proof rather than claimed to be
the fastest classical tuning. Finite-sum methods can improve the dependence on
\(n\): [Katyusha X, Theorem 1](https://proceedings.mlr.press/v80/allen-zhu18a/allen-zhu18a.pdf)
gives the related \(O((n+n^{3/4}\sqrt\kappa)\log(1/\varepsilon))\)
expected-call order in finite dimension. No finite-sum optimality or scientific
novelty claim is made here.
