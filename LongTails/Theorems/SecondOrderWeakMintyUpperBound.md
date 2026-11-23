# Second-order weak-Minty variational inequalities: matching upper bound

## Result

Lean: theorem [`SecondOrderWeakMintyUpperBound.lean`](SecondOrderWeakMintyUpperBound.lean)
(`OracleTemplate.WeakMintyHybrid.SecondOrderWeakMintyUpperBound.result`, a `Convergence` statement);
setup [`../Setups/WeakMintySecondOrderExpected.lean`](../Setups/WeakMintySecondOrderExpected.lean);
algorithm [`../Algorithms/WeakMintyHybrid.lean`](../Algorithms/WeakMintyHybrid.lean) (unchanged);
proof module [`SecondOrderMintyUpper`](../Proofs/SecondOrderMintyUpper.lean) (re-count of the execution,
budget algebra and the expected-residual success). The paired lower bound is
[`SecondOrderWeakMintyLowerBound`](SecondOrderWeakMintyLowerBound.md).

With

$$
M=\min\Big\{\frac{L_2R^2}{\varepsilon},\ \frac{L_1^2R^2}{\varepsilon^2}\Big\},
$$

the hybrid method returns a point with $\|F(x_{\rm out})\|\le\varepsilon$ for every seed, hence
$\mathbb E\|F(x_{\rm out})\|\le\varepsilon$ with an integrable residual, within

$$
\big\lceil 2^{27}\,(1+M)\big\rceil
$$

oracle calls (value and Jacobian calls counted together, all inner Picard iterations and certificates
included). Together with the lower bound $\lfloor M/2^{15}\rfloor$ this determines the complexity of
the class as $\Theta(M)$ up to a universal constant on the lower bound's regime.

## Setup

[`WeakMintySecondOrderExpected`](../Setups/WeakMintySecondOrderExpected.lean) is the repository's
[`WeakMintySecondOrder`](../Setups/WeakMintySecondOrder.lean) class with the accuracy criterion changed
from almost-sure to expected residual and the weak-Minty range restricted to $0\le\rho\le1/L_1$:

- $E$ an arbitrary finite-dimensional real inner-product space, no dimension condition;
- $F$ differentiable with derivative $J$, $\mathrm{Lip}(F)\le L_1$, $\mathrm{Lip}(J)\le L_2$;
- a zero $x^\star$, $\|x_0-x^\star\|\le R$, with $\langle F(x),x-x^\star\rangle\ge-\frac\rho2\|F(x)\|^2$;
- exact oracle: a call returns $F(x)$ or $J(x)$;
- the algorithm receives $L_1,L_2,\rho,\varepsilon,x_0$ but not $R$ (the budget depends on $R$).

The lower-bound setup
[`HighDimensionalWeakMintySecondOrder`](../Setups/HighDimensionalWeakMintySecondOrder.lean) is exactly
the restriction to $E=\mathbb R^d$, $R>0$, $M\ge2^{15}$, $d\ge M^3$ (with $R$ public, which only
strengthens the lower bound); the namespace `SecondOrderMintyInclusion` in [`SecondOrderMintyLowerBound`](../Proofs/SecondOrderMintyLowerBound.lean)
proves that valid restricted parameters map to valid general parameters and that admissibility and
success coincide definitionally. Hence the upper bound applies to every instance of the lower bound.

## Algorithm and what is new

The algorithm is the existing `WeakMintyHybrid` of
[`FullRangeSecondOrderWeakMinty`](FullRangeSecondOrderWeakMinty.md): at an anchor with residual at
most $\delta^2L_1^2/(64L_2)$ it takes a cubic-regularized Newton trial step, otherwise $K$ Picard steps of
step size $(1-\delta/4)/L_1$, followed by a relaxed proximal-point correction, where
$\delta=1-\rho L_1/2\in[1/2,1]$. That theorem proves $O((1+L_2R^2/\varepsilon)\log(2/\delta)/\delta^5)$
calls. This is **not** a new algorithm. The new part is the accounting that yields the minimum:

- New lemma `fallback_progress_residual`: every nonterminal fallback attempt from an anchor with
  $\|F(x)\|\ge\varepsilon$ decreases $\|x-x^\star\|^2$ by at least $\delta^2\varepsilon^2/(256L_1^2)$
  (the Picard certificate gives $\|F(x)\|\le4L_1\|s\|$ for the attempted step $s$).
- When $64L_2\varepsilon\ge\delta^2L_1^2$, an anchor with residual below the cubic threshold already
  satisfies $\|F(x)\|\le\varepsilon$ and stops, so only fallback attempts occur; the decrease above gives
  $1024L_1^2R^2/\varepsilon^2\le2^{18}M$ attempts. Otherwise the existing per-attempt decrease
  $\delta^4\varepsilon/(16384L_2)$ gives $2^{18}L_2R^2/\varepsilon=2^{18}M$ attempts.
- Each attempt costs at most `innerCount δ + 2` $\le276$ calls for $\delta\ge1/2$, and
  $276(2^{18}M+2)\le2^{27}(1+M)$.

The output is seed-independent (exact oracle, deterministic method), so the almost-sure accuracy yields
an integrable residual with expectation at most $\varepsilon$.

## Comparison and limitations

- In the second-order regime $\varepsilon\le L_1^2/L_2$ the bound is $O(1+L_2R^2/\varepsilon)$, the
  $p=2$ case of Lin–Jordan, Perseus (arXiv 2205.03202 v7, Theorem 3.7, Minty, bounded domain) and of the
  repository's full-range theorem; in the complementary regime it is $O(1+L_1^2R^2/\varepsilon^2)$, the
  extragradient rate (Diakonikolas–Daskalakis–Jordan 2021), obtained here by the same second-order
  method without switching algorithms. The point of the theorem is the single expression matching the
  lower bound in both regimes; it is not an improvement over the best known rate in either regime.
- The range $\rho L_1\le1$ keeps the constants universal; the full-range theorem covers
  $1<\rho L_1<2$ with margin-dependent constants, and the optimal margin dependence is open.
- The constant $2^{27}$ is not optimized. Each Jacobian query is a full Jacobian, not a
  Jacobian-vector product, and the cubic subproblem is solved exactly by classical choice; the bound is an
  oracle-call bound, not an arithmetic complexity.
