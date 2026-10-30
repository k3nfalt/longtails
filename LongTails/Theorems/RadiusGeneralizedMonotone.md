# A radius-only curvature transient for monotone root finding

The [main theorem](RadiusGeneralizedMonotone.lean) proves an exact-oracle complexity bound
\[
2\left\lceil 32768\left(1+\frac{L_0R}{\varepsilon}+(L_1R)^{4/3}\right)\right\rceil
\]
for returning a point with \(\|F(x)\|\le\varepsilon\). Write \(A=L_0R/\varepsilon\) and \(C=L_1R\). The contribution is a dimension-free reduction of the worst-case radius-only curvature transient from \(C^2\) to \(C^{4/3}\), while retaining the linear \(A\) term. It concerns monotone root finding, including convex-concave saddle operators; it is not an improved theorem for Nesterov's original minimization algorithm.

## Problem, information, and scope

The [setup](../Setups/RadiusGeneralizedLipschitzMonotone.lean) specifies a continuous monotone operator on a real inner-product space, hence includes every finite dimension. There exists an unknown root \(u\) with \(\|x_0-u\|\le R\). For every segment on which \(\|F\|\le M\),
\[
\|F(x)-F(y)\|\le (L_0+L_1M)\|x-y\|.
\]
This is the continuous, maximum-free formulation of the established 1-symmetric generalized Lipschitz assumption. The parameters satisfy \(L_0>0,L_1\ge0,R\ge0,\varepsilon>0\). No differentiability, strong monotonicity, potential, finite sample space, or initial residual bound is imposed. The root is not supplied or used to construct queries; it appears only in the analysis.

The algorithm knows \(L_0,L_1,R,x_0\). In particular, knowledge of a valid radius is an information requirement: the existing anchored solver below does not need that radius to execute. Accuracy enters only the call budget. Each oracle query returns the full operator value at one point; arithmetic is uncharged. The setup permits unrestricted algorithms. The proof constructs the [warm-started anchored algorithm](../Algorithms/WarmAnchoredMonotone.lean), whose named `output` is its current anchored iterate. Exact answers make its accuracy pathwise; the framework expresses success almost surely for any admissible oracle seed distribution.

These assumptions are those of the monotone case of Choudhury and Loizou, Assumption 1.1 with alpha equal to one and Section 3.2, [NeurIPS 2025 proceedings](https://proceedings.neurips.cc/paper_files/paper/2025/hash/6699e1ef78e8e2e12ee3ca5fec34b28e-Abstract-Conference.html), [arXiv:2510.22421v1](https://arxiv.org/abs/2510.22421v1). Their Theorem 3.6 gives an order \(A^2+C^2\) exact-call bound. Its proof in Appendix D.3.2 sums squared short normalized movements. Our operator class is unchanged; the algorithm and radius information differ.

## Algorithm and mechanism

Put \(h=C^{1/3}\) and \(B=8L_0R\exp(2h)\). If \(C<1\), skip the warm phase. Otherwise perform \(W=\lceil4C^{4/3}\rceil+1\) warm blocks. At a point with \(G=\|F(x)\|>B\), update
\[
x^+=x-\frac{h}{2L_1G}F(x).
\]
When \(G\le B\), keep the point fixed for the remaining warm blocks. Each block makes two calls at the same point, using the first and discarding the second. Frozen blocks also make both calls. This harmless padding aligns the state machine with two-call anchored iterations; it is included in the public budget.

After warming, initialize the existing [anchored extragradient algorithm](../Algorithms/AnchoredExtragradient.lean) at the warm point and run it for the remaining blocks. Its variable step, anchor weight, and two-query update are unchanged. The exact remaining count at a total of \(2N\) calls is \(N-W\) anchored iterations; the theorem applies the established accuracy bound with index \(n=N-W-1\).

The new ingredient is a quantitative radial support estimate valid for nonlinear, nongradient monotone operators. Finite chaining of the segment assumption proves
\[
\|F(u+v)\|\le 2L_0\|v\|e^{2L_1\|v\|}.
\]
For \(\|x-u\|\le R\), \(0\le t\le R\), and \(G\ge8L_0R e^{2L_1t}\), compare monotonicity at \(x\) and \(u+tF(x)/G\). It gives
\[
\langle F(x),x-u\rangle\ge tG/2.
\]
Consequently the normalized step of length \(t/2\) decreases squared distance to the root by at least \(t^2/4\). This permits a step longer than the usual local scale \(1/L_1\); it does not require local objective descent or a nonincreasing residual. The comparison point is only used in the proof.

Taking \(t=h/L_1\) makes every active warm step decrease squared distance by \(h^2/(4L_1^2)\). More than \(4C^{4/3}\) such steps are impossible. Freezing then guarantees a warm point within radius \(R\) and with residual at most \(B\). For \(C<1\), root growth already gives that bound at the start. The existing anchored proof needs
\[
\left\lceil 11A+(27C+4)\log\{1+8A(1+8Ce^{2h})\}\right\rceil+1
\]
iterations. Its logarithm contributes order \(A+C h+C\log(2+C)\), balancing the warm cost \(C^2/h^2\) at \(h=C^{1/3}\). The formal conservative inequalities bound the complete block count by \(18115A+1004C^{4/3}+4\), below the public budget. Zero radius and \(L_1=0\) are covered without divisions in an active warm phase.

## Strongest comparisons and limitations

The strongest dimension-free comparator is already present in the recorded repository base: [AnchoredGeneralizedMonotone](AnchoredGeneralizedMonotone.lean) proves
\[
O\bigl(A+(1+C)\log(1+(L_0+L_1G)R/\varepsilon)\bigr).
\]
Its initial-residual parameter can be eliminated by root growth, but this yields \(O(1+A+C^2)\) in the worst case. Simply substituting a radius bound, applying short clipped extragradient, or using a regularized strongly monotone finisher does not give the new exponent. The anchored finish and its accelerated residual potential are reused, not claimed as new. The gain is significant when \(C\) grows and \(A=o(C^2)\); for \(A\le C\), the worst-case comparison improves by order \(C^{2/3}\). When the initial residual is already small, the old anchored guarantee can be better, and it requires less public information.

Unrestricted oracle complexity also permits expensive center-of-gravity computations. The standard volume-reduction argument, using the centroid theorem in [Nemirovski's lectures, pages 18–22](https://people.orie.cornell.edu/miketodd/Lect_EMCO.pdf), gives stronger dimension-dependent competitors. Applying the radial support estimate at \(t=1/L_1\) yields a controlled-residual warm start in \(O(d\log(2+C))\) cuts, followed by an anchored finish: \(O(A+(C+d)\log(2+C))\). Alternatively, localized extragradient cuts with the exponentially large ball Lipschitz modulus give \(O(d[C+\log(1+A)])\). These are standard reductions, not additional proved Lean results here. Both calls of an extragradient cut must be counted. Thus the claimed improvement is over dimension-free bounds, and also over these comparators in high-dimensional regimes such as \(d\ge C^2,A\le C,C\to\infty\). There is no fixed-dimensional optimality claim.

The leading term matches the familiar high-dimensional lower bound for deterministic gradient-span methods in the globally Lipschitz subclass; see Yoon and Ryu, [ICML 2021, Theorem 3 and Corollary 3](https://proceedings.mlr.press/v139/yoon21d.html), whose stated algorithm class is `A_sep`. This citation alone does not establish a randomized unrestricted minimax lower bound for the present setup. No lower bound matching the new curvature exponent is established here. The final constant is deliberately loose. There is no stochastic, constrained, composite, weak-Minty, or alpha-less-than-one extension. Knowing \(R\) is required. The theorem does not improve the complexity of ordinary extragradient or Nesterov's method under a fixed update restriction.

The current comparison also checked [2610.16886v1](https://arxiv.org/abs/2610.16886v1) (Theorems 3.1–3.2 give constrained gap criteria; Corollary 3.3 gives an unconstrained past-extragradient residual bound of order \(A^2+C^2\); Corollary 3.5 improves strongly monotone guarantees), [2610.14839v1](https://arxiv.org/abs/2610.14839v1) (quantitative parameter-free rates with quasisharpness), and [2610.12641v1](https://arxiv.org/abs/2610.12641v1) (stochastic strongly monotone stages). These October 2026 preprints do not supply the same radius-only monotone residual guarantee; they are not represented as accepted conference papers. Literature screening through 29 October 2026 covered the public 2025–2026 ICML, ICLR, and NeurIPS editions and recent arXiv revisions, with older foundational and stronger results followed separately. Absence from a search is not by itself evidence of novelty.

## Nonlinear instances and formal proof map

A concrete coupled family in any even dimension is
\[
F(x)=\frac{\sinh((r-1)_+)^3}{r}(x-u)+B(x-u),\qquad r=\|x-u\|,
\]
with the radial term defined as zero at zero and a dense skew-symmetric matrix \(B\). The radial term is the gradient of a convex radial potential; the skew term preserves monotonicity and makes the operator nongradient. Its radial and tangential derivatives obey a bound \(5+5\sinh((r-1)_+)^3\); skew orthogonality gives \(\|F(x)\|\ge\sinh((r-1)_+)^3\). Thus \((L_0,L_1)=(5+\|B\|,5)\) suffices independently of dimension. Residuals can grow exponentially with radius. This example illustrates scope, not a lower bound or a claim about practical prevalence. The central proof handles changing operator directions and arbitrary interacting coordinates, without diagonalization or scalar reduction.

[MonotoneRadialSupport](../Proofs/MonotoneRadialSupport.lean) proves growth, support, and the distance decrement. [WarmMonotoneRun](../Proofs/WarmMonotoneRun.lean) proves radius preservation, freezing, and termination below the threshold. [WarmMonotoneExecution](../Proofs/WarmMonotoneExecution.lean) connects every raw query to the warm recursion and existing anchored execution. [WarmMonotoneBudget](../Proofs/WarmMonotoneBudget.lean) proves the explicit scalar and rounding bounds. The public theorem uses the setup's `spec`, constructs the actual algorithm, and transfers exact-oracle execution to every admissible oracle. No existing statement, core definition, or oracle interface is weakened.
