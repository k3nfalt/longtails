This result removes the logarithm from the \(L_1R\) term of the lower bound for convex \((L_0,L_1)\)-smooth optimization with only a radius bound. Write

\[
s=\sqrt{L_0R^2/\varepsilon},\qquad q=L_1R .
\]

The [main theorem](LogFreeGeneralizedSmoothLowerBound.lean) proves that every randomized exact-gradient method needs

\[
\Omega\!\left(\sqrt{L_0R^2/\varepsilon}+L_1R\right)
\]

oracle calls to reach expected accuracy \(\varepsilon\). The best previously known lower bounds were \(\sqrt{L_0R^2/\varepsilon}+L_1R/\sqrt{\log(2+L_1R)}\) for deterministic methods with value-and-gradient oracles ([Descending Everest I](https://arxiv.org/abs/2610.21461), Theorem 4.10), and \(\sqrt{L_0R^2/\varepsilon}+L_1R/\log(2+L_1R)\) for randomized gradient methods in this repository ([FullGeneralizedSmoothConvexLowerBound](FullGeneralizedSmoothConvexLowerBound.md)). Everest I lists the lost \(\sqrt{\log(2+L_1R)}\) as an open question in Section 5 ("Logarithmic factors"). This result settles the lower-bound side of that question. The known upper bound still has one factor \(\log(2+L_1R)\), so the full complexity is determined only up to that factor.

## Setup and statement

The theorem reuses the existing setup [GeneralizedSmoothConvexFull](../Setups/GeneralizedSmoothConvexFull.lean) verbatim. No assumption is added or changed. Its admissible instances are exactly the ones of [RadiusOnlyGeneralizedSmoothConvex](../Setups/RadiusOnlyGeneralizedSmoothConvex.lean):

- \(f\) is convex on \(\mathbb R^d\);
- the oracle returns the exact gradient, and that gradient is differentiable with \(\|D\nabla f(x)\|\le L_0+L_1\|\nabla f(x)\|\);
- some minimizer satisfies \(\|x^0-x^\star\|\le R\).

There is no bound on the initial gap or gradient. Success means the expected optimality gap of the output, an integrable quantity, is at most \(\varepsilon\). All parameters are public, which only strengthens the class of algorithms covered.

The setup's validity conditions are \(L_0,R,\varepsilon>0\), \(L_1\ge0\), \(\varepsilon\le L_0R^2/16\), and \(d\ge\lceil 2^{44}(1+q+s)^5\rceil\). The case \(L_1=0\) is included.

The public budget is one line:

\[
\left\lfloor\frac{\sqrt{L_0R^2/\varepsilon}+L_1R}{2^{26}}\right\rfloor .
\]

For every valid parameter choice, every algorithm, and every integer budget \(0\le b\) up to this value, there is an admissible objective with a deterministic oracle on which the actual `execute` output fails the expected-accuracy criterion. The instance may depend on the algorithm and on \(b\), but not on the algorithm's realized seed. The proof covers every \(b\), including \(0\), and every \(q\ge0\), through three proved cases in [TailEntropyBudget](../Proofs/TailEntropyBudget.lean):

1. When the budget is \(0\), the existing zero-query branch applies.
2. When \(s\ge q\), the existing mollified Nesterov branch, [MollifiedSmoothLowerBound](../Proofs/MollifiedSmoothLowerBound.lean), proves failure for \(b\le\lfloor s/16384\rfloor\).
3. When \(q>s\) and \(q\ge2^{24}\), the new chain branch, [TailEntropyChainLowerBound](../Proofs/TailEntropyChainLowerBound.lean), proves failure for every \(b\le\lfloor q/2^{25}\rfloor\).

## The new hard instance

The construction keeps Everest I's architecture: a conjugate chain on the polytope \(K=\{z\ge0:\sum_i z_i/G_i\le1\}\) with geometric slopes \(G_i\), and Everest's Lemma 4.2, which turns strong convexity of the dual along segments into \((L_0,L_1)\)-smoothness. Those parts are prior work. The new parts are the dual regularizer and the argument that later links stay inactive.

**Regularizer.** Everest's dual has the form \(2\Phi(Z)+Z\sum_i r(z_i/Z)\), with \(Z=\sum_i z_i\) and a separable \(r\). Its curvature requirement at spread gradients (\(\|z\|\approx Z/\sqrt n\)) forces \(r'(1)\gtrsim\log n/L_1\). The KKT margin between consecutive links must exceed this quantity, so the shifts are \(\sigma\gtrsim \log n/(L_1h)+nh/L_1\). The chain then fits only \(n\approx L_1R/\sqrt{\log n}\) links. This is exactly where the \(\sqrt{\log}\) is lost.

The separable term is replaced by a non-separable *tail-ratio entropy*:

\[
H(z)=2\Phi(Z)+\frac{28}{L_1}\Big(\sum_m z_m\log\frac{z_m}{T_m}+Z\log n\Big),\qquad T_m=\sum_{i\ge m}z_i .
\]

Its primal is a nested one-sided smooth maximum \(\operatorname{smax}(v_1,\operatorname{smax}(v_2,\dots))\). Each later link competes only with the next one, and it is switched off *exactly* once it falls a constant margin behind. Two lemmas make this work.

* **Curvature.** [TailEntropyCurvature](../Proofs/TailEntropyCurvature.lean), `curvature_bound`: for \(z\ge0\) and every direction \(u\), the second derivative of \(\sum_m z_m\log(z_m/T_m)\) along \(u\) equals \(\sum_m (u_m-z_mU_m/T_m)^2/z_m\), and

  \[
  \Big\|u-\tfrac{U}{Z}z\Big\|^2\le 14\,\max_i z_i\sum_m\frac{(u_m-z_mU_m/T_m)^2}{z_m}.
  \]

  The proof is a telescoping potential \(2T_m\min(T_m,\max z)\,c_m^2\). With Everest's radial/tangent split this gives modulus \(1/(L_0+L_1\max\|\cdot\|)\) along segments ([TailEntropySegments](../Proofs/TailEntropySegments.lean), `dual_segment_bound`). That in turn gives the \((L_0,L_1)\) pair bound for the conjugate gradient ([TailEntropyConjugate](../Proofs/TailEntropyConjugate.lean)). The bound uses \(\max_i z_i\) rather than \(\|z\|\), so concentrated gradients are covered.

* **Robust chain by mass transfer.** [TailEntropyTransfer](../Proofs/TailEntropyTransfer.lean), `optimizer_later_zero`. If the maximizer put mass on links after \(j\), moving that mass to link \(j\) at the polytope-preserving rate \(G_j/G_l\) would strictly increase the objective. The entropy changes by at most \(\sum_{l>j}(l-j)z_l\) ([TailEntropyChain](../Proofs/TailEntropyChain.lean), `entropy_move`). So only a *cumulative* margin \(\beta(l-j)\) is needed, and the geometric slopes absorb it at a cost of \(\beta/h\), instead of \(\log n/h\).

  With constant shifts \(\sigma=2\Phi'(G_1)+\tfrac{28}{L_1}\log n+\tfrac{140}{L_1h}\) and \(h=1/\sqrt n\), the robust chain property holds whenever the frontier coordinate is \(\ge-14/L_1\) and all later coordinates are \(\le 14/L_1\) ([TailEntropyHardChain](../Proofs/TailEntropyHardChain.lean), `field_tail_zero`). The threshold is independent of \(h\). For the internal parameters \((L_0/4,L_1/4)\) used in the formal chain, \((L_1/4)\sigma\le142\sqrt n+28\log n+4\log(1+q)\), so \(\|\sigma\|\le R/4\) for \(n\approx q/2^{25}\) links ([TailEntropyParameters](../Proofs/TailEntropyParameters.lean), `level_bound`, `shift_norm_le`). The link count has no logarithm.

The gap is at least \(252\varepsilon\) whenever the last link is not passed (`objective_gap`), and the minimum value \(0\) is attained at \(-\sigma\). The instance is nonlinear and non-separable: coordinates interact through \(T_m\) and \(\Phi(Z)\).

**Randomization.** The chain is internally run with \((L_0/4,L_1/4)\) and mollified by a compact bump of radius \(\min\{1/(4L_1),R/(16\sqrt n)\}\) ([TailEntropySmoothedChain](../Proofs/TailEntropySmoothedChain.lean)). It is then embedded along a random coordinate embedding with hiding threshold \(28/L_1\), using the repository's polynomial localization wall ([TailEntropyLocalizedChain](../Proofs/TailEntropyLocalizedChain.lean), [TailEntropyHardOracle](../Proofs/TailEntropyHardOracle.lean)). Seed independence comes from the existing [FinitePrefixExpectation](../Proofs/FinitePrefixExpectation.lean) argument, which counts the final output as an observation. This pipeline is reused from the known-gap and polynomial-dimension contributions (PRs #168 and #188) and is not claimed as new.

The robust threshold \(\Theta(1/L_1)\) does not shrink with the slope ratio \(h\) (the known-gap chain used \(\min(h,1)/(8L_1)\)), so no further logarithm enters through mollification or hiding. The dimension it needs, \(n+2n^2(4\cdot131072R\,L_1/28)^2\le n+q^4/100352\), fits inside the setup's existing dimension condition ([TailEntropyParameters](../Proofs/TailEntropyParameters.lean), `dimension_sufficient`).

## Comparison

| Result | Model | \(L_1R\) term |
| --- | --- | --- |
| [Everest I v2](https://arxiv.org/abs/2610.21461), Thm 4.10 (preprint, 5 Nov 2026) | deterministic, value+gradient, dimension \(2n\) | \(L_1R/\sqrt{\log(2+L_1R)}\) |
| [FullGeneralizedSmoothConvexLowerBound](FullGeneralizedSmoothConvexLowerBound.md) (PR #172) | randomized, gradient, polynomial dimension | \(L_1R/\log(2+L_1R)\) |
| **This theorem** | randomized, gradient, polynomial dimension | \(L_1R\) |
| [Everest I v2](https://arxiv.org/abs/2610.21461), Thm 3.7, upper bound | gradient | \((1+L_1R)\log(2+L_1R)\) |
| [RadiusFreeGeneralizedAccelerated](RadiusFreeGeneralizedAccelerated.md), upper bound | gradient | \((1+L_1R)\log(2+L_1R)\) |

In the same randomized gradient model as the repository's previous theorem, the full \(\log(2+q)\) factor is removed. The improvement is asymptotic: with the explicit constants, the new budget \(q/2^{26}\) exceeds the previous \(q/(2^{23}\log(2+q))\) only once \(\log(2+q)>8\), roughly \(q\gtrsim3000\). Against Everest's Theorem 4.10 the model differs. Randomized algorithms make this theorem stronger, while the gradient-only oracle makes it weaker. Neither formal statement contains the other.

Both upper bounds keep a single \(\log(2+L_1R)\), which Everest I attributes to the line search. The complexity is therefore \(\Theta(\sqrt{L_0R^2/\varepsilon}+L_1R)\) up to that one logarithm, which appears only in the upper bound. Whether the large-gradient regime can be passed in \(O(1+L_1R)\) calls (Everest I, Section 5) remains open.

The \(\sqrt{L_0R^2/\varepsilon}\) term is classical and its branch is reused. [Descending Everest II](https://arxiv.org/abs/2611.04171) (v2, Theorem 7.1) concerns sums of at least two components and loses \(\log^2N_0\). It does not give a single-function bound.

**Deterministic value-and-gradient corollary (not formalized).** The same chain gives Everest's model as well. With threshold \(0\), `optimizer_later_zero` shows that queries in the span of the first \(j-1\) coordinates return gradients in the span of the first \(j\). The minimizer has norm \(\le R\), and the value is at least \(2\varepsilon\) whenever the last coordinate vanishes. Since the maximizer lies on the prefix face, function values also depend only on the prefix. Everest's Proposition 4.3, with \(d=2n\), then gives \(1+N\ge c(\sqrt{L_0R^2/\varepsilon}+L_1R)\) for deterministic methods with value-and-gradient oracles. This remark is a paper-level consequence and is not part of the Lean theorem.

## Scope and limitations

The task asked to remove the logarithm term in the lower bound for \((L_0,L_1)\)-smooth convex functions. This theorem does so for the radius-only class with a single objective, every accuracy in the setup's range, and every \(L_1\ge0\).

- The known-gap class (repository [KnownGapGeneralizedSmoothLowerBound](KnownGapGeneralizedSmoothLowerBound.md), Everest I Appendix B), the small-gap class \(\mathcal P_{4\varepsilon}\), and finite sums are not addressed. Their lower bounds keep their logarithms.
- Value oracles are covered only by the unformalized deterministic remark.
- The constants (\(2^{26}\), \(2^{25}\)) and the polynomial dimension have considerable slack.
- The result concerns a fixed oracle budget, not expected stopping time.
- No upper bound is improved.

Literature was checked through 18 November 2026: Everest I v2 (5 Nov 2026), Everest II v2, Everest III v1 (variational inequalities), and recent arXiv \((L_0,L_1)\) papers. The Everest papers are unrefereed preprints.
