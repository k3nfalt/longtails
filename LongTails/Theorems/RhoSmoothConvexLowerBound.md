This result proves a randomized lower bound for convex \((\rho,L_0,L_1)\)-smooth minimization with only a radius bound. Together with [RhoSmoothConvexUpperBound](RhoSmoothConvexUpperBound.md), it determines the complexity of this class up to a factor \((\rho-1)^{-2}\) and universal constants, with no logarithmic gap. Write

\[
G=(L_0/L_1)^{1/\rho},\qquad Q=\Big(\frac{L_0R}{G}\Big)^2=R^2L_0^{2-2/\rho}L_1^{2/\rho},\qquad s=\sqrt{L_0R^2/\varepsilon}.
\]

The [main theorem](RhoSmoothConvexLowerBound.lean) proves that every randomized gradient method needs more than

\[
\Big\lfloor\frac{\sqrt{L_0R^2/\varepsilon}+(\rho-1)^2\,(L_0R/G)^2}{2^{30}}\Big\rfloor
\]

oracle calls to guarantee expected accuracy \(\varepsilon\). The upper bound uses \(O(\sqrt{L_0R^2/\varepsilon}+Q)\) calls. So, for each fixed \(\rho\in(1,2]\),

\[
N_\varepsilon(\mathcal P_R)=\Theta_\rho\big(\sqrt{L_0R^2/\varepsilon}+R^2L_0^{2-2/\rho}L_1^{2/\rho}\big).
\]

## Setup and statement

The setup is [RhoSmoothConvexFull](../Setups/RhoSmoothConvexFull.lean). Its admissible instances are exactly those of the upper-bound setup [RhoSmoothRadiusConvex](../Setups/RhoSmoothRadiusConvex.lean) on \(\mathbb R^d\):

- \(f\) is convex;
- the oracle returns the exact gradient, which is differentiable with \(\|D\nabla f\|\le L_0+L_1\|\nabla f\|^\rho\);
- some minimizer satisfies \(\|x^0-x^\star\|\le R\).

All parameters are public, which only strengthens the lower bound.

The validity conditions are:

- \(L_0,L_1,R,\varepsilon>0\) and \(1<\rho\le2\);
- \(\varepsilon\le L_0R^2/16\);
- \(d\ge\lceil2^{44}(1+Q+s)^6\rceil\).

Success means the output's expected gap is at most \(\varepsilon\), with the gap integrable. This criterion is weaker than the upper bound's almost-sure criterion, so failing it is the stronger statement.

The theorem covers every valid parameter choice, every algorithm, and every budget \(b\) up to the stated one, including \(b=0\). For each, it gives an admissible objective with a deterministic gradient oracle on which the actual `execute` output fails. The instance depends on the algorithm and on \(b\), not on the realized seed. Three proved cases appear in [RhoSmoothLowerBranches](../Proofs/RhoSmoothLowerBranches.lean):

1. \(b=0\): the existing zero-query instance.
2. \(s\ge (\rho-1)^2Q/16\): the existing mollified Nesterov instance ([MollifiedSmoothLowerBound](../Proofs/MollifiedSmoothLowerBound.lean)). It is \(L_0\)-smooth and therefore admissible (`transfer_failure`).
3. Otherwise: the new chain below, with \(b+1\le\lfloor (R/(13A))^2\rfloor\) links (`links_bound`).

## The new hard instance

The architecture follows Everest I ([arXiv:2610.21461v2](https://arxiv.org/abs/2610.21461), Section 4). The instance is the conjugate of a regularizer on the polytope \(K=\{z\ge0:\sum_iz_i/G_i\le1\}\), with geometric slopes \(G_i\). It uses Everest's Lemma 4.2: strong convexity of the dual along segments, with modulus \(1/\ell(\max\|\cdot\|)\), gives the two-point \(\ell\)-smoothness of the primal gradient. The randomized hiding pipeline is the repository's own (see below). The new ingredient is the dual regularizer.

**Separable saturating dual** ([RhoSmoothHardDual](../Proofs/RhoSmoothHardDual.lean)). The dual is \(H(z)=\sum_i\psi(z_i)\), where

\[
\psi'(r)=A\big(1-(1+r/G)^{1-\rho}\big),\qquad A=\frac{2G}{(\rho-1)L_0'},
\]

and \(L_0'=L_0/512\) is the internal constant. Then:

- \(0\le\psi'\le A\);
- \(\psi''(r)=(2/L_0')(1+r/G)^{-\rho}\ge 1/\ell'(r)\), using \((1+t)^\rho\le2(1+t^\rho)\) for \(\rho\le2\);
- \(H\) is strongly convex along every segment of \(K\) with modulus \(\min_i1/\ell'(z_i)\ge1/\ell'(\max\|\cdot\|)\) (`dual_segment`, `dual_growth`).

**Robust chain without a logarithm** ([RhoSmoothHardChain](../Proofs/RhoSmoothHardChain.lean), `field_tail_zero`). The construction uses ratio-2 slopes \(G_i=g\,2^{m-1-i}\), constant shift \(\sigma=6A\), and threshold \(\theta=A\).

- *Claim.* If the frontier coordinate is \(\ge-\theta\) and all later coordinates are \(\le\theta\), the maximizer puts no mass on later links.
- *Argument.* Move all later mass to the frontier at the polytope-preserving rate \(G_j/G_l\ge2\). The linear gain is at least \((\sigma-\theta)M-(\sigma+\theta)L\), with \(M\ge2L\). The penalty grows by at most \(AM\), because \(\psi\) is \(A\)-Lipschitz and the removed entries only lower it. The net gain is positive since \(\sigma>3\theta+2A\).
- *Gap.* The minimum value \(0\) is attained at \(-\sigma\mathbf 1\). Any point whose last coordinate is \(\ge-\theta\) has gap at least \(g(\sigma-\theta-A)=4\varepsilon\), with \(g=\varepsilon/A\) (`objective_gap`).
- *Why no logarithm.* Every scale is \(O(A)\). So \(\|x^\star\|=\sigma\sqrt m\le R/2\) allows \(m\asymp(R/A)^2\asymp(\rho-1)^2Q\) links.

This is where \(\rho>1\) is used. At \(\rho=1\) the derivative \(\psi'\) is unbounded, which is why Everest and the repository's [LogFreeGeneralizedSmoothLowerBound](LogFreeGeneralizedSmoothLowerBound.md) needed slowly decaying slopes and a Z-based radial term plus entropy. The tail-entropy regularizer of PR #194, transplanted to \(\rho>1\), would cost a \(\log^2Q\) factor: its minimizer is at distance \(\gtrsim\sqrt m\,c\log m\).

**Mollification and localization.** The chain gradient is globally \(\ell'(G_1)\)-Lipschitz, where \(G_1=g2^{m-1}\) is the peak slope. It is averaged with a compact bump of radius \(\min\{A/2,\,G/(4\ell'(G_1))\}\).

- The mollified Jacobian is bounded through the pointwise two-point bound: \(\|D\bar g\|\le\ell'(\|\bar g\|+G)\le(L_0+L_1\|\bar g\|^\rho)/64\) (`average_curvature`, `internal_curvature`).
- It is then embedded by a random coordinate injection and localized by the repository's polynomial-hinge wall ([AdaptivePolynomialLocalization](../Proofs/AdaptivePolynomialLocalization.lean)).
- The \(\rho\)-version of the wall's curvature estimate is [RhoSmoothHardLocalization](../Proofs/RhoSmoothHardLocalization.lean), `gradient_curvature`. Its new step is a Young-type split, `young_split`: for every mixing weight \(p\in[0,1]\),
  \[
  Kp\le L_0/4+(L_1/4)(p\,aB/2)^\rho \quad\text{whenever}\quad B\ge 1632\,n(n+1)\,G/L_0 .
  \]
  The wall coefficient \(a\) and the peak slope cancel out of this condition. So the wall width \(B=16R+1632n(n+1)G/L_0\), with hinge degree \(n=4m+80\), stays polynomial in \(Q\) even though \(G_1\) is exponential in \(m\).
- The hiding dimension is \(m+2m^2(4B)^2/(A/2)^2\le2^{36}(1+m)^6\) ([RhoSmoothHardParameters](../Proofs/RhoSmoothHardParameters.lean), `dimension_sufficient`).
- Seed independence and the treatment of the output as an observation come from the existing [FinitePrefixExpectation](../Proofs/FinitePrefixExpectation.lean) argument, reused unchanged.

## Comparison

| Result | Class | \(\varepsilon\)-free term |
| --- | --- | --- |
| [Tyurin v2](https://arxiv.org/abs/2508.06884), §5.1, upper bound (ICML 2026) | gap \(\Delta\) and radius, \(\rho<2\) | \(Q+L_1\Delta^{\rho/2}R^{2-\rho}/\bar\delta^{1-\rho/2}\); lists the optimal term as open (Section 6) |
| [Everest I v2](https://arxiv.org/abs/2610.21461), Thms 3.7/4.10 | radius-only, \(\rho=1\) | \(\Theta(L_1R)\) up to \(\log\) |
| repo [LogFreeGeneralizedSmoothLowerBound](LogFreeGeneralizedSmoothLowerBound.md) | radius-only, \(\rho=1\), randomized | \(\Omega(L_1R)\) |
| reduction \(\rho\)-class \(\supset(L_0/2,\,c_\rho L_0/G)\)-smooth class | radius-only, \(\rho>1\) | \(\Omega(\sqrt Q)\) only |
| **This theorem** | radius-only, \(\rho\in(1,2]\), randomized | \(\Omega((\rho-1)^2Q)\) |
| [RhoSmoothConvexUpperBound](RhoSmoothConvexUpperBound.md) | same class | \(O(Q)\) |

To our knowledge no lower bound for \(\rho>1\) beyond the \(\sqrt{L_0R^2/\varepsilon}\) term was known before. The reduction to the \(\rho=1\) lower bound shown in the table gives only \(\sqrt Q\). The quadratic phenomenon \(Q=(R/(G/L_0))^2\) comes from the bounded saturation scale \(\int_0^\infty ds/\ell(s)<\infty\), which exists only for \(\rho>1\).

## Limitations

- **\(\rho\)-gap.** The pair is tight only up to \((\rho-1)^{-2}\). The lower-bound scale \(A\asymp G/((\rho-1)L_0)\) is compared with the upper-bound cut depth \(G/(20L_0)\). As \(\rho\downarrow1\), the class transitions to Everest's \(L_1R\) regime.
- **Constants.** The lower-bound constant \(2^{-30}\) is small.
- **Dimension.** The lower bound needs dimension of order \((1+Q+s)^6\).
- **Oracle.** The lower bound is for gradient oracles. Everest I also allows function values.
- **Known-gap class.** The hard instance has an exponentially large initial gap \(\Delta\). The question for the class with a bounded known \(\Delta\), as in Tyurin's Corollary 5.3, is not settled here.
- **Accuracy criterion.** The upper bound is almost sure; the lower bound is in expectation. Since a deterministic almost-sure guarantee implies the expected one, the two bounds compare on the expected-accuracy criterion.

## Scope compliance

This pair was produced under the requirement to close an important, popular setup with almost tight upper and lower bounds stated in terms of `Template` and `TemplateLowerBound`. Here is how each part is met.

1. **An almost tight pair on one class.** [RhoSmoothConvexUpperBound](RhoSmoothConvexUpperBound.lean) proves `Convergence` on [RhoSmoothRadiusConvex](../Setups/RhoSmoothRadiusConvex.lean). [RhoSmoothConvexLowerBound](RhoSmoothConvexLowerBound.lean) proves `NonConvergence` on [RhoSmoothConvexFull](../Setups/RhoSmoothConvexFull.lean), whose admissible instances are exactly the upper-bound ones on \(\mathbb R^d\) (via `toRadius`). Both budgets are written with the same `let G := (L0/L1)^(1/ρ)`, and they contain the same two terms, \(\sqrt{L_0R^2/\varepsilon}\) and \((L_0R/G)^2\). They match up to universal constants and a factor \((\rho-1)^{-2}\), with no logarithm. The setups differ in two ways:
   - the lower bound's validity adds \(\varepsilon\le L_0R^2/16\) and \(d\ge\lceil2^{44}(1+Q+\sqrt{L_0R^2/\varepsilon})^6\rceil\);
   - the upper bound is almost sure, while the lower bound fails the weaker expected-accuracy criterion.
2. **Both bounds are new.** The upper bound is the first radius-only (\(\Delta\)-free) bound for \(\rho>1\), and its techniques are modest. The lower bound is the first for \(\rho>1\) beyond \(\sqrt{L_0R^2/\varepsilon}\), obtained with a new separable saturating dual.
3. **An important, popular setup.** The class is \(\ell\)-smoothness ([Li et al., NeurIPS 2023](https://arxiv.org/abs/2306.01264)) with \(\ell(s)=L_0+L_1s^\rho\). The pair answers, for this family on the radius-only class, the question that [Tyurin (ICML 2026)](https://arxiv.org/abs/2508.06884), Section 6, leaves open: the optimal \(\varepsilon\)-free term. It is also the \(\rho>1\) counterpart of [Descending Everest I](https://arxiv.org/abs/2610.21461).
4. **Overlap check against the updated main, without rebasing.** On 2026-11-25, remote `main` contained no convex \(\ell\)-smooth setups. The related merged PRs #244 and #252 are nonconvex or stochastic. The open PRs #215, #257 and #258 do not overlap. An arXiv search the same day found no overlapping newer work.
