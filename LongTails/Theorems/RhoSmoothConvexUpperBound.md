This result gives a gradient-method upper bound for convex \((\rho,L_0,L_1)\)-smooth minimization when only the distance to a minimizer is bounded. Its lower-bound companion, [RhoSmoothConvexLowerBound](RhoSmoothConvexLowerBound.md), matches it up to a factor \((\rho-1)^{-2}\) and universal constants. Write

\[
G=(L_0/L_1)^{1/\rho},\qquad Q=\Big(\frac{L_0R}{G}\Big)^2=R^2L_0^{2-2/\rho}L_1^{2/\rho}.
\]

The [main theorem](RhoSmoothConvexUpperBound.lean) proves that an explicit three-phase method reaches \(f(x)-f^\star\le\varepsilon\) after

\[
\Big\lceil 9\sqrt{L_0R^2/\varepsilon}+262144\,(1+Q)\Big\rceil
\]

gradient calls, for every \(\rho\in(1,2]\) and every \(\varepsilon>0\). The constants do not depend on \(\rho\).

## Setup

The setup is [RhoSmoothRadiusConvex](../Setups/RhoSmoothRadiusConvex.lean). The function \(f\) is convex on a real Hilbert space, and the oracle returns its exact gradient. That gradient is differentiable, with

\[
\|D\nabla f(x)\|\le L_0+L_1\|\nabla f(x)\|^{\rho},\qquad 1<\rho\le2 .
\]

Some minimizer satisfies \(\|x^0-x^\star\|\le R\).

- **Provenance.** This is the \(\ell\)-smoothness of [Li et al., NeurIPS 2023](https://arxiv.org/abs/2306.01264) with \(\ell(s)=L_0+L_1s^\rho\). It is also the \((\rho,L_0,L_1)\) example of [Tyurin, arXiv:2508.06884v2](https://arxiv.org/abs/2508.06884), Section 5.1.
- **Radius-only class.** As in [Descending Everest I, arXiv:2610.21461v2](https://arxiv.org/abs/2610.21461), there is no bound on the initial gap \(\Delta=f(x^0)-f^\star\) or on the initial gradient.
- **Public parameters.** Unlike the \(\rho=1\) setup [RadiusOnlyGeneralizedSmoothConvex](../Setups/RadiusOnlyGeneralizedSmoothConvex.lean), the parameters \(R\) and \(\varepsilon\) are public. The method uses \(R\) in its momentum initialization.

Success is almost sure, i.e. \(f(\text{output})-f^\star\le\varepsilon\) for every seed. The algorithm and oracle are deterministic, so this also implies the expected-accuracy criterion used by the lower bound.

## Algorithm and output

The algorithm is [RhoSmoothThreePhase](../Algorithms/RhoSmoothThreePhase.lean). It makes one gradient call per step and returns the current point.

1. **Deep cuts.** While \(\|g\|\ge G\), step \(x\leftarrow x-D\,g/\|g\|\), with \(D=G/(4\ell(2G))\ge G/(20L_0)\).
   - The local lemma (\(\ell\)-smoothness along short segments, [RhoSmoothLocal](../Proofs/RhoSmoothLocal.lean)) gives \(\langle g,x-x^\star\rangle\ge D\|g\|\). So \(\|x-x^\star\|^2\) drops by \(D^2\) per step.
   - There are at most \(\lceil R^2/D^2\rceil\le 400Q+1\) such steps, and no step increases the distance.
2. **\(\ell\)-adaptive gradient descent.** Take \(K_1=\lceil 43r+174763r^2\rceil+1\) steps with step size \(1/(4\ell(2\|g\|))\), where \(r=L_0R/G=\sqrt Q\).
   - Starting from a point with \(\|g\|<G\) and \(f-f^\star\le GR\), a two-regime telescoping argument brings the gap below \(G^2/(16384L_0)\). This is `gd_rate` in [RhoSmoothPhaseOne](../Proofs/RhoSmoothPhaseOne.lean).
3. **Accelerated gradient descent.** Run AGD in the form of Tyurin's Algorithm 1, with step \(1/(8L_0)\) and \(\Gamma_0=\min\{G^2/(8192L_0R^2),8L_0\}\).
   - An induction (`inv_step` in [RhoSmoothPhaseTwo](../Proofs/RhoSmoothPhaseTwo.lean)) keeps the Lyapunov value below \(\Gamma_kR^2\) and every query within \(3R\) of \(x^\star\).
   - Every query also has gradient norm at most \(G/4\). There \(\ell\le 2L_0\), so local cocoercivity holds.
   - The rate is \(\Gamma_m\le 72L_0/m^2\).

The budget arithmetic is in [RhoSmoothUpperRun](../Proofs/RhoSmoothUpperRun.lean), `budget_sufficient`. It counts every call of the three phases against the actual `execute` trajectory.

## Relation to prior work

| Result | Class | Bound |
| --- | --- | --- |
| [Tyurin v2](https://arxiv.org/abs/2508.06884), §5.1 (ICML 2026) | gap \(\Delta\) and radius \(R\), \(\rho<2\) | \(\sqrt{L_0R^2/\varepsilon}+Q+L_1\Delta^{\rho/2}R^{2-\rho}/\bar\delta^{1-\rho/2}\) (and \(L_0R^2/\Delta\)), with \(\bar\delta=\min\{G^2/L_0,\,L_0R^2,\,\Delta\}/64\) |
| [Li et al. 2023](https://arxiv.org/abs/2306.01264) | gap-bounded \(\ell\)-smooth | accelerated rate with constants depending on \(\Delta\) |
| [Everest I v2](https://arxiv.org/abs/2610.21461), Thm 3.7 | radius-only, \(\rho=1\) | \(\sqrt{L_0R^2/\varepsilon}+(1+L_1R)\log(2+L_1R)\) |
| **This theorem** | radius-only, \(\rho\in(1,2]\) | \(\sqrt{L_0R^2/\varepsilon}+Q\) |

Tyurin's bound requires \(\Delta\). Its \(\Delta\)-dependent term is unbounded on the radius-only class, where it gives no guarantee. Here the \(\Delta\) term is removed entirely, the value \(\rho=2\) is included, and the remaining \(\varepsilon\)-free term \(Q\) equals Tyurin's \(L_0R^2/\bar\delta\) term up to the constant 64. Tyurin's conclusion (Section 6) lists the optimal non-dominant, \(\varepsilon\)-free term as unresolved. The companion lower bound shows that \(Q\) is necessary on the radius-only class, up to \((\rho-1)^2\) and constants.

The individual ingredients are standard: normalized steps, \(\ell\)-adaptive GD, and AGD started below a gradient threshold. The new part is the radius-only, \(\Delta\)-free statement and the phase-transition bookkeeping that turns the deep-cut depth \(G/L_0\) into the \(Q=(R/(G/L_0))^2\) term. This upper bound's novelty is modest; the main contribution is the matching lower bound.

## Limitations

- The method needs \(L_0\), \(L_1\), \(\rho\) and \(R\).
- The guarantee is for exact gradients only.
- For \(\rho\downarrow1\) the companion lower bound degrades like \((\rho-1)^2Q\). The pair is tight only up to a \((\rho-1)^{-2}\) factor: the upper bound's cut depth \(G/L_0\) is compared with the lower bound's saturation scale \(\int_0^\infty ds/\ell(s)\asymp G/((\rho-1)L_0)\). At \(\rho=1\), the known answer is \(L_1R\) up to a logarithm (Everest I).
- The class with a known initial gap \(\Delta\) is not treated separately.

## Scope compliance

This pair was produced under the requirement to close an important, popular setup with almost tight upper and lower bounds stated in terms of `Template` and `TemplateLowerBound`. Here is how each part is met.

1. **An almost tight pair on one class.** [RhoSmoothConvexUpperBound](RhoSmoothConvexUpperBound.lean) proves `Convergence` on [RhoSmoothRadiusConvex](../Setups/RhoSmoothRadiusConvex.lean). [RhoSmoothConvexLowerBound](RhoSmoothConvexLowerBound.lean) proves `NonConvergence` on [RhoSmoothConvexFull](../Setups/RhoSmoothConvexFull.lean), whose admissible instances are exactly the upper-bound ones on \(\mathbb R^d\) (via `toRadius`). Both budgets are written with the same `let G := (L0/L1)^(1/ρ)`, and they contain the same two terms, \(\sqrt{L_0R^2/\varepsilon}\) and \((L_0R/G)^2\). They match up to universal constants and a factor \((\rho-1)^{-2}\), with no logarithm. The setups differ in two ways:
   - the lower bound's validity adds \(\varepsilon\le L_0R^2/16\) and \(d\ge\lceil2^{44}(1+Q+\sqrt{L_0R^2/\varepsilon})^6\rceil\);
   - the upper bound is almost sure, while the lower bound fails the weaker expected-accuracy criterion.
2. **Both bounds are new.** The upper bound is the first radius-only (\(\Delta\)-free) bound for \(\rho>1\), and its techniques are modest. The lower bound is the first for \(\rho>1\) beyond \(\sqrt{L_0R^2/\varepsilon}\), obtained with a new separable saturating dual.
3. **An important, popular setup.** The class is \(\ell\)-smoothness ([Li et al., NeurIPS 2023](https://arxiv.org/abs/2306.01264)) with \(\ell(s)=L_0+L_1s^\rho\). The pair answers, for this family on the radius-only class, the question that [Tyurin (ICML 2026)](https://arxiv.org/abs/2508.06884), Section 6, leaves open: the optimal \(\varepsilon\)-free term. It is also the \(\rho>1\) counterpart of [Descending Everest I](https://arxiv.org/abs/2610.21461).
4. **Overlap check against the updated main, without rebasing.** On 2026-11-25, remote `main` contained no convex \(\ell\)-smooth setups. The related merged PRs #244 and #252 are nonconvex or stochastic. The open PRs #215, #257 and #258 do not overlap. An arXiv search the same day found no overlapping newer work.
