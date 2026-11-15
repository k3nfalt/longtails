# Interpolation preserves the generalized-smooth finite-sum complexity barriers

## Result and scope

The [Lean theorem](ExpectedInterpolatedGeneralizedFiniteSumLowerBound.lean) proves a lower oracle-complexity bound for convex finite sums whose components share a minimizer. Write

\[
F(x)=\frac1n\sum_{i=1}^n f_i(x),\qquad
H=\frac{L_0R^2}{\varepsilon},\qquad q=L_1R,\qquad
D=1+\log(2+n+q+H).
\]

The [setup](../Setups/ExpectedInterpolatedGeneralizedFiniteSum.lean) requires each component to be convex and differentiable, its gradient to be differentiable, and

\[
\|D\nabla f_i(x)\|\le L_0+L_1\|\nabla f_i(x)\|\quad\text{for every }i,x.
\]

There is a common component minimizer \(x_\star\) with \(\|x_\star\|\le R\) and \(F(0)-F(x_\star)\le\Delta\). The parameters, including a common per-component bound \(L_0\), are public. A query selects any component and any point and receives its exact value and gradient. Algorithms may be adaptive and randomized; no update-family, span, bounded-query, or output-selection restriction is imposed.

For every valid parameter choice, every algorithm, and every integer call budget

\[
b\le\left\lfloor
\frac{n+\sqrt{nH}+\sqrt n\,q+nq^{2/3}}
{10^9D^2}
\right\rfloor,
\]

there is an admissible instance on which the returned point fails the setup's expected-accuracy requirement

\[
\int [F(\widehat x(\omega))-F(x_\star)]\,dP(\omega)\le\varepsilon.
\]

The requirement explicitly includes integrability. The measure is the product of the algorithm's seed law and the oracle's seed law; the hard oracle is deterministic. The hard instance can depend on the algorithm and budget, but not on the algorithm's realized seed. The theorem includes zero calls and the displayed endpoint, and uses `NonConvergence`, rather than merely negating an upper-bound theorem.

The parameter regime is

\[
n\ge2,\quad L_0,R,\varepsilon>0,\quad L_1\ge0,\quad
H\ge4n,\quad\Delta\ge2\varepsilon,
\quad d\ge\left\lceil2^{80}(1+n+q+H)^{24}\right\rceil.
\]

The dimension requirement is a deliberately loose polynomial sufficient for hiding coordinates from arbitrary adaptive queries, including the final output. This is a large-dimensional worst-case lower bound, not a lower bound in every dimension. The regime is nonempty: take \(n=2,L_0=8,R=\varepsilon=1,\Delta=2\), any \(L_1\ge0\), and any dimension above the displayed threshold. Every constructed instance has initial gap exactly \(2\varepsilon\). The nonempty example alone need not give a positive displayed integer budget. For fixed \(n\ge2\) and \(q\), letting \(H\to\infty\) makes \(\sqrt{nH}/(1+\log(2+n+q+H))^2\to\infty\); with dimension increased as required, the proved budget is unbounded. The conservative universal constant is not intended as a practical iteration estimate.

## What is new

The contribution is an interpolation lower bound retaining all four terms

\[
\widetilde\Omega\!\left(n+\sqrt{nH}+\sqrt n\,q+nq^{2/3}\right).
\]

It closes, up to logarithmic factors and in the stated regime, the interpolation question for selectable exact component value-and-gradient access and expected objective accuracy. The new result is the lower bound. The corresponding upper bound already follows from the strongest applicable published preprint; this contribution does not present that upper bound or the restart conversion below as new research.

The closest result is Rudomanov et al., *Descending Everest, Part II*, [arXiv:2611.04171v2](https://arxiv.org/html/2611.04171v2), a preprint. Its Assumptions 2.1–2.6 and Theorem 5.1 give an expected-cost upper bound with leading expression

\[
n(1+q^{2/3})+
\sqrt{n(L_0+L_1^2\delta)R^2/\varepsilon+nq^2}.
\]

Here \(\delta\) is a bound on component-minimum heterogeneity. Its lower-bound discussion in §7.2, Theorem 7.1, does not establish the interpolating case; §8.1 identifies that extension as unresolved. A zero heterogeneity parameter cannot simply be substituted into a hard instance whose component minimizers disagree. Our construction makes the minimizers coincide while retaining the generalized-smooth and component-search obstructions.

The comparison preserves the oracle and accuracy criterion. The source allows known individual \(L_{0,i}\) with controlled average; our setup uses the familiar special case of a common public per-component bound. The new lower bound already holds within that special case. It is not an improvement obtained by restricting the algorithm to a chosen implementation.

## Matching upper bound and its accounting

For \(q>0\), interpolation gives actual heterogeneity zero. At solver accuracy \(e\), use the source theorem's admissible positive certificate

\[
\bar\delta=3e/q^2.
\]

It satisfies both actual heterogeneity \(\le\bar\delta\) and the source's normalization \(q^2\bar\delta/e\ge3\). Equation (2.5) and Theorem 5.1 then give, up to universal constants,

\[
B=O\!\left(
S\log^2(7+n+L_0R^2/e+q^2+\Delta/e)
\right),\qquad
S=n+\sqrt{nL_0R^2/e}+\sqrt n\,q+nq^{2/3},
\]

for expected total component-oracle calls and expected loss at most \(e\). Appendix C.3 accounts for the local solves and all component calls. The case \(q=0\) uses Allen-Zhu, [*Katyusha*, JMLR 18(221), 2018](https://jmlr.org/papers/volume18/16-410/16-410.pdf), Corollary 3.5: AdaptReg plus Katyusha gives \(O(n\log(\Delta/e)+\sqrt{nL_0}R/\sqrt e)\) component-gradient work and expected objective accuracy. It does not use the undefined certificate \(3e/q^2\). Regularization adds a known vector to each queried gradient; the bound counts epoch full gradients and inner component calls.

The source states its theorem for twice continuously differentiable components. Our formal setup asks only for a differentiable gradient. The relevant proof extends without changing constants: the curvature inequality bounds the gradient derivative on every compact segment, because the gradient is continuous there. The mean-value inequality makes the gradient Lipschitz on that segment, hence absolutely continuous. Its derivative is measurable as a pointwise limit of finite differences, so the segment fundamental theorem of calculus applies. Convexity makes the Hessian symmetric positive semidefinite. These facts supply the integral-Hessian steps in A.1–A.4, G.2 and H.1; no continuity of the Hessian is needed in those steps. This is an extension of the source's regularity argument, not a claim that its printed theorem has identical hypotheses. Optional heuristic routines are unnecessary.

Expected stopping cost is converted to a deterministic cap as follows. Run the solver at \(e=\varepsilon/4\), with the corresponding certificate \(3\varepsilon/(4q^2)\). Suppose its expected cost is at most \(B\). Cap each independent run at \(K=\lceil8B\rceil\) calls. A run completes with probability at least \(7/8\), and its conditional expected loss given completion is at most \(2\varepsilon/7\). Completion is observable from the source's history certificates and stopping tests (§3/Algorithm 1, G.1 and H.2); it does not require the unknown optimum value.

Take \(M=\lceil\log(2\Delta/\varepsilon)/\log8\rceil\) fresh independent runs, return the first completed output, and return the initial point only if every run times out. Nonnegative loss and independence give expected loss at most

\[
2\varepsilon/7+\Delta8^{-M}<\varepsilon.
\]

The deterministic budget is \(KM\), counting every call in timed-out runs. This establishes an upper bound with additional logarithmic dependence on \(\Delta/\varepsilon\), comparable to the formal fixed-budget lower bound. This conversion is a standard reduction, not a novelty claim. The logarithms are real limitations: when \(\Delta/\varepsilon\) is exponentially large in another parameter, one cannot discard them and claim a radius-only uniform optimal rate.

## Mechanism and formal proof

A constant linear centering term preserves convexity and cancels in a paired average, but changes generalized smoothness. The [centering lemmas](../Proofs/InterpolatedFiniteSumCentering.lean) account for this change explicitly. For paired exponential components the transformation is

\[
C(e^{m(x)\pm kx_0}-1)
\quad\longmapsto\quad
C(e^{m(x)\pm kx_0}-1\mp kx_0),
\qquad k=2L_1/7.
\]

The tilts \(\pm Ck e_0\) are public and independent of the hidden instance. Given a centered value-and-gradient response, adding back this known affine function recovers the uncentered response with zero additional oracle calls. Generic centering by an unknown \(\nabla f_i(x_\star)\) would not justify such a reduction and could reveal hidden information; the explicit paired construction avoids that defect.

The centered components share a minimum when the latent chain vanishes and the carrier coordinate is zero. Their paired objective and indistinguishability structure survive. The curvature proof pays an additive term \(2CL_1^2/7\), absorbed in the public \(L_0\) allowance by choosing an auxiliary scale \(\delta=L_0/(4L_1^2)\). This auxiliary construction parameter is not nonzero heterogeneity of the final instance. The proof uses a full-space radial wall and the triangle inequality; it never assumes that the carrier is globally orthogonal to the latent gradient.

Four constructions cover the parameter regimes:

- A hidden quadratic component gives the \(n\) term.
- Independent smooth chains give \(\sqrt{nH}\).
- Paired centered exponential chains give \(\sqrt n\,q\), with logarithmic losses.
- A chain whose links occupy distinct hidden component pairs gives \(nq^{2/3}\), again with logarithmic losses.

For the last construction, all unused pairs have the same wall and carrier response. An odd unpaired component gives no information about the hidden placement. A Boolean replay policy independent of the hidden owner word permits exact averaging over distinct owner assignments. The [search bound](../Proofs/InterpolatedFiniteSumDistinctSearch.lean) controls the mean number of discovered links, while the [oracle coupling](../Proofs/InterpolatedFiniteSumLinkOracle.lean) and [actual replies](../Proofs/InterpolatedFiniteSumLinkReplies.lean) connect it to `execute` for unrestricted adaptive algorithms. A conjugate inequality telescopes through the discovered prefix to lower-bound objective loss; the terminal case and far-away outputs are handled separately.

Coordinate hiding is averaged over a finite prior, with an explicit collision, carrier, and unseen-coordinate error bound. The prior is selected before the algorithm's seed. [Finite-prior averaging](../Proofs/InterpolatedFiniteSumHiding.lean) then produces one fixed hard instance violating expected accuracy. This avoids imposing measurability assumptions on every intermediate algorithm state beyond the repository's existing framework.

The complete constructions and execution proofs are in [HiddenComponent](../Proofs/InterpolatedFiniteSumHiddenComponent.lean), [SmoothLower](../Proofs/InterpolatedFiniteSumSmoothLower.lean), [ExponentialLower](../Proofs/InterpolatedFiniteSumExponentialLower.lean), and [LinkLower](../Proofs/InterpolatedFiniteSumLinkLower.lean). [CombinedLower](../Proofs/InterpolatedFiniteSumCombinedLower.lean) proves all parameter cases and connects the simplified public budget to those constructions. There is no newly claimed upper-bound algorithm in this contribution.

## Motivation, assumptions, and limitations

Interpolation is the established common-minimizer model used in overparameterized optimization. It does not imply a strong-growth condition under general convex component geometry. Generalized smoothness allows gradients and curvature to grow without a global Lipschitz-gradient constant. Their combination is meaningful independently of this proof.

For a concrete nonlinear family, let

\[
f_i(x)=c_i\left[e^{a_i^\top(x-x_\star)}-1-a_i^\top(x-x_\star)\right],\qquad c_i>0.
\]

Then all components minimize at \(x_\star\), and

\[
\|\nabla^2 f_i(x)\|
\le c_i\|a_i\|^2+\|a_i\|\,\|\nabla f_i(x)\|.
\]

Thus \(c_i\|a_i\|^2\le L_0\) and \(\|a_i\|\le L_1\) imply the setup's curvature condition. Dense, overlapping, nonparallel features give nonlinear interactions between coordinates in arbitrary dimension; spanning features give a unique common minimizer. This is an elementary centered extension of the exponential example in Gorbunov et al., [arXiv:2409.14989v2](https://arxiv.org/html/2409.14989v2), Example 1.5 and Appendix B; its §7 supplies the interpolation context. Ordinary Poisson or logistic datasets need not share component minimizers, so this example does not assert interpolation for arbitrary real datasets.

The restriction \(H\ge4n\) is material. Outside it, bounded-\(q\) interpolation SGD can have complexity independent of \(n\), so a uniform \(\Omega(n)\) assertion would be false. Likewise, high dimension is essential to this unrestricted-algorithm hiding proof. No claim is made for low-dimensional minimax complexity, noisy component oracles, nonconvex objectives, or an arbitrary heterogeneity class.

The prior interpolation guarantee in Gorbunov et al., §7, controls a clipped objective-loss quantity. It is not directly an expected untruncated objective-gap bound; its nonvacuity regime and Polyak-style access to component minimum values must be retained in a comparison. The present lower bound allows value-and-gradient queries but does not give minimum component values as additional oracle data. A fixed success-probability guarantee is also not silently identified with expected accuracy.

The mathematical novelty is the surviving interpolation obstruction and its complete oracle-complexity consequence, not the Lean formalization, the new setup name, a constant improvement, or the reuse of known zero-chain techniques. The contribution is one new lower theorem paired in the comparison with an existing upper guarantee, rather than a second formal export of an already known upper bound.
