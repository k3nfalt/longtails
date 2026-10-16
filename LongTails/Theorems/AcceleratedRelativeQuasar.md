# Acceleration with relative gradient error beyond convexity

The [Lean theorem](AcceleratedRelativeQuasar.lean) gives a fixed oracle-call guarantee for smooth strongly quasar-convex objectives with a deterministic relative-error gradient oracle. The contribution is a robustness guarantee on a standard nonconvex class: the accelerated condition-number dependence survives relative errors of fourth-root order. It does not improve exact-gradient acceleration, establish a minimax lower bound, or claim acceleration for every PL objective.

The specification is [RelativeGradientStrongQuasar](../Setups/RelativeGradientStrongQuasar.lean). The algorithm and its returned `output` are in [RelativeQuasar](../Algorithms/RelativeQuasar.lean). Supporting proofs establish the energy inequality, integration over a holding interval, finite-product iteration, tuning, and equality with `execute`.

## Problem, information, and guarantee

Let $f:E\to\mathbb R$, where $E$ is any finite-dimensional real inner-product space. Its gradient is $L$-Lipschitz, $L>0$. There is a minimizer $x_\star$ such that, for every $x$,

\[
 \langle\nabla f(x),x-x_\star\rangle
 \ge\gamma(f(x)-f(x_\star))+\frac{\gamma\mu}{2}\|x-x_\star\|^2,
 \qquad 0<\gamma\le1,\quad\mu>0.
\]

This is the usual $(\gamma,\mu)$-strong quasar-convexity condition, without a lower curvature bound between arbitrary pairs of points. We know an initial gap bound $f(x_0)-f(x_\star)\le\Delta$. We do not assume $\mu\le L$.

The only oracle returns a fixed Borel-measurable map $g:E\to E$ satisfying

\[
 \|g(x)-\nabla f(x)\|\le\delta\|\nabla f(x)\|,
 \qquad 0\le\delta<1.
\]

The norm-relative oracle is an established model: [Hallak and Levy, ICML 2024](https://proceedings.mlr.press/v235/hallak24a.html), Equation (1), study this condition for deterministic biased gradient approximations. Their projected and conditional gradient results concern constrained optimization and do not provide the accelerated strong-quasar guarantee here.

No unbiasedness, objective values, exact gradients, minimizer coordinates, or subspace minimization oracle are available. The map can be discontinuous and need not be the gradient of any function. It is fixed across calls and independent of the algorithm's randomness. The theorem does not cover an arbitrary history-dependent or future-aware adversary. Public inputs are $E,L,x_0,\mu,\gamma,\delta,\Delta,\varepsilon$; $f,g,x_\star$ are not public inputs.

Set

\[
 s=1-\delta,\qquad
 \theta=\left(8\sqrt{\frac{L}{\mu s}}+
                   \frac{32\delta^2L}{\gamma\mu s}\right)^{-1}.
\]

Starting at $(x_0,z_0)=(x_0,x_0)$, independently draw an exponential holding time of mean one at each step. Evolve the exactly solvable linear system

\[
 \dot x=\theta(z-x),\qquad \dot z=\gamma\theta(x-z)
\]

for that duration, obtaining $(y,w)$, query $v=g(y)$ once, and set

\[
 x^+=y-v/L,\qquad z^+=w-2\theta v/\mu.
\]

The output is the last $x$ coordinate after exactly $K$ calls, not an average, selected best point, or iterate at a random number of calls. There are no extra initialization calls. Exponential randomness belongs to the algorithm's explicitly specified finite-product seed law; it is not a restriction on a stochastic data distribution.

The public budget is

\[
 K=\max\!\left\{1,\left\lceil
 \frac{32}{\gamma}\sqrt{\frac{L}{\mu(1-\delta)}}+
 \frac{128\delta^2L}{\gamma^2\mu(1-\delta)}
 \right\rceil\right\}
 \max\!\left\{1,\left\lceil\log_2
 \left\lceil1+\frac{2\Delta}{\gamma\varepsilon}\right\rceil
 \right\rceil\right\}.
\]

The inner natural-number ceiling and `Nat.clog` follow the Lean definition exactly. For the actual execution law $P$, the theorem establishes integrability and

\[
 \int [f(\operatorname{output}(\omega))-f(x_\star)]\,dP(\omega)
 \le\varepsilon.
\]

Writing $\kappa=L/\mu$, the cost, with ceiling effects retained by the explicit formula, is

\[
 O\!\left(\left[1+\frac{\sqrt{\kappa/(1-\delta)}}{\gamma}
 +\frac{\delta^2\kappa}{\gamma^2(1-\delta)}\right]
 \left[1+\log\left(1+\frac{\Delta}{\gamma\varepsilon}\right)\right]\right).
\]

## Closest results and the improvement regime

[Wang and Wibisono, ICLR 2023](https://openreview.net/pdf?id=yYbhKqdi7Hz), Theorem 2 and Corollary 2 ([arXiv:2302.07851v1](https://arxiv.org/abs/2302.07851v1), February 15, 2023), establish exact-gradient continuized acceleration for the same strong-quasar condition. Their continuous-time exponent is $\gamma\sqrt{\mu/L}$; their discrete statement controls a gap weighted by the random arrival time and gives a high-probability corollary. Their construction needs no binary search. Our exact-error limit preserves its parameter order, with conservative constants. The new oracle permits persistent, nonconservative relative bias.

[Hermant et al., arXiv:2512.16533v2](https://arxiv.org/abs/2512.16533v2), January 6, 2026, Assumptions 3–4 and Section 4, improve continuized guarantees and constants and treat unbiased stochastic gradients under a strong-growth condition. The unbiasedness requirement eliminates a cross term which remains in our model. Our result is not a faster bound for their stochastic model, nor does it inherit their extensions to multiple minimizers or trajectory-wise guarantees. This source is treated as a preprint, without an asserted conference acceptance.

[Kuruzov and Stonyakin, arXiv:2407.01051v3](https://arxiv.org/abs/2407.01051v3), August 12, 2026, Theorems 3.2–3.3, give restarted subspace optimization with additive gradient error on quasar-convex objectives satisfying quadratic growth. Their accelerated outer-iteration result assumes exact auxiliary subspace minimization. The total oracle accounting in Section 4 requires convex auxiliary problems. Thus this is not the same gradient-only oracle on a general nonconvex strong-quasar objective. Their additive-error condition has squared error proportional to $\gamma^2\mu\varepsilon$, rather than permitting a fixed relative error with fourth-root tolerance.

[Gbaguidi and Hermant, arXiv:2607.19965v1](https://arxiv.org/abs/2607.19965v1), July 22, 2026, Sections 2–4, obtain zeroth-order quasar acceleration. Their estimator is unbiased for a smoothed objective, with smoothing errors explicitly controlled; this does not allow an arbitrary fixed relative-gradient bias. This is also treated as a preprint.

The relevant elementary GD baseline is stronger than simply applying the weakest PL implication. With $c=\min\{\mu,L\}$, step $1/(16L)$, and potential $f-f_\star+c\|x-x_\star\|^2/2$, relative-error GD contracts at least by $1-\gamma c/(32L)$ when $\delta\le1/2$ and $\delta^2\le\gamma/8$. This follows by smooth descent, the quasar inequality, and Young's inequality for the bias. Its cost is $O(\max\{\kappa,1\}/\gamma)$ times the accuracy logarithm. Comparing against $O(\kappa/\gamma^2)$ alone would overstate the gain.

For $\kappa\gg1$, fixed $\gamma$, and

\[
 \delta=O(\sqrt\gamma\,\kappa^{-1/4}),
\]

the new bound retains the exact-gradient accelerated order $O(\sqrt\kappa/\gamma)$, up to the displayed accuracy logarithm. More generally its ratio to the stronger GD baseline is of order $\kappa^{-1/2}+\delta^2/\gamma$ when $\delta$ is bounded away from one. Thus the meaningful improvement regime is small $\delta^2/\gamma$; no uniform superiority for large error or small $\gamma$ is claimed. The deterioration as $\delta\to1$ and the dependence on $\gamma$ are not claimed optimal.

Strong-quasar parameters cannot be compared as if $\mu$ were always the largest PL constant. [Hermant, arXiv:2602.10022v2](https://arxiv.org/abs/2602.10022v2), June 11, 2026, Section 3, explains the resulting pitfalls. Our comparisons hold the stated strong-quasar parameters and oracle fixed. We make no acceleration claim for the entire PL class or for an instance whose sharper independent PL information already gives a better rate.

## Why the proof needs a new robustness argument

The energy is

\[
 V(x,z)=f(x)-f(x_\star)+\frac\mu4\|z-x_\star\|^2.
\]

Using half of the available quasar curvature leaves two negative squared-distance terms in its flow-and-jump generator. With $G=\nabla f(x)$ and $e=g(x)-G$, the uncancelled bias is $-\theta\langle e,z-x_\star\rangle$. Split $z-x_\star=(z-x)+(x-x_\star)$, and absorb each part into one of those reserves. The remaining gradient coefficient is bounded above by

\[
 \frac{\delta^2-1}{2L}+\frac{4\theta^2}{\mu}
            +\frac{2\theta\delta^2}{\gamma\mu}\le0.
\]

The primal step stays $1/L$ while the flow and dual step slow with the error level. This preserves the negative gradient-norm term needed to pay for persistent bias. Merely substituting the slower flow parameter into a linked primal step $\theta^2/(\mu/2)$ would lose that reserve. The original continuized family has freely tunable coefficients; the contribution is the robust parameter coupling and guarantee, not the invention of independent parameters.

A convex relative-error potential is already proved in this repository in [AcceleratedInexactStronglyConvex](AcceleratedInexactStronglyConvex.md). That convex result also permits call-dependent errors and bounded additive error, which are not covered here. Its lower model between a query point and the previous iterate is unavailable here. We reuse the curvature-reserve idea, but replace that convex interpolation argument by the exact flow generator and its two one-point curvature reserves. The substantive claim is the resulting nonconvex robustness theorem, not a new acceleration principle or the formalization itself.

The generator bound gives $\mathcal LV\le-\gamma\theta V$. Separately, a jump has energy at most $4V$. Exponential integration yields, with $I$ the expected energy just before the jump and $Y$ just after it,

\[
 Y\le V_0-\gamma\theta I,\qquad Y\le4I,
 \qquad Y\le\frac4{4+\gamma\theta}V_0.
\]

The deterministic flow lies in a compact line segment, so its energy and derivative are bounded. The jump need only be measurable: its nonnegativity and domination by $4V$ give integrability. Product integration then proves the fixed-call last-iterate expectation bound. Strong-quasar quadratic growth gives $V(x_0,x_0)\le2\Delta/\gamma$. Each block of at least $4/(\gamma\theta)$ calls halves expected energy by Bernoulli's inequality; the binary-log block count gives the public budget.

The standard-reduction checks matter. Converting relative error into an approximate quasar inequality costs $\delta\sqrt{2L(f-f_\star)}\|x-x_\star\|$, which only preserves useful curvature at $\delta^2L\lesssim\gamma^2\mu$. A direct local-accuracy conversion of the cited additive-error restart condition gives the same square-root-scale restriction; this is not an implementation of its auxiliary subspace solves with our oracle. Batching a deterministic biased map does not remove its bias. Adding proximal regularization makes the error relative to the original gradient, which need not vanish at the regularized subproblem's minimizer; an exact-proximal theorem therefore cannot be composed without an additional inexactness argument. These reductions do not supply the displayed fourth-root regime.

## Nonlinear scope and limitations

A concrete coupled family is

\[
 f(x)=\sum_{i=1}^d\left(\frac{r_i^2}{2}+2(1-\cos r_i)\right),
 \qquad r=Ax-b,
\]

for any dense invertible $A\in\mathbb R^{d\times d}$. It combines linear residual fitting with periodic residual penalties, analogous to the quadratic-plus-trigonometric nonconvex family in Kuruzov–Stonyakin, Section 1 and Appendix A. Its unique minimizer is $A^{-1}b$. With $Q=A^\top A$, valid parameters are $L=3\lambda_{\max}(Q)$, $\gamma=1/8$, and $\mu=2\lambda_{\min}(Q)$. Indeed, $t\sin t\ge-t^2/3$ gives a radial gradient product at least $\|r\|^2/3$, while $f\le3\|r\|^2/2$; the required quasar right side is at most $5\|r\|^2/16$. At $r=\pi\mathbf1$, the Hessian is $-Q$, so the objective is genuinely nonconvex. Dense $A$ couples Euclidean coordinates; arbitrary dimension is permitted, with dimension entering only through the stated spectral parameters. These calculations illustrate the theorem's class and are not extra formal assumptions.

Fixed relative perturbations $g=(I+\delta U)\nabla f$, with orthogonal $U$, supply admissible biased oracles, including nonconservative ones. Deterministic rounding or compression satisfying the pointwise relative bound is also permitted. The theorem counts oracle calls, not communication bits or floating-point work, and does not assert that every practical compression scheme meets a chosen small $\delta$.

The formal result is an expected objective-gap upper bound for a fixed measurable oracle. It gives neither a matching lower bound nor high-probability, almost-sure, additive-noise, constrained, composite, or multiple-minimizer extensions. The reviewed literature search covered ICML 2026/2025, ICLR 2026/2025, NeurIPS 2025/2024, recent arXiv submissions and revisions, and cited older sources, as of October 16, 2026 UTC. Some OpenReview forum pages presented browser challenges; the ICLR 2023 proceedings PDF was accessible and identifies the accepted venue. The preprints above are not represented as accepted conference papers. Novelty is an evidence-based comparison with checked primary results, not a guarantee that no overlooked result exists.
