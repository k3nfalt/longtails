# Unbounded non-Euclidean acceleration with biased relative gradient errors

The [Lean theorem](PowerGeometryRelativeErrorAcceleration.lean) constructs [squared-norm dual averaging with a steepest step](../Algorithms/PowerDualAveraging.lean) for the [relative-error convex specification](../Setups/PowerGeometryRelativeErrorConvex.lean). The contribution is a dimension-free power-geometry acceleration guarantee under arbitrary biased relative gradient errors, realized by an unconstrained algorithm that needs no bound on the distance to a minimizer. Radius-free tuning is an additional adaptivity property, not a separate problem-class complexity improvement: a target-dependent localization reduction is given below.

Supporting modules prove [scalar energy inequalities](../Proofs/PowerMirrorEnergy.lean), [norm and minimizer geometry](../Proofs/PowerMirrorGeometry.lean), [tuning and budget algebra](../Proofs/PowerMirrorTuning.lean), and [the trajectory bound and execution identity](../Proofs/PowerDualAveragingRun.lean). Formalization supports correctness; it is not the mathematical novelty.

## Problem and information

Let \(E\) be any finite-dimensional real normed space, with dual norm \(\|\cdot\|_*\). The objective is globally differentiable and convex, and
\[
\|Df(x)-Df(y)\|_*\le L\|x-y\|.
\]
A global minimizer \(u\) exists. The analysis parameter \(R\ge0\) satisfies \(\|u-x_0\|\le R\); it is **not supplied to the algorithm**. There is no bounded-domain, bounded-iterate, strong-convexity, or PL assumption.

The squared norm \(\Psi(x)=\|x-x_0\|^2/2\) is differentiable and satisfies, for known \(p>2,c>0\),
\[
B_\Psi(w,z):=\Psi(w)-\Psi(z)-D\Psi(z)[w-z]
\ge \frac{c\|w-z\|^p}{(\|w-x_0\|+\|z-x_0\|)^{p-2}}.
\]
At zero denominator both points equal \(x_0\), and the quotient is defined as zero, matching Lean's division convention. This is a property of the norm, independent of the objective and iterates. It is satisfied dimension-independently by \(\ell_p\) for every fixed finite \(p>2\), as shown below. No such modulus is claimed for every norm.

Replies at every point, index, and seed satisfy
\[
\|g-Df(y)\|_*\le\alpha\|Df(y)\|_*,\qquad0\le\alpha\le1/4.
\]
The bound \(\alpha\) is public. The threshold \(1/4\) is sufficient for this proof and is not claimed necessary. Errors may be biased and dependent. The proof is pathwise for every seed; the framework's explicit almost-sure accuracy statement is a consequence, not a stochastic moment or unbiasedness analysis. The algorithm knows \(L,p,c,\alpha,x_0\) and the norm, but no minimizer, radius, target accuracy, horizon, exact gradient, or function value. The specification permits unrestricted oracle algorithms; it does not enforce this update family to manufacture a comparison advantage.

## Algorithm and guarantee

Put
\[
B=128\max\{1,32^{(p-2)/2}/c\},\quad a_n=n^2,\quad A_n=\sum_{i=1}^n i^2,
\qquad\beta_n=L[B(n+1)^{2-2/p}+256\alpha^2(n+1)^2].
\]
Initialize \(x_0=z_0\), \(h_0=0\). At step \(n\ge1\),
\[
y_n=(A_{n-1}x_{n-1}+a_nz_{n-1})/A_n,\quad
g_n=\operatorname{oracle}(y_n),\quad h_n=h_{n-1}+a_ng_n,
\]
\[
x_n=y_n-v(g_n)/(2L),\qquad z_n=x_0-v(h_n)/\beta_n.
\]
Here \(\|v(g)\|\le\|g\|_*\) and \(g[v(g)]=\|g\|_*^2\). Finite-dimensional norm attainment establishes existence. The proof shows directly that the explicit \(z_n\) minimizes \(\beta_n\Psi(z)+h_n[z]\) on the whole space. In \(\ell_p\), with \(q=p/(p-1)\), one can use
\[
v(g)_i=\|g\|_q^{2-q}\operatorname{sign}(g_i)|g_i|^{q-1},\qquad v(0)=0.
\]
The return is the **last steepest-step iterate \(x_T\)**. Both trajectories are unconstrained. There is exactly one gradient reply per update and no value calls, batching, or validation calls. Norming-vector arithmetic is outside oracle cost; the abstract theorem does not claim it is inexpensive in every norm. Classical choice in Lean selects known-geometry operations, not objective information.

The convergence calculation gives, for \(T\ge1\),
\[
f(x_T)-f(u)\le\frac{6BLR^2}{T^{1+2/p}}+\frac{2112L\alpha^2R^2}{T}.
\]
The public theorem proves accuracy \(f(x_K)-f(u)\le\varepsilon\) with the explicit budget
\[
K=1+\left\lceil
\left(\frac{1536\max\{1,32^{(p-2)/2}/c\}LR^2}{\varepsilon}\right)^{p/(p+2)}
+\frac{4224L\alpha^2R^2}{\varepsilon}
\right\rceil.
\]
The budget is an analysis guarantee depending on the unknown distance bound and desired accuracy. The algorithm supplies a trajectory that can be truncated at any horizon; it does not provide an observable stopping certificate for an unknown minimizer distance. Every call is charged by `execute`; the extra one avoids zero-horizon divisions. Zero error is included. For \(R=0\), the initial point is optimal, all admissible replies there vanish, and the stated one-call execution remains optimal. Finite \(p>2\) is required; no \(\ell_\infty\) endpoint or uniform-in-\(p\) constant is claimed.

## Natural geometry, nonlinear objectives, and biased oracles

For \(E=(\mathbb R^d,\|\cdot\|_p)\), the curvature condition holds with
\[
c=\frac{2^{2-p}}{p(p-1)}.
\]
Here is a derivation. For \(\phi(x)=\sum_i|x_i|^p/p\), the scalar monotonicity inequality
\[
(\operatorname{sign}(a)|a|^{p-1}-\operatorname{sign}(b)|b|^{p-1})(a-b)
\ge2^{2-p}|a-b|^p
\]
follows from superadditivity for equal signs and convexity for opposite signs. Integrating along a segment gives \(B_\phi(w,z)\ge2^{2-p}\|w-z\|_p^p/p\). At nonzero \(x\), weighted Cauchy in the Hessian of \(\|x\|_p^2/2\) gives
\[
D^2\Psi(x)[h,h]\ge\|x\|_p^{2-p}\sum_i|x_i|^{p-2}h_i^2
=\frac{\|x\|_p^{2-p}}{p-1}D^2\phi(x)[h,h].
\]
On the segment between \(z,w\), its norm is at most \(S=\|w\|_p+\|z\|_p\). Integration against \(1-t\) yields \(B_\Psi(w,z)\ge S^{2-p}B_\phi(w,z)/(p-1)\). A segment crossing zero is split there and limits taken: the norm square is continuously differentiable, with bounded line second derivative. Translate by \(x_0\). The zero-scale case is trivial. Thus this geometry imposes no extra objective restriction.

A concrete interacting nonlinear family is ordinary soft-label logistic regression:
\[
f(x)=\sum_j w_j[\log(1+e^{a_j^\top x})-y_j a_j^\top x],
\qquad w_j>0,\quad y_j\in[\delta,1-\delta],\quad0<\delta\le1/2.
\]
Take a dense full-column-rank feature matrix. The variable Hessian is a sum of dense rank-one matrices with coefficients in \((0,w_j/4]\), giving \(L\le\frac14\sum_jw_j\|a_j\|_q^2\). Each summand is at least \(\delta|a_j^\top x|\), so full rank gives coercivity and a finite minimizer. Strict convexity gives uniqueness. Along a generic ray the Hessian tends to zero, excluding global strong convexity; bounded gradients and unbounded objective values exclude global PL. Dimensions are unrestricted. These examples substantiate scope but are not additional formal hypotheses.

Relative coordinate quantization supplies genuinely biased replies. For \(\alpha>0\), round a nonzero coordinate's magnitude down to a power of \(1+\alpha\), preserving sign; map zero to zero. Then \(|Q(t)-t|\le\alpha|t|\), and summing \(q\)-th powers gives the required dual-norm bound for the whole gradient. The case \(\alpha=0\) uses identity. This models relative-precision communication; it does not save full-gradient evaluation by itself, and finite hardware range requires handling underflow and overflow. Adaptive coordinate truncation with discarded \(q\)-tail at most \(\alpha\|Df(y)\|_q\) is another mechanism. Approximating activation values or individual summands does not automatically imply this condition because of cancellation.

## What changes relative to prior results

Non-Euclidean acceleration predates recent work on Muon. [d'Aspremont, Guzman, and Jaggi, *Optimal Affine-Invariant Smooth Minimization Algorithms*](https://www.di.ens.fr/~aspremon/PDF/HCafe.pdf), Proposition 4.9, Corollary 4.10 and Section 5.1.2, already establish the power-geometry exact-gradient rate. Lemma 4.8 supplies the related power/quadratic inexact-model estimate. Their proof uses exact supporting gradients; the present result removes exactness while retaining that geometry rate. Their constrained-ball lower bounds do not automatically establish optimality for our globally unconstrained objective class and queries.

[Contreras, Guzman, and Martinez-Rubio, arXiv:2411.08987v2](https://arxiv.org/abs/2411.08987v2), Theorems 8 and 10, give a broader high-order framework and the same first-order exact exponent. Their inexact proximal condition includes an enlarged-subgradient inclusion, not merely relative norm proximity to a gradient. This is a real oracle distinction: for \(f(t)=\sqrt{1+t^2}\), \(y=2\), and \(g=(5/4)f'(2)=\sqrt5/2>1\), the relative error is \(1/4\), but \(f(z)-gz\to-\infty\). No finite global affine-support shift makes this reply an enlarged subgradient.

[Pethick, arXiv:2606.15268v1](https://arxiv.org/abs/2606.15268v1), Corollaries 3.2 and A.5, treats accelerated Schatten-\(p\) geometry with stochastic noise. Assumption 3 and Lemma A.2 use unbiasedness. That cancellation is unavailable here. Its absolute-gradient slack has the smaller iteration weight, whereas its larger-weight slack controls gradient differences. Directly absorbing arbitrary relative bias into the former gives an error floor, not this theorem's \(\alpha^2/T\) term. This is a limitation of direct substitution, not a claim that their method cannot be adapted.

[Cohen, Diakonikolas, and Orecchia, ICML 2018](https://proceedings.mlr.press/v80/cohen18a.html), Proposition 3.5, and [Zhou and Pan, JMLR 2022](https://jmlr.org/papers/v23/20-1179.html), Theorems 1 and 3, provide general-norm acceleration with error pairings. Their quadratic strong-prox curvature or radius-weighted error sums do not directly provide the stated power-geometry/relative-bias bound. [Vasin et al., arXiv:2102.02921v3](https://arxiv.org/abs/2102.02921v3), Section 5, studies relative-gradient noise with Euclidean geometry. The Euclidean exact-plus-noise tradeoff is not claimed as new.

The newer [Vasin et al., arXiv:2503.06628v3](https://arxiv.org/abs/2503.06628v3) (December 9, 2025), Assumptions 1–2 and Theorems 4–5, sharpen accelerated convergence with relative errors for Euclidean strongly convex problems. Their relative-error thresholds depend on the condition number; these theorems do not assert the present power-geometry convex-radius guarantee. [Vasin and Gasnikov, arXiv:2603.12376v1](https://arxiv.org/abs/2603.12376v1) (March 12, 2026), Theorem 7.2, gives a Euclidean regularization bound \(O(T_0^{1-\beta}\log T_0)\) for \(\alpha\le(1/3)(12T_0)^{-\beta}\), \(0\le\beta\le1/2\). Its geometry and error threshold must be retained in comparisons. Our mixed-geometry comparator below is stronger than simply importing that regularization result. We do not transfer that paper's span-restricted lower bounds to unrestricted algorithms.

[Alkousa et al., arXiv:2405.16140v3](https://arxiv.org/abs/2405.16140v3) (October 3, 2024), Definition 3.2 and Theorem 5.1, do not supply a shortcut through a higher-degree inexact model. For a genuinely affine approximate-gradient model of positive degree, setting \(x=y\) forces the model's function value to equal \(f(y)\); its global lower-model inequality then forces the gradient to be exact at an interior differentiability point. Example 3.5 establishes an upper-model estimate for relative errors, which is insufficient for that lower-model condition. A degree-zero shifted model on a bounded domain instead introduces an error proportional to \(\alpha R\|Df(y)\|_*\); treating it as a uniform constant does not give the displayed vanishing rate. These are direct-substitution obstructions, not an impossibility theorem about all inexact-model analyses.

[Lezane, Langer, and Koolen, ALT 2026](https://proceedings.mlr.press/v313/lezane26a.html), with accessible [arXiv:2405.18976v2](https://arxiv.org/abs/2405.18976v2), Theorem 3.1 and Corollary 3.2, treats exact-gradient star-convex acceleration in general geometry. Its power-prox optimal tuning uses a Bregman-radius bound. That observation does not prove unknown-radius acceleration is new: accuracy-dependent tuning and localization must also be considered. The official conference PDF could not be retrieved during review; the arXiv theorem was read, official acceptance verified, and the indexed final appendix remains consistent with a power-norm prox. This is a remaining source-access limitation.

Negative regularizer drift is standard, including [Jacobsen and Cutkosky, COLT 2022](https://proceedings.mlr.press/v178/jacobsen22a/jacobsen22a.pdf), Lemma 1. The technical point here is simultaneous absorption of two unbounded terms. Write \(\mu_0=128Ln\), \(\delta_n=16Ln^{1-2/p}\), \(w=z_n,z=z_{n-1}\). Scale-relative curvature implies
\[
\beta_{n-1}B_\Psi(w,z)\ge\mu_0\|w-z\|^2/2-\delta_n(\Psi(w)+\Psi(z)).
\]
Using \(\Psi(z)\le2\Psi(w)+\|w-z\|^2\) leaves quadratic curvature \(3\mu_0/8\) and defect \(3\delta_n\Psi(w)\). The steepest step supplies \(A_n\|g_n\|_*^2/L\) slack; combining it with quadratic mirror curvature costs \((\mu_0/2)\alpha^2\|z-u\|^2\). The bound
\[
\|z-u\|^2\le3\|w-z\|^2+6\Psi(w)+3R^2
\]
separates that error into displacement, iterate scale, and comparator distance. Spare curvature absorbs displacement for \(\alpha\le1/4\), and
\[
\beta_n-\beta_{n-1}\ge3\delta_n+3\mu_0\alpha^2
\]
absorbs both iterate-scale terms. Only \(192L\alpha^2R^2n\) remains. Telescoping the exact dual-averaging potential gives the displayed bound. No iterate radius or convergence inequality is assumed. The familiar drift identity alone is not the claimed technical novelty.

A standard reduction limits the adaptivity claim. Given accuracy \(\varepsilon\) and horizon \(T\), a bounded-ball robust theorem with bound \(Lr^2[C_pT^{-1-2/p}+C\alpha^2/T]\) can be run with
\[
r^2=\frac{\varepsilon/L}{C_pT^{-1-2/p}+C\alpha^2/T}.
\]
Whenever the desired true-distance complexity condition holds, \(R\le r\), so that algorithm already achieves accuracy without an input \(R\). Thus unknown-radius **oracle complexity** follows from the corresponding bounded-ball guarantee. The present unbounded, single-trajectory implementation avoids accuracy/horizon-dependent localization; that is an adaptivity and implementation gain. A constrained power-norm prox also has an explicit formula in \(\ell_p\), so explicit prox alone is not a novelty claim. For the abstract curvature model, restriction to a radius-\(r\) ball and the kernel \(r^{p-2}\Psi\) give power modulus \(2^{2-p}c\) and kernel radius at most \(r^p/2\). The bounded-ball analysis can therefore retain complexity dependence \(c^{-2/(p+2)}\), whereas the present explicit unbounded bound has \(c^{-p/(p+2)}\) dependence when \(c\) is small, for fixed \(p\). This is a real tradeoff. The dimension comparisons below use the standard fixed-\(p\) \(\ell_p\) modulus, not a claim of superiority for every \(c\). The substantive class-complexity claim is the simultaneous relative-bias/power-geometry rate versus the strongest applicable prior guarantees below.

## Improvement regimes and limitations

Let \(T_0=LR^2/\varepsilon\ge1\), \(s=1/2-1/p\), and use the concrete \(\ell_p\) geometry. A stronger comparator than naive Euclidean norm conversion keeps \(p\)-steepest descent but uses a Euclidean mirror constrained to the same \(p\)-ball. The initial mirror radius is at most \(d^{2s}R^2/2\); the bias pairing still uses \(2R\). The resulting standard coupling bound gives

\[
O(d^s\sqrt{T_0}+\alpha^2T_0),
\]

with constant admissible \(\alpha\). Thus dimension-free noise tolerance, or the noise term by itself, is not new. Our guarantee is

\[
O_p(T_0^{p/(p+2)}+\alpha^2T_0),
\]

preserving the dimension-free geometry exponent simultaneously with robustness. For \(\alpha\lesssim T_0^{-1/(p+2)}\) and \(d\gg T_0^{p/(p+2)}\), it is asymptotically smaller than that comparator. For example, \(p=5/2\), \(\alpha=T_0^{-2/9}\), and \(d\asymp T_0^{10/9}\) give exponents \(5/9\) versus \(11/18\), an improvement factor \(T_0^{1/18}\). The comparison must retain this dimension regime. These are asymptotic parameter-rate comparisons, not measured running-time gains; the explicit constants in the proved budget can delay the crossover substantially. At fixed nonzero error level, the noise term eventually dominates and there is no corresponding asymptotic acceleration claim; low-dimensional Euclidean geometry can also be better.

There is also a dimension-free \(O(T_0)\) comparator, derived directly using Frank–Wolfe on the auxiliary ball \(B(x_0,4R)\). This is not a claim about ordinary unconstrained steepest descent. Choose a unit norming vector \(v\), the linear minimizer \(s=x_0-4Rv\), and \(\gamma=\|g\|_*/(128LR)\). The minimizer's interior margin and convexity give
\[
Df(x)[x-s]\ge[4(1-2\alpha)-1]R\|Df(x)\|_*
\ge(4/5)R\|g\|_*.
\]
Since \(Df(u)=0\), smoothness gives \(\|g\|_*\le(25/4)LR\), so \(0\le\gamma<1\) and the ball is invariant. Its diameter and the smooth upper model imply decrease at least \(\|g\|_*^2/(256L)\). Convexity also gives \(f(x)-f(u)\le7R\|g\|_*\). Thus the gaps satisfy \(\Delta_{t+1}\le\Delta_t-\Delta_t^2/(12544LR^2)\), proving the stated bound with one reply per step. A zero reply already certifies optimality.

The combined elementary comparator is therefore
\[
O\!\left(\min\{T_0,\ d^{1/2-1/p}\sqrt{T_0}+\alpha^2T_0\}\right).
\]
For the previous \(p=5/2\) example with \(d\ge T_0^5\), this comparator is \(O(T_0)\), while our guarantee is \(O(T_0^{5/9})\). The improvement factor \(T_0^{4/9}\) requires this larger dimension regime. Neither comparator is asserted to be a lower bound.

Repeating or batching an adversarial reply does not force its bias to decrease. Clipping does not restore unbiasedness or a supporting-affine oracle. Adding a known regularizer also changes the error model: gradient cancellation at the new minimizer generally turns relative error into mixed relative and absolute error. Any regularization composition must retain its error floor, admissible noise threshold, inner calls, and logarithms. Euclidean strong-convexity regularization retains geometric distortion; a power-uniform kernel is not quadratically strongly convex, so a Hilbert-space relative-error theorem cannot simply be substituted. These checks exclude the direct reductions discussed above, not all conceivable algorithms.

No matching noisy lower bound or universal superiority is claimed. The algorithm requires known smoothness, geometry constants and a relative-error bound, exact norming-vector operations, globally smooth unconstrained objectives, and \(\alpha\le1/4\). Constants can grow rapidly with \(p\); the improvement comparisons hold for fixed finite \(p\), not uniformly as \(p\to\infty\). Anytime operation is convenient but not a separate complexity contribution: doubling and restarting a horizon-based construction can remove horizon knowledge at constant overhead. The novelty claim concerns the simultaneous robust geometry guarantee under the stated standard assumptions.
