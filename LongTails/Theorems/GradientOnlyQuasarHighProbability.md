# Gradient-only acceleration with arbitrary confidence for generalized-smooth quasar objectives

The [main theorem](GradientOnlyQuasarHighProbability.lean) proves a fixed-budget, last-iterate guarantee for the [gradient-only setup](../Setups/GradientOnlyGeneralizedQuasar.lean). For an arbitrary finite-dimensional real inner-product space, it constructs the [algorithm `accelerated`](../Algorithms/GradientOnlyQuasar.lean), whose named `output` is its actual `execute` output, and proves

\[
\Pr\{f(y_K)-f(x_\star)>\varepsilon\}\le\delta.
\]

There are exactly

\[
K=\left\lceil\frac{65536}{\gamma}
\left(1+\operatorname{clog}_2\left\lceil4/\delta\right\rceil\right)
\left[1+\sqrt{L_0R^2/\varepsilon}
+L_1R\left(1+\operatorname{clog}_2\left\lceil8\Delta/\varepsilon\right\rceil\right)\right]
\right\rceil
\]

gradient calls. Here `clog` is the natural-number ceiling logarithm, with `clog 2 1 = 0`. This is the formula in the public Lean `budget`, not an asymptotic replacement for the implemented cost. Its order is

\[
O\!\left(\frac{1+\log(1/\delta)}{\gamma}
\left[1+\frac{\sqrt{L_0}R}{\sqrt\varepsilon}
+L_1R\bigl(1+\log(1+\Delta/\varepsilon)\bigr)\right]\right).
\]

The contribution concerns oracle access, confidence dependence, and objective-class scope. Fixed-confidence continuized acceleration alone is already known. The claim is logarithmic arbitrary-confidence overhead with exact gradients alone, while allowing nonlinear, nonconvex objectives with globally unbounded curvature. It does not claim a faster rate than every method that also receives function values.

## Assumptions and information

The function is differentiable everywhere with continuous gradient. There is one attained global minimizer satisfying

\[
\gamma(f(x)-f(x_\star))\le\langle\nabla f(x),x-x_\star\rangle\quad\text{for every }x,
\qquad 0<\gamma\le1.
\]

The public data include positive upper bounds \(R,\Delta\) on \(\|x_0-x_\star\|\) and \(f(x_0)-f(x_\star)\). They do not include the minimizer or its value. Quasar convexity and the distance-based formulation are the established assumptions in Wang–Wibisono, [ICLR 2023, Definition 1 and Theorem 1](https://openreview.net/pdf?id=yYbhKqdi7Hz). The gap bound is an additional public-information assumption in the generalized-smooth setting. On the common \(L_1=0\) subclass, smoothness and stationarity of the attained minimizer give \(f(x_0)-f(x_\star)\le L_0R^2/2\), so the algorithm can use \(\Delta=L_0R^2/2\) without additional oracle information. The confidence comparison on that subclass therefore uses the same available information.

For \(L_0>0,L_1\ge0\), the setup requires

\[
\|\nabla f(x)-\nabla f(y)\|
\le (L_0+L_1M)\|x-y\|
\]

whenever \(M\) bounds the gradient norm throughout the segment joining \(x\) and \(y\). With continuous gradient, this is the \(\alpha=1\) symmetric condition in Chen–Zhou–Liang–Lu, [ICML 2023, Definition 3, equation (4)](https://proceedings.mlr.press/v202/chen23ar/chen23ar.pdf). For twice continuously differentiable functions, the usual bound \(\|\nabla^2 f(x)\|\le L_0+L_1\|\nabla f(x)\|\) implies it by integration along a segment. The Lean theorem uses the first-order condition and does not assume a Hessian exists.

No convexity, PL inequality, quadratic growth, strong quasar condition, unique minimizer, bounded level set, uniform gradient bound, or stochastic-gradient moment condition is imposed. The quasar inequality is required relative to the same one minimizer that satisfies the initial bounds, not relative to every minimizer. The combination of quasar and generalized smoothness is an established question: Ablaev et al., [Automation and Remote Control 86(9), 2025](https://doi.org/10.31857/S0005117925090012), study it with additional PL assumptions in Theorem 1 and a restricted \((0,M)\) setting in Theorems 2–3.

The oracle reply is exactly a gradient vector, at every history and oracle seed. The algorithm receives no objective values, value comparisons, Hessians, subproblem solutions, or stationarity certificates. It knows \(L_0,L_1,R,\Delta,\gamma,\varepsilon,\delta\). There is no `allowedAlgorithm` restriction: this is a problem-class oracle-complexity result. The probability comes from the algorithm's chosen independent exponential holding times. Their finite product law is an internal seed distribution, not an assumption restricting an external stochastic oracle. Continuous sample spaces are supported.

## Algorithm and proof mechanism

Let \(p=1+\operatorname{clog}_2\lceil4/\delta\rceil\), \(E=2R^2\), \(A_0=R^2/(2\Delta)\), and \(S=\operatorname{clog}_2\lceil8\Delta/\varepsilon\rceil\). Stage \(j\) doubles the weight from \(A_j=2^jA_0\) to \(2A_j\) in time

\[
H_j=\frac{256p}{\gamma}\sqrt{L_0A_j+L_1^2E}.
\]

A continuously differentiable ramp interpolates each stage:
\(H(s)=2(s_+)^2-4((s-1/2)_+)^2+2((s-1)_+)^2\).
It is zero before the stage, one after it, and has derivative between zero and two. After all stages, the weight freezes. Put
\(a(t)=A'(t)/\gamma\) and \(L(t)=128(L_0+L_1^2E/A(t))\).
All these quantities depend only on public data and the accumulated clock.

Start at \((y,z)=(x_0,x_0)\). For each of exactly \(K\) independent unit-rate exponential holds, advance the clock from \(t\) to \(t+h\) and compute the exact flow

\[
y\leftarrow z+\left(A(t)/A(t+h)\right)^{1/\gamma}(y-z).
\]

Make one query \(g=\nabla f(y)\), then set
\(y\leftarrow y-g/L(t+h)\) and \(z\leftarrow z-a(t+h)g\).
Return the last primal point. The implementation clamps negative seed coordinates to zero to define a total function; this does not change its exponential-law execution. It continues to count and execute all \(K\) queries after the weight freezes, including the zero-stage case \(\varepsilon\ge8\Delta\).

The optimization-specific inequality uses
\(P=A(f(y)-f(x_\star))+\|z-x_\star\|^2/2\).
On \(P\le E\), generalized smoothness implies safe descent with the declared \(L\); the schedule proves \(64p^2La^2\le A\). For \(P>0\), write

\[
u=\frac{A\|g\|^2}{2LP},\qquad b=\frac{a\langle g,z-x_\star\rangle}{P},\qquad
r=\frac{a^2\|g\|^2}{2P}.
\]

Minimality and descent give \(0\le u\le1\), \(64p^2r\le u\), \(b^2\le4r\), and \(0\le P^+/P\le1-u-b+r\). The [power inequality](../Proofs/QuasarPowerBarrier.lean) proves

\[
(P^+/P)^p\le1-pb.
\]

The flow derivative is at most \(pP^pb\), so it cancels this jump drift. This is a one-sided estimate: negative jumps can be large. An absolute-small-jump assumption is neither true nor used.

To avoid imposing moments on unsuccessful trajectories, use the bounded differentiable barrier
\(B=h((P/E)^p)\), where \(h(q)=1-(\max\{0,1-q\})^2\).
Its concavity transfers the power drift bound inside the safe region; at or beyond \(P=E\), it is flat at one and every subsequent barrier value is at most one. The zero-energy case is handled separately. The [energy proof](../Proofs/GradientOnlyQuasarEnergy.lean) therefore establishes the generator inequality globally, even where local descent is unavailable.

The [holding proof](../Proofs/GradientOnlyQuasarHolding.lean) integrates that inequality against the exponential density and iterates a finite product of holds. The flow derivative is bounded for each fixed history because it is continuous and vanishes after the finite schedule; no uniform history-dependent moment assumption is introduced. The expected final barrier is at most \(2^{1-p}\). The [clock proof](../Proofs/GradientOnlyQuasarProbability.lean) independently gives
\(\Pr\{T_K<T\}\le e^T2^{-K}\).
The [tuning proof](../Proofs/GradientOnlyQuasarTuning.lean) proves both \(A_S\varepsilon\ge E\) and \(K\ge2T+2p\), with the public budget above. A union bound yields the stated failure probability. [Execution equivalence](../Proofs/GradientOnlyQuasarExecution.lean) connects the calculation to the framework's actual query plan.

Exponential integration, finite-product probability, barrier truncation, and Chernoff bounds are standard tools. The claimed new mathematical step is their optimization-specific power drift and gradient-only curvature localization, not a new general concentration theorem.

## Closest results, reductions, and improvement regimes

* **Gradient-only global smoothness.** Wang–Wibisono, [ICLR 2023](https://openreview.net/forum?id=yYbhKqdi7Hz), [arXiv:2302.07851v1](https://arxiv.org/abs/2302.07851v1), Theorem 1 and Corollary 1, provide continuized acceleration. Their corollary gives an error proportional to \(c_0LR^2/(\gamma^2K^2)\) with failure \(1/c_0+1/(c^2K)\). Setting these failures to order \(\delta\) gives an accuracy term proportional to \(\delta^{-1/2}\sqrt{L}R/(\gamma\sqrt\varepsilon)\), plus the clock condition. The present result replaces that confidence deterioration by \(1+\log(1/\delta)\), including on the common \(L_1=0\) subclass.
* **Sharper clock tails.** Hermant et al., [arXiv:2512.16533v2, January 6, 2026](https://arxiv.org/abs/2512.16533v2), PDF Proposition 14 and Corollary 15, sharpen clock concentration but retain a Markov bound for the energy. Their principal optimization application is globally smooth strongly quasar minimization. Improving only the clock does not supply the power-energy bound here. This source is treated as a preprint; the HTML and PDF proposition numbering differ.
* **Function-value acceleration.** Hinder–Sidford–Sohoni, [COLT 2020](https://proceedings.mlr.press/v125/hinder20a.html), [arXiv:1906.11985v3](https://arxiv.org/abs/1906.11985v3), use value and gradient access in their binary search (Lemmas 1, 2, and 4). A two-state restart retaining the primal and mirror points, combined with local curvature control, already gives the corresponding generalized-smooth accelerated dependence with value-based line searches. That reduction is not the novelty claim. The improvement here is removing value access while obtaining arbitrary confidence at logarithmic overhead.
* **Generalized quasar objectives.** Ablaev et al.'s Theorem 1 additionally requires PL and quasar convexity with respect to every solution; its other relevant theorems use \(L_0=0\) and a restricted quasar parameter. Kovalev, [arXiv:2605.15522v2, May 26, 2026](https://arxiv.org/abs/2605.15522v2), Appendix C, Theorem 11 and Corollary 6, handles the broader generalized-Lipschitz stochastic quasar setting with the nonaccelerated bound \(\widetilde O(\gamma^{-6}(RG_1)^4+\gamma^{-2}(RG_0/\varepsilon)^2)\). Its sharper smooth specialization in Appendix B assumes convexity. Neither provides this exact-gradient, nonconvex guarantee under the stated assumptions.

A first-moment stopped-energy argument under the target assumptions is an important baseline: it already gives the accelerated fixed-confidence order. To make its escape probability \(P_0/E\) at most \(\delta\), it chooses \(E\) of order \(P_0/\delta\), enlarging the leading stage times by \(\delta^{-1/2}\). The power barrier keeps \(E=2R^2\) and pays \(p\) instead. Independent repetition with selection by objective values is unavailable to this oracle. Quasar sublevel sets need not be convex or concentrated near the minimizer, so averaging and geometric-median selection do not furnish the missing guarantee. Gradient-norm certification without an error bound loses accelerated objective accuracy.

[ProxBoost, JMLR 22(49), 2021](https://www.jmlr.org/papers/v22/20-821.html), Sections 3–6, uses strongly convex regularized problems and distance-based confidence amplification. A direct application would add assumptions or require a separately justified, counted inner oracle algorithm. Generic confidence machinery in Bonnerjee–Ramdas, [arXiv:2610.23570v1](https://arxiv.org/html/2610.23570v1), equation (2), Section 9.5.1 and Section 10.3, also does not itself establish the required drift: the gradient query depends nonlinearly on the same exponential hold that randomizes the update. These checks exclude the stated reductions; they are not impossibility theorems for all future amplification methods.

For fixed problem parameters and fixed accuracy, the confidence gain over the checked Markov-energy analyses is asymptotic as \(\delta\) decreases. The stronger deterministic GD comparison matters: setting the noise to zero and the step size to \(1/(2L_0)\) in Jin, [arXiv:2010.04937v3, equation (12)](https://arxiv.org/html/2010.04937v3), gives \(\sum_{t=1}^K(f(x_t)-f(x_\star))\le(2/\gamma-1)L_0R^2\). Descent then gives a last-iterate cost \(O(L_0R^2/(\gamma\varepsilon))\), with no confidence dependence. Against that guarantee on the common globally smooth subclass, the accelerated accuracy benefit is meaningful when
\(1+\log(1/\delta)\ll\sqrt{L_0}R/\sqrt\varepsilon\);
extremely small \(\delta\) can favor a deterministic nonaccelerated method. There is no claim of uniform dominance, parameter adaptivity, or optimal confidence dependence. On \(L_1=0\), the remaining multiplicative confidence gap from the known accelerated constant-confidence scale is \(1+\log(1/\delta)\). Optimal dependence on \(L_1R\), initialization, and confidence for the full class remains unresolved. The explicit numerical constant is conservative.

## Nonlinear scope and limitations

A family with interacting coordinates is
\[
f(x)=\frac1m\sum_{i=1}^m\bigl[h(a_i^\top x)-h(a_i^\top x_\star)\bigr]^4,
\qquad h(t)=t+t^3,
\]
with a dense, overcomplete, full-column-rank design matrix \(A\). Fourth-power residual losses have an independent history in least-mean-fourth system identification; see Zerguine–Bettayeb, [EUSIPCO 1998](https://www.eurasip.org/Proceedings/Eusipco/Eusipco1998/sessions/W%20M/WM%20P-6/737/EUS.PDF), and Zerguine, [Digital Signal Processing 17(1), 2007](https://doi.org/10.1016/j.dsp.2006.01.005). Those references motivate the loss, not a practical performance claim for this particular realizable cubic-link model.

Here are explicit sufficient parameters. Set \(B_\star=\max_i|a_i^\top x_\star|\), \(a=\max_i\|a_i\|\), \(s=\sigma_{\min}(A)>0\), and
\(\gamma=\min\{1,4/(1+3B_\star^2/2)\}\).
For scalar inputs \(v,u\),
\(h(u)-h(v)=(u-v)(1+u^2+uv+v^2)\) and
\(1+u^2+uv+v^2\le(1+3v^2/2)(1+3u^2)\), which gives the quasar inequality term by term. Let
\[
U=B_\star+a,\quad C_r=U+U^3+B_\star+B_\star^3,\quad C_d=1+3U^2,
\quad H=\frac{\|A\|^2}{m}(12C_r^2C_d^2+24C_r^3U),
\quad c=\frac{s^{12}}{256m^6}.
\]
Writing \(r=\|x-x_\star\|\), direct differentiation gives
\(\|\nabla^2f(x)\|\le H\max\{1,r^{10}\}\), while
\(f(x)\ge cr^{12}\) and quasar convexity imply
\(\|\nabla f(x)\|\ge\gamma cr^{11}\).
Thus \(L_0=H\), \(L_1=H/(\gamma c)\) suffice. These formulas make design and dimension dependence explicit; they are not optimized.

Near the minimizer, the loss is of fourth order and its gradient of third order, so no positive global PL constant exists. Nonconvexity occurs already for a scalar residual at input \(u=1/2\), target \(v=2\), where \(3h'(u)^2+(h(u)-h(v))h''(u)<0\); it persists after sufficiently small dense, full-rank, overcomplete perturbations. Curvature grows without a global Lipschitz bound. This illustrates genuinely nonlinear coverage, not a restriction of the theorem to that family. The family also satisfies stronger fractional generalized-smoothness bounds and can be weakly convex; it is not evidence that every specialized method or proximal reduction is inferior.

The theorem itself is formalized; this illustrative family and its parameter calculation are explanatory mathematics, not additional Lean assumptions or a second main theorem. There is no noisy-gradient, composite, constrained, or infinite-dimensional claim. Known parameters and initial bounds are required. No empirical speedup or conference acceptance is asserted.

The literature assessment was made against current UTC date October 28, 2026: publicly available 2025 and 2026 ICML, ICLR, and NeurIPS records, targeted arXiv submissions and revisions from roughly October 2024 onward, and foundational citations. Official proceedings/OpenReview were used to distinguish acceptance from preprints. Some conference virtual pages were inaccessible; available proceedings, primary PDFs, and arXiv versions were used instead. The cited arXiv versions above were checked against their current version histories. The novelty assessment concerns the full oracle/assumption/confidence combination; the absence of a search hit is not its justification.
