# Energy-controlled Hessian reuse under gradient-dependent third derivatives

The result concerns general nonconvex objectives in arbitrary finite dimension. It reduces the number of full Hessian evaluations under the standard pointwise condition

\[
\|D^3 f(x)\|\le L_0+L_1\|\nabla f(x)\|.
\]

The contribution is a Hessian-reuse guarantee for this class, not a claim of optimal complexity for every subclass. In particular, the guarantee does **not** improve the strongest known rate when a uniform Hessian Lipschitz constant is available.

## Formal statement and information model

The [setup](../Setups/GradientDependentHessian.lean) specifies a real finite-dimensional inner-product space, a globally three-times continuously differentiable objective, and the displayed bound in operator norm. Its public parameters satisfy

\[
L_0>0,\quad L_1\ge0,\quad \Delta>0,\quad G_0\ge0,\quad \varepsilon>0,\quad m\in\mathbb N,\ m\ge1.
\]

The initialization assumptions are \(f(x_0)-f(x)\le\Delta\) for every \(x\), and \(\|\nabla f(x_0)\|\le G_0\). No minimizer, convexity, bounded Hessian, bounded gradient, or bounded sublevel set is assumed. The nested derivative of the gradient used in Lean represents the third derivative through the Euclidean Riesz identification, with no dimension-dependent norm conversion.

There are two separate exact oracle channels: a gradient channel and a full Hessian channel. Tagged replies prevent either channel from returning the other derivative for free. The algorithm knows the stated scalar parameters and its starting point; it does not know the objective or its derivative maps. There is no restriction to an artificially prescribed algorithm family.

The [main theorem](EnergyHessianReuse.lean) constructs the [algorithm](../Algorithms/EnergyHessianReuse.lean), runs it through `execute`, and guarantees

\[
\|\nabla f(x_{\rm out})\|\le\varepsilon.
\]

The returned point has the smallest observed gradient norm among all queried iterates. The guarantee holds for every oracle-seed realization, and hence almost surely for the probability measure in the framework. It is a first-order stationarity guarantee, not a second-order stationarity guarantee.

## Algorithm and oracle budgets

Write

\[
k=\left\lceil\frac{\log(1+L_1G_0/(mL_0))}{\log(4/3)}\right\rceil,
\qquad
A=27000\Delta\sqrt{mL_0}\,\varepsilon^{-3/2}
 +15000\Delta\sqrt{mL_1}\,\varepsilon^{-1}.
\]

The public budgets are

\[
N_g=k+\lceil A\rceil+m+74,
\qquad
N_H=k+\left\lceil54000\Delta\sqrt{L_0/m}\,\varepsilon^{-3/2}
 +30000\Delta\sqrt{L_1/m}\,\varepsilon^{-1}\right\rceil+146.
\]

The Lean budget expands these formulas directly in the setup parameters. With gradient cost one and full-Hessian cost \(m\), they imply

\[
N_g+mN_H\le
2mk+81000\Delta\sqrt{mL_0}\,\varepsilon^{-3/2}
+45000\Delta\sqrt{mL_1}\,\varepsilon^{-1}+223m.
\]

The algorithm first takes \(k\) fresh-Hessian steps. Each subsequent block takes one fresh-Hessian preparatory step, obtains a new Hessian at its endpoint, and reuses that Hessian for \(m\) steps. There are \(B=\lceil(A+72)/(m+1)\rceil\) blocks. The completion prefix uses exactly \(k+B(m+1)+1\) gradient calls and \(k+2B\) Hessian calls. Cached gradients are retained across block boundaries. The framework can issue padding queries after completion; the completed state preserves its output and the public budgets cover those calls.

Each step uses a capped cubic model with quadratic damping. Its radius is \(\rho=\Delta/\varepsilon\) when \(L_1=0\), and \(\rho=1/(100\sqrt{L_1})\) otherwise. The cubic coefficient is

\[
\sigma=\max\{\sigma_{\rm previous}/2,\ 100(mL_0+L_1\|g\|)\}.
\]

A preparatory step has zero damping. A reuse step has

\[
\delta=4L_0P+100L_1E_{\rm history},
\]

where \(P\) is the accumulated lazy-step path length and \(E_{\rm history}\) includes the preparatory energy and previous lazy-step energies. These quantities use cached model data, not objective queries.

The model certificate includes stationarity, a nonnegative cap multiplier \(\mu\), complementary slackness, and positive semidefiniteness of the shifted Hessian. Its existence is proved, including the trust-region hard case, in [CappedCubicModel](../Proofs/CappedCubicModel.lean). Exact model solution is internal computation, not an additional oracle. Arithmetic complexity and finite-precision subproblem solution are not covered by this theorem. Thus the result addresses the oracle cost of making second-order methods cheaper; it does not establish a complete implementation-level speedup.

## New proof mechanism

The useful energy is

\[
e=\sigma r^3+\delta r^2+\mu r^2,
\qquad f(x)-f(x+s)\ge e/3.
\]

The pointwise third-derivative condition does not provide a uniform constant along an unknown trajectory. Endpoint interpolation first controls gradients on each short segment. The resulting Hessian transport term contains products of endpoint gradient norms and step lengths. These products are charged to adjacent step energies, including the cap multiplier term.

The block invariant is

\[
\|\nabla^2f(x)-B\|\le
2L_0P+36L_1E_{\rm history}-18L_1e_{\rm previous}.
\]

It propagates under the actual cached-Hessian update and implies the required error bound \(\|\nabla^2f(x)-B\|\le\delta/2\). A fresh preparatory step makes the invariant valid at every reset. The proof therefore replaces an uncontrolled maximum-gradient smoothness constant by computable descent energy. Burn-in removes polynomial dependence on the initial gradient, leaving only the explicit logarithm. The [block proof](../Proofs/EnergyHessianBlock.lean), [running totals](../Proofs/EnergyHessianLedger.lean), and [execution-to-convergence proof](../Proofs/EnergyHessianRun.lean) make these connections explicit.

## Closest results and improvement regimes

* **Fang, Marumo, and Takeda, arXiv:2607.10741v1, July 12, 2026.** [Assumption 1, Theorem 2, and Corollary 1](https://arxiv.org/html/2607.10741v1) treat this gradient-dependent third-derivative class with fresh Hessians. The first-order accuracy terms are of order \(\Delta(\sqrt{L_0}\varepsilon^{-3/2}+\sqrt{L_1}\varepsilon^{-1})\) iterations, with initialization terms. Charging a Hessian by \(m\) multiplies these terms by \(m\). Our bound replaces that factor by \(\sqrt m\), when the accuracy terms dominate initialization and additive costs. Their parameter-free features and second-order stationarity guarantee are not preserved: our algorithm uses the public parameters and proves first-order stationarity only. This source is a preprint, not claimed here as an accepted conference paper.
* **Doikov, Chayti, and Jaggi, Second-Order Optimization with Lazy Hessians, ICML 2023.** [Theorem 3.1, Corollary 3.6, and Lemma B.1 / equation (47)](https://proceedings.mlr.press/v202/doikov23a/doikov23a.pdf), with [official proceedings status](https://proceedings.mlr.press/v202/doikov23a.html), are the direct algorithmic predecessor. LazyCRN already obtains a square-root weighted Hessian-reuse improvement under a uniform Hessian Lipschitz constant, using a fixed cubic coefficient proportional to that constant times the block length. Its stale-Hessian analysis absorbs path-length cubes with that uniform constant. The present contribution is not the square-root factor itself: it extends reuse to gradient-dependent third derivatives through energy damping, the preparatory reset, and cap-multiplier charging. Substituting an epoch maximum gradient in the earlier proof leaves an uncontrolled quantity and does not establish the displayed bound.
* **Chen, Liu, Luo, and Zhang, NALEN, arXiv:2501.17488v3, July 13, 2026; COLT 2026.** [Theorem 4.1 and its oracle-cost analysis](https://arxiv.org/html/2501.17488v3), with [official proceedings status](https://proceedings.mlr.press/v336/chen26a.html), give the stronger \(m^{1/3}\) weighted factor under uniform Hessian Lipschitzness. Our \(L_1=0\) specialization loses a factor \(m^{1/6}\) in the leading term. NALEN's midpoint/online-to-nonconvex construction does not supply a bound on the pointwise gradients appearing in the present assumption; substituting an unknown maximum gradient is not a complexity guarantee for this setup.
* **Filho and Gonçalves, May 14, 2026, adaptive Hessian reuse.** The [primary manuscript](https://optimization-online.org/wp-content/uploads/2026/05/Vilmar_e_Max-28-1.pdf) assumes uniform Hessian Lipschitzness. The later [Blockwise Stabilized ARC preprint, arXiv:2608.22129v3, October 14, 2026, Assumption 2.1](https://arxiv.org/html/2608.22129v3), also retains a uniform constant. Neither checked theorem provides the energy-controlled extension above.

If a uniform Hessian Lipschitz constant \(H\) is additionally available, applying NALEN gives an alternative bound. Ignoring universal constants and initialization terms, the present bound is smaller only in regimes such as

\[
H\gg m^{1/3}(L_0+L_1\varepsilon).
\]

This is a comparison with an applicable upper bound, not a lower bound or a claim that specialized algorithms cannot do better. No matching lower bound for the full gradient-dependent class is established here. When Hessian cost substantially exceeds dimension, approximating curvature with gradient finite differences is a competing option; no optimal tradeoff is claimed in that regime. The intended weighted comparisons include \(1\le m\le\dim E\), while the theorem itself permits every integer \(m\ge1\).

## Natural nonlinear instances and limitations

An interacting family is

\[
f(x)=\sum_i\cosh(x_i-a_i)
 +A\sum_{\{i,j\}\in\mathcal E}\cos(x_i-x_j).
\]

For \(A>0\) and a graph of maximum degree \(D\ge1\), the third-derivative condition holds with \(L_1=1\) and \(L_0=(1+2\sqrt2)AD\), independently of the ambient dimension. The objective is bounded below, has unbounded global gradients and curvature, and can be nonconvex when the graph interaction is sufficiently strong. Nonconstant shifts avoid building a known stationary point into the example. These are coupled nonlinear objectives, not a scalar or quadratic restriction of the theorem.

For a local-curvature diagnostic, take the known lower bound \(n-A|\mathcal E|\) and choose \(\Delta\ge f(x_0)-(n-A|\mathcal E|)\). On the initial sublevel set the Hessian Lipschitz constant can be bounded by

\[
H_K\le\sqrt{\Delta(\Delta+2)}+2\sqrt2 AD.
\]

This bound is of order \(\Delta+AD\) when \(\Delta\ge1\); the square-root term must be retained for small gaps. This is a diagnostic of the parameter cost of a local-curvature reduction, not an application of NALEN's global theorem: such an application would additionally require a proof that all its internal query points remain in a suitable region, or a valid global extension. Neither is supplied here. The rigorous NALEN comparison above assumes an actually available global constant \(H\).

More generally, the pointwise assumption does not imply a finite sublevel-set Hessian Lipschitz constant: the scalar function \(\sqrt{1+x^2}-x\cos x\) in the primary Fang–Marumo–Takeda examples already demonstrates that obstruction. This scalar calculation diagnoses the failed reduction; the proved theorem remains arbitrary-dimensional and nonlinear.

The literature comparison was checked against primary sources available on October 16, 2026 UTC, following independent surveys of publicly available 2025/2026 ICML, ICLR, and NeurIPS material and roughly the preceding two years of arXiv submissions and revisions. The novelty claim is the energy-controlled Hessian-reuse guarantee under the stated standard assumption. It is not based on the Lean formalization, a newly named setup, or an artificial restriction on competing algorithms.
