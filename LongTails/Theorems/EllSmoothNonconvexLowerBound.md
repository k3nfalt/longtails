This result is a lower bound for finding stationary points of nonconvex functions under generalized \(\ell\)-smoothness, \(\|\nabla^2 f(x)\|\le \ell(\|\nabla f(x)\|)\). The [main theorem](EllSmoothNonconvexLowerBound.lean) proves that every randomized first-order method needs

\[
\Omega\!\left((2-\rho)\,\frac{\Delta\,\ell(\varepsilon)}{\varepsilon^{2}}\right)
\]

exact value-and-gradient queries to reach \(\mathbb E\|\nabla f(\hat x)\|\le\varepsilon\), for every smoothness function \(\ell\) of order \(\rho<2\) (defined below) with \(\ell(0)>0\), in sufficiently high dimension. The companion [upper bound](EllSmoothNonconvexUpperBound.md) shows that gradient descent with the step \(1/(2\ell(2\|\nabla f(x)\|))\) uses at most \(\lfloor 16\Delta\ell(\varepsilon)/\varepsilon^2\rfloor+1\) queries on the same class. Together they determine the complexity up to the factor \(2^{31}/(2-\rho)\):

\[
\Theta_\rho\!\left(\frac{\Delta\,\ell(\varepsilon)}{\varepsilon^{2}}\right),
\qquad\text{for }\ell(u)=L_0+L_\rho u^{\rho}:\quad
\Theta_\rho\!\left(\frac{L_0\Delta}{\varepsilon^{2}}+\frac{L_\rho\Delta}{\varepsilon^{2-\rho}}\right).
\]

The upper bound is known (Tyurin, [Toward a Unified Theory of Gradient Descent under Generalized Smoothness](https://arxiv.org/abs/2412.11773), ICML 2025, Theorem 5.1 and Section 5.3). The lower bound was known for \(\rho=0\) (Carmon, Duchi, Hinder, Sidford, [Lower bounds for finding stationary points I](https://arxiv.org/abs/1710.11606)) and for \(\rho=1\), the \((L_0,L_1)\) class (Shulgin and Sadiev, OPT 2026 workshop at NeurIPS, deterministic methods; Liang and Luo, [arXiv:2610.21692](https://arxiv.org/abs/2610.21692), Theorem 4.5, randomized methods). The new part is the lower bound for \(\rho\in(1,2)\) and for general \(\ell\), in one statement that covers all \(\rho\in[0,2)\) and all randomized algorithms.

## Setup

The base setup is [EllSmoothNonconvex](../Setups/EllSmoothNonconvex.lean). The parameters are the dimension \(d\), a function \(\ell:\mathbb R\to\mathbb R\), an order \(\rho\), the gap \(\Delta\), the accuracy \(\varepsilon\) and the starting point \(x^0\). An instance is a function \(f:\mathbb R^d\to\mathbb R\) such that

- \(f\) has a gradient everywhere and \(\nabla f\) is differentiable;
- \(\|D\nabla f(x)\|\le \ell(\|\nabla f(x)\|)\) for all \(x\) (operator norm of the Hessian);
- \(f(x^0)-f(x)\le\Delta\) for all \(x\);
- the oracle answers a query \(x\) with the exact pair \((f(x),\nabla f(x))\).

Success means \(\mathbb E\|\nabla f(\hat x)\|\le\varepsilon\) for the output \(\hat x\), where the expectation is over the algorithm's seed. All parameters, including \(\ell\), are public. There is no restriction on the algorithm (`allowedAlgorithm` is not used).

The Hessian condition is the \(\ell\)-smoothness of Li, Qian, Tian, Rakhlin, Jadbabaie ([Convex and Non-convex Optimization Under Generalized Smoothness](https://arxiv.org/abs/2306.01264), NeurIPS 2023, Definition 1) and of Tyurin's Assumption 3.1. Constant \(\ell\) is \(L\)-smoothness, \(\ell(u)=L_0+L_1u\) is the \((L_0,L_1)\)-smoothness of Zhang, He, Sra, Jadbabaie ([ICLR 2020](https://arxiv.org/abs/1905.11881)), and \(\ell(u)=L_0+L_\rho u^\rho\) is the \((\rho,L_0,L_\rho)\) family used in both papers.

**Order-\(\rho\) regularity.** The setup requires \(0\le\rho\le2\), \(\Delta\ge0\), \(\varepsilon>0\) and `Regular ℓ ρ`:

1. \(\ell\) is nondecreasing on \([0,\infty)\);
2. \(\ell(v)\,u^{\rho}\le \ell(u)\,v^{\rho}\) for \(0<u\le v\), that is, \(\ell(u)/u^{\rho}\) is nonincreasing;
3. \(\ell(u)>0\) for \(u>0\).

Items 1 and 3 are part of Tyurin's Assumption 3.1, which asks for a nondecreasing positive locally Lipschitz \(\ell\) (and allows \(f\) to be defined on an open domain; here \(f\) is defined on all of \(\mathbb R^{d}\)). Item 2 is an added restriction relative to that assumption; it says that \(\ell\) grows at most like \(u^\rho\). It is used in two places. The upper bound uses it above \(\varepsilon\): \(\ell(2g)\le\ell(\varepsilon)(2g/\varepsilon)^{\rho}\) for \(g\ge\varepsilon\), which gives \(g^2/\ell(2g)\ge\varepsilon^2/(4\ell(\varepsilon))\). The lower bound uses it below \(\varepsilon\): \(\ell(g)\ge\ell(\varepsilon)(g/\varepsilon)^{\rho}\) for \(g\le\varepsilon\), which is the amount of curvature the hard instance is allowed where its gradient is small. The lemma `regular_polynomial` in [EllSmoothExamples](../Proofs/EllSmoothExamples.lean) proves that \(\ell(u)=L_0+L_\rho u^{\rho}\) is regular of order \(\rho\) for \(L_0>0\), \(L_\rho\ge0\), \(\rho\ge0\), and `regular_weaken` proves that order \(\rho\) implies order \(\rho'\ge\rho\). So the class contains the \((\rho,L_0,L_\rho)\) family for every \(\rho\le2\), in particular \(L\)-smooth and \((L_0,L_1)\)-smooth functions.

**High-dimensional regime.** The lower bound is stated on [HighDimensionalEllSmoothNonconvex](../Setups/HighDimensionalEllSmoothNonconvex.lean), which has the same instances, oracle and success criterion and adds four validity conditions:

- \(\rho<2\);
- \(\ell(0)>0\);
- \(2^{27}\varepsilon^{2}\le(2-\rho)\,\Delta\,\ell(\varepsilon)\);
- \(d\ \ge\ 2^{56}\,(N+1)^{6}\,\big(\ell(\varepsilon)/\ell(0)\big)^{4}\), where \(N=\lfloor(2-\rho)\Delta\ell(\varepsilon)/(2^{27}\varepsilon^{2})\rfloor\) is the budget.

The third condition says that the budget is at least one. The condition \(\ell(0)>0\) and the dimension requirement are required by this construction; the note does not claim that they are necessary. Positivity of \(\ell\) at \(0\) is also part of Tyurin's Assumption 3.1. The dimension is polynomial in the budget and in the ratio \(\ell(\varepsilon)/\ell(0)\), and this ratio may be arbitrarily large: for \(\ell(u)=L_0+L_\rho u^\rho\) it is \(1+L_\rho\varepsilon^\rho/L_0\), so the regime where the term \(L_\rho\Delta/\varepsilon^{2-\rho}\) dominates is covered. The regime is nonempty: the lemma `highDimensional_valid_nonempty` in [EllSmoothExamples](../Proofs/EllSmoothExamples.lean) checks all validity conditions for \(\ell(u)=1+u\), \(\rho=1\), \(\varepsilon=1\), \(\Delta=2^{27}\), \(d=2^{60}\cdot729\), where \(N=2\) and \(\ell(\varepsilon)/\ell(0)=2\). More generally, the first three added conditions do not involve \(d\), and the fourth is a lower bound on \(d\). So for every regular \(\ell\) of order \(\rho<2\) with \(\ell(0)>0\) and every \(\Delta,\varepsilon\) with \(2^{27}\varepsilon^{2}\le(2-\rho)\Delta\ell(\varepsilon)\), in particular for \(\ell(u)=L_0+L_\rho u^{\rho}\) with \(\rho\in(1,2)\), the parameters are valid in all sufficiently large dimensions.

## Statement

The public budget is

\[
\left\lfloor\frac{(2-\rho)\,\Delta\,\ell(\varepsilon)}{2^{27}\,\varepsilon^{2}}\right\rfloor .
\]

For every valid parameter choice, every algorithm (with any seed space and law) and every budget \(b\) up to this value, including \(0\), there is an admissible \(f\) with its exact oracle such that the output of the actual `execute` run does not satisfy \(\mathbb E\|\nabla f(\hat x)\|\le\varepsilon\). The instance depends on the algorithm and on \(b\), but not on the realized seed. The proof shows more: on the chosen instance \(\|\nabla f(\hat x)\|\ge4\varepsilon\) with probability greater than \(1/4\).

For \(\ell(u)=L_0+L_\rho u^{\rho}\) the budget is \(\lfloor(2-\rho)(L_0\Delta/\varepsilon^{2}+L_\rho\Delta/\varepsilon^{2-\rho})/2^{27}\rfloor\). For \(\rho=1\) this is \(\Omega(L_0\Delta/\varepsilon^{2}+L_1\Delta/\varepsilon)\), and for \(\rho=0\) it is \(\Omega(L\Delta/\varepsilon^{2})\).

## Why the known instances do not give this

For \(\rho\le1\) the bound follows from the \(\rho=1\) instance: a chain whose tails satisfy \(|\Phi''|\le\Phi'\le1\) also satisfies \(|\Phi''|\le(\Phi')^{\rho}\). That range is routine.

For \(\rho\in(1,2)\) it does not. The natural class inclusion is given by Young's inequality, \(L_0'+L_1'u\le L_0'+L_1'(\rho-1)\tau/\rho+L_1'u^{\rho}/(\rho\tau^{\rho-1})\), which embeds an \((L_0',L_1')\) class into a \((\rho,L_0,L_\rho)\) class. Optimizing over \(\tau\) turns the known \(\Omega(L_1'\Delta/\varepsilon)\) into \(\Omega(\Delta L_\rho^{1/\rho}L_0^{(\rho-1)/\rho}/\varepsilon)\). This is smaller than \(L_\rho\Delta/\varepsilon^{2-\rho}\) by the factor \((L_0/(L_\rho\varepsilon^{\rho}))^{(\rho-1)/\rho}\), which tends to zero exactly when the \(L_\rho\) term dominates. A new instance is needed, with tails adapted to \(\rho\).

## The hard instance

All of the following is proved in Lean; the modules are linked at each step. Write \(\vartheta=\min(2-\rho,\tfrac12)\) and \(\mu=\ell(0)/\ell(\varepsilon)\in(0,1]\).

**Profiles** ([EllSmoothProfiles](../Proofs/EllSmoothProfiles.lean)). \(\Psi\) is a twice differentiable step, \(0\) on \((-\infty,\tfrac12]\) and \(1\) on \([1,\infty)\). The link profile \(\Phi\) is nondecreasing with \(\Phi'=1\) on \([-1,1]\) and, outside, a terminated power-law tail

\[
\Phi'(t)=\frac{g_v(P(t))}{1-2v},\qquad P(t)=\Big(1+\frac{(|t|-1)_+^{2}}{\vartheta^{2}}\Big)^{-e},\qquad e=\frac{1}{2(1-\vartheta)},\qquad v=\frac{\mu\vartheta}{12},
\]

where \(g_v\) is a \(C^{1}\) function that is \(0\) below \(v\) and equals \(y-2v\) above \(3v\). The exponent is chosen so that \(e(2-\vartheta)=e+\tfrac12\), which gives \(|P'|\le(2/\vartheta)P^{2-\vartheta}\) (`dP_abs`). Three facts are used later:

- \(|\Phi''|\le(36/\vartheta)\,(\Phi')^{2-\vartheta}+\mu\) (`ddphi_relative`): the curvature is controlled by a power \(2-\vartheta\ge\rho\) of the slope, except near the cut-off, where it is at most \(\mu\);
- \(\Phi'=0\) for \(|t|\ge1+12/\mu\) (`dphi_of_ge`): the tail ends, which is where \(\ell(0)>0\) is used;
- \(0\le\Phi\le10\) (`phi_le`): the tail has bounded mass, uniformly in \(\vartheta\) and \(\mu\). Indeed \(\int_0^\infty(1+s^{2}/\vartheta^{2})^{-e}ds\le\vartheta+\vartheta/(2e-1)=1\), because \(2e-1=\vartheta/(1-\vartheta)\). This is why only one factor \(\vartheta\) is lost, in the curvature constant, and none in the gap.

At \(\rho\to2\) the exponent \(e\to\tfrac12\) and the tail stops being integrable, so the construction cannot reach \(\rho=2\).

**Chain** ([EllSmoothChain](../Proofs/EllSmoothChain.lean), [EllSmoothChainHessian](../Proofs/EllSmoothChainHessian.lean)). On \(\mathbb R^{n+1}\),

\[
F(u)=-\Phi(u_0)+\sum_{i<n}\big[\Psi(-u_i)\Phi(-u_{i+1})-\Psi(u_i)\Phi(u_{i+1})\big].
\]

This is the two-sided zero-chain of Carmon et al. with the new profiles. The lemmas are: \(\|\nabla F(u)\|\ge1\) whenever some \(|u_k|<1\) (`field_norm_ge_one`); the gradient at \(u\) depends only on the coordinates up to the first one with \(|u_k|\le\tfrac14\) (`visibleField_eq`); and

\[
\|\nabla^{2}F(u)\|\le\frac{1000}{\vartheta}\min\!\big(1,\|\nabla F(u)\|^{2-\vartheta}\big)+\mu
\]

(`fderiv_field_bound`). The last bound is the technical core. If some \(|u_k|<1\) it follows from \(\|\nabla F\|\ge1\) and a uniform Hessian bound. If all \(|u_i|\ge1\), all \(\Psi\) factors are constant, \(F\) is separable, the Hessian is diagonal with entries \(\pm\Phi''(\pm u_i)\), and the profile inequality applies coordinate by coordinate.

**Confinement** ([EllSmoothHard](../Proofs/EllSmoothHard.lean), [EllSmoothHardBounds](../Proofs/EllSmoothHardBounds.lean)). The chain is placed on hidden coordinates \(\pi:[n+1]\hookrightarrow[d]\) and cut off far from the origin:

\[
h_\pi(w)=\mathrm{cut}(\|w\|^{2})\,F(w_{\pi(0)},\dots,w_{\pi(n)})+\mathrm{wall}(\|w\|^{2}),\qquad R=\frac{2^{22}(n+1)^{2}}{\mu^{2}},
\]

where \(\mathrm{cut}=1\) for \(\|w\|\le2R\) and \(0\) for \(\|w\|\ge4R\), and the wall is zero for \(\|w\|\le R\) and grows with curvature of order \(\mu^{2}/(n+1)\). Then \(h_\pi\) does not depend on \(\pi\) outside the ball of radius \(4R\), \(\|\nabla h_\pi(w)\|\ge1\) for \(\|w\|\ge2R\) (`hgrad_far`), \(\|\nabla h_\pi(w)\|\ge\tfrac12\) inside when some chain coordinate is below \(1\) in absolute value (`hgrad_near_unfinished`), \(-20(n+1)\le h_\pi\) and \(h_\pi(0)\le0\) (`hval_ge`, `hval_zero_le`), and the class inequality survives with a larger constant (`hgrad_class`):

\[
\|\nabla^{2}h_\pi(w)\|\le\frac{4000}{\vartheta}\Big(\min\!\big(1,\|\nabla h_\pi(w)\|^{2-\vartheta}\big)+\mu\Big).
\]

The cut-off is what allows unbounded queries: a query outside the ball reveals nothing about \(\pi\), and a query inside has at most \(256R^{2}\) coordinates above \(\tfrac14\).

**Scaling** ([EllSmoothLowerBound](../Proofs/EllSmoothLowerBound.lean)). \(f(x)=a\,h_\pi((x-x^{0})/\lambda)\) with

\[
\frac{a}{\lambda}=8\varepsilon,\qquad\frac{a}{\lambda^{2}}=\frac{\vartheta\,\ell(\varepsilon)}{8000}.
\]

With \(g=\|\nabla f(x)\|=8\varepsilon\|\nabla h_\pi\|\), the Hessian bound becomes \(\|\nabla^2 f(x)\|\le\tfrac12\ell(\varepsilon)\big(\min(1,(g/8\varepsilon)^{2-\vartheta})+\mu\big)\). This is at most \(\ell(g)\) (`class_scalar`): for \(g\ge\varepsilon\) by monotonicity, and for \(g<\varepsilon\) because \((g/8\varepsilon)^{2-\vartheta}\le(g/\varepsilon)^{\rho}\le\ell(g)/\ell(\varepsilon)\) by regularity, while \(\tfrac12\ell(\varepsilon)\mu=\tfrac12\ell(0)\le\tfrac12\ell(g)\). The gap is \(f(x^{0})-\inf f\le20(n+1)a\le\Delta\) when \((n+1)\,2^{26}\varepsilon^{2}\le(2-\rho)\Delta\ell(\varepsilon)\), using \(\vartheta\ge(2-\rho)/4\). This is where the budget formula and the factor \(2-\rho\) come from.

**Hiding** ([EllSmoothSimulation](../Proofs/EllSmoothSimulation.lean), [EllSmoothLowerBound](../Proofs/EllSmoothLowerBound.lean)). The algorithm's run on \(f_\pi\) is compared with a simulated run that reveals one hidden coordinate per query. The two coincide unless some query inside the ball of radius \(4R\) has a coordinate larger than \(\tfrac14\) at a not yet revealed index of \(\pi\). The counting lemma `bounded_prefix_bad_count` from [SmoothConvexFiniteHiding](../Proofs/SmoothConvexFiniteHiding.lean), already in the repository, bounds the number of such \(\pi\); with the stated dimension fewer than one eighth of all \(\pi\) are hit, for every seed. On a \(\pi\) that is not hit, the last chain coordinate of the output is at most \(\tfrac14\), so \(\|\nabla f(\hat x)\|\ge4\varepsilon\). Averaging over \(\pi\) (`some_bad_set`) gives one \(\pi\) with failure probability above \(\tfrac14\), and Markov's inequality gives \(\mathbb E\|\nabla f(\hat x)\|>\varepsilon\).

## What is new and what is not

- Not new: the upper bound; the lower bound at \(\rho=0\) and \(\rho=1\); the zero-chain architecture, the random-coordinate hiding argument and its counting lemma. The range \(\rho<1\) is a routine consequence of the \(\rho=1\) instance.
- New: the lower bound for \(\rho\in(1,2)\) and for general \(\ell\) of order \(\rho<2\). The mechanism is the terminated power-law tail with exponent tied to \(\rho\) through \(e(2-\vartheta)=e+\tfrac12\), its bounded mass, and the proof that the chain, the cut-off and the wall keep the relative curvature bound \(\|\nabla^2\|\lesssim\vartheta^{-1}\min(1,\|\nabla\|^{2-\vartheta})+\mu\) on all of \(\mathbb R^{d}\). The statement holds for all randomized algorithms and unbounded queries, with the factor \(2-\rho\) explicit.
- For \(\rho=1\) the theorem gives a randomized lower bound for the \((L_0,L_1)\) class with power-law instead of exponential or logistic tails. It does not improve the rate of Shulgin–Sadiev or Liang–Luo there, and its dimension requirement is much stronger than theirs. Liang–Luo (Lemma 4.4) need \(d\ge T+32R^{2}\log(2T^{2}/(q\delta))\) with \(R=1000\sqrt T/\mu\), which is linear in the budget \(T\) and quadratic in \((L_0+L_1\varepsilon)/L_0\) up to logarithms. Shulgin–Sadiev (abstract) need a dimension proportional to the budget, for deterministic methods. This theorem needs \(2^{56}(N+1)^{6}(\ell(\varepsilon)/\ell(0))^{4}\).

## Limitations

- The upper and lower budgets differ by \(2^{31}/(2-\rho)\). The dependence on \(2-\rho\) is not shown to be necessary. At \(\rho=2\) the upper bound still holds (it gives \(O(L_0\Delta/\varepsilon^{2}+L_2\Delta)\), as in Tyurin's Section 5.3), but this lower bound does not: the tail of the construction is no longer integrable. Whether the upper bound is tight at \(\rho=2\) is left open.
- The lower bound needs \(\ell(0)>0\), dimension at least \(2^{56}(N+1)^6(\ell(\varepsilon)/\ell(0))^4\), and \(N\ge1\). These are requirements of this construction. The dimension is a degree-six polynomial in the budget and degree four in \(\ell(\varepsilon)/\ell(0)\); it comes from the confinement radius \(R\propto(n+1)^{2}/\mu^{2}\) and the deterministic counting argument, and is far from the dimension requirements known for \(\rho\in\{0,1\}\). No attempt was made to optimize it.
- Regularity of order \(\rho\) is an extra assumption relative to Tyurin's Assumption 3.1. Without it neither the simple formula \(\Delta\ell(\varepsilon)/\varepsilon^{2}\) nor this lower bound is claimed.
- The oracle is exact. No stochastic statement is made.
- The criterion is the expected gradient norm at a single output point. The upper bound is deterministic, so it also satisfies every stronger criterion; the lower bound holds for the weakest of them.
- Only the [abstract](https://neurips.cc/virtual/2026/161557) of the Shulgin–Sadiev workshop paper was accessible when this note was written. The comparison with it relies on that abstract alone (deterministic methods, \((L_0,L_1)\) class, logistic tail, dimension proportional to the query budget).

## Scope

The task asked for almost tight upper and lower bounds for an important and popular setup, in terms of `Template` and `TemplateLowerBound`. Generalized smoothness is the standard model for gradient clipping and adaptive steps. The pair consists of [EllSmoothNonconvexUpperBound](EllSmoothNonconvexUpperBound.lean), a `Convergence` statement on the base setup, and this `NonConvergence` statement on the high-dimensional restriction of the same setup. Every instance of the restricted setup is an instance of the base setup, so the upper bound applies to it with the same budget. The two budgets match up to the factor \(2^{31}/(2-\rho)\) wherever the lower bound is valid. No open pull request of the repository treats \(\ell\)-smooth or \((\rho,L_0,L_\rho)\)-smooth nonconvex optimization.
