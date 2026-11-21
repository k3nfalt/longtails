This file formalizes the gradient-descent upper bound for nonconvex optimization under generalized \(\ell\)-smoothness, \(\|\nabla^2 f(x)\|\le\ell(\|\nabla f(x)\|)\). The [main theorem](EllSmoothNonconvexUpperBound.lean) proves that gradient descent with the step \(1/(2\ell(2\|\nabla f(x)\|))\) returns a point with \(\|\nabla f(\hat x)\|\le\varepsilon\) after at most

\[
\left\lfloor\frac{16\,\Delta\,\ell(\varepsilon)}{\varepsilon^{2}}\right\rfloor+1
\]

oracle calls, for every \(\ell\) that is regular of order \(\rho\le2\). The rate is not new. It is the nonconvex rate of Tyurin ([Toward a Unified Theory of Gradient Descent under Generalized Smoothness](https://arxiv.org/abs/2412.11773), ICML 2025, Theorem 5.1 and Section 5.3), specialized to regular \(\ell\) and written with one closed-form step. It is included because it is the upper half of a pair: the companion [lower bound](EllSmoothNonconvexLowerBound.md), which is the new result, shows that every randomized method needs \(\lfloor(2-\rho)\Delta\ell(\varepsilon)/(2^{27}\varepsilon^{2})\rfloor\) queries on the same class in high dimension.

## Setup

The setup is [EllSmoothNonconvex](../Setups/EllSmoothNonconvex.lean). An instance is \(f:\mathbb R^{d}\to\mathbb R\) with a gradient everywhere, a differentiable gradient map, \(\|D\nabla f(x)\|\le\ell(\|\nabla f(x)\|)\) for all \(x\), and \(f(x^{0})-f(x)\le\Delta\) for all \(x\). The oracle returns the exact pair \((f(x),\nabla f(x))\). Success means \(\mathbb E\|\nabla f(\hat x)\|\le\varepsilon\).

The validity conditions are \(0\le\rho\le2\), \(\Delta\ge0\), \(\varepsilon>0\), and regularity of order \(\rho\): \(\ell\) is nondecreasing on \([0,\infty)\), positive on \((0,\infty)\), and \(\ell(v)u^{\rho}\le\ell(u)v^{\rho}\) for \(0<u\le v\). The last condition is an added restriction relative to Tyurin's Assumption 3.1, which asks only for a nondecreasing positive locally Lipschitz \(\ell\). It holds for \(\ell(u)=L_0+L_\rho u^{\rho}\) with \(L_0>0\), \(L_\rho\ge0\) (`regular_polynomial` in [EllSmoothExamples](../Proofs/EllSmoothExamples.lean)), so the theorem covers \(L\)-smooth functions (\(\rho=0\)), \((L_0,L_1)\)-smooth functions (\(\rho=1\)) and the \((\rho,L_0,L_\rho)\) family for \(\rho\le2\). For that family the budget is

\[
\left\lfloor 16\Big(\frac{L_0\Delta}{\varepsilon^{2}}+\frac{L_\rho\Delta}{\varepsilon^{2-\rho}}\Big)\right\rfloor+1 .
\]

Neither \(\ell(0)>0\) nor a dimension condition is needed here.

## Algorithm

The algorithm is `ellGd` in [EllSmoothGd](../Algorithms/EllSmoothGd.lean). Its state is the current point. It queries the oracle at the current point, reads the gradient \(g\) from the reply, and

- keeps the point if \(\|g\|\le\varepsilon\);
- otherwise moves to \(x-\dfrac{1}{2\ell(2\|g\|)}\,g\).

The output is the current point after the last query. The function value in the reply is ignored, so the method is a pure gradient method; the value is part of the oracle only because the lower bound is proved against the stronger oracle. The algorithm uses \(\ell\), \(\varepsilon\) and \(x^{0}\), and does not use \(\rho\) or \(\Delta\). The method is deterministic, so the expectation in the success criterion is over a point mass.

Tyurin's step is \(\int_0^1 dv/\ell(\|g\|+\|g\|v)\). The step used here is its lower bound \(1/(2\ell(2\|g\|))\) with an extra factor \(\tfrac12\), which keeps the formula closed-form and makes the proof short.

## Proof

The proof is in [EllSmoothGd (proofs)](../Proofs/EllSmoothGd.lean).

**One step** (`descent`). Let \(g=\nabla f(x)\ne0\), \(\gamma=1/(2\ell(2\|g\|))\) and \(x_t=x-t\gamma g\). The map \(t\mapsto\nabla f(x_t)-g\) vanishes at \(0\) and its derivative has norm at most \(\gamma\,\ell(\|\nabla f(x_t)\|)\,\|g\|\). As long as \(\|\nabla f(x_t)-g\|\le t\|g\|\) with \(t\le1\), the gradient norm is at most \(2\|g\|\), so this derivative is at most \(\gamma\ell(2\|g\|)\|g\|=\|g\|/2<\|g\|\). The fencing lemma `image_norm_le_of_norm_deriv_right_lt_deriv_boundary` of Mathlib turns this into \(\|\nabla f(x_t)-g\|\le t\|g\|\) on \([0,1]\) without assuming it. Then \(t\mapsto f(x_t)+\gamma\|g\|^{2}(t-t^{2}/2)\) has nonpositive derivative, and

\[
f(x-\gamma g)\le f(x)-\frac{\|g\|^{2}}{4\,\ell(2\|g\|)} .
\]

Only monotonicity of \(\ell\) is used in this step.

**Decrease per step** (`decrease_lower`). For \(\|g\|>\varepsilon\), regularity gives \(\ell(2\|g\|)\le\ell(\varepsilon)(2\|g\|/\varepsilon)^{\rho}\le4\ell(\varepsilon)\|g\|^{2}/\varepsilon^{2}\), so every moving step decreases \(f\) by at least \(\varepsilon^{2}/(16\ell(\varepsilon))\).

**Counting** (`iterate_accuracy`). If the output after \(K\) queries had gradient norm above \(\varepsilon\), then no earlier iterate was frozen, all \(K\) steps moved, and \(K\varepsilon^{2}/(16\ell(\varepsilon))\le f(x^{0})-f(x_K)\le\Delta\). This is impossible for \(K=\lfloor16\Delta\ell(\varepsilon)/\varepsilon^{2}\rfloor+1\). The theorem connects this to the actual `execute` run with the exact oracle.

## Relation to prior work and to the lower bound

- Tyurin's Theorem 5.1 proves \(\min_{k<T}\|\nabla f(x_k)\|^{2}/\ell(2\|\nabla f(x_k)\|)\le4\Delta/T\) for general \(\ell\), and Section 5.3 derives from it \(\max\{8L_0\Delta/\varepsilon^{2},\,32L_\rho\Delta/\varepsilon^{2-\rho}\}\) iterations for the \((\rho,L_0,L_\rho)\) family with \(0\le\rho\le2\) (in that paper the target is \(\|\nabla f\|^{2}\le\varepsilon\), so its \(\varepsilon\) is \(\varepsilon^{2}\) here). The present statement has the same rate. The differences are presentational: a closed-form step, a last-iterate output obtained by freezing, an explicit constant, and the one-line budget \(16\Delta\ell(\varepsilon)/\varepsilon^{2}\) valid for all regular \(\ell\). For the \((\rho,L_0,L_\rho)\) family the constant \(16\) on both terms lies between Tyurin's \(8\) on the \(L_0\) term and \(32\) on the \(L_\rho\) term, so the two bounds agree up to a factor \(2.5\).
- For \(\rho=1\) the rate \(O(L_0\Delta/\varepsilon^{2}+L_1\Delta/\varepsilon)\) predates Tyurin: it was obtained by Vankov, Rodomanov, Nedich, Sankar and Stich ([arXiv:2410.10800](https://arxiv.org/abs/2410.10800)), and Tyurin's Section 5.2 notes that his bound coincides with theirs. Older results, such as Li et al. ([arXiv:2306.01264](https://arxiv.org/abs/2306.01264), NeurIPS 2023) for general \(\ell\) and Zhang et al. ([arXiv:1905.11881](https://arxiv.org/abs/1905.11881)) for \(\rho=1\), have rates that depend on the initial gradient norm or on additional constants.
- The companion lower bound has budget \(\lfloor(2-\rho)\Delta\ell(\varepsilon)/(2^{27}\varepsilon^{2})\rfloor\) and is valid when \(\rho<2\), \(\ell(0)>0\), \(2^{27}\varepsilon^{2}\le(2-\rho)\Delta\ell(\varepsilon)\) and the dimension is large. In that regime the two budgets differ by the factor \(2^{31}/(2-\rho)\), so gradient descent is optimal among all randomized first-order methods up to this factor. Outside that regime, in particular in low dimension, no matching lower bound is claimed.

## Limitations

- The rate is not new and is not claimed as a contribution on its own.
- The case \(\rho=2\) is covered by this upper bound but not by the companion lower bound, so the pair is tight only for \(\rho<2\), and the gap grows like \(1/(2-\rho)\).
- The oracle is exact. Nothing is claimed for stochastic gradients.

## Scope

The task asked for almost tight upper and lower bounds for an important and popular setup in terms of `Template` and `TemplateLowerBound`. This file is the `Convergence` half of the pair for nonconvex optimization under generalized smoothness; the `NonConvergence` half and the discussion of novelty are in [EllSmoothNonconvexLowerBound](EllSmoothNonconvexLowerBound.md).
