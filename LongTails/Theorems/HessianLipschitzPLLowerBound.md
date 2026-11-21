# Second-order oracle complexity of Polyak–Łojasiewicz functions: lower bound

The [lower theorem](HessianLipschitzPLLowerBound.lean) and its [upper counterpart](HessianLipschitzPLCubicNewton.lean) determine, up to universal constants and one additive doubly-logarithmic term, how many value–gradient–Hessian queries are needed to minimize a Polyak–Łojasiewicz (PŁ) function with Lipschitz Hessian. With

\[
\vartheta=\frac{H^2\Delta}{\mu^3},
\]

the answer is of order \(\vartheta^{1/4}=\sqrt H\,\Delta^{1/4}\mu^{-3/4}\). The new mathematical claim is the lower bound: no algorithm, randomized or not, improves the global phase of cubic-regularized Newton on this class. The upper theorem formalizes a known rate with explicit constants and is not claimed as new.

## Problem and precise statements

The general [setup](../Setups/HessianLipschitzPL.lean) takes any finite-dimensional real inner-product space \(E\) and a function \(f:E\to\mathbb R\) such that

* \(f\) has a gradient everywhere, the gradient is differentiable, and the Hessian is \(H\)-Lipschitz in operator norm: \(\|\nabla^2f(x)-\nabla^2f(y)\|\le H\|x-y\|\);
* \(f\) attains its minimum \(f_\star\) and \(f(x_0)-f_\star\le\Delta\);
* the global PŁ inequality \(2\mu(f(x)-f_\star)\le\|\nabla f(x)\|^2\) holds for every \(x\).

There is no convexity assumption and no bound on the gradient-Lipschitz constant. This is the class of "gradient dominated functions of degree two" of Nesterov and Polyak (Definition 3 with \(p=2\) and \(\tau_f=1/(2\mu)\)), with the conditions imposed globally. One oracle call at a point \(x\) returns \((f(x),\nabla f(x),\nabla^2f(x))\). Success means a measurable output \(X\) with integrable gap and \(\mathbb E[f(X)]-f_\star\le\varepsilon\). `allowedAlgorithm` imposes no restriction.

The lower bound is stated on the [high-dimensional restriction](../Setups/HighDimensionalHessianLipschitzPL.lean): \(E=\mathbb R^d\), \(x_0=0\), and `valid` requires

\[
H,\mu,\varepsilon>0,\qquad 32\varepsilon\le\Delta,\qquad \vartheta\ge2^{160},\qquad d\ge\vartheta .
\]

Its admissibility and success predicates are literally those of the general setup; [`HessianLipschitzPLInclusion`](../Proofs/HessianLipschitzPLInclusion.lean) records the inclusion and transfers the upper bound to the restricted setup.

**Lower bound (new).** For every valid parameter choice, every algorithm (arbitrary internal randomness, adaptive queries, arbitrary output rule) and every budget

\[
0\le b\le\Big\lfloor\frac{\vartheta^{1/4}}{2^{39}}\Big\rfloor ,
\]

there is an admissible objective, depending on the algorithm and on \(b\) but not on its random seed, on which the algorithm fails the expected-accuracy criterion after \(b\) queries. On the valid set the budget is at least \(2\) (`limit_large`), and the valid set is nonempty (`valid_nonempty`).

**Upper bound (known rate, formalized).** Cubic-regularized Newton with regularization constant \(H\) reaches \(f(x_K)-f_\star\le\varepsilon\) deterministically after

\[
K=\Big\lceil 53\,\vartheta^{1/4}+5\log\!\big(1+\log(1+\mu^3/(H^2\varepsilon))\big)+4\Big\rceil
\]

queries, for every \(H,\mu,\varepsilon>0\), \(\Delta\ge0\), every dimension and every starting point.

**Tightness, stated exactly.** Writing \(\mathrm{LB}\) for the lower budget and \(\ell\ell=\log(1+\log(1+\mu^3/(H^2\varepsilon)))\),

\[
\mathrm{UB}\le 53\cdot2^{39}\,(\mathrm{LB}+1)+5\,\ell\ell+5 .
\]

The pair is tight up to the universal factor whenever \(\vartheta^{1/4}\gtrsim\max\{1,\ell\ell\}\), i.e. in the regime where the global phase dominates. The lower bound does not contain the doubly-logarithmic term, is vacuous for \(\vartheta<2^{160}\), requires \(\varepsilon\le\Delta/32\) and dimension \(d\ge\vartheta\). These are limitations of the present construction; the upper bound needs none of them. We do not call the bounds matching.

## How the result meets the stated research requirements

* *Upper and lower bound for one question.* Both theorems concern the same class, oracle and accuracy criterion; the upper bound holds on the general setup and is transferred to the restricted one by an inclusion lemma.
* *Standard, popular setup.* The PŁ / gradient-domination class with Lipschitz Hessian is the setting of Nesterov–Polyak's Section 4.2 and of later work on cubic regularization under Łojasiewicz conditions; all assumptions are taken from that literature and none is added.
* *What is closed.* The global (polynomial) part of the second-order complexity is determined up to constants. The local doubly-logarithmic part is not; see below.

## What is known, and what changes

**Upper bounds.** [Nesterov and Polyak, *Cubic regularization of Newton method and its global performance*, Math. Program. 108 (2006)](https://doi.org/10.1007/s10107-006-0706-8), Theorem 7, treats exactly this class. As stated there, the first phase is a linear rate \(f(x_k)-f_\star\le(f(x_0)-f_\star)e^{-k\sigma}\) with \(\sigma=\tilde\omega^{1/4}/(\tilde\omega^{1/4}+(f(x_0)-f_\star)^{1/4})\), \(\tilde\omega\asymp\mu^3/H^2\), followed by the superlinear phase \(f(x_{k+1})-f_\star\le\tilde\omega((f(x_k)-f_\star)/\tilde\omega)^{4/3}\). Read literally this gives \(O(\vartheta^{1/4}\log\vartheta)\) iterations for the first phase. The logarithm-free count \(O(\vartheta^{1/4})\) follows from the one-step inequality in their proof, \(\delta_k\ge\delta_{k+1}+\delta_{k+1}^{3/4}\) in normalized units, because it makes \(\delta^{1/4}\) decrease by a constant per step while \(\delta\gtrsim1\). The upper theorem formalizes this refinement; it is a short consequence of their argument and not a new rate. Related upper bounds: [Zhou, Wang and Liang, NeurIPS 2018](https://arxiv.org/abs/1808.07382) (asymptotic rates under the KŁ property), [Yue, Zhou and So, SIAM J. Optim. 2019](https://arxiv.org/abs/1801.09387) (local quadratic convergence under an error bound), and stochastic variants such as [Masiha et al., NeurIPS 2022](https://arxiv.org/abs/2205.12856). None contains a lower bound.

**Lower bounds.** We found no lower bound for second-order (or higher-order) methods on a PŁ, gradient-dominated or KŁ class. The neighbouring results are:

* First-order PŁ: \(\Omega(\kappa\log(1/\varepsilon))\) for deterministic methods, [Yue, Fang and Lin, COLT 2023](https://arxiv.org/abs/2212.13551); randomized versions in [Ou and Wang, arXiv:2609.03990](https://arxiv.org/abs/2609.03990) and [Masiha, Kiyavash and Thiran, arXiv:2606.28278](https://arxiv.org/abs/2606.28278) (preprints). They need a gradient-Lipschitz constant and a first-order oracle and say nothing once Hessians are available.
* Second-order convex: [Arjevani, Shamir and Shiff, Math. Program. 2019](https://arxiv.org/abs/1705.07260), Theorem 1, gives for \(\lambda\)-strongly convex functions a bound of the form \(\min\{\sqrt{\mu_1/\lambda},(\mu_2D/\lambda)^{2/7}\}+\log\log(\lambda^3/(\mu_2^2\varepsilon))\) for deterministic algorithms, in terms of the initial distance \(D\) and with a finite gradient-Lipschitz constant \(\mu_1\).
* Second-order nonconvex stationarity: [Carmon, Duchi, Hinder and Sidford, arXiv:1710.11606](https://arxiv.org/abs/1710.11606), \(\Omega(\Delta\sqrt H\,\varepsilon_g^{-3/2})\) for finding \(\|\nabla f\|\le\varepsilon_g\).

**Relation to the stationarity bound.** The number \(\vartheta^{1/4}\) is Carmon et al.'s rate evaluated at \(\varepsilon_g^2\asymp\mu\Delta\), the gradient scale that the PŁ inequality attaches to a gap of order \(\Delta\). The lower bound is nevertheless not a corollary of theirs: their hard function is not PŁ, so it is not a member of the class, and a gap guarantee on a PŁ function does not reduce to their stationarity problem on a non-PŁ function. The repository's [PointwiseHessianStationarityLowerBound](PointwiseHessianStationarityLowerBound.lean) uses the same chain for a gradient-norm criterion; converting between gap and gradient through the instance's smoothness would lose a factor of order the square root of the chain length. What is needed, and proved here, is that the hard chain itself is globally PŁ with the right constant, and that unfinished points have a large function gap.

**Comparison with the strongly convex subclass.** A \(\mu\)-strongly convex function is PŁ with the same constant and \(D^2\le2\Delta/\mu\). On that subclass accelerated second-order methods with restarts have complexity \(\tilde O((HD/\mu)^{2/7})\le\tilde O(\vartheta^{1/7})\) plus the local term (Monteiro–Svaiter acceleration; optimal versions in [Kovalev–Gasnikov](https://arxiv.org/abs/2205.09647) and [Carmon et al.](https://arxiv.org/abs/2205.15371)); we quote this only as an upper bound on the subclass and have not re-derived its logarithmic factors. Against it, the PŁ class requires \(\Omega(\vartheta^{1/4})\). So second-order acceleration is impossible under PŁ alone, the second-order counterpart of the first-order gap between \(\sqrt\kappa\) and \(\kappa\) established by Yue, Fang and Lin.

**The doubly-logarithmic term.** The upper bound contains \(\log\log(\mu^3/(H^2\varepsilon))\) from the superlinear phase; the lower bound does not. A term of this type is known to be necessary for deterministic second-order methods on strongly convex functions in the distance parametrization (Arjevani–Shamir–Shiff, Theorem 1; classical results of Nemirovski and Yudin). Its necessity for randomized algorithms, or for the present \(\Delta\)-parametrized class without a gradient-Lipschitz bound, is not established here and we do not claim it.

**Consistency with first-order bounds.** The hard instances have a bounded gradient-Lipschitz constant \(L_1\) with \(L_1/\mu\asymp\vartheta^{1/4}\), so on them the first-order bound \(\kappa\log(1/\varepsilon)\) and the second-order bound agree in the polynomial part; the theorem shows that Hessian access cannot improve this polynomial part, only the dependence on \(\varepsilon\).

## Construction and proof mechanism

*Hard function.* For \(N=m+1\) hidden coordinates \(y_j=x_{\pi(j)}\) the unit instance is

\[
F(x)=\chi\!\big(\|x\|^2/R^2\big)\Big[-\Phi(y_0)+\sum_{j\ge1}\big(g(-y_{j-1})\Phi(-y_j)-g(y_{j-1})\Phi(y_j)\big)\Big]+\frac a2\|x\|^2 ,
\]

with \(\Phi(t)=\pi/2+\arctan t\), a monotone \(C^3\) gate \(g\) that is \(0\) below \(1/10\) and \(1\) above \(1/5\), \(a=3\sqrt3/4\), a radial cutoff \(\chi\) and \(R=2^{60}N\). This is the repository's existing quadratically guarded chain [`RelativeHessianLocalized.value`](../Proofs/RelativeHessianLocalized.lean), built for a different class (gradient-dependent third derivatives, gradient-norm criterion). Its \(C^3\) regularity, the bound \(\|D^3F\|\le2^{56}\) and the oracle-hiding argument are reused.

*New lemma: the chain is globally PŁ.* [`HessianPLChain`](../Proofs/HessianPLChain.lean) and [`HessianPLLocalized`](../Proofs/HessianPLLocalized.lean) prove, for every \(x\in\mathbb R^d\),

\[
F(x)-F_\star\le 2^{9}N\,\|\nabla F(x)\|^2,\qquad F_\star=N\,h(b),\quad h(t)=\tfrac a2t^2-\Phi(t),\quad b=1/\sqrt3 ,
\]

with \(F_\star\) attained at \(y\equiv b\). The proof has four ingredients.

1. *Bracket decomposition.* \(F-F_\star\) (inside the cutoff radius) is \(\frac a2\) times the squared norm of the component of \(x\) orthogonal to the chain, plus one nonnegative bracket per coordinate, \(\frac a2y_j^2+\mathrm{link}(y_{j-1},y_j)-h(b)\). Nonnegativity uses the one-signed coupling: \(\mathrm{link}(s,t)\ge-\Phi(t)\) and \(h\ge h(b)\).
2. *Saturated points.* If every \(y_j>1/5\), all gates are constant, the gradient coordinate is \(h'(y_j)\), and \(h(t)-h(b)\le\frac12h'(t)^2\) for \(t\ge0\) because \(h''\ge a\ge1\) there.
3. *Unsaturated points.* If some coordinate is at most \(1/5\), the gradient norm is at least \(1/5\): either the first coordinate of small magnitude has gradient component \(\le-7/10\) (existing `first_small`), or a negative coordinate has gradient component \(\le a\,y_j\). Each bracket is at most \(y_j^2+8\), and \(y_j^2\le2g_j^2+8\) where \(g_j\) is the \(j\)-th gradient coordinate: for \(|y_j|\ge1/5\) the non-quadratic part of \(g_j\) lies in \([-2,0]\) because the outgoing gate derivative vanishes, and for \(|y_j|<1/5\) the bound is trivial. Summing, \(F-F_\star\le2\|\nabla F\|^2+16N\), and \(16N\le400N\|\nabla F\|^2\).
4. *Outside the cutoff radius* the quadratic guard dominates: \(\|\nabla F\|\ge\|x\|/2\) and \(F-F_\star\le\|x\|^2\).

The PŁ constant degrades like \(1/N\), which is exactly what a chain of length \(N\) must exhibit: by PŁ and smoothness an optimal method contracts the gap at a rate governed by the condition number, here of order \(N\).

*Gap at unfinished points.* If all coordinates with index \(>r\) have magnitude at most \(1/10\), the brackets with index \(\ge r+2\) have closed gates and are at least \(-h(b)\ge1\), so \(F-F_\star\ge N-r-2\) (`value_unfinished`). This holds for arbitrary such points, also outside the cutoff radius.

*Scaling.* \(f(x)=A\,F(\beta x)\) has Hessian-Lipschitz constant \(\le2^{56}A\beta^3\), PŁ constant \(\ge A\beta^2/(2^{10}N)\) and initial gap \(\le4AN\). With \(A=\Delta/(4N)\) and \(\beta^2=2^{12}N^2\mu/\Delta\) the class constraints reduce to \(2^{144}N^4\le\vartheta\). The proof takes \(N=2b+3\).

*Randomized algorithms.* The chain coordinates are a uniformly random injection \(\pi\) into \(\{1,\dots,d\}\). A value–gradient–Hessian reply at a point whose undiscovered coordinates are below \(1/20\) depends on \(\pi\) only through one more coordinate than already discovered, because the gate and its first three derivatives vanish below \(1/10\). A counting argument over injections (existing `RelativeHessianExposure`) shows that for at most a quarter of the injections some query or the output has a large undiscovered coordinate; this is where \(d\ge\vartheta\) is used. For the remaining injections the output after \(b\) queries has gap at least \(A(b+1)\ge\Delta/12\). Averaging gives an injection with expected gap \(>\varepsilon\) whenever \(32\varepsilon\le\Delta\); [`HessianPLHardness`](../Proofs/HessianPLHardness.lean) assembles the statement, including the integrability clause of the success criterion.

## Limitations

* The universal constants (\(2^{39}\) in the budget, \(2^{160}\) in the validity threshold) and the dimension requirement \(d\ge\vartheta\) are large. They come from the reused bounds \(\|D^3F\|\le2^{56}\) and \(R=2^{60}N\), which were chosen for transparent formal estimates; no numerical relevance is claimed.
* The lower bound misses the additive \(\log\log\) term and covers \(\varepsilon\le\Delta/32\) only.
* The starting point of the restricted setup is \(x_0=0\); the class is translation invariant.
* The oracle is exact. Stochastic or inexact second-order oracles, an additional gradient-Lipschitz constraint as a separate parameter, higher-order oracles (expected rate \(H_p^{1/p}\Delta^{(p-1)/(2p)}\mu^{-(p+1)/(2p)}\)), and the sublevel \(\alpha\)-PŁ classes with \(\alpha<2\) are not treated.

## Literature search record

Searches on 2026-11-21 (arXiv API, all years; OpenReview search including ICLR 2027 submissions; web search): "lower bound" combined with Polyak / Łojasiewicz / gradient dominated / Kurdyka / error bound and with second-order / cubic / Newton / Hessian / higher-order / tensor. No lower bound for this class was found. The independent Reviewer repeated the search with the same outcome. Keyword search is evidence, not proof, of absence; the Cartis–Gould–Toint monograph and the full text of some ICLR 2027 submissions were not accessible.
