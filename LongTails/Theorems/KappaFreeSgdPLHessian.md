# Condition-number-free statistical rate for constant-step SGD on PL objectives with a Lipschitz Hessian and non-isolated minimizers

The new result is a non-asymptotic oracle-complexity bound for **plain constant-step SGD** with uniform output from a final window. It covers smooth nonconvex objectives that satisfy the Polyak–Łojasiewicz (PL) inequality and whose Hessian is Lipschitz; the minimizer set may be non-isolated (a manifold, or any closed set). The noise is unbiased with variance \(\sigma^2\) and bounded kurtosis \(\mathbb E\|\zeta\|^4\le K\sigma^4\).

Write \(\kappa=L/\mu\). The method returns a point \(\hat x\) with \(\mathbb E f(\hat x)-\min f\le\epsilon\) after

\[
T=\Big\lceil \tfrac{32}{\mu}\Big(16L+14L\kappa^{1/4}+\tfrac{28311552\,K\sqrt\kappa\,L\sigma^2\rho^2}{\mu^4}+\tfrac{64\sigma^2}{\epsilon}\Big)\Big(\log\big(1+\tfrac{6\sqrt\kappa\,\Delta}{\epsilon}\big)+1\Big)+\tfrac{512\sigma^2}{\mu\epsilon}\Big\rceil+1
\]

stochastic gradient calls, i.e.

\[
T=O\!\Big(\Big(\kappa^{5/4}+\frac{K\kappa^{3/2}\sigma^2\rho^2}{\mu^4}+\frac{\sigma^2}{\mu\epsilon}\Big)\log\Big(1+\frac{\sqrt\kappa\,\Delta}{\epsilon}\Big)\Big).
\]

The leading statistical term \(\sigma^2/(\mu\epsilon)\) carries **no factor \(\kappa\)**. Known guarantees for plain SGD under PL have a leading term of \(\kappa\sigma^2/(\mu\epsilon)\). That factor is unavoidable for any method on \(C^{1,1}\) PL functions with bounded variance only, that is, with no Hessian or kurtosis condition (see the comparison below). Every \(\kappa\)- and \(\rho\)-dependent term is \(\epsilon\)-independent up to the logarithm. Here \(K\) is a kurtosis constant, not an iteration count.

## Lean files

- Theorem: [`KappaFreeSgdPLHessian.lean`](KappaFreeSgdPLHessian.lean) (`OracleTemplate.PLHessian.result : Convergence spec budget`).
- Setup: [`../Setups/PLHessianLipschitzKurtosis.lean`](../Setups/PLHessianLipschitzKurtosis.lean).
- Algorithm: [`../Algorithms/WindowSgd.lean`](../Algorithms/WindowSgd.lean).
- Proofs:
  - [`PLHessianHuber`](../Proofs/PLHessianHuber.lean): the Huber ramp \(\psi\) and its calculus.
  - [`PLHessianGeometry`](../Proofs/PLHessianGeometry.lean):
    - quadratic growth from PL, proved through the length of the gradient-descent path and compactness;
    - the aiming inequality, by a second-order Taylor bound along the segment from a minimizer.
  - [`PLHessianStep`](../Proofs/PLHessianStep.lean): the scalar inequality of the one-step analysis in both regions.
  - [`PLHessianExpect`](../Proofs/PLHessianExpect.lean): the one-sample expectation bound for the potential.
  - [`PLHessianRun`](../Proofs/PLHessianRun.lean): the SGD process, conditioning on the past, the geometric bound, and the window sum.
  - [`PLHessianTuning`](../Proofs/PLHessianTuning.lean): the parameter constraints and the final accuracy algebra.
  - [`PLHessianConvergence`](../Proofs/PLHessianConvergence.lean): execution of the algorithm, the uniform output, and assembly.

## Setup

\(E\) is a finite-dimensional real inner-product space and \(f:E\to\mathbb R\). The instance assumptions (`admissible`) are:

1. **Smoothness.** \(\nabla f\) exists everywhere and is \(L\)-Lipschitz.
2. **Lipschitz Hessian.** \(\nabla f\) is differentiable and \(\|\nabla^2 f(x)-\nabla^2 f(y)\|_{op}\le\rho\|x-y\|\).
3. **Global PL with an attained minimum.** There is a global minimizer \(u\) with \(\|\nabla f(x)\|^2\ge2\mu(f(x)-f(u))\) for all \(x\).
   - The minimizer is not assumed unique: the set \(\{f=f(u)\}\) can be a manifold.
   - Quadratic growth is **not** assumed; it is derived in Lean (`quad_growth`, constant \(\mu/16\) in squared distance).
4. **Initial gap.** \(f(x_0)-f(u)\le\Delta\).
5. **Oracle.** One query at \(x\) returns \(g(x,\xi_k)\), where:
   - \(g\) is jointly measurable;
   - the \(\xi_k\) are i.i.d. with law \(P_0\) (`StochasticGeneralizedSmoothAndConvex.IID`);
   - unbiasedness \(\int g(x,\cdot)\,dP_0=\nabla f(x)\), variance \(\int\|g-\nabla f\|^2\le\sigma^2\), and fourth moment \(\int\|g-\nabla f\|^4\le K\sigma^4\) hold uniformly in \(x\).

Valid parameters: \(0<\mu\le L\), \(\rho\ge0\), \(\sigma\ge0\), \(K\ge1\), \(\Delta\ge0\), \(\epsilon>0\).

**Accuracy criterion** (`successful`): the output is measurable and \(\int (f(\hat x)-f(u))\,d\mathbb P\le\epsilon\), under the product of the algorithm's seed law and the oracle law.

**Admissible algorithms** (`allowedAlgorithm`): exactly constant-step SGD \(x_{t+1}=x_t-\eta\,g(x_t,\xi_t)\), with a uniformly random output among \(x_{T_a},\dots,x_{T_a+T_b}\) (`WindowSgd.method η Ta Tb x0`). The proof chooses \(\eta, T_a, T_b\) from the parameters. One oracle call per iteration; the budget is the number of calls.

**Nonlinear instances with curved, non-isolated minimizer sets.** Write \(x\in\mathbb R^{d-1}\), \(y\in\mathbb R\), and set \(f(x,y)=\tfrac12 r(x,y)^2\) with \(r=y-\phi(x)\theta(y)\), where:
- \(\phi(x)=\tfrac12\sin\langle a,x\rangle\);
- \(\theta\) is a smooth bump with \(\theta=1\) on \([-1,1]\), \(\theta=0\) outside \([-3,3]\), and \(|\theta'|\le1\).

Then:
- \(\partial_y r=1-\phi\theta'\ge\tfrac12\), so \(\|\nabla f\|^2\ge r^2(\partial_yr)^2\ge r^2/4=f/2\). Hence PL holds with \(\mu=\tfrac14\), and \(\min f=0\).
- The minimizer set is the curved graph \(\{y=\tfrac12\sin\langle a,x\rangle\}\). It is non-isolated, and its normal direction rotates with \(x\).
- \(\nabla^2f=\nabla r\nabla r^\top+r\nabla^2r\) and \(\nabla^3 f\) involve \(\nabla^2 r,\nabla^3 r\), which vanish outside \(|y|\le3\), where \(r\) is bounded. So \(L\) and \(\rho\) are finite, and of order \(1+\|a\|^3\).
- Additive Gaussian noise \(N(0,\Sigma)\) has \(K\le3\); bounded noise has \(K\le\sup\|\zeta\|^4/\sigma^4\).

The simpler family \(f(x)=h(Ax)\), with \(h(y)=\sum_j(y_j^2+3\sin^2y_j)\) and \(A\) of full row rank \(m<d\), is also admissible: \(8\|A\|^2\)-smooth, \(\sigma_{\min}(A)^2/32\)-PL, with a \(12\|A\|^3\)-Lipschitz Hessian. Its minimizer set, a translate of \(\ker A\), is flat, however, and SGD on it is essentially SGD on \(\mathrm{row}(A)\), where the minimizer is isolated with a positive-definite Hessian, plus a harmless diffusion along \(\ker A\). So it does not exercise the non-isolated case.

Limitation of the class: under global PL, the limit map of the gradient flow is a continuous retraction of \(E\) onto the minimizer set, so the minimizer set is contractible. Compact curved manifolds of minimizers, such as circles, are therefore excluded; only unbounded curved sets like the graph above are possible.

## Proved guarantee and mechanism

Let \(\Phi=f-f(u)\), \(D(x)=\mathrm{dist}(x,\{f=f(u)\})^2\), \(\Phi_0=\big(36864\rho^2/\mu^3+\mu/(24K\sqrt\kappa L\epsilon)\big)^{-1}\), \(\lambda=32\sqrt\kappa/\mu\), and let \(\psi\) be the convex Huber ramp that vanishes on \([0,\Phi_0/4]\), is quadratic on \([\Phi_0/4,\Phi_0/2]\) and has slope 1 beyond.

1. **Quadratic growth** (from PL, via the GD path length): \(\mu D(x)\le16\,\Phi(x)\).
2. **Local aiming.** Let \(p\) be a nearest minimizer.
   - A second-order Taylor bound gives \(\langle\nabla f(x),x-p\rangle\ge2\Phi(x)-3\rho\|x-p\|^3\).
   - Hence \(\langle\nabla f(x),x-p\rangle\ge\Phi(x)\) whenever \(36864\rho^2\Phi(x)\le\mu^3\).
   - This is the mechanism of Liu–Drusvyatskiy–Belkin–Davis–Ma, Thm 2.2.
3. **Potential** \(W=D+\lambda\psi(\Phi)\). With one SGD step of size \(\eta\) and the constraints in `Tune`:
   \[\mathbb E[W(x_{+})\mid x]\le(1-\tfrac{\mu\eta}{32})W(x)-\tfrac\eta2\Phi(x)+2\eta^2\sigma^2.\]
   - **Near the minimizer set** (\(\Phi\le\Phi_0\)), aiming makes the distance part behave like strongly convex SGD. The noise enters only as \(\eta^2\sigma^2\), with no \(L\eta^2\sigma^2/\mu\) penalty.
   - **Far away**, the distance can grow by \(O(\sqrt\kappa\,\eta\Phi)\). The PL descent of the slope-1 part of \(\lambda\psi\) pays for it.
   - The descent is split into a deterministic part \(-\tfrac\eta2\|\nabla f\|^2\) and a noise part \(N\); this keeps the deterministic term at \(\kappa^{5/4}\).
   - The curvature of \(\psi\) costs \(\mathbb E N^2/\Phi_0\). This is where the bounded fourth moment is used.
   - No high-probability containment argument is needed.
4. **Output.** Iterating gives \(\mathbb E W_t\le(1-\mu\eta/32)^tW_0+64\eta\sigma^2/\mu\). Summing over the final window bounds the average \(\mathbb E\Phi\), which is the expectation for the uniformly sampled output.

## Comparison with the closest results

| Result | Assumptions | Oracle / output | Complexity for \(\mathbb E f-f^\*\le\epsilon\) |
|---|---|---|---|
| SGD under PL: Karimi–Nutini–Schmidt (ECML-PKDD 2016); Khaled–Richtárik ([arXiv 2002.03329](https://arxiv.org/abs/2002.03329), Cor. 1-type); Gower et al. (AISTATS 2021) | \(L\)-smooth, PL, bounded variance | one query/sample; last iterate | \(O(\kappa\log(\Delta/\epsilon)+\kappa\sigma^2/(\mu\epsilon))\) |
| Lower bound, Masiha–Kiyavash–Thiran ([arXiv 2606.28278](https://arxiv.org/abs/2606.28278) v3, Thm 4.3) | globally PL, \(C^{1,1}\), bounded variance | any stochastic first-order method | \(\Omega(\kappa\sigma^2/(\mu\epsilon))\) |
| Strongly convex lower bound (e.g. quadratics) | strongly convex | any | \(\Omega(\sigma^2/(\mu\epsilon))\) |
| **This result** | PL, \(L\)-smooth, \(\rho\)-Lipschitz Hessian, kurtosis \(K\) | one query/sample; uniform window output | \(O\big((\kappa^{5/4}+K\kappa^{3/2}\sigma^2\rho^2/\mu^4+\sigma^2/(\mu\epsilon))\log(1+\sqrt\kappa\Delta/\epsilon)\big)\) |

- **Relation to the lower bound.** Masiha et al. note (Remark 4.6) that their hard instances are only piecewise \(C^1\) and do not claim optimality for the Hessian-Lipschitz class. Their hard oracle multiplies the gradient by \(z/q\) with \(z\sim\mathrm{Bernoulli}(q)\), so its kurtosis is \(\asymp1/q\), which is unbounded.
  - The hard instance therefore lies outside the present class for **two** reasons: Hessian regularity and kurtosis.
  - This result does **not** prove that a Lipschitz Hessian alone, or bounded kurtosis alone, removes the \(\kappa\) factor. Whether either suffices alone is open.
  - The present proof needs both. The Hessian bound is used for aiming; the kurtosis is used to control rare large jumps of \(f\) into the region where the PL-based term is active, which otherwise cost about \(\kappa^{3/2}\eta^2\sigma^2\) per step.
  - A clipped variant that would avoid the fourth moment fails in our expectation argument because of a sublinear far-field phase. This is a limitation of the proof, not evidence that the moment is necessary.
- **Improvement regime.**
  - Up to the logarithm, the bound improves on the SGD bound \(\kappa\sigma^2/(\mu\epsilon)\) by a factor \(\kappa/\log(1+\sqrt\kappa\Delta/\epsilon)\).
  - This holds once \(\sigma^2/(\mu\epsilon)\) dominates the \(\epsilon\)-independent terms, i.e. for \(\epsilon\lesssim\min\{\sigma^2\kappa^{-1/4}/\mu,\ \mu^3/(K\sqrt\kappa\,\rho^2)\}\). The second condition says that \(\epsilon\) lies well inside the aiming region (\(\epsilon\lesssim\Phi_0/\sqrt\kappa\)).
  - For larger \(\epsilon\), or when \(\kappa\lesssim\log(1/\epsilon)\), the classical bound can be smaller.
  - The deterministic term \(\kappa^{5/4}\log\) is worse than gradient descent's \(\kappa\log\).
- **Isolated minimizers.** Gadat–Panloup ([arXiv 1709.03342](https://arxiv.org/abs/1709.03342), Thm 2) already give a \(\kappa\)-free leading term for Ruppert–Polyak averaging without convexity, with an asymptotically optimal mean-squared error \(\mathrm{Tr}(H^{-1}\Sigma H^{-1})/n\).
  - Their setting has a unique minimizer with a positive-definite Hessian, together with noise-covariance and \(L^p\) conditions.
  - The higher-order constants are not explicit.
  - The present result is new only for **non-isolated** minimizer sets, with explicit non-asymptotic constants, a global start, and the function-gap criterion.
- **Aiming and interpolation.** Liu, Drusvyatskiy, Belkin, Davis and Ma ([arXiv 2306.02601](https://arxiv.org/abs/2306.02601), Thm 2.2) prove local aiming under quadratic growth and a Lipschitz Hessian, the same mechanism as step 2.
  - Their SGD guarantees are for **interpolation** (\(\sigma=0\) at the solution set) and are local, on a ball, with escape probabilities.
  - Here \(\sigma>0\), the start is global, and excursions are handled in expectation by the Huber-weighted function-value term.
- **Distance-based SGD under global aiming.** SGD analyses through the squared distance are known under *global* strong-aiming-type conditions: strongly quasar-convex functions (Gower–Sebbouh–Loizou, AISTATS 2021, "SGD for structured nonconvex functions"; Hinder–Sidford–Sohoni, COLT 2020, for quasar-convex acceleration). Step 3 near the minimizer set is of this type. The contribution here is twofold:
  - aiming is obtained only **locally**, from PL plus a Lipschitz Hessian (Liu et al. Thm 2.2);
  - the local regime is glued **globally and in expectation**, with \(\sigma>0\), through the Huber-weighted function-value term.
  A clipped variant aimed at removing the fourth moment fails exactly at this gluing step, because of the sublinear far-field phase.
- **Local and asymptotic analyses.**
  - Fehrman–Gess–Jentzen ([arXiv 1904.01517](https://arxiv.org/abs/1904.01517), Thm 1.1/5.12) give local rates on manifolds of minima. Their bounds have a basin-failure probability and unspecified constants, and contain no \(\kappa\)-explicit statistical term.
  - Dereich–Kassing (JMLR 2024 and their CLT papers) give asymptotic or almost-sure results on manifolds of minimizers. We did not read their full texts.
- **In this repository.** [`HeavyTailedPLLastIterate`](HeavyTailedPLLastIterate.md) proves a high-probability last-iterate bound for SGD under PL with leading term \(\sigma^2(\kappa+\log(1/\delta))/(\mu\epsilon)\), without Hessian or kurtosis assumptions.

## Limitations

- **Three conditions are needed together:** PL, a Lipschitz Hessian, and uniformly bounded kurtosis. Global PL with a Lipschitz Hessian is restrictive for deep networks. The fourth-moment bound must hold uniformly in \(x\), which excludes noise that grows with \(\|x\|\).
- **Logarithm.** The leading term carries \(\log(1+\sqrt\kappa\Delta/\epsilon)\), which comes from constant steps followed by window averaging. A decreasing-step version could remove it; this was not attempted.
- **Constants.** They are large (\(28311552=768\cdot36864\)), and the \(\epsilon\)-independent terms \(\kappa^{5/4}\log\) and \(K\kappa^{3/2}\sigma^2\rho^2/\mu^4\cdot\log\) are not shown to be necessary.
- **Inputs.** The method must know \(L,\mu,\rho,\sigma,K,\Delta,\epsilon\) to choose \(\eta,T_a,T_b\). The output is a random iterate from the final window, not the last iterate.
- **Dimension.** \(E\) is finite-dimensional (nearest minimizers and compactness are used); the bounds themselves are dimension-free.
- **Literature search.** Searches covered arXiv and Google-indexed sources up to October 2026 for SGD + PL + Hessian / manifold of minima / aiming / Ruppert–Polyak. We found no non-asymptotic \(\kappa\)-free function-gap bound for non-isolated minimizers with \(\sigma>0\). This is evidence, not proof, of priority.
