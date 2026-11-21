# Cubic-regularized Newton on Polyak–Łojasiewicz functions: explicit upper bound

The [upper theorem](HessianLipschitzPLCubicNewton.lean) is the companion of the [lower theorem](HessianLipschitzPLLowerBound.lean). It formalizes, with explicit constants and exact oracle accounting, the complexity of cubic-regularized Newton on Polyak–Łojasiewicz (PŁ) functions with Lipschitz Hessian. The rate is due to Nesterov and Polyak (2006); it is not claimed as a new result. Its role is to make the pair with the new lower bound precise inside one oracle model.

## Setup

The [specification](../Setups/HessianLipschitzPL.lean) covers an arbitrary finite-dimensional real inner-product space \(E\) and any \(f:E\to\mathbb R\) with

* a gradient everywhere, a differentiable gradient, and an \(H\)-Lipschitz Hessian in operator norm;
* an attained minimum \(f_\star\) with \(f(x_0)-f_\star\le\Delta\);
* the global PŁ inequality \(2\mu(f(x)-f_\star)\le\|\nabla f(x)\|^2\).

No convexity and no gradient-Lipschitz constant are assumed. `valid` only asks \(H,\mu,\varepsilon>0\) and \(\Delta\ge0\). One oracle call returns \((f(x),\nabla f(x),\nabla^2f(x))\). The public input given to the algorithm consists of the space, \(H\) and \(x_0\) only: \(\mu\), \(\Delta\) and \(\varepsilon\) enter the budget but not the updates. Success is \(\mathbb E[f(X)]-f_\star\le\varepsilon\) for the measurable output \(X\); the method is deterministic, so the guarantee holds surely.

## Algorithm and guarantee

The [algorithm](../Algorithms/CubicNewtonPL.lean) is cubic-regularized Newton with the fixed constant \(H\):

\[
x_{k+1}=x_k+\operatorname*{arg\,min}_{s}\Big\{\langle\nabla f(x_k),s\rangle+\tfrac12\langle s,\nabla^2f(x_k)s\rangle+\tfrac H3\|s\|^3\Big\},
\]

one oracle call per iteration, output the last iterate. The global minimizer of the cubic model is taken as a primitive: internal linear algebra is free in the oracle model. The method does not use function values.

With \(\vartheta=H^2\Delta/\mu^3\), the public budget is

\[
K=\Big\lceil 53\,\vartheta^{1/4}+5\log\!\big(1+\log(1+\mu^3/(H^2\varepsilon))\big)+4\Big\rceil ,
\]

and \(f(x_K)-f_\star\le\varepsilon\). The first term is the global phase, the second the superlinear local phase.

## Proof

[`CubicNewtonPLDescent`](../Proofs/CubicNewtonPLDescent.lean) gives the two standard one-step facts for a step \(s\) of length \(r\): \(f(x+s)\le f(x)-\frac H3r^3\) and \(\|\nabla f(x+s)\|\le\frac{3H}2r^2\). They follow from the Taylor bounds for an \(H\)-Lipschitz Hessian and from the first- and second-order optimality conditions of the global model minimizer (existing repository lemmas). With the PŁ inequality at the new point, the normalized gap \(u_k=(f(x_k)-f_\star)/\omega\), \(\omega=512\mu^3/(59049H^2)\), and the normalized step \(\rho_k=r_k\cdot27H/(8\mu)\) satisfy

\[
u_{k+1}\le\rho_k^4,\qquad u_{k+1}+\rho_k^3\le u_k .
\]

[`CubicNewtonPLRecursion`](../Proofs/CubicNewtonPLRecursion.lean) analyses this recursion without fractional powers.

* *Global phase.* If \(u_k\le T^4\) with \(T\ge9/16\) then \(u_{k+1}\le(T-1/16)^4\); otherwise \(\rho_k>T-1/16\ge1/2\) and \((T-\frac1{16})^4+(T-\frac1{16})^3\ge T^4\) contradicts the second inequality. Hence the fourth root of the gap decreases by \(1/16\) per step until \(u\le1/16\): at most \(16\,u_0^{1/4}+1\) steps, and \(u_0^{1/4}\le3.3\,\vartheta^{1/4}\).
* *Local phase.* If \(u_k\le c^{27}\) with \(c\le1\), three steps give \(u_{k+3}\le c^{64}\le(c^2)^{27}\), since \(u\le a^3\) forces \(\rho\le a\) and \(u'\le a^4\). Starting from \(u\le1/16\le0.91^{27}\), after \(3j\) steps \(u\le(0.91^{27})^{2^j}\le e^{-2^j}\). Choosing \(2^j\ge1+\log(1+\mu^3/(H^2\varepsilon))\) gives \(f(x_K)-f_\star\le\varepsilon\).

[`CubicNewtonPLConvergence`](../Proofs/CubicNewtonPLConvergence.lean) connects the recursion to the actual execution of the algorithm under the template (every oracle call is counted; the bound holds for every larger budget because the gap is nonincreasing) and proves that the simplified public budget suffices.

## Relation to the literature

[Nesterov and Polyak, Math. Program. 108 (2006)](https://doi.org/10.1007/s10107-006-0706-8), Theorem 7, covers this class ("gradient dominated functions of degree two", with \(\tau_f=1/(2\mu)\)). Its statement gives a linear rate \(e^{-k\sigma}\) with \(\sigma=\tilde\omega^{1/4}/(\tilde\omega^{1/4}+(f(x_0)-f_\star)^{1/4})\) in the first phase and the order-\(4/3\) rate in the second, i.e. \(O(\vartheta^{1/4}\log\vartheta+\log\log)\) when read literally. The logarithm-free first phase proved here uses only the one-step inequality from their proof (their (4.17) in normalized form) and is a refinement of the bookkeeping, not a new method or rate. We are not aware of an earlier explicit statement of the count \(O(\vartheta^{1/4}+\log\log(\mu^3/(H^2\varepsilon)))\), but it is an immediate consequence of their argument and we do not claim it as a contribution. Asymptotic and local analyses under Kurdyka–Łojasiewicz and error-bound conditions are in [Zhou–Wang–Liang (NeurIPS 2018)](https://arxiv.org/abs/1808.07382) and [Yue–Zhou–So (SIAM J. Optim. 2019)](https://arxiv.org/abs/1801.09387).

What the pair adds is the [lower bound](HessianLipschitzPLLowerBound.md): \(\lfloor\vartheta^{1/4}/2^{39}\rfloor\) queries are necessary for every randomized algorithm when \(\vartheta\ge2^{160}\), \(\varepsilon\le\Delta/32\) and \(d\ge\vartheta\). Thus the global phase of cubic Newton is optimal up to a universal constant; the additive doubly-logarithmic term is not matched by the lower bound.

## Limitations

* The cubic subproblem is solved exactly; inexact subproblem solutions, Hessian-vector implementations and arithmetic cost are not analysed.
* The method needs \(H\). Adaptive estimation of \(H\) is standard for cubic regularization but not formalized here.
* The constants 53, 5 and 4 are convenient, not optimized.
* Tightness is with respect to the lower theorem's regime only; see its note for the exact statement.
