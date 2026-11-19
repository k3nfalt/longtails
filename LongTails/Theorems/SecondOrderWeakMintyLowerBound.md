# Second-order weak-Minty variational inequalities: a randomized lower bound

## Result

Lean: theorem [`SecondOrderWeakMintyLowerBound.lean`](SecondOrderWeakMintyLowerBound.lean)
(`LongTails.Theorems.SecondOrderWeakMintyLowerBound.result`, a `NonConvergence` statement); setup
[`../Setups/HighDimensionalWeakMintySecondOrder.lean`](../Setups/HighDimensionalWeakMintySecondOrder.lean);
hard instance and proof in
[`SecondOrderMintyChain`](../Proofs/SecondOrderMintyChain.lean) (scalar profiles, chain, derivative),
[`SecondOrderMintyChainBounds`](../Proofs/SecondOrderMintyChainBounds.lean) (operator-norm, Minty, floor and
prefix lemmas),
[`SecondOrderMintyInstance`](../Proofs/SecondOrderMintyInstance.lean) (smooth wall),
[`SecondOrderMintyHiding`](../Proofs/SecondOrderMintyHiding.lean) (simulation, counting, averaging) and
[`SecondOrderMintyLowerBound`](../Proofs/SecondOrderMintyLowerBound.lean) (parameters, translated oracle,
admissibility, budget arithmetic, and the restriction to the general setup).
The companion upper bound is [`SecondOrderWeakMintyUpperBound`](SecondOrderWeakMintyUpperBound.md).

Write

$$
M=\min\Big\{\frac{L_2R^2}{\varepsilon},\ \frac{L_1^2R^2}{\varepsilon^2}\Big\}.
$$

For every valid parameter choice, every randomized adaptive algorithm that uses at most
$\lfloor M/2^{15}\rfloor$ oracle calls (value and Jacobian calls counted together, any budget
$b\le\lfloor M/2^{15}\rfloor$, including $b=0$) fails on some admissible operator: its output
satisfies $\mathbb E\|F(\hat x)\|>\varepsilon$ (or the residual is not integrable). Together with the
upper bound $\lceil 2^{27}(1+M)\rceil$ of the companion theorem, the oracle complexity of this class is

$$
\Theta\Big(\min\Big\{\frac{L_2R^2}{\varepsilon},\ \frac{L_1^2R^2}{\varepsilon^2}\Big\}\Big)
$$

up to a universal constant (no logarithms), in the stated regime $0\le\rho\le1/L_1$,
$M\ge2^{15}$ and $d\ge M^3$.

## Problem class and oracle

The setup is the standard second-order weak-Minty class, identical to the repository's
[`WeakMintySecondOrder`](../Setups/WeakMintySecondOrder.lean) setup restricted to
$E=\mathbb R^d$, to $\rho L_1\le1$ and to an expected-residual criterion:

- $F:\mathbb R^d\to\mathbb R^d$ is differentiable with derivative $J$; $\|F(x)-F(y)\|\le L_1\|x-y\|$ and
  $\|J(x)-J(y)\|\le L_2\|x-y\|$ (first- and second-order smoothness, Lin–Jordan Perseus Assumption 2.3 with
  $p=1,2$; Vyas–Bullins arXiv 2304.08389 Assumptions 1–2);
- weak Minty: some zero $x^\star$ with $\|x_0-x^\star\|\le R$ satisfies
  $\langle F(x),x-x^\star\rangle\ge-\frac\rho2\|F(x)\|^2$ for all $x$, $0\le\rho\le1/L_1$
  (Diakonikolas–Daskalakis–Jordan, AISTATS 2021; $\rho=0$ is the Minty condition, Perseus Definition 2.5);
- one call returns either $F(x)$ or $J(x)$ (exact, as in the upper bound); queries may be anywhere;
- success: $\|F(\text{output})\|$ is integrable and its expectation under the algorithm's seed law is at
  most $\varepsilon$. The parameters $L_1,L_2,\rho,R,\varepsilon,x_0,d$ are all public, so the bound also holds
  against algorithms that know $R$.

`valid` requires $0<L_1$, $0<L_2$, $0\le\rho\le1/L_1$, $0<R$, $0<\varepsilon$, $2^{15}\le M$ and
$M^3\le d$. The regime is nonempty, e.g. $L_1=L_2=R=1$, $\varepsilon=2^{-16}$ gives
$M=\min(2^{16},2^{32})=2^{16}$, and $d=2^{48}$.

## Hard instance

All instances are Minty ($\rho=0$), hence admissible for every $\rho\ge0$. Fix $m=\lfloor M/2^{14}\rfloor$,
$n=m-1$, $r=R/\sqrt m$, $\kappa=8\varepsilon/r$, $b=8R$, and a random injection
$\pi:\{0,\dots,n\}\to\{1,\dots,d\}$. With $z_i=x_{\pi(i)}$,

$$
G_{\pi(0)}(x)=\kappa r\,\mathrm{sat}(z_0/r-1),\qquad
G_{\pi(j+1)}(x)=\kappa r\,\mathrm{gate}(z_j/r)\,\mathrm{sat}(z_{j+1}/r-1),
$$

and all other components vanish. Here $\mathrm{step}(u)=\mathrm{ramp}(u)-\mathrm{ramp}(u-1)$ is a
$C^{1,1}$ smoothstep from 0 (for $u\le0$) to 1 (for $u\ge2$), $\mathrm{gate}(t)=\mathrm{step}(8t-2)$ is
exactly flat (value and derivative zero) for $t\le1/4$ and equals 1 for $t\ge1/2$, and
$\mathrm{sat}(s)=2\,\mathrm{step}(s+1)-1$ is odd, nondecreasing and saturating, so $s\,\mathrm{sat}(s)\ge0$.
The operator is $F(x)=G(\psi(x-x_0))+\kappa\,(x-x_0-\psi(x-x_0))$, where $\psi$ is the smooth radial
retraction of PR #176 (identity on the ball of radius $b$, image in radius $3b/2$, Lipschitz derivative
$32/b$). Proved properties:

1. **Minty everywhere.** $\langle G(z),z-z^\star\rangle=\kappa r^2\sum(\ldots)\,s\,\mathrm{sat}(s)\ge0$
   termwise, with $z^\star=r\sum_i e_{\pi(i)}$, $\|z^\star\|=R$. Outside the ball, writing $\psi(x)=sx$,
   $\langle F(x),x-x^\star\rangle\ge\kappa(1-s)\|x\|(\|x\|-2R)\ge0$ because $\|G\|\le\kappa R$.
2. **Smoothness.** $\|DG\|\le12\kappa$ and $\|DG(x)-DG(y)\|\le256\frac{\kappa}{r}\|x-y\|$ (a bidiagonal
   operator-norm lemma), so $\mathrm{Lip}(F)\le14\kappa\le L_1$ and
   $\mathrm{Lip}(J)\le256\kappa/r+416\kappa/b\le L_2$. Both inequalities are exactly the choice
   $m\le M/2^{14}$; this is where both terms of the minimum arise from one family.
3. **Residual floor.** If the last chain coordinate of $\psi(x-x_0)$ is at most $r/4$, then
   $\|F(x)\|\ge\frac3{10}\kappa r=2.4\varepsilon$: the first coordinate $j^\star$ with
   $z_{j^\star}\le r/2$ has an open gate and $|\mathrm{sat}|\ge3/4$; the wall term is handled by a split on
   $\|x-\psi(x)\|$ combining the triangle inequality with the Minty-coercivity estimate.
4. **Jet hiding.** If the coordinates $\pi(i)$, $i\ge k$, of $\psi(x)$ are at most $r/4$ in absolute value,
   both the value and the full Jacobian at $x$ coincide with a prefix operator depending only on
   $\pi(0),\dots,\pi(k)$ (flat gates kill both the rows and their derivatives; $D\psi$ depends on $x$ only).
5. **Counting.** All observations ($\psi$ of every query point and of the output) have norm at most
   $12R$, hence at most $2304m$ coordinates above $r/4$. Averaging over all injections, at most half are
   "bad" when $d\ge4609m^3$, and on good injections the output keeps the last coordinate hidden. The hard
   operator depends on the algorithm and budget, not on its realized seed.

The proof is connected to the frozen `execute` through the translated oracle and
`execute_iterate`, for both query types.

## What is new, and what is reused

- **New.** No lower bound for nonmonotone Minty or weak-Minty VIs with higher-order (Jacobian) oracles was
  available. Lin and Jordan explicitly leave it open: Perseus (arXiv 2205.03202 v7, Mathematical
  Programming 2024), Section 2, “Comments on weak versus strong solutions” — “We would be very surprised
  if the optimal complexity bound for the monotone setting … can be achieved for the setting when only the
  Minty condition holds” —; Remark 3.13 — the lower bound “for finding an ε-strong solution under the
  Minty condition is largely unexplored and missing even in the current literature for first-order VI
  methods”; and the concluding section — “Future research include the investigation of lower bounds for
  the nonmonotone setting with the Minty condition”.
  At $p=2$ the result settles their question: the Minty price is $\Theta(L_2R^2/\varepsilon)$, while the
  monotone residual complexity is $\tilde\Theta((L_2R^2/\varepsilon)^{2/5})$
  (Jiang–Yoon, arXiv 2609.30212 v2, Theorems 5.1 and 6.1; repository PR #176 randomized lower bound),
  a separation of order $(L_2R^2/\varepsilon)^{3/5}$. It also shows that the $O(\varepsilon^{-2/p})$ rate of
  Perseus Theorem 3.7 at $p=2$ and the repository's hybrid method are optimal up to constants, and it
  captures the transition to the first-order term $L_1^2R^2/\varepsilon^2$ at $\varepsilon\approx L_1^2/L_2$
  with the same family.
- **Reused (credited).** Hiding complete derivative information behind exactly flat gates is a known
  technique for higher-order lower bounds: zero-chains of Carmon, Duchi, Hinder and Sidford
  (*Lower bounds for finding stationary points I*, Mathematical Programming 2020), and the scalar
  convex–concave chain "with exactly flat gates that hide complete derivative information" of Li et al.
  ([arXiv 2609.28246](https://arxiv.org/abs/2609.28246)) for higher-order minimax. The dead-zone Minty chain
  idea for $p=1$ is from the repository's [`EuclideanWeakMintyLowerBound`](EuclideanWeakMintyLowerBound.md)
  (PR #182), whose clip/clamp chain and ball projection are not $C^1$ and therefore do not belong to the
  $L_2$ class. The smooth radial retraction, the prefix simulation of full jets, the finite random
  injection and the pointwise-in-seed averaging come from
  [`RandomizedGlobalJacobianMonotoneLowerBound`](RandomizedGlobalJacobianMonotoneLowerBound.md) (PR #176,
  for monotone operators). The new mathematical content is not the flat-gate hiding itself but a
  $C^{1,1}$ non-gradient chain that is Minty everywhere, a Minty-preserving smooth wall with a residual
  floor that survives outside the identity region, and the joint choice of link length that produces both
  terms of the minimum.
- **Standard reductions do not give it.** Monotone hard instances are monotone and give only
  $(L_2R^2/\varepsilon)^{2/5}$; rescaling an $L_1$-only lower bound cannot produce an $L_2$ term; affine
  Minty operators are monotone, so no linear or quadratic family can exhibit the gap; and the hard operator
  is not a gradient field (its Jacobian is not symmetric), so star-convex minimization bounds do not apply.

## Limitations

- High dimension: $d\ge M^3$ is required by the random-injection argument. In low dimension, every value
  query of a Minty operator gives a cutting plane through $x^\star$, so $\mathrm{poly}(d)\log(1/\varepsilon)$
  methods are plausible; the theorem says nothing there.
- The weak-Minty range is $0\le\rho\le1/L_1$; dependence on the margin $1-\rho L_1/2$ near the boundary
  $\rho L_1\to2$ is not captured. The lower-bound instances are Minty ($\rho=0$).
- Only $p=2$ is formalized. The same construction with $C^{p-1,1}$ gates suggests
  $\Theta((L_pR^p/\varepsilon)^{2/p})$ for general $p$, but that is not proved here.
- The constants ($2^{15}$ versus $2^{27}$) are not optimized.
- Literature search: ICML/ICLR/NeurIPS 2024–2026 and arXiv 2024–2026 on higher-order and nonmonotone VI
  lower bounds, including full-text checks of arXiv 2609.13462 v2, 2609.30212 v2, 2609.28246 and
  2611.11691 (resolvent-ellipsoid method for Minty inclusions, a different oracle model); none contains a
  Minty or weak-Minty lower bound for value-plus-Jacobian oracles.
