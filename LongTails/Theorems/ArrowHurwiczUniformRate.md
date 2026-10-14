# The Arrow–Hurwicz method / projected alternating GDA on bounded composite saddle problems: a uniform $O(1/T)$ ergodic gap with a game-independent step

Lean: [`ArrowHurwiczUniformRate.lean`](ArrowHurwiczUniformRate.lean) (theorem `result`, budget `budget`),
setup [`../Setups/BoundedCompositeSaddle.lean`](../Setups/BoundedCompositeSaddle.lean) (reused unchanged),
algorithm [`../Algorithms/ArrowHurwicz.lean`](../Algorithms/ArrowHurwicz.lean) (reused unchanged),
new proofs [`../Proofs/ArrowHurwiczBand.lean`](../Proofs/ArrowHurwiczBand.lean),
[`../Proofs/ArrowHurwiczToeplitz.lean`](../Proofs/ArrowHurwiczToeplitz.lean),
[`../Proofs/ArrowHurwiczSpectral.lean`](../Proofs/ArrowHurwiczSpectral.lean),
[`../Proofs/ArrowHurwiczMultiplier.lean`](../Proofs/ArrowHurwiczMultiplier.lean),
[`../Proofs/ArrowHurwiczFriction.lean`](../Proofs/ArrowHurwiczFriction.lean),
and the existing [`../Proofs/ArrowHurwiczGap.lean`](../Proofs/ArrowHurwiczGap.lean),
[`../Proofs/ArrowHurwiczRate.lean`](../Proofs/ArrowHurwiczRate.lean),
[`../Proofs/ArrowHurwiczRun.lean`](../Proofs/ArrowHurwiczRun.lean),
[`../Proofs/ArrowHurwiczStep.lean`](../Proofs/ArrowHurwiczStep.lean).

## Problem class (unchanged from the existing setup)

$$\min_{x\in X}\max_{y\in Y}\ \Phi(x,y)=g(x)+\langle y,Kx\rangle-h(y).$$

- $E, F$ are real inner-product spaces of arbitrary (possibly infinite) dimension.
- $X\subseteq E$ and $Y\subseteq F$ are convex, with $\|x\|\le R$ on $X$ and $\|y\|\le R$ on $Y$.
- $K:E\to F$ is a bounded linear map with $\|K\|\le L$; the adjoint is available.
- $g$ is convex on $X$, $h$ is convex on $Y$, and both are $M$-Lipschitz on their sets (possibly nonsmooth).

This is the Chambolle–Pock problem class with both domains bounded and Lipschitz $g,h$. With $g=h=0$ it contains every
bilinear game over compact convex sets: matrix games (simplices), extensive-form games in sequence form, and bilinear
problems over balls, boxes or spectraplexes. With $g,h\neq 0$ it contains, for example, $\ell_1$-regularized games and
LP saddle formulations on bounded boxes. The setup is exactly the repository's existing
`BoundedCompositeSaddle`; nothing is added or strengthened.

## Oracle and algorithm (unchanged)

- **Oracle queries:** $y\mapsto K^*y$, $x\mapsto Kx$, and the exact proximal points
  $\mathrm{prox}_{\tau(g+\iota_X)}$ and $\mathrm{prox}_{\tau(h+\iota_Y)}$.
- **Algorithm:** the Arrow–Hurwicz method (PDHG with $\theta=0$; projected alternating GDA when $g=h=0$):
  $$x_{t+1}=\mathrm{prox}_{\eta(g+\iota_X)}(x_t-\eta K^*y_t),\qquad y_{t+1}=\mathrm{prox}_{\eta(h+\iota_Y)}(y_t+\eta Kx_{t+1}),$$
  with the constant step $\eta = 1/(2L)$. This uses only the public parameter $L$.
- **Output:** the uniform averages $\bar x_T=\frac1T\sum_{t=1}^T x_t$ and $\bar y_T=\frac1T\sum_{t=1}^T y_t$.
- **Cost:** each iteration makes 4 oracle calls. The setup's `allowedAlgorithm` admits exactly `arrowHurwicz η x0 y0`
  with $\eta>0$. The proof reuses `execute_ah` and `output_eq`, so the execution performs exactly $4T$ calls and returns
  these averages.

## Guarantee

**Theorem (`result`).** Let $\eta=1/(2L)$. For every $T\ge 1$, $\bar x_T\in X$, $\bar y_T\in Y$, and

$$\sup_{x\in X,\,y\in Y}\ \Phi(\bar x_T,y)-\Phi(x,\bar y_T)\ \le\ \frac{162\,LR^2+28\,MR}{T}\ \le\ \frac{162\,R(LR+M)}{T}.$$

**Budget.** The formal budget is

`budget p = 4 * ⌈200 * p.R * (p.L * p.R + p.M) / p.ε⌉₊`,

so $O(R(LR+M)/\varepsilon)$ oracle calls suffice for an $\varepsilon$-saddle point.

The supporting lemma `Hyp.uniform_total` holds for **every** step $0<\eta\le 1/(2L)$:

$$\eta\sum_{t=1}^{T}\mathrm{gap}_{(x,y)}(x_t,y_t)\le 81R^2+28\,\eta MR,$$

so the gap is at most $(81R^2/\eta+28MR)/T$. The public theorem fixes $\eta=1/(2L)$ to give the one-line budget.

## What was known, and what is new

**The same setup in this repository** ([`ArrowHurwiczBoundedSaddle.md`](ArrowHurwiczBoundedSaddle.md)):
- The existing theorem gives a uniform $O(R(LR+M)\,T^{-3/4})$ gap, i.e. $O(\varepsilon^{-4/3})$ calls, with a
  $T$-dependent step.
- Its note records whether a uniform $O(1/T)$ holds as open.
- The new theorem improves the complexity from $\varepsilon^{-4/3}$ to $\varepsilon^{-1}$ in the same setup, with the
  same oracle, algorithm, output and accuracy criterion.
- The step is now a $T$-independent constant $1/(2L)$.

**Chambolle–Pock** (J. Math. Imaging Vis. 2011, §3.2, the case $\theta=0$):
- With constant steps, the Arrow–Hurwicz analysis leaves a non-vanishing $O(\tau)$ error term. Ergodic $O(1/N)$ rates
  there are for $\theta=1$ (PDHG), a different algorithm.
- The authors list understanding the good practical behaviour of Arrow–Hurwicz as an open question.

**Nan, Das Gupta, Iyengar, Kroer**, ICLR 2026 ([arXiv:2510.03855](https://arxiv.org/abs/2510.03855)):
- For bilinear matrix games, alternating GDA has an ergodic $O(1/T)$ rate only for games with an interior Nash
  equilibrium; otherwise the results are local.
- They raise as open whether alternation improves on simultaneous GDA's $O(1/\sqrt T)$ in general constrained games.

**Nan, Iyengar, Kroer, Das Gupta**, preprint [arXiv:2609.32995v1](https://arxiv.org/abs/2609.32995) (Sept. 2026,
unrefereed as of 2026-10-06):
- **Thm 1 (simplices):** $\mathrm{Gap}\le 15/(2\eta T)$, but only for $\eta\le\delta/(2\sqrt2L)$. Here $\delta$ is a
  game-dependent separation constant that can be arbitrarily small, so the rate is not uniform at any fixed step.
- **Thm 2 (compact convex sets):** $O(1/T)$ *conditional* on exact feasibility of a history-$h$ Lyapunov LMI. They
  report numerical feasibility for $h\ge2$ in a small step range.
- **Examples:** the last iterate need not converge.

**New in this theorem:**
- the first *uniform* (game- and instance-independent step and constants) $O(1/T)$ ergodic gap for the Arrow–Hurwicz
  method / projected alternating GDA;
- it holds over arbitrary bounded convex sets in arbitrary inner-product spaces, and also in the composite case with
  Lipschitz $g,h$;
- it is unconditional;
- it removes the dependence on $\delta$ in 2609.32995 Thm 1, makes their conditional Thm 2 an unconditional theorem
  (with explicit constants), and answers the question of 2510.03855 for this method affirmatively;
- as a consequence, $O(1/T)$ in $T$ matches the order of known lower bounds for first-order methods on bilinear
  saddle problems (Ouyang–Xu, Math. Program. 2021). The constant 162 is not claimed to be tight.

## Technical mechanism

**1. Reduction to friction** (existing `Hyp.one_step_sum`). For every comparator,
$\eta\sum_{t<T}\mathrm{gap}(z_{t+1})\le \mathrm{lyap}_0-\mathrm{lyap}_T+\frac12\sum_{t<T}r_t$, where:
- $r_t=\langle\nu_t,z_{t+1}-z_t\rangle$ is the "friction" of the prox residual $\nu_t$ (nonnegative when $g=h=0$; in general $r_t\ge\eta(\varphi(z_{t+1})-\varphi(z_t))$, and the proof needs no sign);
- $\nu_t=(x_t-\eta K^*y_t-x_{t+1},\ y_t+\eta Kx_{t+1}-y_{t+1})$.

A uniform $O(1/T)$ rate is therefore equivalent to a uniform bound on the total friction. The previous
$T^{-3/4}$ proof bounded friction step by step, which leaves an $\eta^4$ per-step remainder.

**2. Friction lemma** (`Hyp.friction_le`). If $\eta L\le\frac12$, then $\sum_{t<T}r_t\le150R^2+56\,\eta MR$ for all $T$.
- **Constraints.** The prox optimality condition gives a generalized cyclic-monotonicity inequality
  $\langle\nu_t,z_{t+1}-q\rangle\ge\eta(\varphi(z_{t+1})-\varphi(q))$ for **every** $q\in X\times Y$, where
  $\varphi=g+h$.
- **Multiplier.** We add these inequalities for *all* pairs $(t,s)$ with nonnegative weights $w_{t+1-s}$ that depend
  only on the lag. The weights are non-causal (both past and future lags) and have infinite memory, truncated
  at $|k|\le T+1$. Indices outside $[0,T]$ use $q=z_0$.
- **Toeplitz form** (`toeplitz_identity`). After the shift $z\mapsto z-z_0$, the weighted sum becomes a Toeplitz
  bilinear form in the trajectory, plus two boundary terms bounded by $O(R^2)$.
- **Coefficients.** The kernel coefficients equal
  $-\beta\,c_j$, with $c_j=\frac2\pi\int_{\pi/6}^{\pi}(\sin\frac\omega2-\sin\frac\pi{12})^2\sin((j+\tfrac12)\omega)\,d\omega$
  (`bandH_diff`, `bandKer`).
- **Sign.** The form equals
  $-\beta\frac2\pi\int_{\pi/6}^{\pi}(\sin\frac\omega2-\sin\frac\pi{12})^2G(\omega)\,d\omega$ (`bandKer_integral_form`).
  Here $G(\omega)$ is an explicit quadratic form in the cosine/sine transforms of the trajectory.
  Cauchy–Schwarz on the $K$-block gives
  $G(\omega)\ge(\sin\frac\omega2-\frac{\eta L}2)\cdot(\text{sum of squares})\ge0$ on $[\pi/6,\pi]$
  (`quad_bound`, `trig_form_nonneg`, `band_form_nonneg`). Hence the form is $\le0$ (`qfull_nonpos`).
- **Validity of the weights.** They are nonnegative and give $r_t$ coefficient one, which requires
  $c_0>\sum_{j\ge1}|c_j|$. This is proved from an explicit closed form of $c_j$ (fundamental theorem of calculus)
  together with telescoping majorants: $c_0\ge0.415$, $\sum_{j\ge1}|c_j|\le0.294$ and
  $\sum_{j\ge1}(j+1)|c_j|\le0.834$ (`bandCoef_zero_ge`, `bandCoef_sum_le`).
- **Function values.** The $\varphi$-terms telescope across lags into at most $|k|$ boundary values per lag, giving
  the $56\eta MR$ term (`lag_tele`, `lag_bound`, `friction_lower`).

In control language this is a Zames–Falb-type multiplier for the cyclically monotone prox nonlinearity. Its symbol is
designed to **vanish on the whole low-frequency band** $[0,\pi/6]$, which contains every rotation frequency
$2\arcsin(\eta\sigma/2)$ of the alternating dynamics. On the complementary band the Cayley-transformed AltGDA symbol
is positive definite.

**Why finite windows cannot work.**
- A multiplier with finitely many lags has a trigonometric-polynomial symbol, which cannot vanish on an interval.
- The best length-$h$ window vanishes to order $2h+1$ at $\omega=0$, leaving a per-step defect of order
  $\eta^{2h+2}$. We observed this law numerically in Lyapunov searches for $h=1,2,3$.
- This explains why one-step Lyapunov arguments (the repository's $T^{-3/4}$) and the history-$h$ LMI of 2609.32995
  fall short of a uniform $O(1/T)$.
- The all-lag multiplier with a band-limited symbol defined by an integral removes the defect exactly. Only finitely
  many lags enter for any fixed $T$, and no Fourier series or Parseval argument is needed.

As far as we could determine (search of the ICML 2025–2026, ICLR 2025–2026 and NeurIPS 2024–2025 proceedings, OpenReview, and arXiv through
2026-10-06), integral quadratic constraint (IQC) and Zames–Falb analyses of optimization algorithms have targeted
linear rates under strong monotonicity. Examples are Lessard–Recht–Packard (SIOPT 2016) and Zhang–Bao–Lessard–Grosse
(JMLR 2021). We found none that uses a non-causal, band-vanishing multiplier to bound cumulative friction and obtain an
$O(1/T)$ gap for constrained game dynamics.

## Limitations and open points

- **Fixed step.** The public theorem fixes $\eta=1/(2L)$, and the supporting bound covers all $\eta\le1/(2L)$.
  Numerically the uniform rate persists for $\eta L\le1$, but the proof's coefficient inequality is established only
  for the band edge $\sin(\pi/12)>\frac14\ge\frac{\eta L}2$.
- **Ergodic only.** The result is for the averaged iterates. The last iterate does not converge in general (examples in
  2609.32995).
- **Constants.** Large constants: 162 versus empirical $T\cdot\mathrm{gap}/R^2$ of roughly 4–12 on simplices, balls
  and boxes.
- **Assumptions.** Both domains must be bounded, and $g,h$ must be Lipschitz on them, exactly as in the existing setup.
  The unbounded-primal setting of Chambolle–Pock's imaging examples is not covered.
- **Oracle.** The oracle model assumes exact prox steps and adjoint evaluations.
- **Novelty risk.** The novelty assessment rests on the literature search above. 2609.32995 is a recent preprint by
  active authors, and a later version could contain related results.
