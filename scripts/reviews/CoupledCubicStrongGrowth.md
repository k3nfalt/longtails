# Novelty assessment: CoupledCubicStrongGrowth

[`result`](../../LongTails/Theorems/CoupledCubicStrongGrowth.lean) proves the following. Take a finite sum $F=\frac1n\sum_i f_i$ of $C^2$ components on a $d$-dimensional real Hilbert space, satisfying strong growth and RMS component-Hessian Lipschitzness ([setup](../../LongTails/Setups/StrongGrowthFiniteSumSecondOrder.lean)). Then the sampled cubic tournament ([algorithm](../../LongTails/Algorithms/CoupledCubicTournament.lean)) returns $X$ with $\Pr(\|\nabla F(X)\|\le\varepsilon,\ \nabla^2F(X)\succeq-\sqrt{\rho\varepsilon}I)\ge 2/3$.

**Parameters.** $\kappa\ge1$ is the strong-growth constant: $\frac1n\sum_i\|\nabla f_i\|^2\le\kappa\|\nabla F\|^2$. $\rho>0$ is the RMS Hessian-Lipschitz constant: $\frac1n\sum_i\|\nabla^2f_i(x)-\nabla^2f_i(y)\|^2\le\rho^2\|x-y\|^2$. $\Delta\ge F(x_0)-\inf F$ is the initial gap, and $d=\dim E$. One call returns the pair $(\nabla f_i(x),\nabla^2f_i(x))$. No gradient-Lipschitz constant is assumed. The public budget $\lceil10^{20}\kappa(d+1)\rceil\,(\lfloor\log_2 3T\rfloor+1)\,T$, where $T=\lceil16000\sqrt\rho\Delta/\varepsilon^{3/2}\rceil+1$, is

$$
O\!\Big(\kappa(d+1)\big(1+\tfrac{\sqrt\rho\,\Delta}{\varepsilon^{3/2}}\big)\log\big(3+\tfrac{\sqrt\rho\,\Delta}{\varepsilon^{3/2}}\big)\Big)\quad\text{paired calls, with no dependence on } n.
$$

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Full-batch cubic regularization: Nesterov–Polyak, *Math. Program.* 108 (2006), Thm 1, with the small-step stopping rule; the CR row of STR Table 1 restates the rate. Applies to the **full target class**: it needs only population Hessian Lipschitzness, which RMS-$\rho$ implies. | $O(n(1+\sqrt\rho\Delta\varepsilon^{-3/2}))$ → $O(\kappa(d+1)(1+\sqrt\rho\Delta\varepsilon^{-3/2})\log(3+\sqrt\rho\Delta\varepsilon^{-3/2}))$ | A factor $n/(\kappa(d+1)\log(\cdot))$ when $\kappa(d+1)\log(3+\sqrt\rho\Delta\varepsilon^{-3/2})\ll n$. Worse otherwise; the constant $10^{20}$ makes the gain purely asymptotic. | None: CR covers a broader class (it needs neither strong growth nor RMS Hessian regularity). | None: same exact cubic subproblem and stopped-iterate certificate. | Success probability is 2/3 rather than deterministic. Requires strong growth and RMS (not merely population) Hessian Lipschitzness. |
| STR2: Shen–Zhou–Fang–Ribeiro, [arXiv:1903.01540v1](https://arxiv.org/abs/1903.01540v1), Cor. 5.1 (Estimator 6). **Special-case baseline**: requires component $L_1$-gradient and uniform $L_2$-Hessian Lipschitzness. | Total of $\tilde O(n^{3/4}\sqrt\rho\Delta\varepsilon^{-3/2})$ (an $L_1$-dependent Hessian batch and $\log(d/\delta)$ are hidden) → this result on the common subclass | Gain when $\kappa(d+1)\log(\cdot)\ll n^{3/4}$. For example, $n=\varepsilon^{-1}$ and $d=\varepsilon^{-1/4}$ give $\varepsilon^{-7/4}$ vs $\varepsilon^{-9/4}$ up to logarithms. Worse when $\kappa d\gtrsim n^{3/4}$. | Removes the global gradient-Lipschitz constant $L_1$ and weakens uniform Hessian Lipschitzness to RMS; adds strong growth. The classes are incomparable. | None. STR2 holds with probability $1-\delta$ and pays $\log(1/\delta)$; here confidence is fixed at 2/3. | Strong growth (all $\nabla f_i=0$ wherever $\nabla F=0$). Cost is linear in $d$. |
| PSGD: Roy–Balasubramanian–Ghadimi–Mohapatra, [NeurIPS 2020](https://proceedings.neurips.cc/paper/2020/hash/92a08bf918f44ccd961477be30023da1-Abstract.html), Thm 3.1(a). **Special case**: needs population $L_G$ and relative sub-Gaussian tails. | $\tilde O(\varepsilon^{-2})$ gradient calls ($\kappa,L_G$ hidden) → $\tilde O(\kappa d\,\varepsilon^{-3/2})$ | For fixed $\kappa,\rho,\Delta,L_G$, the $\varepsilon$-exponent improves from $2$ to $3/2$ when $d\log(1/\varepsilon)\ll\varepsilon^{-1/2}$. | Drops $L_G$ and the tail condition; adds RMS component-Hessian regularity. Incomparable. | Thm 3.1(a) only guarantees that half of the iterates are good and gives no selection rule; here the stopped output is certified (probability 2/3). | Needs a full component-Hessian oracle; PSGD needs only stochastic gradients. Their SCRN (Thm 4.1) has $O(\varepsilon^{-5/2})$ cost and a Hessian batch of size $\varepsilon^{-1}$. |

**Standard-reduction check.** Plugging strong growth into existing inexact or probabilistic cubic and trust-region frameworks does not give an accuracy-independent batch. Examples are Kohler–Lucchi (ICML 2017, Assumptions 4–5), Scheinberg–Xie ([arXiv:2308.13161](https://arxiv.org/abs/2308.13161)) and Roy et al. Thm 4.1. These frameworks need separate *absolute* gradient errors $\lesssim\|s\|^2$ and Hessian errors $\lesssim\|s\|$.

I checked the companion's scalar counterexample, $f_i=w_i\lambda x^2/2$ with mean weight one. It satisfies the setup with $\kappa=\mathbb E w^2$, and the separate errors scale like $|s_\star|$ while the coupled residual scales like $\rho|s_\star|^2$.

The new ingredients are three:
- a relative Hessian-moment bound derived from strong growth at displaced points;
- coupled residual control;
- majority-compatibility selection among $\log T$ models.

Roy et al. (Remark 6) explicitly leave Hessian-level use of interpolation open. Proof ancestry: Nesterov–Polyak cubic descent (step-to-stationarity bounds), plus median-of-means style amplification. Neither supplies the coupled sampling bound.

**Search coverage.** On 2026-11-05 UTC I searched arXiv, PMLR/AISTATS, NeurIPS and optimization-online, and read the theorem statements of STR, SRVRC ([AISTATS 2020](https://proceedings.mlr.press/v108/zhou20a.html), Cor. 4.3; its total gradient count is no better than STR2's in general), Roy et al. and Meng et al. (AISTATS 2020, strongly convex only).
- **Not re-read:** the original Nesterov–Polyak text (paywalled; I relied on standard statements and STR Table 1).
- **Not checked:** the proofs of Re3MCN ([arXiv:2510.08714](https://arxiv.org/abs/2510.08714)).
- **Not comparable:** [arXiv:2611.05807](https://arxiv.org/abs/2611.05807) (4 Nov 2026, one day before this commit). It uses Hessian-vector-product calls and requires averaged $L$-smoothness. It is also more recent than the companion's reference list.

The 2026 strong-growth trust-region preprint ([arXiv:2604.14017](https://arxiv.org/abs/2604.14017)) is first-order only and lists second-order variants as future work. The companion note says its searches ran "through 6 November 2026", which postdates the current UTC date. Otherwise its claims match the Lean statement.

## Conclusion

**Yes: under strong growth, the proved cost for finding a second-order stationary point no longer depends on $n$, which beats full-batch cubic regularization when $n$ is large.**

The strongest baseline covering the whole class is full-batch cubic regularization:

| | paired calls |
|---|---|
| Cubic regularization | $n\,(1+\sqrt\rho\Delta\varepsilon^{-3/2})$ |
| This result | $\kappa(d+1)\,(1+\sqrt\rho\Delta\varepsilon^{-3/2})\log(3+\sqrt\rho\Delta\varepsilon^{-3/2})$ |

The gain survives only when $\kappa(d+1)\log(\cdot)\ll n$; the $10^{20}$ constant makes it asymptotic. On the subclass with global gradient smoothness, it also beats STR2's $n^{3/4}\varepsilon^{-3/2}$ when $\kappa d\log(\cdot)\ll n^{3/4}$. It improves the $\varepsilon$-exponent of the interpolation-based PSGD bound ($\varepsilon^{-2}$), but PSGD uses a cheaper gradient-only oracle.

The costs are real. The success probability is only 2/3, the cost grows linearly in $d$, strong growth is a strong assumption, and each call returns a full Hessian. I checked that the obvious reduction fails: existing inexact-cubic error conditions force accuracy-dependent batches here. That is a proved obstruction, not an exhaustive priority search. Under Hessian-vector-product oracles, no comparison is established.

What can be claimed: an $n$-independent $O(\kappa d\,\varepsilon^{-3/2}\log)$ bound for second-order stationarity of strong-growth finite sums. I found no such bound in the checked literature, and it rests on a coupled-error sampling argument.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
