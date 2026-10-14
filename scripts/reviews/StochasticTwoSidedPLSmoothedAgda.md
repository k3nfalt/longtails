# Stochastic smoothed AGDA under two-sided PL: novelty assessment

[`result`](../../LongTails/Theorems/StochasticTwoSidedPLSmoothedAgda.lean) shows the following. Take $f$ with $L$-Lipschitz partial gradients, $\mu_x$-PL in $x$ and $\mu_y$-PL in $-y$ (against arbitrary competitors), with $\max_y f(x,\cdot)$ attained, $E$ finite-dimensional and $F$ Hilbert ([setup](../../LongTails/Setups/StochasticTwoSidedPL.lean)). Use unbiased partial-gradient oracles with variance $\le\sigma^2$. Then one constant-step run of stochastic Smoothed-AGDA ([algorithm](../../LongTails/Algorithms/StochasticSmoothedAgda.lean), $p=2L$), which outputs a uniformly random iterate from the second half, achieves $\mathbb E[(\Phi(\hat x)-\Phi^*)+(\Phi(\hat x)-f(\hat x,\hat y))]\le\varepsilon$.

**Proved budget** (formula `budget`, which counts both oracle branches):
$$N=O\Big(\Big(\frac{L^2}{\mu_x\mu_y}+\frac{L^3\sigma^2}{\mu_x^2\mu_y^2\varepsilon}\Big)\log\Big(e+\frac{\Delta}{\varepsilon}\Big)\Big).$$
Here $L$ is smoothness, $\mu_x,\mu_y$ are the PL constants, $\sigma^2$ is the variance and $\varepsilon$ is the accuracy. The bound $\Delta\ge 2\Phi(x_0)-\Phi^*-f(x_0,y_0)+\|\nabla_xf(x_0,y_0)\|^2/L$ is a known initial bound. The algorithm needs $L,\mu_x,\mu_y,\sigma,\Delta,\varepsilon$. Write $\kappa_x=L/\mu_x$ and $\kappa_y=L/\mu_y$.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Stoc-AGDA, Yang–Kiyavash–He, [NeurIPS 2020](https://proceedings.neurips.cc/paper/2020/file/0cc6928e741d75e7a92396317522069e-Paper.pdf), Thm 3.3 + Remark 3 (prior; same class) | $O\big(\tfrac{L^3}{\mu_x\mu_y^2}\tfrac{P_0}{\varepsilon}+\tfrac{L^5\sigma^2}{\mu_x^2\mu_y^4\varepsilon}\big)$. Here $\gamma\asymp\kappa_x\kappa_y^2$ is forced by $\tau_1\lesssim\mu_y^2/L^3$, and the first term becomes $\kappa_x\kappa_y^2\log$ after a Thm 3.1 warm start. → $N$ | Noise term smaller by a factor $\kappa_y^2/\log(e+\Delta/\varepsilon)$; this is a gain when $\kappa_y^2\gtrsim\log(e+\Delta/\varepsilon)$. Deterministic term: $\kappa_x\kappa_y^2\to\kappa_x\kappa_y$ | None | Worse: last iterate → random second-half iterate. Stoc-AGDA's diminishing steps need no $\sigma,\varepsilon,\Delta$ (anytime); here all three are needed | Extra $\log(\Delta/\varepsilon)$ factor; $\Delta$ also includes $\|\nabla_xf(x_0,y_0)\|^2/L$ |
| Restarted stochastic Smoothed-AGDA: Yang–Orvieto–Lucchi–He, [AISTATS 2022](https://proceedings.mlr.press/v151/yang22b/yang22b.pdf), Thm 4.1 (NC-PL), plus restarts and PL in $x$. This is a reduction derived below from prior results | $O\big(\tfrac{L^2}{\mu_x\mu_y}\log(e+\tfrac{\Delta}{\varepsilon})+\tfrac{L^3\sigma^2}{\mu_x^2\mu_y^2\varepsilon}\big)$ → $N$ | Worse: an extra $\log(e+\Delta/\varepsilon)$ factor on the noise term; deterministic term is the same order | Minor: $\mathbb R^{d_y}$ → Hilbert $F$ | None: both outputs are random iterates and both need $\sigma,\Delta,\varepsilon$. The selected method runs once without restarts | The reduction needs restarts; see the caveat below |
| FESS-GDA, Shen et al., [AISTATS 2024](https://arxiv.org/abs/2311.00944), Thm 3.5 with $M=1$ (prior) | $O(\kappa'^3\kappa''^4\epsilon^{-2}\log)$ for $\mathbb E\|z_T-z^*\|^2\le\epsilon^2$ → $N$ | Not comparable: distance criterion | Saddle-point existence required there; not required here | Not comparable | None checked |

**Reduction check.** For any $(x,y)$, PL in $x$ (with $\inf_{x'}f(x',y)\le\Phi^*$) and PL in $y$ give
$$a+b\le\frac{\|\nabla_xf\|^2}{2\mu_x}+\frac{\|\nabla_yf\|^2}{\mu_y}\le\frac{\|\nabla_xf\|^2+\kappa_y\|\nabla_yf\|^2}{\mu_x}.$$
Similarly, the next stage's initial quantities satisfy $(\Phi(z_0)-\Phi^*)+b_0\lesssim(\cdot)/\mu_x$ when $z_0=\hat x$. Thm 4.1 bounds exactly the average of $\|\nabla_xf\|^2+\kappa_y\|\nabla_yf\|^2$ by
$$\frac{c\,L\kappa_y(\Delta+b_0)}{T}+c\,\kappa_y\sigma\sqrt{\frac{L\Delta}{T}}.$$
Halving $D_k$ therefore costs $T_k\asymp\kappa_x\kappa_y+\kappa_x^2\kappa_y^2\sigma^2/(LD_k)$. Summing over geometrically decreasing $D_k$ gives row 2.

*Caveat:* stages run from random starts, so the step size must use a deterministic upper bound $D_k$ in place of $\Delta$. I checked Thm 4.1's statement but not its appendix inequality line by line.

The note's "double-loop" reduction check misses this composition. The selected proof's envelope-gap lemma and its gradient-norm criterion bound are only a pathwise, restart-free route to the same order. Proof ancestry: the potential of Zhang et al. (2020) and Yang et al. (2022) supplies the descent inequality. The new work is the PL inequality for the potential, which gives linear contraction in a single run.

**Search coverage (2026-10-07).** I covered arXiv, NeurIPS, AISTATS and JMLR for stochastic two-sided-PL and NC-PL GDA, including Chen–Yao–Luo (NeurIPS 2022; finite-sum only) and Guo et al. (JMLR 2023; strongly concave in $y$, so a narrower class; I did not verify its exponents). I found no published stochastic two-sided-PL bound below $\kappa_x^2\kappa_y^4$. Ha ([arXiv:2610.07814](https://arxiv.org/abs/2610.07814), 2026-10-06) appeared at about the same time as the result's commit (acdd9e9, 2026-10-06). It treats only NC-PL SGDA lower bounds and does not apply here. No two-sided-PL stochastic lower bound was found. The companion note says Yang 2022 Thm A.1 covers deterministic two-sided-PL Smoothed-AGDA. In fact, Thm A.1 restates Yang 2020's AGDA result.

## Conclusion

**It improves on the best published two-sided-PL theorem, but the same rate already follows from a short standard reduction.**

Against Yang–Kiyavash–He's Stoc-AGDA (same class), the noise term drops by a factor $\kappa_y^2$ (up to a logarithm):

| | noise term | deterministic term |
|---|---|---|
| Stoc-AGDA (2020) | $\kappa_x^2\kappa_y^4\sigma^2/(L\varepsilon)$ | $\kappa_x\kappa_y^2\cdot(\log\text{ or }P_0/\varepsilon)$ |
| Restarted Stoc-Smoothed-AGDA (2022 Thm 4.1) | $\kappa_x^2\kappa_y^2\sigma^2/(L\varepsilon)$ | $\kappa_x\kappa_y\log(\Delta/\varepsilon)$ |
| This result | $\kappa_x^2\kappa_y^2\tfrac{\sigma^2}{L\varepsilon}\log(\Delta/\varepsilon)$ | $\kappa_x\kappa_y\log(\Delta/\varepsilon)$ |

Yang–Orvieto–Lucchi–He's stochastic Smoothed-AGDA theorem for one-sided PL already controls $\|\nabla_xf\|^2+\kappa_y\|\nabla_yf\|^2$. Two elementary PL inequalities turn that quantity into the target criterion, and geometric restarts then give the same order with one fewer logarithm. Under identical assumptions, the selected result therefore keeps no complexity advantage in any regime. Its output is also weaker than Stoc-AGDA's last iterate, and it needs $\sigma,\varepsilon,\Delta$.

What remains is a restart-free, single-run constant-step analysis using a new potential-PL lemma, and a careful formalization. This is a method-specific proof, not a new optimization guarantee. One step of the reduction (replacing $\Delta$ by an expected bound across restarts) was checked only at the statement level, so confidence is medium.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: medium**
