# RidgeClockTwoTapLogistic: certified first fit of two-tap logistic GD

[`result`](../../LongTails/Theorems/RidgeClockTwoTapLogistic.lean) proves the following. Take fixed-step full-batch GD on the mean logistic loss of the two-tap model $m_i=a\langle x_i,v\rangle+b\langle Sx_i,v\rangle$, where $S$ is the cyclic shift. The run starts at $x_0$, uses step $\eta>0$, and freezes at its first strict fit. If the instance satisfies the setup's `geometry` certificate, every run returns a point with all $m_i>0$ within `budget` oracle calls ([setup](../../LongTails/Setups/RidgeClockTwoTapLogistic.lean), [algorithm](../../LongTails/Algorithms/FirstFitGradientDescent.lean)).

**Complexity.** The proved budget, in full-gradient-plus-fit-flag calls, satisfies

$$1+t_0+B\Big\lceil \sum_{j<J}\frac{w_j}{2\eta B\,c_jW_j}\Big\rceil \;=\; O\Big(1+t_0+B+\sum_{j<J}\frac{w_j}{\eta\,c_jW_j}\Big).$$

The parameters are:
- $t_0$: burn-in steps.
- $B$: block length.
- $J$: number of radius bins.
- $w_j$: bin widths in the radius $R=(a^2+b^2+\|v\|^2)/2$.
- $W_j$: interpolated ridge-logistic reference work at the bin edges.
- $c_j>0$: efficiency factors.

The certificate must validate all of these. It also contains a polynomial enclosure of the actual GD orbit with data bounds, a filtered ridge profile, and either margin bounds at the crossing or a signed exponential-work certificate. No bound in terms of a margin $\gamma$, $n$, $d$ or $\|x_0\|$ follows.

**Degenerate case.** Take $J=0$ and an exact orbit enclosure: a single polynomial cell with all radii $r_t=0$ and error terms zero. Then any instance on which GD first fits at step $T$ is admissible with $t_0=T$, provided the filtered ridge-profile check can be met. Its budget is $T+1$. I checked this by reading the definitions, not in Lean. So the budget is a number supplied by the certificate, not a derived complexity.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Zhang–Wu–Lin–Bartlett, adaptive large-step GD on raw logistic regression, [arXiv 2504.04105](https://arxiv.org/abs/2504.04105) (Apr 2025), [JMLR 27 (2026)](https://jmlr.org/papers/v27/25-1941.html), Thm 2.1. Lower bound in Thm 3.2. Prior. | $O(1/\gamma^2)$ full gradients give a separating averaged iterate. This needs $\|x_i\|\le1$ and margin $\gamma$, with $\eta\gtrsim\gamma^{-2}\log n$. → $O(1+t_0+B+\sum_j w_j/(\eta c_jW_j))$ | Not comparable: the selected budget has no bound in $\gamma,n,d$. Thm 3.2 shows $1/\gamma^2$ is minimax for span methods when $1/(30\gamma^2)\le \ln n/(8\ln2)$. | Incomparable classes: all $\gamma$-separable data → data carrying an orbit certificate. | Averaged raw iterate → first-fit iterate of fixed-step joint GD. | Same oracle: a query at $(a,b)=(1,0)$ returns the raw gradient in its $v$-block. The setup's `family` forbids this method. The selected result needs certificates whose construction can cost more than training. |
| Classical perceptron / batch perceptron (Novikoff 1962). Zhang et al. Thm 3.4 discuss its optimality. Prior. | $\le 1/\gamma^2$ updates (each at most one full pass) → same as above | Not comparable (no $\gamma$-dependence proved) | Same as row 1 | Online/batch perceptron iterate → two-tap GD iterate | Same as row 1 |
| Tyurin, [ICML 2026 (PMLR 306)](https://proceedings.mlr.press/v306/tyurin26a.html), [arXiv 2512.11587](https://arxiv.org/abs/2512.11587), Thms 5.1–5.2. Applies only to one two-sample dataset in the $\|w_0\|\to\infty$ quadratic-perceptron limit. Prior. | $\tilde O(\sqrt d/\mu)$ steps vs. $\Omega(d/\mu)$ for the linear perceptron → certificate budget | Not comparable: different data class, limit and loss | Two-sample construction → arbitrary rows, but only under the certificate | None | The selected result proves no dimension or margin advantage |
| Repository: the note's PR 279 spectral certificate for the same focal CIFAR run. I could not check it; it is not in this tree. | 24,456 → 28,161 calls (per the note) | Worse on the one shared instance (by the note's own numbers) | None | None | None |

**Reduction check.** Given the certificate, the proof combines three standard steps:
- an elementary identity for the change in $R$;
- a monotone reciprocal-speed clock (time ≤ Σ width/speed);
- the potential argument that $\sum_i e^{-\beta m_i}<1$ forces every $m_i>0$.

The hard work, namely enclosing the nonlinear orbit and checking its bounds numerically, lies in hypotheses that Lean does not derive. Factorization ([Arora et al. 2018](https://proceedings.mlr.press/v80/arora18a.html)) and ridge-path geometry ([Ji et al. 2020](https://proceedings.mlr.press/v125/ji20a/ji20a.pdf)) are proof ancestry only.

**Search coverage.** On 2026-11-27 I searched arXiv, PMLR/ICML and JMLR for logistic GD time-to-separation, large-step GD and convolutional/perceptron dynamics. I read the theorem statements of Zhang et al. only in partial HTML, so I took their Thm 3.2 constants from a summary. I did not verify Ji–Telgarsky (2018), Wu et al. (2024) or the note's CIFAR/Gisette numerics. The theorem was introduced in commit `6666e5a4` (2026-11-27), so all the cited papers are prior work. The companion note is consistent with this assessment: it states that there is "no improved class-wide separable-logistic complexity" and that PR 279 gives a smaller focal bound. I did not run the build or the audit.

## Conclusion

**No: this proves no complexity bound for any problem class and covers no meaningful new class; it is a certificate-to-success implication for one fixed method.**

The strongest relevant baseline is adaptive large-step GD on the raw linear model (Zhang–Wu–Lin–Bartlett, Thm 2.1). It runs through the same oracle by querying at taps $(1,0)$:

| | Complexity to strict separation |
|---|---|
| Zhang et al. | $O(1/\gamma^2)$ for every margin-$\gamma$ dataset |
| This result | $1+t_0+B\lceil\sum_j w_j/(2\eta Bc_jW_j)\rceil$, with every term supplied by an instance certificate |

These bounds cannot be compared in any parameter regime, because the selected budget is never bounded by data quantities. With an exact orbit certificate, it collapses to the observed first-fit time plus one.

The admissible class is defined by a validated enclosure of the GD trajectory itself, so the instances it covers are not independently motivated. Lean checks only the final, fairly standard implication. Even on the one shared instance, the note's own earlier repository certificate (24,456 calls) beats this one (28,161 calls). The empirical tables are useful for understanding when joint training wins, but they are outside the formal result.

What can be claimed is a formal checker that turns numerical certificates into first-fit guarantees for two-tap GD on specific datasets.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
