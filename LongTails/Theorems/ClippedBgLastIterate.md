# High-probability terminal iterates with distance-growing second moments

The [main theorem](ClippedBgLastIterate.lean) proves an oracle-complexity guarantee for the actual last iterate of [a clipped projected subgradient algorithm](../Algorithms/TerminalClipping.lean). The [setup](../Setups/TerminalClippingConvex.lean) permits nonsmooth convex objectives on unbounded closed convex subsets of arbitrary finite-dimensional Euclidean space. The algorithm receives a bound on the distance to a minimizer and computes its horizon from the requested accuracy. Its clipping threshold depends on the influence of the current update in a terminal-iterate potential, as well as the observable local second-moment bound.

## Setup and guarantee

Let $X\subseteq\mathbb R^d$ be nonempty, closed and convex, $x_0\in X$, and $f:X\to\mathbb R$ convex with a minimizer $u$. Write $R\ge\|x_0-u\|$. Fresh IID samples provide a jointly measurable oracle $g(x,\omega)$ such that

$$
 h(x):=\int g(x,\omega)\,d\nu(\omega)\in\partial_X f(x),\qquad
 \int\|g(x,\omega)\|^2\,d\nu(\omega)
 \le B^2\|x-x_0\|^2+G^2.
$$

Here relative subgradients mean $f(x)-f(y)\le\langle h(x),x-y\rangle$ for all $x,y\in X$. The assumption bounds the **full second moment**, including the mean; it is stronger than a bound on centered variance. The setup explicitly requires the displayed integrability, measurable objective and projection, and exact Euclidean projection onto $X$. No smoothness, bounded domain, higher moments, samplewise convexity, or strong convexity is required. The probability space is arbitrary: the Lean proof assumes an abstract sample-stream law with IID coordinates and derives the finite product representation internally.

The algorithm receives $x_0$, positive bounds $B,G$, a distance bound $R$, accuracy $\varepsilon>0$, and confidence $0<\delta<1$. It computes $T$ from these inputs; neither a horizon nor the minimizer $u$ is supplied. With $q=\log(8/\delta)$, the proved bound is

$$
 \Pr\!\left[f(x_T)-f(u)>
  \frac{16384\,(BR^2+G^2/B)q}{\sqrt T}\right]\le\delta.
$$

This quantitative statement is proved in [the probability module](../Proofs/TerminalClippingProbability.lean) and converted to the framework's epsilon-accuracy statement in [the convergence module](../Proofs/TerminalClippingConvergence.lean). The convergence proof derives the conservative sufficient inequality from the computed horizon

$$
 \bigl(2^{20}(BR^2+G^2/B)\log(8/\delta)\bigr)^2\le T\varepsilon^2.
$$

The algorithm computes $T$ as the maximum and ceiling below, and the public budget explicitly counts $T$ stochastic subgradient calls and $T$ exact projection calls. There are no hidden validation batches, objective queries, or selection calls. The total budget is

$$
 2\max\!\left\{1,\left\lceil
 \frac{2^{40}(BR^2+G^2/B)^2\log^2(8/\delta)}{\varepsilon^2}
 \right\rceil\right\}.
$$

The setup imposes only sign and confidence restrictions on the parameters; sufficient runtime is proved rather than assumed in `valid`. The epsilon-complexity interface requires the supplied bound $R$ to compute the horizon. The theorem returns the actual final projected iterate $x_T$, not an average or an independently selected candidate. Each full-vector oracle query counts once; vector arithmetic and projection implementation costs are separate from this oracle model.

## Algorithm

Index updates by $t=0,\ldots,T-1$. Define

$$
 \eta_t=\frac{T-t}{4096B\sqrt T\,qT},\qquad
 w_t=1-\frac{t+1}{2T},\qquad
 S_t=\sum_{s=t}^{T-1}w_s\eta_s,
 \quad S_{-1}:=S_0,
 \quad a_t=\frac{w_t\eta_t}{S_{t-1}}.
$$

The implementation evaluates the sum without extra iteration:

$$
 S_t=\frac{m(m+1)(3T+2m-2)}{12T^2(4096B\sqrt Tq)},\qquad m=T-t.
$$

Start $P_0=0$. Before sampling, compute

$$
 U_t=a_t(x_t-x_0-P_t),\qquad
 M_t=\sqrt{B^2\|x_t-x_0\|^2+G^2},
$$

$$
 C_t=\min\!\left\{M_t\sqrt T,
          \frac{M_t^2}{B\sqrt T\|U_t\|}\right\},
$$

where the second argument is omitted if $U_t=0$. Set

$$
 x_{t+1}=\Pi_X\bigl(x_t-\eta_t\operatorname{clip}_{C_t}(g(x_t,\omega_t))\bigr),
 \qquad
 P_{t+1}=\frac{S_t}{S_{t-1}}P_t+
       \left(1-\frac{S_t}{S_{t-1}}\right)(x_t-x_0).
$$

Radial clipping is $\operatorname{clip}_C(v)=\min\{1,C/\|v\|\}v$, with zero mapped to zero. $P_t$ is an auxiliary vector used only to choose the threshold; the returned point is never averaged. The algorithm uses one trajectory and no restarts. In the framework, gradient and projection queries alternate. Projection replies are deterministic; the proof extracts the even-indexed IID gradient samples and proves that precisely $2T$ queries produce $x_T$.

## Contribution and closest results

The contribution is the conjunction of a high-probability $T^{-1/2}$ **terminal-iterate objective bound**, a distance-growing full second moment, for general nonsmooth convex objectives. The clipping threshold needs no separate localization radius; the epsilon-complexity interface does require $R$ to compute its horizon. Neither unknown-radius clipping alone nor the terminal-comparator identity is claimed as new. The proposed technical contribution is the computable influence-dependent threshold and its simultaneous control of terminal martingale increments and clipping bias under that growing moment bound.

* **Distance-growing moments, expectation at the terminal iterate.** Alacaoglu, Malitsky and Wright, [arXiv:2504.09951v3, 26 September 2026](https://arxiv.org/html/2504.09951v3), Assumption 3.1 and Theorem 3.6, analyze Halpern-anchored subgradient iterations under the full second-moment condition. Their expected last-iterate bound is
  $2\sqrt6 B(1+\log(k+2))(3R^2+G^2/B^2)/\sqrt{k+1}$.
  That exact version is treated here as a preprint. We obtain logarithmic confidence dependence with a different, horizon-tuned clipped algorithm, and no logarithmic horizon factor in the displayed accuracy bound. We lose the anytime schedule. Markov's inequality applied to their expectation guarantee gives polynomial confidence dependence; ordinary independent repetition alone supplies neither a selector nor the same single-trajectory terminal output.
* **High-probability terminal analysis under lighter tails.** Liu and Zhou, [arXiv:2312.08531v4, 19 March 2026](https://arxiv.org/html/2312.08531v4), Theorem 3.5, give a linear-decay terminal guarantee under sub-Gaussian assumptions. Section 5 treats heavy tails in expectation, and Section 6 treats sub-Weibull tails. The [preliminary paper was accepted at ICLR 2024](https://openreview.net/forum?id=xxaEhwC1I4). Their Lemma 4.1 supplies the moving-comparator telescope underlying our proof. Extending that telescope by itself is not our novelty claim.
* **Clipping without a known radius.** Liu and Zhou, [arXiv:2303.12277v3](https://arxiv.org/html/2303.12277v3), already give unknown-radius clipping on unbounded domains for averaged outputs under global Lipschitzness and uniform central-moment assumptions. Their radius adaptation does not by itself yield the present terminal guarantee or state-dependent moment control.
* **Recent nonsmooth heavy-tail clipping.** Liu, [arXiv:2512.23178v3, 17 May 2026](https://arxiv.org/html/2512.23178v3), [ICLR 2026](https://openreview.net/forum?id=2dbLeXDe39), Assumptions 1–4 and Theorems 1, 10 and 11, analyzes averaged outputs under global objective Lipschitzness and uniform directional and norm central moments. Its refined confidence and dimension dependence is not improved uniformly by our theorem. Its generic clipping-bias bounds are useful established tools, but do not supply the terminal influence cancellation below. Likewise, Parletta, Paudice, Pontil and Salzo, [SIMODS 2024, Theorem 2.2](https://discovery.ucl.ac.uk/10211859/1/22m1536558.pdf), allow general positive averaging weights; concentrating them at the terminal point loses the effective sample-size factor.
* **Recent high-probability clipped last iterates.** Chezhegov, Parletta, Paudice and Gorbunov, [ICLR 2026](https://proceedings.iclr.cc/paper_files/paper/2026/hash/03382840834c7fbdc1e882fac11904d6-Abstract-Conference.html), [Theorem 1 and Section 4](https://openreview.net/pdf?id=4sGEvpwyxN), treat smooth convex objectives with uniform central $p$-moment noise. Their last-iterate accuracy scales as $T^{-2(p-1)/(3p)}$, hence $T^{-1/3}$ at $p=2$, and their tuning uses an initial-distance bound. They emphasize anytime operation. Our theorem covers nonsmooth objectives and growing moments but assumes a full moment bound and computes its horizon using $R$ and the target accuracy; it does not dominate their entire centered-noise class.
* **Other heavy-tail terminal results.** Parletta, Paudice and Salzo, [arXiv:2410.00573v2, 18 April 2025](https://arxiv.org/abs/2410.00573), separate terminal expectation results from averaged high-probability results; Section 7 discusses the latter terminal difficulty. Smooth strongly convex growth-noise results, including [Tsai et al., arXiv:2108.11483v2](https://arxiv.org/abs/2108.11483v2), Theorem 1, use curvature and radius-dependent tuning unavailable here.

These are comparisons of different, explicitly stated classes. The meaningful improvement is over expectation-only terminal guarantees on the full-moment BG class: fixed $B,G,R$ give $\varepsilon^{-2}\log^2(1/\delta)$ sufficient samples, rather than the polynomial confidence cost from Markov's inequality. The theorem also provides a nonsmooth terminal guarantee where the cited finite-variance clipping results return averages. It does not establish a minimax lower bound, optimal confidence dependence, or universal superiority over all uniform-variance smooth algorithms.

## Why the proof is not a standard clipping substitution

For analysis only, define the feasible moving comparator

$$
 z_t=x_0+P_t+\frac{S_{t-1}}{S_0}(u-x_0),\qquad
 V_t=a_t(x_t-z_t)=U_t-\frac{w_t\eta_t}{S_0}(u-x_0).
$$

The coefficient of the unknown minimizer is at most $4/T$. This permits clipping with the observable $U_t$, while controlling the actual terminal influence $V_t$. Ordinary local clipping at $M_t\sqrt T$ can leave a late terminal martingale jump of order $BD\sqrt T$, with $D=R^2+(G/B)^2$. The additional threshold caps it at order $BD/\sqrt T$. Its extra bias is not ignored: the [local bias bound](../Proofs/TerminalClippingMartingale.lean) gives

$$
 \langle h(x_t)-\mathbb E[\operatorname{clip}_{C_t}(g_t)],V_t\rangle
 \le 2B\sqrt T\|V_t\|^2+\frac{26BD}{T\sqrt T}.
$$

The decreasing weights retain a negative squared-comparator-distance term. The [pathwise proof](../Proofs/TerminalClippingPathwise.lean) shows that it pays both this clipping bias and the martingale quadratic compensation. The cancellation applies to indices $1,\ldots,T-1$; the initial term is explicitly retained and bounded. It also handles $T=1$.

A separate stopped exponential potential controls the radius without assuming it is known to the algorithm. Stopping retains the first overshoot before freezing the state. Two further exponential bounds control the terminal martingale and the clipped squared-step sum on the same good-radius event. Their joint event union costs at most $3e^{-q}=3\delta/8\le\delta$. No future-dependent conditioning, union over $T$ confidence events, or bounded-noise substitution is used. [The probability proof](../Proofs/TerminalClippingProbability.lean) then transfers this finite-sample argument to the abstract IID law.

Standard alternatives do not establish this guarantee directly. Localization to a known ball changes the projection domain and generally gives an averaged output. Ordinary repetition alone supplies neither an implementable selector nor the same single-trajectory terminal output. Existing weighted-average bounds lose their sample-size gain when only the endpoint has weight. Smoothing or regularization introduces additional access or inner-solve requirements; uniform-noise, smooth strongly convex clipping results do not apply to a merely convex nonsmooth BG oracle. These exclusions explain the remaining gap addressed by the influence threshold, rather than asserting that all possible reductions are impossible.

## Meaningful instances and limitations

A coupled nonlinear family is robust sparse regression

$$
 f(x)=\mathbb E\!\left[\tfrac12(a^Tx-b)^2+
       \kappa\operatorname{Huber}(c^Tx-d)\right]
       +\lambda\|Cx-e\|_1.
$$

Dense features and $C$ couple coordinates. With invertible $C$, $\lambda>0$, and finite objective moments, coercivity gives a minimizer. A rank-deficient quadratic covariance permits instances without global strong convexity. A stochastic subgradient includes the deterministic term $\lambda C^T\operatorname{sgn}(Cx-e)$. If the relevant moments are finite, one valid choice is

$$
 B^2=6\mathbb E\|a\|^4,\qquad
 G^2=6\mathbb E[(a^Tx_0-b)^2\|a\|^2]
       +3\kappa^2\mathbb E\|c\|^2+3\lambda^2m\|C\|_{\mathrm{op}}^2,
$$

where $m$ is the number of rows of $C$. Any larger positive upper bounds are permitted. This family motivates growing full moments independently of the proof; the theorem does not assume this particular regression structure. Samplewise convexity of this example is not required by the setup.

The constants are conservative. The rate has no explicit dimension factor beyond $B,G,R$, which themselves may depend on dimension. Positive supplied $B,G$ do not preclude instances with zero intrinsic growth or noise, since larger valid upper bounds can be used; the theorem does not optimize those degenerate limits. The result is fixed-horizon, assumes IID rather than arbitrary adapted conditional oracles, and uses exact Euclidean projection. Measurability and integrability are explicit bookkeeping conditions, not an implicit finite-sample-space restriction. A measurable ambient extension of $f$ is required in Lean; accuracy and convexity concern $X$.

The literature search was conducted on 7 October 2026 UTC, independently by the Researcher and Reviewer, covering publicly accessible ICML, ICLR and NeurIPS 2026/2025 records and roughly the preceding two years of arXiv submissions and revisions, followed by older foundational results. Some bulk conference listings and individual web endpoints were inaccessible; individual official records, primary PDFs and latest arXiv versions were used where available. The comparisons above identify checked theorem scopes, not an exhaustive certificate that no other relevant result exists.
