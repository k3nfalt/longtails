# BoundedScalarConvex: novelty assessment

The [theorem](../../LongTails/Theorems/BoundedScalarConvex.lean), [setup](../../LongTails/Setups/BoundedScalarConvex.lean), and [algorithm](../../LongTails/Algorithms/ScalarSgd.lean) prove the integrable expected gap $\int(f(X_K)-f(x_\star))\,dO.\mathrm{law}\le\varepsilon$ for constant-step projected scalar SGD’s last iterate, for every admissible objective/oracle.

Here $C=[\mathrm{lower},\mathrm{upper}]$ is nonempty and bounded, $f:C\to\mathbb R$ is convex and $H$-Lipschitz, $H,\varepsilon>0$, $R\ge0$, and $x_0\in C$ lies within $R$ of some constrained minimizer. Jointly measurable replies satisfy $|Y_n|\le H$ almost surely and conditional means support $f$ on $C$, for **every** feasible query measurable in the revealed-seed past; the probability law need not be IID. With $\eta=\varepsilon/(25H^2)$,

$$K=\max\{1,\lceil25H^2R^2/\varepsilon^2\rceil\}=O(1+H^2R^2/\varepsilon^2).$$

[Execution](../../LongTails/Proofs/ScalarExecution.lean) uses exactly $K$ replies, no objective values or extra calls, and is always feasible. Parameters are public; $R$ enters stopping only. $R=0$ still costs one call; a singleton has zero gap, and $\varepsilon\ge HR$ permits returning $x_0$ without calls. $H=0$ is excluded.

Table: expected last-iterate gap $\le\varepsilon$; one reply/update; universal constants suppressed.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Liu–Zhou, [Theorem 3.1/C.1](https://proceedings.iclr.cc/paper_files/paper/2024/file/b1239ceb879da48b4bac7aa91ea53162-Paper-Conference.pdf), ICLR 2024; retained in March 2026 v4 | $O(1+(H^2R^2/\varepsilon^2)\log(2+HR/\varepsilon))\to O(1+H^2R^2/\varepsilon^2)$ | Factor $\log(2+HR/\varepsilon)$ between these bounds as $\varepsilon/(HR)\to0$; $0<\varepsilon<HR$ | None | None: both tuned constant-step last iterates | Current: scalar, compact, bounded replies; prior: arbitrary dimension, finite variance |
| Liu–Zhou, [Theorem 3.4/C.3](https://arxiv.org/html/2312.08531v4), March 19, 2026 v4 extended preprint | $O(1+H^2R^2/\varepsilon^2)\to O(1+H^2R^2/\varepsilon^2)$ | None: same order | None | Linear decay → constant updates; same output/parameter knowledge | Current loses higher-dimensional/general-domain/finite-variance scope |
| Beretta et al., [Theorem 2, Eq. (2)](https://arxiv.org/html/2606.24879), June 23, 2026 v1 preprint | $O(1+H^2R^2/\varepsilon^2)\to O(1+H^2R^2/\varepsilon^2)$ on bounded-response overlap | None: same order | IID additive → dependent replies, within compact bounded-response overlap | None | Incomparable overall: current caps replies/domain; prior allows unbounded noise/domain |

For Liu–Zhou, extend $f$ outside $C$ with slopes $\pm H$: bounded relative supporting means become global subgradients. Set their smoothness $L=0$, $M=2H$, variance bound $\sigma=H$, and Euclidean Bregman initialization $\le R^2/2$; admissible steps are respectively $\Theta(R/(H\sqrt{T\log T}))$ and $\Theta(R(T-t+1)/(HT^{3/2}))$ for $R>0$. For Beretta's overlapping IID model, set $L=\sigma=H$: Eq. (2) becomes $R^2/(2\eta n)+5\eta H^2$; $\eta=\varepsilon/(10H^2)$ and $n\ge\max\{2,10H^2R^2/\varepsilon^2\}$ suffice, costing $n-1$ calls.

Substitution/rescaling, batching, clipping, and regularization do not preserve the selected recursion while producing its bound: generic constant-step analysis retains a logarithm; Beretta's excursion domination needs identical future noise laws. The [proof](../../LongTails/Proofs/ScalarRate.lean) inherits the excursion-plus-regret skeleton, adding finite conditional hinge supersolutions and secant-weighted telescoping to establish $E[f(X_T)-f(X_s)]\le12\eta H^2$ without stationarity.

Search on **2026-10-05 UTC** covered primary arXiv versions, ICML/ICLR/NeurIPS/COLT sources, foundational averaging/last-iterate proofs and later improvements/counterexamples; no decisive source remained inaccessible. Git introduces this result on **2026-09-28** (`3c0299d`), so all table sources predate it. No material companion-note mismatch found: [Liu–Lu, §4.1/Theorem 4.10](https://arxiv.org/pdf/2106.14588v1) (June 28, 2021 v1 preprint) requires nearly linear slopes; Theorem 4.12 is stationary, with no finite mixing budget. Beretta's Theorem 3 counterexamples use horizon-growing replies (§6), excluded here. Local [SgdConvex](../../LongTails/Theorems/SgdConvex.lean) and subsequent October 1 [LinearDecaySgdLastIterate](../../LongTails/Theorems/LinearDecaySgdLastIterate.lean) concern smooth IID models, not this nonsmooth adapted class.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED** — confidence **medium**.

**New advantages**

- Liu–Zhou constant-step baseline: logarithmic call overhead → no logarithm for scalar bounded replies, as $\varepsilon/(HR)\to0$.
- Liu–Lu: nearly linear slope restriction → arbitrary convex Lipschitz profiles; a genuine objective-class enlargement under bounded responses.
- Beretta: IID additive noise → dependent bounded replies, trading finite variance/unbounded-domain scope for this extension.
- Liu–Zhou linear decay: retains the same call order and last-iterate accuracy with unmodified constant updates.
- Beretta's stationary domination: finite conditional hinge bounds handle changing conditional laws; the excursion/regret framework itself is inherited.

This addresses the bounded-response scalar part of [Koren–Segal’s Open Problem 1](https://proceedings.mlr.press/v125/koren20a/koren20a.pdf) (COLT 2020), through stronger analysis of a standard algorithm; best-algorithm complexity is unchanged. No oracle-access, adaptive-stopping, or optimality advantage is established; prior-art completeness remains uncertain.
