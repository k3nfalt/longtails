# Novelty assessment: radius-only acceleration for (L₀,L₁)-smooth + Lipschitz composite objectives

[`result`](../../LongTails/Theorems/LipschitzCompositeGeneralizedAccelerated.lean) proves a deterministic guarantee on a real Hilbert space for $F=f+\psi$. Here $f$ is convex and $C^1$, and it is symmetric $(L_0,L_1)$-smooth in segment form. The term $\psi$ is convex and $M$-Lipschitz, and the problem is unconstrained ([setup](../../LongTails/Setups/LipschitzCompositeGeneralizedSmooth.lean)). The guarantee: [`CompositeSherpa.algorithm`](../../LongTails/Algorithms/CompositeSherpa.lean) gets $\nabla f$, an exact composite prox and values of $\psi$. Its updates receive only $L_0,L_1,M,x_0$. After the budget below, its current point satisfies $F(\hat x)-F^*\le\varepsilon$ with no extra condition. Here $R\ge\|x_0-x^*\|$ for some minimizer $x^*$, and no bound on the initial gap is assumed.

**Complexity** (total calls to $\nabla f$, prox and $\psi$ values; from the proved budget $\lceil 184\sqrt{\cdot}+130000(1+L_1R)\log(2+L_1R)\rceil$):
$$N=O\Big(\sqrt{(L_0+L_1M)R^2/\varepsilon}+(1+L_1R)\log(2+L_1R)\Big),$$
valid for $L_0,L_1,R,\varepsilon>0$ and $M\ge0$. Below, $q:=L_1R$.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Li–Lai–An–Hu–Wen, [arXiv:2512.09443v3](https://arxiv.org/abs/2512.09443) (v3 posted 21 Sep 2026; unrefereed), App. B, Thm B.1 (full proof in [l0l1.pdf](https://github.com/optsuite/MathResearchPrompts/blob/main/materials/l0l1/l0l1.pdf), Thm 4.4). Applied to this class with $\tau=M\ge\|\nabla f(x^*)\|$ and the valid gap bound $\Gamma_0R^2=2[(L_0+L_1M)L_1^{-2}(e^{q}-1-q)+2MR]$ | $O\big(\sqrt{(L_0+L_1M)R^2/\varepsilon}+(1+q)[\,q+\log(2+\tfrac{(L_0+L_1M)/L_1^2+MR}{\varepsilon})]\big)$ → $O\big(\sqrt{(L_0+L_1M)R^2/\varepsilon}+(1+q)\log(2+q)\big)$ | Transient drops from $q^2+(1+q)\log(1/\varepsilon)$ to $q\log q$. This is a speedup of order $q/\log q$ when $q\ge2$ and $(L_0+L_1M)/(L_1^4R^2)\ll\varepsilon\le(L_0+L_1M)/L_1^2$. Example: $L_0=L_1=M=\varepsilon=1$, $R=q$ gives $q^2$ vs. $q\log q$. As $\varepsilon\to0$ the shared leading term dominates and the orders coincide | Removes the need for a bound on the initial gap $\Delta$ that does not grow exponentially with $q$. Classes are incomparable: Li allows any proximable $h$, including constraints | Updates need $(L_0,L_1,\tau,R,\Gamma_0)$ → $(L_0,L_1,M)$ only. $R$ and $\varepsilon$ enter only the stopping budget. Both return the last point | Lipschitz $\psi$, unconstrained, plus a $\psi$-value oracle. Li's leading term uses $L_0+L_1\tau$, which can be smaller when a $\tau\approx\|\nabla f(x^*)\|\ll M$ is known. Li requires twice-differentiable $f$ on $\mathbb R^d$ |
| Derived reduction: Moreau smoothing of $\psi$ ($\mu=\varepsilon/M^2$) plus $\tfrac{\varepsilon}{4R^2}\|\cdot-x_0\|^2$, then Everest Thm 3.7 ([arXiv:2610.21461v2](https://arxiv.org/abs/2610.21461), 5 Nov 2026) | $O\big(\sqrt{(L_0+L_1M)R^2/\varepsilon}+MR/\varepsilon+(1+q)\log(2+q)\big)$ → selected bound | Removes $MR/\varepsilon$. The gain is $\to\infty$ when $\varepsilon\ll M^2/(L_0+L_1M)$ and $\varepsilon\ll MR/((1+q)\log(2+q))$; otherwise the two have the same order | None (same class) | Reduction needs $R,\varepsilon$ in updates → not needed | $\psi$ values are needed; the reduction uses only $\nabla f$ and prox |
| Everest Thm 3.7 (special case $\psi\equiv0$, $M=0$ only) | $5\sqrt{L_0R^2/\varepsilon}+240(1+q)\log_2(64(1+q))+2$ → same order | None: same order on the overlap | Smooth → Lipschitz-composite | Updates need $R,\varepsilon$ → not needed | None on the overlap |

**Reduction check and mechanism.** I verified the smoothing reduction: the surrogate is $(L_0+L_1M+M^2/\varepsilon+\varepsilon/(2R^2),L_1)$-smooth, and its minimizer lies within $\sqrt3R$. That reduction keeps $MR/\varepsilon$. Li's method on the radius-only class pays $q^2$. I found no standard reduction that gets through the large-gradient region in $\tilde O(q)$ calls for composite problems. Proof ancestry: the centering $f-\langle\nabla f(x^*),\cdot\rangle$ appears already in Li et al. Everest supplies the weight rule, the enlargement $\Phi$ and the count of first-stage iterations. The new pieces are the bisection on the segment using $\psi$-secants without values of $f$, the exit threshold $5M+L_0/L_1$, and the restart into an existing backtracking method. Together these remove $R$ and $\varepsilon$ from the updates. I did not check the Lean proofs or run builds or audits.

**Search coverage (13 Nov 2026).** Sources searched: arXiv and the web for composite, proximal and $(L_0,L_1)$ accelerated work. I read Everest v2 (Thms 3.7 and 4.10, Def. 2.1, open questions; it treats only unconstrained smooth $f$), Li et al. App. B and its proof note, and the [Deng–Gao](https://arxiv.org/abs/2512.09720) and [Lobanov](https://arxiv.org/abs/2608.04884) papers; neither of those two is a composite $(L_0,L_1)$ competitor. Unverified: Yang et al. (JAMP 2026, ResearchGate only), Tyurin 2508.06884, the unmerged repository PR #155, and the correctness of Li et al.'s proof. The theorem was introduced in commit `2ad7d1fa` on 13 Nov 2026, after both Everest and Li et al.

Discrepancies with the companion note:
- It omits Li et al.
- Its claim to be the "first radius-only accelerated guarantee" holds only for the single-log transient. Li's bound already gives a radius-only guarantee once the explicit gap bound is plugged in.
- Li's span-respecting lower bound (Thm 4.5, instance $h=G^*|r|$) shows the $M$ in the leading term cannot be improved in the worst case over this class when $G^*=M$, for that restricted method family. The note does not mention this.

**Conclusion**

**Yes — on the radius-only Lipschitz-composite class, the proved total complexity is better than the checked composite baselines.**

The strongest prior composite guarantee is Li–Lai–An–Hu–Wen Thm B.1. On this class it needs an initial-gap bound that grows exponentially with $L_1R$, so it pays a quadratic transient:

| | calls |
|---|---|
| Li et al. (worst-case gap bound) | $\sqrt{(L_0+L_1M)R^2/\varepsilon}+(1+L_1R)[L_1R+\log(1/\varepsilon)]$ |
| this result | $\sqrt{(L_0+L_1M)R^2/\varepsilon}+(1+L_1R)\log(2+L_1R)$ |

The gain is a factor of about $L_1R/\log(L_1R)$ when the transient dominates. For example, with $L_0=L_1=M=\varepsilon=1$ and $R=q$, the cost is $q^2$ vs. $q\log q$. As $\varepsilon\to0$ the two coincide. Compared with smoothing $\psi$ and then applying Everest's smooth method, the result removes the term $MR/\varepsilon$. Its updates also do not need $R$, $\varepsilon$ or a gap bound.

The price is narrower scope: $\psi$ must be Lipschitz, constraints are excluded, and $\psi$ values are needed. When a small $\|\nabla f(x^*)\|$ is known, Li's leading term can be better. The literature search found no prior composite method with Everest's single-log transient, but priority within such a fast-moving month is not certain.

The claim that can be made: a composite extension of Everest's near-optimal radius-only bound that needs no smoothing and no gap bound. It brings a polynomial gain over Li et al. in the stated regime.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
