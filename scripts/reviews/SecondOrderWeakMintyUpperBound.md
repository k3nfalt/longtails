# Novelty assessment: SecondOrderWeakMintyUpperBound

The [theorem](../../LongTails/Theorems/SecondOrderWeakMintyUpperBound.lean) proves the following. Let $F$ be an operator on a finite-dimensional Euclidean space with $L_1$-Lipschitz $F$ and $L_2$-Lipschitz Jacobian, and suppose it satisfies weak Minty $\langle F(x),x-x^\star\rangle\ge-\frac\rho2\|F(x)\|^2$ with $0\le\rho L_1\le1$ ([setup](../../LongTails/Setups/WeakMintySecondOrderExpected.lean)). The existing [`WeakMintyHybrid`](../../LongTails/Algorithms/WeakMintyHybrid.lean) method then returns a point with $\|F(x_{\rm out})\|\le\varepsilon$ for every seed, so also in expectation. It uses exact value and full-Jacobian calls, and it receives $L_1,L_2,\rho,\varepsilon,x_0$ but not $R$.

**Complexity** (budget $\lceil 2^{27}(1+\min\{\cdot\})\rceil$, with value and Jacobian calls counted together):
$$O\Big(1+\min\Big\{\tfrac{L_2R^2}{\varepsilon},\ \tfrac{L_1^2R^2}{\varepsilon^2}\Big\}\Big).$$
Here $R\ge\|x_0-x^\star\|$ and $\varepsilon$ is the target residual. There is no logarithm, and the dimension is unrestricted.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Pethick–Mavrothalassitis–Cevher, [ICLR 2025](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf), Thm 6.1(ii), Cor 6.3 (first-order, weak MVI with $\rho_P>-1/L$, i.e. repo $\rho L<2$; accuracy in the squared residual) | $O(1+L_1^2R^2/\varepsilon^2)$ → $O(1+\min\{L_2R^2/\varepsilon,L_1^2R^2/\varepsilon^2\})$ | Better only for $\varepsilon< L_1^2/L_2$, by a factor of $L_1^2/(L_2\varepsilon)$. Same order otherwise | None. Their class (no Jacobian assumption, maximally monotone $A$ allowed, $\rho L<2$) is broader | None (both use a best/stopped certified point and the same known parameters) | Needs $L_2$-Lipschitz Jacobian, full-Jacobian queries, an exact cubic-subproblem root by choice, unconstrained, $\rho L_1\le1$ |
| Repository [FullRangeSecondOrderWeakMinty](../../LongTails/Theorems/FullRangeSecondOrderWeakMinty.lean) (commit 85dcf517, 2026-10-16; same algorithm, $\rho L_1<2$, a.s. residual) | $\lceil2^{20}(1+L_2R^2/\varepsilon)\log(2/\delta)/\delta^5\rceil$, with $\delta=1-\rho L_1/2\ge\tfrac12$, i.e. $O(1+L_2R^2/\varepsilon)$ → selected bound | Better only for $\varepsilon>L_1^2/L_2$, by a factor of $L_2\varepsilon/L_1^2$ | None. Range narrowed from $\rho L_1<2$ to $\le1$ | Almost-sure → expected residual is a weaker criterion; the output is the same | Range restricted to $\rho L_1\le1$ |
| Vyas–Bullins, [arXiv:2304.08389v1](https://arxiv.org/abs/2304.08389v1), Thm 3.5, App. B.1 (second-order, standard weak Minty) | $O(1+L_2R^2/\varepsilon)$ under trajectory-scale smallness of $\rho$ → selected bound | Same first-regime gain as the row above | Removes trajectory smallness. That removal is inherited from FullRange, not new here | None | None beyond the rows above |

**Standard-reduction check.** The minimum is a regime switch that depends only on the known quantities $\varepsilon$ vs $L_1^2/L_2$, because $\min\{L_2R^2/\varepsilon,L_1^2R^2/\varepsilon^2\}=\frac{R^2}{\varepsilon}\min\{L_2,L_1^2/\varepsilon\}$ does not involve $R$. So the bound follows by composing known theorems. Run the ICLR 2025 method when $\varepsilon\ge L_1^2/L_2$, and the FullRange hybrid otherwise. On $\rho L_1\le1$ ($\rho_P\ge-1/(2L)$), Cor 6.3's inner count $n$ and its constants stay bounded, and FullRange's $\delta$-factors are at most $32\log4$. The one new ingredient is `fallback_progress_residual`, a per-attempt decrease of $\delta^2\varepsilon^2/(256L_1^2)$. It lets the single hybrid method achieve both regimes without an explicit switch. That is a convenience, not a gain in complexity. Proof ancestry: the relaxed inexact-proximal Picard correction comes from Pethick et al. 2025 (§6.2–6.3), and the cubic certificate and charging argument from the FullRange proof. Earlier first-order baselines: CEG+ ([Pethick et al., ICLR 2022](https://arxiv.org/abs/2302.09831), Thm 3.1, $\gamma\in(\{-2\rho_P\}_+,1/L]$) blows up as $\rho L_1\to1$, and EG+ (Diakonikolas–Daskalakis–Jordan, AISTATS 2021) covers only $\rho_P>-1/(8L)$. Neither changes the comparison.

**Search coverage** (2026-11-19). I read the theorem statements of Pethick et al. 2022 Thm 3.1 and 2025 Thm 6.1/Cor 6.3 from the PDFs. Vyas–Bullins, Perseus ([Lin–Jordan](https://arxiv.org/abs/2205.03202), Minty $\rho=0$, bounded domain, $O(\varepsilon^{-1})$ for $p=2$) and the inexact-Jacobian work (Agafonov et al., NeurIPS 2024) were checked only through the repository notes and abstracts. I did not re-derive an explicit universal constant for Cor 6.3. The companion note agrees that neither regime's rate is new. Its stated contribution is the single expression matching the paired lower bound, which is a contribution of the lower bound and is outside this assessment. I did not find a published weak-Minty second-order bound that removes the trajectory restriction, so that historical gain remains with the repository's FullRange theorem.

**Conclusion**

**No: this theorem takes the better of two existing bounds and does not improve either one.** Write $\varepsilon$ for the target residual. The strongest first-order baseline (Pethick et al., ICLR 2025, Cor 6.3) and the repository's earlier second-order theorem already give these bounds on the same weak-Minty class:

| regime | known bound | this theorem |
|---|---|---|
| $\varepsilon\ge L_1^2/L_2$ | $O(1+L_1^2R^2/\varepsilon^2)$ (first-order) | same |
| $\varepsilon< L_1^2/L_2$ | $O(1+L_2R^2/\varepsilon)$ (FullRange) | same |

The threshold between the two regimes involves only parameters the algorithm already knows. So running the appropriate known method reproduces the stated bound exactly, with no extra logarithm and no dependence on $R$.

The proof does show something new about method design: the single hybrid method reaches both regimes without an explicit switch. However, its setup is narrower ($\rho L_1\le1$ instead of $<2$), and its expected-residual criterion is weaker than the earlier almost-sure one. What can be claimed is the upper half of a $\Theta(\min\{L_2R^2/\varepsilon,L_1^2R^2/\varepsilon^2\})$ characterization; any novelty there comes from the paired lower bound. The upper bound itself is a straightforward combination of known results.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
