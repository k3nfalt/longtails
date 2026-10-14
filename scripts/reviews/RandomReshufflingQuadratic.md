# Random reshuffling for indefinite quadratic finite sums: novelty assessment

[`QuadraticFiniteSum.result`](../../LongTails/Theorems/RandomReshufflingQuadratic.lean) proves that the final endpoint of plain random reshuffling, with one independent uniform permutation per epoch, a constant step, and no averaging or restarts ([algorithm](../../LongTails/Algorithms/QuadraticReshuffling.lean)), satisfies $\mathbb E[F(y_K)]-F(x_*)\le\varepsilon$. Here $F=\frac1n\sum_i(\frac12\langle x,A_ix\rangle+\langle b_i,x\rangle)$ on a real Hilbert space ([setup](../../LongTails/Setups/QuadraticFiniteSum.lean)), each $A_i$ is self-adjoint with $\|A_i\|\le L$, and $\bar A\succeq\mu I$; components may be indefinite. The algorithm is given $n,L,\mu,R,G,\varepsilon$, and each oracle call returns $A_ix+b_i$ exactly.

**Parameters:** $n$ is the number of components; $R\ge\|x_0-x_*\|$; $G\ge\max_i\|A_ix_*+b_i\|$ bounds heterogeneity at the optimum; $\varepsilon$ is the target expected objective gap. The proved budget $n\lceil(\cdot)\log(1+LR^2/\varepsilon)\rceil$ gives

$$O\!\left(n+\Big[\tfrac{nL}{\mu}+\tfrac{L^{3/2}G}{\mu^{2}\sqrt\varepsilon}+\big(\tfrac{n^{2}L^{3}G^{2}}{\mu^{4}\varepsilon}\big)^{1/3}\Big]\log\!\Big(1+\tfrac{LR^{2}}{\varepsilon}\Big)\right)$$

component-gradient calls. The budget is deterministic, and there are zero calls when $R=0$. Below, $\ell=\log(1+LR^2/\varepsilon)$ and $\varepsilon<LR^2$.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Nesterov AGD on $F$, [Bubeck 2015, Thm. 3.18](https://arxiv.org/pdf/1405.4980) (direct competitor) | $O(n+n\sqrt{L/\mu}\,\ell)$ → $O(n+[\frac{nL}{\mu}+\frac{L^{3/2}G}{\mu^2\sqrt\varepsilon}+(\frac{n^2L^3G^2}{\mu^4\varepsilon})^{1/3}]\ell)$ | Worse: slower by a factor of at least $\sqrt{L/\mu}$ in every regime, even when $G=0$, plus the $G$ terms | None: AGD needs only $\bar A$ to be $L$-smooth and $\mu$-strongly convex | None. AGD's final-iterate gap is deterministic, not just in expectation, and AGD does not need $G$ | AGD forms full gradients from exactly $n$ component calls each and uses momentum; it needs no other oracle |
| Katyusha X, [Allen-Zhu, arXiv 1802.03866v1 (2018)](https://arxiv.org/pdf/1802.03866v1), Cor. 4.4 with $b=1$, $\ell_1=\ell_2=L$ (direct competitor, finite-dimensional overlap) | $O((n+n^{3/4}\sqrt{L/\mu})\,\ell)$ expected calls → same as above | Worse: since $n^{3/4}\sqrt{L/\mu}\le nL/\mu$, Katyusha X is at least as good up to constants in every regime | Finite dimension → Hilbert space (formal only; neither proof uses dimension) | Expected call count → deterministic budget | Katyusha X uses SVRG snapshots, random epoch lengths and momentum; it needs $\mu$ |
| Ahn–Yun–Sra, [NeurIPS 2020; arXiv v2](https://arxiv.org/pdf/2006.06946v2), Thm. 2, App. B, Lemmas 6–8 (special-case baseline: same algorithm) | $O(n+[\frac{nL}{\mu}\max\{1,\sqrt{\frac{L}{n\mu}}\}+\frac{L^{3/2}G}{\mu^2\sqrt\varepsilon}+(\frac{n^2L^3G^2\log n}{\mu^4\varepsilon})^{1/3}]\ell)$ → this result | Factor $\sqrt{L/(n\mu)}$ on the transient when $L>36n\mu$ and $G\le n\mu\sqrt{\varepsilon/L}$; also removes a $(\log n)^{1/3}$ factor | None: same class and oracle | None: both bound the final endpoint | None relative to this baseline |

The Ahn row follows from their admissible step bound, $\eta\lesssim(nL)^{-1}\min\{1,\sqrt{n\mu/L}\}$ (Thm. 2's epoch requirement), and their distance bound with noise terms $640\eta^2L^2G^2/\mu^2+36\eta^3n^2L^2G^2\log n/\mu$. Multiplying by $L/2$ converts distance to objective gap.

**Reduction check.** The class needs no component convexity, only an $L$-smooth, $\mu$-strongly convex average, so AGD applies verbatim. That reduction already dominates the result without any rescaling trick. The genuinely new mechanism is the [collision-energy bound](../../LongTails/Proofs/ReshufflingHomogeneousEnergy.lean) on the reshuffled Gram product, giving mean-square stability at $\eta nL\le1/32$. Ahn–Yun–Sra's palindromic expansion and [Peng, §4.2, Lemma 7](https://arxiv.org/html/2607.22620) are proof ancestry. Neither is a complexity baseline.

**Search coverage (2026-10-07 UTC).** I read the theorem statements in Bubeck, Katyusha X, Ahn–Yun–Sra, and [Li, arXiv 2609.04578v1 (2026-09-04)](https://arxiv.org/pdf/2609.04578v1). Li predates this result, which was introduced in commit `b71dbcf` on 2026-09-29, but requires $n\eta\le\mu/(32L^2)$. The literature searches also covered recent reshuffling preprints. Mishchenko–Khaled–Richtárik's $1/(nL)$ steps assume convex components and were not re-read here. I found no prior result with this exact random-reshuffling stability radius, so the method-specific priority looks plausible but is not established. The companion note correctly states that acceleration is faster. Its framing of the result as an "improved" bound is valid only relative to other analyses of reshuffling.

**Conclusion**

**No: the result does not improve the complexity of solving this problem class; it is a sharper analysis of one particular method.** The strongest relevant baseline is plain Nesterov acceleration on the average, which applies because the average is smooth and strongly convex, even though individual components are indefinite.

$$\underbrace{O\big(n+n\sqrt{L/\mu}\,\ell\big)}_{\text{AGD, deterministic}}\quad\text{vs.}\quad \underbrace{O\big(n+[\,nL/\mu+\text{$G$-terms}\,]\,\ell\big)}_{\text{this result, in expectation}}$$

The selected bound is larger by at least $\sqrt{L/\mu}$ in every regime, including $G=0$. Katyusha X's $O((n+n^{3/4}\sqrt{L/\mu})\ell)$ expected calls is better still. The setup, the required parameters (it additionally needs $G$), and the final-iterate output give no compensating advantage.

The comparison does show a real gain over Ahn–Yun–Sra's analysis of the same reshuffling method: a factor of $\sqrt{L/(n\mu)}$ on the transient when $L>36n\mu$ and heterogeneity is low. The stability argument behind it may be new, but the literature search alone does not establish priority. The claim that can actually be made is a better convergence guarantee for random reshuffling on indefinite quadratics, not a better optimization guarantee for the class.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
