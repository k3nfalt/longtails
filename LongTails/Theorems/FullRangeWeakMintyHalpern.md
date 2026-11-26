# A value-only bound with margin power one for weak Minty root finding

For a fixed positive initial-distance bound and fixed smoothness and accuracy parameters, the guaranteed number of calls grows as $\delta^{-1}$ when the weak Minty margin $\delta$ tends to zero. The previous full-range theorem grows as $\delta^{-5}\log(1/\delta)$. A public choice between a value-only method and the existing second-order method preserves the smaller accuracy exponent of the latter when accuracy becomes demanding. [Theorem](FullRangeWeakMintyHalpern.lean) · [Algorithm](../Algorithms/FullRangeWeakMintyHalpern.lean)

## Setup and budget

On a finite-dimensional real inner-product space, $F$ is $L_1$-Lipschitz and its derivative is $L_2$-Lipschitz. Some zero $z$ satisfies $\|x_0-z\|\le R$ and $\langle F(x),x-z\rangle\ge-(\rho/2)\|F(x)\|^2$ for all $x$. Here $L_1,L_2,\varepsilon>0$, $R,\rho\ge0$ and $\rho L_1<2$. Each exact value or full Jacobian query costs one call. The output must satisfy $\|F(x_{\rm out})\|\le\varepsilon$ almost surely. The proof gives accuracy for every seed. [Setup](../Setups/WeakMintySecondOrder.lean)

Put $\delta=1-\rho L_1/2$, $T_1=L_1^2R^2/\varepsilon^2$, $T_2=L_2R^2/\varepsilon$, and define
\[
 K=\lceil2+32/\sqrt\delta\rceil,\qquad m=2K+3,\qquad H=2^{20}\log(2/\delta)/\delta^5.
\]
The algorithm compares the public coefficients $c_v=256mL_1^2/(\sqrt\delta\,\varepsilon^2)$ and $c_h=HL_2/\varepsilon$. Its budget is
\[
 N=\begin{cases}
 V=m(1+\lfloor256T_1/\sqrt\delta\rfloor), & c_v\le c_h,\\
 J=\lceil H(1+T_2)\rceil, & c_v>c_h.
 \end{cases}
\]
The first case uses only values. The second executes the existing hybrid. The selector, updates and certification tests use only public inputs and replies. The execution allowance depends on $R$. Both include calls made by the fixed-budget execution after certification.

## How the value queries give a separating half-space

Scale to $G=F/L_1$, $e=\varepsilon/L_1$, and put $t=\delta^{1/4}$. At an anchor $w$ query $b=G(w)$. For a center $c$, a solve starts at $u_0=c$ and sets $u_{j+1}=c-\frac{j+1}{j+2}G(u_j)$ for $0\le j<K$. It queries the endpoint $u_K$ as well. The first center is $c=w-b/2$. Write $y=u_K$ and $v=G(y)$. Use this endpoint if $t\|v\|\le\|b\|$. Otherwise solve again at $(w+2y)/3$ and use that endpoint. The anchor and each endpoint certify immediately upon passing the norm test.

For $S(u)=c-G(u)$, $h_j=u_j-c$ and $r_j=u_j-S(u_j)$, take $P_j=j\|r_j\|^2/2+\langle r_j,h_j\rangle$. Direct expansion gives
\[
 (j+2)P_{j+1}-(j+1)P_j
 =\tfrac{(j+1)(j+2)}2\big(\|G(u_{j+1})-G(u_j)\|^2-\|u_{j+1}-u_j\|^2\big)\le0 .
\]
Since $P_0=0$, Cauchy–Schwarz gives $K\|r_K\|\le2\|h_K\|$. Using $h_K=r_K-G(u_K)$ and the chosen $K$ gives $\|r_K\|\le(t^2/16)\|G(u_K)\|$. This argument requires no fixed point of $S$. [Residual proof](../Proofs/FullRangeWeakMintyHalpernResidual.lean)

For the selected trial $u$ with $f=G(u)$, define $d=\langle f,w-u\rangle/\|f\|-(1-\delta)\|f\|$. The nonterminal cases both give $d\ge t\|b\|/16$.

- **First endpoint.** Put $r=y-c+v$. Expanding $\|v-b\|^2\le\|y-w\|^2$ gives $d\|v\|\ge\delta\|v\|^2+\|b\|^2/8-2\langle v,r\rangle/3+\langle b,r\rangle/6-\|r\|^2/6$. Here $\|r\|\le t\|b\|/16$, so each of $\|v\|\|r\|$, $\|b\|\|r\|$, and $\|r\|^2$ is at most $\|b\|^2/16$. The absolute error weights sum to one. Thus $d\|v\|\ge\|b\|^2/16$.
- **Second endpoint.** Write $a=(w+2y)/3$ and $s=u-a+f$. The Lipschitz inequalities between $u$ and each of $w,y$, with weights $1/3,2/3$, give
  \[
  d\|f\|\ge\delta\|f\|^2+\|b\|^2/6+\|v\|^2/3-\|y-w\|^2/9-\|s\|^2/2-2\langle f,r\rangle/3 .
  \]
  Now $\|b\|<t\|v\|$, so $\|y-w\|\le25\|v\|/16$. The two terms involving $\|v\|^2,\|y-w\|^2$ leave at least $\|v\|^2/18$. The squared second error consumes at most $\delta\|f\|^2/2$. AM–GM on the two remaining squares gives $d\ge(t^2/3-t^2/16)\|v\|>t\|b\|/16$. No value at the average is inferred from $b,v$. [Geometry proof](../Proofs/FullRangeWeakMintyHalpernGeometry.lean)

Weak Minty places $z$ in $\{x:\langle f,x-u\rangle\le(1-\delta)\|f\|^2\}$. The correction $w^+=w-df/\|f\|$ projects $w$ onto its boundary. Squared distance to $z$ drops by at least $d^2>\sqrt\delta\,e^2/256$. At most $\lfloor256T_1/\sqrt\delta\rfloor$ updates can therefore finish. One additional attempt covers the certification, even at the second endpoint. Each attempt costs at most $1+2(K+1)=m$ values. The absorbing state keeps querying the certified point through budget exhaustion. If $R=0$, the first anchor already passes. [Execution proof](../Proofs/FullRangeWeakMintyHalpernExecution.lean)

## Exact comparisons

**Existing full-range theorem.** The new budget is strictly smaller precisely on $c_v\le c_h$, and equal everywhere else. Indeed $m<9+64/\sqrt\delta\le73/\sqrt\delta<H$, since $\delta^5\le\sqrt\delta$ and $\log(2/\delta)\ge\log 2>1/2$. In the value branch $V\le m+c_vR^2<H+c_hR^2\le J$. Also $V\le73/\sqrt\delta+18688T_1/\delta$. For fixed $L_1,L_2,\varepsilon$ the guard eventually selects values as $\delta\downarrow0$. Thus $N=\Theta(\delta^{-1})$ for fixed $R>0$, or $\Theta(\delta^{-1/2})$ for $R=0$, against $J=\Theta(\delta^{-5}\log(1/\delta))$. At fixed margin as $\varepsilon\downarrow0$ the selector eventually chooses the hybrid. [Existing theorem](FullRangeSecondOrderWeakMinty.lean) · [Budget inequalities](../Proofs/FullRangeWeakMintyHalpernBudget.lean)

**Earlier value-only contribution.** PR 264, outside this base commit, proves $A=1+\lfloor8T_1/\delta^2\rfloor$. For a given $(\delta,T_1)$ let $x=8T_1/\delta^2$. Exactly, $V<A$ if $x\ge V$, $V=A$ if $V-1\le x<V$, and $V>A$ if $x<V-1$. Thus no margin alone guarantees a smaller count for all radii. A strict gain is possible for some $T_1$, and occurs for every sufficiently large $T_1$, exactly when
\[
 32m\delta^{3/2}<1.
\]
This follows by comparing the two slopes and using $256mT_1/\sqrt\delta<V\le m+256mT_1/\sqrt\delta$. The crossover is near $4.87\cdot10^{-4}$. More precisely, writing $d_k=[32(2k+3)]^{-2/3}$, the slope inequality holds on $(0,d_{1453})\cup[(32/1450)^2,d_{1452})$. The three endpoints are approximately $0.00048686012$, $0.00048703924$, and $0.00048708340$. To check the ceiling effect, bound $m$ between $7+64/\sqrt\delta$ and $9+64/\sqrt\delta$. The transition is confined to $[0.00048677,0.00048711]$, where only $K=1453,1452$ occur. This is a boundary-regime improvement in order with large constants. [PR 264, theorem and selection rule](https://github.com/k3nfalt/longtails/pull/264)

For the two **selected** budgets, PR 264 takes $A$ when $8L_1^2/(\delta^2\varepsilon^2)\le c_h$, and $J$ otherwise. When both select values the preceding integer test applies. When both select the hybrid they tie. When exactly one selects values, that selector is strictly smaller, by $V<J$ under our guard and $A\le1+c_hR^2<J$ under theirs.

**Restricted-range results.** For $\rho L_1\le1$, put $D=\min(T_1,T_2)$. The repository's expected-norm upper bound is $\lceil2^{27}(1+D)\rceil$. On that overlap $\delta\ge1/2$, $H\le2^{25}\log4$, and $256m/\sqrt\delta\le37376$. Comparing the public slopes shows $N\le\lceil H+\min(37376T_1,HT_2)\rceil$, strictly below the restricted upper count everywhere. Both have order $1+D$ on this range. The related expected-norm lower theorem rules out $\lfloor D/2^{15}\rfloor$ calls when $D\ge2^{15}$, $R>0$, and dimension is at least $D^3$, even with public $R$. It supplies no lower bound growing as $\delta\downarrow0$. The repository therefore leaves the necessary margin dependence open. [Restricted upper bound](SecondOrderWeakMintyUpperBound.lean) · [High-dimensional lower bound](SecondOrderWeakMintyLowerBound.lean)

## Prior work and limitations

- Halpern's 1967 construction uses $x_{n+1}=k_{n+1}f(x_n)$ with anchor zero. His introduction on p. 957 identifies strong convergence as the conclusion of Theorem 3. Lieder's Theorem 2.1 and equations (1)–(2) give the $O(1/k)$ fixed-point residual with weights $1/(k+2)$. In fact his equation (12) already gives precisely the displacement-relative estimate used here, before introducing any fixed point in (13). Diakonikolas's Fact 1.2, iteration (H) and Lemmas 2.1–2.2 give the corresponding potential analysis for the cocoercive residual $I-S$. These are results about the inner map. [Halpern, 1967](https://doi.org/10.1090/S0002-9904-1967-11864-0) · [Original opening page](https://scispace.com/pdf/a-combinatorial-coincidence-problem-32bnhcj910.pdf) · [Lieder, 2021](https://www.econstor.eu/bitstream/10419/289042/1/s11590-020-01617-9.pdf) · [Diakonikolas, 2020](https://arxiv.org/pdf/2002.08872)
- Yoon and Ryu's extra anchored gradient Theorem 1 and Corollary 1 give squared last-gradient norm at most $260L_1^2R^2/(k+1)^2$ for the smooth convex–concave saddle problem. Two-point operator structure is also central to Lee and Kim's FEG and Cai, Oikonomou and Zheng's composite-FEG. With their signed comonotonicity constant set to $-\rho/2$ and step $1/L_1$, both Theorems 4.1 give residual norm at most $2L_1R/[(1-\rho L_1)k]$ on the unconstrained overlap. Their assumptions require a two-point inequality and $\rho L_1<1$. None of these rates covers the full one-point weak Minty range. [Yoon and Ryu, EAG-C and (4)](https://proceedings.mlr.press/v139/yoon21d/yoon21d.pdf) · [Lee and Kim, Algorithm 1 and (3)](https://arxiv.org/pdf/2106.02326) · [Cai, Oikonomou and Zheng, §4, 2022 preprint / ICML 2024](https://arxiv.org/pdf/2206.05248)
- Alacaoglu, Kim and Wright use the positive defect $r=\rho/2$. Their inexact Halpern Corollary 2.2 under two-point cohypomonotonicity gives $\widetilde O(L_1R/(\varepsilon\delta^2))$ first-order calls. For one-point weak Minty, Theorem 3.1 and Corollary 3.2 analyze inexact Krasnosel'skiĭ–Mann. Equation (B.16) gives an outer cost proportional to $R^2/[(\eta-r)^2\varepsilon^2]$, with additional inner cost proportional to $(1-\eta L_1)^{-1}$ up to logs. Taking $\eta=(r+1/L_1)/2$ gives $\widetilde O(T_1/\delta^3)$ near the boundary. The metric in (B.16) is a scaled resolvent residual. In the unconstrained case it equals $\|F\|$ at the exact resolvent point, and Remark 3.4 and Appendix B.5 discuss recovering approximate points. [Alacaoglu, Kim and Wright, ICML 2024](https://arxiv.org/html/2402.05071v2)
- Pethick, Mavrothalassitis and Cevher's corrected inexact proximal scheme (8), Theorem 5.5 and Corollary 6.3 cover one-point weak Minty over the full range with signed defect $-\rho/2$. Their accuracy is squared tangent residual, so use $\varepsilon^2$ here and set the set-valued term to zero. The corollary allows $\lceil6\log(3/\delta)/\delta\rceil$ inner steps. Reserving a fixed fraction of the margin in the outer denominator gives a comparable $O(T_1\delta^{-3}\log(2/\delta))$ value count near the boundary. [Pethick, Mavrothalassitis and Cevher, ICLR 2025, §6 and Appendix D](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf)
- Böhm's one-call OGDA+ also admits a full-range comparison from Theorem A.1, in this setup's half-defect convention. In equation (11) take $aL_1=1-\delta/4$, $p=\lambda\gamma=2-\delta$, and $\gamma=(2-p)(1-aL_1)/(1+aL_1)$. Then $(ap-\rho)L_1=\delta/2+\delta^2/4$, and $\gamma$ is of order $\delta^2$. The numerator is at most $(1+aL_1)^2 R^2$ by Lipschitzness at the zero. Substitution into the displayed bound gives $O(T_1/\delta^3)$ values to reach a small residual. [Böhm, Algorithm 1, Theorem A.1 and (11)](https://arxiv.org/pdf/2201.12247)
- The projection has a classical precedent in Solodov and Svaiter's Algorithm 2.1 and Theorem 2.1. Their condition (1.2) places solutions in the trial half-space under nonnegative Minty. Here the boundary shifts by the permitted negative defect. Pethick, Mavrothalassitis and Cevher, cited above, already use such a shifted weak-Minty half-space. The repository hybrid likewise uses weak Minty to control a correction in the trial-value direction. The two-center construction above ensures a sufficient distance to the separating half-space using only values. [Solodov and Svaiter, 1999](https://pages.cs.wisc.edu/~solodov/solsva99proj.pdf) · [Hybrid proof](../Proofs/WeakMintyHybridBounds.lean)

The comparison covers the base repository, PR 264 and the primary works cited above. The result concerns exact oracle calls, with large constants near the boundary. The value method needs $L_1,\rho,\varepsilon$ and $x_0$, and the selector additionally needs $L_2$. Arithmetic cost, noisy queries and optimality of the margin exponent remain open here.
