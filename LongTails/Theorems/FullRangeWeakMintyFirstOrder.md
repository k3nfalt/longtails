# Full-range weak Minty root finding with a value-only branch

Let $F$ act on a finite-dimensional real inner-product space. The operator is $L_1$-Lipschitz, its derivative is $L_2$-Lipschitz, and some zero $z$ satisfies $\|x_0-z\|\le R$ and $\langle F(x),x-z\rangle\ge-(\rho/2)\|F(x)\|^2$ everywhere. Put $\delta=1-\rho L_1/2\in(0,1]$, $T_1=L_1^2R^2/\varepsilon^2$, $T_2=L_2R^2/\varepsilon$, and $H=2^{20}\log(2/\delta)/\delta^5$. The theorem certifies $\|F(\mathrm{output})\|\le\varepsilon$ for every execution seed, hence almost surely, within
\[
\begin{cases}
\lfloor 8T_1/\delta^2\rfloor+1, &
  8L_1^2/(\delta^2\varepsilon^2)\le H L_2/\varepsilon,\\
\lceil H(1+T_2)\rceil, & \text{otherwise}.
\end{cases}
\]
oracle calls. A value and a full Jacobian each cost one call. The first case uses only values and includes ties. The second runs the existing hybrid. Both the comparison and the updates use public inputs. The algorithm does not receive $R$. The bound uses it through the initial-distance assumption. [Setup](../Setups/WeakMintySecondOrder.lean) · [Theorem](FullRangeWeakMintyFirstOrder.lean)

The earlier full-range budget is $\lceil H(1+T_2)\rceil$. In the first case, multiplying the public comparison by $R^2$ gives $8T_1/\delta^2\le HT_2$. Since $0<\delta\le1$ gives $H\ge2^{20}\log 2>1$,
\[
\lfloor 8T_1/\delta^2\rfloor+1\le HT_2+1\le\lceil H(1+T_2)\rceil.
\]
In the second case the budgets are equal. [Existing full-range theorem](FullRangeSecondOrderWeakMinty.md)

For every $\delta$, the first case holds exactly when $L_1^2/\varepsilon\le2^{17}L_2\log(2/\delta)/\delta^3$. Along any family in this case the total budget is smaller in order precisely when $8T_1/\delta^2+1=o(H(1+T_2))$. For fixed positive $L_1,L_2,R,\varepsilon$ as $\delta\to0$, the first case eventually holds and the budgets have orders $\delta^{-2}$ and $\delta^{-5}\log(1/\delta)$, respectively. At fixed $R=0$ the eventual value budget is one call. For example, fixing public parameters at equality in the selector and sending $R\to\infty$ makes the ratio of the budgets tend to one.

On $\rho L_1\le1$, the repository already gives $\lceil2^{27}(1+\min\{T_2,T_1\})\rceil$ for the expected residual. Here $\delta\ge1/2$, so the parameter orders on that overlap agree. The corresponding expected-residual lower bound is $\lfloor\min\{T_2,T_1\}/2^{15}\rfloor$ in dimension at least $\min\{T_2,T_1\}^3$, for $\min\{T_2,T_1\}\ge2^{15}$, positive radius, and public $R$. It supplies no lower bound on the cost of approaching $\delta=0$. [Restricted upper theorem](SecondOrderWeakMintyUpperBound.lean) · [High-dimensional lower setup](../Setups/HighDimensionalWeakMintySecondOrder.lean) · [Lower theorem](SecondOrderWeakMintyLowerBound.lean)

## The value iteration and its certificate

Set $G=F/L_1$, $b=\delta/4$, $a=1-b$. Starting at $(y,h)=(x_0,0)$, query $F(y)$. A passing residual freezes the state. After a failed test set $g=G(y)$ and replace $(y,h)$ with $(y-g+ah,g)$. Thus each step of this past-extragradient (Popov or optimistic gradient) method uses one new value. In the anchor coordinate $p=y+ah$, the update is the short step $p'=p-bg$. The actual execution keeps querying the certified point until its allotted budget is exhausted. Those repeated calls and the first successful test are included. [Algorithms](../Algorithms/FullRangeWeakMintyFirstOrder.lean)

For $u=y-z$ use $V=\|u+ah\|^2+\|g-h\|^2-2ab\|h\|^2$. Since $G$ is nonexpansive and $G(z)=0$, $\|g\|\le\|u\|$. Write $C=1+a^2-2ab>0$. Expanding the square gives
\[
CV=\|Ch+au-g\|^2+(1-2ab)(\|u\|^2-\|g\|^2)
+2a(\langle g,u\rangle+(1-\delta)\|g\|^2)+(b^2+4ab)\|g\|^2.
\]
Every term is nonnegative. Initially $V\le2R^2$. For $y'=y-g+ah$ and $v=G(y')$, expanding $V'-V$ gives
\[
V'-V+\tfrac{\delta^2}{4}\|g\|^2+b^2\|g-h\|^2
=\|v-g\|^2-\|ah-g\|^2-2b(\langle g,u\rangle+(1-\delta)\|g\|^2)\le0.
\]
The two signs follow from nonexpansiveness and weak Minty. Thus $k$ failed queries spend at least $k\delta^2\varepsilon^2/(4L_1^2)$ of the initial potential. At $k=\lfloor8T_1/\delta^2\rfloor+1$ this exceeds $2R^2$, so one of those calls certifies. For $R=0$ the initial call certifies. The hybrid branch reuses the existing execution bound, including its inner and terminal calls. [Proof](../Proofs/FullRangeWeakMintyFirstOrder.lean)

## Prior work and limitations

- Diakonikolas, Daskalakis and Jordan’s EG+ Theorem 3.2 bounds the best squared residual with a factor $2L/(1/(4L)-\rho)$, in the same half-defect convention as this setup. It uses two evaluations per extragradient iteration and requires $\rho L<1/4$. [AISTATS 2021, Theorem 3.2](https://proceedings.mlr.press/v130/diakonikolas21a/diakonikolas21a.pdf)
- Pethick, Latafat, Patrinos, Fercoq and Cevher use a signed coefficient $r=-\rho/2$. For their constant-step CEG+, Corollary 3.2 with $\gamma=1/L$ and relaxation $(1+2rL)/2$ gives a squared margin penalty $(1-\rho L)^{-2}$ on $\rho<1/L$ in the positive half-defect convention. Their own threshold is $r>-1/(2L)$. CurvatureEG+ also adapts the extrapolation step to local curvature, which can permit larger steps on individual instances. [ICLR 2022, §§3–4](https://openreview.net/pdf?id=2_vhkAMARk)
- Böhm’s OGDA+ is the same recurrence in one current value and one stored value after initialization, with previous-value coefficient $s=a/L_1$ and relaxation $\gamma=b/a$. The paper initializes the previous value at $F(x_0)$, and its initial factor is bounded through the common radius by $\|x_0+sF(x_0)-z\|\le(1+sL_1)R\le2R$. Theorem 3.1 gives the factor $1/[s\gamma(s-\rho)]$ for $\rho L<1$. Its more general Theorem A.1 deserves a separate comparison. Write $t=\lambda\gamma$ and $q=sL$. Its constraints read $qt>\rho L$, $t\le2$ and $\gamma\le(2-t)(1-q)/(1+q)$. Near $\rho L=2(1-\delta)$ they imply $2-t=O(\delta)$, $1-q=O(\delta)$, $\gamma=O(\delta^2)$ and $qt-\rho L=O(\delta)$. Conversely $t=2-\delta$, $q=1-\delta/4$ and equality in the stepsize constraint give a positive gap of order $\delta$ and $\gamma$ of order $\delta^2$. Thus our reading of the appendix already gives single-call full-range coverage, with a cubic inverse-margin penalty in its displayed factor $1/[s\gamma(st-\rho)]$. The quadratic dependence here improves that bound. [Böhm, 2022 preprint, Theorems 3.1 and A.1](https://arxiv.org/pdf/2201.12247)
- Alacaoglu, Kim and Wright cover the full range for weak Minty through inexact Krasnosel’skiĭ–Mann iteration. With their defect $r=\rho/2$ and $r<\eta<1/L$, the squared resolvent residual has outer factor $(\eta-r)^{-2}$. Their first-order call bound includes $(1-\eta L)^{-1}$ and inner logarithms. Taking $\eta$ halfway between $r$ and $1/L$ gives a cubic inverse-margin cost up to logarithms. Their unconstrained output conversion is discussed in Remark 3.4 and Appendix B.5. [ICML 2024, Section 3](https://arxiv.org/html/2402.05071v2)
- Pethick, Mavrothalassitis and Cevher likewise cover the full range. For their corrected inexact proximal scheme, Corollary 6.3 bounds the inner count by $\lceil6\log(3/\delta)/\delta\rceil$. Together with the squared outer margin factor, the comparable bound on value calls is of order $T_1\delta^{-3}\log(2/\delta)$ near the boundary. Their accuracy parameter bounds a squared residual. [ICLR 2025, Theorem 5.5 and Corollary 6.3](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf)

These comparisons identify no earlier bound combining one fresh value per step, this full range and the quadratic inverse-margin cost. They establish no general priority or optimality. The hybrid branch retains $\delta^{-5}\log(2/\delta)$. The value-only argument uses neither differentiability nor the derivative Lipschitz constant, although the combined theorem assumes both. The result concerns exact queries and residual certification. Arithmetic costs, noisy evaluations and the optimal margin exponent remain open here.
