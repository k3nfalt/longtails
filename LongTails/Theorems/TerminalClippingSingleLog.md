# Single-logarithm confidence for the last clipped iterate

For the unchanged [TerminalClippingConvex setup](../Setups/TerminalClippingConvex.lean), put $q=\log(8/\delta)$ and $M^2=G^2+16B^2R^2$. The algorithm returns a feasible last iterate with objective gap at most $\varepsilon$ with probability at least $1-\delta$. Its total oracle allowance is

$$
N=\begin{cases}
0 & GR\le\varepsilon,\\
2\lceil 576 R^2 M^2 q/\varepsilon^2\rceil & GR>\varepsilon .
\end{cases}
$$

The domain $X$ is closed and convex in finite-dimensional Euclidean space. The objective $f$ is measurable and convex on $X$. There is a minimizer $u$ within $R$ of the feasible starting point $x_0$. At every feasible $x$, the mean sample is a subgradient relative to $X$, and the full second moment is bounded by $G^2+B^2\|x-x_0\|^2$. The sample seeds are IID. Each subgradient query evaluates the jointly measurable oracle at the query point with its fresh seed. Projection replies are exact. The public parameters satisfy $B,G,\varepsilon>0$, $R\ge0$, and $0<\delta<1$. The zero-call test follows by applying the subgradient inequality at $x_0$ and bounding the mean norm by $G$.

## Update and proof

In the positive-budget branch set $T=N/2$. For $t=1,\ldots,T$ use $\eta_t=R(T-t+1)/(12MT\sqrt{Tq})$ and $C=M\sqrt{T/q}$. Query the sample $g_t$ at $x_{t-1}$, then query the projection of $x_{t-1}-\eta_t\operatorname{clip}_C(g_t)$ onto $X$. The projection reply is $x_t$. Both parameters are fixed before sampling. Numbering calls from zero, the even calls supply the stochastic samples. The final projection exhausts the allowance and supplies the output.

For the analysis, project onto $K=X\cap\overline B(x_0,4R)$ with the same samples. On $K$ the moment bound is $M^2$, so the subgradient inequality bounds objective differences by $M$ times distance. Write $m$ for the number of updates remaining, $r=R/T$ and $k=r/(12M\sqrt{Tq})$. Starting with comparator $z=u$, mix each new point $y'$ into the comparator as $z'=((m-1)z+2y')/(m+1)$. At the last update $z'=y'$. Convexity and the projection inequality control $\|y'-z\|^2/[m(m+1)]+k(f(z')-f(u))$. Replacing its distance term by the next starting energy can only decrease it.

Two exponential estimates control every prefix up to $T$. One controls squared clipped norms. The other controls the centered inner products with the predictable direction $2k(y-z)/(m+1)$, clipped in the proof at $b=3kr$. Freezing each accumulated sum at its first threshold crossing gives failure probability at most $e^{-q}$ per estimate. The clipping bias has norm at most $M^2/C$. On the joint event, induction bounds the energy plus the comparator gap by $2r^2$, so the direction clipping preserves each direction encountered. The same induction bounds each comparator displacement by $2.9r$ and keeps every localized output strictly inside the ball. Testing the localized projection inequality on short segments toward points in $X$ then identifies each projection with the actual oracle reply. In particular, for any $T\ge1$ and $R\ge0$ (at zero radius every iterate equals the minimizer),

$$
\Pr\{f(x_T)-f(u)>24RM\sqrt{q/T}\}\le 2e^{-q}=\delta/4.
$$

Squaring gives the displayed coefficient $576$. The public budget names $W=M^2$. Keeping this scale avoids the relaxation $M^2\le16(G^2+B^2R^2)$ and its larger coefficient $9216$.

## Repository comparisons

- **Restricted last iterate.** Write $V=G^2+B^2R^2$. The published count is $2\max(1,\lceil O\rceil)$ with $O=2^{40}(V/B)^2q^2/\varepsilon^2$. It is at least two on the zero branch. On the positive branch write $A=576 R^2 M^2 q/\varepsilon^2$. Here $A>1$, $(V/B)^2\ge R^2V$, and $M^2\le16V$. Thus $O/A\ge2^{40}q/9216>2$, giving $O>A+1$. The new integer budget is strictly smaller for every valid input. Substituting $b=\max(B,G/R)$ in the earlier theorem already controls $bR^2+G^2/b\le2bR^2$ for $R>0$. The gain over that retuning is the single power of the confidence logarithm and the explicit constant. [ClippedBgLastIterate](ClippedBgLastIterate.lean)
- **Unrestricted averaged upper bound.** On the common range $B,G,R>0$ the zero branches agree. Otherwise the averaged method uses $2\lceil U\rceil$ calls with $U=1024R^2Vq/\varepsilon^2$. Before rounding $A/U=(9/16)M^2/V$, below one exactly when $G^2>(128/7)B^2R^2$. Including rounding, the last-iterate budget is smaller if $A\le\lceil U\rceil-1$, equal if $\lceil U\rceil-1<A\le\lceil U\rceil$, and larger if $A>\lceil U\rceil$. The averaged construction can apply an additional arithmetic ball projection and return an average. [DistanceGrowingSubgradientUpperBound](DistanceGrowingSubgradientUpperBound.lean)
- **Unrestricted lower bound.** On the overlap $d\ge2,\ B,G,R,\varepsilon>0,\ 65536\varepsilon\le GR,\ 0<\delta\le1/8$, failure can be forced through $\lfloor H\rfloor$ calls, $H=R^2V\log(1/\delta)/(2^{28}\varepsilon^2)$. Its whole-space smooth interpolating hard instances fit the present oracle model, and hardness for unrestricted algorithms covers this family. The exact pre-rounding ratio $2A/H$ is $1152\cdot2^{28}(M^2/V)q/\log(1/\delta)$, at most $1152\cdot2^{33}$ on the overlap. Thus the powers of radius, moment scale, inverse accuracy and confidence logarithm agree there. The integer endpoints are $2\lceil A\rceil$ and $\lfloor H\rfloor$. The lower theorem supplies no corresponding constant comparison outside its parameter regime. [DistanceGrowingSubgradientLowerBound](DistanceGrowingSubgradientLowerBound.lean)

## Prior work and limitations

Harvey, Liaw, Plan and Randhawa give the general Lipschitz convex last-iterate comparison in Remark 3.7. Their displayed high-probability gap scales as $\log(T)\log(1/\delta)/\sqrt T$ for their SGD schedule. Liu and Zhou, Theorem 3.5, use known-horizon linear decay with a sub-Gaussian noise assumption and obtain a square-root confidence logarithm in the noise term. Their finite central moment result, Theorem 5.3, bounds the expected terminal gap. In Euclidean geometry their initial Bregman divergence is half the squared initial distance. [Harvey et al.](https://proceedings.mlr.press/v99/harvey19a/harvey19a.pdf) · [Liu and Zhou](https://arxiv.org/html/2312.08531v4)

Vaidyan, Alacaoglu and Friedlander, Theorem 3.5(i), explicit estimate (A.10) and Remark 3.6, analyze known-horizon proximal and projected SGD under a second moment growing from initialization. Their expected gap is of order $(BR^2+G^2/B)/\sqrt{T+1}$. Direct Markov conversion divides that gap by $\delta$. Chezhegov et al., Theorem 1 and Corollary 1, analyze horizon-independent clipping schedules for smooth objectives with a uniform central moment bound. At moment order two their stochastic term decays as $K^{-1/3}$ up to logarithms. Corollary 1 uses failure probability $2\delta_{\rm paper}$, giving $\log^2(12(K+1)^2/\delta)$ after translating confidence. [Vaidyan et al.](https://arxiv.org/html/2611.07334v1#S3) · [Chezhegov et al.](https://openreview.net/pdf/284a6b25e148c2bea0d5b374894ef55d5c330a26.pdf)

Jiang, Bai and Li state Theorem 2 for a globally Lipschitz convex objective with a uniform central noise moment. To apply their proof here, take $R>0$, use the indicator of the compact set $K=X\cap\overline B(x_0,4R)$ as the regularizer, and write $h(y)$ for the oracle mean. Extend the objective to the whole space by
$$
\widetilde f(x)=\sup_{y\in K}\{f(y)+\langle h(y),x-y\rangle\}.
$$
The relative subgradient inequality gives $\widetilde f=f$ on $K$. Each affine support has slope of norm at most $M$, so equality at $x_0$ makes the supremum finite everywhere and globally $M$-Lipschitz. It is convex, and the support attaining equality at each $y\in K$ gives $h(y)\in\partial\widetilde f(y)$. On $K$ the centered second moment is bounded by the full second moment $M^2$. Thus the paper's indicator-proximal update projects onto $K$ with $p=2$ and both its Lipschitz and noise bounds set to $M$. [Jiang, Bai and Li, Theorem 2](https://arxiv.org/html/2610.18555v1#S3.SS1)

Write $x_1$ for the starting point in the paper's indexing. On the event in Appendix C.3, (25), (55) and (63) give, simultaneously for $1\le s\le T$ and $m=T-s+1$,
$$
P_s=\frac{\|x_{s+1}-z_s\|^2}{m(m+1)}<\frac{2R^2}{T^2}.
$$
For $s<T$, (25) gives $z_{s+1}-z_s=2(x_{s+1}-z_s)/(m+1)$, of norm at most $2\sqrt2 R/T$. Summing from $z_1=u$ and using $\|x_{s+1}-z_s\|\le(m+1)\sqrt2 R/T$ yields
$$
\|x_{s+1}-x_1\|\le R+[2(s-1)+(m+1)]\sqrt2 R/T\le(1+2\sqrt2)R<4R.
$$
At each such interior output, the projection variational inequality on $K$ extends along short segments toward every point of $X$. Hence projection onto $X$ gives the same output, and induction with the same seeds couples the two trajectories through the final update. [Appendix A.2](https://arxiv.org/html/2610.18555v1#A1.SS2) · [Appendix C.3](https://arxiv.org/html/2610.18555v1#A3.SS3)

For $\ell=\log(4/\delta)$ and $T\ge4\ell$, (7) sets $\lambda=M\sqrt{T/\ell}$, $H=M\sqrt T+\lambda\ell$ and $\eta=R/(128H)$, with step $\eta_s=\eta(T-s+1)/T$. With this tuning, (8) and the localization above bound the last-iterate gap by $256RH/T=256RM(1+\sqrt\ell)/\sqrt T$ with probability at least $1-\delta$ for the restricted family under the growth model. Each update uses one sample and one projection onto $X$, hence $2T$ oracle calls. On the positive-budget branch $RM\ge GR>\varepsilon$, so choosing $T=\lceil(256RM(1+\sqrt\ell)/\varepsilon)^2\rceil$ already meets the horizon condition. [Theorem 2, equations (7)–(8)](https://arxiv.org/html/2610.18555v1#S3.SS1)

Liu’s Theorem 1, with tuning (13), refines the leading fixed-horizon term using uniform directional and norm moment bounds on a Lipschitz objective. Peng, Tang and Jia’s Theorem 2, equations (5)–(7), instead controls all horizons in one run for smooth convex objectives. At moment order two the time-uniform exponent in (6) is $2/5$. The present guarantee uses the selected terminal time. [Liu](https://arxiv.org/pdf/2610.21026v1) · [Peng, Tang and Jia](https://arxiv.org/html/2610.33381v4)

Against the repository's ClippedBgLastIterate theorem, the certified call budget improves from squared to single logarithmic dependence on $1/\delta$. The localized Jiang–Bai–Li proof already gives that confidence exponent. The present theorem certifies the smaller gap estimate $24RM\sqrt{q/T}$ for every integer $T\ge1$, gives a smaller certified budget on the positive-budget branch, and machine-checks the guarantee for the repository's exact oracle and restricted family. The proof uses a known horizon and public scale and radius bounds. The literature check covered last-iterate SGD, heavy-tailed clipping with fixed and horizon-independent schedules, and distance-growing second moments. It establishes neither priority across all models nor sharp constants.
