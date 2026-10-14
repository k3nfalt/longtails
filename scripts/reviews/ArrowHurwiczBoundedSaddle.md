# Arrow–Hurwicz on bounded composite saddle problems: uniform $O(T^{-3/4})$ ergodic gap

For $\min_{x\in X}\max_{y\in Y} g(x)+\langle y,Kx\rangle-h(y)$ with convex $X,Y$ in real inner-product spaces, $\|x\|,\|y\|\le R$ on them, $\|K\|\le L$, and $g,h$ convex and $M$-Lipschitz on $X,Y$, the Arrow–Hurwicz method ($x$-prox step, then $y$-prox step using the new $x$) with $T=\lceil(11R(LR+M)/\varepsilon)^{4/3}\rceil$ and $\eta=R/((LR+M)T^{1/4})$ returns uniform averages $(\bar x_T,\bar y_T)\in X\times Y$ with $\sup_{x\in X,y\in Y}\Phi(\bar x_T,y)-\Phi(x,\bar y_T)\le\varepsilon$, deterministically ([theorem](../../LongTails/Theorems/ArrowHurwiczBoundedSaddle.lean), [setup](../../LongTails/Setups/BoundedCompositeSaddle.lean), [algorithm](../../LongTails/Algorithms/ArrowHurwicz.lean)).

**Complexity.** Oracle calls ($Kx$, $K^*y$, $\mathrm{prox}_{\eta(g+\iota_X)}$, $\mathrm{prox}_{\eta(h+\iota_Y)}$; 4 per iteration):
$$N_{\rm AH}=4\big\lceil(11R(LR+M)/\varepsilon)^{4/3}\big\rceil=O\!\big(1+(R(LR+M)/\varepsilon)^{4/3}\big),$$
where $R$ bounds the norms on $X$ and $Y$ (so $x_0,y_0$ enter only through $R$), $L$ bounds $\|K\|$, $M$ is the Lipschitz constant of $g$ and $h$, and $\varepsilon$ is the target duality gap. The formula requires $R,L,\varepsilon>0$ and $M\ge0$. It was introduced in commit `d7fe8d4` (2026-10-05).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| PDHG, $\theta=1$, $\tau=\sigma=1/(2L)$: Chambolle–Pock, JMIV 40 (2011), Thm 1(b), eq. (16) ([preprint 685](http://www.cmap.polytechnique.fr/preprint/repository/685.pdf)). **Direct competitor:** same oracle and ergodic gap. | $4\lceil 8LR^2/\varepsilon\rceil=O(1+LR^2/\varepsilon)$ → $O(1+(R(LR+M)/\varepsilon)^{4/3})$ | **Worse** in every regime: by a factor of at least $(LR^2/\varepsilon)^{1/3}$ when $LR^2\ge\varepsilon$, and further when $M>0$ (PDHG has no $M$-dependence) | None. PDHG needs only bounded comparator sets: unbounded $X,Y$ and non-Lipschitz $g,h$ are allowed | None (both are ergodic, deterministic gaps) | Selected result needs both domains bounded and $g,h$ Lipschitz; it is restricted to $\theta=0$ |
| Arrow–Hurwicz, CP 2011 §3.2, eq. (20), with $D=2R$, $\beta=1$, $\tau=\sigma=\sqrt2/(L\sqrt N)$. **Same algorithm.** | $O(1+L^2R^4/\varepsilon^2)$ → $O(1+(R(LR+M)/\varepsilon)^{4/3})$ | Better iff $R(LR+M)/\varepsilon\lesssim(LR^2/\varepsilon)^{3/2}$; e.g. for $M\le LR$, $LR^2\ge\varepsilon$, the speedup is $\Theta((LR^2/\varepsilon)^{2/3})$. Worse when $M\gg L^{3/2}R^2/\sqrt\varepsilon$ | None. CP needs only $\mathrm{dom}F^*$ bounded and no Lipschitz bound | Step depends on $\varepsilon$ in both | Bounded primal domain and Lipschitz $g,h$ are added |
| AltGDA on matrix games: Nan–Iyengar–Kroer–Das Gupta, [arXiv:2609.32995v1](https://arxiv.org/abs/2609.32995) (2026-09-26, prior, preprint), Thm 1 with $\eta=\delta/(2\sqrt2L)$. **Special-case baseline:** simplices, $g=h=0$, $R=1$. | $O(1+L/(\delta\varepsilon))$ → $O(1+(L/\varepsilon)^{4/3})$ on simplices | Better iff $\delta\lesssim(\varepsilon/L)^{1/3}$; worse otherwise | Simplices → arbitrary bounded convex sets with Lipschitz composite $g,h$ (a nested extension) | Step needs the Goldman–Tucker constant $\delta$ → needs only $L,R,M,\varepsilon$ | Worse $\varepsilon$-exponent on matrix games with $\delta\gg(\varepsilon/L)^{1/3}$ |
| Repository, **subsequent** ([`ArrowHurwiczUniformRate.lean`](../../LongTails/Theorems/ArrowHurwiczUniformRate.lean), `2a21c70`, 2026-10-06): same setup, $\eta=1/(2L)$ | $O(1+R(LR+M)/\varepsilon)$ ← $O(1+(R(LR+M)/\varepsilon)^{4/3})$ | Selected is **worse** by a factor of $(R(LR+M)/\varepsilon)^{1/3}$; it has a smaller numeric budget only when $R(LR+M)/\varepsilon\lesssim540$ | None | Later step is $\varepsilon$-independent | Not a disadvantage of the later result |

**Reductions and mechanism.** Tuning CP's §3.2 bound cannot beat $1/\sqrt N$, because its floor $\tau L^2D^2$ is linear in the step. The $\eta^4$ "friction" bound, obtained by combining alternation cross terms into a product of a first difference and a second difference, is not implied by any source I checked. Its proof ancestry is CP's one-step inequality (18)–(19) and the friction quantity $r_t$ of Nan et al. ([arXiv:2510.03855](https://arxiv.org/abs/2510.03855), ICLR 2026, whose $O(1/T)$ result needs an interior equilibrium). Neither supplies the reference-free fourth-order estimate. PDHG's eq. (16) uses only prox optimality inequalities for arbitrary comparators, so it applies to this setup, including infinite dimensions and non-closed $X$ with an exact prox oracle.

**Search coverage (2026-10-07).** I read the PDHG/AH text of the CP preprint and Thm 1 and the examples of arXiv:2609.32995. For Wibisono–Tao–Piliouras ([arXiv:2206.04160](https://arxiv.org/abs/2206.04160), $O(K^{-2/3})$ for alternating mirror descent), I checked only the abstract; whether it excludes Euclidean projection is unverified. I did not access He–Xu–Yuan (2022) or He–You–Yuan (2014). The companion note's citations and its own concession that PDHG is better are consistent with what I checked.

**Conclusion**

**No: as an optimization guarantee, this is another, slower analysis of a specific method.**

The strongest baseline is PDHG (Chambolle–Pock 2011, Thm 1). It uses the same four oracle calls per iteration and gives the same ergodic duality-gap guarantee, under weaker assumptions:

| | oracle calls |
|---|---|
| PDHG ($\theta=1$) | $O(1+LR^2/\varepsilon)$ |
| This result (AH, $\theta=0$) | $O(1+(R(LR+M)/\varepsilon)^{4/3})$ |

PDHG wins by at least $(LR^2/\varepsilon)^{1/3}$ in every regime, has no $M$-term, and needs neither a bounded primal domain nor Lipschitz $g,h$.

Restricted to Arrow–Hurwicz itself, the result does improve CP's own $O(L^2R^4/\varepsilon^2)$ bound when $M\lesssim L^{3/2}R^2/\sqrt\varepsilon$. On matrix games, it also beats the $\delta$-dependent $O(L/(\delta\varepsilon))$ preprint bound when $\delta\lesssim(\varepsilon/L)^{1/3}$. I found no earlier uniform $o(1/\sqrt T)$ bound for constant-step projected Arrow–Hurwicz, but the search does not establish priority. One day later, the repository's own $O(1+R(LR+M)/\varepsilon)$ theorem for the same method and setup superseded it, so it keeps no present-day advantage in any asymptotic regime.

What can be claimed is a method-specific analysis: a historically plausible first instance-uniform $T^{-3/4}$ rate for Arrow–Hurwicz, which is not an improvement for the problem class.

**Verdict: NO IMPROVEMENT**
**Confidence: high**
