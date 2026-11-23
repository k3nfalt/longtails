# The dimension-dependent complexity of weak-Minty root finding

For a globally Lipschitz weak-Minty operator on Euclidean space, write $t=LR/\varepsilon$. The number of exact vector evaluations needed for expected residual at most $\varepsilon$ is, up to universal constants,

$$
H(d,t)=d\log(1+t^2/d).
$$

The characterization holds for every $d\ge1$ and $t>1$. The upper algorithm is deterministic and returns a queried point with residual at most $\varepsilon$ on every execution. The lower bound allows randomized, adaptive queries anywhere in space. Both use the same setup and cost unit. [Upper theorem](DimensionAdaptiveMinty.lean) · [Lower theorem and hard instance](DimensionAdaptiveMintyLowerBound.md)

## Problem and oracle

A query $x\in\mathbb R^d$ returns $F(x)$. The unknown operator is $L$-Lipschitz and has a root $z$ within distance $R$ of the supplied $x_0$ such that
$$
\langle F(x),x-z\rangle\ge-\rho\|F(x)\|^2\quad\text{for all }x.
$$
The parameters $d,L,R,\varepsilon,x_0,\rho$ are public, with $0\le\rho L\le1/20$. The admissibility and expected-residual predicates are those of the earlier Euclidean weak-Minty setup. The new specification extends validity to every positive dimension and the entire nontrivial accuracy range. At $LR\le\varepsilon$, Lipschitz continuity gives $\|F(x_0)\|\le\varepsilon$ before any query. Diakonikolas, Daskalakis and Jordan write the coefficient on the squared residual as $\rho_{\mathrm{DDJ}}/2$, so their parameter equals $2\rho$ in this notation. The positive-$\rho$ range gives a uniform separation margin in the proof. Larger allowances have dimension-free analyses with different constants. [Setup](../Setups/FiniteDimensionalWeakMinty.lean) · [Original predicates](../Setups/EuclideanWeakMinty.lean) · [Diakonikolas, Daskalakis and Jordan, Assumption 1 and Theorem 3.2](https://proceedings.mlr.press/v130/diakonikolas21a/diakonikolas21a.pdf) · [Pethick, Mavrothalassitis and Cevher, ICLR 2025, Table 1](https://proceedings.iclr.cc/paper_files/paper/2025/file/7f44f98e5e70dea605d0c5baca231c58-Paper-Conference.pdf)

## Algorithm and counted execution

Put $a=\varepsilon/(16L)$. A round queries $g=F(x)$ and $h=F(x-g/(2L))$. If $\|g\|\le\varepsilon$, the algorithm saves $x$. Otherwise $u=h/\|h\|$ satisfies $\langle u,x-z\rangle\ge a$. For $d>t^2$, the next point is $x-au$, which reduces squared distance to $z$ by at least $a^2$. For $d\le t^2$, the first point is the centroid of the uniform ball of radius $2R$ centered at $x_0$. The next point is the centroid after multiplying the current density by
$$
\exp\!\left[-(2/a)\max\{0,\langle u,y-x\rangle+a/2\}\right].
$$
The saved point stays fixed through all remaining calls. The budget counts both oracle evaluations in each of $\lceil1024 H(d,t)\rceil$ rounds, including padding after success. The formal accuracy criterion integrates the residual norm under the product of the algorithm and oracle seed laws. Exact replies make the returned point independent of both seeds. Exact integration for centroid computation is internal work. The theorem bounds oracle calls and leaves arithmetic complexity open. [Algorithm and output](../Algorithms/DimensionAdaptiveMinty.lean) · [Separation](../Proofs/MintySeparatingCut.lean) · [Execution and accuracy](../Proofs/MintyDimensionRun.lean)

## Why the dimension enters inside the logarithm

A hard cut preserving a ball of radius proportional to $a$ about the root gives the usual volume term $d\log(O(R/a))$. Here the comparison distribution is uniform on a ball of radius $a\sqrt d/16$ about $z$. Rotational invariance bounds its second moment along every unit cut normal by $a^2/256$. The separation margin then bounds its expected hinge penalty by $a/256$, even for cuts that pass through this larger ball. At a centroid, the Grünbaum halfspace bound contracts total mass by a factor at most $5/6$. Jensen's inequality compares that contraction with the cumulative expected penalty. Their difference yields a constant decrease per unsuccessful round against a log-volume ratio of $d\log(32R/(a\sqrt d))$. The larger ball lies in the starting region in the branch that uses it. [Directional moment](../Proofs/MintyCutMoments.lean) · [Potential proof](../Proofs/MintyCutPotential.lean) · [Budget comparison](../Proofs/MintyDimensionBudget.lean)

## Improvement and comparisons

Diakonikolas, Daskalakis and Jordan give the dimension-free $O(t^2)$ bound. Anagnostides et al. obtain polynomial time for bounded-set Stampacchia inequalities using a look-ahead separating hyperplane. Their weak-Minty definition uses squared SVI gap; Lemma 4.12 gives a separation margin for that criterion. Using a normalized look-ahead cut for the present unconstrained residual and a hard centroid cut gives $O(d\log(2+t))$ queries. Taking the better of this and extragradient yields $O(\min\{t^2,d\log(2+t)\})$. For $d\asymp t^2/\log t$, its order is $t^2$, while the proved complexity is $t^2\log\log t/\log t$. For fixed $d$, both upper bounds grow logarithmically in $t$. For $d\ge t^2$, $H(d,t)\asymp t^2$ and the dimension-free rate is already sharp. The paired lower theorem establishes the transition across these regimes. [AISTATS 2021, Theorem 3.2](https://proceedings.mlr.press/v130/diakonikolas21a.html) · [Anagnostides et al., v4, §§4.2–4.3 and 6.2](https://arxiv.org/html/2504.03432v4) · [FOCS 2026 acceptance](https://focs.computer.org/2026/accepted-papers/) · [Earlier repository lower bound](EuclideanWeakMintyLowerBound.md)

The separating step, log-concave halfspace bound and soft-cut density have precedents. The contribution is the sharp joint dimension and accuracy rate, with a directional comparison on the upper side and a continuous prefix construction on the lower side. The hard family has nonlinear interactions and already satisfies $\rho=0$. The result covers general VI operators. Restriction to the saddle-gradient field of a game is a further structural question. The topical literature and PR comparison is detailed in the [lower contribution note](DimensionAdaptiveMintyLowerBound.md).
