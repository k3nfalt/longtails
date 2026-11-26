# Weighted-average SGD for Markov quadratic interpolation

Write $F(x)=f(x)-f(u)$ and $B=LR^2/2$. After $n\ge1$ component-gradient calls, the weighted output satisfies
\[
\mathbb E F(y_n)\le \frac{B}{1+\alpha(n-1)}.
\]
At zero calls $F(x_0)\le B$. The resulting sufficient budget is
\[
N=\begin{cases}
0 & \varepsilon\ge B,\\
1+\left\lceil(B/\varepsilon-1)/\alpha\right\rceil & 0<\varepsilon<B .
\end{cases}
\]
The separate branch retains zero calls at equality and throughout $R=0$.

## Oracle and output

In a separable real Hilbert space, $F(x)=\tfrac12\sum_i\pi_i\langle x-u,H_i(x-u)\rangle$, where $0\preceq H_i\preceq LI$ are selfadjoint and $\|x_0-u\|\le R$. The finite chain has arbitrary initial law, stationary distribution $\pi$, and transition rows $\kappa(i,\cdot)\ge\alpha\pi$, with $0<\alpha\le1$. One call at $x_k$ returns $g_k=H_{s_k}(x_k-u)$. The algorithm knows $L,\alpha,x_0$ and its ambient space. It sets $x_{k+1}=x_k-g_k/L$ and accumulates $S_n=\sum_{k=1}^{n-1}x_k$. At $n=0$ it returns $x_0$. At positive $n$ it returns $(\alpha S_n+x_n)/(1+\alpha(n-1))$. Neither the updates nor the output require $\varepsilon,R$, state identities, or refresh labels. Execution uses every reply through the final allowed call, and the bound holds at every larger budget.

## Why the terminal iterate gets weight one

Put $e_k=x_k-u$ and $B_i(e)=\langle e,H_i e\rangle$. Cocoercivity gives $\|H_i e\|^2\le L B_i(e)$, so each step reduces squared distance by at least $B_{s_k}(e_k)/L$. This bounds $\|e_1\|$ by $R$ for every initial state. For $k\ge1$, $e_k$ is fixed by the prefix through $s_{k-1}$. Averaging the nonnegative forms against that state's transition row gives conditional expected form at least $2\alpha F(x_k)$. Summing the resulting energy drops yields
\[
\alpha\sum_{k=1}^{n-1}\mathbb E F(x_k)+\tfrac L2\mathbb E\|e_n\|^2\le B.
\]
The terminal term covers $\mathbb E F(x_n)$ directly. Jensen's inequality with these same weights gives the displayed risk bound. Each finite-horizon output depends on a finite prefix, which ensures measurability and integrability. The proof uses row minorization even for initial laws concentrated on a state of stationary mass zero.

## Comparison within LongTails

The existing theorem certifies the last iterate with step $\alpha/(10^4L)$ after $1+\lceil10^{16}D\rceil$ calls, where $D=LR^2/(\alpha\varepsilon)$. Both the model and the expected objective accuracy are identical. In the zero-call branch the older budget is at least one. Otherwise $D>2$ and the new ceiling argument is $D/2-1/\alpha\le D/2$, more than one below $10^{16}D$. Thus the new integer budget is strictly smaller at every valid parameter choice, with no ties. For fixed positive $L,R,\alpha$ and $\varepsilon\downarrow0$, the leading coefficient of $D$ falls from $10^{16}$ to $1/2$. This gain concerns the certified budget for a different output. The earlier note already states an average bound $B/[\alpha(n-1)]$ for $n\ge2$ and discusses a thinning comparator for the last iterate. The terminal weight improves that average bound for every $B>0$ and gives a guarantee at $n=1$. [Existing theorem and note](MarkovQuadraticLastIterate.md)

There is no repository lower bound for this setup. Its unrestricted validity predicate includes $R=0$, when returning $x_0$ succeeds without a call.

**Informal lower bound (not machine-checked).** In a nontrivial space take $R>0$, $0<\varepsilon\le LR^2/4$, unit $v$, minimizers $x_0\pm Rv$, and Hessians $0,LI$ with stationary active mass $p=4\varepsilon/(LR^2)$, starting inactive and refreshing from $\pi$ with probability $\alpha$ each transition. Until the first active sample the two signs have identical transcripts and their mean gap is at least $2\varepsilon$, so success requires $N\ge1+\lceil LR^2/(8\alpha\varepsilon)\rceil$ by the union bound on the $N-1$ transitions (zero calls also fail), fixing the order in this restricted regime and leaving at most a factor four.

## Prior work and limitations

The comparison covers the sources cited in the last-iterate note and primary papers on averaged least squares, Markov SGD, and shuffled finite sums. Here $R$ always denotes an initial-distance bound. Several papers use the same letter for a feature moment.

- Bach and Moulines (2013), Theorem 1, (1)–(2), analyze constant-step SGD on IID least-squares samples and the uniform average of the first $n$ iterates, including initialization. At zero residual noise their excess-risk bound reduces to $\|\theta_0-\theta_*\|^2/(2\gamma n)$ for $\gamma R_{\rm BM}^2<1$. Their feature fourth-moment bound plays the role of a smoothness scale, and (2) also retains a variance term for noisy data. [Paper](https://arxiv.org/pdf/1306.2119)
- Jain, Kakade, Kidambi, Netrapalli and Sidford, Theorem 1, (4), analyze IID least-squares mini-batches and a tail average. At batch size one, after $s$ burn-in steps out of $n$, for $0<\gamma\le\gamma_{1,\max}/2$ their excess-risk bound has bias at most $2(1-\gamma\mu)^s F(x_0)/[\gamma^2\mu^2(n-s)^2]$ and a variance term of order $1/(n-s)$ which vanishes under interpolation. Their $\mu$ is positive minimum population curvature. [Paper](https://jmlr.org/papers/volume18/16-595/16-595.pdf)
- In their accelerated least-squares paper, Jain et al. use the IID first-order oracle (2) and average the tail of the accelerated iterates. Theorem 1 and Corollary 2 give, after their sample-size threshold and with half the run used for burn-in, an exponentially decaying bias on the scale $\sqrt{\kappa\widetilde\kappa}$ plus $11\sigma^2 d/n$. The condition numbers require positive population curvature, and interpolation removes the noise term. [Paper](https://proceedings.mlr.press/v75/jain18a/jain18a.pdf)
- Dereziński and Dong, Theorem 3.1 and Corollary 3.3, use independent samples. For noiseless rank-one least squares from zero initialization, Corollary 3.3 bounds last-iterate expected half-squared prediction loss by $3R_{\rm DD}\|\theta_*\|^2/(T+1)$ with step $1/R_{\rm DD}$, where $R_{\rm DD}$ bounds the fourth moment relative to covariance. Bounded squared feature norms permit $R_{\rm DD}=L$. [Paper](https://arxiv.org/pdf/2606.29593)
- Mou et al., Proposition 1, (23), study linear stochastic approximation with mixing Markov data and positive stability margin $1-\kappa$. At moment order one the last iterate's mean squared parameter error has an exponentially decreasing initial term plus an $O(\eta\bar\sigma^2\tau d/(1-\kappa))$ term for allowed step $\eta$ and mixing window $\tau$. Their margin differs from the refresh probability here. [Paper](https://arxiv.org/pdf/2112.12770)
- Even (2023), Theorem 5.6 applied to update (2), gives $\mathbb E\|x_T-x_*\|^2\le2(1-\gamma\mu)^T\|x_0-x_*\|^2$ for the last iterate under interpolation and $\gamma L<1$. The result covers Markov sampling and even arbitrary index sequences because each component is $\mu$-strongly convex. Here individual Hessians may vanish. [Paper](https://proceedings.mlr.press/v202/even23a/even23a.pdf)
- Doan et al., Theorem 1, (22)–(23), use geometrically mixing Markov sampling and steps $4/(\sigma k)$ for a $\sigma$-strongly convex objective. Their last-iterate expected squared distance is $O(\log(k)/k)$ with a decaying initialization term. Their assumptions allow noise, and their error criterion is parameter distance. [Paper](https://arxiv.org/pdf/2003.10973)
- Mishchenko, Khaled and Richtárik, Theorem 3, Algorithms 1–2, analyze fresh random permutations per epoch or one permutation reused. For convex smooth components the mean of $T$ epoch endpoints has expected gap at most $\|x_0-x_*\|^2/(2\gamma mT)+\gamma^2 Lm\sigma_*^2/4$ on $m$ components. Interpolation kills the second term. The allowed step scales as $1/(Lm)$ and $T$ epochs cost $mT$ calls. Permutation sampling enforces coverage within an epoch, while this oracle can return the same state repeatedly. [Paper](https://arxiv.org/pdf/2006.05988)

The guarantee concerns exact interpolating quadratics, bounded component Hessians, finite-state sampling, known minorization, and an average. The comparisons establish a tighter explicit budget within this repository. Priority for the averaging technique, a sharp constant, and a corresponding large-step last-iterate guarantee remain open here.
