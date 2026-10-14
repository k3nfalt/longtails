# The Arrow–Hurwicz method / alternating GDA on bounded composite saddle problems: a uniform $O(T^{-3/4})$ ergodic gap

Lean: [`ArrowHurwiczBoundedSaddle.lean`](ArrowHurwiczBoundedSaddle.lean) (theorem `result`, budget `budget`),
setup [`../Setups/BoundedCompositeSaddle.lean`](../Setups/BoundedCompositeSaddle.lean),
algorithm [`../Algorithms/ArrowHurwicz.lean`](../Algorithms/ArrowHurwicz.lean),
proofs [`../Proofs/ArrowHurwiczStep.lean`](../Proofs/ArrowHurwiczStep.lean),
[`../Proofs/ArrowHurwiczRun.lean`](../Proofs/ArrowHurwiczRun.lean),
[`../Proofs/ArrowHurwiczGap.lean`](../Proofs/ArrowHurwiczGap.lean),
[`../Proofs/ArrowHurwiczRate.lean`](../Proofs/ArrowHurwiczRate.lean).

## Problem class

(Lee–Cho–Yun, ICML 2024, study alternating updates in the unconstrained strongly-convex–strongly-concave setting; the
constrained, bounded setting below is the one where the duality gap over the bounded comparator sets is the standard
accuracy criterion.)

$$\min_{x\in X}\max_{y\in Y}\ \Phi(x,y)=g(x)+\langle y,Kx\rangle-h(y),$$

where $E, F$ are real inner-product spaces of any dimension; $X\subseteq E$ and $Y\subseteq F$ are convex sets with
$\|x\|\le R$ on $X$ and $\|y\|\le R$ on $Y$; $K:E\to F$ is a bounded linear map with $\|K\|\le L$; $g$ is convex on $X$ and $h$ is
convex on $Y$, and both are $M$-Lipschitz on their sets (they may be nonsmooth). This is the Chambolle–Pock problem class
with both domains bounded and Lipschitz $g, h$. It contains:

- bilinear games over compact convex sets ($g=h=0$): matrix games, extensive-form games in sequence form, and bilinear
  problems over balls or spectraplexes;
- regularized games with linear or $\ell_1$ regularizers;
- LP saddle formulations on bounded boxes.

**Excluded:** problems where one domain is unbounded. An example is ROF/TV denoising without a primal box, which motivated
the Arrow–Hurwicz analysis in Chambolle–Pock. Chambolle–Pock's Arrow–Hurwicz bound needs only $\mathrm{dom}\,F^*$ to be
bounded, so on the primal side our assumptions are stronger.

## Oracle and algorithm

The oracle answers four kinds of query:

- $y\mapsto K^*y$, the gradient in $x$ of the coupling term;
- $x\mapsto Kx$;
- the exact proximal points $\mathrm{prox}_{\tau(g+\iota_X)}(u)$ and $\mathrm{prox}_{\tau(h+\iota_Y)}(v)$, i.e. a minimiser over
  $X$ of $\tau g(w)+\tfrac12\|w-u\|^2$ (and the same for $Y$).

The algorithm knows $X, Y, R, L, M, \varepsilon, x_0, y_0$. The Arrow–Hurwicz method (PDHG with $\theta=0$; alternating
projected GDA when $g=h=0$) with a constant step $\eta$ is

$$x_{t+1}=\mathrm{prox}_{\eta(g+\iota_X)}(x_t-\eta K^*y_t),\qquad y_{t+1}=\mathrm{prox}_{\eta(h+\iota_Y)}(y_t+\eta Kx_{t+1}).$$

The dual step uses the new primal iterate. The method outputs the uniform averages
$\bar x_T=\frac1T\sum_{t=1}^T x_t$ and $\bar y_T=\frac1T\sum_{t=1}^T y_t$. Each iteration makes 4 oracle calls.

The setup's `allowedAlgorithm` fixes the algorithm to `arrowHurwicz η x0 y0` with some $\eta>0$. The proof shows that the
execution performs exactly $4T$ calls in the alternating order and returns these averages (`execute_ah`, `output_eq`).

## Guarantee

**Theorem.** Let $\Lambda=LR+M$. For every $T\ge1$ and every $\eta>0$ with $\eta\Lambda\le R$ (which implies $\eta L\le 1$),

$$\sup_{x\in X,\,y\in Y}\ \Phi(\bar x_T,y)-\Phi(x,\bar y_T)\ \le\ \frac{10R^2}{\eta T}+\frac{\eta^3L^2\Lambda^2}{4},$$

and $\bar x_T\in X$, $\bar y_T\in Y$.

With $T=\lceil(11R\Lambda/\varepsilon)^{4/3}\rceil$ and $\eta=R/(\Lambda T^{1/4})$, the duality gap is at most
$11R\Lambda\,T^{-3/4}\le\varepsilon$. The Lean budget is the one-line formula

`budget p = 4 * ⌈(11 * R * (L * R + M) / ε) ^ (4/3)⌉₊` oracle calls, i.e. $O\big((R(LR+M)/\varepsilon)^{4/3}\big)$.

The constants do not depend on the game or instance: there is no equilibrium-dependent quantity, no strong convexity and
no polyhedrality. The bound is deterministic and holds for every comparator in $X\times Y$.

## What was known

1. **Chambolle–Pock 2011, §3.2, eqs. (18)–(20).** Reference: A. Chambolle, T. Pock, *A first-order primal-dual algorithm
   for convex problems with applications to imaging*, JMIV 40 (2011); CMAP preprint R.I. 685, May 2010.
   - For the Arrow–Hurwicz method with $\mathrm{dom}F^*$ bounded, they prove
     $\mathrm{Gap}\le \frac1N\big(\frac{\|y-y^0\|^2}{2\sigma}+\frac{\|x-x^0\|^2}{2\tau}\big)+\tau\frac{L^2D^2}{2\beta}$.
   - They write that "O(1/N) convergence can only be guaranteed within a certain error range". Taking $\tau=1/\sqrt N$
     gives $O(1/\sqrt N)$.
   - In their Discussion (§7 of the preprint) they list as an open question "(c) understand why does the Arrow–Hurwicz
     method perform so well in some situations".
2. **He–Xu–Yuan, JMIV 64 (2022) 662–671.** Arrow–Hurwicz with any constant step need not converge on generic convex saddle
   problems; their counterexamples include bilinear problems and LP. Convergence is known only under extra conditions:
   strong convexity (He–You–Yuan, SIAM J. Imaging Sci. 7 (2014)) or vanishing steps (Bonettini–Ruggiero 2012). We read
   only the abstracts of these two papers; their full texts were paywalled.
3. **Bilinear games ($g=h=0$, projected AltGDA).**
   - Nan–Das Gupta–Iyengar–Kroer, ICLR 2026, [arXiv:2510.03855](https://arxiv.org/abs/2510.03855):
     - Thm 1 gives $O(1/T)$ on simplices, but only when the game has an interior Nash equilibrium and with a step size
       $\eta\le\min_i x^*_i,\min_j y^*_j/(2\|A\|)$ that depends on the game.
     - Thm 2 is a local result.
     - §1 states as an open question whether AltGDA achieves a speedup over simultaneous GDA ($O(1/\sqrt T)$) for game
       solving.
   - Nan–Iyengar–Kroer–Das Gupta, [arXiv:2609.32995v1](https://arxiv.org/abs/2609.32995) (Sept 2026 preprint, not peer
     reviewed):
     - Thm 1 (Thm A.1, eq. (A.10)) gives $\mathrm{Gap}\le 15/(2\eta T)$ for matrix games (simplices), but only for
       $0<\eta\le\delta/(2\sqrt2\,L)$, i.e. at best $O(L/(\delta T))$. Here
       $\delta$ is a Goldman–Tucker separation constant of the game, which can be arbitrarily small, so at a fixed step
       size the guarantee is not uniform over games.
     - For general compact convex sets, their Thm 2 is conditional on exact feasibility of a Lyapunov LMI, which is
       verified only numerically.
   - Alternating mirror descent with Legendre regularizers never touches the boundary, so it does not cover Euclidean
     projections. Known rates: $O(T^{-2/3})$ (Wibisono–Tao–Piliouras, NeurIPS 2022) and $O(T^{-4/5})$
     (Katona–Wang–Wibisono, JMLR 2026, [arXiv:2405.03472](https://arxiv.org/abs/2405.03472)).
   - The alternating-regret line studies *other* algorithms built for alternation (Hedge variants, FTRL plus best
     response). It includes Cevher et al. (NeurIPS 2023), [arXiv:2502.12529](https://arxiv.org/abs/2502.12529),
     [2608.24731](https://arxiv.org/abs/2608.24731) and [2608.25182](https://arxiv.org/abs/2608.25182). Cevher et al. note
     that projected OGD has $\Omega(\sqrt T)$ alternating regret against an adversary, so a regret reduction cannot give
     this result.

## New contribution

For the classical Arrow–Hurwicz method on this class, we give the first $o(1/\sqrt T)$ guarantee that is uniform over
instances: $O(R(LR+M)\,T^{-3/4})$.

- The constant-step error floor improves from $O(\tau L^2D^2)$ (Chambolle–Pock eq. (20)) to $O(\eta^3L^2\Lambda^2)$.
- In the bilinear special case, this is the first instance-independent $o(1/\sqrt T)$ rate for projected AltGDA:
  - It holds over arbitrary compact convex sets (beyond simplices and beyond interior equilibria).
  - It uses a step size that does not depend on the game.
  - In particular, it covers the sequence-form polytopes of extensive-form games.

**Mechanism.** Write $n_t=x_t-\eta K^*y_t-x_{t+1}$ and $m_t=y_t+\eta Kx_{t+1}-y_{t+1}$ for the normal/subgradient parts of
the two prox steps. The analyses of Nan et al. ([2510.03855](https://arxiv.org/abs/2510.03855), eq. (5);
[2609.32995](https://arxiv.org/abs/2609.32995)) control the cumulative "friction" $r_t=\langle n_t,\Delta x_t\rangle+\langle
m_t,\Delta y_t\rangle$ using equilibrium-referenced energies. Here is the exact one-step inequality, which needs no equilibrium:

$$\eta[\Phi(x_{t+1},\hat y)-\Phi(\hat x,y_{t+1})]\le\Psi_t-\Psi_{t+1}+\tfrac12 r_t,\qquad
\Psi_t=\tfrac12\|x_t-\hat x\|^2+\tfrac12\|y_t-\hat y\|^2-\tfrac\eta2\langle y_t,Kx_t\rangle+\eta\langle y_t,K\hat x\rangle.$$

The friction is bounded without any reference point, as follows.

1. The prox variational inequality at the previous step gives
   $\langle n_{t-1},\Delta x_t\rangle\le\eta(g(x_{t+1})-g(x_t))$, which telescopes. Hence
   $\langle n_t,\Delta x_t\rangle\le\langle n_t-n_{t-1},\Delta x_t\rangle+\eta(g(x_{t+1})-g(x_t))$.
2. Since $n_t-n_{t-1}=-\eta K^*\Delta y_{t-1}-(\Delta x_t-\Delta x_{t-1})$, the main term becomes a telescoping "velocity
   energy" $\tfrac12\|\Delta x_{t-1}\|^2-\tfrac12\|\Delta x_t\|^2-\tfrac12\|\Delta x_t-\Delta x_{t-1}\|^2$ plus a cross term.
   The same holds for $y$.
3. Because of alternation, the two cross terms combine into $\eta\langle K\Delta x_t,\Delta y_t-\Delta y_{t-1}\rangle$: a
   first difference times a second difference. This is absorbed by $-\tfrac12\|\Delta y_t-\Delta y_{t-1}\|^2$, up to
   $\tfrac{\eta^2}2\|K\Delta x_t\|^2=O(\eta^4)$.

As a result, the friction is fourth order per step. The simultaneous-update analysis loses second order per step, which is
where its $O(\eta)$ floor comes from. Two consequences follow: $\sum_{t<T} r_t\le O(\eta^2R^2+\eta MR)+\tfrac12\eta^4L^2\Lambda^2T$,
and the theorem.

## Limitations and honest comparison

- **The rate is $T^{-3/4}$, not $T^{-1}$.**
  - Numerical PEP/LMI evidence (Nan et al.; 2609.32995) suggests $O(1/T)$ for AltGDA over compact convex sets.
  - $O(1/(\eta T))$ is proved for simplices with a step size depending on $\delta$ (2609.32995).
  - Our per-step loss $\tfrac{\eta^2}{2}\|K\Delta x_t\|^2$ is a limitation of the friction argument. It is not a lower bound.
  - Whether a uniform $O(1/T)$ holds remains open.
- **This is not a state-of-the-art rate for the problem class.** Extrapolated PDHG ($\theta=1$), extragradient and OGDA
  achieve $O(1/T)$ on this class. The contribution concerns the classical alternating (Arrow–Hurwicz) method itself.
- **The coupling must be bilinear (a limitation of this argument).** For nonbilinear smooth convex–concave $f$, the
  cross terms no longer telescope because the mixed Jacobian varies along the trajectory. The one-step inequality then
  carries an error of order $\eta\cdot\eta\cdot R$ per step, i.e. an $O(\eta)$ error floor after averaging, so our
  analysis gives no improvement over $1/\sqrt T$ there. Whether AltGDA achieves $o(1/\sqrt T)$ on general smooth
  convex–concave problems over compact sets is open. Replacing the prox steps on $g,h$ by gradient steps on smooth $g,h$
  leaves a descent-lemma term $\eta\tfrac{L_g}{2}\|\Delta x_t\|^2=O(\eta^3)$ per step, which gives only $T^{-2/3}$ in our
  analysis. Neither variant is claimed.
- **Assumptions stronger than Chambolle–Pock:** both domains are bounded (they need only $\mathrm{dom}F^*$ bounded), and
  $g, h$ are Lipschitz on the sets.
- **The result is ergodic.** The last iterate of AltGDA need not converge (2609.32995, Examples 1–2).
- **No separation from simultaneous GDA is claimed in the worst case.**
  - The best known analysis of simultaneous or Arrow–Hurwicz-type methods with a constant step has an $O(\tau)$ floor.
    In numerical experiments, simultaneous GDA on a $2\times2$ game shows a floor proportional to $\eta$, but we have
    not proved a matching lower bound.
- **Literature status.**
  - Full texts of He–You–Yuan 2014 and He–Xu–Yuan 2022 were not accessible.
  - OpenReview pages could not be read (bot protection).
  - The search for a later $o(1/\sqrt N)$ bounded-domain Arrow–Hurwicz result found none as of 2026-10-05.
