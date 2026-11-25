# Stochastic PŁ optimization with a mean-squared-smooth oracle: upper bound

The [upper theorem](MeanSquaredSmoothPLUpperBound.lean) is the algorithmic half of a pair with the [lower theorem](MeanSquaredSmoothPLLowerBound.lean) ([note](MeanSquaredSmoothPLLowerBound.md)). Together they show that, for \(\mu\)-PŁ objectives accessed through bounded-variance, mean-squared-smooth stochastic gradients with same-sample pair queries, the query complexity is

\[
\kappa\log_2(1+\Delta/\varepsilon)+s^2+\min\{\kappa s^2,\ \bar\kappa s\},\qquad
\kappa=\frac L\mu,\quad\bar\kappa=\frac{\bar L}\mu,\quad s=\frac\sigma{\sqrt{\mu\varepsilon}},
\]

up to universal constants and up to the logarithm on the first term (the lower bound has \(\kappa\) there). **The upper bound is routine**: it restarts a SARAH/SPIDER-type estimator with geometrically growing anchor batches. Its role in the pair is to remove the logarithm that the known analyses put on the two noise terms, to state the rate with separate \(L\) and \(\bar L\), and to give a formal proof under the exact setup of the lower bound. The new mathematical content of the pair is the lower bound.

## Setup

The [setup](../Setups/MeanSquaredSmoothPL.lean) is described in detail in the lower-bound note: a separable real Hilbert space \(E\) of any dimension; \(f\) with \(L\)-Lipschitz gradient, attained minimum, \(f(x_0)-f_\star\le\Delta\) and global PŁ constant \(\mu\) (no convexity); an unbiased stochastic gradient \(g(x,\xi)\) with variance at most \(\sigma^2\) and \(\mathbb E\|g(x,\xi)-g(y,\xi)\|^2\le\bar L^2\|x-y\|^2\); IID samples from an abstract probability space; one query returns \((g(x,\xi),g(y,\xi))\) for a pair \((x,y)\) and a fresh \(\xi\). `valid` is \(0<\mu\le L\le\bar L\), \(\sigma,\Delta\ge0\), \(\varepsilon>0\). The algorithm knows \(L,\bar L,\mu,\sigma,\Delta,\varepsilon,x_0\). `allowedAlgorithm` is unrestricted; nothing in the claim depends on restricting the method.

## Algorithm

[Stage-wise SARAH](../Algorithms/StagewiseSarah.lean). An *epoch* \((B,m,\eta)\) started at \(x\) spends \(B\) queries \((x,x)\) to form the anchor \(v_0=\frac1B\sum g(x,\xi_i)\), then performs

\[
x_{t+1}=x_t-\eta v_t,\qquad v_{t+1}=v_t+g(x_{t+1},\xi)-g(x_t,\xi)\quad(t=0,\dots,m-1),
\]

using one pair query \((x_{t+1},x_t)\) per step, and ends at \(x_{m+1}=x_m-\eta v_m\). Stage \(j=0,\dots,K-1\), \(K=\lceil\log_2(\Delta/\varepsilon)\rceil\), halves the expected gap from \(\Delta/2^j\). With \(b_j=8\sigma^2 2^j/(\mu\Delta)\) and \(B_j=\max\{1,\lceil b_j\rceil\}\) it repeats one epoch \(\lceil 3/((m+1)\eta\mu)\rceil\) times, where

* if \(\bar L\sqrt{b_j}<L\,b_j\) (variance reduction pays): \(m+1=\min\{B_j,\lfloor\bar\kappa^2\rfloor\}\), \(\eta=1/(2\bar L\sqrt{m+1})\);
* otherwise: \(m=0\), \(\eta=1/(2L)\), i.e. mini-batch gradient descent.

The output is the last iterate; the schedule and the number of queries are deterministic, and the algorithm ignores replies received after its schedule is exhausted.

## Guarantee

For every valid parameter choice, every admissible \((f,g)\) and every dimension, after

\[
\Big\lceil 640\big(\kappa\log_2(1+\Delta/\varepsilon)+s^2+\min\{\kappa s^2,\ \bar\kappa s\}\big)\Big\rceil
\]

pair queries the output satisfies \(\mathbb E[f(X)]-f_\star\le\varepsilon\) (measurability and integrability are part of the proved statement). One pair query costs at most two stochastic-gradient evaluations, so the bound changes by a factor of at most two if evaluations are counted instead.

## Proof idea

A one-step potential argument replaces the usual epoch-wise summation. For an epoch with \(\theta=1-\eta\mu\) and \(e_t=v_t-\nabla f(x_t)\), the quantity

\[
\Psi_t=\frac{f(x_t)-f_\star}{\theta^{t}}+\eta\,(m+1-t)\,\|e_t\|^2
\]

is a supermartingale along the inner loop when \(\eta L\le\tfrac12\), \(4\bar L^2\eta^2m\le1\) and \((m+1)\eta\mu\le\tfrac12\): the descent inequality under PŁ gives \(f(x_{t+1})-f_\star\le\theta(f(x_t)-f_\star)-\tfrac\eta4\|v_t\|^2+\tfrac\eta2\|e_t\|^2\), and mean-squared smoothness gives \(\mathbb E\|e_{t+1}\|^2\le\|e_t\|^2+\bar L^2\eta^2\|v_t\|^2\). A similar potential handles the anchor phase. Hence one epoch maps the expected gap \(a\) to at most \(\theta^{m+1}(a+\eta(m+1)\sigma^2/B)\) ([potential](../Proofs/StagewiseSarahPotential.lean), [supermartingale step](../Proofs/StagewiseSarahSupermartingale.lean)). These epoch maps are composed into a single potential on the state of the algorithm, and a generic lemma for state machines driven by an IID stream ([process](../Proofs/StagewiseSarahProcess.lean)) turns the one-step inequality into a bound on the actual execution; no product-measure structure is assumed beyond what follows from IID. The [tuning](../Proofs/StagewiseSarahTuning.lean) shows each stage halves the gap, and the [cost count](../Proofs/StagewiseSarahCost.lean) sums the geometric series: stage \(j\) costs at most \(7\kappa+17\min\{\kappa b_j,\bar\kappa\sqrt{b_j}\}+40b_j\). The [execution lemma](../Proofs/StagewiseSarahExecution.lean) connects the template execution, with every oracle call counted, to this analysis.

## Relation to prior work

* [PAGE (Li, Bao, Zhang, Richtárik, ICML 2021), Theorem 6 and Corollary 7](https://arxiv.org/abs/2008.10898), online case under PŁ and average smoothness: \(O((b+\sqrt b\,\bar\kappa)\log(1/\varepsilon))\) with \(b=\sigma^2/(\mu\varepsilon)\), i.e. \(O((\bar\kappa+s^2+\bar\kappa s)\log(1/\varepsilon))\).
* [SNVRG under PŁ (Zhou, Xu, Gu, arXiv:1806.07811, Theorem 4.4)](https://arxiv.org/abs/1806.07811): the same polynomial terms with additional logarithmic factors.
* [PAGER (Fatkhullin, Etesami, He, Kiyavash, NeurIPS 2022, Theorem 2)](https://arxiv.org/abs/2210.01748) is literally PAGE with restarts and stage-dependent batch sizes, for \(\alpha\)-PŁ with \(\alpha<2\). It is the direct precedent of the restart schedule used here.
* SGD under PŁ with bounded variance: \(O(\kappa\log(\Delta/\varepsilon)+\kappa s^2)\) ([Khaled–Richtárik, arXiv:2002.03329, Theorem 3 and Corollary 2](https://arxiv.org/abs/2002.03329)).

Compared with these, the present bound (i) has no logarithm on \(s^2\) or on the cross term, because the anchor batch grows geometrically with the stage, and (ii) takes the better of the SGD-type and the variance-reduced regime stage by stage, which gives \(\min\{\kappa s^2,\bar\kappa s\}\) with \(\kappa=L/\mu\) in the first term rather than \(\bar\kappa\). Both improvements are standard restart arguments; we found no statement of this exact bound but do not claim it as a new idea. Obtaining the same terms by restarting any optimal mean-squared-smooth nonconvex method is equally possible.

## Limitations

* The logarithm on \(\kappa\) is necessary for exact gradients (Yue–Fang–Lin, COLT 2023; Ou–Wang, arXiv:2609.03990, unreviewed), but the companion lower theorem contains only \(\kappa\); see the lower-bound note for the exact tightness statement.
* The method needs \(L,\bar L,\mu,\sigma,\Delta\). No adaptivity is claimed.
* The guarantee is in expectation; no high-probability statement is made.
* Only classical PŁ (\(\alpha=2\)) is covered.
