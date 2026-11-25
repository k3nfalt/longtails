# Stochastic PŁ optimization with a mean-squared-smooth oracle: lower bound

The [lower theorem](MeanSquaredSmoothPLLowerBound.lean) and its [upper counterpart](MeanSquaredSmoothPLUpperBound.lean) ([note](MeanSquaredSmoothPLUpperBound.md)) determine, up to universal constants and one logarithm on the noiseless term, the number of same-sample stochastic-gradient pair queries needed to minimize a Polyak–Łojasiewicz (PŁ) function when the stochastic gradients have bounded variance and are mean-squared smooth. With

\[
\kappa=\frac L\mu,\qquad \bar\kappa=\frac{\bar L}{\mu},\qquad s=\frac{\sigma}{\sqrt{\mu\varepsilon}},
\]

the complexity is

\[
\kappa\ (\text{times }\log_2(1+\Delta/\varepsilon)\text{ in the upper bound})\;+\;s^2\;+\;\min\{\kappa s^2,\ \bar\kappa s\}.
\]

The new mathematical claim is the lower bound, and in it the term \(\min\{\kappa s^2,\bar\kappa s\}\): the variance-reduction cross term \(\bar\kappa\,\sigma/\sqrt{\mu\varepsilon}\) is necessary for every randomized algorithm. The upper bound is a routine restart of a known variance-reduced method and is not claimed as a new algorithmic idea.

## Problem and precise statements

The general [setup](../Setups/MeanSquaredSmoothPL.lean) takes a separable real Hilbert space \(E\) (any dimension), an abstract sample space \(\Omega\), and

* an objective \(f:E\to\mathbb R\) with an \(L\)-Lipschitz gradient that attains its minimum \(f_\star\), with \(f(x_0)-f_\star\le\Delta\) and the global PŁ inequality \(2\mu(f(x)-f_\star)\le\|\nabla f(x)\|^2\) for every \(x\) (no convexity);
* a jointly measurable stochastic gradient \(g(x,\xi)\) with \(\mathbb E\,g(x,\xi)=\nabla f(x)\), \(\mathbb E\|g(x,\xi)-\nabla f(x)\|^2\le\sigma^2\), and mean-squared smoothness \(\mathbb E\|g(x,\xi)-g(y,\xi)\|^2\le\bar L^2\|x-y\|^2\) for all \(x,y\);
* IID samples \(\xi_1,\xi_2,\dots\); one oracle call names two points \((x,y)\) and returns \((g(x,\xi_k),g(y,\xi_k))\) for one fresh sample. This is the same-sample ("multi-point") oracle on which SARAH, SPIDER, STORM and PAGE are built.

`valid` requires \(0<\mu\le L\le\bar L\), \(\sigma\ge0\), \(\Delta\ge0\), \(\varepsilon>0\). (\(L\le\bar L\) loses nothing: mean-squared smoothness implies that \(\nabla f\) is \(\bar L\)-Lipschitz.) Success means a measurable output \(X\) with integrable gap and \(\mathbb E[f(X)]-f_\star\le\varepsilon\). `allowedAlgorithm` imposes no restriction. All assumptions are standard: PŁ (Polyak 1963; Karimi–Nutini–Schmidt 2016), bounded variance, and the mean-squared ("average") smoothness of Arjevani et al. and of PAGE.

The lower bound is stated on the [high-dimensional restriction](../Setups/HighDimensionalMeanSquaredSmoothPL.lean): \(E=\mathbb R^d\), \(\Omega=\mathbb R\), and `valid` additionally requires

\[
\kappa\ge2^{73},\qquad \Delta\ge64\,\varepsilon,\qquad d\ge\kappa^4(1+s^2).
\]

Its admissibility and success predicates are literally those of the general setup ([inclusion](../Proofs/MeanSquaredSmoothPLInclusion.lean)); the upper theorem holds on the general setup, hence on the restriction.

**Lower bound (new).** For every valid parameter choice, every algorithm (arbitrary internal randomness, adaptive pair queries, arbitrary output rule) and every budget

\[
0\le b\le\Big\lfloor\frac{\kappa+s^2+\min\{\kappa s^2,\ \bar\kappa s\}}{2^{200}}\Big\rfloor ,
\]

there is an admissible objective and oracle, depending on the algorithm and on \(b\) but not on the realized seeds, on which the algorithm fails \(\mathbb E[f(X)]-f_\star\le\varepsilon\) after \(b\) pair queries. This is `NonConvergence`, not the negation of an existential guarantee; the case \(b=0\) is included. The valid set is nonempty for every value of \(s\ge0\) and every ratio \(\bar\kappa/\kappa\ge1\) (take \(\kappa\ge2^{73}\), \(\Delta=64\varepsilon\), \(d\) large; for instance \(\mu=\varepsilon=1\), \(L=\bar L=2^{200}\), \(\sigma=0\), \(\Delta=64\), \(d=2^{800}\) is valid and has budget one). Two consequences of the loose constants should be read literally: the smallest admissible dimension is \(2^{292}\), and the budget is nonzero only when \(\kappa+s^2+\min\{\kappa s^2,\bar\kappa s\}\ge2^{200}\). The theorem is a statement about rates, not about practical problem sizes.

**Upper bound (companion theorem).** Stage-wise SARAH succeeds with

\[
\Big\lceil 640\big(\kappa\log_2(1+\Delta/\varepsilon)+s^2+\min\{\kappa s^2,\ \bar\kappa s\}\big)\Big\rceil
\]

pair queries for every valid parameter choice of the general setup, in every dimension.

**Tightness, stated exactly.** Writing \(\mathrm{LB}\) and \(\mathrm{UB}\) for the two budgets, on the valid set of the restricted setup

\[
\mathrm{UB}\le 640\cdot2^{200}\,\log_2(1+\Delta/\varepsilon)\,(\mathrm{LB}+1)+1 .
\]

The two bounds agree up to the universal constant whenever \(s\ge\log_2(1+\Delta/\varepsilon)\), i.e. \(\sigma\ge\sqrt{\mu\varepsilon}\,\log_2(1+\Delta/\varepsilon)\) (then \(\min\{\kappa s^2,\bar\kappa s\}\ge\kappa s\ge\kappa\log_2(1+\Delta/\varepsilon)\)). In the low-noise regime they differ by at most the factor \(\log_2(1+\Delta/\varepsilon)\) on the term \(\kappa\). We do not claim a \(\Theta\) characterization for the formalized pair. On paper the missing logarithm is supplied by the exact-gradient lower bound \(\Omega(\kappa\log(\Delta/\varepsilon))\) of [Yue–Fang–Lin (COLT 2023, arXiv:2212.13551; see the paper for its algorithm class)](https://arxiv.org/abs/2212.13551) and, for all adaptive randomized gradient-only algorithms, of Ou–Wang (arXiv:2609.03990v2, Theorem 3.1; an unreviewed preprint); that geometrically weighted chain is not formalized here.

## How the result meets the stated research requirements

* *Upper and lower bound for one question, in `Template` and `TemplateLowerBound`.* Both theorems use the same objective class, the same pair oracle with the same cost (one pair = one query, at most two gradient evaluations), and the same criterion \(\mathbb E[f]-f_\star\le\varepsilon\). All three terms of the rate appear in both budgets.
* *Important, popular setup.* PŁ objectives with variance-reduced stochastic gradients: the online PŁ case of PAGE (Li–Bao–Zhang–Richtárik, ICML 2021), SNVRG/SPIDER-type restarts, and PAGER (Fatkhullin et al., NeurIPS 2022).
* *What is closed.* The dependence on \(\kappa\), \(\bar\kappa\), \(\sigma\), \(\mu\), \(\varepsilon\) of the noise terms, including when variance reduction helps (exactly when \(\bar L/L<\sigma/\sqrt{\mu\varepsilon}\)). What is not closed in Lean: the factor \(\log(\Delta/\varepsilon)\) on the noiseless term, small condition numbers \(\kappa<2^{73}\), the range \(\Delta<64\varepsilon\), and fixed small dimension.
* *Overlap check.* No theorem or pull request of this repository treats a PŁ class with a mean-squared-smooth oracle (the PŁ results there use single-point oracles or second-order oracles; the mean-squared-smooth lower bounds there are convex or stationarity results).

## What is known, and what is new

*Without mean-squared smoothness.* SGD needs \(O(\kappa\log(\Delta/\varepsilon)+\kappa\sigma^2/(\mu\varepsilon))\) single-point queries ([Khaled–Richtárik, arXiv:2002.03329, Theorem 3 and Corollary 2](https://arxiv.org/abs/2002.03329)), and [Masiha–Kiyavash–Thiran, arXiv:2606.28278v3, Theorem 4.3](https://arxiv.org/abs/2606.28278) prove the matching noise term \(\Omega(\kappa\sigma^2/(\mu\varepsilon))\) for randomized gradient-only methods on the global PŁ class; [Ou–Wang, arXiv:2609.03990v2, Theorem 3.1 and Appendix B.2](https://arxiv.org/abs/2609.03990) prove \(\Omega(\kappa\log(\Delta/\varepsilon)+\kappa\sigma^2/(\mu\varepsilon))\) (and heavy-tailed analogues) with a Bernoulli-thinned PŁ chain. Both are unreviewed preprints. Their oracles multiply the frontier coordinate by a coin through a hard progress indicator; such an oracle is discontinuous in \(x\) and therefore not mean-squared smooth, so these theorems say nothing about the class studied here beyond the trivial terms.

*With mean-squared smoothness.* [PAGE (Li–Bao–Zhang–Richtárik, ICML 2021), Theorem 6 and Corollary 7 (online PŁ case, under its Assumption 2 of average smoothness)](https://arxiv.org/abs/2008.10898) gives \(O((b+\sqrt b\,\bar\kappa)\log(1/\varepsilon))\) with \(b=\sigma^2/(\mu\varepsilon)\), i.e. \(O((\bar\kappa+s^2+\bar\kappa s)\log(1/\varepsilon))\); SNVRG under PŁ ([Zhou–Xu–Gu, arXiv:1806.07811, Theorem 4.4](https://arxiv.org/abs/1806.07811)) has the same polynomial terms with more logarithms. The only lower bounds available for this class were the statistical term \(s^2\) and the exact-gradient term. For finite sums the analogous question is settled for large condition numbers: \(\Omega(n+\bar\kappa\sqrt n\,\log(1/\varepsilon))\) for linear-span methods under mean-squared smoothness ([Bai–Liu–Luo, arXiv:2402.02569, Corollary 3.6](https://arxiv.org/abs/2402.02569)) and \(\Theta(n+\kappa\sqrt n\,\log(\Delta/\varepsilon))\) for \(\kappa\ge\sqrt n\) against randomized methods under individual smoothness, with a different small-\(\kappa\) branch ([Peng–Tang–Jia, arXiv:2609.00045v3, Theorem 3.3](https://arxiv.org/abs/2609.00045)). Both papers work with exact component oracles; the second lists noisy oracle models as open.

*The open question.* [Masiha–Kiyavash–Thiran, Section 5, third question](https://arxiv.org/abs/2606.28278) ask, for an "average-smooth stochastic oracle used in variance-reduced methods" on \(\alpha\)-PŁ classes, whether the gap between their candidate lower bound (deterministic term plus the statistical term, no cross term) and the PAGER upper bound of [Fatkhullin et al., Theorem 2](https://arxiv.org/abs/2210.01748) is intrinsic. That question is posed for sublevel \(\alpha\)-PŁ classes with \(\alpha<2\) implied. **We do not answer it as posed.** We settle its \(\alpha=2\), global-PŁ analogue: there the known upper bound already has the cross term \(\bar\kappa s\), and the contribution is to prove that this term is necessary (so the candidate lower bound without a cross term is not the truth at \(\alpha=2\)), together with the exact interpolation \(\min\{\kappa s^2,\bar\kappa s\}\) between the non-variance-reduced and variance-reduced regimes.

*What is new, precisely.*

1. The lower bound \(\Omega(\min\{\kappa s^2,\bar\kappa s\})\) for all randomized algorithms with same-sample pair queries. In the special case \(\bar L\ge L\sigma/\sqrt{\mu\varepsilon}\) it reproduces the rate \(\kappa\sigma^2/(\mu\varepsilon)\) of Masiha et al. and Ou–Wang on a smaller class and against a stronger oracle.
2. The exact two-parameter form of the rate, which states when variance reduction helps under PŁ.
3. A formal proof of both sides.

*What is not new.* The mechanism is a recombination of known ingredients: a thinned globally-PŁ zero-chain (Yue–Fang–Lin; Masiha et al.; Ou–Wang; in this repository the guarded chain of the second-order PŁ pair), the mean-squared-smooth probabilistic chain of [Arjevani et al., arXiv:1912.02365, Theorem 3](https://arxiv.org/abs/1912.02365) with its smoothness–variance rescaling, and coordinate hiding against arbitrary queries. We claim no new lower-bound technique.

## Why standard reductions do not give the bound

* *From finite-sum lower bounds with \(n\approx\sigma^2/(\mu\varepsilon)\).* A finite-sum instance sampled uniformly is an online instance, and an online pair-query algorithm is a special incremental-first-order algorithm, so a finite-sum lower bound transfers whenever the instance has uniformly bounded variance \(\sigma^2\). The relevant instance is the "dense weak hiding" chain of [Peng–Tang–Jia, arXiv:2609.00045v3, Theorem 3.3 and Appendix D](https://arxiv.org/abs/2609.00045): its components are individually smooth (hence mean-squared smooth) and differ from their mean only through sign tables of relative size \(1/\rho\approx\sqrt n\). But that noise is not confined to the frontier: every stage that has been opened keeps it. From their formulas (eqs. (163)–(172); this computation is ours and is not stated in the paper) the variance of a uniformly sampled component is of order \(n\,\mu\Delta'\) at the starting point and grows to order \(\kappa\sqrt n\,\mu\Delta'\) once all stages are open, where \(\Delta'\gtrsim\varepsilon\) is the initial gap of the instance. Bounded variance \(\sigma^2\) therefore forces \(\sqrt n\lesssim s^2/\kappa\), and the transferred bound \(n+\kappa\sqrt n\) is \(O(s^2+s^4/\kappa^2)\), i.e. \(O(s^2)\) in the regime \(s\le\kappa\) where the cross term matters. The reduction yields only the statistical term. The older finite-sum constructions with components on orthogonal blocks fail more simply (variance \(\approx n\|\nabla f\|^2\)). In the hard oracle used here the noise lives on the frontier edge only, which is what a bounded-variance online oracle permits and a fixed finite sum does not.
* *From the non-smooth-oracle bound \(\kappa\sigma^2/(\mu\varepsilon)\).* Substituting \(L=\bar L\sqrt q\), \(q\asymp\mu\varepsilon/\sigma^2\), is exactly the heuristic that predicts \(\bar\kappa s\); it is not a proof, because the oracles of those theorems are not mean-squared smooth for any constant and do not allow same-sample pairs.

## Hard instances and proof

Two families are used; every valid parameter choice is covered by one of them.

**Masked PŁ chain** (terms \(\kappa\) and \(\min\{\kappa s^2,\bar\kappa s\}\)). The unit function is the repository's guarded, radially cut-off chain \(h\) on \(n+1\) hidden coordinates. It is \(2^{55}\)-smooth, globally PŁ with constant \(2^9(n+1)\), has gap at least \(n-r\) at any point whose coordinates beyond the first \(r\) are still small, and equals a quadratic outside a ball. The objective is \(f(x)=a\,h((x-x_0)/\lambda)\). The oracle is

\[
g(x,\xi)=\nabla f(x)+(c_q(\xi)-1)\,\frac a\lambda\,M\big((x-x_0)/\lambda\big),\qquad c_q=\tfrac1q\mathbf 1\{\xi\le q\},\ \xi\sim U[0,1],
\]

where the *secret field* \(M(w)=\sum_{s}m_s(w)\,D_s(w)\) collects the gradient blocks \(D_s\) of the individual (cut-off) edges, each multiplied by a Lipschitz mask \(m_s(w)=\min_{i\ge s}\chi(w_{\pi(i)})\) (\(\chi=1\) on \([-1/40,1/40]\), \(0\) outside \([-1/20,1/20]\)). At every point at most one term of \(M\) is nonzero (the frontier edge), so \(M\) is bounded by \(2^{51}\) and \(2^{58}\)-Lipschitz on all of \(\mathbb R^d\), including the guard and cut-off regions ([mask](../Proofs/MeanSquaredPLMask.lean), [secret field](../Proofs/MeanSquaredPLSecret.lean)). Consequently the oracle is unbiased, has variance \((1/q-1)\|aM/\lambda\|^2\) and satisfies

\[
\mathbb E\|g(x,\xi)-g(y,\xi)\|^2=\|\nabla f(x)-\nabla f(y)\|^2+(1/q-1)\Big\|\tfrac a\lambda(M(\cdot)-M(\cdot))\Big\|^2\le\frac{(2^{59}a/\lambda^2)^2}{q}\|x-y\|^2
\]

for all pairs ([oracle](../Proofs/MeanSquaredPLOracle.lean)). When the coin is zero the reply at a point whose undiscovered coordinates are small depends only on the discovered coordinates; when it fires, one more coordinate is revealed, simultaneously for both points of the pair. A simulation with a clipped level, a coupling lemma, and a counting argument over coordinate embeddings ([execution](../Proofs/MeanSquaredPLExecution.lean)) show that, for at least seven eighths of the embeddings, the output of any algorithm has gap at least \(a(n-\#\text{coins}-1)\). With \(a=16\varepsilon/(n+1)\), \(a/\lambda^2=2^{10}\mu(n+1)\), reveal probability \(q=\min\{1,2^{116}\mu\varepsilon/\sigma^2\}\) and \(n+1=\lfloor\min\{\kappa/2^{65},\ \bar\kappa\sqrt q/2^{69}\}\rfloor\), all class constraints hold ([parameters](../Proofs/MeanSquaredPLParameters.lean)), and Markov's inequality on the number of coins gives failure for \(N\le n/(64q)\) ([hard instance](../Proofs/MeanSquaredPLHard.lean)).

**Two shifted quadratics** (term \(s^2\)). \(f_\pm(x)=\tfrac\mu2\|x-x_0\mp v\|^2\) with \(\|v\|^2=5\varepsilon/\mu\) and oracle \(\mu(x-x_0)\mp c_q(\xi)\mu v\), \(q=5\mu\varepsilon/\sigma^2\). The noise is additive, so the oracle is mean-squared smooth with constant \(\mu\). Until the first coin fires the two instances are indistinguishable and the two gaps sum to at least \(5\varepsilon\) ([quadratic family](../Proofs/MeanSquaredPLQuadratic.lean)).

The [case analysis](../Proofs/MeanSquaredPLLowerBound.lean) uses the chain with \(q=1\) when \(s^2\le2^{116}\), the masked chain when \(s^2>2^{116}\) and \(\bar\kappa\ge2^{15}s\), and the quadratics otherwise.

## Limitations

* Constants are astronomically loose (\(2^{200}\), \(\kappa\ge2^{73}\)); they come from the reused chain (third-derivative-safe profiles, radius \(2^{60}(n+1)\)).
* The dimension requirement \(d\ge\kappa^4(1+s^2)\) is sufficient, not shown necessary.
* The logarithm \(\log(\Delta/\varepsilon)\) on the noiseless term is not in the formal lower bound.
* The hard oracle is a general unbiased vector oracle; it is not shown to be the gradient of sampled scalar losses, so the narrower "conservative oracle" or individually-smooth-loss problem is not addressed.
* Only \(\alpha=2\) (classical PŁ) is treated; the \(\alpha<2\) question of Masiha et al. remains open.
* Literature access: OpenReview pages for ICLR 2027 submissions could not be read by either agent. In particular, one anonymous submission (`jpLJRwjrpk`) could not be checked; a title search for it returns only Jin's bounded-noise lower bound (arXiv:2608.09004), which has neither PŁ nor mean-squared smoothness.
