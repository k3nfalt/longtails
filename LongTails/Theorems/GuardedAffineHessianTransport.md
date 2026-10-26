# Guarded Hessian transport with affine mixed-tail noise

The [Lean theorem](GuardedAffineHessianTransport.lean) proves expected first-order stationarity for a general nonlinear, finite-dimensional nonconvex objective with gradient-dependent curvature and affine heavy-tailed oracle noise. Its contribution is to recover the distinct gradient/Hessian tail exponents in this setting, where the closest applicable published analysis couples them. It does not claim second-order stationarity, optimality, or an improvement in every parameter regime.

## Problem and information

The [setup](../Setups/GeneralizedAffineHessianVector.lean) assumes a differentiable objective with continuously differentiable gradient, a finite lower bound, and initial gap at most Δ. At every point,

\[
\|\nabla^2 f(x)\|\le L_0+L_1\|\nabla f(x)\|.
\]

A gradient query returns an unbiased vector with central p-th moment at most σg^p+αg^p‖∇f(x)‖^p. A directional Hessian query at (x,v) returns an unbiased estimate of ∇²f(x)v with central q-th moment at most (σh^q+αh^q‖∇f(x)‖^q)‖v‖^q. Here 1<p,q≤2. The setup explicitly includes joint measurability and the required integrability. Samples have an abstract IID law; the proof derives the product representation rather than prescribing it. Gradient and Hessian estimators need not be derivatives of the same sample loss, and a sampled directional Hessian estimator need not be linear across directions.

These are the generalized smoothness and affine central-moment assumptions in [RanSOM, arXiv:2602.06824v3, Assumptions 4.1, 4.2, and 4.4](https://arxiv.org/html/2602.06824v3). The known public inputs are the initial point, accuracy, gap bound, moment exponents, and curvature/noise bounds. The algorithm uses no objective values, lower-bound value, exact gradient, full Hessian, or reusable stochastic samples. No algorithm-family restriction is imposed. Dimension is arbitrary and does not appear explicitly in the oracle count; the supplied curvature and noise parameters may depend on dimension. Each vector reply is one oracle call. This is not a bound on arithmetic or automatic-differentiation cost.

## Guarantee and comparison

For readable notation define

\[
\begin{aligned}
b&=p/(p-1),& R&=\sqrt{L_0\Delta}+L_1\Delta+\varepsilon,\\
H&=L_0+\sigma_h+(L_1+\alpha_h)R+\varepsilon/R,&
S&=1+(\sigma_g+\alpha_gR)/\varepsilon,\\
G&=1+\sigma_g/R+\alpha_g,& A&=\Delta H/\varepsilon^2,\\
\ell&=1+\log(2+R/\varepsilon+A+S).
\end{aligned}
\]

The returned point X is measurable, its gradient norm is integrable, and E‖∇f(X)‖≤ε. The total number of gradient and directional Hessian replies, including initialization, guards, failed trials, validation, and padding, is at most

\[
N=\left\lceil 2^{100b+100}(1+b)\ell^{b+1}
\left[S^b+A S^{b/q}G^b\right]\right\rceil.
\]

The Lean public budget expands these quantities directly in the setup parameters on one line. The large constants and common logarithmic factor simplify the bound; they are not practical tuning recommendations. Importantly, G^b multiplies the training term, not the initialization/validation term.

With positive fixed Δ,L1,σg,αg and fixed remaining parameters, the accuracy exponent is max{b,2+b/q}, up to logarithms. For q>p this is strictly smaller than b+1: for p=3/2,q=2 the exponents are 7/2 versus 4; for p=6/5,q=2 they are 6 versus 7. The retained ε^(-b) term can dominate. At q=p the exponent is b+1; the theorem covers q<p but makes no improvement claim there. Constants, logarithms, and dependence on other parameters prevent a claim of universal superiority. Degenerate zero-gap or zero-noise cases are included in the formal statement, without asserting sharpness in those cases.

The closest comparisons are:

* [RanSOM v3, §4.5 and Remark B.26](https://arxiv.org/html/2602.06824v3), revised October 9, 2026, treats the same generalized curvature and affine moment model. In its generalized branch, triggered by L1>0 or αh>0, its step-size/momentum coupling gives exponent b+1 when q>p. That paper identifies a limitation of its analysis; it is not a lower bound for the problem or its algorithm. This result removes that loss using a different algorithm. RanSOM is cited here as a preprint; no conference acceptance is asserted.
* [Fradin et al., AISTATS 2026](https://proceedings.mlr.press/v300/fradin26a.html), [extended version arXiv:2512.18713v2, Theorem 5.1 and Appendix E](https://arxiv.org/html/2512.18713v2), provides the prior mixed-tail stochastic terms and uniform-segment Hessian transport. Theorem 5.1 additionally assumes a Lipschitz Hessian (constant L₂) and uniform operator-norm q-th moments for stochastic Hessians. Its bound includes the term √L₂ Δ σg^(1/4) ε^(-7/4)(σg/ε)^(1/(4(p−1))). RanSOM Corollary 4.8/B.27 supplies the global-smooth, uniform-noise mixed-tail baseline without Hessian Lipschitzness. Neither the mixed-tail exponent nor uniform-segment transport is new here; the extension is to gradient-dependent curvature and affine directional noise with unconditional expected accuracy.
* [Chezhegov, Parletta, Paudice, and Gorbunov, ICLR 2026, §4.2](https://proceedings.iclr.cc/paper_files/paper/2026/hash/03382840834c7fbdc1e882fac11904d6-Abstract-Conference.html), provides a relevant generic high-probability-to-expectation argument. Its polynomial almost-sure growth control on the accuracy criterion does not follow here: bounded normalized steps and L1>0 can allow exponential gradient growth in the horizon. [Jin et al., arXiv:2609.37787v2, Theorem B.2 and Lemma 5.4](https://arxiv.org/html/2609.37787v2), has polynomial-growth control for a strictly sublinear smoothness exponent, rather than the linear growth allowed here.

A batching check follows directly from [RanSOM's equations (54)–(56) and Remark B.26](https://arxiv.org/html/2602.06824v3). For fixed positive L1 and σg, its unbatched path term keeps the coupling η≤cβ even as the minibatch size B grows. If the direction radius ρ is tuned too, the same restriction holds on the effective displacement ρη, which also replaces η in the descent term. The gradient term scales as (β/B)^(1/b). Making that displayed bound at most ε requires B/β≳ε^(-b) and T≳Δ/(ηε), hence BT≳ε^(-(b+1)). Optimizing batching within that bound therefore does not recover the new exponent. This calculation limits that sufficient bound, not RanSOM's actual performance or the problem class.

## Algorithm and new proof mechanism

The [primitive algorithm](../Algorithms/GuardedHessianTransport.lean) periodically resets its estimator with a fresh gradient batch and otherwise transports it with one fresh Hessian-vector query at a uniformly sampled point of the actual normalized-step segment. Gradient resets and transport use separate p- and q-moment bounds. Every proposed step receives a fresh robust gradient-norm guard. A rejected proposal aborts the trial and its output falls back to the initial point. All remaining allocated calls are still counted.

The important new ingredient is the interaction of this guard with the affine oracle model. Let M=65536R. Conditional on a candidate whose gradient norm exceeds 2M, the guard accepts with probability at most 1/16. Short-step generalized geometry bounds the next gradient by twice the larger of the previous gradient and M. Together these yield a contracting recurrence for the unconditional second moment of the gradient multiplied by the survival indicator, bounded by 8M². Candidate outputs, including fallback, have second moment at most 9M². This bound is independent of horizon despite possible exponential growth along unguarded paths.

The estimator increments are masked by survival **before** their fresh randomness is generated. They are not conditioned on acceptance of their own guard. This preserves unbiased transport and the separate moment exponents. An analytical stopped point retains the rejected proposal, so the objective descent ledger is not invalidated by the algorithm's fallback. A curvature-gap inequality and the descent ledger bound true aborts; fresh guard concentration bounds false aborts. A uniform pre-step iterate then has gradient norm at most ε/4 with probability at least 2/3, while retaining the unconditional second-moment bound.

The [returned output](../Algorithms/ValidatedHessianTransport.lean) is the candidate with smallest fresh validation mean norm among independent trials and the initial point. There are K=⌈log(8M/ε)/log 3⌉+1 trials, and each candidate receives ⌈(1048576(K+1)(σg+αgM)/ε)^b⌉+1 validation queries. The second-moment control makes validation errors integrable under affine noise. Finite disjoint training blocks establish trial independence; overlapping infinite tails are not asserted independent. The proof connects this construction to actual `execute`, including stability of its output under the public padded budget.

Batching and uniform-segment transport alone do not supply the new global moment bound. Nor does a final-only norm guard: a multiplicative oracle returning either zero or twice the true gradient has a positive all-zero-batch probability independent of gradient magnitude. A final guard can therefore miss an arbitrarily large gradient without controlling its contribution to expectation. Restart/validation is an established conversion technique; the per-step unconditional moment control that makes it work in this affine generalized setting is the substantive mechanism.

## Nonlinear instances and limitations

An interacting-coordinate example is

\[
f(x)=\sum_i\cosh((Ax)_i)+c\sum_i\cos((Bx)_i),
\]

with invertible dense A and a nonaligned dense B. Choosing c and B appropriately makes the Hessian at zero indefinite. The objective is bounded below and has unbounded gradient and Hessian. If s is the smallest singular value of A, valid constants are L1=‖A‖²/s and L0=‖A‖²(1+c‖B‖√d/s)+c‖B‖². Thus this is not a separable or quadratic-only theorem.

For a common sample-loss model take (1+Zq)f(x)+Zp⟨u,x⟩, where ‖u‖=1 and the independent centered variables Zp,Zq have finite p- and q-th moments respectively. Zp can have infinite q-th moment when q>p. The gradient has affine p-moment noise, while the Hessian has affine q-moment noise; admissible bounds follow from the two-term moment inequality. This explains how better directional Hessian tails can coexist with heavy gradient tails in the same stochastic objective. The example is explanatory mathematics, not an additional hypothesis or a separately formalized family theorem.

The theorem requires known bounds for tuning, IID fresh samples, and unbiased oracles. It does not cover Markov dependence, biased Hessian products, high-probability accuracy, or finding local minima. The proof does not establish minimax optimality. The comparison supports a strict accuracy-exponent improvement in the stated affine generalized regime, not a lower bound against all first-order methods or a claim that every use of second-order information is computationally cheap.

The literature assessment used the two most recent publicly available ICML, ICLR, and NeurIPS editions as of October 25, 2026, recent arXiv submissions/revisions, and older cited baselines. Final targeted checks included the latest versions above and follow-up localization/conversion results. Official proceedings establish the AISTATS and ICLR statuses linked above. An OpenReview browser challenge prevented access through that route, but the official ICLR proceedings PDF was accessible. Search coverage is not an exhaustive novelty certificate; the substantive comparison is against the explicit assumptions and proof steps above.
