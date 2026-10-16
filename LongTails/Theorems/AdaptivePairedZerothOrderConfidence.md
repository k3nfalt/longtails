# Accelerated paired zeroth-order optimization with separated confidence cost

This result gives an efficient accelerated realization of separated dimension and confidence costs for paired zeroth-order optimization. The comparison below is with primary results whose full texts were accessible during review. Two potentially relevant papers have unresolved full-text comparisons, disclosed below; no superiority over them is asserted.

## Formal result and scope

The [main theorem](AdaptivePairedZerothOrderConfidence.lean) proves `Convergence` for the [paired zeroth-order setup](../Setups/AdaptivePairedZerothOrder.lean), using the [explicit accelerated algorithm](../Algorithms/AdaptivePairedZerothOrder.lean). In dimension `d ≥ 1`, the feasible set `Q` is compact and convex, has diameter at most `D > 0`, and has an available exact Euclidean projection. Queries may lie within distance `γmax > 0` of `Q`. The population objective is convex and `M`-Lipschitz on this enlarged domain. The smooth case additionally assumes an `L`-Lipschitz gradient on its interior.

A paired oracle returns `F(x, ω) + δ(x)` at two points using the same sample; different pairs use independent samples. The fixed measurable perturbation satisfies `|δ(x)| ≤ Δ` on the enlarged domain. Sample functions are almost surely continuous and have locally integrable weak gradients `G`. At every interior point, `E‖G(x, ω)‖² ≤ M2²`. Function values are integrable and have mean `f(x)`. Joint measurability and the weak-gradient identity are explicit hypotheses. Sample convexity, sample smoothness, bounded sample gradients, and second moments of raw function values are not required. The probability spaces need not be finite or standard Borel.

The target paper’s Lemma B.2 assumes locally Lipschitz samples on a neighborhood of the evaluation domain. This specification weakens that regularity to continuity on the closed domain and a weak-gradient identity on its interior; the supporting mollification and boundary-transfer proofs justify this change. It does not cover every abstract vector oracle satisfying only a second-moment condition. Exact projection, known feasible geometry, paired samples, and validity of queries on the enlarged domain are substantive requirements.

Set `ℓ = log(8/δfail)` for `0 < δfail ≤ 1`, and `q = d^(1/4)`. For positive integers `N,T`, the theorem requires

```
T ≥ 2^48 (d + ℓ) (1 + M2² D² / ε²) + N.
```

In the smooth case it requires `N ≥ 32(1 + sqrt(L D²/ε))`, with radius `γs = min(γmax,D/N)`. In the nonsmooth case it requires

```
N ≥ 1024(1 + q M D/ε + q D sqrt(M/(γmax ε))),
γn = min(γmax,q D/N).
```

The radius of the applicable branch must satisfy `sqrt(d) Δ/γ ≤ ε/(16384 D)`. These conditions include a genuine restriction on persistent deterministic error; the result does not tolerate arbitrary fixed `Δ` at arbitrarily small accuracy.

The returned point lies in `Q` for every raw oracle outcome, is measurable, and satisfies

```
Pr[f(output) - f(xstar) > ε] ≤ 8 exp(-ℓ) = δfail.
```

The public budget is exactly `6T + 4N` scalar function evaluations, including padding after termination. Choosing `T = ceil(2^48 (d+ℓ)(1+M2²D²/ε²) + N)` gives parameter order `N + (d+ℓ)(1+M2²D²/ε²)`. An arbitrarily oversized public `T` does not have this upper bound. The constant `2^48` is conservative and precludes any claim of practical superiority from this bound. The additive initialization and dimension/confidence terms are retained even at zero stochastic moment.

## Algorithm, information, and actual execution

The algorithm runs smooth-radius and nonsmooth-radius accelerated branches without restarts. It clips paired spherical difference estimates, uses iteration weights `αt=t+1`, total weight `A=N(N+1)/2`, and batches `Bt=ceil(T αt/A)`. A fresh clipped comparison selects between the two terminal candidates. Only the branch corresponding to the valid regime needs the stated accuracy guarantee; both candidates remain feasible.

All tuning functions are explicit in the algorithm module and use the public inputs `d,Q,x0,project,D,γmax,ε,ℓ,N,T`. The algorithm does not read `M,M2,L,Δ`, the regime flag, or the minimizer. However, choosing budgets that satisfy the guarantee depends on those hidden parameters: this is a budget-validity guarantee, not an implemented parameter-free stopping rule or an anytime guarantee.

The supporting [execution certificate](../Proofs/AdaptivePairedZerothOrderWork.lean) is paired with convergence for the same named algorithm. It proves at most `128(T+N+1)` charged primitive operations, exactly `2N` projections, at most `2(T+N)` direction accesses, and exactly `6T+4N` scalar oracle calls. It also proves at most `N+1` query-adaptivity layers and equality of the entire certified query trace with actual execution, including padding. Each solver layer fixes both branches' queries from their previous states; the last layer contains validation and constant-point padding.

These computational statements use exact-real scalar/vector primitives, unit-cost exact projections, and unit-cost direction access. They do not implement finite-bit uniform-sphere sampling or bound bit complexity, memory, or parallel arithmetic depth. A vector primitive can require dimension-dependent scalar work. The setup does not artificially restrict admissible algorithms.

## Contribution and comparison

The proposed contribution is an efficient accelerated realization of a separated dimension/confidence cost under the stated weak-gradient paired model. It is not an unrestricted oracle-complexity improvement over all known methods.

[Adaptive two-points zero-order accelerated methods for stochastic convex optimization problems, v1](https://arxiv.org/html/2610.15202v1), Corollary N.3, supplies an expected-error accelerated baseline. Improving a high-probability guarantee does not improve that expected-error result automatically. Theorems T.3–T.4 supply a simultaneous confidence event using supplied vector-variance and relative-comparison moment bounds. Their exact scalar evaluation count is twice the median-block sample count. Equation (282) bounds the latter by

```
k [2 Ktr + 16 Λ Ktr D²/ε² + 4 Λ (N²+(2+sqrt(2))N+2)/(L0 ε)],
```

where `k` is the smallest positive odd integer at least `2 log2(2Ktr/δconf)`, and `Λ=((72 σbar²)^(1/3)+(8 Mbar2²)^(1/3))³`. This retains trial-cap and curvature-reference costs, including rejections. The confidence event gives the objective bound in (275); Theorem T.4 also states an expected-risk bound. Our construction uses neither those supplied moment bounds in its updates nor per-trial confidence amplification. The stronger efficient comparator below is necessary when assessing the statistical improvement.

[Liu, Clipped Gradient Methods for Nonsmooth Convex Optimization under Heavy-Tailed Noise: A Refined Analysis, v3](https://arxiv.org/html/2512.23178v3), Theorems 1 and 10, is the efficient refined-noise comparator (ICLR 2026). Substituting total second moment of order `d M2²` and directional second moment of order `M2²` gives statistical confidence dependence `d + sqrt(d) ℓ`, with its deterministic and finite-budget terms also relevant. The candidate's `d+ℓ` term improves this comparison when `ℓ` grows beyond `sqrt(d)` and the statistical term dominates the other costs. The asymptotic factor is at most order `sqrt(d)` and saturates when `ℓ` exceeds `d`; there is no universal improvement at constant confidence or after ignoring constants and competing terms.

[Sharp High-Probability Statistical Rates for Heavy-Tailed Nonsmooth Convex Optimization, v1](https://arxiv.org/html/2610.00260v1), Theorem 2.2 and Corollary 2.3 already attain the corresponding information-theoretic `d+ℓ` dependence, subject to their finite-budget and statistical-regime conditions. Its Section 6 and Appendix A.3 distinguish unrestricted internal computation from efficient implementation; the stated finite-net construction can be exponential in dimension. This prior result defeats an unrestricted statistical novelty claim. The present comparison concerns the concrete efficient accelerated spherical construction, not a new information-theoretic rate or an efficiency lower bound for competing algorithms.

[The estimator-geometry preprint, arXiv:2509.21484v3](https://arxiv.org/abs/2509.21484v3), Theorem 2.3 and Appendix A, is also a mechanism comparator. Its deterministic global Lipschitz envelope for every sample is stronger than the pointwise weak-gradient second-moment model here. A raw all-moments argument requiring that envelope cannot simply be substituted under the present assumptions. Its preprint status is distinct from an accepted conference paper.

[Puchkin et al., AISTATS 2024](https://proceedings.mlr.press/v238/puchkin24a/puchkin24a.pdf), Assumption 2.1 and Corollary 5.8, require coordinate density and convolution-tail structure not implied by pointwise weak-gradient second moments. Positive-probability zero samples already permit atoms. Their general acceleration theorem, detailed in Appendix C.3, equations (114)–(115), uses trace variance and a logarithmic confidence factor; substituting variance of order `d M2²` gives `d log(K/δfail)`, not separated `d+ℓ`. The detailed theorem uses a maximum in its tuning constraint; the main-text Theorem 5.7 prints a minimum. This comparison relies on the detailed statement, and does not exclude later extensions.

A standard per-iteration robust-mean reduction does not directly give this bound. Even granting an efficient estimator with cost `O(C/ηt²)` for norm error `ηt` at each query center, where `C` contains the dimension, moment, and simultaneous-confidence terms, the deterministic accelerated error requirement is `Σ αt ηt ≤ A ε/D`. Writing `S=Σ αt^(2/3)`, Hölder's inequality gives `Σ ηt^(-2) ≥ S³ D²/(A² ε²)`, attained in the continuous allocation problem by `ηt=(A ε/(D S)) αt^(-1/3)`. For `αt=t+1`, this retains an order-`N` factor in the resulting sample allocation. This calculation concerns that absolute-error certificate reduction only; it is not a lower bound on robust estimators, centered-error analyses, or global robust optimization constructions.

The mathematical mechanism combines weighted spherical moment control, directional concentration for clipped paired differences, and stopped Hilbert-space control of weighted batch energy. These preserve the smaller directional confidence scale while allowing only second moments in the sample variable. The [weighted spherical proof](../Proofs/WeightedSphericalMoments.lean), [clipped spherical proof](../Proofs/ClippedSphericalMoments.lean), [stopped concentration proof](../Proofs/StoppedVectorConcentration.lean), and [acceleration proof](../Proofs/ScalarClippedAcceleration.lean) expose these steps. Clipping bias bounds and final two-candidate selection are supporting devices, not independently claimed innovations.

## Nonlinear instances and limitations

A concrete interacting family on a compact convex domain is a convex quadratic plus a sum of `log cosh(aᵢᵀx)` terms with dense, nonorthogonal vectors `aᵢ`. Adding a mean-zero random linear perturbation `Zᵀx` and a point-independent integrable random offset gives sample functions with weak gradients of bounded pointwise second moment whenever `E‖Z‖² < ∞`. Neither higher moments of `Z` nor a second moment of the offset is needed. Dense directions give nonlinear interactions in arbitrary finite dimension. This example illustrates scope; it is not a claim that all instances are separable or quadratic.

Full-text comparison remains unresolved for two NeurIPS 2026 papers: [Median-of-Means under Structured Heavy-Tailed Noise](https://openreview.net/forum?id=vGEUrQdO7l) and [Normalized SGD in the Convex Regime](https://openreview.net/forum?id=f322xYHDgN). Official entries are accessible, but current full-text requests return access challenges and no alternate primary full text has been located. Their precise assumptions and guarantees cannot be excluded using titles or abstracts. They are disclosed uncertainties outside the accessible-full-text comparison used here, not evidence of weaker results. Accordingly, this note makes no exhaustive priority claim or claim of superiority over those two papers.
