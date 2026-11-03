# Tail-index-oblivious stochastic monotone root finding

The [Lean theorem](TailObliviousRootFinding.lean) proves an expected-residual guarantee for stochastic root finding with Lipschitz monotone operators under heavy-tailed noise. The method is anchored extragradient without clipping. Its updates depend only on the starting point and the Lipschitz constant. It does not know the noise moment order α, the noise scale σ, the initial distance R, the accuracy ε, or the oracle budget.

For every α ∈ (1,2] and every σ ≥ 0, the budget is of order LR/ε + (σ/ε)^{α/(α−1)} up to polylogarithmic factors and α-dependent constants (a factor (α/(α−1))⁴ on the deterministic term, and 2^{20/(α−1)} with a higher-degree polylogarithm on the noise term). Both terms match known lower bounds up to these factors.

The contribution is adaptivity to the unknown tail index and noise scale, for operators that need not be cocoercive. A new clipping-free extragradient estimate under α-th moments makes this possible. No improvement of the accuracy exponent is claimed.

## Problem, information, and guarantee

The [setup](../Setups/TailObliviousMonotoneRootFinding.lean) concerns a map F : E → E on a finite-dimensional real inner-product space with the following properties:

- **Monotone:** ⟨F(x) − F(y), x − y⟩ ≥ 0 for all x, y.
- **L-Lipschitz:** ‖F(x) − F(y)‖ ≤ L‖x − y‖.
- **Zero near the start:** some x⋆ satisfies F(x⋆) = 0 and ‖x0 − x⋆‖ ≤ R.

This covers smooth convex–concave saddle problems through F = (∇ₓf, −∇ᵧf), monotone variational inequalities without constraints, and fixed points of nonexpansive maps through F = I − T. Cocoercivity is not assumed.

**Oracle.** The oracle returns g(x, ξ) for IID samples ξ, using the repository's `IID` structure. It is jointly measurable and unbiased, with E g(x, ξ) = F(x). For some α ∈ (1,2], the noise has a bounded central α-th moment:

  E‖g(x, ξ) − F(x)‖^α ≤ σ^α   for all x.

The setup states the integrability conditions explicitly. The variance may be infinite. There is no bounded domain, no bounded variance, no samplewise smoothness, and no symmetry assumption.

**Information.** The setup's `Public` type is (E, x0, L). The algorithm is built from this public data only. The parameters α, σ, R and ε exist only in `Params`, and so does the budget. The method therefore has to be anytime, and the Lean statement enforces this by typing. Every oracle call is counted, including those of unfinished epochs.

**Accuracy criterion.** The returned point Z satisfies

  ∫ ‖F(Z)‖^α dP ≤ ε^α,

which implies E‖F(Z)‖ ≤ ε. The guarantee holds for the oracle budget

  N = ⌈2²⁰(1 + LR/ε)·Γ² + 2^{20/(α−1)}·(σ/ε)^{α/(α−1)}·Γ^{2α/(α−1)}⌉,  where  Γ = 64·(α/(α−1))²·(1 + log(1 + LR/ε + σ/ε)).

In words, the first term is the deterministic cost LR/ε times Γ². Since Γ² contains (α/(α−1))⁴, this factor also blows up as α → 1, though only polynomially in 1/(α−1). The second term is the statistical cost (σ/ε)^{α/(α−1)}, times the factor 2^{20/(α−1)} and Γ^{2α/(α−1)}, a polylogarithm of degree 2α/(α−1). That degree tends to infinity as α → 1. So the bound is polylogarithmically optimal only for α bounded away from 1. Constants are conservative.

## Algorithm and output

The [algorithm](../Algorithms/TailObliviousExtragradient.lean) runs epochs k = 0, 1, 2, …. Each epoch restarts from x0.

**Stage operators.** Epoch k has k + 1 stages j = 0, …, k, with strengths a_{k,j} = L·2^{j−k}. Stage j uses the operator

  H_j(x) = F(x) + a_{k,j}·x − b_j,   where b_0 = a_{k,0}·x0 and b_{j+1} = b_j + a_{k,j}·z_j,

and z_j is the output of stage j. This is the recursive anchoring of Chen and Luo, and of the repository's StochasticSmoothBanachFixedPoint result.

**Stage steps.** Each stage runs N_k = 96·2^k stochastic extragradient steps with step size η = 1/(16·L·2^j):

  y = x − η(g(x, ξ) + a x − b),   x⁺ = x − η(g(y, ξ′) + a y − b).

Each step uses two fresh samples, so epoch k costs 2(k + 1)N_k oracle calls. There is no clipping, normalization, or batching.

**Output.** The algorithm stores the last point of the most recently completed epoch and returns it. The point of the epoch in progress is never returned.

## Proof idea

**1. Clipping-free extragradient bound under α-th moments** ([geometry](../Proofs/TailObliviousGeometry.lean), [one step](../Proofs/TailObliviousNoise.lean)).

Let H be a-strongly monotone and (L + a)-Lipschitz with zero u. Let ζ₁ be the noise at x and A = x − ηH(y) − u. Applying monotonicity at the noisy extrapolation point y gives, pathwise and without centering,

  ‖A‖² ≤ (1 − ηa)‖x − u‖² + 2η²‖ζ₁‖².

Because α/2 ≤ 1, the map t ↦ t^{α/2} is subadditive. This turns the quadratic noise term, whose mean is infinite under heavy tails, into 2^{α/2}η^α‖ζ₁‖^α.

The second noise ζ₂ is centered given y. To handle it, a short lemma shows that any 2-smooth norm is α-power smooth: ‖x + y‖^α ≤ ‖x‖^α + α J(x)[y] + (C + 6)‖y‖^α. In a Hilbert space C = 7. Together:

  E‖x⁺ − u‖^α ≤ (1 − ηa/2)‖x − u‖^α + 9η^α σ^α.

The algorithm never uses α. The exponent appears only in the analysis.

The standard finite-variance analysis of stochastic extragradient takes the expectation of η²‖ζ₁‖², which is infinite here. Linearizing H(y) instead would require 2α moments.

**2. Stages and anchors** ([stage](../Proofs/TailObliviousStage.lean), [anchors](../Proofs/TailObliviousAnchoring.lean), [process](../Proofs/TailObliviousProcess.lean)).

With δ = 1/(16·2^k), each stage contracts the normalized α-energy a^α‖x − u‖^α by a factor 1/18, up to a noise floor 18σ^α δ^{α−1}. The anchor shift ‖u_{j+1} − u_j‖ ≤ ‖z_j − u_j‖/2 holds by strong monotonicity. It keeps the energies bounded by (2a_{k,0}R)^α + 324σ^α δ^{α−1}.

**3. Terminal bound and accuracy** ([accuracy](../Proofs/TailObliviousAccuracy.lean)).

A telescoping anchor correction gives

  ‖F(z_k)‖ ≤ 4 Σ_j a_{k,j}‖z_j − u_j‖ + 2a_{k,0}R.

The α-power mean inequality and the stage bounds then give

  E‖F(z_k)‖^α ≤ 17(k + 2)^α·[(2LR·2^{−k})^α + 324σ^α(16·2^k)^{1−α}].

**4. Execution, IID blocks, and budget** ([execution](../Proofs/TailObliviousExecution.lean), [law](../Proofs/TailObliviousLaw.lean), [budget](../Proofs/TailObliviousBudget.lean)).

- **Execution.** `execute` with N calls returns the output of epoch K, where K is the last epoch completed within N calls.
- **Law.** That epoch's seeds are IID blocks with the product law. This follows from IID shift and regrouping lemmas.
- **Budget.** The budget algebra shows K + 2 ≤ Γ and accuracyBound(K) ≤ ε^α.

## Closest results and what is new

The comparisons below use the primary versions checked on 2 November 2026. Items marked *preprint* have no verified conference status.

| Result | Setting | Noise and knowledge | Residual complexity |
|---|---|---|---|
| Chen & Luo, RAIN ([JMLR 25(387), 2024; arXiv 2208.05925v4](https://arxiv.org/abs/2208.05925), Alg. 1, Thm 4.2) | Monotone Lipschitz (convex–concave) | Finite variance. Tuning uses ε, D, σ. | Õ(LR/ε + σ²/ε²) |
| Sadiev et al., ICML 2023 ([arXiv 2302.00999v2](https://arxiv.org/abs/2302.00999), Thm 4.1 Case 2, Thm G.4) | Quasi-strongly monotone, clipped SEG | α-moment. Clipping levels and steps use σ, α, and the horizon. | High-probability distance bound. Combined with anchoring it gives Õ(LR/ε + (σ/ε)^{α/(α−1)}) **with σ, α, ε known**. |
| Gorbunov et al., NeurIPS 2022 ([arXiv 2206.01095](https://arxiv.org/abs/2206.01095)) | Monotone, clipped SEG and SGDA | Finite variance ("heavy-tailed" there means not sub-Gaussian) | High-probability gap |
| Fatkhullin, Hübler & Lan ([arXiv 2508.04860v2](https://arxiv.org/abs/2508.04860), extended SIOPT version) | Strongly convex minimization, SGD with step 2/(μt) | α-moment, **tail-index-oblivious** | Optimal for strongly convex minimization. Their parameter-free schedule is suboptimal for convex problems. No operators. |
| Chandak et al. ([arXiv 2603.19648v1](https://arxiv.org/abs/2603.19648), preprint) | Strongly monotone, forward stochastic approximation | Heavy-tailed, α-free steps | Forward steps need η ≲ μ/L². For non-cocoercive operators this costs (L/μ)² per stage, i.e. (LR/ε)² overall after anchoring. |
| Present theorem | Monotone L-Lipschitz, Euclidean | α-moment. **Only L and x0 known**, anytime. | Expected residual: Õ(LR/ε + (σ/ε)^{α/(α−1)}), with the factors stated above |

**What is new.** To our knowledge this is the first optimal-order residual guarantee for monotone (not necessarily cocoercive) stochastic root finding that does not require knowledge of the noise moment order or the noise scale. Clipping-based heavy-tailed methods for variational inequalities set their clipping levels from σ and α. The tail-index-oblivious analysis of Fatkhullin, Hübler and Lan is for strongly convex minimization. The ingredient that removes the need for clipping in extragradient is the pathwise bound plus subadditivity in Step 1.

**What is not claimed.**
- *Cocoercive and nonexpansive special case.* Anchoring combined with an α-oblivious forward stochastic-approximation solver is probably a direct composition there, so we do not claim that case as new.
- *Finite variance (α = 2).* A horizon-tuned RAIN variant that does not need σ or R is likely easy. Our result recovers the RAIN rate up to logarithms, and its novelty lies in α < 2.
- *High probability.* With σ, α, ε known, anchoring plus clipped SEG (Sadiev et al.) gives the same rate with high probability. Our result is in expectation only. Its advantage is obliviousness and the absence of clipping.

Other related works use finite variance or a different structure:
- Kim & Alacaoglu, arXiv 2609.15257 (preprint): anytime, single-sample, structured finite variance.
- Yoon & Loizou, arXiv 2608.12043: dual anchoring, finite variance, cocoercive.
- Puchkin & Gorbunov, arXiv 2311.04161: structured symmetric densities, clipping.
- Gorbunov et al., arXiv 2310.01860: high probability, clipping.
- Repository results StochasticSmoothBanachFixedPoint and RegularizedProxExtragradientCohypomonotone: finite variance. The anchoring structure here follows the former.
- Repository setup StochasticGeneralizedMonotone and its theorems: high-probability residual guarantees for generalized-Lipschitz monotone operators under finite variance, with σ known.

## Instances

The class includes smooth convex–concave problems with interacting variables, e.g.

  f(x, y) = (1/n) Σᵢ φ(aᵢᵀx) + xᵀBy − (1/m) Σⱼ ψ(cⱼᵀy),

with φ and ψ convex and smooth, e.g. logistic or softplus. Then F = (∇ₓf, −∇ᵧf) is monotone and Lipschitz, and generally not cocoercive because of the bilinear coupling.

Two noise models satisfy the assumption:
- additive noise with Student-t(ν) coordinates, ν ∈ (1,2], which has finite α-th moments for α < ν but infinite variance;
- importance-sampled component gradients with heavy-tailed weights.

In both cases the tail index is typically unknown, which is the situation the theorem addresses.

## Lower bounds (pen-and-paper, not formalized)

- **Deterministic term.** Ω(LR/ε) operator evaluations are needed even with exact oracles, for the residual criterion and span-respecting methods (Yoon & Ryu, ICML 2021, lower-bound theorem; also Diakonikolas 2020).
- **Statistical term.** Take F(x) = x − m on a line, with samples m + ζ where ζ has α-th moment σ^α. Any algorithm's output Z then estimates m, since ‖F(Z)‖ = |Z − m|. The classical two-point construction for heavy-tailed mean estimation (Bubeck, Cesa-Bianchi & Lugosi 2013; Devroye et al. 2016) gives Ω((σ/ε)^{α/(α−1)}) samples for expected error ε.

No lower bound on the price of adaptivity is claimed. The polylogarithmic factors and the constant 2^{20/(α−1)} are not shown to be necessary.

## Limitations

- **Expectation only.** No high-probability guarantee with logarithmic dependence on the confidence level is proved.
- **Lipschitz constant.** L must be known. The method adapts to α, σ, R and ε, not to L.
- **Large constants.** The noise term carries the factor 2^{20/(α−1)}, and the logarithmic degree 2α/(α−1) grows as α → 1. The deterministic term carries (α/(α−1))⁴ through Γ². The proved bound is far from practical constants.
- **Stated budget only.** The guarantee is proved at the stated budget, not for every larger budget. The output is the last completed epoch, and the proof uses an upper bound on the budget relative to the formula.
- **Euclidean only.** The space is a finite-dimensional inner-product space. The Banach-space ℓ_p geometry was explored but is not part of this result.
