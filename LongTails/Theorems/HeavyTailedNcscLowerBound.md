# Heavy-tailed nonconvex–strongly-concave minimax: the condition-number exponent κ^{p/(2(p−1))} is necessary

The [main theorem](HeavyTailedNcscLowerBound.lean) proves `NonConvergence spec budget` for the
[high-dimensional heavy-tailed NC–SC setup](../Setups/HighDimensionalHeavyTailedNcsc.lean), against **all randomized
algorithms**. Together with the repository's accelerated upper bound
[HeavyTailedNcscAccelerated](HeavyTailedNcscAccelerated.lean) (PR #143), transferred verbatim to the same restricted
specification in [HighDimensionalHeavyTailedNcscUpperBound](HighDimensionalHeavyTailedNcscUpperBound.lean), it pins down
the oracle complexity of heavy-tailed stochastic NC–SC minimax optimization in the stochastic regime σ ≥ ε, up to
p-dependent constants and polylogarithmic factors.

Notation: κ = L/μ, A = LΔ/ε², u = σ/ε, r = p/(p−1) ∈ [2, ∞).

## Problem class, oracle and criterion

The class is exactly that of [HeavyTailedNcsc](../Setups/HeavyTailedNcsc.lean). The restricted setup only fixes
public types and starting points. A function f(x, y) on ℝ^d × ℝ^d has a jointly L-Lipschitz gradient and is
μ-strongly concave in y. The primal function Φ(x) = max_y f(x, y) has initial gap Φ(x0) − inf Φ ≤ Δ, and the initial
dual residual satisfies ‖∇_y f(x0, y0)‖ ≤ G, with x0 = y0 = 0.

One oracle call returns both partial gradients at a queried pair. The oracle is unbiased, jointly measurable, and has
central joint Euclidean p-th moment at most σ^p, with 1 < p ≤ 2. The samples are IID; the sample space is ℝ.

An algorithm succeeds if its measurable output X satisfies P(‖∇Φ(X)‖ > ε) ≤ δ, for every maximizing selector.
The algorithm may be randomized and adaptive. There is no zero-respecting, linear-span, or fixed-method restriction.

`valid` adds the following conditions to the general validity conditions:
- δ ≤ 1/4 and κ ≥ 8;
- LΔ ≥ 2^32 ε²;
- G ≥ 4176 ε/√κ;
- d ≥ 2^40 (1 + A(1 + (√κ u)^r))^4.

## Result

For every valid parameter choice, every allowed algorithm, and every budget

  N ≤ ⌊ ( A·(1 + (√κ·u/2^14)^r) + (κ·u/2^5)^r ) / 2^61 ⌋,

including N = 0, there is an admissible instance on which the actual execution fails. The instance may depend on the
algorithm and on N, but not on the realized seed. Failure means P(‖∇Φ(X)‖ > ε) > 1/4 ≥ δ, or a non-measurable output.

**Matching upper bound.** The PR #143 budget is

  ⌈(2^80 r)^{r+2} Λ^{2r+3} [ √κ(1 + A + Q) + (A κ^{r/2} + κ^r) u^r ]⌉,

where Q = log(2 + κ³L(Δ + G²/μ)/ε²) and Λ = 1 + log(2 + κ + 1/δ + A + (κu)^r + Q). Suppose u ≥ 1. Then
√κ A ≤ A(√κ u)^r and √κ Q ≤ κ^r u^r Q, because r ≥ 2. So both bounds are

  Θ̃_p( (LΔ/ε²)·κ^{p/(2(p−1))}·(σ/ε)^{p/(p−1)} + (κσ/ε)^{p/(p−1)} )

whenever σ ≥ ε and the parameters satisfy the lower bound's `valid` conditions: κ ≥ 8, LΔ ≥ 2^32 ε², G ≥ 4176 ε/√κ,
δ ≤ 1/4, and the dimension bound. This regime is nonempty: for example p = 2, κ = 8, LΔ = 2^32 ε², σ = ε, any
G ≥ 4176 ε/√8, δ = 1/4, and d large enough. The lower bound carries the constant 2^{−14r−61}; the upper bound carries (2^80 r)^{r+2}
and the polylogarithmic factor Λ^{2r+3}Q, which contains log(1/δ) and log G. At p = 2 this is
Θ̃(κLΔσ²/ε⁴ + κ²σ²/ε²), the noise terms of Wu et al. (below).

## What is new, and the closest prior work

- **Heavy-tailed NC–SC upper bounds.**
  - Liu–Luo, [arXiv:2509.14952](https://arxiv.org/abs/2509.14952) v3 (preprint, no venue listed), N²SGDA, Thm 4.1
    (in expectation) and Thm 4.2 (high probability), as listed in their Table 2:
    Õ(κ^{(2p−1)/(p−1)} σ^{p/(p−1)} ε^{−(3p−2)/(p−1)}).
  - Zhu–Xu–Ji, [arXiv:2609.06064](https://arxiv.org/abs/2609.06064) v1 (Stoc-TRGDAmax): the same κ^{(2p−1)/(p−1)} = κ^{r+1}.
  - Repository PR #143: improves the leading term to κ^{r/2}.
- **Heavy-tailed NC–SC lower bounds.** The only κ-dependent one we found is 2609.06064, Thm 3.4:
  Ω(Δ L κ^{1/3} σ^r ε^{−(3p−2)/(p−1)}).
  - It holds for zero-respecting algorithms only. Its criterion is the expected norm of the proximal gradient mapping
    of Φ over a constraint set; our setting is unconstrained.
  - Its conclusion states that the κ-dependence "cannot match that of the upper bound", and its Remark 3.1 says
    "We expect to be able to close this gap in the future." Single-level heavy-tailed lower bounds have no κ: Zhang et al., NeurIPS 2020, and Fradin–Sadiev–Condat–Richtárik, [arXiv:2512.18713](https://arxiv.org/abs/2512.18713) (AISTATS 2026).
- **Finite-variance case p = 2.**
  - Zhang–Wu–Yang, [arXiv:2609.35206](https://arxiv.org/abs/2609.35206): Ω(κLΔσ²ε⁻⁴), for zero-respecting algorithms.
  - Wu et al., [arXiv:2610.00229](https://arxiv.org/abs/2610.00229) v2, Thm 3.4: Θ̃(√κA + κAu² + κ²u² + √κ log₊(G/(ε√κ))), for randomized algorithms. Its Discussion lists "weaker noise moment assumptions" as an open direction.
- **New contribution.** For every 1 < p < 2, this is the first κ-dependent lower bound for heavy-tailed minimax
  optimization that holds for all randomized algorithms. It is also the first with the optimal exponent: it improves
  the κ^{1/3} of 2609.06064 (zero-respecting algorithms only) to κ^{r/2} = κ^{p/(2(p−1))}. This resolves the gap
  left open in their Remark 3.1, in the unconstrained setting.
  - The lower bound shows that the κ^{r/2} exponent of PR #143 is optimal.
  - The leading terms of the earlier κ^{r+1}-type methods are therefore suboptimal by a factor κ^{r/2+1}.
  - Heavier tails amplify the dependence on the condition number: r/2 exceeds the finite-variance exponent 1 whenever
    p < 2. For smooth nonconvex single-level stochastic optimization there is no condition number, and heavy tails
    change only the ε- and σ-exponents.
- **Expected-accuracy consequence.** Failure means P(‖∇Φ(X)‖ > ε) > 1/4, so by Markov's inequality the same
  instances also give E‖∇Φ(X)‖ > ε/4. The lower bound therefore also applies, up to the constant 4 in ε, to
  expected-norm criteria. This conversion is not formalized.
- **Not new.**
  - The p = 2 specialization: its noise terms reproduce Wu et al.
  - The lifting construction, from 2609.35206, Prop. 3.1.
  - The masked hard chain and its randomized hiding argument, reused from the repository's ABC-noise lower bound (PR #185 and PR #229, after Arjevani et al., Math. Program. 2023).

## Technical mechanism

**Chain term, A(√κ u)^r.** The proof is an exact reduction. Any base function H with an ℓ-Lipschitz gradient lifts to

  f(x, y) = α H(βy) − (ν/2)‖y − γx‖²,

with h = μ/(4ℓ), ν = μ + ℓh = 5μ/4, γ² = κ/4, α = q²/h and β = h/q. The lifted function has these properties:
- it is exactly μ-strongly concave in y;
- its joint smoothness is at most L when κ ≥ 8;
- its gap satisfies f(0, y) − f(x, γx) ≤ α(H(0) − inf H) + q²‖∇H(0)‖²/(2μ).

By Danskin's theorem, ∇Φ(x) = νγ(y* − γx) = γq∇H(βy*), which gives
‖∇H(βγx)‖ ≤ (ν + ℓh)/(νγq)·‖∇Φ(x)‖. With q = 6/(5γ) this factor is exactly 1.
See [HeavyTailNcscLift](../Proofs/HeavyTailNcscLift.lean).

The lifted x-reply is exact. The lifted y-reply is q·(base reply at βy) − ν(y − γx), so every minimax algorithm is
simulated by a base algorithm, with output βγ·X; see [HeavyTailNcscChain](../Proofs/HeavyTailNcscChain.lean).

The base instance is the repository's masked hard chain. Its reveal probability π_rev = min{1, (1/2)(8352/(√κ u))^r}
is matched to heavy tails. The base noise is (Bernoulli(π_rev)/π_rev − 1)·w with ‖w‖ ≤ 1740 ε. The lifted noise
therefore has p-th moment at most 2π_rev^{1−p}(1740 q ε)^p = σ^p exactly, because r(p − 1) = p. The randomized
hiding lemma for that chain (`exists_hp_failure`) gives P(‖∇H(βγX)‖ ≤ ε) < 3/4. Through the transfer inequality,
P(‖∇Φ(X)‖ > ε) > 1/4. The base budget is ≍ A(1 + (√κ u)^r). The key point is that the lifting shrinks the effective
gradient scale to ε/√κ while the noise level stays σ, and the heavy-tailed reveal probability then scales as
(ε/(√κσ))^r.

**Dual-estimation term, (κu)^r.** A new two-point family handles every G ≥ 0, including G = 0
([HeavyTailNcscTwoPoint](../Proofs/HeavyTailNcscTwoPoint.lean)). Let a = ⟨e, x⟩ and b = ⟨e, y⟩, and define

  f_s(x, y) = L₁ab − L₁Ya − (μ₁/2)‖y‖² + sθW·hub(b/W),  s = ±1,

where hub(t) = ∫₀ᵗ clip(τ) dτ is the Huber function, L₁ = L/2, μ₁ = 8μ/5, Y = 8ε/L, W = 2Y and θ = 3μ₁Y/4.
- The dual residual at the origin is zero, and the modulus of strong concavity is μ₁ − θ/W = μ.
- An ε-stationary point for s requires the dual maximizer b* ∈ [3Y/4, 5Y/4]. On that range the Huber derivative is
  exact, which forces L₁a into disjoint ranges for s = +1 and s = −1.
- The s-dependent part of the y-gradient is revealed only through a Bernoulli(ρ) spike scaled by 1/ρ, which keeps
  the oracle unbiased. Here ρ = min{1, (1/2)(2θ/σ)^r} and θ ≍ ε/κ, so the p-th moment equals σ^p. Without a spike
  the replies are identical, so N ≤ 1/(4ρ) ≍ (κu)^r queries leave both instances indistinguishable with
  probability ≥ 3/4.

## Scope, assumptions and limitations

- **Scope compliance.**
  - The task was to prove almost tight upper and lower bounds that close a problem in terms of `Template` and
    `TemplateLowerBound`. This contribution adds the lower bound (`NonConvergence`, `TemplateLowerBound`) and states
    the matching upper bound (`Convergence`, `Template`) on the same specification `HighDimensionalHeavyTailedNcsc`.
    The two share the oracle model, accuracy criterion and parameters, and agree up to p-dependent constants and
    polylogarithmic factors on the regime above.
  - The setup is important and widely used. Nonconvex–strongly-concave minimax with heavy-tailed stochastic
    gradients models GAN training, distributionally robust optimization, and adversarial training, where gradient
    noise is empirically heavy-tailed. The class and oracle are the standard ones of the primary papers cited above.
    No new assumption is introduced, and the lower bound covers all randomized algorithms.
  - Overlap check. Open PR #215 concerns generalized-smooth NC–SC with Scion, and PR #4 quadratic finite-sum
    acceleration. Concurrent sessions work on stochastic NC–PL minimax and on PL with mean-squared smoothness. None
    of them treats heavy-tailed NC–SC lower bounds.
- **Regime.** Tightness is claimed only for σ ≥ ε, each fixed p ∈ (1, 2], κ ≥ 8, LΔ ≥ 2^32 ε², and
  G ≥ 4176 ε/√κ. The G condition is needed only by the chain family, because the hidden chain has ∇H(0) ≠ 0 and y0
  is public. No tightness is claimed below that threshold.
- **Deterministic term.** For σ < ε the formal lower bound provides only A, against the upper bound's √κ A. Wu et al.
  (2610.00229, Thm 3.4) claim a randomized √κ A lower bound; we have not verified it. Their σ = 0 instances belong
  to every p-class.
- **Initialization term.** The √κ log₊(G/(ε√κ)) term of 2610.00229 is not formalized here; in the upper bound it
  sits inside the polylogarithmic factor.
- **Not addressed.** The optimal δ-dependence, fixed or small dimension (the required d grows like the fourth power
  of the budget), and uniformity of the constants as p → 1. The constants are deliberately loose.
