# Novelty assessment: `MarkovQuadraticWeightedAverage`

[`result`](../../LongTails/Theorems/MarkovQuadraticWeightedAverage.lean) works in the setup [`MarkovQuadraticInterpolation`](../../LongTails/Setups/MarkovQuadraticInterpolation.lean). The objective is f(x) − f(u) = ½ Σᵢ πᵢ⟨x−u, Hᵢ(x−u)⟩ with self-adjoint 0 ⪯ Hᵢ ⪯ L·I on a separable Hilbert space. The oracle returns H_{sₖ}(x−u), where sₖ is a finite Markov chain with an arbitrary initial law, stationary law π, and rows κ(i,·) ≥ α·π. The theorem proves that SGD with step 1/L and the [weighted output](../../LongTails/Algorithms/MarkovQuadraticWeightedAverage.lean) (α Σ_{k=1}^{n−1} xₖ + xₙ)/(1 + α(n−1)) has 𝔼[f(y) − f(u)] ≤ ε. It was introduced in commit b33ace65 on 2026-11-26.

**Proved complexity.** L bounds the Hessians, R ≥ ‖x₀ − u‖, α ∈ (0,1] is the known refresh probability, and ε > 0 is the target expected gap. The exact budget is:

  N = 0 if LR² ≤ 2ε, and N = 1 + ⌈(LR²/(2ε) − 1)/α⌉ otherwise. This is O(1 + LR²/(αε)).

The bound holds for every initial law and in any dimension. The proof (`output_risk`) uses the energy inequality α Σ_{k=1}^{n−1} 𝔼F(xₖ) + (L/2)𝔼‖eₙ‖² ≤ LR²/2. It then uses F(xₙ) ≤ (L/2)‖eₙ‖² and Jensen's inequality.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Uniformly averaged SGD, step 1/L, **same class**. This is a derived baseline in the [last-iterate note](../../LongTails/Theorems/MarkovQuadraticLastIterate.md) and its [review](MarkovQuadraticLastIterate.md). It is not a published theorem, and I rechecked it. | 1 + ⌈LR²/(2αε)⌉ → 1 + ⌈(LR²/(2ε) − 1)/α⌉, or 0 if LR² ≤ 2ε | None: same order. It saves about 1/α calls, a factor LR²/(LR² − 2ε). That factor is at least 2 only when 2ε < LR² ≤ 4ε, and it tends to 1 as ε → 0. | None | Uniform average of x₁…x_{K−1} → the same average with xₙ added at weight 1. Both are averaged outputs. Adding xₙ also gives a bound at n = 1. | None. The updates are identical. Both outputs need α: here in the output weights, in the baseline in the budget. |
| [Repository last-iterate theorem](../../LongTails/Theorems/MarkovQuadraticLastIterate.lean) (`MarkovQuadratic.result`), same class | ⌈10¹⁶LR²/(αε)⌉ + 1 → as above | None in order. The constant improves from 10¹⁶ to ½. | None | Worse output: last iterate → weighted average | Larger step (1/L instead of α/(10⁴L)) |
| [Even, ICML 2023, Thm 3 / Cor 1](https://arxiv.org/abs/2302.14428v3) (arXiv v3, Jun 2023). Interpolating Markov SGD. **Applies only if every Hᵢ ⪰ μI with μ > 0.** | O((L/μ)·log(LR²/ε)), last iterate, any sampling sequence → O(1 + LR²/(αε)) | Not comparable in general. On the overlap, this result is smaller only when μ ≲ αε·log(LR²/ε)/R². | Strongly convex components → μ = 0 allowed, for example realizable least squares with Hᵢ = aᵢaᵢᵀ. The repository's earlier averaged baseline already covers this. | Last iterate → average | Needs α-minorization |

**Reduction check.** Once the elementary averaged-SGD argument is written down, the result follows from it by one routine step. The terminal term (L/2)‖eₙ‖² in the telescoped energy already dominates F(xₙ), because Hᵢ ⪯ L·I, and Jensen's inequality with weights (α,…,α,1) does the rest. No new mechanism is involved. The proof ancestry is the standard cocoercivity telescoping plus a conditional minorization step, which is also the repository's earlier averaged baseline. The companion note sketches a lower bound of about 1 + LR²/(8αε), using a two-state lazy chain with H ∈ {0, L·I} and ε ≤ LR²/4. The argument looks sound to me, but it is not machine-checked. If correct, it leaves a factor of about 4. Even's Theorem 1 gives a hitting-time lower bound for general convex Markov problems, but I did not check that it applies to this quadratic class.

**Search coverage (2026-11-26).** I read at theorem level Even (ICML 2023; §5.2, Thm 3, Cor 1, Thm 1) and the repository's last-iterate note and review. The review already checked Dereziński–Dong (arXiv:2606.29593), Nagaraj et al. (NeurIPS 2020) and the thinning reduction. My searches for Markov-row Kaczmarz and Markov SGD under interpolation found only IID last-iterate work (Attia et al., arXiv:2507.11274; Dereziński–Dong, COLT 2026). I did not check at theorem level Bach–Moulines, Jain et al., Mou et al. or Doan et al., which the note cites, and I did not check accelerated IID least-squares methods such as Varre–Flammarion, which are dimension-dependent. The note's own claim is only "a tighter explicit budget within this repository". That claim is accurate and matches the Lean budget.

## Conclusion

**No: this is the known averaged-SGD complexity with a slightly better constant.**

The strongest baseline is the uniformly averaged SGD bound on the identical class, with the identical step 1/L and the same expected-gap criterion:

| Method | Calls to reach ε |
|---|---|
| Uniform average (earlier derived baseline) | 1 + ⌈LR²/(2αε)⌉ |
| This result (terminal-weighted average) | 1 + ⌈(LR²/(2ε) − 1)/α⌉, or 0 if LR² ≤ 2ε |

The saving is about 1/α calls. This saving is a meaningful fraction of the budget only at coarse accuracy, 2ε < LR² ≤ 4ε, where it is at most a factor of 2. As ε → 0 the ratio of the two budgets tends to 1.

The comparison shows this rigorously. The proof adds one standard observation to the averaged argument: the leftover distance term already bounds the last iterate's gap. The output is still an average, so the result says nothing new about the last iterate. Within the repository, the gain over the earlier last-iterate theorem is in the constant (10¹⁶ → ½), and it comes at the cost of a weaker output type. I found no prior paper stating this exact weighted bound, but the absence of a citation does not make a routine Jensen refinement novel.

The result can claim a clean, formally verified constant for averaged Markov SGD on interpolating quadratics. It does not give a better complexity, broader scope or a stronger output.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
