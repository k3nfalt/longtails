# HighDimensionalStrongQuasarUpperBound: novelty assessment

The [theorem](../../LongTails/Theorems/HighDimensionalStrongQuasarUpperBound.lean) shows the following. Take an L-smooth function on ℝᵈ that is (γ,μ)-strongly quasar-convex with respect to a global minimizer x⋆, has initial gap at most Δ, and has an exact gradient oracle. The randomized continuized method [`RelativeQuasar.accelerated`](../../LongTails/Algorithms/RelativeQuasar.lean), run with δ = 0, returns its last primal iterate after a fixed number of calls, and its expected gap is at most ε. The theorem uses the setup [HighDimensionalStrongQuasar](../../LongTails/Setups/HighDimensionalStrongQuasar.lean).

**Complexity.** Here κ = L/μ, Δ ≥ f(x₀) − f⋆, γ is the quasar parameter and ε is the target expected gap. The budget is ⌈32√κ/γ⌉·⌈log₂⌈1+2Δ/(γε)⌉⌉ gradient calls, that is,

  O( γ⁻¹ √(L/μ) · log(2 + Δ/(γε)) ).

The setup's `valid` also restricts the regime: γ ≤ 1/256, κ ≥ 870400, γ²κ ≥ 4, Δ ≥ 1000γ√κ ε, and d ≥ (√κ/γ)⁵(Δ/(1000γ√κε))³. These conditions are needed only by the companion lower bound.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Repository: [AcceleratedRelativeQuasar](../../LongTails/Theorems/AcceleratedRelativeQuasar.lean) (2026-10-16), at δ = 0 | ⌈32√κ/γ⌉·⌈log₂⌈1+2Δ/(γε)⌉⌉ → identical (proved equal in [StrongQuasarChainUpper](../../LongTails/Proofs/StrongQuasarChainUpper.lean) `calls_eq`) | None: same budget, same algorithm | None. The earlier result covers any finite-dimensional E, δ ∈ [0,1), and all γ ≤ 1, Δ ≥ 0 | None | Narrower: restricted to ℝᵈ, δ = 0, and the high-dimensional, small-γ, large-κ regime above |
| [Hinder–Sidford–Sohoni, COLT 2020](https://proceedings.mlr.press/v125/hinder20a.html), Thm 1 ([arXiv:1906.11985v3](https://arxiv.org/abs/1906.11985)) | O(γ⁻¹√κ log(κ/γ) log⁺(Δ/(γε))) function+gradient evaluations, deterministic ε-optimality (which implies an expected gap ≤ ε) → O(γ⁻¹√κ log(2+Δ/(γε))) | Removes the factor log(κ/γ). This gain is unbounded as κ/γ → ∞ but only logarithmic | None (same class) | Needs no function values. HSS needs only a lower bound on γ and need not know L | Randomized, with an expected gap only, instead of a deterministic guarantee. Requires μ and γ to be known |
| [Wang–Wibisono, ICLR 2023](https://openreview.net/pdf?id=yYbhKqdi7Hz), Thm 2 and Cor. 2 ([arXiv:2302.07851v1](https://arxiv.org/abs/2302.07851)) | O(γ⁻¹√κ log(V/ε)) gradient calls, where V = Δ + μ‖x₀−x⋆‖²/2 ≤ (1+1/γ)Δ by strong-quasar quadratic growth. The guarantee is a time-weighted expectation E[e^{γ√(μ/L)T_k} gap], or a bound holding with probability 1 − 1/(c²k) − 1/c₀ → same order | None: same order | None | Gives a plain expected gap at a fixed number of calls, which their weighted expectation does not directly give. The repository already proved this conversion in AcceleratedRelativeQuasar | Larger constants |

**Reduction check and proof ancestry.** The theorem is a direct substitution of δ = 0 and E = ℝᵈ into the existing repository theorem: `valid_relative` checks the parameter conditions, `calls_eq` checks that the two budgets are equal, and the execution argument is copied. It contains no new mechanism. The continuized flow-and-jump energy comes from Wang–Wibisono, who built on Even et al.'s continuized acceleration.

**Search coverage.** On 2026-11-17 UTC I checked HSS (arXiv v3, Theorem 1), Wang–Wibisono (v1, Theorem 2 and Corollary 2), the Fu–Xu–Wilson ICML 2023 result (summary only, which reports the same binary-search form as HSS), and Hermant et al. (arXiv:2512.16533, abstract only; it gives high-probability and almost-sure continuized bounds). I did not verify whether Hermant et al. or Fu–Xu–Wilson state a fixed-budget expected bound. The companion note says explicitly that this is "not a new upper-complexity claim", and that statement is consistent with what I found.

## Conclusion

**No: this theorem restates a known upper bound and adds nothing new mathematically.**

Its budget is literally the δ = 0 case of the repository's earlier [AcceleratedRelativeQuasar](../../LongTails/Theorems/AcceleratedRelativeQuasar.lean) theorem, restricted to ℝᵈ and to a narrow parameter regime. The order matches Wang–Wibisono's continuized acceleration (ICLR 2023):

  γ⁻¹√κ · log(Δ/(γε))   (vs. Hinder–Sidford–Sohoni's γ⁻¹√κ · log(κ/γ) · log(Δ/(γε)) with function values).

Removing the log(κ/γ) factor relative to HSS is Wang–Wibisono's improvement. Turning their time-weighted expectation into a fixed-call expected gap was already done in this repository. So this theorem has no advantage over its source theorem in any regime.

The theorem exists only so that the companion [lower bound](../../LongTails/Theorems/HighDimensionalStrongQuasarLowerBound.lean) has a matching upper bound in the same setup. The pair matches up to a constant when ε ≤ Δ/(10⁶γκ). Any novelty in the pair belongs to the lower bound, which is not assessed here.

What can be claimed: a correct restatement in the lower bound's setup, with no new complexity, scope, or output guarantee.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: high**
