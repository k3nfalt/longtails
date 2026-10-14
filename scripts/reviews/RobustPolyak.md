# Novelty assessment: robust Polyak step for uncalibrated sharp oracles

The Lean result ([theorem](../../LongTails/Theorems/RobustPolyak.lean), [setup](../../LongTails/Setups/UncalibratedSharp.lean), [algorithm](../../LongTails/Algorithms/RobustPolyak.lean)) studies a G-Lipschitz function on a real inner-product space. The function has a minimizer `u` with `μ‖x−u‖ ≤ f(x)−f(u)`. At each query the oracle returns `(γr, γ(g+e))`, where `g` is a subgradient with `‖g‖ ≤ G`, the error satisfies `‖e‖ ≤ ρ < μ`, the gap estimate satisfies `r ∈ [αΔ(x), βΔ(x)]` with `Δ(x) = f(x)−f*`, and `γ > 0` is an unknown per-query scale. The global subgradient condition forces `f` to be convex. The update is `x⁺ = x − c·r̂/‖ŵ‖²·ŵ`, where `r̂ = γr` and `ŵ = γ(g+e)` are the returned components, and `c = 2(1−ρ/μ)/(α+β)`. The theorem proves that the **last iterate** satisfies `f(x_K) − f* ≤ ε` deterministically.

**Complexity.** The algorithm knows only `μ, ρ, α, β, x₀`. The stopping index is the budget `K = ⌈(G+ρ)²(α+β)²/(4(μ−ρ)²αβ) · log(1+G²R²/ε²)⌉`, which also needs `G`, the bound `R ≥ ‖x₀−u‖` and the target `ε`. Using `G+ρ ≤ 2G` and `β/4α ≤ (α+β)²/(4αβ) ≤ β/α`, the bound is

  **K = Θ( 1 + (β/α) · G²/(μ−ρ)² · log(1 + GR/ε) )** oracle calls.

The `1 +` term accounts for the ceiling.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Polyak 1969, relaxed Polyak step `λ_k ∈ [λ₁,λ₂] ⊂ (0,2)` with known `f*`; convex case of [Davis et al., JOTA 2018, Thm 3.1](https://arxiv.org/abs/1803.02461). **Special case only:** `ρ = 0` | With `ρ = 0`, taking `λ_k = c·r/Δ ∈ [2α/(α+β), 2β/(α+β)]` gives per-step contraction `1 − λ(2−λ)μ²/G² ≤ 1 − 4αβμ²/((α+β)²G²)`. Both bounds are therefore `O(1 + (β/α)(G/μ)² log(1+GR/ε))` | None: same order. At `α = β`, `ρ = 0` the contraction factors are identical | Exact subgradient → subgradient error `‖e‖ ≤ ρ < μ` (only the factor `μ → μ−ρ` changes) | None. Both methods use G- and R-free updates and a last-iterate guarantee | None on the overlap. The scale `γ` cancels in Polyak's ratio |
| Goffin 1977 ([Math. Program. 13](https://link.springer.com/doi/10.1007/BF01584346)) normalized subgradient step with geometric decay; convex version of Davis et al. 2018, Thm 5.1. **Full target setup via reduction** | `O(1 + ((G+ρ)/(μ−ρ))² log(1+GR/ε))` (derivation below) → `O(1 + (β/α)((G+ρ)/(μ−ρ))² log(1+GR/ε))` | Worse by the factor `(α+β)²/(4αβ) ∈ [1, β/α]`. The two bounds are equal only when `α = β` | None. Both cover the same class | Updates no longer need upper bounds on `G` and `R` (only `μ, ρ, α, β`). The stopping index still needs `G, R, ε` | Needs the gap estimate `r`; Goffin uses only the direction of `g+e`. Loses the factor `≤ β/α` |

**Reduction check.** Every component of the result follows by composing standard arguments. The error bound gives `⟨g+e, x−u⟩ ≥ (μ−ρ)‖x−u‖ ≥ (1−ρ/μ)Δ(x)`. The multiplicative gap estimate acts as a varying Polyak relaxation factor in `[cα, cβ]`. Polyak's step ratio is invariant under the common scale `γ` (lemma `scale_invariance`).

For Goffin's method, let `c₀ = (μ−ρ)/(G+ρ)`. Use the step `t_k = (c₀/2)R q^k` with `q² = 1 − c₀²/2`. Then
`‖x_{k+1}−u‖² ≤ d_k² − 2t_k c₀ d_k + t_k²`.
Whenever `d_k ≤ Rq^k`, the right-hand side is at most `R²q^{2k+2}`. Since `f(x_K) − f* ≤ G·d_K`, this gives `K = O(c₀⁻² log(1+GR/ε))`. The repository proof follows exactly this ancestry: Polyak's relaxed-step argument (lemma `interval_progress`) plus the `(μ−ρ)` support inequality. I found no new mechanism.

**Search coverage.** I searched on 2026-10-07 across arXiv and journal sources on Polyak and Goffin steps, sharp minima, inexact `f*`, and inexact subgradients. I read the theorem text of Davis–Drusvyatskiy–MacPhee–Paquette (arXiv 1803.02461, JOTA 2018). For Polyak 1969/1979 and Goffin 1977 I relied on their statements as summarized there. I could not access Nedić–Bertsekas (Math. Program. 125, 2010), which treats noisy subgradients under weak sharpness. Ablaev–Stonyakin et al. ([arXiv 2212.06055](https://arxiv.org/abs/2212.06055)) treats Polyak steps with an inexact minimum value; I checked only its abstract. Git history dates the result's introduction to 2026-09-23 (commit 8646a89). There is no companion note.

## Conclusion

**No: this is another analysis of a Polyak-type method, obtained by composing known arguments, with no complexity gain.**

The strongest applicable baseline is Goffin's normalized subgradient method with geometrically decaying steps. On this exact class it needs only the direction of `g+e`:

| | Oracle calls |
|---|---|
| Goffin (geometric steps) | `O(1 + ((G+ρ)/(μ−ρ))² log(1+GR/ε))` |
| This result | `O(1 + (β/α)((G+ρ)/(μ−ρ))² log(1+GR/ε))` |

So the selected method is never faster and is worse by up to `β/α` when the gap estimate is loose. Its one advantage is that its updates do not need `G` or `R`. That advantage is weak, because the proved stopping index still requires `G`, `R` and `ε`. Exact-`f*` Polyak, the special case `α = β`, `ρ = 0`, already has this G- and R-free update property.

Each ingredient is standard: relaxed Polyak steps (multiplicative gap estimate), the `μ → μ−ρ` robustness argument, and scale invariance. The combined statement may not appear verbatim in the literature, and Nedić–Bertsekas 2010 was unchecked; neither changes the assessment. What can be claimed is a clean formal proof of a routine corollary of Polyak's relaxed-step analysis.

**Verdict: ALREADY KNOWN OR STANDARD COROLLARY**
**Confidence: medium**
