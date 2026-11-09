# ε⁻² stochastic subgradient complexity for χ²-constrained DRO

Lean theorem: [`ChiSquareBracketedDro.lean`](ChiSquareBracketedDro.lean) (`OracleTemplate.ChiSquareBracketedDro.result`).
Setup: [`Setups/ChiSquareConstrainedDro.lean`](../Setups/ChiSquareConstrainedDro.lean).
Algorithm: [`Algorithms/ChiSquareBracket.lean`](../Algorithms/ChiSquareBracket.lean) (`bracketAlgorithm`).
Main proof modules: [`Proofs/ChiSquareDuality.lean`](../Proofs/ChiSquareDuality.lean),
[`Proofs/ChiSquarePerspective.lean`](../Proofs/ChiSquarePerspective.lean),
[`Proofs/ChiSquareSgd.lean`](../Proofs/ChiSquareSgd.lean),
[`Proofs/ChiSquareSelection.lean`](../Proofs/ChiSquareSelection.lean),
[`Proofs/ChiSquareConvergence.lean`](../Proofs/ChiSquareConvergence.lean).

## Problem

Let `P0` be a probability distribution on a sample space `Ξ`, and let `X` be a closed convex subset of a real Hilbert space `E`. The χ²-constrained distributionally robust objective is

```
L(x) = sup { E_{P0}[q(ξ) ℓ(x; ξ)] : q ≥ 0 measurable, q ∈ L²(P0), E q = 1, ½ E (q − 1)² ≤ ρ } .
```

This is the objective (3) of Levy, Carmon, Duchi and Sidford, written for a general `P0` rather than an empirical distribution. It uses their convention `D_χ²(q) = ½ E(q − 1)²`. In Lean this is `objective`, a supremum over `IsFeasibleDensity` weights. The proof shows that this set is nonempty (`q = 1`) and bounded above, using weak duality.

The task is to minimize `L` over `X`.

**Assumptions** (`spec.admissible`):
- `ρ > 0`.
- For every sample `ξ` and every `x ∈ X`, the loss satisfies `0 ≤ ℓ(x; ξ) ≤ B`.
- The loss is convex on `X`, with a measurable subgradient selection `g(x; ξ)` satisfying `‖g(x; ξ)‖ ≤ G`. Lean states this as the subgradient inequality on `X`.
- There is a minimizer `x⋆ ∈ X` of `L` with `‖x0 − x⋆‖ ≤ R`.
- Samples are i.i.d. from `P0`, stated with the shared `IID` structure. `P` is an abstract law, not a prescribed product measure.
- The loss and the subgradient are jointly measurable, and the projection onto `X` is measurable.

These are the standing assumptions of Levy et al. (§2, "Assumptions"): a closed convex domain, a loss in `[0, B]` that is convex and `G`-Lipschitz, and i.i.d. sampling. There is one mild relaxation: we need only `‖x0 − x⋆‖ ≤ R`, not `diam X ≤ R`. No smoothness and no inverse-cdf assumption (their A1/A2) is used.

**Oracle and cost model** (`sampleOracle`). A query `y ∈ E` draws a fresh sample `ξ_k` and returns `(Π_X(y), ℓ(Π_X(y); ξ_k), g(Π_X(y); ξ_k))`. One call therefore costs one stochastic loss/subgradient evaluation plus one Euclidean projection. The public budget counts calls.

**Accuracy criterion** (`spec.successful`). The returned point `x̂` is measurable, lies in `X`, and satisfies `E[L(x̂)] − L(x⋆) ≤ ε`. This is the criterion of Levy et al.'s Table 1.

## Result

The theorem `result : Convergence spec budget` holds with the explicit public budget

```
budget = (clog₂ ⌈8 √(1+2ρ) (B + B/√ρ) / ε⌉ + 2)² · (⌈2¹⁶ (1+2ρ) (G²R² + B²(1 + 1/ρ)) / ε²⌉ + 144)
```

That is,

```
N(ε) = O( (1+ρ) (G²R² + B²(1 + 1/ρ)) / ε² · log²( (1+ρ) B / (√ρ ε) ) ) .
```

The bound is independent of the sample-space size and of the dimension of `E`. It is an expected-accuracy guarantee with a deterministic number of oracle calls.

## Algorithm (`bracketAlgorithm`)

The method runs projected stochastic subgradient descent on the joint dual. Write `c = √(1+2ρ)`.

1. **Dual and perspective majorizer.** Weak duality gives `L(x) ≤ F(x, η) := η + c ‖(ℓ(x; ·) − η)₊‖_{L²(P0)}` for every `η` (`weak_duality`). Strong duality is attained at some `η⋆ ∈ [−B/√ρ, B]` (`strong_duality`). The proof is derivative-free: it takes the smallest root of `h(η) = c E(ℓ − η)₊ − ‖(ℓ − η)₊‖₂`, and handles a degenerate root by an indicator density. The algorithm minimizes the jointly convex majorizer

   ```
   Φ(x, η, s) = η + c E[(ℓ(x;ξ) − η)₊²]/(2s) + c s/2 = F(x, η) + (c/2s)(s − s(x, η))²,
   ```

   where `s(x, η) = ‖(ℓ(x;·) − η)₊‖₂`. Its unbiased one-sample stochastic subgradient is available from one oracle call.
2. **Brackets.** For `j = 0, …, J` with `J = clog₂⌈8cB'/ε⌉` and `B' = B + B/√ρ`, the method runs `T` steps of projected SGD on `(x, η, s) ∈ X × [−B/√ρ, B] × [s_j, 4 s_j]`, where `s_j = 2^j ε/(8c)`. The step sizes are constant and explicit. It returns the averages `(x̄_j, η̄_j)`.
3. **Selection.** Using `m = (J+1) T` fresh samples per bracket, it estimates `F̂_j = η̄_j + c ( m⁻¹ Σ_i (ℓ(x̄_j; ξ_i) − η̄_j)₊² )^{1/2}` and outputs the `x̄_j` with the smallest `F̂_j`.

All parameters depend only on public data `(ρ, G, B, R, ε, x0)`. The Lean algorithm is a state machine run by `execute`. `execute_eq` proves that its output equals the mathematical procedure for every sample path, and that every one of the `(J+1)(T+m) ≤ budget` calls is counted.

## Technical mechanism

The joint dual, together with the perspective variable `s` (equivalently `ν` with `s = cν`), is known to Levy et al. (App. A.1.2). For the constraint they do not analyze it. In §1.1 they say the perspective transform makes dual SGM "unstable". The obstruction is the `1/s` factor in the stochastic subgradients, `(c (ℓ−η)₊/s) g` and `c/2 − c (ℓ−η)₊²/(2s²)`: its second moment involves `s(x,η)²/s²` and is unbounded in the worst case.

The new step is the **self-bounding lemma** (`self_bound`, `noise_self_bound`). Because `Φ − L⋆ ≥ (c/2s)(s − s(x, η))²`,

```
s(x, η)² ≤ 2 s² + (4 s / c) (Φ(x, η, s) − L⋆).
```

Restricted to a bracket `s ∈ [s_j, 4 s_j]` with `s_j ≥ ε/(8c)`, this bounds the second moment of the stochastic subgradient by a constant `A` plus `K (Φ − L⋆)`, with `K ≤ 1/2` (`noiseSlope_le`). The `K(Φ − L⋆)` part is absorbed by the descent term of projected SGD (`exp_step`, `bracket_bound`), so each bracket costs `O(ε⁻²)` steps. This holds although the raw noise is not bounded.

The bracket that contains `s(x⋆, η⋆)`, or the lowest bracket when that value is below `ε/(8c)`, has comparator bias at most `ε/16` (`good_bracket`). Selection with `m` samples costs `E(ŝ − s)² ≤ B'²/m` (`sqrt_mean_dev`). This uses `|ŝ − s| ≤ |ŝ² − s²|/s` and `Var(Z²) ≤ B'² E Z²`, so no extra moment assumption is needed. Jensen for the averages is proved directly from the per-sample majorizer inequality (`sample_ineq`, `phi_average_le`).

## Comparison with prior work

- **Levy, Carmon, Duchi, Sidford, "Large-scale methods for distributionally robust optimization", NeurIPS 2020** ([arXiv:2010.05893](https://arxiv.org/abs/2010.05893)).
  - *Same setting, assumptions and criterion.* Table 1 lists `ρ ε⁻³` (Thm. 4) for the χ² constraint against a lower bound `ρ ε⁻²` [their ref. 18].
  - *Their upper bound.* Theorem 4 brackets the penalty parameter `λ` and solves penalized subproblems by MLMC. Its cost is `≲ (GR)² (ρB + ε log₂(B/ε)) ε⁻³ · log²(1 + ρB/ε²)` gradient evaluations, with probability at least `1 − ε/B`.
  - *Their bound omits some terms.* Their Lemma 3 contains `B²` terms that the Theorem 4 display drops. Comparing against the display therefore favours their bound, so the comparison below is conservative.
  - *Open problem.* §6 states: "Establishing the optimal rate for this problem remains an open question." §8 states: "the corresponding result for χ² constraint remains open. In particular, there is a gap between our O(ρε⁻³) upper and the Ω(ρε⁻²) lower bound."
  - *Our result.* We close the ε-gap: our rate is `ε⁻²` up to `log²` factors, for every fixed `ρ > 0`.
- **Regime of improvement.** These comparisons ignore logarithms; when `ρB ≪ ε²` Levy et al.'s `log²` factor is itself small, so no conclusion is drawn there.
  - **ρ ≥ 1.** Ours is `≍ ρ (G²R² + B²)/ε²` and Levy's is `≍ ρ G²R² B/ε³`. Ours is smaller iff `ε ≲ G²R² B/(G²R² + B²)`, for example whenever `ε ≲ min(B, G²R²/B)`. Above that threshold, in the low-accuracy regime, Levy's displayed bound is smaller.
  - **ρ ≤ 1.** Ours is `≍ (G²R² + B²/ρ)/ε²` and Levy's is `≍ G²R²(ρB/ε + 1)/ε²`. Ours is smaller iff `ρ ≳ min{ B²/(G²R²), √(εB)/(GR) }`.
  - **ρ → 0.** When `ρ ≪ min{B²/(G²R²), √(εB)/(GR)}`, Levy's bound is better. Our bound degrades like `B²/(ρ ε²)` as `ρ → 0`, although the problem tends to ERM.
  - This limitation comes from the η-range `[−B/√ρ, B]` in our analysis. We do not know whether it is necessary. **The improvement is therefore not uniform in ρ.**
- **Lower bound.**
  - Levy et al. attribute an `Ω(ρ ε⁻²)` lower bound to Duchi and Namkoong, "Learning models with uniform performance via distributionally robust optimization", Ann. Statist. 2021 ([arXiv:1810.08750](https://arxiv.org/abs/1810.08750), Theorem 6).
  - With `k = 2` and the same `½(t − 1)²` convention, Theorem 6 gives minimax risk at least `(M/32)·√(2ρ/n)` for `ρ > 1/2`. The instance uses linear losses `θ x` with `x ∈ [−1, 1]` and `θ ∈ [−M, M]`, so `G = 1`, `R = 2M`, and `B = 2M` after a shift. Accuracy `ε` therefore needs `≳ ρ M²/ε²` samples.
  - This transfers to our oracle model, because any algorithm making `n` calls is a measurable function of `n` i.i.d. samples.
  - Hence, for `ρ ≥ 1` and `GR ≍ B`, our bound matches the lower bound in `ρ` and `ε` up to `log²` factors and constants. Optimality in `G`, `R` and `B` separately is not established.
  - The `G²R²` term matches the standard `Ω(G²R²/ε²)` lower bound for stochastic convex Lipschitz minimization.
- **Namkoong and Duchi, NeurIPS 2016**, stochastic primal-dual: `O((1 + ρN) ε⁻²)`. This depends on the number `N` of samples; our bound is `N`-independent and applies to general `P0`.
- **Carmon and Hausler, NeurIPS 2022** ([arXiv:2203.13225](https://arxiv.org/abs/2203.13225)): `Õ(N ε^{-2/3} + ε⁻²)` for finite-`N` empirical objectives. This is `N`-dependent, so it does not apply to population `P0`.
- **Qi et al., TMLR 2023** ([arXiv:2210.05740](https://arxiv.org/abs/2210.05740)): KL-constrained DRO with an added KL regularizer `λ0`.
  - *Misstatement.* Their §2 states that Levy et al. "achieved a convergence rate of Õ(1/ϵ²) for the χ²-constrained/regularized … convex DRO problems". This contradicts Levy et al.'s own Table 1, §6 and §8, which give `ρε⁻³` for the χ² constraint and state the question as open.
- **Im and Grigas** ([arXiv:2305.16584](https://arxiv.org/abs/2305.16584)) work with a truncated uncertainty set with lower-bounded weights. This changes the problem.
- **Standard reduction checked.** Combining Duchi–Namkoong's uniform convergence with full-batch or cutting-plane methods gives dimension-dependent rates: `ρ² d ε⁻⁴` (Levy et al., Table 1) and roughly `ρ² d² ε⁻²` (Levy et al., §8). Our bound is dimension-free. Bracketing `λ` in the penalized problem, as in Levy et al.'s Theorem 4, inherits the `λ⁻¹ε⁻²` penalized lower bound (their Thm. 3) at `λ ≍ ε/ρ`, which is where their `ε⁻³` comes from.

## Limitations

- The guarantee is in expectation, with a deterministic budget. No high-probability version is proved.
- The `B²/ρ` term makes the bound worse than Levy et al.'s when `ρ` is very small, as quantified above.
- The constants (`2¹⁶`, `144`) are loose. The logarithmic factor is `log²`, coming from `J+1` brackets with `m = (J+1)T` selection samples each.
- The novelty assessment is based on a literature search of NeurIPS, ICML, ICLR and arXiv from 2020 to 2026, including the papers above. We found no prior analysis of the constrained joint dual with a bracketed scale variable or a self-bounded noise argument. OpenReview submissions that are not on arXiv could not be checked.
