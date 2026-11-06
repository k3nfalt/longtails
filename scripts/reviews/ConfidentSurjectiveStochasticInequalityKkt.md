# Novelty assessment: ConfidentSurjectiveStochasticInequalityKkt

**What is proved.** For `min f(x)` subject to `c_i(x) ≤ 0` (i ≤ m) on a finite-dimensional Hilbert space, with unbiased, finite-variance, mean-square-smooth stochastic triples `(∇f, c, J)`, the [theorem](../../LongTails/Theorems/ConfidentSurjectiveStochasticInequalityKkt.lean) shows that the replicated variance-reduced prox-linear [algorithm](../../LongTails/Algorithms/SurjectiveConfidence.lean) returns `(x, λ)` satisfying, with probability at least `1−δ`, `λ ≥ 0`, `‖∇f+J*λ‖ ≤ ε`, `‖[c]₊‖ ≤ ε`, and `∑|λ_i c_i| ≤ ε`. The [setup](../../LongTails/Setups/StochasticSurjectiveInequalities.lean) assumes globally `‖∇f‖, ‖J‖_F, Lip(∇f), Lip(J) ≤ H` and `‖λ‖ ≤ H‖J(x)*λ‖` for **every** `x` and **every** row, including inactive ones.

**Complexity (paired same-sample calls, each giving the triple at two points):**

N = O( log(2/δ)·[1 + m²H¹⁰Δ/ε² + m⁴H¹⁹Δσ/ε³] + log²(2/δ)·[1 + m⁴H¹⁸σ²/ε²] ),

with `m ≥ 1` constraints, `H ≥ 1` the common regularity bound, `Δ ≥ 0` the gap of the exact penalty `f + 4H(H+1)∑[c_i]₊` at `x₀`, `σ ≥ 0` the joint noise level, `0 < ε ≤ 1`, and `0 < δ < 1`. The algorithm needs `m, H, Δ, σ, ε, δ`. This bound follows directly from `total_call_budget`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Zhang–Xiao, [arXiv:2004.04357v2](https://arxiv.org/abs/2004.04357v2) (Math. Program. 2022), Thm 3, applied to the hinge penalty `h(f,c)`; the norm-scale KKT conversion uses this setup's surjectivity | values `O(ε⁻⁵)`, Jacobians `O(ε⁻³)`, in expectation, for fixed `m,H,Δ,σ` (their constants not mapped); joint calls `O(ε⁻⁵)` → `O(ε⁻³log(2/δ) + ε⁻²log²(2/δ))` | value calls `ε⁻⁵ → ε⁻³`, for fixed `m,H,Δ,σ>0` and `log(2/δ) ≪ ε⁻²` | None: their outer function and regularity are broader | `E‖G_M‖² ≤ t` → KKT pair with complementarity, probability `1−δ` | needs global surjectivity (forces `m ≤ dim E`); `poly(m,H)` factors up to `m⁴H¹⁹` |
| Alacaoglu–Wright, [AISTATS 2024](https://proceedings.mlr.press/v238/alacaoglu24a.html), Thm 3.1. Special case only, via slacks `c(x)+s=0`, `X=E×ℝ₊ᵐ`: their (A5) holds with constant `1/H`, but their (A4) bound on `‖c‖` must also hold for the slack constraints, which it does only when the slacks stay bounded (unverified) | `Õ(ε⁻⁵)` expected → as above | `ε⁻⁵ → ε⁻³` and no `ε`-logarithm, same regime | bounded samples, values and `|f|` (A4) → finite variance only | "∃λ" with expected residuals → explicit `λ`, complementarity, `1−δ` | global `‖∇f‖ ≤ H` is still required |
| Shi–Wang, [arXiv:2511.03210v2](https://arxiv.org/abs/2511.03210v2), Thm 7 (preprint). Restricted to bounded `c`, level-bounded `f`, sample-wise smoothness | `Õ(ε⁻³)` gradients, `Õ(ε⁻⁵)` values, with probability `1−ε` → as above | value calls `ε⁻⁵ → ε⁻³` on the common subclass | bounded `c` and level-bounded `f` → penalty lower bound only | probability tied to `ε` → any `δ` | **Incomparable classes:** their slack-form strong MFCQ allows redundant rows and `m > d`; this result does not |

**Reductions and mechanism.** I checked the obvious reduction to equality constraints. [Cui et al., arXiv:2606.28230](https://arxiv.org/abs/2606.28230) (June 2026), Thm 4.2, get `O(ε⁻³)` for every primitive, but only for equalities, and they also need Lipschitz Hessians and bounded `c`. With squared slacks `c+s²=0`, the Jacobian `[J, 2diag(s)]` keeps full rank under this setup, which contradicts the companion note's claim that rank is lost. The reduction still fails for a different reason: first-order KKT points of the slack problem do not force `λ ≥ 0`. A Huber-smoothed penalty with compositional variance reduction is the other candidate. There the outer smoothness grows like `ρ/μ` with `μ ≲ ε/(mρ)`, so I found no `ε⁻³` route, though I did not derive its exact exponent. The new ingredient is a quadratic bound on how errors in the constraint *values* move the subproblem step, combined with a Moreau-envelope potential. Proof ancestry: SPIDER/SARAH recursive estimators; Ghadimi–Lan post-selection and Minsker median-of-means for the confidence wrapper. The wrapper is routine.

**Search coverage (2026-11-06 UTC).** I read the full theorem statements of Zhang–Xiao, Alacaoglu–Wright, Li et al. ([arXiv:2212.09513](https://arxiv.org/abs/2212.09513), `O(ε⁻⁵)`, equality constraints, compact domain), Shi–Wang, Cui et al. (Fletcher ALM), Liu–Xu ([arXiv:2501.19214v3](https://arxiv.org/abs/2501.19214), weakly convex, compact domain, `O(ε⁻⁶)` values; read only partly), [arXiv:2504.07607](https://arxiv.org/abs/2504.07607) (stochastic *linear* constraints, compact polyhedral `X`, `ε⁻³` only sketched in Remark 5.8) and MoSSP ([arXiv:2605.29635](https://arxiv.org/abs/2605.29635), deterministic `c`). I did not independently check Wu–Grimmer or the October 2026 NS-SQP preprint. The result was introduced in commit `a34c39b5` (2026-11-06); all of the work above predates it.

## Conclusion

**Yes: for stochastic inequality constraints, the proved value-oracle complexity improves from ε⁻⁵ to ε⁻³, but only under a strong global full-rank assumption.**

The strongest checked baselines for fully stochastic nonlinear inequality constraints are Zhang–Xiao's prox-linear method and Shi–Wang's directional decomposition. Both need order ε⁻⁵ constraint-value samples:

| | constraint-value / joint calls |
|---|---|
| prior (Zhang–Xiao, Shi–Wang, Alacaoglu–Wright) | `O(ε⁻⁵)` |
| this result | `O(m⁴H¹⁹Δσ ε⁻³ log(2/δ) + m⁴H¹⁸σ² ε⁻² log²(2/δ) + m²H¹⁰Δ ε⁻² log(2/δ))` |

The gain holds for fixed `m, H, Δ, σ > 0` and `log(2/δ) ≪ ε⁻²`. At moderate `ε` it can be cancelled by factors such as `m⁴H¹⁹`.

The price is the assumption that the whole mean Jacobian, inactive rows included, is uniformly surjective everywhere, together with globally bounded gradients. This excludes redundant constraints and `m > d`, which Shi–Wang's strong MFCQ allows, so the classes are incomparable rather than nested. Nonlinear instances such as `c(x,y) = y − A tanh(Bx)` do satisfy every assumption, so the class is not empty or trivial. The known equality-constraint `ε⁻³` result does not carry over through slack variables, because the multiplier sign is lost.

The comparison establishes the exponent gain. The literature search found no earlier `ε⁻³` inequality result, but this fast-moving 2026 literature was not exhaustively checked. The claimable contribution is the first verified `O(ε⁻³)` all-primitive KKT complexity for stochastic nonlinear *inequality* constraints, under global surjectivity; the arbitrary-confidence wrapper itself is standard.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
