# SurjectiveStochasticInequalityKkt: novelty assessment

[Theorem](../../LongTails/Theorems/SurjectiveStochasticInequalityKkt.lean) · [setup](../../LongTails/Setups/StochasticSurjectiveInequalities.lean) · [algorithm](../../LongTails/Algorithms/SurjectiveProxLinear.lean)

**What is proved.** The problem is min f(x) s.t. c(x) ≤ 0 (m inequalities, any finite dimension), where the gradient, constraint values and Jacobian are all stochastic. The mean Jacobian must be surjective at every point, for all rows, with ‖λ‖ ≤ H‖J(x)ᵀλ‖. A clipped, ridge-regularized stochastic prox-linear method with a STORM/SARAH-type estimator and a random output time then returns (x, λ ≥ 0). With probability ≥ 3/4, at that x the true stationarity residual ‖∇f+Jᵀλ‖, the infeasibility ‖[c]₊‖, and the complementarity Σ|λᵢcᵢ| are each ≤ ε.

**Budget.** The proved budget is the number of paired same-sample queries. Each query costs 2 evaluations of each of g, v, D:

  N = O( 1 + (m²H¹⁰Δ + m⁴H¹⁸σ²)/ε² + m⁴H¹⁹Δσ/ε³ ).

- H ≥ 1 is one common bound on ‖∇f‖, the Frobenius norm ‖J‖_F, their Lipschitz constants, the mean-square smoothness of the oracle triple, and the reciprocal smallest singular value of J.
- σ² bounds the summed variance of the triple.
- Δ bounds the initial gap of the exact penalty f + 4H(H+1)Σ[cᵢ]₊.
- The domain is m ≥ 1 and 0 < ε ≤ 1.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Tran-Dinh–Pham–Nguyen, [ICML 2020](https://proceedings.mlr.press/v119/tran-dinh20a.html), Thm 4.3 (SARAH Gauss–Newton), applied to the composite φ(F) with φ = hinge penalty | values O(σ²/ε⁴ + Δ/ε⁵), Jacobians O(σ²/ε² + Δ/ε³), with constants polynomial in m,H that I did not derive → N for every primitive | Values: ε⁻⁵ → ε⁻³ for fixed m,H, σ>0, Δ>0 and ε→0. Jacobian/gradient: none, same ε⁻³ | None. Their class is broader: Lipschitz convex outer function, no surjectivity | Their output is E‖G̃_M‖² ≤ ε² (a gradient mapping of the penalty) at a random iterate. Turning it into a KKT pair with constant probability takes Markov's inequality plus a surjectivity-based multiplier argument; I did not check that conversion separately | The present result needs global full-row-rank J; a broader class is not a performance disadvantage for the baseline. The factors H¹⁹, m⁴ and 2⁴⁸ can dominate at moderate ε |
| Shi–Wang, [arXiv:2511.03210v2](https://arxiv.org/abs/2511.03210) (Nov 2025), Thm 7 (recursive momentum), for c(x)=0, x ≥ 0. Applies only to the subclass reached through linear slacks and satisfying its assumptions | gradients/Jacobians Õ(ε⁻³), values Õ(ε⁻⁵), with probability 1−ε → N | Values: ε⁻⁵ up to logarithms → ε⁻³, on the common subclass | Their almost-surely bounded noise, samplewise smoothness, and bounded c and lower-bounded f on the iterate region → finite variance, mean-square smoothness, and only a penalty lower bound | Their confidence is 1−ε; ours is a fixed 3/4, with no δ-dependence proved | Their Strong MFCQ is weaker than global surjectivity of every row. Their stochastic theorems are stated for equality plus x ≥ 0; the general-inequality extension is asserted, not proved |
| Cui–Shi–Wang–Xiao (SmALM), [optimization-online, June 2026](https://optimization-online.org/wp-content/uploads/2026/06/SmALM-5.pdf), Thm 4.2. Covers equality constraints only | O(ε⁻³) per primitive (expected stochastic ε-KKT) → not comparable | Not comparable: the classes do not overlap, because writing c = 0 as ±c ≤ 0 breaks surjectivity | Hessian-Lipschitz requirement (Assumption 1.3) → only C¹,¹; equality → inequality | None verified | Equality problems are outside the present class. SmALM already gives the all-primitive ε⁻³ exponent there |

**Reduction check.**
- *Squared slacks into SmALM.* The Jacobian [J, 2diag(s)] does stay surjective. The reduction still fails at three points:
  - first-order points of the reformulation do not force λᵢ ≥ 0 when sᵢ = 0;
  - it needs C²,¹ data;
  - the slack Jacobian 2s is unbounded.
- *Linear slacks.* These need bound constraints, which SmALM does not treat.
- *Quadratic penalties.* These need ρ ≍ 1/ε. The realized results of that type for stochastic constraints are ε⁻⁵ (Alacaoglu–Wright, [AISTATS 2024](https://proceedings.mlr.press/v238/alacaoglu24a.html), equality only).
- *The new step.* The prox-linear step is Lipschitz in the value error (not square-root): the dual of the subproblem is strongly concave under surjectivity. The descent argument is carried out on a Moreau-envelope potential rather than on the model gap. Nonsmooth composite analyses enter value errors linearly. The note's scalar tanh example shows why that breaks a model-gap argument; I did not re-derive the example.
- *Proof ancestry.* Recursive variance reduction (SARAH/STORM), the Moreau-envelope analysis of weakly convex functions (Davis–Drusvyatskiy), and Lipschitz QP sensitivity under LICQ. These supply tools, not the stated complexity.

**Search coverage.** Searched 2026-11-06: arXiv, PMLR, optimization-online.
- Read: theorem statements of Tran-Dinh et al. and SmALM (full text), and Shi–Wang (HTML, partly via summaries).
- Abstract/HTML level only: Alacaoglu–Wright, arXiv:2608.27676 (inequalities only through a convex g; ε⁻⁵ with stochastic constraints) and arXiv:2601.20345 (deterministic constraints).
- Not verified independently: Zhang–Xiao Thm 3, Wu–Grimmer, NS-SQP (Oct 2026), and the note's arXiv:2609.34099 / 2611.04403.
- The theorem was introduced in commit 79aa4a56 (2026-11-06), so every source above predates it.
- I found no mismatch between the companion note and the Lean statement. Its readings of SmALM and Shi–Wang agree with what I read.

## Conclusion

**Yes: on this class, the cost in stochastic constraint values improves from ε⁻⁵ to ε⁻³, but the class is narrow.**

The strongest applicable baselines are SARAH-type stochastic prox-linear/Gauss–Newton (Tran-Dinh et al., Thm 4.3) and Shi–Wang's recursive-momentum method on a common slack subclass. For fixed m, H, σ > 0, Δ > 0:

| | gradient / Jacobian calls | constraint-value calls |
|---|---|---|
| prior | ε⁻³ | ε⁻⁵ |
| this result | ε⁻³ | ε⁻³ |

The gain appears only as ε → 0. The proved constants (H¹⁹, m⁴, 2⁴⁸) can dominate at moderate accuracy, and the gradient and Jacobian exponents are unchanged.

The price is a strong assumption: every inequality row, active or not, must have a uniformly full-rank mean Jacobian on the whole space. That excludes redundant constraints, m larger than the dimension, and typical compact feasible sets. It does cover nonlinear families such as y ≤ A tanh(Bx) with dense A and B. The equality-constrained case already has all-primitive ε⁻³ (SmALM), but it does not transfer: squared slacks lose the multiplier sign, and linear slacks need bound constraints that SmALM does not handle.

The comparison does establish the exponent gain over the checked analyses. Priority is less certain, because a recent SQP preprint (Oct 2026) and several cited sources went unchecked. The claimable contribution: the first verified ε⁻³ cost in every primitive, including stochastic constraint values, for nonlinear inequality constraints under global uniform surjectivity, at constant success probability.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
