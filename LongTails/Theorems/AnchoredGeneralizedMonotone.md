# Accelerated root finding for monotone (L0, L1)-Lipschitz operators

This note explains the contribution formalized in
[AnchoredGeneralizedMonotone.lean](AnchoredGeneralizedMonotone.lean).

The theorem gives an oracle-complexity bound for finding an approximate root of a monotone operator that is (L0, L1)-Lipschitz rather than globally Lipschitz. A single anchored extragradient run with an explicit, observable step rule reaches ‖F(x)‖ ≤ ε in

  O( L0 R/ε + (1 + L1 R) · log(1 + (L0 + L1 G) R/ε) )

evaluations of F, where R bounds the distance from the start to a root and G bounds the initial residual ‖F(x0)‖. The best published bound for this class is O(L0² R²/ε² + L1² R²).

## Setup and proved guarantee

The [setup](../Setups/GeneralizedLipschitzMonotone.lean) is the unconstrained root-finding problem F(x) = 0 on a real inner-product space E of any dimension.

- **Operator class.** F : E → E is continuous and monotone, ⟨F x − F y, x − y⟩ ≥ 0, and satisfies the 1-symmetric (L0, L1)-Lipschitz condition

    ‖F x − F y‖ ≤ (L0 + L1 · max_{θ∈[0,1]} ‖F(x + θ(y − x))‖) · ‖x − y‖.

  The Lean statement uses the equivalent form without a maximum: if ‖F‖ ≤ M on the whole segment then ‖F x − F y‖ ≤ (L0 + L1 M)‖x − y‖. Continuity makes the maximum exist; it is not an extra restriction, because the condition itself forces local Lipschitz continuity once F is locally bounded.
- **Solution and scale parameters.** There is a root x* with ‖x0 − x*‖ ≤ R, and ‖F(x0)‖ ≤ G. The validity conditions are L0 > 0, L1 ≥ 0, G ≥ 0, R ≥ 0, ε > 0.
- **Oracle and cost.** One call returns F at the queried point. The cost is the number of calls.
- **Success.** The returned point satisfies ‖F(x)‖ ≤ ε.
- **Information.** The algorithm is constructed from (L0, L1, x0) only. R, G and ε appear in the budget and nowhere in the method.

The assumption is Assumption 1.1 of Choudhury–Loizou with α = 1, introduced for variational inequalities by Vankov, Nedich and Sankar. With L1 = 0 it is ordinary L0-Lipschitz continuity.

**Algorithm.** The [algorithm](../Algorithms/AnchoredExtragradient.lean) keeps the anchor a = x0, the current point x_k and the accumulated step S_k (S_0 = 0). Iteration k makes two calls:

  p_k = F(x_k),  m_k = ‖p_k‖ + ‖x_k − a‖/S_k  (the second term is 0 at k = 0),
  γ_k = 1/(4(L0 + L1 m_k)) at k = 0, and min{ S_k/3, 1/(4(L0 + L1 m_k)) } afterwards,
  S_{k+1} = S_k + γ_k,  β_k = γ_k/S_{k+1},
  x_{k+1/2} = x_k + β_k(a − x_k) − (1 − β_k) γ_k p_k,
  x_{k+1} = x_k + β_k(a − x_k) − γ_k F(x_{k+1/2}).

The output is the current x_k. With a constant step this is the fast extragradient method of Lee and Kim. There is no line search, no restart and no switch between phases.

**Guarantee.** With

  n = ⌈11 L0 R/ε + (27 L1 R + 4) · ln(1 + 8 (L0 + L1 G) R/ε)⌉,

the point x_{n+1}, reached after the public budget of 2(n + 1) calls, satisfies ‖F(x_{n+1})‖ ≤ ε. Since ln t ≤ t, the parts of the logarithm that grow with 1/ε are themselves O(L0 R/ε), so the bound is also O(L0 R/ε + (1 + L1 R) · ln(2 + L1 R (1 + L1 G/L0)) + ln(2 + L1 G/L0)).

**Lean layout.**
- [AnchoredExtragradientStep](../Proofs/AnchoredExtragradientStep.lean): the local Lipschitz inequality, the potential identity, and the one-step bounds.
- [AnchoredExtragradientRun](../Proofs/AnchoredExtragradientRun.lean): the invariants along the run, the step-growth potential, and the accuracy theorem.
- [AnchoredExtragradientExecution](../Proofs/AnchoredExtragradientExecution.lean): the algorithm's execution equals the analysed recursion, with two calls per iteration.

## Mechanism

Write Γ = S_k + γ_k, V_k = (S_k²/2)‖F x_k‖² + S_k⟨F x_k, x_k − a⟩ and E_k = ‖x_k − x*‖².

1. **Local inequality.** If L1‖x − y‖ ≤ 1 then ‖F x − F y‖ (1 − L1‖x − y‖) ≤ (L0 + L1‖F x‖)‖x − y‖. It follows from the assumption by bounding the segment maximum in terms of itself; no exponential factor appears.
2. **An observable step rule certifies both extragradient segments.** The half step has length at most γ_k m_k, because the anchor pull β_k‖x_k − a‖ is at most γ_k‖x_k − a‖/S_k. The rule γ_k(L0 + L1 m_k) ≤ 1/4 therefore gives ‖F x_{k+1/2} − F x_k‖ ≤ m_k/3 and then ‖F x_{k+1} − F x_{k+1/2}‖ ≤ ‖x_{k+1} − x_{k+1/2}‖/(2γ_k). Nothing about the trajectory is assumed in advance.
3. **Potential.** V_k − V_{k+1} equals a nonnegative multiple of ⟨F x_{k+1} − F x_k, x_{k+1} − x_k⟩ plus (Γ²/2)(‖x_{k+1} − x_{k+1/2}‖²/γ_k² − ‖F x_{k+1} − F x_{k+1/2}‖²). Hence V_k ≤ 0 and S_k‖F x_k‖ ≤ 2‖a − x*‖.
4. **Distance control.** Anchored extragradient iterates are not Fejér monotone. The proof shows E_k ≤ (5/4)R² for all k. The first step satisfies γ_0‖F(x0)‖ ≤ R/2, which is the only place where a large initial residual could have produced a factor e^{L1 R}. For k ≥ 1 the cap γ_k ≤ S_k/3 gives β_k ≤ 1/4 and E_{k+1} ≤ β_k R² + (1 − β_k)E_k.
5. **Step growth.** Steps 3 and 4 give S_k m_k ≤ 5R, so γ_k ≥ min{S_k/3, 1/(4L0 + 20 L1 R/S_k)}. The function Ω(S) = 4 L0 S + (20 L1 R + 3) ln S then increases by at least 3/4 per iteration, and S_1 = 1/(4(L0 + L1‖F x0‖)). Reaching S ≥ 2R/ε takes at most (4/3)(Ω(2R/ε) − Ω(S_1)) further iterations, which is the stated count.

## Relation to prior results

- **Choudhury and Loizou ([arXiv:2510.22421](https://arxiv.org/abs/2510.22421), NeurIPS 2025 per the arXiv listing).** For the same class, extragradient with step ν/(L0 + L1‖F(x_k)‖) satisfies min_{k≤K} ‖F(x_k)‖ ≤ √2 L0 R/(ν√(K+1) − √2 L1 R) once K + 1 ≥ 2 L1² R²/ν² (Theorem 3.6), that is O(L0² R²/ε² + L1² R²) calls; Theorem 3.5 has no burn-in but a factor (1 + L1 R e^{L1 R})². This is the baseline. The assumption is their Assumption 1.1, following Vankov, Nedich and Sankar ([ICML 2024](https://proceedings.mlr.press/v235/vankov24a.html)).
- **What a routine argument already gives.** Extragradient is residual-nonincreasing under that step rule, so the baseline bounds hold for the last iterate too. After its burn-in, regularizing with μ ≈ ε/R and running extragradient on the strongly monotone problem gives O(L1² R² + (L0 R/ε) log(L0 R/ε)), with knowledge of R and ε. The present theorem therefore improves the published leading term from L0² R²/ε² to L0 R/ε, and improves on the routine bound by removing the logarithm from the leading term and the need to know R or ε.
- **Leading term.** For L-Lipschitz monotone operators, deterministic first-order methods need Ω(L R/ε) evaluations when the dimension is large compared with the number of evaluations (Yoon and Ryu, [arXiv:2102.07922](https://arxiv.org/abs/2102.07922), ICML 2021), and that class is the case L1 = 0 here. In that regime the term L0 R/ε cannot be improved beyond its constant. The lower bound says nothing about a fixed low dimension.
- **Additive term.** The gain over L1² R² is conditional. It holds when log(1 + L1 G/L0) is small compared with L1 R, in particular whenever the initial residual is at most polynomial in the problem parameters. In the worst case over G, namely G = L0 R e^{L1 R} (which always holds, by Proposition 3.1 of Choudhury–Loizou), the bound becomes O(L0 R/ε + L1² R² + 1), the same order as the baseline's additive term. No lower bound on an L1-dependent additive cost is known to us.
- **Anchored extragradient.** The template is EAG (Yoon and Ryu) and FEG (Lee and Kim, [arXiv:2106.02326](https://arxiv.org/abs/2106.02326), NeurIPS 2021), both for globally Lipschitz operators; FEG-A is a backtracking variant. The weight β_k = γ_k/Σγ and the ending ‖F(x_k)‖ ≤ 2R/Σγ for variable steps are used by line-search anchored methods, for example the moving-anchor method of Sun, Zhang and Zhao ([arXiv:2607.07585](https://arxiv.org/abs/2607.07585)), whose rate requires global Lipschitz continuity. These parts are not new here.
- **Other work beyond global Lipschitz continuity.**
  - Zhang ([arXiv:2606.22392](https://arxiv.org/abs/2606.22392)) analyses anchored methods under Hölder continuity with decaying steps and rates slower than 1/k.
  - Yoon, Choudhury, Greenberg and Loizou ([arXiv:2609.26581](https://arxiv.org/abs/2609.26581)) give Polyak-type extragradient steps with unaccelerated rates.
  - Shen and Kılınç-Karzan ([arXiv:2604.07662](https://arxiv.org/abs/2604.07662)) give a backtracking extragradient method for locally Lipschitz operators with an o(1/√T) last-iterate rate.
  - Ou, Themelis and Latafat ([arXiv:2609.15936](https://arxiv.org/abs/2609.15936)) give an adaptive unaccelerated method under local Lipschitz continuity, with constants depending on a Lipschitz modulus over a bounded set containing the iterates. For this class that modulus can be as large as L0 e^{L1 R}.

  We found no accelerated O(1/k) residual rate under (L0, L1)-Lipschitzness, no closed-form residual-plus-anchor step rule, and no distance bound for adaptive anchored iterates (searches dated 2026-10-02).
- **Minimization analogue.** For convex (L0, L1)-smooth minimization, Gorbunov et al. ([arXiv:2409.14989](https://arxiv.org/abs/2409.14989)) give unaccelerated rates with an L0-only leading term and an additive L1² R² cost, and an accelerated method whose rate carries an exponential factor in L1 R. Accelerated leading terms of order √L0 R/√ε with an additive L1-dependent cost are due to Vankov et al. and, without extra factors for small ε, Tyurin ([arXiv:2508.06884](https://arxiv.org/abs/2508.06884)). The theorem here is the operator counterpart with the residual criterion.

**What is new.** The step rule of item 2, the distance bound of item 4, and the counting argument of item 5, which together give the first accelerated guarantee for this operator class.

## Example

Take F(x, y) = (sinh(x) + A y, sinh(y) − Aᵀx) on ℝⁿ × ℝⁿ, the saddle operator of Σ cosh(x_i) − Σ cosh(y_i) + xᵀA y, with ‖A‖ < 1 and sinh applied coordinatewise. It is monotone and not globally Lipschitz, and A couples all coordinates. Its Jacobian has norm at most 1 + ‖A‖ + ‖sinh u‖, and ‖F(u)‖ ≥ (1 − ‖A‖)‖sinh u‖, so the assumption holds with L0 = 1 + ‖A‖ and L1 = 1/(1 − ‖A‖), independent of n. Nothing is claimed for ‖A‖ ≥ 1.

## Scope and limitations

- **α = 1 only.** The baseline paper also treats α ∈ (0, 1); that case is not covered.
- **Unconstrained, deterministic.** No constraints, proximal terms or stochastic oracles.
- **L0 > 0 and known L0, L1.** The step uses both constants, as the baseline does.
- **Constants.** They are not optimized. With L1 = 0 the bound is about five times the FEG bound 2 L0 R/k at step 1/L0, and the first iteration spends a redundant second call.
- **Witness properties.** The theorem is an oracle-complexity statement for the class. That the witness is a single anchored run returning its last point describes the proof, not a separately stated guarantee, and the last-iterate property is not claimed as new relative to extragradient.
- **Computer assistance.** The potential identity and the invariants were checked numerically before formalization. Every step is proved in Lean without `sorry` or extra axioms.
