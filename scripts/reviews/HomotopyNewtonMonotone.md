# Novelty assessment: HomotopyNewtonMonotone

[`result`](../../LongTails/Theorems/HomotopyNewtonMonotone.lean) proves the following. Let `F : E → E` be a C², monotone operator on a finite-dimensional space of any dimension, with an `L`-Lipschitz second derivative `D²F` and a zero within `D` of `x₀`. Suppose `‖DF(x₀)‖ ≤ H₀`. Then [`HomotopyNewtonAEP`](../../LongTails/Algorithms/HomotopyNewtonAEP.lean), which queries only exact `F` and `DF`, returns its last outer iterate `z_N` with `‖F(z_N)‖ ≤ ε` deterministically. The setup is [`UnconstrainedLipschitzSecondDerivativeMonotone`](../../LongTails/Setups/UnconstrainedLipschitzSecondDerivativeMonotone.lean).

**Complexity.** For `L, D, ε > 0` and `H₀ ≥ 0`, the theorem charges `⌈2²¹(1+(LD³/ε)^{1/4})·log²(2+H₀D/ε+LD³/ε)⌉` calls to each of `F` and `DF`:

  O( (1 + (LD³/ε)^{1/4}) · log²(2 + H₀D/ε + LD³/ε) ) calls to `F` and `DF`.

Here `L` is the Lipschitz constant of `D²F`, `D` bounds `‖x₀−x⋆‖`, `H₀` bounds `‖DF(x₀)‖`, and `ε` is the residual target. Linear solves are not charged. The algorithm needs `L, D, H₀, ε`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Jiang–Yoon, AEP third-order, [arXiv 2609.30212v1](https://arxiv.org/abs/2609.30212) (24 Sep 2026, preprint), Thms 5.2–5.3 at p=3; lower bound Thm 6.1 | `O((1+(LD³/ε)^{1/4})·log(1+LD³/ε))` calls to an `(F, DF, D²F)` oracle → `O((1+(LD³/ε)^{1/4})·log²(2+H₀D/ε+LD³/ε))` calls to `F` and `DF` | None: same order up to one extra log factor (worse by `log(2+H₀D/ε+LD³/ε)`) | None for the problem class (identical unconstrained, residual class; JY also covers composite `F+H`) | None (both last iterate, both use known parameters) | Weaker oracle: no `D²F` queries. Costs: an extra log factor, the need to know `H₀`, a constant of `2²¹`, unconstrained only |
| Jiang–Yoon AEP Newton, same paper, Thms 4.4/4.6 (p=2, `F, DF` oracle), on the overlap where `DF` is also globally `L₂`-Lipschitz | `O((1+(L₂D²/ε)^{2/5})·log(1+L₂D²/ε))` → `O((1+(LD³/ε)^{1/4})·log²(2+H₀D/ε+LD³/ε))` | Regime-specific gain: better whenever `(LD³/ε)^{1/4}·log²(2+H₀D/ε+LD³/ε) ≪ (L₂D²/ε)^{2/5}`, for example as `ε→0` with `L, L₂, D, H₀` fixed (the gain factor is about `ε^{-3/20}` up to logs). Worse when `L₂` is small relative to `L` and `D` | Global Lipschitz `DF` → only `D²F` Lipschitz. This newly covers unbounded-curvature instances, such as the quartic games `Σ(aᵢᵀx)⁴ + xᵀBy − Σ(cⱼᵀy)⁴`. The classes are incomparable | None | Needs `L` (third-order) and `H₀`. Newton's bound does not need `D²F` to exist |
| Same p=2 theorem after localization (my check): on `B(x₀,5D)`, `‖D²F‖ ≤ 6√(LH₀)+5LD` (from `jac_growth` in [`TikhonovHomotopy`](../../LongTails/Proofs/TikhonovHomotopy.lean)) | `Õ(1+((LD³+√(LH₀)D²)/ε)^{2/5})`, assuming JY's analysis localizes to that ball (unchecked) → selected bound | Better by about `(LD³/ε)^{3/20}/log²` when `LD³/ε ≫ 1`. `H₀` enters polylogarithmically rather than as `(LH₀D⁴/ε²)^{1/5}` | None (same class) | None | Localization of the JY Newton analysis is not verified |

Repository overlap: [`LazyAnchoredExtraProximal`](../../LongTails/Theorems/LazyAnchoredExtraProximal.lean) is the p=2 row with `m = 1`. Other high-order VI results all query `D²F` at p=3. These include [arXiv 2609.13462v2](https://arxiv.org/abs/2609.13462) Thm 3.3 (compact `X`, tangent residual, log¹²) and [arXiv 2608.08463](https://arxiv.org/abs/2608.08463) (`Õ(D(L/ε)^{1/3})`, which is weaker). Agafonov et al.'s VIHI ([arXiv 2405.15990](https://arxiv.org/abs/2405.15990), §7) accepts an inexact `D²F`, but uses a compact domain and the gap criterion. Building that `D²F` from Jacobians by finite differences would cost about `dim E` Jacobians per step, so the bound would depend on dimension. Nesterov's superfast methods ([JOTA 2021](https://doi.org/10.1007/s10957-021-01930-y)) and his inexact high-order proximal point ([SIOPT 2021](https://doi.org/10.1137/20M134705X)) are the convex, symmetric-Hessian analogue.

**Reduction check and mechanism.** I found no standard reduction that gives this bound. The p=2 Newton theorem, even localized, gives exponent 2/5. JY's p=3 step needs `D²F` itself. Finite differences make the bound dimension-dependent. The step that is genuinely new is the inner solver. It is a Tikhonov-homotopy Newton method whose number of stages is set by the Euclidean distance `√(aL)·R`, rather than by a distance weighted by the stiffness of `DF`. It relies on a relative bound for the `D²F` tensor of a monotone operator (via the Koszul identity), which handles the non-symmetric Jacobian. Proof ancestry: JY's AEP outer loop and Lyapunov argument supply the `N ≍ (LD³/ε)^{1/4}` outer count and the inexactness certificate. The homotopy/Newton inner solver and its cost accounting are this result's own. I did not check whether JY's Taylor-model subproblem could be solved with directional Jacobian differences in `O(polylog)` calls. That is the main alternative route.

**Search coverage.** Searched on 2026-11-06 UTC: arXiv math.OC/cs.LG 2024–2026 and NeurIPS/ICML/ICLR listings. Queries covered superfast and lower-order implementations, Jacobian-only third-order VI methods, and homotopy Newton methods. I read the JY, 2609.13462 and 2405.15990 theorems through their arXiv HTML versions; some sections were read only in summary. The companion note's citations check out: JY Thm 6.1 is a deterministic lower bound for queries of `F, DF, D²F` and needs `n ≥ 2N+1`. JY §7 lists derivative-free (quasi-Newton) variants as future work. JY's line search adds one log factor, not zero. COLT 2026 and journal online-first lists were not checked. All key competitors are recent unreviewed preprints, and JY predates this result (introduced in commit `7d8f2a06` on 2026-11-06).

**Conclusion**

**Yes: this is the first Jacobian-only guarantee I could find that reaches the optimal third-order residual rate for monotone equations.**

The strongest baseline is Jiang–Yoon's third-order AEP method. It has the same rate, but it queries the second-derivative tensor `D²F` at every step. The selected result removes that oracle and keeps the dimension-free bound:

| | oracle | calls for `‖F(x)‖ ≤ ε` |
|---|---|---|
| Jiang–Yoon p=3 | `F, DF, D²F` | `Õ((LD³/ε)^{1/4})` |
| Best Jacobian-only (JY Newton, needs Lipschitz `DF`) | `F, DF` | `Õ((L₂D²/ε)^{2/5})` |
| This result | `F, DF` | `O((LD³/ε)^{1/4}·log²(2+H₀D/ε+LD³/ε))` |

Among Jacobian-only methods, this is a polynomial gain in the small-`ε` regime. It also covers operators whose Jacobian is not globally Lipschitz. JY's lower bound applies a fortiori, so the rate is optimal up to log² in high dimension. The costs are one extra log factor compared with JY's p=3 method, the need to know `H₀`, an unconstrained setting only, and uncounted linear algebra.

The comparison establishes the oracle-access gain. The literature search supports priority but cannot prove it: the field is moving fast, and I did not check whether JY's tensor subproblem can be solved with directional Jacobian differences. The claimable contribution is a dimension-free, Jacobian-only method that attains the optimal third-order rate for unconstrained monotone equations.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
