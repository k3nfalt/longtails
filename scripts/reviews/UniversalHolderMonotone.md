# Novelty assessment: UniversalHolderMonotone

[`result`](../../LongTails/Theorems/UniversalHolderMonotone.lean) ([setup](../../LongTails/Setups/HolderMonotone.lean), [algorithm](../../LongTails/Algorithms/UniversalRegularizedExtragradient.lean)) applies to every monotone `F : E → E` on a finite-dimensional real inner-product space with `‖Fx−Fy‖ ≤ L‖x−y‖ + H‖x−y‖^α`, `0 < α ≤ 1`, and a zero within `R` of `x0`. The algorithm is told only `x0`, `ε` and a guess `0 < r0 ≤ R`; it is not told `L`, `H`, `α` or `R`. It is a Tikhonov-regularized extragradient method that backtracks on its step size and doubles its radius guess. It deterministically returns the first queried point `x̂` with `‖F(x̂)‖ ≤ ε` (a stopped iterate), counting every call to `F`.

**Complexity** (substituted from `budget`). `L` and `H` are the Lipschitz and Hölder constants, `α` is the Hölder exponent, `R ≥ ‖x0−x*‖`, and `ε` is the target residual:

```
N = O( [ LR/ε + (8HR^α/ε)^{1/α} + log(R/r0) + 1 ] · log( (LR/ε + (8HR^α/ε)^{1/α} + 1)·R/r0 ) )
```

The factor `8^{1/α}` is not a universal constant as `α → 0`, so it is kept. If `r0` overestimates the distance, the theorem applies with `R = r0`. Below, `X := (HR^α/ε)^{1/α} = H^{1/α}R/ε^{1/α}`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Yoon–Choudhury–Greenberg–Loizou, *Polyak-Type Extragradient Methods for Monotone Root-Finding*, [arXiv:2609.26581v1](https://arxiv.org/abs/2609.26581) (22 Sep 2026, preprint), Thm 3.4 eq. (12) + Prop 3.5(b), PolyakEG-LS. **Prior (11 days earlier). Applies only to pure Hölder (`L = 0`) or pure Lipschitz operators.** | Pure Hölder: `O(c^{1/α}X² + log₊(H^{1/α}ε^{−(1−α)/α}/λ₋₁))` calls, where `λ₋₁` is the initial step-size guess → `O((8^{1/α}X + log(R/r0))·log(X R/r0))`. | Polynomial: `X²` → `X·log`. The gain holds when `X ≳ log(XR/r0)`. Example with `α = 1/2`, `H = R = r0 = 1`: `ε^{−4}` → `ε^{−2}log(1/ε)`. | Pure `(H,α)`-Hölder or pure Lipschitz → the sum `L‖·‖ + H‖·‖^α`. Their Prop 3.3 argument extends to sums verbatim. | None. Both are parameter-free and both return the first iterate with `‖F‖ ≤ ε`. Yoon et al. use a guess `λ₋₁`; this method uses a guess `r0`. | This result is unconstrained and finite-dimensional, and its stopping rule needs `ε`. With `H = 0` it costs `O(LR/ε·log)`, against Yoon's `O(L²R²/ε²)`. |
| Zhang, *Tseng's splitting … sum of Hölder operators*, [arXiv:2606.22392v1](https://arxiv.org/abs/2606.22392) (21 Jun 2026), Thm 2 (anchored/FEG, last iterate); Thm 1 (Tseng, best iterate) | Thm 2: `dist(0,T(x_K))² ≤ O(K^{−(3α−1)}·log K)` needs `Õ(ε^{−2/(3α−1)})` calls, only for `α > 1/3`. Thm 1 needs `Õ(ε^{−2/α})`. The theorem does not make the `H`/`R` dependence explicit. → `Õ(ε^{−1/α})` | Exponent `2/(3α−1)` → `1/α` for every `α < 1`, plus coverage of `α ≤ 1/3`. At `α = 1` the exponents are equal and this result has an extra log factor. | None. Zhang treats a broader class: inclusions with a maximal monotone `G` and sums of `N` Hölder operators. | Known `H`, `α` for the step sizes → no knowledge needed. Last iterate → stopped iterate (a weaker output). | Equations only, with no set-valued part. |
| Anchored EG with known `L` (Yoon–Ryu 2021, ICML). **Special case `H = 0` only.** | `O(LR/ε)` → `O(LR/ε·log(LR/r0ε))` | Worse by a log factor. | None | Known `L` → unknown `L`. Last iterate → stopped iterate. | None beyond the log factor. |

**Reduction check.** The bound follows from standard pieces:
- Tikhonov regularization `G = F + (ε/4R)(·−x0)` turns the problem into a strongly monotone one.
- Yoon et al.'s strongly monotone contraction (Thm 3.4, eq. (13)) applies under their "critical condition" `‖G(x̂)−G(x)‖ ≤ A‖G(x)‖`.
- Their Prop 3.3/3.5(b) argument shows backtracking keeps the step `γ ≳ min{1/L, H^{−1/α}ε^{(1−α)/α}}` while `‖G(x)‖ ≥ ε/2`.

Together these give `O(X log)` steps for known `R`. I checked this composition by hand. Guess-and-double for `R` uses the certificate `‖G‖ ≤ ε/2 < ‖F‖`. I found no paper that states this composed bound. The only non-routine piece I see is the observation that the separation tested by backtracking equals a computable residual. That same observation already drives Yoon et al.'s Prop 3.5(b).

A second reduction, through Stonyakin et al.'s restarted universal mirror-prox ([arXiv:1806.05140](https://arxiv.org/abs/1806.05140)), gives only `X^{2/(1+α)}` (a rough check, consistent with the note).

**Proof ancestry** (not competitors):
- Tikhonov/anchoring as a residual device (e.g. Chen, [arXiv:2605.30905](https://arxiv.org/abs/2605.30905), Lipschitz only).
- Classical linear convergence of extragradient with line search under strong monotonicity (Solodov–Tseng, as cited by Yoon et al.).

**Search coverage (2026-10-07).** I searched arXiv and the web for Hölder or non-Lipschitz monotone equations and inclusions, residual criteria, universal mirror-prox (Stonyakin et al.; Klimza et al. [arXiv:2407.17519](https://arxiv.org/abs/2407.17519), gap-only), parameter-free extragradient (Shen–Kılınç-Karzan [arXiv:2604.07662](https://arxiv.org/abs/2604.07662), locally Lipschitz only), and anchoring. I read the relevant theorem statements in Yoon et al. and Zhang. I did not read Dang–Lan Thm 4.4 directly; its `ε^{−2/α}` rate is as reported by Yoon et al. I did not verify the note's Sun–Zhang–Zhao and Nguyen–Gasnikov citations. The result was introduced on 2026-10-03 (commit 28ee0d5). **Note discrepancy:** the companion note omits Yoon et al. It therefore presents parameter-free operation as new, and it misses that their strongly monotone theorem nearly yields this bound. I found no later work covering the same setup.

## Conclusion

**Yes, the proved residual complexity is polynomially better than any published bound I found, but it follows from a short composition of known tools.**

The strongest prior parameter-free baseline is Yoon et al.'s PolyakEG-LS (Sep 2026). On pure Hölder operators, the comparison is:

| | calls for `‖F(x̂)‖ ≤ ε` |
|---|---|
| Yoon et al. 2026 | `O((HR^α/ε)^{2/α})` |
| this result | `O((LR/ε + (8HR^α/ε)^{1/α} + log(R/r0))·log(·))` |

The gain also holds against Zhang's known-parameter `ε^{−2/(3α−1)}`, whenever `(HR^α/ε)^{1/α}` exceeds the logarithm. With `H = 0` the result loses a log factor to anchored extragradient.

The comparison proves a gain. Priority is a separate question, and the search found no earlier statement of this bound. Still, Tikhonov regularization plus Yoon et al.'s own strongly monotone theorem and Hölder step-size argument reproduce the result. I checked that composition, so the improvement is real but routine.

What can be claimed is an explicit, parameter-free `Õ(ε^{−1/α})` residual bound for Lipschitz-plus-Hölder monotone equations, obtained by a straightforward regularization of a known analysis. No optimality is shown for `α < 1`.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
