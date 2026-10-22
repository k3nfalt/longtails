# SCENT for compositional entropic risk: moment-ratio complexity

[`result`](../../LongTails/Theorems/ScentCompositionalEntropicRisk.lean) shows that SCENT ([algorithm](../../LongTails/Algorithms/Scent.lean)) on `F(w) = (1/n) Σᵢ log E_{ζ∼Pᵢ} exp sᵢ(w;ζ)` ([setup](../../LongTails/Setups/CompositionalEntropicRisk.lean)) attains `E[F(w̄_T) − F(w⋆)] ≤ ε` for the **averaged iterate**. Here each `sᵢ(·;ζ)` is convex on a closed convex `W` (subgradient inequality only), takes values in `[c₀,c₁]`, and has `E‖∇sᵢ‖² ≤ G²`. The setup also assumes `E e^{2sᵢ} ≤ κ (E e^{sᵢ})²` and `E e^{2sᵢ}‖∇sᵢ‖² ≤ σ′² (E e^{sᵢ})²` on `W`, and `‖w₀ − w⋆‖ ≤ R`. Each oracle call draws an anchor uniformly and returns two independent samples from it; projection calls are counted too.

**Complexity (oracle calls, batch `B ≥ 1`), with Δ = c₁ − c₀:**

`N = O( B + [ B κG²R²(1 + e^Δ ε) + ( min(e^Δσ′², e^{2Δ}G²) R² + n e^Δ (1 + (1+Δ)(κ−1)) )(1 + ε) ] / ε² )`.

This bound is minimized at `B = 1`. Both remaining parameters are automatically bounded: `κ ≤ e^Δ` and `σ′ ≤ e^Δ G`. The proof actually gives an anchor term of `n e^Δ/ε + n e^Δ(1+Δ)(κ−1)/ε²`, but the one-line public budget loosens it to the expression above.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| SCENT, Wei–Zhou–Wang–Lin–Yang, [arXiv 2602.02877](https://arxiv.org/abs/2602.02877) v1 2 Feb 2026, v2 24 Jun 2026, ICML 2026 (PMLR 306), Thm 3.6 (prior; same algorithm and oracle). Its bound depends on trajectory quantities σ_t², δ_t²; I instantiated them with σ_t² ≤ e^{2Δ}G², δ_t² ≤ e^{2c₁−c₀}/4, D_φ ≤ n e^{−c₀}, and a constant αₜ ≤ e^{−c₁} | `e^{2Δ}(BG²R² + n(1+Δ))/ε²` → `[κG²R² + min(e^Δσ′², e^{2Δ}G²)R² + n e^Δ(1+(1+Δ)(κ−1))]/ε²` at B = 1, ignoring burn-in when ε ≤ 1 | Never worse up to constants for ε ≤ 1. Primal term gains a factor ≈ e^{2Δ}/(κ + e^Δσ′²/G²). Anchor term gains ≈ e^Δ/(κ−1) if κ−1 ≥ 1/(1+Δ), and ≈ (1+Δ)e^Δ if κ−1 ≤ 1/(1+Δ). Example: κ = O(1) and σ′ = O(G) give an overall gain of order e^Δ | Assumption 3.2(i): differentiable sᵢ → subgradient inequality only (nonsmooth convex scores covered) | None; same averaged output. Tuning needs κ, σ′ (or their worst-case values e^Δ, e^ΔG) | Uses (κ, σ′) uniformly on W, though this is implied by Assumption 3.2. Batch variant samples anchors sequentially with replacement, not as the paper's uniform subset; identical at B = 1. Burn-in term `e^Δ κG²R²/ε` can exceed the old bound only when 1 < ε ≤ Δ. Some e^Δ factors remain |
| Joint projected SGD on the min–min form over `W × [c₀,c₁]ⁿ` (standard reduction; derived here) | `e^{2Δ}(GR + √n Δ)²/ε²` → as above | Anchor term changes from `n e^{2Δ}Δ²` to `n e^Δ(1+(1+Δ)(κ−1))`; primal term as in row 1 | None | None | None |
| BSGD, Hu–Zhang–Chen–He, NeurIPS 2020, as summarized in SCENT's Table 1 (nonsmooth case; theorem not rechecked) | `O(ε⁻⁴)` samples (constants not extracted) → `O(ε⁻²)` | Better ε-exponent; parameter constants not comparable | None | None | Not comparable in κ, Δ, n constants |

**Standard-reduction check.** Plugging the paper's Lemma 4.2 into Thm 3.6 does not close the argument. The variance bound in Lemma 4.2 is quadratic in the gap of the *actual* sequence and is stated only for n = 1, and the paper closes the recursion only for fixed `w` (Thms 4.3, 4.5, E.10). The Lean proof (`ScentConvergence.lean`) closes it for n ≥ 2 with two steps. First, linear self-bounding `e^u ≤ 2(1+ψ(u))` on the *virtual* dual sequence. Second, a bias-to-dual-gap bound `‖∇_wF(w,ν) − ∇F(w)‖² ≤ 2e^Δ κG²·gap`, which also lets batching reduce the primal term to the floor `κG²R²/ε²`. The paper's SPMD dual-regret lemma (Lemma 3.5) and its virtual-sequence device are proof ancestry, reproved here per sub-step.

**Search coverage (2026-10-22).** I searched arXiv, the ICML 2026 listing, and the web for CERM, Log-E-Exp, LogSumExp, KL-DRO/OCE, MLMC, and FCCO work, and read SCENT v2's Thm 3.6, Lemmas 3.4–3.5, Assumption 4.1, Lemma 4.2, Section 4.3, and Thm E.4. I found no κ-explicit analysis for n ≥ 2. Several other works are outside this setup: MLMC ([2408.11084](https://arxiv.org/abs/2408.11084)) needs smooth sᵢ, the softplus surrogate methods ([2509.24894](https://arxiv.org/abs/2509.24894), [2609.40120](https://arxiv.org/abs/2609.40120)) are smooth or slower, and OCE ([2608.07113](https://arxiv.org/abs/2608.07113)) treats a single risk. I did not read the BSGD theorem itself. The companion note's citation "Hu, Chen and He" for 2408.11084 is inaccurate: the arXiv authors are Hu, Wang, Chen, He, and the title differs. The theorem was added in commit a3ae0de (2026-10-22), after both SCENT versions.

**Conclusion**

**Yes: for the same algorithm and assumptions, the proved total complexity is better, by up to an exponential factor e^Δ.** The strongest baseline I found that applies to this setup is SCENT's own Theorem 3.6. Once its trajectory variances are bounded a priori, it gives the first bound below; the new theorem gives the second (B = 1, ε ≤ 1):

| | oracle calls |
|---|---|
| SCENT Thm 3.6 (instantiated) | `e^{2Δ}(G²R² + n(1+Δ))/ε²` |
| This result | `[κG²R² + min(e^Δσ′², e^{2Δ}G²)R² + n e^Δ(1+(1+Δ)(κ−1))]/ε²` |

Since `κ ≤ e^Δ` and `σ′ ≤ e^ΔG` always hold, the new bound is never worse up to constants. It gains roughly a factor e^Δ when the scores are concentrated (κ = O(1), σ′ = O(G)), which is the regime the SCENT authors themselves raised as an open question for n ≥ 2. The `ε⁻²` rate and the additive `n/ε²` anchor term are unchanged, residual `e^Δ` factors remain, and no lower bound shows the new bound is tight.

The comparison establishes the gain against the checked baselines. My search found no earlier κ-explicit bound for n ≥ 2, but failing to find one does not prove priority. The claimable contribution is a new a-priori complexity bound for compositional entropic risk with nonsmooth convex scores that replaces the worst-case exponential factors with the moment ratios κ and σ′, plus a batch iteration floor.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
