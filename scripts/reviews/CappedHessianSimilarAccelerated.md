# Novelty assessment: CappedHessianSimilarAccelerated

[`result`](../../LongTails/Theorems/CappedHessianSimilarAccelerated.lean) proves an expected objective-gap guarantee. For `F = (1/m)Σ fᵢ` with convex differentiable clients, μ-strongly convex `F`, and average Hessian similarity δ, the [setup](../../LongTails/Setups/CappedHessianSimilarConvex.lean) allows rounds that contact at most `s` clients, each returning one gradient or one exact proximal point. The [CappedProximal algorithm](../../LongTails/Algorithms/CappedProximal.lean) returns a final iterate `x̂` with `E[F(x̂)] − F* ≤ ε` within a deterministic budget of

**O( [ 1 + m/s + (1 + m^{3/4}/s)·√(δ/μ) ] · log(2 + m + δ/μ) · log(2 + Δ/ε) )** rounds.

Here `m` is the number of clients, `s` the per-round cap, and Δ ≥ F(x₀) − F*. The similarity condition is `(1/m)Σᵢ‖∇(fᵢ−F)(x) − ∇(fᵢ−F)(y)‖² ≤ δ²‖x−y‖²`. The bound needs no smoothness constant. This is the public budget (`2^40`-scaled), which is proved to dominate the exact plan cost `NKJ(⌈m/s⌉+3T)`.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| AccSVRS, Lin–Han–Ye–Zhang, NeurIPS 2023 ([arXiv:2304.07504v2](https://arxiv.org/abs/2304.07504), Thm 3.6). Its sequential steps contact a fixed master and one client, so the method runs under any cap. | O((m + m^{3/4}√(δ/μ))·log(Δ/ε)) expected rounds → this result's bound | Coefficient of √(δ/μ) drops from m^{3/4} to 1 + m^{3/4}/s, and m → m/s: a factor ≈ min(s, m^{3/4}). The gain survives the logarithms when that factor ≫ log(m+δ/μ). At s = 1, the result is worse by log(2+m+δ/μ). | None. AccSVRS allows nonconvex fᵢ, so the classes are nested and the present one is narrower. | Expected → deterministic round count. Both outputs are final iterates. | Requires convex clients and exact proximal steps (AccSVRS accepts inexact master steps). Carries an extra log factor. |
| Restarted Acc-S-DANE, batched under the cap: Jiang–Rodomanov–Stich, NeurIPS 2024 ([arXiv:2407.07084v2](https://arxiv.org/abs/2407.07084), Thm 6, case μ_client = 0, 4δD²/R²). Restart via D² ≤ 2Δ/μ (my reduction); 2⌈m/s⌉ rounds per iteration (Wang, Prop. 13). | O((m/s)(1+√(δ/μ))·log(Δ/ε)) → this result's bound | Coefficient of √(δ/μ) drops from m/s to 1 + m^{3/4}/s: a factor ≈ min(m/s, m^{1/4}) for s ≤ m/2. At s = m, the result is worse by log(2+m+δ/μ). | None. Same class: convex fᵢ, strongly convex F, the same average similarity (δ-SOD). | None. Acc-S-DANE is deterministic with a last-iterate guarantee; this result is randomized, in expectation. | Exact proximal steps (S-DANE accepts inexact ones). Extra log factor. Randomized output. |
| Catalyst VM-SVRS, Wang ([arXiv:2610.33835v1](https://arxiv.org/abs/2610.33835), 24 Oct 2026 preprint, Thm 14 / Cor 15). Prior, but only for quadratic, individually strongly convex clients. | O([m/s + (√(m/s) + m^{3/4}/s)√(δ/μ)]·ℓ(ℓ+log(1/ε))) with ℓ = log(mL_max/μ) → this result's bound | On the quadratic overlap, the √(m/s) term disappears: a factor min(√(m/s), s/m^{1/4}) when √m < s < m. It peaks at m^{1/8} for s = m^{3/4}. Logarithms are no worse, and there is no L_max. | Quadratic, individually strongly convex clients → general differentiable convex clients with strongly convex mean. | Expected rounds → deterministic budget. | None beyond exact proximal steps, which are trivial for quadratics. |

**Reduction check.** Neither prior method nor the min of the two gives `(1 + m^{3/4}/s)√(δ/μ)`. Combining batched Acc-S-DANE with AccSVRS gives only the coefficient `min(m^{3/4}, m/s)`. Wang's virtual-master Catalyst composition keeps `√(m/s)`. The new mechanism is a sampled-primal certificate inside an accelerated inner epoch: it bounds `E[F(z) − F(U)]` at the sample-correlated averaged proximal point using only average similarity. It sits inside a Catalyst-style outer loop with ρ = μ + δ/√m. Proof ancestry, not competing rates: S-DANE's common-point centering, Catalyst/accelerated proximal point, and SVRG-type snapshot estimators. I did not verify the Lean proof beyond reading the statement, setup, algorithm, and budget lemma, and I ran no build or audit.

**Search coverage.** On 30 Oct 2026 I searched arXiv and NeurIPS/ICLR sources for SVRP/Catalyzed SVRP, AccSVRS, S-DANE/Acc-S-DANE, SPAM, the cost-aware SABER comparison (nonconvex, not a competitor), and Wang. The Lin et al. theorem text was read. For Wang and S-DANE I relied on HTML extracts; the S-DANE partial-participation appendix D.3 and Wang's Corollary 12 were not read. The result was introduced in commit 92d4e85 on 30 Oct 2026, six days after Wang v1. The companion note's claims agree with what I checked. It omits the restarted Acc-S-DANE baseline, but that baseline is weaker than this result except near s = m.

**Conclusion**

**Yes, for intermediate caps the proved round complexity is polynomially better than any applicable bound I found.** On the same class (convex clients, strongly convex mean, average similarity, exact local proximal steps), the best prior is the better of AccSVRS and batched restarted Acc-S-DANE. Write κ = δ/μ:

| | rounds (up to logs) |
|---|---|
| prior best | min( m + m^{3/4}√κ , (m/s)(1+√κ) ) |
| this result | m/s + (1 + m^{3/4}/s)√κ, times an extra log(m+κ) |

Example: s = m^{3/4} and κ = m. The prior best is about m^{3/4}, this result is about m^{1/2}·log m, so it saves roughly m^{1/4}/log m. In general the √κ term improves by min(s, m^{1/4}, m/s). The result loses a logarithm at s = 1 and at s = m. It also requires convex clients and exact proximal steps, while AccSVRS covers nonconvex clients.

Against Wang's preprint, which came out six days earlier and covers only quadratic, strongly convex clients, the result gains up to m^{1/8} and extends to non-quadratic clients. By my reading of Wang's Cor. 11, it matches that zero-respecting lower bound's polynomial dependence for s ≤ m^{3/4}. Priority rests on a targeted search, and the proof is not independently re-verified. The claimable contribution is the first polynomial round complexity m/s + (1 + m^{3/4}/s)√(δ/μ) for capped participation under average similarity, closing the intermediate-cap gap.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
