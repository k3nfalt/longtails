# Novelty assessment: log-free last iterate of linear-decay random reshuffling

[`ReshuffledLinearDecayLastIterate.lean`](../../LongTails/Theorems/ReshuffledLinearDecayLastIterate.lean) proves the following for f = (1/n)Σᵢfᵢ with convex, differentiable fᵢ on a real Hilbert space. Run random reshuffling ([algorithm](../../LongTails/Algorithms/ReshuffledGradient.lean), [setup](../../LongTails/Setups/ReshuffledSmoothConvex.lean)) with a fresh uniform permutation in each of K epochs and the known-horizon epoch step nηₖ = γ(K−k)/K, where γ = 1/(64√(L̄L*) + 5σ√(L̄/(nε))). Then the **last iterate** satisfies E f(x_{nK}) − f* ≤ ε after exactly n·⌈384√(L̄L*)R²/ε + 30σR²√(L̄/(nε³))⌉ component-gradient calls.

Here ∇fᵢ is ℓᵢ-Lipschitz with ℓᵢ ≤ L* and (1/n)Σℓᵢ ≤ L̄ ≤ L*. R ≥ ‖x₀ − x*‖, and σ² ≥ (1/n)Σ‖∇fᵢ(x*)‖². The setup restricts the admissible algorithms to RR. If R > 0, the guarantee is

**Calls = O(n + n√(L̄L*)R²/ε + σR²√(nL̄)/ε^{3/2})**, with no logarithmic factor. If R = 0, the budget is 0.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Liu–Zhou, ICML 2024, [arXiv:2403.07723v3](https://arxiv.org/abs/2403.07723), Thm 4.4 / full Thm C.1. This is a direct competitor: (prox) RR, constant step ≤ 1/(4n√(2L̄L*(1+log K)))). | O(n + √ℓ·[n√(L̄L*)R²/ε + σR²√(nL̄)/ε^{3/2}]) with ℓ = 1+log K → O(n + n√(L̄L*)R²/ε + σR²√(nL̄)/ε^{3/2}) | The √(1+log K) factor is removed in both terms. Liu–Zhou's O-constants are unstated, so the gain is asymptotic in K; no explicit-constant crossover was checked. | None. Their class is broader. | None. Both give the last iterate, and both need K, σ, R, ε for tuning. | Narrower scope: no proximal ψ. The bound needs uniformly random orders; their "any permutation" row is only a proof-module lemma (`any_order_gap`) here. Schedule: linear decay vs. constant step. |
| Liu, COLT 2026, [arXiv:2606.32005](https://arxiv.org/abs/2606.32005) ([PMLR v336](https://proceedings.mlr.press/v336/liu26d.html)), Thm 1 / Cor. 1. Same RR method, but it returns a **weighted average** with step ≤ 1/(6L*). | O(n + L*R²/ε + min{σ²R²/ε², σR²√(nL̄)/ε^{3/2}}) → this result | Worse in the deterministic term, by a factor n√(L̄/L*) (≥ nL̄/L*). The noise term is the same order or worse. | None | Averaged → last iterate. The averaged bound does not imply a last-iterate bound. | The last-iterate output is the only gain, and it costs up to a factor n in the deterministic term. |
| Full-gradient GD / Nesterov AGD (Nesterov, *Lectures on Convex Optimization* 2018, Cor. 2.1.2 / Thm 2.2.2). Each full gradient costs n calls, and f is L̄-smooth. | GD n⌈2L̄R²/ε⌉; AGD O(n + n√(L̄R²/ε)) → this result | Never better, up to constants: n√(L̄L*)R²/ε ≥ nL̄R²/ε, and the σ-term is additional. It is the same order only when σ = 0 and L̄ ≍ L*. Otherwise it is strictly worse. | None | None. Both are deterministic last-iterate bounds. | This result adds σ-dependence and L*-dependence. The setup's algorithm restriction excludes GD/AGD, but they solve the same instances under the same oracle. |

**Reductions and mechanism.** I found no derivation by substitution. Averaging changes the output. Constant-step analysis loses K^{Θ(γ²L̄L*)}. The note credibly says that inserting linear decay into Liu–Zhou's Lemma D.2 fails, because their error term sits at the reference point. The new step is a pathwise epoch inequality whose error sits at the start-of-epoch gap and whose noise is isolated in W(π). A prefix-sum Gronwall bound and a transposition moment bound E W(π) ≤ n²L̄σ*² complete it. Proof ancestry: Zamani–Glineur ([arXiv:2307.11134](https://arxiv.org/abs/2307.11134)) supplies the anchor sequence. The repository's i.i.d. SGD lemma `potential_bound` supplies the weight bookkeeping. Neither yields the shuffling bound by itself.

**Repository overlap.** RandomReshufflingQuadratic is a negative example; it is quadratic-only. The later repository result [ReshuffledConstantStepLastIterate](../../LongTails/Theorems/ReshuffledConstantStepLastIterate.lean) (2026-10-05) is subsequent. It needs O(n + log n·log(n+a)·(L*R²/ε + σ²R²/ε²)) calls, with a = (L*ε+σ²)R²/ε². That bound is better than this result in the deterministic term, but worse than it when σ² ≳ nL̄ε·polylog.

**Search coverage (2026-10-07).** I covered arXiv/ICML/ICLR/COLT for last-iterate shuffling from 2023 to 2026. This included Cai–Diakonikolas ICLR 2025 ([arXiv:2403.06873](https://arxiv.org/abs/2403.06873)), checked by abstract only: its smooth last-iterate bounds are "up to a square-root-log or a log factor". It also included Liu–Zhou ICML 2025 ([arXiv:2505.23056](https://arxiv.org/abs/2505.23056)), which is about nonsmooth components and so not comparable. I found no earlier log-free smooth RR last-iterate bound. The result was introduced in commit ffab4e6 on 2026-10-03. The note's citations match what I verified. Liu–Zhou §6 states the open problem verbatim. Cha–Lee–Yun's lower bound was not rechecked. The note does not claim that RR beats GD/AGD, but it also does not mention them.

**Conclusion**

**No optimization advantage is established; what is new is a sharper analysis of RR's last iterate.** Within RR, the proof removes the √(1+log K) factor from Liu–Zhou's ICML 2024 last-iterate bound. This answers the question their Section 6 leaves open, for ψ = 0 and uniformly random orders.

| Method (same oracle, last iterate) | Calls to reach E-gap ≤ ε |
|---|---|
| Liu–Zhou RR | O(n + √(log K)·[n√(L̄L*)R²/ε + σR²√(nL̄)/ε^{3/2}]) |
| This result | O(n + n√(L̄L*)R²/ε + σR²√(nL̄)/ε^{3/2}) |
| Full-gradient AGD | O(n + n√(L̄R²/ε)) |

The guarantee does not improve the problem class. Accelerated full-gradient descent, and even plain GD (n⌈2L̄R²/ε⌉), use the same component oracle and are at least as good in every regime, with no σ term. Liu's averaged RR bound (COLT 2026) is also better by up to a factor n in the deterministic term; only the output type differs.

The comparison proves a logarithmic gain over the direct RR competitor. The literature search did not find prior log-free work, but that does not prove priority. What can be claimed is a new, log-free last-iterate analysis of random reshuffling with linear decay, with no complexity advantage for smooth convex finite sums. This is the same pattern as the QuadraticFiniteSum negative example.

**Verdict: NO IMPROVEMENT**
**Confidence: medium**
