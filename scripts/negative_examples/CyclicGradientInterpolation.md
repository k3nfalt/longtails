# CyclicGradientInterpolation: novelty assessment

The [theorem](../../LongTails/Theorems/CyclicGradientInterpolation.lean), with its [setup](../../LongTails/Setups/InterpolatedFiniteSum.lean) and [algorithm](../../LongTails/Algorithms/CyclicGradient.lean), guarantees last-pass-iterate average objective gap at most ε for fixed-order cyclic component-gradient steps of exactly 1/L.

For m≥1 convex differentiable L-smooth components on any real Hilbert space, sharing a minimizer x* with ‖x₀−x*‖≤R, the exact budget is

**N = m⌈m³LR²/ε⌉ = O(m + m⁴LR²/ε)**,

where L>0, R≥0 and ε>0. Each call returns an exact component gradient; uniqueness removes seed/index dependence. Accuracy holds for every outcome, although stated almost surely. Updates know m,L,x₀; stopping additionally needs R,ε. No bounded domain, strong convexity or regularity is required. R=0 gives zero calls; m=1 is ordinary gradient descent. For ε≥LR²/2, x₀ already suffices, but the proved budget still performs at least one pass when R>0.

All table bounds count component calls and ensure the same average objective gap; O suppresses universal constants only. Projection rows use fᵢ=(L/2)dist²(·,Cᵢ), so one gradient call implements one exact projection.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| [Evron et al., ICML 2023, Proposition 4.13](https://proceedings.mlr.press/v202/evron23a/evron23a.pdf), m≥3 | O(m+m⁴L²R⁴/ε²) → O(m+m⁴LR²/ε) | ε⁻²→ε⁻¹; factor LR²/ε when ε≪LR². Converted from their maximum-distance bound. | Squared-distance losses → arbitrary smooth interpolating losses; nested broader class. | None: deterministic last iterate; known parameters. | Selected accuracy is average, not their maximum; projection specialization is not formalized. For m=2 their order already matches. |
| [Swartworth et al., NeurIPS 2023, Theorem 1 and Lemma 2](https://papers.nips.cc/paper_files/paper/2023/file/d72ae75abaa70a3b19c5d4f436c680d1-Paper-Conference.pdf) | O(m+m³LR²/ε) → O(m+m⁴LR²/ε) | Worse: factor m in the accuracy term. | Subspace squared-distance losses → nonlinear convex sets and smooth interpolating losses; nested broader class. | None: last iterate, dimension-independent bounds. | Rescale their unit initialization by R and loss by L; specialize task matrices to orthogonal complements. General regression losses are not all projection losses. |
| [Cai–Diakonikolas, ICLR 2025, Theorem 1](https://proceedings.iclr.cc/paper_files/paper/2025/file/fea9f93f4cec99f65a8b4d575fc353a8-Paper-Conference.pdf); [arXiv v2, 2024-06-28, Theorem 2.3](https://arxiv.org/pdf/2403.06873v2) | O(m+(mLR²/ε)√log(2+LR²/ε)) → O(m+m⁴LR²/ε) | Removes logarithm but loses m³; asymptotic gain only when log(2+LR²/ε)≫m⁶. | Finite-dimensional → Hilbert space, but interpolation narrows their objective class: incomparable overall. | Horizon-tuned updates → horizon-independent updates; both last iterate; R,ε still needed for stopping. | Their admissible small step cannot equal 1/L. Set variance at optimum to zero, α=4, β=4max{1,log K}, η=1/(mL√β), then invert the bound. |
| Repository [AcceleratedConvex.result](../../LongTails/Theorems/AcceleratedConvex.lean), applied to the average | O(m+m√(LR²/ε)) → O(m+m⁴LR²/ε) | Worse: ε⁻¹/²→ε⁻¹. | None on shared Hilbert-space class; current additionally requires interpolation. | None: known L; deterministic returned iterate. | Batch all m gradients per accelerated update, with no line search or restart. Same component oracle; different method, excluded by selected setup's algorithm restriction. |

Standard rescaling/batching yields faster optimization competitors, not the selected trajectory; small-step substitution violates its update rule. [The proof](../../LongTails/Proofs/CyclicGradientRun.lean) couples online loss with squared pass displacement through a weighted potential. Firm nonexpansiveness and Fejér summability are inherited tools: [Reich–Zalas, Theorem 3.2](https://arxiv.org/pdf/2205.13843) gives only slower general-convex estimates; [Bauschke–Borwein, §5](https://cmps-people.ok.ubc.ca/bauschke/Research/05.pdf) needs regularity for linear convergence. These do not supply the extra loss–displacement cancellation.

Search coverage, **2026-10-05 UTC**: primary arXiv versions, ICML/ICLR/NeurIPS proceedings, older projection and incremental-method literature, and forward improvements/counterexamples, including random-order 2025 results; no verified subsequent cyclic supersession located. Git introduces this result at **2c23917, 2026-10-03**; external introduction is unknown. The companion note matches the formal guarantee, but its projection and maximum-distance claims require additional instantiation/derivation; its formerly inaccessible [Kohlenbach, Corollary 2.15](https://www2.mathematik.tu-darmstadt.de/~kohlenbach/inconsistentfeasibility.pdf) and Bauschke–Borwein were accessible here. Original FISTA full text was inaccessible; the acceleration row instead uses inspected repository declarations. No build or axiom audit was run.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED — confidence: medium.**

**New advantages**

- Against Evron's general cyclic projections: ε⁻²→ε⁻¹ call guarantee for average squared-distance loss when m≥3 and ε≪LR².
- Against subspace-only O(1/K) analyses: nonlinear convex sets and arbitrary smooth interpolating components, retaining full-step cyclic behavior, at worse m dependence.
- Against Cai–Diakonikolas's tuned guarantee: full step 1/L and updates independent of horizon, with the stated m³/logarithm tradeoff and no adaptive stopping claim.

This supports a meaningful new analysis of a classical fixed method, not a faster solver for the problem class or a new algorithm. Priority of the particular potential remains unverified; neither optimal m dependence nor a general random-order improvement is established.
