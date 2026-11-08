# BirchCollections: novelty review

The [theorem](../../LongTails/Theorems/BirchCollections.lean), [setup](../../LongTails/Setups/BirchCollections.lean), and [compiled algorithm](../../LongTails/Setups/BirchCollectionExecutionModel.lean) guarantee expected squared dual-gradient norm at most ε at a uniformly selected marked publication, for certified finite traces on finite-dimensional, lower-bounded, nonconvex objectives.

Here L is native smoothness, Δ bounds the initial objective gap, σ² bounds unbiased IID dual-norm variance, and κ witnesses dual regularity; L,ε>0 and σ,Δ≥0. With the setup's original controls I=initialization, D=waste, a=amplification, r=massRatio and m₋,m₊=lowerMass,upperMass, its full raw-call budget is

\[
O\!\left(I+D+1+a m_+\left(1+\frac{L\Delta}{m_-\varepsilon}\right)
\left(1+\frac{r\kappa\sigma^2}{\varepsilon}\right)\right).
\]

This follows directly from the three ceilings, without deleting initialization or discarded/pending work. The setup requires 0<m₋≤m₊≤1, m₊≤rm₋ and a>0. Updates use step scale 1/(20L), retained refresh weights, exact sharp directions and history subtraction. Joint measurability, integrability and an abstract IID law are explicit; there is no finite sample-space restriction. Parameters and the event list are public: this is neither parameter-free stopping nor a theorem for arbitrary gradient-dependent schedulers. Arithmetic, communication and exact sharp evaluation are unpriced. At σ=0 the noise terms vanish; at Δ=0 the supplied budget still pays for a batch although x₀ is already stationary.

The comparisons below use ε≤LΔ; oracle counts refer to individual samples. Serial comparisons specialize the controls to vanilla. Resource comparisons specialize to Euclidean geometry and independent one-stage devices with sorted service times τᵢ.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
| --- | --- | --- | --- | --- | --- |
| [Birch SGD, Theorem 2.4 and E.1](https://arxiv.org/pdf/2505.09218v3), ICLR 2026, v3 28 March 2026; serial Euclidean overlap | O(LΔ/ε+LΔσ²/ε²) → O(LΔ/ε+LΔσ²/ε²) calls | None: same order | Euclidean tree updates → certified native sharp/retained histories; algorithmic scope, not a larger Euclidean objective class | None: expected selected-iterate stationarity | Native variants need not reproduce the original updates or sharp delay dependence |
| [Sokolov–Tyurin–Richtárik, Appendix D.4 and Lemma 15](https://arxiv.org/html/2610.38773v1#A4.SS4), arXiv preprint, 28 October 2026; same native objective/oracle class | O(LΔ/ε+κLΔσ²/ε²) → O(LΔ/ε+κLΔσ²/ε²) calls | None: same order | None for optimization instances; additional certified histories | None: both uniform random output in expectation | D.4 already assumes only finite variance. Comparing solely with their light-tail Theorem 1 would manufacture an improvement |
| [Tyurin–Richtárik, Theorems 7.4–7.5 and 6.4](https://arxiv.org/html/2305.12387), NeurIPS 2023, v2; independent-device overlap only | O((LΔ/ε) minₘ (m+σ²/ε)/(Σᵢ≤ₘ1/τᵢ)) → O((LΔ/ε) minₘ (m+σ²/ε)/(Σᵢ≤ₘ1/τᵢ)) time | None: same order on this overlap | Independent devices → shared exclusive routes or power-feasible atomic modes; genuine hardware extension | None; selected output unchanged; new optimized dispatch needs hardware information | Prior theorem does not solve shared-resource allocation. Its wall-clock bound is not an all-issued-work bound |

**Framework and recovery.** The [common lemma](../../LongTails/Proofs/BirchTraceDescent.lean) is weighted telescoping with a column-sum absorption condition; the mathematical work lies in deriving its certificates. The [retained energy proof](../../LongTails/Proofs/BirchRetainedEnergy.lean), causal sampling and history identities support actual reuse and overlapping merges. This is a meaningful extension of analysis coverage beyond raw-gradient trees, but not a new problem-class rate. The existing repository framework/composition results already supply norm-native certificate machinery; the collection compiler makes particular protocols concrete.

The [Euclidean reduction](../../LongTails/Proofs/BirchCollectionEuclidean.lean) preserves bases, queries, cached identities, the original independence condition and branch output. It recovers exactly
\[
K\ge 4(R+1)L\Delta/\varepsilon+8\sigma^2L\Delta/\varepsilon^2,
\]
with prefix execution cost equal to the branch index, not automatically K. This uses a separate Euclidean certificate through `BirchSgdConvergence.assembly`; it is not a claim that substituting N=ℓ₂ in the native budget gives that sharp threshold. The [dependency script](../VerifyBirchCollectionsDependencies.lean) searches proof-body dependency paths to the common lemma for all named exports; I inspected it but did not execute it or run build/axiom checks.

**Eleven families and retained examples.** I inspected the constructions and validity/success proofs for Vanilla, Rennala, Ringmaster/Delayed, Local, Cycle, Async-Local, Async-Batch, Local-Async, Nested Local-Async, Meta Local and Dual-Process. They respectively implement current batches, stop-and-drain, age gates, completed private prefixes, rotating groups, age-times-size gates, saved-point packets, inner arrivals/outer quotas, tiered prefix publication, capped soft synchronization, and immutable acknowledged send prefixes. These are substantive coverage witnesses, not eleven independent optimization improvements. Many use full refresh and conservative movement scaling; for example native Delayed's accepted-work bound contains (1+LΔ(1+4h)/ε)(1+κσ²/ε), so delay h multiplies noise, unlike the recovered Euclidean rate.

The [variable-quota construction](../../LongTails/Algorithms/BirchCollectionRetainedQuota.lean) genuinely retains estimators across hierarchical phases, allowing phase work between half and all of its tuned quota, with explicit restart waste. [Rolling-window sharp](../../LongTails/Theorems/BirchWindow.lean) genuinely reuses cached replies and pays B+K−1 calls, but its step is 1/(4LB) and its substituted total is O((1+LΔ/ε)(1+κσ²/ε)): reuse establishes no oracle improvement over fresh minibatching.

**Geometry.** Nonlinear sharp updates do not generally arise from a linear Euclidean change of variables. Nevertheless their basic variance/descent rate is already supplied by Appendix D.4 above. A concrete non-Hilbert example is N(x)=‖x‖₂+|x₁| in dimension at least two: the [geometry proofs](../../LongTails/Proofs/BirchResourceGeometry.lean) give ‖v‖₂/2≤N*(v)≤‖v‖₂ and κ=4. The quadratic f(x)=L‖x‖₂²/2 with oracle Lx+Ze₁, centered IID Z and E Z²≤σ², satisfies every objective/oracle assumption with Δ≥L‖x₀‖₂²/2. This demonstrates non-Hilbert coverage, not a complexity separation: Euclidean conversion loses only constants here.

**Both resource results and the strongest reduction.** Let R(t) maximize feasible aggregate fractional route rate among routes of latency at most t, and Rᵤ(t) maximize Σ samples/duration over simultaneous configurations with distinct devices, total draw within the power cap, durations≤t and packet sizes≤u. J is maximum route depth; device durations are positive and routes do not revisit devices. Infima below range only over positive rates. The [routed](../../LongTails/Theorems/BirchRoutedTime.lean) and [power](../../LongTails/Theorems/BirchPowerTime.lean) guarantees imply
\[
\begin{aligned}
T_{route}&=O\!\left(J^2(1+L\Delta/\varepsilon)
\inf_t\left[t+\frac{1+\kappa\sigma^2/\varepsilon}{R(t)}\right]\right),
&Q_{route}&=O((1+L\Delta/\varepsilon)(1+\kappa\sigma^2/\varepsilon)),\\
T_{power}&=O\!\left((1+L\Delta/\varepsilon)
\inf_t\left[t+\frac{1+\kappa\sigma^2/\varepsilon}{R_u(t)}\right]\right),
&Q_{power}&=O((1+L\Delta/\varepsilon)(1+\kappa\sigma^2/\varepsilon+u)).
\end{aligned}
\]

Freeze one point per phase, obtain Θ(1+κσ²/ε) independent samples using exactly the same dispatcher, then take one sharp step. Conditional minibatch variance is ≤κσ²/B and ordinary descent needs O(1+LΔ/ε) phases. The routed plan pays exactly B samples; the power plan pays whole packets totaling between B and B+u. Thus frozen minibatching matches both displayed orders, including overshoot, without private updates. This is a verified reduction here, not an attribution of the new scheduling theorem to an older optimization paper.

For routing, greedy fractional assignment followed by forbidden-interval packing gives the explicit phase bound 2J²B/R+(4J+2)t. After this weighted no-wait scheduling step and zero-chain transfer, the optimization wrapper adds no better complexity; its residual value is accommodating private updates. Classical [Leighton–Maggs–Rao routing](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/phrensy/pub/papers/LeightonMR94/LeightonMR94.html) is proof ancestry, not a checked replacement for weighted no-wait scheduling. Optimality is only at fixed J, not uniformly in depth.

The atomic frontier is the strongest candidate contribution. [MatchingLower](../../LongTails/Proofs/BirchResourceMatchingLower.lean) charges each successful chain transition to a distinct frozen packet; a pathwise work limit W restricts useful packet size to order Wε/(LΔ). It yields expected time
\[
\Omega\!\left(\frac{L\Delta}{\varepsilon}\inf_t
\left[t+\frac{1+\sigma^2/\varepsilon}{R_{\lfloor CW\varepsilon/(L\Delta)\rfloor}(t)}\right]\right).
\]
This matches the upper frontier with constant work dilation at fixed κ and feasible work levels, not at exactly the same W. Taking u at least the largest available packet size gives the unrestricted matching time order; this does not establish κ-optimality. For σ=0, one device with modes (duration,size)=(M,1),(1,M), both drawing the full cap, illustrates real content: O(LΔ/ε) work forces order MLΔ/ε time when M exceeds the dilation constants, whereas O(MLΔ/ε) work allows O(LΔ/ε) time.

The [Euclidean companions](../../LongTails/Proofs/BirchResourceTimedTrace.lean) use one private and one virtual main edge per accepted reply, preserve frozen packet points, and achieve distance≤B−1. The native companions use retained sharp steps and exact merges. Lower-bound ancestry is the stochastic zero chain of [Arjevani et al., Theorem 1, Mathematical Programming 2023](https://arxiv.org/pdf/1912.02365); hardware eligibility and atomic transition charging are additional work, not consequences of its oracle lower bound alone.

**Formal scope and search limits.** The lower statements concern finite predictable completion ledgers, supported outputs, integrable elapsed time and zero-respecting information flow; routing permits buffering. They construct dimensions of order LΔ/ε, require LΔ/ε≥983040 for the displayed matching scaling, and cover Euclidean/controlled-distortion norms including the axial example, not arbitrary κ-dependent optimality. Unbounded randomized stopping requires an additional truncation argument not established by these finite-ledger exports. The companion note largely states these limits correctly; its Θ summaries must retain them.

Research date: **2026-11-08 UTC**. Searches covered arXiv, ICML/ICLR/NeurIPS sources, subsequent synchronous and universal-computation analyses, norm-native descent, zero chains, and no-wait/power scheduling. [Tyurin's ICLR 2025 Theorem 5.3](https://arxiv.org/html/2408.04929) handles exogenous worker speeds, not controllable shared resources; it supplies no automatic atomic-work frontier. The Bansal–Mahdian–Sviridenko weighted no-wait paper's [full report](https://dominoweb.draco.res.ibm.com/reports/rc23070.pdf) was inaccessible, and priority of the precise atomic cutoff lower bound remains unverified. Git has no commits here, so introduction chronology is unavailable; the October 2026 paper is a present-day baseline, not proven historical prior art. Both repository assessment-example files were applied.

**Conclusion**

**Broader analysis coverage is established; a new optimization advantage is not.** The strongest direct native baseline, Rennala NSGD Appendix D.4, already gives the same finite-variance expected-stationarity rate. The collection framework adds retained and overlapping histories, with eleven concrete families and exact Euclidean recovery, but those facts do not imply uniformly sharper budgets.

The routed result remains a useful shared-resource model and private-update construction; its upper order also follows from frozen minibatching once the same weighted no-wait dispatcher is available. The power result goes further by relating indivisible packet work to attainable time, and the two-mode example shows why throughput alone misses that tradeoff. Neither result proves a practical speedup over a competitor using the same scheduling resources and costs.

As one standalone paper, the integrated compiler, retained-history analysis and atomic frontier form a coherent candidate, rather than eleven separate novelty claims. Substantive novelty would rest chiefly on the frontier and the non-tree certificate construction; the outstanding scheduling-priority comparison prevents a firm positive assessment, while the checked minibatching reduction does not invalidate the lower frontier. The defensible contribution is an integrated analysis of certified native histories and resource-constrained executions, with no established present-day total-complexity advantage over frozen minibatching in any checked regime.

**Verdict: INCONCLUSIVE**. **Confidence: medium**.
