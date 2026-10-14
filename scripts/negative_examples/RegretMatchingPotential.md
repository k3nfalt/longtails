# RegretMatchingPotential: novelty assessment

The [theorem](../../LongTails/Theorems/RegretMatchingPotential.lean), [setup](../../LongTails/Setups/RegretMatchingPotential.lean), and [algorithm](../../LongTails/Algorithms/RegretMatchingPotential.lean) guarantee, for every admissible game and every oracle seed, an additive ε-Nash mixed profile saved from an earlier certified round of zero-initialized simultaneous RM+.

Here m,n≥1 are action counts, B>0 bounds an exact potential P∈[0,B], and ε>0. Payoff differences equal potential differences; payoff levels are unrestricted. Each call returns both exact payoff vectors (Ay,Cᵀx). The execution uses exactly

\[
\left\lceil20000B^2(m+n)^4/\varepsilon^2\right\rceil+1
=O\!\left(1+B^2(m+n)^4/\varepsilon^2\right)
\]

calls; no batching/search/restarts. Updates normalize regret states (uniform at zero), then clip after adding regrets. Public information is m,n,ε; B sets the external horizon. Output is a certified **pre-update** profile, not averaged or last-iterate accuracy.

All table bounds count this paired-vector oracle and certify the same ε-Nash inequalities; comparisons use 0<ε≤B.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Anagnostides et al., [ICLR 2026 / arXiv v2 (17 Nov 2025), Th. 3.12, App. C.1](https://arxiv.org/html/2510.17067v2#S3.Thmtheorem12) | O(1+B⁸(m+n)¹⁰/ε⁸) → O(1+B²(m+n)⁴/ε²) | ε⁻⁸→ε⁻² for fixed dimensions and B; ratio of dominant bounds B⁶(m+n)⁶/ε⁶. | None: current games are a subclass of smooth product-simplex objectives. | None: both certify an iterate using ε. | Prior is ε-lazy; current updates every round. Prior also covers more players/objectives. |
| Same paper, [Cor. 3.5](https://arxiv.org/html/2510.17067v2#S3.Thmtheorem5), discounted alternating RM+ | O(1+B²max(m,n)/ε²) → O(1+B²(m+n)⁴/ε²) | Worse dimension bound; same accuracy exponent. | None. | None. | Current removes discounting and sequential updates, but covers only two players. |
| Dewasurendra–Jayawardhana, [v2, Ths. 6, 8](https://arxiv.org/html/2608.17417v2), 23 Aug 2026; withdrawn 24 Sep | O(1+B²max(m,n)/ε²) → O(1+B²(m+n)⁴/ε²) | Worse dimension bound; same accuracy exponent. | None. | None: observable certificates in both. | Prior is lazy alternating and covers any player count; current is ordinary simultaneous. Withdrawal concerns unverifiable authorship, not a verified mathematical refutation. |
| Monderer–Shapley, [GEB 1996, Lemmas 2.3, 4.2](https://people.csail.mit.edu/jrennie/trg/papers/monderer-potential-96.pdf), unilateral improvement / matrix-recovery reductions (derived) | O(min{max(m,n),1+B/ε}) → O(1+B²(m+n)⁴/ε²) | Worse for ε≤B; no general equilibrium-computation speedup. | None. | None: both certify a profile without B in updates. | Prior coordinates deviations or reconstructs matrices, returning a pure profile; current preserves simultaneous RM+. |

First-row derivation: substitute P/B, ε/B, and smoothness √(mn); solve the appendix inequality T≤O(1+(m+n)⁴B²/ε²)(1+2max(m,n)B²√T/ε²). Discounting uses γ=1/2; alternating sweeps cost two calls. Unilateral improvement costs one call per profile and gains >ε potential. Alternatively, max(m,n) paired basis queries recover A,C; maximize Pᵢⱼ=Aᵢⱼ−A₁ⱼ+C₁ⱼ−C₁₁ to obtain exact Nash. Arithmetic is uncharged.

Payoff shifts/rescaling are routine, adding no substantive scope. Simultaneous low-state motion requires [lagged_le](../../LongTails/Proofs/RegretMatchingStep.lean) and [bound_of_potential / size_bound](../../LongTails/Proofs/RegretMatchingGame.lean) to prove ‖Qᵢ(T)‖₂≤100B(m+n)² uniformly. Gain/movement and norm-growth tools already appear in ICLR Lemmas C.5–C.6, 3.8 and withdrawn Th. 2; neither supplies this simultaneous bound by substitution. Hart–Mas-Colell's [GEB 2003, Th. A.1](https://math.huji.ac.il/hart/papers/regret.pdf) concerns asymptotic empirical marginals of different dynamics, not this finite certified-iterate guarantee.

Search through **2026-10-05 UTC** covered current arXiv, ICLR proceedings/author PDF, journal foundations, and ICML/NeurIPS searches; no material source remained inaccessible or subsequent superseding theorem was located. Git introduction: `7b749ed`, 2026-10-04; all baselines predate it. The companion note overstates the ε⁻⁸ baseline as ordinary RM+: its proof is lazy; it also omits discounted ε⁻² competition. Repository `SmoothConvexConcave` addresses saddle points, not general potential games. Constant potentials and m=n=1 are trivial; ε≥B makes every profile accurate; B=0 and ε=0 are excluded. No build or axiom audit was run.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED** — confidence **medium**.

**New advantages**

- Versus ICLR Th. 3.12: ε⁻⁸→ε⁻² for two-player potential games, with ordinary always-updating simultaneous dynamics replacing lazy updates.
- Versus ICLR Cor. 3.5 and withdrawn Ths. 6/8: discounted/sequential or lazy alternating play → zero-initialized, undiscounted simultaneous RM+; dimension dependence worsens and player count narrows.
- Versus those analyses: a lagged-gain correction controls the simultaneous transient and establishes a uniform regret-state bound without an initialization threshold.

The substantive contribution is controlling unchanged simultaneous RM+ dynamics, despite faster general equilibrium solvers. No parameter-knowledge, oracle-access, last-iterate, or optimality advantage is established; the comparisons support historical and current novelty with medium confidence.
