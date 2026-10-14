# Uniformly bounded regret for zero-initialized simultaneous Regret Matching+ in two-player potential games

This note explains the result formalized in
[RegretMatchingPotential.lean](RegretMatchingPotential.lean).

Two players run Regret Matching+ (RM+) against each other in an exact potential game. Both start from zero regret vectors and update simultaneously, with no warm start, threshold initialization, alternation or restart. The potential takes values in [0, B]. Then for every horizon T, each player's cumulative regret vector satisfies

  ‖Q_T‖₂ ≤ 100 · B · (m + n)²,

where m and n are the numbers of actions. The bound does not depend on T, on the payoff scale beyond the potential range, or on the game otherwise. As a consequence, some round t < T is an ε-Nash equilibrium once T > 20000 B² (m+n)⁴ / ε². The algorithm can recognize such a round from feedback it already receives.

Anagnostides et al. (ICLR 2026, arXiv:2510.17067) prove an ε⁻⁸ iteration bound for zero-initialized RM+ in potential games, and ε⁻⁴ under a threshold (lazy) initialization. They leave open whether RM+, with or without alternation, can suffer growing regret in potential games. For two players and simultaneous updates, the result here answers this: regret stays uniformly bounded, and the iteration complexity is ε⁻².

## Setup and proved guarantee

The [setup](../Setups/RegretMatchingPotential.lean) contains the following.

- **Game.** Player 1 has m ≥ 1 actions and payoff matrix A. Player 2 has n ≥ 1 actions and payoff matrix C. There is a potential P with entries in [0, B], B > 0, such that A(i,j) − A(i',j) = P(i,j) − P(i',j) and C(i,j) − C(i,j') = P(i,j) − P(i,j'). This covers every two-player exact potential game whose potential has range at most B. The payoffs themselves can be arbitrarily large.
- **Oracle.** A query (x, y) of mixed strategies returns both payoff vectors, A y and Cᵀ x, exactly. One query is one call, and each round uses one call.
- **Public data.** The algorithm knows m, n and ε. It does not know B, P or the payoffs.
- **Success.** The output (x̂, ŷ) is a pair of mixed strategies. Player 1 gains at most ε by deviating to any pure action: (A ŷ)_i ≤ x̂ᵀ A ŷ + ε for all i. The analogous inequality holds for player 2 with C.
- **Admissible algorithm.** `allowedAlgorithm` admits exactly one algorithm, `rmPlusPotential m n ε`. The theorem is therefore a statement about this method.

**Algorithm.** The [algorithm](../Algorithms/RegretMatchingPotential.lean) is simultaneous RM+ from zero.
- Each player keeps Q ≥ 0, starting at Q = 0. It plays x = Q / ΣQ, or the uniform strategy when Q = 0.
- After observing its payoff vector u, it updates Q ← [Q + u − ⟨x, u⟩𝟙]₊ coordinatewise.
- The output is the last round in which both observed regret vectors u − ⟨x, u⟩𝟙 have all entries at most ε. This needs no extra oracle calls. ε is used only in this selection.

**Guarantee.** The budget is

  ⌈20000 · B² · (m + n)⁴ / ε²⌉₊ + 1

oracle calls. The Lean theorem states that the execution with this budget returns an ε-Nash equilibrium.

## Mechanism

Write N = ‖Q‖₂², R = √N, s = ΣQ, q_t = Q_{t+1} − Q_t, and r_t for the instantaneous regret vector. Let D_t = ⟨x_{t+1} − x_t, u_t⟩ be the forward gain. RM+ ignores additive constants in u, so each player effectively sees P y or Pᵀ x.

1. **Single player, any utilities** (`RegretMatchingStep`).
   - ⟨Q_t, r_t⟩ = 0, q_t ≥ r_t and ⟨Q_t, q_t⟩ ≥ 0. Hence N_{t+1} − N_t ≥ ‖q_t‖², and R is nondecreasing.
   - D_t · s_{t+1} = ⟨Q_{t+1}, q_t⟩ ≥ ‖q_t‖², and 0 ≤ D_t ≤ B.
   - Charge: R_{t+1} − R_t ≤ 2m D_t.
   - Movement: if R_t ≥ K, then K · ‖x_{t+1} − x_t‖₁² ≤ 4m D_t.
2. **Lagged-gain lemma** (`lagged_le`). For every utility sequence,
   ⟨x_t, r_{t+1}⟩ ≤ 2 (R_{t+2} − R_t).
   Two bounds give this. First, ⟨x_t, r_{t+1}⟩ ≤ R_{t+2}. Second, ⟨x_t, r_{t+1}⟩ ≤ (N_{t+2} − N_t)/(2R_t). The proof then splits on whether R_t at least doubles. The quantity −⟨x_t, r_{t+1}⟩ = ⟨x_{t+1} − x_t, u_{t+1}⟩ is the gain a player makes against the opponent's *next* strategy. The lemma says its negative part telescopes.
3. **Potential identity.** The bilinear potential Φ(x, y) = xᵀ P y satisfies, exactly,
   Φ_{t+1} − Φ_t = D_y(t) + ⟨x_{t+1} − x_t, u_x^{t+1}⟩ = D_x(t) + D_y(t) + Δxᵀ P Δy.
4. **Phases** (`bound_of_potential`). Fix K = 4B(m+n).
   - When both R_x, R_y ≥ K, the movement bound gives |Δxᵀ P Δy| ≤ ½(D_x + D_y). So Φ increases by at least half the total gain.
   - When R_y ≥ K but R_x < K, the first form of the identity together with the lagged-gain lemma gives Φ_{t+1} − Φ_t ≥ D_y − 2(R_x(t+2) − R_x(t)).
   - Since R_x is nondecreasing, the rounds with R_x < K form a prefix. The subtracted terms therefore telescope and are bounded by about 2K.
   - A potential Ψ = Φ + 2·min(R_x(t) + R_x(t+1), 2K + 6mB) increases by at least D_y/2 in every round with R_y ≥ K, and Ψ stays bounded.
   - The charge inequality turns this into R_y(T) ≤ K + 2nB + 4n(B + 4K + 12mB) ≤ 100 B (m+n)². The same argument works with the players exchanged.
5. **ε-Nash** (`exists_good_round`). Player 1's Nash gap at round t is max_a r_t(a) ≤ ‖q_t‖. A round where this gap exceeds ε increases N by more than ε², and N ≤ (100B(m+n)²)². So at most 10⁴B²(m+n)⁴/ε² rounds are bad for each player, and the budget leaves at least one round that is good for both.

**Lean layout.**
- [RegretMatchingStep](../Proofs/RegretMatchingStep.lean): single-player RM+ inequalities, including the lagged-gain lemma, the charge and movement bounds, and the gap-to-growth bound.
- [RegretMatchingGame](../Proofs/RegretMatchingGame.lean):
  - the phase/potential lemma on real sequences and the counting lemma;
  - the potential-game identities and the cross-term bound;
  - the uniform bound `size_bound`.
- [RegretMatchingRun](../Proofs/RegretMatchingRun.lean): existence of a good round, the execution invariant for the output rule, and the ε-Nash conclusion.

## Relation to prior work

- **Anagnostides et al., ICLR 2026 (arXiv:2510.17067).**
  - RM+ in potential games: ε⁻⁸ iterations from zero initialization, ε⁻⁴ with a threshold initialization.
  - Bounded regret for RM+ in potential games, with or without alternation, is posed as open.
  - Here, for two players and simultaneous updates from zero, regret is bounded uniformly in T, giving ε⁻².
- **arXiv:2608.17417 (withdrawn by arXiv administrators).** It contains a charge inequality similar to item 1. It uses it to bound regret uniformly only under alternating (and cyclic) play, where forward gains telescope directly into the potential. Its abstract claims no result for simultaneous play, and its regret bound in terms of the centered temporal variation of the utilities does not give one, because under simultaneous play that variation is controlled by the opponent's path length, which is not bounded a priori. Its proofs were not peer reviewed and the paper was withdrawn for unverifiable authorship.
- **What is new here.** For simultaneous play, the forward gains do not telescope, and a low-regret player's strategy can move by O(1) per round. The lagged-gain lemma, combined with the exact one-player-lagged form of the potential identity, controls this transient. To our knowledge, neither ingredient appears in prior work.

## Limitations

- **Two players only.** For three or more players, two players can be in the low-regret phase at the same time. The low–low cross terms are not covered by the argument. Numerically, three-player games show the same behavior: in 300 random 2–3-action three-player potential games run to T = 20000, max ‖Q‖₂ ≤ 1.79, flat in T. But this is not proved.
- **Constants and the dependence on (m, n).** The bound uses s ≤ m R in place of s ≤ √m R, plus crude phase constants. The (m+n)⁴ factor in the budget is not claimed to be optimal; numerically the regret is far below the bound.
- **The guarantee concerns a good iterate found by the algorithm's own feedback,** not the last iterate. Last-iterate convergence is not claimed.
- **ε⁻² is not known to be optimal** for this method. No lower bound is proved.
