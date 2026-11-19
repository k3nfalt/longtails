# Novelty review: MultirateDistributedStationarity

The [theorem](../../LongTails/Theorems/MultirateDistributedStationarity.lean) covers a bit-priced star network with $n$ workers. Each worker holds an $L_i$-smooth $f_i$ with an unbiased oracle of variance $\sigma_i^2$, and $F=\frac1n\sum_i f_i$ has initial gap $\Delta$. The [event-driven multirate algorithm](../../LongTails/Algorithms/MultirateProtocol.lean) returns $X$ with $\mathbb E\|\nabla F(X)\|^2\le\varepsilon^2$ within the elapsed time `budget p` ([setup](../../LongTails/Setups/MultirateSmoothNonconvex.lean)).

**Simplified bound.** The parameters are as follows. $h_i$ is worker $i$'s time per gradient, with $h_{\max}=\max_i h_i$. $\ell$ and $b$ are the packet latency and the time per bit. $d$ is the dimension, and $\bar L=\frac1n\sum_iL_i$. All of $h_i,L_i,\sigma_i,\Delta,\ell,b$ are known. The proved budget is

$$
O\Big(h_{\max}+\tfrac{\sum_ih_i\sigma_i^2}{n^2\varepsilon^2}+\big(1+\tfrac{\bar L\Delta}{\varepsilon^2}\big)\big[\ell+b\,d\log_2\!\big(2n(d+1)(1+\tfrac{\bar L\Delta}{\varepsilon^2})\big)\big]+\tfrac{\Delta\sum_iL_ih_i}{n\varepsilon^2}+\tfrac{\Delta(\sum_i\sigma_i\sqrt{L_ih_i})^2}{n^3\varepsilon^4}\Big).
$$

The constant 64 clock bits per packet is absorbed into the $O$.

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Malenia SGD, Tyurin–Richtárik, [NeurIPS 2023, arXiv 2305.12387](https://arxiv.org/abs/2305.12387), Thm A.4. The matching lower bound, Thm A.2, is over the class where only the average is smooth. Direct competitor; communication is free. | Set ε→ε², $L=\bar L$ (F is $\bar L$-smooth), $\sigma=\max_i\sigma_i$. Before: $h_{\max}\bar L\Delta/\varepsilon^2+\frac{\sum_ih_i}{n}\frac{\sigma_{\max}^2\bar L\Delta}{n\varepsilon^4}$. After, at $\ell=b=0$: the display above. | Uniformly no worse when $\bar L\Delta\ge\varepsilon^2$, because $\sum_iL_ih_i\le n\bar Lh_{\max}$ and, by Cauchy–Schwarz, $(\sum_i\sigma_i\sqrt{L_ih_i})^2\le\sigma_{\max}^2n\bar L\sum_ih_i$. Polynomial gain when curvature is not concentrated on the slow workers. Example: $L_i=\sigma_i=\Delta=1$, $h_n=n^3$, all other $h_i=1$, $\varepsilon=1/n$ gives $n^5\to n^4$. With equal $L_i$ the deterministic term improves from $h_{\max}$ to the mean of the $h_i$. | None. The class is narrower; see the last column. | Before, a single variance bound $\sigma_{\max}$ was used. Now worker-specific $\sigma_i$ enter through a batch allocation. The output criterion is the same: a random or selected iterate with an expected squared norm. | Requires each $f_i$ to be $L_i$-smooth, not just the average. The hard instance of Thm A.2 places the scaled hard function $n\cdot g$ on the slowest worker, which gives $L_n=n\bar L$. There the new bound reduces to $h_{\max}\bar L\Delta/\varepsilon^2$, so the extra assumption is essential. Needs known, fixed $h_i$, whereas Malenia does not use $\tau_i$. Charges a startup cost of $h_{\max}$. Adds a bit cost with a $\log(\bar L\Delta/\varepsilon^2)$ factor. |
| Ringleader ASGD, Maranjyan–Richtárik, [ICLR 2026, arXiv 2509.22860v3](https://arxiv.org/abs/2509.22860), §5.2 and Table 1 | $\frac{L\Delta}{\varepsilon^2}\big(h_{\max}+\frac{\sum_ih_i}{n}\frac{\sigma^2}{n\varepsilon^2}\big)$ with the mixed-point constant $\bar L\le L\le\sqrt{\tfrac1n\sum L_i^2}$ → the display above | Same gains as for Malenia. Ringleader's $L$ is no smaller than $\bar L$. | None | Ringleader handles time-varying speeds without knowing them. The new result needs known, fixed times. | Same as the Malenia row. Communication is not priced. |
| Leon SGD, Tyurin, [arXiv 2603.20735v1](https://arxiv.org/abs/2603.20735) (Mar 2026), Thm 1.7 | $\max\{d/\bar w_1,h_{\max},\frac{\sigma^2}{n\varepsilon^2}\frac{\sum_ih_i}{n}\}\frac{L\Delta}{\varepsilon^2}$ → the display above | Gains in the computation terms are as above. Communication is not comparable: Leon prices real coordinates on general graphs, while this result prices bits on a star. | None | None | Same as the Malenia row. Communication is not comparable. |
| Repository: [MultiscaleAggregateStationarity](../../LongTails/Theorems/MultiscaleAggregateStationarity.lean), committed the same day (2026-11-19) | $(1+\frac{\bar L\Delta}{\varepsilon^2})[h_{\max}+\frac{\sum h_i\sigma_i^2}{n^2\varepsilon^2}+\ell+bd\log_2(n(d+1))]$, for the weaker criterion $\mathbb E\|\nabla F\|\le\varepsilon$ → the display above | Same gain in the computation terms. | None | The criterion is stronger: the squared norm is controlled rather than the norm. | Worse bandwidth term, by an extra $\log(1+\bar L\Delta/\varepsilon^2)$ bits per coordinate. Requires individual smoothness. |

**Reduction and mechanism.** No substitution into Malenia, Ringleader, Rescaled ASGD ([arXiv 2605.13434](https://arxiv.org/abs/2605.13434), Cor. 4.2), or FedSUM ([arXiv 2512.18275](https://arxiv.org/abs/2512.18275), Thm 4.1) yields $\sum_iL_ih_i$. All of them keep $\tau_{\max}$ in the deterministic term, even those that assume each $f_i$ is $L_i$-smooth. The ingredients are familiar: drift of stale gradients weighted by $L_i$ is the same idea as LAG's skip rule, and the cached-noise orthogonality echoes DuDe-ASGD. The new part is how they are combined: refresh periods $q_i$ tied to curvature and time, concurrent outstanding requests, a variance-weighted batch allocation, and a finite-bit lattice codec. That combination gives the stated end-to-end time bound. The note's multi-tier argument suggests that a naive synchronous snapshot method loses a factor $\log n$, but this is shown only for one proof template.

**Search coverage.** The search was done on 2026-11-19. It covered arXiv and proceedings for asynchronous and heterogeneous elapsed-time SGD: Malenia, Ringleader, Ringmaster, Shadowheart, Leon/Grace, Rescaled ASGD, clipped ASGD ([arXiv 2606.13287](https://arxiv.org/abs/2606.13287)), FedSUM, LAG, and Tyurin's [arXiv 2609.17483](https://arxiv.org/abs/2609.17483). Some theorem statements (Ringleader, Rescaled ASGD, FedSUM) were read only through partial HTML extracts. I did not survey the classical IAG and asynchronous-iteration literature with per-component delays exhaustively. The companion note's citations match what I checked. Its claim of $n^4$ against $n^5$ in the one-straggler example is consistent with my calculation.

## Conclusion

**Yes: the proved elapsed time beats the best known heterogeneous asynchronous bounds whenever slow workers carry little curvature.**

The strongest baseline is Malenia SGD, which is optimal for the class where only the average $F$ is smooth. On the common class where each $f_i$ is $L_i$-smooth and communication is free:

| | deterministic term | statistical term |
|---|---|---|
| Malenia | $\bar L\Delta\,h_{\max}/\varepsilon^2$ | $\sigma_{\max}^2\bar L\Delta\sum_ih_i/(n^2\varepsilon^4)$ |
| this result | $\Delta\sum_iL_ih_i/(n\varepsilon^2)$ | $\Delta(\sum_i\sigma_i\sqrt{L_ih_i})^2/(n^3\varepsilon^4)$ |

Each new term is no larger than the corresponding Malenia term. The gain is polynomial, for example $n^5\to n^4$ with one straggler. When all $h_i$ and $L_i$ are equal the bounds coincide. At Malenia's own lower-bound instance, which concentrates all curvature on the slowest worker, the new bound also reduces to $h_{\max}$. This shows that individual smoothness is exactly what removes the $h_{\max}$ barrier.

The tradeoffs are as follows. The result needs individual smoothness, known and fixed worker times, and a startup cost of $h_{\max}$. Its bit-priced communication carries an extra logarithmic factor. Its optimality is unproved, since no lower bound in terms of $\sum_iL_ih_i$ exists.

The comparison establishes the gain. My search found no prior bound with curvature-weighted computation times, but the classical incremental-aggregated-gradient literature was not exhaustively checked. The claimable contribution is the first elapsed-time guarantee in which the cost of slow workers scales with their curvature, giving a strict improvement over Malenia, Ringleader and Leon for heterogeneous profiles.

**Verdict: SUBSTANTIVE NOVELTY SUPPORTED**
**Confidence: medium**
