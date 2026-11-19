# Distributed stationarity with curvature-weighted worker times

A server minimizes the average of $n$ smooth local objectives. Each worker owns one objective and has a dedicated link to the server. A slow worker can have a large gradient while contributing little change in that gradient as the server moves. The algorithm keeps that worker in the average and pays for its updates less frequently. [Lean theorem and explicit elapsed-time budget](MultirateDistributedStationarity.lean) · [Problem and accuracy criterion](../Setups/MultirateSmoothNonconvex.lean) · [Event-driven algorithm](../Algorithms/MultirateProtocol.lean)

## Guarantee

Write $F(x)=n^{-1}\sum_i f_i(x)$ on $\mathbb R^d$, $\bar L=n^{-1}\sum_i L_i$, and $h_{\max}=\max_i h_i$. Each $\nabla f_i$ is $L_i$-Lipschitz. A lower bound $a$ on **the average objective** satisfies $F(x_0)-a\le\Delta$. Individual objectives may be unbounded below. Worker $i$ returns a jointly measurable, unbiased gradient estimate with centered second moment at most $\sigma_i^2$. Samples are IID within a worker and independent across workers. Each query consumes a fresh sample. The parameter bounds, initial point, service times, and link costs are public.

Each oracle call returns one stochastic gradient vector and takes $h_i>0$ time on worker $i$. A packet of $m$ bits takes $\ell+bm$, including the template's 64 clock bits. Each worker computes serially. Each directed link carries at most one packet at a time. Distinct links and workers can operate concurrently. The model charges zero elapsed time for local arithmetic and storage. Both $\ell$ and $b$ may be zero. [Star computation and communication oracles](../Setups/StarNetwork.lean) · [Execution and time conventions](../TemplateDistributed.lean)

For any $\varepsilon>0$, the server returns $X$ with $\mathbb E\|\nabla F(X)\|^2\le\varepsilon^2$. Its elapsed time is at most a universal constant times

$$
 h_{\max}+\frac{\sum_i h_i\sigma_i^2}{n^2\varepsilon^2}
 + \left(1+\frac{\bar L\Delta}{\varepsilon^2}\right)c
 + \frac{\Delta\sum_i L_i h_i}{n\varepsilon^2}
 + \frac{\Delta(\sum_i \sigma_i\sqrt{L_i h_i})^2}{n^3\varepsilon^4},
$$

where $c=O(\ell+b[64+d(1+\log_2(n(d+1)(1+\bar L\Delta/\varepsilon^2)))])$ accounts for an entire packet in either direction. The Lean budget gives explicit constants and integer bit lengths. Every seed has finitely many events at every deadline through the budget. The guarantee covers arbitrary finite dimension, nonconvex objectives, zero variances, and flat components. It charges startup even when the initial gradient meets the tolerance. [Budget proof](../Proofs/MultirateBudget.lean) · [Termination and execution proof](../Proofs/MultirateExecution.lean)

For example, take $f_i(x)=a_i^\top x+\lambda_i(1-\cos(v_i^\top x))$, with $\sum_i a_i=0$, $\lambda_i\ge0$, and nonorthogonal unit vectors $v_i$. Here $L_i=\lambda_i$. Dense directions couple coordinates, and scaling the $a_i$ can make the local gradients arbitrarily far apart. Independent centered gradient noise of finite variance, including noise with unbounded support, is allowed.

## Algorithm and proof

Let $\delta=\varepsilon/1024$, $V=\sum_i h_i\sigma_i^2$, $Q=\sum_i\sigma_i\sqrt{L_i h_i}$, and $E=(n\delta)^2$. Worker $i$ receives a share $s_i=(E/2)(h_i\sigma_i^2/V+\sigma_i\sqrt{L_i h_i}/Q)$ of the variance budget and uses $m_i=1+\lfloor\sigma_i^2/s_i\rfloor$ samples per request. A ratio with zero denominator contributes zero. The allocation gives three simultaneous bounds,

$$
\sum_i\sigma_i^2/m_i\le E,\qquad
m_i h_i\le h_i+2V/E,\qquad
\sum_i L_i m_i h_i\le\sum_i L_i h_i+2Q^2/E.
$$

The individual time bounds pay for startup, when every worker reports. The curvature-weighted sum governs the repeated work. [Allocation and rounding proof](../Proofs/MultirateAllocation.lean)

There are $K$ normalized updates, a power of two of order $1+\bar L\Delta/\varepsilon^2$. Let $c_0$ be the exact packet time. The server sets

$$
 u=2c_0+h_{\max}/K+\frac{\sum_i L_i m_i h_i}{\sum_i L_i},\qquad
 q_i=1+\left\lfloor(2c_0+m_i h_i)/u\right\rfloor .
$$

At round $k$, it collects replies from workers with $q_i\mid k$, keeps the other cached estimates, and sends each due worker its next query if that query will be used. A request issued at round $k$ can finish by the time bound for round $k+q_i$. Faster workers can finish other requests meanwhile. Worker $i$ completes $m_i(1+\lfloor(K-1)/q_i\rfloor)$ gradient calls and one query and one reply packet per batch. This includes the second batch at the initial point when scheduled. Early replies wait in a mailbox. Local wake events consume no time and the termination proof counts them. [Calendar](../Proofs/MultirateCalendar.lean) · [Request schedule](../Proofs/MultirateSchedule.lean)

The server takes steps of length at most $2\delta/\bar L$. The point underlying a cached gradient is less than $2q_i$ updates old, including the time spent evaluating the outstanding query. Since $\sum_i L_i q_i\le3\sum_i L_i$, the mean drift stays of order $\varepsilon$. The current caches have different random query points. Ordering two cached batches by their scheduled release makes the earlier error and the later query measurable before the later batch's samples are revealed. The centered errors therefore have zero cross moment, including at tied releases. [Drift bound](../Proofs/MultirateDrift.lean) · [Orthogonality proof](../Proofs/MultirateOrthogonality.lean)

The downlink rounds displacement from the public initial point. On the uplink, workers send residues of rounded local batch gradients. The server sums the residues and lifts the **aggregate vector** in a ball of radius $3R$, where $R=2K\delta$. It returns the zero estimate if the ball contains no congruent vector. Bounded normalized travel and the initial gap keep the true gradient within $2R$. Even on samples that overflow the ball, the decoded error is at most five times the unwrapped error. This controls squared error without bounding local gradients. The server draws two independent uniform iterate indices and returns the point with the smaller stored estimate norm. Selection uses no extra calls. [Codec inequality](../Proofs/MultirateEncoding.lean) · [Output and expected accuracy](../Proofs/MultirateAccuracy.lean)

## Comparisons and limitations

**Same finite-bit star.** The earlier MultiscaleAggregateStationarity theorem uses the same computation times, link latency, per-bit costs, concurrency restrictions, and worker-specific IID variance bounds. It assumes only $L$-smoothness of the average and guarantees $\mathbb E\|\nabla F(X)\|\le\varepsilon$ in time
$$
O\!\left((1+L\Delta/\varepsilon^2)
\left[h_{\max}+\frac{\sum_i h_i\sigma_i^2}{n^2\varepsilon^2}
+\ell+b\{64+d(1+\log_2(n(d+1)))\}\right]\right).
$$
On the common class take $L=\bar L$. The new squared criterion implies the earlier norm criterion by $\mathbb E\|\nabla F(X)\|\le\sqrt{\mathbb E\|\nabla F(X)\|^2}$. Individual smoothness allows the server to amortize the slow workers' startup and charge later refreshes by their curvature. The new fixed-width code also adds a term of order $\log_2(1+\bar L\Delta/\varepsilon^2)$ bits per coordinate. The earlier multiscale code can give a better communication contribution when bandwidth dominates. In the one-straggler example below, the earlier formula gives order $n^5$ and the new one gives order $n^4$ with the same positive link prices. [Previous theorem and budget](MultiscaleAggregateStationarity.lean) · [Previous setup and success criterion](../Setups/DistributedAggregateSmoothNonconvex.lean)

**Elapsed-time baselines.** Ringleader ASGD and Malenia SGD already handle arbitrary gradient dissimilarity. Their fixed-service bounds with free real-vector communication and common variance contain terms of order $L\Delta h_{\max}/\varepsilon^2$ and $L\Delta\sigma^2\sum_i h_i/(n^2\varepsilon^4)$ on our norm-accuracy scale. Ringleader uses a mixed-point smoothness condition and also handles changing speeds. Malenia and Leon SGD can use smoothness of the average alone. We require individual curvature and service bounds. On equal local curvatures the repeated deterministic computation term becomes $L\Delta\sum_i h_i/(n\varepsilon^2)$. The statistical term involves $(\sum_i\sqrt{h_i})^2/n$ in place of $\sum_i h_i$. Leon prices real coordinates over general graphs. A comparison of its communication time with the bit-priced star requires a separate encoding argument. [Ringleader ASGD, ICLR 2026, Table 1 and §2.3, v3](https://arxiv.org/html/2509.22860v3) · [Tyurin, Theorem 1.7 and §5, v1](https://arxiv.org/html/2603.20735v1)

**Stale-gradient baselines.** DuDe-ASGD already caches heterogeneous stochastic gradients and proves stale-noise orthogonality. Its Theorem 1 retains a maximum delay. FedSUM's Theorem 4.1 incorporates average delay in the statistical term while retaining maximum delay in the deterministic term. Even granting perfect initialization, this term requires order $\tau_{\max}L\Delta/\varepsilon^2$ rounds in the certificate, and a slow source must participate at least once per $1+\tau_{\max}$ rounds. Larger per-participation batches still require at least one call. MIFA's nonconvex average-delay theorem additionally uses Lipschitz Hessians, almost-sure noise control, and a dissimilarity bound. The contribution here is to realize a curvature-weighted concurrent rate, including its worker-specific variance allocation and full finite-bit execution, for the unrestricted local offsets of this problem. [DuDe-ASGD, Lemma 1 and Theorem 1](https://arxiv.org/html/2405.16966v1) · [FedSUM, Theorem 4.1, v1](https://arxiv.org/html/2512.18275v1) · [MIFA, NeurIPS 2021, Theorem 6.1](https://proceedings.neurips.cc/paper_files/paper/2021/hash/64be20f6dd1dd46adf110cf871e3ed35-Abstract.html)

**One straggler.** For $L_i=\sigma_i=\Delta=1$, $h_n=n^3$, all other $h_i=1$, $d=n$, $\varepsilon=1/n$, and fixed positive $\ell,b$, the bound is $O(n^4)$, including both finite-bit links. The maximum-service certificates above give order $n^5$ even with communication free. A synchronous method that freezes the slow worker's estimate for $n$ fast updates can also attain the $n^4$ scaling in this two-tier example. Uniform worker times remove the compute-profile advantage in this equal-curvature, equal-noise comparison. Communication can dominate, and the fixed-width codec pays a logarithmic factor in accuracy and dimension.

**Several speed tiers.** Take $n=2^J-1$ and $2^{J-1-j}$ workers with service $H2^j$ in tier $j=0,\ldots,J-1$. Set $H=n^2$, $L_i=\Delta=1$, $\sigma_i=n^{-1/2}$, $d=n$, and $\varepsilon=1/n$, with fixed positive link costs. The theorem gives $O(n^4J)$. For synchronous periodic snapshots with periods $p_j$ and tier fractions $w_j$, the usual drift certificate costs a factor $\sum_j w_jp_j$ in updates. A blocking refresh pays at least half the sum of the due tier costs because the services are geometric. The resulting computation certificate contains

$$
 \left(\sum_j w_jp_j\right)\left(\sum_j H2^j/p_j\right)
 \ge \left(\sum_j\sqrt{w_jH2^j}\right)^2=\Theta(HJ^2).
$$

Concurrent requests reduce the corresponding factor to $\sum_j w_jH2^j=\Theta(HJ)$. This comparison concerns that synchronous schedule and drift proof. Optimality across all worker profiles remains open.

**Limits.** Tyurin's lower bounds show that smooth similarity conditions alone can leave a substantial heterogeneous startup penalty. Strong interpolation with local PL structure gives a different route to exploiting fast workers. This theorem requires neither condition. It proves an upper bound for known, fixed service times on a dedicated star. [Tyurin, §§2–3, v1](https://arxiv.org/html/2609.17483v1)
