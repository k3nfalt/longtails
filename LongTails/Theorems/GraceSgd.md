# GRACE SGD with finite-bit links

A worker can forward one part of a gradient while the next part is still arriving. How much time does that save when links carry finite binary messages and a gradient can have arbitrary real coordinates? This result adapts GRACE SGD to that model. It bounds the elapsed time until a designated worker returns a point with expected squared gradient norm at most $\varepsilon$. The bound includes the time for the first packet to traverse its route. [Lean theorem and budget](GraceSgd.lean) · [Problem and oracle model](../Setups/GraphBandwidthSmoothNonconvex.lean) · [Worker program](../Algorithms/GraceSgd.lean)

## Guarantee

Let $G=(V,E)$ be a finite connected undirected graph with $n$ workers. In each direction, edge $e$ has bandwidth $b_e>0$ bits per second and its own FIFO queue. Distinct directions and links can operate concurrently. Every physical packet carries a 64-bit header. There is zero additional propagation delay. A worker serves one minibatch at a time, taking $h_i>0$ seconds per sample. Local arithmetic and preprocessing take zero modeled time.

All workers sample the same jointly measurable, unbiased stochastic gradient with variance at most $\sigma^2$. Samples are IID within workers and independent across workers. The objective on $\mathbb R^d$ has $L$-Lipschitz gradient and admits a lower bound $f_*$ with $f(x_0)-f_*\leq\Delta$. For example, $f(x)=m^{-1}\sum_{j=1}^m(1-\cos(a_j^\top x))$ with nonorthogonal, nonparallel $a_j$ is a smooth nonconvex instance with interacting coordinates. A uniform summand gives an unbiased oracle with variance bounded by $m^{-1}\sum_j\|a_j\|^2$. Graph rates, computation times, $L,\Delta,\sigma,\varepsilon$ and $x_0$ are public.

Define

$$
\begin{aligned}
K&=\max\{1,\lceil 32L\Delta/\varepsilon\rceil\},&
B&=\max\{1,\lceil256\sigma^2/\varepsilon\rceil\},\\
t&=64+\operatorname{bitlength}(B),&
w&=32+4\left\lfloor\log_2\!\left(2+d+\lceil2L\Delta/\varepsilon\rceil+
                    \lceil\sigma^2/\varepsilon\rceil\right)\right\rfloor .
\end{aligned}
$$

For a worker set $S$ of size at least two, $\alpha(S)$ is the minimum bandwidth of any cut with workers of $S$ on both sides. The algorithm selects $J$ uniformly from $0,\ldots,K-1$, independently of the gradient samples. The actual root output $x_J$ satisfies $\mathbb E\|\nabla f(x_J)\|^2\leq\varepsilon$ by the following deadline:

$$
(K-1)\min_{\emptyset\ne S\subseteq V}
\left\{
 \frac{B+|S|}{\sum_{i\in S} h_i^{-1}}+
 \frac{16}{\alpha(S)}
 \left[d(w+t)+t(|E|+1)n\right]
\right\}.
$$

For a singleton $S$, the communication term is zero. A single worker then runs locally even on a graph with expensive edges. If $K=1$, the root returns $x_0$ immediately. The proof bounds the number of executor events at every deadline up to the stated one and counts exactly $JB$ gradient samples across all workers at completion. [Actual output and SGD-family compliance](../Proofs/GraceSgdGuarantee.lean) · [Expected accuracy](../Proofs/GraceBatchTuning.lean) · [Elapsed-time accounting](../Proofs/GraceSgdBudget.lean)

## Algorithm and packet schedule

Choose a nonempty set minimizing the displayed bound. Assign integer local batch sizes $B_i$ with sum $B$ so that each worker finishes by the computation deadline in the first term. Each participating worker clips its local mean to a public, iterate-dependent radius and quantizes it on a common grid. The radius grows with the distance from $x_0$, allowing unbounded stochastic gradients with finite variance. The root reconstructs the batch-weighted mean of the quantized vectors, clips and quantizes that mean once, and broadcasts the resulting grid indices. Each selected worker takes the same step with $\gamma=1/(2L)$. The two quantizations enter the descent proof. The setup also requires that every pending request uses the prescribed iterate and local batch size. [Grid and sample updates](../Algorithms/GraceSgd.lean) · [Statistical trajectory](../Proofs/GraceSgdTrajectory.lean)

For each set $S$, pricing terminal cuts gives a fractional packing of Steiner trees of throughput at least $\alpha(S)/2$. A sparse packing uses at most $|E|+1$ trees. Rounding its weights gives integer numbers of data streams with bounded total load on each link. Any worker may relay for $S$. The program splits a grid index into $t$-bit digits and stripes the digits across the trees. Intermediate workers sum the batch-weighted digits without carrying. Each subtotal fits in $t+\operatorname{bitlength}(B)$ bits, and the root can reassemble the exact weighted index sum. A scheduled packet bundles all digits for one link in one slot and pays the header once. Parent and child slots differ by one hop. This accounts for both the streamed payload and the initial traversal even when the payload is short. [Packing proof](../Proofs/GraceGraphPacking.lean) · [Packet timing](../Proofs/GraceCommunicationTime.lean) · [Reduction and broadcast identities](../Proofs/GraceRoutedValues.lean)

## Comparison and limitations

Tyurin's homogeneous GRACE theorem uses Assumptions 1.1–1.4, a common stochastic objective, the same stationarity criterion and the same step size. Algorithms 1–3 combine heterogeneous minibatches with a Steiner-tree AllReduce. Theorems 1.5 and F.1 charge a communication term of order $d/\bar w_k$ per round in coordinate-throughput units. Our minimum includes each fastest-worker prefix of each Gomory–Hu component in Algorithm 2. For such a prefix $S$ of size at least two, every separating cut has capacity at least the component threshold $\bar w_k$. The computation term has the paper's dependence on $\sigma^2/\varepsilon$, worker speeds and active-set size, up to universal constants. The result here counts transmitted bits and permits arbitrary finite nonnegative payload lengths in the event-driven protocol. [Tyurin, arXiv:2603.20735v1, Theorem 1.5, Section 2 and Appendix F.1](https://arxiv.org/abs/2603.20735v1)

At a fixed bit rate the bulk term is $d(w+t)/\alpha(S)$. The grid precision depends logarithmically on dimension, noise and accuracy. The additional fill-time term $t(|E|+1)n/\alpha(S)$ is independent of $d$. For $d(w+t)\ge t(|E|+1)n$ this charge is at most the bulk term. For a short vector or a large graph it can dominate. The graph factor is an upper bound from sparse packing and worst-case tree depth. Its sharpness is open. Throughput-oriented graph collectives likewise exploit simultaneous tree routes. Here the local estimates, packets and SGD output are linked within one finite execution. [ForestColl, NSDI 2026](https://www.usenix.org/conference/nsdi26/presentation/zhao-liangyu)

This is a finite-bit reproduction of the homogeneous GRACE strategy. It establishes an upper bound for symmetric full-duplex links with the specified deterministic service times. The paper's coordinate-model lower bound does not establish optimality of the bit precision, graph surcharge or this protocol. Public selection and tree construction use exact mathematical optimization over the known graph. Their computational complexity lies outside the elapsed-time model. Heterogeneous worker objectives, independent propagation delays and time-varying link rates would require further analysis.
