# Shorter distributed deadlines from worker smoothness bounds

A fast worker can contribute many noisy gradients while a slow worker computes one. Under mean-squared strong growth, the optimal statistical weighting of these gradients is already known. The remaining question is how often the coordinator must wait for all workers and exchange finite-bit packets. This theorem uses public worker smoothness bounds to set the clipping and step sizes. On one heterogeneous family it reduces the certified time by a factor of order $\sqrt n$ relative to the earlier gradient-diversity schedule. Its leading statistical term is the one proved in the earlier strong-growth theorem. [New theorem and exact deadline](DistributedLocallySmoothGrowth.lean) · [Statistical weighting](DistributedStrongGrowthTime.md) · [Earlier communication bound](DistributedGradientDiversity.md)

## Problem and execution

Worker $i$ has a differentiable convex loss $f_i$ on $\mathbb R^d$ and a public Lipschitz bound $L_i$ for its gradient. Let $F=\sum_i f_i/n$ and $X_*=\arg\min F$. Some $z\in X_*$ satisfies $\|x_0-z\|\le R$. At every point,
$$
F(x)-F^*\ge \frac{\mu}{2}\operatorname{dist}(x,X_*)^2,\qquad
\frac1n\sum_i\|\nabla f_i(x)\|^2\le\rho\|\nabla F(x)\|^2,\qquad \rho\ge1 .
$$
The second inequality is on local **mean** gradients. Each worker supplies jointly measurable, unbiased gradients with centered second moment at most $\sigma^2$. Samples are IID within workers and independent across workers under the specified joint law. The setup reuses the aggregate strong-growth specification with the derived smoothness bound $\max(\mu,\max_i L_i)$, which is valid by the triangle inequality. Local smoothness caps can come from the loss and the local design matrix, as in smooth generalized linear models. The quantitative information they supply matters even though convexity and aggregate smoothness already imply a coarse local bound of order $nL$ for an $L$-smooth average. [Setup](../Setups/DistributedLocallySmoothGrowth.lean) · [Aggregate model](../Setups/DistributedMeanStrongGrowth.lean) · [Aggregate-to-component smoothness](../Proofs/DistributedGrowthGeometry.lean)

For example, take nonorthogonal unit vectors $v,w$ and $F(x)=\mu\|x\|^2/2+\mu\log\cosh(v^\top x)+\mu\log\cosh(w^\top x)$. On an even number of workers, give half the loss $2F$ and half zero. The average is $F$, the growth factor is two, and every local gradient is $6\mu$-Lipschitz. Active workers have interacting coordinates and an $x$-dependent Hessian. Inactive workers have every point as a minimizer. Independent centered perturbations of bounded second moment realize the stochastic oracle.

Each physical worker takes $h_i>0$ time per raw gradient and serves one at a time. Distinct workers and directed star links operate concurrently. Each link serves one packet at a time, with latency $\ell$ and cost $b$ per bit, including a 64-bit clock. Workers form batches, scale and clip their local means, and send a quantized vector. The coordinator broadcasts an encoded aggregate after each update. If $P$ is the number of updates in each of the two phases, the returned point is the coordinator's stored iterate after $2P$ updates. Its expected squared distance to $X_*$ is at most $\varepsilon$. The physical protocol runs $2P+1$ rounds. The deadline includes all their raw samples and both message directions, and the proof establishes finite execution at every earlier deadline as well. [Algorithm and output](../Algorithms/LocallySmoothGrowthSgd.lean) · [Physical execution](../Proofs/WeightedInterpolationExecution.lean)

## Deadline and proof

The shared worker profile $u$ minimizes $\sum_i u_i^2/h_i$ over signed vectors with $\sum_i u_i=n$ and $\sum_i u_i^2\le n\rho$. Its entries are positive and the public budget computes it using a scalar threshold. Put
$$
a_i=\mu u_i,\quad I=\sum_i a_i^2/h_i,\quad S=\sum_i h_i^{-1},
\quad U=\max_i a_i,\quad H=\max_i h_i.
$$
The new calibration and the resulting deadline, up to universal constant factors, are
$$
M=\max_i a_i\max(a_i,L_i),\quad A=2SM/I,\quad \Gamma=\sigma U/M,
$$
$$
T=O\!\left(\frac{\sigma^2}{I\varepsilon}
+A[1+\log(1+R^2/\varepsilon)]
 \left[H+\ell+b\left(64+d\log\left(4+d+A+
 (R^2+\Gamma^2)/\varepsilon\right)\right)\right]\right).
$$
The schedule retains the full statistical coefficient without a logarithm in accuracy. A smaller $M$ reduces the round factor $A$ and can increase the packet width through $\Gamma$. The formula accounts for both effects. If the supplied $L_i$ are loose while a sharper aggregate $L$ is available, the earlier deadline can be preferable. [Public Lean budget](DistributedLocallySmoothGrowth.lean) · [Earlier budget with aggregate smoothness](DistributedGradientDiversity.lean)

The signed-profile support inequality and the growth it transfers to the surrogate $\sum_i(a_i/h_i)f_i$ are from the earlier strong-growth result. At any global minimizer $z$, relative growth forces every local gradient to vanish. Thus $\|\nabla f_i(x)\|\le L_i\|x-z\|$. Multiplying by the individual signal $a_i$ gives the clipping bound $a_iL_i\le M$. The same inequality bounds the smoothness of the actual update by $\sum_i a_i L_i/h_i\le SM$. Finally $a_i^2\le M$ makes the calibrated schedule realize precisely the prescribed coefficients $a_i/h_i$. These three inequalities justify changing the scale while using the existing finite-bit convergence and execution proofs. [Local clipping and descent bounds](../Proofs/LocallySmoothGrowth.lean) · [Worker profile](../Proofs/StrongGrowthWeights.lean) · [Surrogate growth](../Proofs/DistributedGrowthGeometry.lean)

## What improves

First take $n=4m$, with $3m$ workers of service time one and $m$ of service time $n$. Set $\rho=2$, $L_i=4\mu$, $\varepsilon=n^{-3/2}$, and hold the other positive parameters and dimension fixed. By Cauchy–Schwarz the slow group has signal mass at most $n/\sqrt2$. Symmetry within each group gives $\max_i u_i\le4$, and the positive fast-group mass gives $I=\Theta(n)$ at fixed $\mu$. The new $A$ stays bounded. The three full deadlines are $\Theta(n\log n)$ here, $\Theta(n^{3/2}\log n)$ for gradient diversity, and $\Theta(n^2\log n)$ for the original strong-growth schedule with constant aggregate smoothness. This compares schedules on all workers. For this example alone an even faster reduction exists: the fast mean's gradient differs from the global gradient by at most $\|\nabla F\|/\sqrt3$ by centering the RMS bound. Its alignment gives quadratic growth with factor at least $(1-1/\sqrt3)\mu$ and the same solution set. The weak-interpolation protocol on these fast workers then takes $O(\sqrt n+\log^2 n)$ time. [Gradient-diversity deadline](DistributedGradientDiversity.lean) · [Original deadline](DistributedStrongGrowthTime.lean) · [Gap comparison from alignment](../Proofs/DistributedGrowthComparison.lean) · [Weak interpolation](DistributedWeightedInterpolation.md)

For a many-speed example, let $n=2m$. Give $m$ workers service time $m^{3/4}$ and the others times $1,\ldots,m$. Set $\rho=2$, $L_i=8\mu$, $\varepsilon=m^{-4/3}$, and again fix the other positive parameters and dimension. Here $H=m$, $S=\Theta(m^{1/4})$, $U=\Theta(\mu)$, and $J=I/\mu^2=\Theta(\log m)$. To see the bound on $U$, each worker with service time at least $H/2$ has at least half the largest signal by the scalar profile formula. There are at least $m/2$ such workers and the total signal is $2m$.

For the information bound, the feasible signal zero on the constant-time group and two on the ramp gives $J\le4\sum_{j\le m}1/j$. For a matching lower estimate let $K=m^{15/16}$ and give weight $c=1/K$ to each worker of the first group and $w_j=1/\max(K,j)$ on the ramp. Write $r=\sum_j w_j=\Theta(\log m)$ and $s=\sum_j w_j^2\le cr$. For the combined weight vector $w$, every feasible signal $v$ satisfies
$$
w^\top v\ge mc+r-\sqrt{m^2c^2+2ms-2mcr-r^2}\ge 2r-s/c\ge r .
$$
The first inequality centers $v$ around the all-ones vector and applies Cauchy–Schwarz there. The second uses the tangent upper bound for the square root at $m^2c^2$. Since $\sum_i h_i w_i^2=O(\log m)$, weighted Cauchy–Schwarz gives $J=\Omega(\log m)$.

Now $M=\Theta(1)$ and $A=\Theta(m^{1/4}/\log m)$. The transient costs $\Theta(m^{5/4})$, so the full deadline is $\Theta(m^{4/3}/\log m)$. For the Gaussian benchmark take $d\ge1$, a real-valued sample space with Gaussian draws, $\sigma>0$, and $R\ge2\sqrt\varepsilon$ (eventually true for fixed $R>0$). The earlier strong-growth testing construction fits the local caps since $U\le8\mu$, and yields the same leading statistical order. The gradient-diversity budget on the original workers still incurs at least order $m^{7/4}$ from its transient. Its calibration includes $L U\min(n,1+\sqrt{n(\rho-1)})$. For the weak-interpolation budget alone, a feasible curvature profile concentrates $4\mu$ on the slowest half of the ramp (take even $m$) and zero elsewhere, giving only $O(\mu^2)$ information. That budget has statistical cost $\Omega(m^{4/3})$. The comparisons and Gaussian benchmark are calculations in this note. The Lean result proves the all-parameter upper bound. [Statistical benchmark](DistributedStrongGrowthTime.md) · [Weak-interpolation profile](DistributedWeightedInterpolation.lean)

The logarithmic gain over uniform subsets in this example also survives optimizing the subset. A subset of size at most $m$ can have zero signal. In a subset of size $m+j$, assign zero to $m$ selected workers and two to every other worker. The resulting feasible signal has selected mass $2j$. At least $j$ selected workers belong to the ramp, so their service-time sum is at least $j(j+1)/2$. A uniformly weighted average, even with optimized batch counts, has squared signal per unit noise bounded by a constant.

## Limits of the comparison

The improvement concerns a single finite-bit schedule in the physical star, with a formula valid for all input profiles. Known theorems can recover some of these gains by changing the oracles. For example, in the many-speed family above one can apply weak interpolation to the scaled losses $w_i f_i$. The support estimate gives their mean quadratic growth at least $\mu r/n$. With $B=m^2/\log m$, each virtual sample can average $\lceil B w_i^2\rceil$ raw samples on its physical worker, giving a common variance bound $\sigma^2/B$. Pad the virtual service times to $t_i=\max(m/\log m,h_i\lceil B w_i^2\rceil)$. Then $\sum t_i=\Theta(m^2)$, $\max t_i=O(m^{17/16})$ and $\sum 1/t_i=O(\log m)$. Supplying smoothness caps $\max(w_i L_i,c't_i)$ with $c'=\mu r/\sum t_i$ makes the weak profile exactly $c't_i$. Substitution gives the same statistical order, with a transient of order $m^{19/16}$ up to logarithmic factors. Thus this instance demonstrates an earlier transition to statistical time for the public schedules; it does not establish a new problem-class lower bound.

More generally, replicating a worker into virtual workers can reproduce weighted computation through serial local sampling. Their finite-bit replies must share the physical outgoing link. For $k$ equally weighted replicas on a common quantization grid, forwarding the exact sum of their codes can require up to $\lceil\log_2 k\rceil$ additional bits per coordinate. The theorem controls a physical worker's aggregate before transmission and pays for one quantized vector per direction per round. Optimal transient and communication costs for arbitrary algorithms remain open. Tyurin’s question about the arithmetic-time obstruction under pure relative growth was already addressed by the statistical profile result. [Tyurin, Remark 2.4 and Theorems 3.8 and F.2](https://arxiv.org/html/2609.17483v1) · [Earlier strong-growth contribution](DistributedStrongGrowthTime.md)
