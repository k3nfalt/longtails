# Expected residual for noisy nonexpansive maps on a cube

Let $T$ map $[-R,R]^d$ into itself and be nonexpansive in the sup norm. A query at $x$ returns the full vector $T(x)+Z$, with fresh IID noise satisfying $\mathbb E Z=0$ and $\mathbb E\|Z\|_\infty^2\le\sigma^2$. The coordinates may be dependent. Samples may be unbounded and replies may leave the cube. The algorithm returns a point $X$ in the cube with $\mathbb E\|T(X)-X\|_\infty\le\varepsilon$. The dimension, radius, second-moment bound and tolerance are public. [Setup](../Setups/AdditiveCubeFixedPoint.lean) · [Theorem](AdditiveCubeFixedPoint.lean)

For a nonlinear example, take transition vectors $P_{ia}$ and rewards $r_{ia}$ and define $T_i(x)$ by clipping $\max_a(r_{ia}+\sum_j P_{ia,j}x_j)$ to $[-R,R]$. Each transition vector has nonnegative entries summing to one. Averages, finite maxima and coordinate clipping preserve the sup-norm Lipschitz bound, including when the maximizing action changes with the point. One observation model for this example is a full update followed by vector-valued measurement error. Sampling a transition inside the maximum can have a different mean and noise law. The companion hardness theorem covers the general nonexpansive class. [Diakonikolas, Guzmán, and Martínez-Rubio, Sections 1–2](https://arxiv.org/pdf/2609.09524v1)

## Guarantee and comparison

Write $t=R/\varepsilon$ and $u=\sigma/\varepsilon$. For $t\le1$, the center of the cube already meets the target without a query. For $t>1$ the public budget is

$$
\left\lceil4096\,t\left(1+2097152\log(2d)\,u^2\right)\right\rceil.
$$

One observation at one point costs one call. The count includes every member of every batch and any padding after the final iterate is saved. The guarantee holds in every positive finite dimension. Its order agrees with Lee's Theorem 3 for stochastic dual Halpern iteration. Applying Lee to $x\mapsto T(\operatorname{clip}(x))$ and clipping the output gives the cube result. Diakonikolas, Guzmán, and Martínez-Rubio's Theorem 5 previously gave a recursively anchored algorithm with additional logarithms. Both works cited here are arXiv preprints. [Lee, Theorems 2–3](https://arxiv.org/pdf/2610.26484v1) · [Diakonikolas, Guzmán, and Martínez-Rubio, Theorem 5](https://arxiv.org/pdf/2609.09524v1)

The new complexity result in the pair is the lower bound for fresh additive isotropic Gaussian errors against adaptive randomized algorithms. Both statements target the same expected residual and count full-vector observations. The lower theorem requires $t\ge128$ and $d\ge\lceil t\rceil$. At $R=\sigma=1$, $d=\lceil1/\varepsilon\rceil$, the lower bound grows as $\Omega(\varepsilon^{-3}/\log^2(1/\varepsilon))$. The upper bound is $O(\varepsilon^{-3}\log(1/\varepsilon))$ for the general additive class there. Gaussian averaging gives $O(\varepsilon^{-3})$ on the Gaussian subclass. Closing these logarithmic gaps remains open in this analysis. [Companion theorem, prior lower bounds and paired observations](AdditiveCubeFixedPointLowerBound.md)

## Algorithm and proof

Write $F=T\circ\operatorname{clip}$. Start from $x=b=0$ and choose $M$ as the smallest power of eight, starting at one, at least $\lceil32t\rceil$. At strength $a=1/M$, perform $6M$ updates $x\leftarrow(b+\overline Y)/(1+a)$, where $\overline Y$ is a fresh batch mean at $\operatorname{clip}(x)$. The initial batch size is $\max\{1,\lceil2097152\log(2d)u^2\rceil\}$. At each phase boundary add $7ax$ to $b$. Between phases divide $M$ by eight and quadruple the batch size. After the phase with $M=1$, return the clipped last iterate. The number of calls per phase halves. [Algorithm](../Algorithms/AdditiveCubeAnchoring.lean) · [Template execution and exact counts](../Proofs/AdditiveCubeAnchoringExecution.lean)

For a fixed anchor let $v$ solve $(1+a)v=F(v)+b$. The noiseless inner iteration contracts by $1/(1+a)$, so a phase reduces its initial error to at most $1/64$ of its starting value. If $z$ ends that phase, increasing the strength to $8a$ moves the root by at most $7\|z-v\|_\infty/8$ and increases its unregularized residual by at most $14a\|z-v\|_\infty$. The next phase starts at $z$. These estimates give a pathwise residual bound involving the sum of batch error norms, weighted by $1/M$ in each phase. [Root movement and residual proof](../Proofs/AdditiveCubeAnchoringRate.lean)

For a batch of size $n$, its expected sup-norm error is at most $\tau$ if $n\tau^2\ge8\log(2d)\sigma^2$. The proof uses a log-sum-exp potential on signed coordinates. Centering removes its linear expected increment, and the second moment controls the remainder. Quadrupling the batch size halves the error tolerance. Summing the tolerances across phases bounds the expected residual directly. [Batch inequality](../Proofs/AdditiveFixedPointBatch.lean) · [Expected residual and budget](../Proofs/AdditiveCubeAnchoringAccuracy.lean)
