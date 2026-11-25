# Stopped model flow with a reused Hessian

For a globally $C^3$ objective in a finite-dimensional real inner-product space, suppose
\[
 \|D^3 f(x)\|\le L_0+L_1\|\nabla f(x)\|,\qquad
 f(x_0)-f(x)\le\Delta,\qquad \|\nabla f(x_0)\|\le G_0 .
\]
Here $L_0,\Delta,\varepsilon>0$, $L_1,G_0\ge0$, and the public block length $m\ge1$ is an integer.
The two exact oracles separately return a gradient and a full Hessian. The output satisfies
$\|\nabla f(x_{\rm out})\|\le\varepsilon$ for every seed. [Setup](../Setups/GradientDependentHessian.lean) · [Theorem](HessianReuseModelFlow.lean)

Let $A=L_0+L_1\varepsilon$, $S=\Delta\sqrt A/(\varepsilon\sqrt\varepsilon)$, and
$C=9/(2\sqrt2)$. To compare the budgets, write $u=\Delta\sqrt{L_0}/\varepsilon^{3/2}$,
$w=\Delta\sqrt{L_1}/\varepsilon$, and
$k=\lceil\log(1+L_1G_0/(mL_0))/\log(4/3)\rceil$. Then $S=\sqrt{u^2+w^2}$.

| Method | Gradient calls | Hessian calls |
|---|---|---|
| Energy-controlled reuse | $k+\lceil\sqrt m(27000u+15000w)\rceil+m+74$ | $k+\lceil(54000u+30000w)/\sqrt m\rceil+146$ |
| Stopped model flow | $\lfloor C\sqrt m S\rfloor+1$ | $\lfloor CS/\sqrt m\rfloor+1$ |

The leading powers of accuracy and block length agree. The smaller constants apply throughout the setup.
Both channels lose the initialization logarithm, and each additive allowance becomes one call.
With $L_1>0$ and the other parameters fixed, increasing the public initial-gradient allowance now leaves both budgets fixed.
The older algorithm uses fresh preparatory steps to control its cubic regularization parameter. [Previous guarantee and analysis](EnergyHessianReuse.md)

## Step and certificate

Set $b=2\varepsilon/9$, $q=7\varepsilon/9$, $r=\sqrt{b/(mA)}$, and $h=qr$.
At each active step read $g=\nabla f(x)$. A gradient of norm at most $\varepsilon$ certifies $x$.
Use the Hessian $B$ from the start of the current block to compute
\[
 v(t)=e^{-tB}g,\quad y(t)=x-\int_0^t v(s)\,ds,\quad U(t)=\int_0^t\|v(s)\|^2\,ds .
\]
Stop at the first speed hit $\|v\|=q$ or energy hit $U=h$. A speed hit certifies the endpoint,
including a simultaneous hit. Otherwise take the endpoint as the next iterate. Before either hit,
speed is at least $q$, so a hit occurs by $h/q^2$. Each prefix has length $\ell\le U/q\le r$.
[Algorithm](../Algorithms/HessianReuseModelFlow.lean) · [Stopping proof](../Proofs/HessianReuseModelFlowPath.lean)

After $j<m$ segments of a block, assume the Hessian error at the start of the next segment is at most $jrA$.
This holds with $j=0$ at every refresh. Let $D$ be the maximum of $\|e\|$ on the stopped segment,
where $e=\nabla f(y)-v$. Integration of the third-derivative bound gives a Hessian error throughout of at most
\[
 M=jrA+(L_0+L_1D)r+L_1h=(j+1)rA+L_1r(D-b).
\]
Since $e(0)=0$ and $e'=-(\nabla^2 f(y)-B)v$, we have $\|e(t)\|\le M\ell(t)$.
Thus $D-b\le L_1r^2(D-b)$, using $mr^2 A=b$. The coefficient is at most $2/9$, so $D\le b$.
Consequently $M\le(j+1)rA\le b/r$, which propagates the block invariant and gives the speed-hit certificate $q+b=\varepsilon$.

The objective decrease is at least $U-M\ell^2/2$, since $\ell'=\|v\|$.
Each continuing step spends energy $h$ and decreases the objective by at least
$d=(q-b/2)r=(2\sqrt2/9)\varepsilon^{3/2}/\sqrt{mA}$. The gap allows at most
$K=\lfloor\Delta/d\rfloor$ continuations. The fixed execution schedules steps $0,\ldots,K$,
including the final gradient check and a Hessian at each multiple of $m$. Once certified, the output is retained.
All scheduled calls, including padding and the final block-boundary Hessian when $m\mid K$, cost exactly
$K+1$ gradients and $\lfloor K/m\rfloor+1$ Hessians. [Descent proof](../Proofs/HessianReuseModelFlowDescent.lean) · [Execution proof](../Proofs/HessianReuseModelFlowExecution.lean)

## Prior work and limitations

Fang, Marumo and Takeda use the same pointwise condition in Assumption 1(a). Their parameter-free cubic Newton method also controls negative curvature. Corollary 1, Eq. (130), has first-order terms of order $u+w$ and includes $k_0$. Eq. (105) defines that index using the logarithm of a ratio whose numerator is $\max\{\sigma_{\rm init},4L_1\|\nabla f(x_0)\|\}$. Thus their guarantee retains logarithmic initialization dependence when $L_1>0$. [Primary manuscript, v1](https://arxiv.org/html/2607.10741v1)

Doikov, Chayti and Jaggi reuse a Hessian across fresh gradients in a cubic-regularized method and obtain the square-root reuse factor with a uniform Hessian Lipschitz constant. Filho and Gonçalves allow adaptive reuse of approximate Hessians under uniform Hessian Lipschitzness. Blockwise stabilized ARC also assumes Lipschitz Hessians in Assumption 2.1. [Lazy Hessians](https://proceedings.mlr.press/v202/doikov23a.html) · [Adaptive reuse](https://optimization-online.org/wp-content/uploads/2026/05/Vilmar_e_Max-28-1.pdf) · [Blockwise stabilized ARC](https://arxiv.org/html/2608.22129v3)

Charge one full Hessian as $m$ gradients and call $N_g+mN_H$ the weighted cost. When a global Hessian Lipschitz constant $H$ is available, Chen, Liu, Luo and Zhang's Theorem 4.1, with the reuse period matched to that price, gives a weighted cost with leading term proportional to $m^{1/3}\Delta\sqrt H/\varepsilon^{3/2}$. For $L_1=0$ and the common bound $H=L_0$, the present weighted cost has a larger leading factor by $m^{1/6}$. For general $L_1$, the leading-term comparison favors model flow when $H\gg m^{1/3} A$, as in the earlier repository note. [Theorem 4.1 and cost model](https://arxiv.org/html/2501.17488v3) · [Repository comparison](EnergyHessianReuse.md)

The quadratic-model flow itself is classical. Behrman's dissertation gives the displacement equation $z'=-g-Bz$ in Eq. (1.3). Here its speed and energy supply stopping criteria for a stale Hessian. [Behrman, 1998, Chapter 1](https://web.stanford.edu/~behrman/publications/1998/egf.pdf)

The result uses known $L_0,L_1,\varepsilon$, and its fixed horizon also uses the public gap bound $\Delta$ and block length $m$; it does not read $G_0$. It treats exact exponentiation, integration and first-hit selection as free internal computation. It bounds first-order stationarity only. The sharp constant and optimal two-channel trade-off remain open. The repository supplies no lower bound for that trade-off. The improvement claimed here is relative to the explicit comparisons above.
