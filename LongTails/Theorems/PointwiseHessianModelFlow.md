# First-order stationarity from a stopped quadratic-model flow

For the joint value, gradient and Hessian oracle, the call budget is
\[
  \left\lfloor\frac{32}{3}
    \frac{\Delta\sqrt{L_0+L_1\varepsilon}}{\varepsilon\sqrt{\varepsilon}}
  \right\rfloor+1.
\]
The public theorem uses the same setup as the previous upper and lower bounds. It removes the previous upper bound's additive logarithm in the initial gradient allowance \(G\). The supporting estimates apply in every finite dimension with the validity conditions of `broadSpec`, including \(L_0=0\) and \(L_1=0\) separately. The high-dimensional lower bound in the public regime thus matches the order of the upper bound. [Theorem](PointwiseHessianModelFlow.lean) · [Setup](../Setups/PointwiseHessianStationarity.lean) · [Previous upper bound](PointwiseHessianStationarity.md) · [Lower bound and its regime](PointwiseHessianStationarityLowerBound.md)

## The step

Set \(A=L_0+L_1\varepsilon\), \(r=\sqrt{\varepsilon}/(4\sqrt A)\), and \(h=\varepsilon r/2\). At a point \(x\), one call supplies \(g=\nabla f(x)\) and \(H=D\nabla f(x)\). If \(\|g\|\le\varepsilon\), return \(x\). Otherwise compute
\[
  v(t)=\exp(-tH)g,\qquad z(t)=-\int_0^t v(s)\,ds,\qquad
  U(t)=\int_0^t\|v(s)\|^2\,ds .
\]
The identities \(z'=-v\), \(v'=-Hv\) and \(v(0)=g\) give \(v(t)=g+Hz(t)\). Stop at the first zero of \(\min\{\|v(t)\|-\varepsilon/2,h-U(t)\}\) on \(t\ge0\). Continuity gives such a zero by time \(h/(\varepsilon/2)^2\), since each unit of ordinary time before the threshold accumulates at least \((\varepsilon/2)^2\) energy. A threshold hit certifies \(x+z(t)\) as the output, including a simultaneous hit. An energy-only hit makes \(x+z(t)\) the next query. Exponentiation, integration and first-zero selection use only the reply and public scalars, as permitted by the exact-real oracle model. [Algorithm](../Algorithms/PointwiseHessianModelFlow.lean) · [Path and stopping proof](../Proofs/HessianModelFlowPath.lean)

## Why the bound is independent of the initial gradient

Until the stop, the model gradient has norm at least \(\varepsilon/2\). Hence the path length \(\ell(t)=\int_0^t\|v\|\) is at most \(2U(t)/\varepsilon\le r\). Let \(E\) be the maximum of \(\|\nabla f(x+z)-v\|\) on the stopped path. The third-derivative assumption bounds the variation of the Hessian by \((L_0+L_1 E)\ell(t)+L_1 U(t)\). Integrating the Hessian error against speed then bounds \(E\) by \(((L_0+L_1 E)r+L_1h)r\). Here \(Ar^2=\varepsilon/16\) and \(L_1r^2\le1/16\), so \(E\le\varepsilon/15\). At the model threshold this gives \(\|\nabla f(x+z)\|\le\varepsilon/2+\varepsilon/15\le\varepsilon\) without a validation query. Writing \(e=\nabla f(x+z)-v\), one has
\[
  \frac{d}{dt}f(x+z)=-\|v\|^2-\langle e,v\rangle
        \le -\tfrac34\|v\|^2 .
\]
Every continuing step therefore spends \(h\) of model energy and decreases the objective by at least \(3h/4\). [Gradient error and descent](../Proofs/HessianModelFlowDescent.lean)

After \(k\) continuing steps the global gap gives \(k(3h/4)\le\Delta\). The next call after \(\lfloor4\Delta/(3h)\rfloor\) continuing steps must certify an output. The fixed-budget execution stores each certified point in an absorbing state and directs any padding queries to zero. It returns the same point for every seed of an admissible exact oracle, which gives measurability, integrability and the required expected gradient-norm bound. [Execution and budget proof](../Proofs/HessianModelFlowExecution.lean)

## Relation to prior work and limitations

The closest upper comparison is [Fang, Marumo and Takeda, arXiv:2607.10741v1](https://arxiv.org/html/2607.10741v1). Their Assumption 1(a) is the same pointwise third-derivative bound with \(L_0>0\). By their Corollary 1, Eq. (130), a parameter-free cubic-regularized Newton method finds an \((\varepsilon,\delta)\)-second-order stationary point within
\[
  O\!\left(\Delta\left(\frac{\sqrt{L_0}}{\varepsilon^{3/2}}+\frac{\sqrt{L_1}}{\varepsilon}
      +\frac{L_0^2}{\delta^3}+\frac{L_1}{\delta}\right)+k_0
      +\left[\log\frac{L_0+L_1^{3/2}\Delta}{\sigma_{\rm init}}\right]_+\right)
\]
oracle calls, where \(k_0=\max\{1,\lceil\log_2(\max\{\sigma_{\rm init},4L_1\|\nabla f(x_0)\|\}/(L_0+L_1^{3/2}\Delta))\rceil\}\) by their Eq. (105). The first-order polynomial terms agree with \(S=\Delta\sqrt{L_0+L_1\varepsilon}/\varepsilon^{3/2}\), since \(\sqrt{L_0+L_1\varepsilon}/\varepsilon^{3/2}\) has the order of \(\sqrt{L_0}/\varepsilon^{3/2}+\sqrt{L_1}/\varepsilon\). For \(L_1>0\) the term \(k_0\) grows logarithmically with the initial gradient norm, as the previous repository bound does through \(G\). The budget here stays fixed as \(G\) grows with the other parameters fixed. Their method needs no knowledge of \(L_0\) and \(L_1\) and also controls negative curvature. The method here uses the public \(L_0\), \(L_1\) and \(\varepsilon\) in its step and certifies first-order stationarity only.

For \(L_1=0\) the assumption is Lipschitz continuity of the Hessian, and cubic regularization ([Nesterov and Polyak, 2006](https://doi.org/10.1007/s10107-006-0706-8)) already gives \(O(1+\Delta\sqrt{L_0}/\varepsilon^{3/2})\) calls with no dependence on the initial gradient. The contribution concerns \(L_1>0\).

The path itself is classical. Following the gradient flow of the local quadratic model, \(z'=-g-Hz\), through its closed-form solution goes back to the differential-equation methods reviewed in [Behrman's dissertation (1998), Eq. (1.3)](https://web.stanford.edu/~behrman/publications/1998/egf.pdf). The oracle bound here rests on the stopping rule: the energy cap \(h\), the model-gradient threshold \(\varepsilon/2\), and the proof that a threshold-hit endpoint is certified stationary without a further call.

Limitations. The constant \(32/3\) is not claimed to be sharp, and the lower bound's constant \(2^{-39}\) leaves a constant-factor gap. The order match holds in the public regime shared with the lower bound, \(G\ge16\varepsilon\), \(S\ge2^{39}\) and \(d\ge2^{140}(1+\lceil S\rceil)^4\); no optimality in fixed dimension is claimed. The matrix exponential, the integrals and the first-zero selection are exact internal computations, and no finite-precision implementation or running-time bound is given. A brief search found no earlier bound of order \(1+S\) joint calls independent of the initial gradient for the full pointwise class with \(L_1>0\); priority beyond the comparisons above is not claimed.
