# BirchCollections

Birch SGD represents a stochastic-gradient update as a tree edge with a base point, a query point, and a reply. BirchCollections extends that representation to batches, retained gradient estimators, and overlapping private histories. A common descent theorem recovers Birch Theorem 2.4 in Euclidean geometry and analyzes native sharp-step methods in regular norm geometry. [Birch SGD, Algorithm 1 and Theorem 2.4](https://arxiv.org/html/2505.09218v3)

## Where to start

| Question | Lean entry point |
| --- | --- |
| What problems and algorithms are covered? | [Collection setup](../Setups/BirchCollections.lean) and [trace compiler](../Setups/BirchCollectionExecutionModel.lean) |
| What theorem do the analyses share? | [Common descent theorem](../Proofs/BirchTraceDescent.lean) and [native convergence result](BirchCollections.lean) |
| How is the original Birch theorem recovered? | [Tree-to-trace reduction](../Proofs/BirchCollectionEuclideanTrace.lean), [Euclidean recovery](../Proofs/BirchCollectionEuclidean.lean), and [Birch convergence proof](../Proofs/BirchSgdConvergence.lean) |
| Where are the new algorithms and their time bounds? | [Routed Pipeline Local](BirchRoutedTime.lean), [Power-Capped Packet Local](BirchPowerTime.lean), [Euclidean companions](../Proofs/BirchResourceTimedTrace.lean), and [matching lower bounds](../Proofs/BirchResourceMatchingLower.lean) |

## Objective, algorithm, and theorem

We minimize a differentiable, lower-bounded, possibly nonconvex function \(f\) with initial gap at most \(\Delta\). In the native setting, the gradient is \(L\)-Lipschitz from a continuous norm \(N\) to its dual \(N_*\). A jointly measurable IID stochastic gradient is unbiased and has dual variance bounded by \(\sigma^2\). The dual space has a regularity witness with coefficient \(\kappa\). The goal is \(\mathbb E[N_*(\nabla f(X))^2]\le\varepsilon\).

A worker captures a saved state \((x,m)\), gathers a collection of replies at \(x\), and can compute
\[
m'=(1-\beta)m+\beta\bar g,\qquad
x'=x+\frac{w}{20L}\operatorname{sharp}_N(m'),\qquad
\operatorname{sharp}_N(v)=N_*(v)\arg\min_{N(s)\le 1}\langle v,s\rangle .
\]
States are immutable. To merge two histories, the trace adds their states and subtracts their certified common history. This counts each displacement once. The trace distinguishes issued, accepted, discarded, and pending work, and explicitly marks the points eligible for output.

The common theorem sums per-publication descent inequalities. A nonnegative matrix bounds how earlier movements contribute to current estimation error. A weighted column bound lets the accumulated error be absorbed by descent. In the native application, the event, sampling, and retained-estimator proofs establish these inequalities from the structural certificate. The public result gives expected squared dual stationarity at a uniform marked publication and counts every raw oracle call. [Retained energy estimate](../Proofs/BirchRetainedEnergy.lean) · [Oracle execution and success](../Proofs/BirchCollectionSuccess.lean)

For a Euclidean Birch tree, the translation preserves update bases, query points, cached reply identities, the original independence premise, and the main branch. Birch's tree-distance estimate supplies a different certificate to the same descent theorem. The original first-\(K\) average follows with its original threshold
\[
K\ \ge\ \frac{4(R+1)L\Delta}{\varepsilon}
        +\frac{8\sigma^2L\Delta}{\varepsilon^2}.
\]
The noise term has no \(R\) factor. The Lean template's uniform branch output and exact execution count are checked separately. [Euclidean recovery](../Proofs/BirchCollectionEuclidean.lean)

## Method coverage

Original Euclidean tree analyses fall under the recovered Birch theorem. The table shows the separate native realizations, whose sharp updates and retained estimators can differ from those of the Euclidean originals.

| Birch family | Native construction |
| --- | --- |
| Vanilla | [Batch and take one sharp step at the current point](../Proofs/BirchCollectionVanilla.lean) |
| Rennala | [Collect the current-round quota and charge stale replies through stop-and-drain](../Proofs/BirchCollectionRennala.lean) |
| Ringmaster | [Apply a sharp displacement from a saved point subject to an age gate](../Proofs/BirchCollectionDelayed.lean) |
| Local | [Publish completed private prefixes at the common quota](../Proofs/BirchCollectionLocal.lean) |
| Cycle | [Rotate publishing groups while the other branches continue](../Proofs/BirchCollectionCycle.lean) |
| Async-Local | [Merge moving blocks under an age-times-size gate](../Proofs/BirchCollectionAsyncLocal.lean) |
| Async-Batch | [Apply one sharp direction to a batch at a saved point under the same gate](../Proofs/BirchCollectionAsyncBatch.lean) |
| Local-Async | [Apply arrivals within each group and publish at the outer completed quota](../Proofs/BirchCollectionLocalAsync.lean) |
| Nested Local-Async | [Merge at each tier and export completed prefixes of unfinished cluster rounds, following Remark E.9](../Proofs/BirchCollectionNested.lean) |
| Meta Local | [Allow soft synchronization with a hard cap on accumulated work and age](../Proofs/BirchCollectionMeta.lean) |
| Dual-Process | [Capture immutable send prefixes and publish acknowledged work at an equality-hit quota](../Proofs/BirchCollectionDualPool.lean) |

Two further examples are the [variable-quota retained hierarchy](../Proofs/BirchCollectionRetainedQuota.lean), which keeps full raw work under overlapping histories, and [rolling-window sharp](BirchWindow.lean), which reuses cached replies and pays exactly \(B+K-1\) calls for a window of size \(B\) and \(K\) updates. The earlier [protocol framework](BirchNonEuclideanFramework.lean) and [recursive composition result](BirchNonEuclideanComposition.lean) are included as distinct verified entry points.

## Two resource models

Let \(A=L\Delta/\varepsilon\), \(b_0=1+\sigma^2/\varepsilon\), and \(\Phi_u(b)=\inf_{t:R_u(t)>0}(t+b/R_u(t))\). The oracle clock counts service time with free coordination, arithmetic, and sharp operations.

| Model and controller | Matching complexity |
| --- | --- |
| **Routed Pipeline Local.** A job freezes its point, visits a compatible sequence of exclusive devices, and exposes a reply at the final stage. Assign a quota using feasible fractional route rates and pack jobs without intermediate waits. Here \(R(t)\) is the feasible aggregate route rate at latency cutoff \(t\); omit \(u\). | Time \(\Theta_J(A\Phi(b_0))\) at fixed maximum route depth \(J\), with \(O(Ab_0)\) paid work. The lower bound includes buffered schedules. |
| **Power-Capped Packet Local.** A mode fixes a packet's duration, draw, and size. Its replies share a frozen point and arrive together. Choose a power-feasible configuration and charge every sample in each selected packet. Here \(R_u(t)\) is the maximum simultaneous rate among configurations with duration cutoff \(t\) and packet-size cutoff \(u\). | Unrestricted time \(\Theta(A\Phi_\infty(b_0))\). At cutoff \(u\), time \(O(A\Phi_u(b_0))\) with work \(O(A(b_0+u))\). A pathwise work cap \(W\) gives lower time \(\Omega(A\Phi_{\lfloor CW/A\rfloor}(b_0))\) for a numerical constant \(C\). The frontier matches up to constant work dilation. |

In each model the Euclidean companion gives one private edge and one virtual main edge to each paid accepted reply, with distance at most quota minus one. The native controller instead uses retained sharp steps, one per accepted job or packet, and exact history merges. Both use the common descent theorem. [Schedule bounds and tuning](../Proofs/BirchResourceComplexity.lean) · [Native timed instantiation](../Proofs/BirchResourceNativeTimed.lean)

The time comparisons fix geometry regularity and use zero-respecting policies in the stated accuracy regime. The checked lower instance applies in Euclidean geometry and for the axial norm \(N(x)=\|x\|_2+|x_i|\), with \(\kappa=4\). Lean checks legal repeated schedules, exact serial replay, and lower bounds for finite predictable completion ledgers. Extending the lower to arbitrary randomized stopping uses a separate truncation argument. Frozen minibatching on the same schedulers reaches the same worst-case upper orders. The power result characterizes a resource trade-off, and the routed result demonstrates that private updates fit the common analysis at the optimal fixed-depth order.

## Reproduce the checks

From the repository root with the pinned Lean toolchain:

~~~sh
lake build $(awk '/^import LongTails[.]/ {print $2}' scripts/VerifyBirchCollections*.lean | sort -u)
lake env lean scripts/VerifyBirchCollections.lean
lake env lean scripts/VerifyBirchCollectionsDependencies.lean
~~~
