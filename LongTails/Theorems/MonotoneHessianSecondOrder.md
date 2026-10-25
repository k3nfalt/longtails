# Sparse Hessian queries for same-point second-order stationarity

The [theorem](MonotoneHessianSecondOrder.lean) constructs the [monotone Hessian-reuse algorithm](../Algorithms/MonotoneHessianReuse.lean) for the [Hessian-Lipschitz second-order specification](../Setups/HessianLipschitzSecondOrder.lean). The contribution is a weighted oracle-complexity guarantee for approximate **second-order** stationarity under the standard globally Lipschitz-Hessian assumptions, without a global gradient-Lipschitz constant. It is an oracle result, not a claim about practical running time or numerical stability.

## Problem, information, and guarantee

Let E be any finite-dimensional real Hilbert space, of dimension d. Assume f is C², its Hessian is globally H-Lipschitz in operator norm, and f(x₀)−f(x)≤Δ for every x. The supplied parameters satisfy H>0, Δ≥0, ε>0, m≥1, and 0<ρ<1. There is no convexity, bounded-domain, bounded-Hessian, low-rank, or spectral-gap assumption. The oracle provides exact (f(x),∇f(x)) in channel 0 and an exact full Hessian in channel 1, for every history and oracle seed. Their respective costs are 1 and m. A full combined first/second-order evaluation therefore costs m+1. The algorithm uses only these channels and supplied parameters; it has no access to a minimizer or to an unknown local smoothness constant.

Write S=Δ√H/ε^(3/2) and Lg=log(2+(d+1)m(1+S)/ρ). The actual `execute` output y, under the explicit product of the algorithm's internal law and the oracle's law, satisfies

P{‖∇f(y)‖≤ε and ∇²f(y)≽−√(Hε)I} ≥ 1−ρ.

Both inequalities concern the **same returned point**. The public channel budgets are

- ordinary queries: G=ceil(2^120 m^(1/3)(1+S) Lg²);
- full Hessian queries: J=ceil(2^44(1+S/m^(2/3))).

Consequently G+mJ=O(m+m^(1/3)(1+S)Lg²). The large universal constants are proof slack, not implementation recommendations. The initialization term, 1+S, dimension offset d+1, and failure dependence remain even when Δ=0 or d=0. There is no asymptotic optimality claim and no claim that the logarithms are optimal.

The setup uses the classical cubic-regularization problem class. Its assumptions are not a restriction invented to obtain the rate. For example, in arbitrary dimension,

f(x)=xᵀQx/2 + Σᵢ bᵢ(1+(aᵢᵀx)²)^(3/2) + Σⱼ cⱼ cos(vⱼᵀx)

has a globally Lipschitz Hessian when Q is positive semidefinite and bᵢ>0. A valid H is 6Σᵢbᵢ‖aᵢ‖³+Σⱼ|cⱼ|‖vⱼ‖³. Spanning, nonorthogonal aᵢ give coercive nonlinear objectives with interacting coordinates; sufficiently large cosine coefficients permit negative curvature. Their positive Hessian can be unbounded. Adding an arbitrarily large Q does not increase H. A supplied gap may be f(x₀)−Σᵢbᵢ+Σⱼ|cⱼ|. This illustrates the scope, rather than asserting that the family models a particular application. No additional restrictions are needed for the proof.

## Algorithm and technical mechanism

Set γ=√(Hε), t=max(1,ceil(m^(1/3))), δ=t²γ, τ=γ/(2³⁰H), and q=γτ². At a fresh snapshot, curvature below −δ triggers a signed coarse negative-curvature move. Otherwise B=∇²f(snapshot)+4δI defines the local metric. The snapshot is reused while the center stays within δ/(4H). In B coordinates, the relative Hessian has spectrum in [−2,1], even though the Euclidean Hessian has no upper norm bound.

A guarded accelerated stage either makes monotone progress of at least q, returns a failed-support witness giving negative curvature at its center, or obtains a small regularized dual gradient. In the last case a single correction y=x−B⁻¹∇f(x) is monotone and produces a small **Euclidean** gradient. The curvature test is performed after this correction, so the certificate applies at the returned point. A detected direction causes a signed escape and continues the algorithm; a test with no validated direction terminates.

The relative curvature test uses Chebyshev filtering of finite differences of ordinary gradients, followed by deterministic Rayleigh validation. No Hessian-vector-product oracle is assumed. With a=γ/(64δ), its degree is ceil(2 log(16 max(1,d)/a)/√a). Normalized independent Rademacher starts have a constant probability of sufficient overlap with a bad eigenvector. Repeating ceil(16 log(K/ρ)) times, with K=ceil(Δ/q)+1, gives miss probability at most ρ/K. All repetitions and validation calls are counted, including padding. A fixed finite tensor of fresh sign blocks makes adaptive conditional failure control explicit. Finite internal randomization does not restrict the objective domain or oracle seed space.

The integration is essential: a dual-gradient stopping rule alone does not certify the Euclidean gradient, and curvature at the uncorrected point does not certify the output. The correction resolves the first issue without global smoothness; testing afterward resolves the second. Each nonterminal step decreases f by at least q. An objective/path ledger charges movement at rate ε/2^40 and accounts separately for coarse escapes. It yields the actual Hessian-count bound

J_actual ≤ 1 + [2^40/ε + R/D] Δ/R,

where R=δ/(4H) and D=δ(δ/H)²/3. This is at most 1+2^43 HΔ/(εδ), and hence is covered by the public budget. Ordinary-call accounting covers the entire bounded execution, including discarded branches' prescribed padding. No uncounted stopping test or final refinement is required.

The supporting proofs are grouped into stage geometry/certificates, relative spectral filtering and finite differences, snapshot transitions and potential accounting, and adaptive probability/execution modules. In particular, [convergence](../Proofs/MonotoneHessianConvergence.lean) proves the same-output event for actual execution; [cost](../Proofs/MonotoneHessianCost.lean), [rates](../Proofs/MonotoneHessianRates.lean), and [budget](../Proofs/MonotoneHessianBudget.lean) connect the public bounds to its queries.

## Closest results and what is new

| Primary result | Comparable guarantee and distinction |
|---|---|
| [Nesterov–Polyak, *Cubic regularization of Newton method and its global performance*, Mathematical Programming 2006](https://link.springer.com/article/10.1007/s10107-006-0706-8) | Fresh cubic regularization gives matched second-order stationarity in O((m+1)(1+S)) weighted queries, up to universal tolerance rescaling. This is the full-class second-order baseline. |
| [Adil, Bullins, Sidford, Zhang, NeurIPS 2025](https://proceedings.neurips.cc/paper_files/paper/2025/hash/3dc910c921507a5d51d3dac0202b2618-Abstract-Conference.html), [arXiv 2510.20786v1](https://arxiv.org/html/2510.20786v1), Theorems 2–3 and Algorithms 1–2 | Achieves the m^(1/3) weighted dependence for first-order stationarity. At the weighted tuning its coarse curvature threshold is of order m^(2/3)γ, not γ. A terminal gradient branch can increase the objective, obstructing a direct γ-scale escape wrapper. |
| [Chen, Liu, Luo, Zhang, COLT 2026](https://proceedings.mlr.press/v336/chen26a.html), [arXiv 2501.17488v3, July 13, 2026](https://arxiv.org/html/2501.17488v3), Definition 3.2 and Theorem 4.1 | NALEN gives O(m+m^(1/3)S) for first-order stationarity. Its averaging/regret conversion does not certify a same-point second-order condition. |
| [Doikov, Chayti, Jaggi, ICML 2023](https://proceedings.mlr.press/v202/doikov23a/doikov23a.pdf), Corollary 3.7 and equation (15) | The headline square-root reuse improvement allows curvature of order √(reuse·Hε), and separately indexed minima. Matching γ in the displayed curvature bound requires a reuse²S iteration scale. The headline rate is not a matched same-point SOSP comparison. |
| [Chayti, Jaggi, arXiv 2510.15714v4, October 9, 2026](https://arxiv.org/html/2510.15714v4), Theorem 7 | Its delayed curvature bound has the analogous delay penalty and separate indexing. Treat this version as a preprint here; conference status was not verified. |
| [Carmon, Duchi, Hinder, Sidford, arXiv 1611.00756v2 / SIAM J. Optimization 2018](https://arxiv.org/abs/1611.00756), accelerated nonconvex methods | On the additional globally L-smooth overlap, Corollary 4.4 gives matched SOSP in the high-accuracy regime S≳1, with roughly S√(L/γ) gradient/Hessian-vector-product evaluations and logarithmic factors. A gradient-only realization uses finite-difference/NEON2 reductions at the same polynomial rate; ordinary-only access is not attributed directly to its HVP theorem. This is a genuine competitor, not excluded by selecting a particular method family. |

The proposed new guarantee extends the favorable weighted Hessian-query powers to **matched same-point second-order stationarity on the full Hessian-Lipschitz class**. It does not claim that spectral warping, negative-curvature escape, guarded acceleration, or Chebyshev filtering is individually new. In particular, convex-until-proven-guilty arguments appear in [Carmon et al., ICML 2017](https://proceedings.mlr.press/v70/carmon17a/carmon17a.pdf), and finite-gradient-difference Chebyshev detection appears in [NEON2, NeurIPS 2018](https://proceedings.neurips.cc/paper_files/paper/2018/file/d4b2aeb2453bdadaa45cbe9882ffefcf-Paper.pdf), Section 4 and Appendix C.2.

The strongest standard-composition challenge is to combine Adil et al.'s spectral metric, guarded acceleration, and NEON2. Such a composition does not by itself supply the claimed bound: one must resolve terminal objective rise, Euclidean gradient conversion without a global L, post-correction curvature, and the refresh/path cost of repeated fine-scale escapes. The monotone dual-gradient correction and joint objective/path accounting above resolve these obstacles in one execution. Batching is irrelevant to the exact oracle; a fresh-Hessian wrapper incurs m per fine-scale escape; ordinary Euclidean finite-difference filtering introduces smoothness dependence absent from this setup. Dimension-dependent simulation of a full Hessian remains a competing approach, so the result is not uniformly better for large m and small d.

There are nonempty regimes of polynomial improvement over the stated matched baselines. Let d=m, S=m, L/γ=m on the globally smooth overlap, and ρ=m^(−c) for fixed c>0. The bound is O(m^(4/3)log²m), versus O(m²) for fresh cubic and approximately m^(3/2) for accelerated first-order methods before their logarithms. More generally initialization must be accounted for, and the logarithms must be small compared with m^(2/3) and √(L/γ)/m^(1/3), respectively. No universal superiority or improvement for a broader class obtained by silently strengthening assumptions is asserted.

## Scope, search coverage, and limitations

The analysis uses exact real arithmetic. Dense factorization, spectral choices from a queried matrix, and vector arithmetic are uncharged. The finite-difference radii can be extremely small and Chebyshev intermediate magnitudes can be large; no finite-precision stability or wall-clock advantage is established. The algorithm is tuned using H, Δ, ε, m, and ρ; it is not adaptive to unknown smoothness. The logarithm squared reflects repeated constant-success starts. Constants are conservative. The theorem does not assert local-minimum recovery beyond the displayed approximate stationarity condition.

The research and independent review began October 25, 2026 UTC. Topic searches covered official ICML 2025/2026, ICLR 2025/2026, NeurIPS 2025 and publicly available 2026 material, roughly October 2024–October 2026 arXiv submissions/revisions, and older foundational references. Latest versions checked included the papers above, [2610.22208v2, October 19, 2026](https://arxiv.org/html/2610.22208v2) (mixed-query first-order lower bounds, not used to claim optimality), [2610.03222v1](https://arxiv.org/html/2610.03222v1) (convex lazy acceleration), [2302.11962v7](https://arxiv.org/html/2302.11962v7) (stochastic/helper cubic methods), and [2609.28238v1](https://arxiv.org/html/2609.28238v1) (fresh stochastic common-loss gradient/HVP complexity under an additional global gradient-Lipschitz bound; Theorems 3.3–3.5 do not give this exact weighted-query result). This was a bounded topic survey, not exhaustive coverage of all conference papers.

Access limitations included blocked NeurIPS 2026 virtual detail pages (official download listings were available), blocked OpenReview access for the delayed-Newton paper, and an unavailable primary manuscript for the listed affine-invariant cubic Newton/weak-learners paper. Some raw proceedings PDF endpoints failed, with corresponding arXiv HTML used instead. Acceptance status is asserted only where official proceedings were checked. Neither missing search hits nor formal verification alone establishes novelty; the contribution assessment rests on the explicit primary-theorem comparisons and integrated proof obligations above.
