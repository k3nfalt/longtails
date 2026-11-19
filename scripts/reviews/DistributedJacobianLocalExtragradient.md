# Novelty review: DistributedJacobianLocalExtragradient

[Theorem](../../LongTails/Theorems/DistributedJacobianLocalExtragradient.lean) · [Setup](../../LongTails/Setups/DistributedJacobianStrongGrowth.lean) · [Algorithm](../../LongTails/Algorithms/DistributedLocalExtragradientProtocol.lean)

The theorem proves an elapsed-time bound for n tree-connected workers. The problem class is quasi-strongly monotone, L-Lipschitz operators F: ℝᵈ→ℝᵈ with an M-Lipschitz Jacobian. Each worker has an unbiased oracle with strong growth, E‖g‖² ≤ ρ‖F‖². After the stated time, the output satisfies E‖x − x*‖² ≤ ε². The method is SGD warm-up, a quantized coordinatewise median, and then rounds of T local extragradient steps whose endpoints are averaged.

**Parameters.** κ = L/μ, and R ≥ ‖x₀ − x*‖. Each oracle call takes time τ. Each tree edge costs λ + β·(bits) per message, and h is the tree depth. Write G = 2 + ρ/8 + ρ²/128 ≍ ρ².

**Simplified bound.** The budget has three branches:
- If R ≤ ε, the time is 0.
- If n < 64κG, the method uses the root alone, and the time is O(τρκ² log(R/ε)).
- Otherwise the local depth is T = min{⌊κ⌋, ⌊log(n/64κ)/log G⌋} ≥ 1. Using G^T ≤ n/(64κ) and κ/T ≍ max{1, κ(1+log ρ)/log(n/64κ)}, the budget is at most

  B = O( [τρκ² + h(λ + βd log n)]·log(d(1 + ρMRn/L)) + τκ log(R/ε) + h(λ + βd log(ndR/ε))·max{1, κ(1+log ρ)/log(n/64κ)}·log(R/ε) ).

| Previous result (source and theorem) | Previous complexity → This result | Complexity improvement | Setup / assumptions improved | Adaptivity / output improved | Extra assumptions / tradeoffs |
|---|---|---|---|---|---|
| Novoselov–Dorn–Dvinskikh–Gasnikov, [arXiv:2610.12641v1](https://arxiv.org/abs/2610.12641) (8 Oct 2026, prior), Prop. F.4 / eq. (34), **serial EG on one worker**. *Restriction: strongly monotone; no Jacobian assumption needed.* | τρκ log(R/ε), with no communication, so it is end-to-end in this time model → B | Up to a factor Θ(min{ρ,T}), but only when log(R/ε) ≳ ρκT·log(d(1+ρMRn/L)) and hλ + βd log(ndR/ε) ≲ Tτ. **Worse** by a factor ≈ κ when n < 64κG (the fallback is τρκ² log(R/ε)) and whenever the τρκ² startup dominates. | Pairwise strong monotonicity → quasi-strong monotonicity, but an M-Lipschitz Jacobian is added. The two classes are incomparable. | None. Both bound expected squared distance, and both use known parameters. | Needs Jacobian regularity, n ≥ 64κG^T workers, and a tree network. |
| Same paper, eq. (3) / Prop. F.4, **common-query minibatch EG**, N rounds. *Restriction: strongly monotone; the analysis uses exact real-vector rounds.* | κ·max{1, ρ/n}·log(R/ε) rounds. In this model that is at least κ log(R/ε)·(τ + 2hλ) for n ≥ ρ, with bit costs uncharged (no finite-bit proof exists) → B | At most a factor T in the communication term. The gain is Θ(T) when hλ ≍ Tτ, βd log(ndR/ε) ≲ λ, and the τρκ² startup is negligible. Since T ≤ log(n/64κ)/log G, the gain is logarithmic in n. | Same as above. | None | Extra startup cost τρκ² log(d(1+ρMRn/L)). The bits for the comparison method are not modeled. |
| Wang–Kale, [arXiv:2602.09164v1](https://arxiv.org/abs/2602.09164) (NeurIPS 2026), Thms. 1 and 4 (LESGD, LIPPAX) | Not comparable: monotone operators, restricted-gap criterion, additive noise σ², and a bounded operator (Thm. 4) | Not comparable | Not comparable: additive noise versus strong growth; neither class contains the other | Gap of averaged iterates versus distance | — |

**Reduction check.** On the strongly monotone overlap, the stronger of the two Novoselov schedules already gives time κ log(R/ε)·min{ρτ, τ + 2hλ}. The new result gains only by replacing the round latency hλ with hλ/T. That gain is not obtained by substitution or batching. It needs the local-depth mechanism: the endpoint mean follows a linearized EG recursion, and the Taylor bias is controlled by M·E‖X − x*‖². This is plausibly new relative to the checked papers, whose local extragradient guarantees are affine-only (Novoselov, §3) or use additive noise with a gap criterion (Wang–Kale).

**Proof ancestry.** This is not a complexity baseline. Woodworth et al., "Is Local SGD Better than Minibatch SGD?" (ICML 2020), shows that local methods can beat minibatch methods under quadratic or third-order smoothness. That work covers convex optimization with additive noise only, and I did not recheck its theorem numbers.

**Search coverage (19 Nov 2026).** I searched arXiv, NeurIPS and the general web for federated and local extragradient under strong growth and Jacobian smoothness. I read Novoselov et al. §1–6 and App. E–F, and Wang–Kale through Thm. 2 verbatim; their Thms. 3–7 come only from a summary. The following were not verified:
- the affine paper arXiv:2611.02598 cited in the companion note (not found);
- Gorbunov et al. (AISTATS 2022) on quasi-strongly monotone SEG;
- Newton or finite-difference competitors.

The result entered the repository on 18 Nov 2026 (commit `03f5f1cc`), after both checked papers. The companion note says the checked guarantees reach order τt⁷ in its example. Our recomputation agrees for both the serial schedule and the common-query schedule. The note does not stress that the root-only fallback is a factor κ worse than serial EG on the strongly monotone overlap.

## Conclusion

**There is a real speedup, but it is small: at most logarithmic in the number of workers.** The strongest baselines are both schedules of Novoselov et al. (2026), serial EG and common-query minibatch EG, on strongly monotone operators. With J = log(R/ε), the comparison is:

| | elapsed time (ε ≪ R) |
|---|---|
| best prior | κJ·min{ρτ, τ + hλ} |
| this result | τρκ² log(dq) + τκJ + hλ·(κ/T)·J |

Here q ≤ 1 + ρMRn/L, and bit-cost terms are omitted. The gain is at most Θ(min{ρ, T}). It is attained only when latency dominates (hλ ≍ Tτ), the accuracy is very high (J ≳ ρκT log(dq)), and n ≥ 64κG^T workers are available, where G ≍ ρ². For example, with ρ = 20, a 10× speedup needs about 4·10¹⁰κ workers.

The method loses elsewhere. The τρκ² startup term, and the root-only branch used when n < 64κG, are a factor κ worse than serial EG's τρκJ on the overlap. It also requires a Lipschitz Jacobian. The removal of pairwise strong monotonicity is offset by that added Jacobian assumption, so the two classes are incomparable.

The search found no earlier nonlinear local-step guarantee under strong growth, but that does not establish priority. Newton-type competitors and the affine paper remain unchecked. What can be claimed is a first proved nonlinear local-EG elapsed-time gain under strong growth plus Jacobian smoothness, by a factor of at most about log(n/κ)/log ρ in extreme regimes.

**Verdict: LIMITED OR INCREMENTAL NOVELTY**
**Confidence: medium**
