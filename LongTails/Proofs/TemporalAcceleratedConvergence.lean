import LongTails.Proofs.TemporalAcceleratedExecution
import LongTails.Proofs.TemporalAcceleratedRate

noncomputable section

namespace OracleTemplate.TemporalDiscrepancy

open LongTails.Setups.QuadraticTemporalDiscrepancy

lemma run_accuracy (p : Params) (I : Instance p.toPublic) (e : ℕ → p.E)
    (hp : spec.valid p)
    (hcurv : ∀ x, p.μ * ‖x‖ ^ 2 ≤ ‖I.A x‖ ^ 2 ∧ ‖I.A x‖ ^ 2 ≤ p.L * ‖x‖ ^ 2)
    (hinit : objective I p.x0 ≤ p.Δ)
    (he : ∀ n, ‖∑ k ∈ Finset.range n, e k‖ ≤ p.D) (K : ℕ)
    (hbudget : max 1 ⌈(1 / Real.sqrt (p.μ / p.L)) * Real.log (1 + 8 * p.Δ / p.ε) + 8 * p.D / Real.sqrt (p.μ * p.ε)⌉₊ ≤ K) :
    let θ := Real.sqrt (p.μ / p.L)
    let g := fun k x => exactGradient I x + e k
    objective I (tailAverage (fun k => (acceleratedRun g θ p.μ p.x0 k).1) K K) -
      objective I I.xstar ≤ p.ε := by
  obtain ⟨hμ, hμL, hD, hΔ, hε⟩ := hp
  have hL : 0 < p.L := hμ.trans_le hμL
  let θ := Real.sqrt (p.μ / p.L)
  let g := fun k x => exactGradient I x + e k
  let s := acceleratedRun g θ p.μ p.x0
  let v := fun k => s k - (I.xstar, I.xstar)
  have hθ : 0 < θ := Real.sqrt_pos.mpr (div_pos hμ hL)
  have hs : θ ^ 2 = p.μ / p.L := Real.sq_sqrt (div_nonneg hμ.le hL.le)
  have hθ1 : θ ≤ 1 := by
    have hrat := (div_le_one hL).mpr hμL
    nlinarith
  have hstep : θ ^ 2 * p.L ≤ p.μ := by rw [hs, div_mul_cancel₀ _ hL.ne']
  have hden : 1 + θ ≠ 0 := by positivity
  have hv (k : ℕ) : v (k + 1) = transition I.A p.μ θ (v k) + injection p.μ θ (e k) := by
    dsimp only [v, s, acceleratedRun]
    rw [← update_sub_const θ p.μ hden]
    change acceleratedUpdate θ p.μ (s k - (I.xstar, I.xstar))
      (I.A.adjoint (I.A (acceleratedQuery θ (s k) - I.xstar)) + e k) = _
    rw [← query_sub_const θ hden]
    exact forced_transition I.A p.μ θ _ _
  have hzero : v 0 = (p.x0 - I.xstar, p.x0 - I.xstar) := rfl
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hbudget)
  have hr := accelerated_tail_rate I.A hμ hθ hθ1 hD hstep
    (fun x => (hcurv x).1) (fun x => (hcurv x).2) v e (p.x0 - I.xstar) hzero hinit hv he K K hK
  have hb := tail_budget hμ hθ hθ1 hD hΔ hε K hbudget
  change 4 * p.Δ * (1 - θ) ^ K + 32 * p.D ^ 2 / (p.μ * (K : ℝ) ^ 2) ≤ p.ε at hb
  have ht : (tailAverage v K K).1 = tailAverage (fun k => (s k).1) K K - I.xstar := by
    rw [tailAverage_sub_const s (I.xstar, I.xstar) K K hK]
    simp only [tailAverage, Prod.fst_sub, Prod.smul_fst]
    congr 2
    exact map_sum (LinearMap.fst ℝ p.E p.E) _ _
  rw [ht] at hr
  change objective I (tailAverage (fun k => (s k).1) K K) - objective I I.xstar ≤ p.ε
  simpa [objective] using hr.trans hb

lemma execute_accuracy (p : Params) (I : Instance p.toPublic) (O : Oracle p.E p.E)
    (hp : spec.valid p) (ho : spec.admissible p I O) (ξ : (k : ℕ) → O.Seed k) (K : ℕ)
    (hbudget : max 1 ⌈(1 / Real.sqrt (p.μ / p.L)) * Real.log (1 + 8 * p.Δ / p.ε) + 8 * p.D / Real.sqrt (p.μ * p.ε)⌉₊ ≤ K) :
    let θ := Real.sqrt (p.μ / p.L)
    let out := execute O (tailAccelerated θ p.μ p.x0) (fun _ => (2 * K)) () ξ
    objective I out - objective I I.xstar ≤ p.ε := by
  obtain ⟨hcurv, hinit, e, hO, he⟩ := ho
  let θ := Real.sqrt (p.μ / p.L)
  let g := fun k x => exactGradient I x + e k
  have hx := execute_tailAccelerated O g hO θ p.μ p.x0 (2 * K) () ξ
  have hk1 : 2 * K / 2 = K := by omega
  have hk2 : 2 * K - K = K := by omega
  dsimp only
  rw [hx, hk1, hk2]
  exact run_accuracy p I e hp hcurv hinit he K hbudget

end OracleTemplate.TemporalDiscrepancy
