import LongTails.Proofs.NonlinearTemporalConvergence
import LongTails.Proofs.NonlinearTemporalExecution
import LongTails.Proofs.NonlinearTemporalWarmup
import LongTails.Proofs.NonlinearTemporalTuning

open scoped RealInnerProductSpace

namespace OracleTemplate.NonlinearTemporalDiscrepancy

open LongTails.Setups.HessianLipschitzTemporalDiscrepancy

open TemporalDiscrepancy

lemma warmup_entry (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ContDiff ℝ 2 f)
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (u : p.E) (hmin : IsMinOn f Set.univ u) (hgap : f p.x0 - f u ≤ p.Δ)
    (w : ℕ → p.E × p.E) (w0 : w 0 = (p.x0, p.x0)) (e : ℕ → p.E)
    (he : ∀ k, ‖e k‖ ≤ 2 * p.D / warmupBatch p)
    (hw : ∀ k, w (k + 1) = acceleratedUpdate (warmupMomentum p) p.μ (w k)
      (gradient f (acceleratedQuery (warmupMomentum p) (w k)) + e k)) :
    SimilarQuasar.energy f p.μ u (w (warmupLength p)) ≤ 2 * p.Δ ∧
      p.M ^ 2 * SimilarQuasar.energy f p.μ u (w (warmupLength p)) ≤ p.μ ^ 3 / 1024 := by
  have hθ := (momentum_valid p hp).1
  have hb := warmup_batch_positive p hp
  obtain ⟨hμ, hμL, hM, hD, hΔ, hε⟩ := hp
  have hzero := minimizer_gradient_zero hmin
  have hstrong (x : p.E) : p.μ / 2 * ‖x - u‖ ^ 2 ≤ f x - f u := by
    have hh := hs u x
    rw [hzero, inner_zero_left] at hh
    linarith
  have hinit : SimilarQuasar.energy f p.μ u (w 0) ≤ 2 * p.Δ := by
    rw [w0]
    exact initial_nonlinear_energy p.x0 u hgap (hstrong p.x0)
  by_cases hskip : 4096 * p.M ^ 2 * p.Δ ≤ p.μ ^ 3
  · rw [warmupLength, ite_eq_left hskip]
    refine ⟨hinit, ?_⟩
    have hh := mul_le_mul_of_nonneg_left hinit (sq_nonneg p.M)
    nlinarith
  · have hMp : 0 < p.M := by
      by_contra hh
      have hz : p.M = 0 := le_antisymm (le_of_not_gt hh) hM
      simp only [hz, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul] at hskip
      exact hskip (by positivity)
    have hrate := warmup_energy_bound hμ hθ.1 hθ.2.1 hθ.2.2
      (fun x => (hf.differentiable (by norm_num) x).hasGradientAt) hlip hs u
      (fun x => hmin (Set.mem_univ x)) w e he hw (warmupLength p)
    have hq : 0 ≤ 1 - 3 * warmupMomentum p / 4 := by linarith [hθ.2.1]
    have hi := mul_le_mul_of_nonneg_left hinit (pow_nonneg hq (warmupLength p))
    have hflo := warmup_floor_bound hμ (show (0 : ℝ) < warmupBatch p by exact_mod_cast hb)
      hM hD (Nat.le_ceil _)
    have hdecay := warmup_length_decay hθ.1 hθ.2.1
      (show 0 ≤ p.M ^ 2 * p.Δ / p.μ ^ 3 by positivity)
    have hsbound : (1 - 3 * warmupMomentum p / 4) ^ warmupLength p ≤
        ((2 + 4096 * p.M ^ 2 * p.Δ / p.μ ^ 3) ^ (2 : ℕ))⁻¹ := by
      rw [warmupLength, ite_eq_right hskip]
      simpa only [mul_div_assoc, mul_assoc] using hdecay
    apply warmup_scalar_finish hμ hMp hΔ (pow_nonneg hq _) (lt_of_not_ge hskip)
      hsbound hflo
    nlinarith

lemma trajectories_accuracy (p : Params) (hp : spec.valid p) (hεΔ : p.ε < p.Δ)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.M * ‖x - y‖)
    (u : p.E) (hmin : IsMinOn f Set.univ u) (hgap : f p.x0 - f u ≤ p.Δ)
    (w : ℕ → p.E × p.E) (hw0 : w 0 = (p.x0, p.x0)) (ew : ℕ → p.E)
    (hew : ∀ k, ‖ew k‖ ≤ 2 * p.D / warmupBatch p)
    (hw : ∀ k, w (k + 1) = acceleratedUpdate (warmupMomentum p) p.μ (w k)
      (gradient f (acceleratedQuery (warmupMomentum p) (w k)) + ew k))
    (v : ℕ → p.E × p.E) (hv0 : v 0 = w (warmupLength p)) (e : ℕ → p.E)
    (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ 2 * p.D)
    (hv : ∀ k, v (k + 1) = acceleratedUpdate (finalMomentum p) p.μ (v k)
      (gradient f (acceleratedQuery (finalMomentum p) (v k)) + e k)) :
    f (tailAverage (fun k => (v k).1) (finalLength p) (finalLength p)) - f u ≤ p.ε := by
  obtain ⟨hentry, hsmall⟩ := warmup_entry p hp f hf hs hlip u hmin hgap w hw0 ew hew hw
  obtain ⟨hbM, hbε, hn, hnoise⟩ := final_noise_tuning p hp hεΔ
  obtain ⟨_, hθ, hθ1, hstep⟩ := momentum_valid p hp
  have hμ := hp.1
  have hM := hp.2.2.1
  have hD := hp.2.2.2.1
  have hε := hp.2.2.2.2.2
  have hL : 0 ≤ p.L := (hμ.trans_le hp.2.1).le
  have hzero := minimizer_gradient_zero hmin
  obtain ⟨A, hA, hlower, hupper⟩ := factorized_hessian_model hμ hL hf hs hlip u
  let R := fun x => gradient f (u + x) - A.adjoint (A x)
  have hG (x : p.E) : gradient f x = A.adjoint (A (x - u)) + R (x - u) := by
    dsimp [R]
    rw [add_sub_cancel]
    abel
  have hR (x : p.E) : ‖R x‖ ≤ p.M * ‖x‖ ^ 2 :=
    hessian_remainder_bound hf hM hH u hzero A hA x
  have hrem (x : p.E) : |f (u + x) - f u - ‖A x‖ ^ 2 / 2| ≤ p.M * ‖x‖ ^ 3 := by
    simpa only [add_sub_cancel_left] using objective_linearization_bound hf hM hH u (u + x) hzero A hA
  let c := fun k => v k - (u, u)
  let r := fun k => R (acceleratedQuery (finalMomentum p) (c k))
  have hc (k : ℕ) : c (k + 1) = transition A p.μ (finalMomentum p) (c k) +
      injection p.μ (finalMomentum p) (e k + r k) := by
    dsimp only [c]
    rw [hv]
    exact centered_forcing_step A (by linarith : 1 + finalMomentum p ≠ 0)
      (gradient f) R u hG (v k) (e k)
  have hr (k : ℕ) : ‖r k‖ ≤ p.M * ‖acceleratedQuery (finalMomentum p) (c k)‖ ^ 2 := hR _
  have hstrong : p.μ / 2 * ‖(v 0).1 - u‖ ^ 2 ≤ f (v 0).1 - f u := by
    have hh := hs u (v 0).1
    rw [hzero, inner_zero_left] at hh
    linarith
  have hcsmall : p.M ^ 2 * SimilarQuasar.energy f p.μ u (v 0) ≤ p.μ ^ 3 / 1024 := by
    rwa [hv0]
  obtain ⟨hp2, haM⟩ := local_energy_conversion hμ A u (v 0) hstrong
    (objective_linearization_bound hf hM hH u (v 0).1 hzero A hA) hcsmall
  have hinit : energySeminorm A p.μ (c 0) ^ 2 ≤ 6 * p.Δ := by
    rw [hv0] at hp2
    have hΔ := hp.2.2.2.2.1
    dsimp only [c]
    rw [hv0]
    nlinarith
  have ht := final_transient_tuning p hp hεΔ hinit
  have hresult := local_tail_accuracy A u hμ hθ hθ1 (show 0 ≤ 2 * p.D by positivity)
    hM hε.le hstep hlower hupper hrem c e r hc he hr haM hbM hbε (finalLength p) hn ht hnoise
  have hout : (tailAverage c (finalLength p) (finalLength p)).1 =
      tailAverage (fun k => (v k).1) (finalLength p) (finalLength p) - u := by
    rw [show c = fun k => v k - (u, u) from rfl, tailAverage_sub_const v (u, u) _ _ hn]
    simp only [tailAverage, Prod.fst_sub, Prod.smul_fst]
    congr 2
    exact map_sum (LinearMap.fst ℝ p.E p.E) _ _
  rw [hout, add_sub_cancel] at hresult
  exact hresult

lemma execute_twoPhase_accuracy (p : Params) (hp : spec.valid p) (hεΔ : p.ε < p.Δ)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.M * ‖x - y‖)
    (u : p.E) (hmin : IsMinOn f Set.univ u) (hgap : f p.x0 - f u ≤ p.Δ)
    (O : Oracle p.E p.E) (e : ℕ → p.E)
    (hO : ∀ history x seed, O.answer history (0, x) seed = gradient f x + e history.length)
    (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ p.D)
    (K : ℕ) (hK : 2 * finalLength p + warmupBatch p * warmupLength p ≤ K)
    (seed : (twoPhaseAccelerated (warmupMomentum p) (finalMomentum p) p.μ p.x0
      (warmupBatch p) (warmupLength p) (finalLength p)).Seed) (ξ : (k : ℕ) → O.Seed k) :
    f (execute O (twoPhaseAccelerated (warmupMomentum p) (finalMomentum p) p.μ p.x0
      (warmupBatch p) (warmupLength p) (finalLength p)) (fun _ => K) seed ξ) - f u ≤ p.ε := by
  let B := warmupBatch p
  let N₀ := warmupLength p
  let N := finalLength p
  let g := fun k x => gradient f x + e k
  let ew := fun k => (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B, e (B * k + i)
  let w := acceleratedFrom (fun k x => gradient f x + ew k) (warmupMomentum p) p.μ (p.x0, p.x0)
  let ef := fun k => e (B * N₀ + k)
  let v := acceleratedFrom (fun k x => gradient f x + ef k) (finalMomentum p) p.μ (w N₀)
  have hw0 : w 0 = (p.x0, p.x0) := rfl
  have hv0 : v 0 = w N₀ := rfl
  have hw (k : ℕ) : w (k + 1) = acceleratedUpdate (warmupMomentum p) p.μ (w k)
      (gradient f (acceleratedQuery (warmupMomentum p) (w k)) + ew k) := rfl
  have hv (k : ℕ) : v (k + 1) = acceleratedUpdate (finalMomentum p) p.μ (v k)
      (gradient f (acceleratedQuery (finalMomentum p) (v k)) + ef k) := rfl
  have hwb (k : ℕ) : w (k + 1) = acceleratedUpdate (warmupMomentum p) p.μ (w k)
      ((B : ℝ)⁻¹ • ∑ i ∈ Finset.range B, g (B * k + i) (acceleratedQuery (warmupMomentum p) (w k))) := by
    dsimp only [g]
    rw [frozen_gradient_identity (gradient f) e _ (warmup_batch_positive p hp)]
    exact hw k
  have hout := execute_twoPhase_trajectory O g hO (warmupMomentum p) (finalMomentum p) p.μ p.x0
    B N₀ N K hK w v hw0 hv0 hwb hv seed ξ
  rw [hout]
  exact trajectories_accuracy p hp hεΔ f hf hs hlip hH u hmin hgap w hw0 ew
    (fun k => frozen_error_bound e he (warmup_batch_positive p hp) (B * k)) hw v hv0 ef
    (fun n => shifted_prefix_bound e he (B * N₀) n) hv

end OracleTemplate.NonlinearTemporalDiscrepancy
