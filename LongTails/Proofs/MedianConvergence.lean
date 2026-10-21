import LongTails.Algorithms.MedianGradient
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.DyadicHolderTrajectory
import LongTails.Proofs.IIDBlocks
import LongTails.Proofs.DyadicHolderTuning
import LongTails.Setups.SymmetricFirstMomentNonconvex
import LongTails.Proofs.MedianOracleMoments
import LongTails.Proofs.AdaptiveIID

open MeasureTheory

namespace OracleTemplate.MedianGradient

open LongTails.Setups.SymmetricFirstMomentNonconvex
open OracleTemplate.DyadicHolder

lemma execute_paired {d : ℕ} {U Ω : Type} [MeasurableSpace Ω]
    (A : Algorithm (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) U)
    (g : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d))
    (P : ProbabilityMeasure (ℕ → Ω)) (Q : ProbabilityMeasure (ℕ → (Fin 3 → Ω)))
    (B : ℕ) (τ : A.Seed) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) }
      (paired A) (fun _ => 3 * B) τ ξ =
    execute {
      Seed := fun _ => Fin 3 → Ω
      law := Q
      answer := fun _ (_, z) ω => (oracle g z.1 ω, oracle g z.2 ω) }
      A (fun _ => B) τ (fun k i => ξ (k * 3 + i.val)) := by
  have h := execute_batched (by decide : 0 < 3) A (fun s _ => (A.query s).2)
    (fun _ v => (median (v 0).1 (v 1).1 (v 2).1, median (v 0).2 (v 1).2 (v 2).2))
    (0, 0) P (fun z ω => (g z.1 ω, g z.2 ω)) ξ B τ
  rw [Nat.mul_comm 3 B]
  refine h.trans ?_
  erw [StochasticGradient.execute_advance]
  rfl

lemma tuning {L Λ σ Δ ε : ℝ} (hL : 0 < L) (hΛ : 0 ≤ Λ) (hσ : 0 ≤ σ)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) : TuneHyp L (18 * Λ * σ) (1 / 2) (2 * σ) Δ ε :=
  ⟨hL, by positivity, le_rfl, by norm_num, by positivity, hΔ, hε⟩

lemma calls_le {L Λ σ Δ ε : ℝ} (hL : 0 < L) (hΛ : 0 ≤ Λ) (hσ : 0 ≤ σ)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (off (tcfg L (18 * Λ * σ) (1 / 2) (2 * σ) Δ ε)
      ((tcfg L (18 * Λ * σ) (1 / 2) (2 * σ) Δ ε).K + 1) : ℝ) ≤
      14400 * (1 + Real.logb 2 (2 + 16 * L * Δ / ε ^ 2)) ^ 2 *
        (1 + (L * Δ + σ ^ 2) / ε ^ 2 + Λ * σ * Δ / ε ^ 3) := by
  have hc := (tuning hL hΛ hσ hΔ hε).calls
  norm_num at hc
  refine hc.trans ?_
  have hin : 1 + (L * Δ + (2 * σ) ^ 2) / ε ^ 2 + Δ * (18 * Λ * σ) / ε ^ 3 ≤
      18 * (1 + (L * Δ + σ ^ 2) / ε ^ 2 + Λ * σ * Δ / ε ^ 3) := by
    apply sub_nonneg.mp
    ring_nf
    positivity
  have hmul := mul_le_mul_of_nonneg_left hin
    (show 0 ≤ 800 * (1 + Real.logb 2 (2 + 16 * L * Δ / ε ^ 2)) ^ 2 by positivity)
  convert hmul using 1
  ring

lemma convergence : Convergence LongTails.Setups.SymmetricFirstMomentNonconvex.spec
    (fun q _ => 3 * ⌈14400 * (1 + Real.logb 2 (2 + 16 * q.L * q.Δ / q.ε ^ 2)) ^ 2 *
      (1 + (q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 + q.Λ * q.σ * q.Δ / q.ε ^ 3)⌉₊) := by
  apply convergence_of_public_budget (S := spec) (fun q => 3 * ⌈14400 *
    (1 + Real.logb 2 (2 + 16 * q.L * q.Δ / q.ε ^ 2)) ^ 2 *
      (1 + (q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 + q.Λ * q.σ * q.Δ / q.ε ^ 3)⌉₊)
  refine ⟨fun q => method (tcfg q.L (18 * q.Λ * q.σ) (1 / 2) (2 * q.σ) q.Δ q.ε) q.x0,
    ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  dsimp only
  obtain ⟨hL, hΛ, hσ, hΔ, hε⟩ := hq
  obtain ⟨g, p, P, hIID, rfl, hgrad, hlip, hgap, hgm, hint, _hmean, hfirst, hinc, hsym⟩ := hadm
  have ht := tuning hL hΛ hσ hΔ hε
  have H := LongTails.Proofs.MedianOracleBridge.regularized_hyp
    hL hΛ hσ hgrad hlip hgm hint hfirst hinc hsym
  let cfg := tcfg q.L (18 * q.Λ * q.σ) (1 / 2) (2 * q.σ) q.Δ q.ε
  let B := ⌈14400 * (1 + Real.logb 2 (2 + 16 * q.L * q.Δ / q.ε ^ 2)) ^ 2 * (1 + (q.L * q.Δ + q.σ ^ 2) / q.ε ^ 2 + q.Λ * q.σ * q.Δ / q.ε ^ 3)⌉₊
  let Q : ProbabilityMeasure (ℕ → (Fin 3 → q.Ω)) :=
    ⟨Measure.infinitePi (fun _ : ℕ => Measure.pi fun _ : Fin 3 => (p : Measure q.Ω)), inferInstance⟩
  have hbatch : ∀ k, 1 ≤ cfg.batch k := by
    intro k
    unfold DyadicConfig.batch
    split_ifs
    · exact tbA_pos (2 * q.σ) q.ε
    · exact tb_pos q.L (18 * q.Λ * q.σ) (1 / 2) (2 * q.σ) q.Δ q.ε _
  have hB : off cfg (cfg.K + 1) ≤ B := by
    have h := calls_le hL hΛ hσ hΔ hε
    exact_mod_cast h.trans (Nat.le_ceil _)
  let block : (ℕ → q.Ω) → ℕ → Fin 3 → q.Ω := fun ξ k i => ξ (k * 3 + i.val)
  have hblock : MeasurePreserving block (P : Measure (ℕ → q.Ω)) (Q : Measure _) :=
    FiniteVariance.infinite_block_law (p : Measure q.Ω) (P : Measure (ℕ → q.Ω))
      hIID.independent hIID.marginal 3
  have hexec : ∀ (τ : Fin (cfg.K + 1)) (ξ : ℕ → q.Ω),
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d))
          (EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)))
        (method cfg q.x0) (fun _ => 3 * B) τ ξ = X cfg (oracle g) q.x0 0 (block ξ) τ.val := by
    intro τ ξ
    have he := execute_paired (dyadicVR cfg q.x0) g P Q B τ ξ
    exact he.trans (execute_dyadicVR cfg hbatch (oracle g) Q q.x0 B τ (block ξ) hB)
  have hmX : Measurable (fun ω : Fin (cfg.K + 1) × (ℕ → (Fin 3 → q.Ω)) =>
      X cfg (oracle g) q.x0 0 ω.2 ω.1.val) :=
    measurable_from_prod_countable_right fun τ => measurable_X H.meas q.x0 0 τ.val
  have hjoint := (MeasurePreserving.id
    (PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure).prod hblock
  have hmout : Measurable (fun ω : Fin (cfg.K + 1) × (ℕ → q.Ω) =>
      X cfg (oracle g) q.x0 0 (block ω.2) ω.1.val) := hmX.comp hjoint.measurable
  have hout : (fun seed : (method cfg q.x0).Seed × (ℕ → q.Ω) =>
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d))
          (EuclideanSpace ℝ (Fin q.d) × EuclideanSpace ℝ (Fin q.d)))
        (method cfg q.x0) (fun _ => 3 * B) seed.1 seed.2) =
      fun ω => X cfg (oracle g) q.x0 0 (block ω.2) ω.1.val := by
    funext ω
    exact hexec ω.1 ω.2
  change Measurable _ ∧ Integrable _ _ ∧ _
  erw [hout]
  refine ⟨hmout, ?_⟩
  have hfun := congrArg (fun out => fun ω => ‖gradient f (out ω)‖) hout
  dsimp only at hfun
  erw [hfun]
  change Integrable (fun ω : Fin (cfg.K + 1) × (ℕ → q.Ω) =>
      ‖gradient f (X cfg (oracle g) q.x0 0 (block ω.2) ω.1.val)‖)
      ((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ ω : Fin (cfg.K + 1) × (ℕ → q.Ω),
      ‖gradient f (X cfg (oracle g) q.x0 0 (block ω.2) ω.1.val)‖
      ∂((PMF.uniformOfFintype (Fin (cfg.K + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  have hm := (H.grad_continuous.measurable.comp hmout).norm
  simp only [Function.comp_apply] at hm
  have hmc := ENNReal.measurable_ofReal.comp ((H.grad_continuous.measurable.comp hmX).norm)
  have hcanon := H.master_lintegral cfg q.x0 ht.eta_pos (tbA_pos (2 * q.σ) q.ε)
    (tb_pos q.L (18 * q.Λ * q.σ) (1 / 2) (2 * q.σ) q.Δ q.ε)
    (β := q.ε ^ 2 / (32 * ((tJ q.L (18 * q.Λ * q.σ) (1 / 2) (2 * q.σ) q.Δ q.ε : ℝ) + 1)))
    (V := q.ε ^ 2 / 16) (fun j _ => ht.beta j) ht.variance hgap ht.accuracy
  have hraw := (hjoint.lintegral_comp hmc).trans_le hcanon
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hraw
  refine ⟨?_, ?_⟩
  · have hi := integrable_toReal_of_lintegral_ne_top
      (ENNReal.measurable_ofReal.comp hm).aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (norm_nonneg _)] using hi
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hraw

end OracleTemplate.MedianGradient
