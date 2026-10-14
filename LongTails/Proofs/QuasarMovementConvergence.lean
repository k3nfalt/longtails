import LongTails.Proofs.QuasarMovementEpoch
import LongTails.Proofs.CachedQuasarRate

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.ContinuizedSimilarQuasar.Movement

open LongTails.Setups.ContinuizedSimilarQuasar

open ContinuizedSimilarQuasar
open LongTails.Setups.ContinuizedSimilarQuasar

set_option maxHeartbeats 3200000 in
lemma run_accuracy (p : Params) (f : Fin p.n → p.E → ℝ)
    (O : Oracle (Fin p.n × p.E) p.E) (hp : spec.valid p) (ho : spec.admissible p f O) :
    ∃ u, IsMinOn (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) Set.univ u ∧
      Integrable (fun seed => LongTails.Setups.FiniteSumSmoothAndConvex.objective f
        (run p (fun ix => gradient (f ix.1) ix.2) (epochs p) (p.x0, p.x0) seed).1 -
          LongTails.Setups.FiniteSumSmoothAndConvex.objective f u) (samplesLaw p.n p.n (epochs p) : Measure _) ∧
      (∫ seed, LongTails.Setups.FiniteSumSmoothAndConvex.objective f
        (run p (fun ix => gradient (f ix.1) ix.2) (epochs p) (p.x0, p.x0) seed).1 -
          LongTails.Setups.FiniteSumSmoothAndConvex.objective f u ∂(samplesLaw p.n p.n (epochs p) : Measure _)) ≤ p.ε := by
  have hpCopy := hp
  obtain ⟨hμ, hμL, hγ, hγ1, hδ, hΔ, hε⟩ := hpCopy
  obtain ⟨hcomponents, hans, hlip, hsim, u, hmin, hgap, hquasar⟩ := ho
  let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let g : Fin p.n × p.E → p.E := fun ix => gradient (f ix.1) ix.2
  let G := gradient F
  let V := SimilarQuasar.energy F p.μ u
  let θ := theta p
  let q := 4 / (4 + p.γ * θ)
  have hfull : ∀ x, FiniteSum.fullGradient g x = G x := fun x =>
    (FiniteSum.objective_gradient hcomponents x).gradient.symm
  have hg : ∀ x, HasGradientAt F (G x) x := by
    intro x
    rw [← hfull]
    exact FiniteSum.objective_gradient hcomponents x
  have hf : Continuous F := continuous_iff_continuousAt.mpr
    (fun x => (hg x).hasFDerivAt.continuousAt)
  have hV : Continuous V := energy_continuous hf p.μ u
  have hmin' : ∀ x, F u ≤ F x := fun x => hmin (Set.mem_univ x)
  have hqg := SimilarQuasar.strong_quasar_quadratic_growth hg hγ1 hmin' hquasar
  have hV0 (s : p.E × p.E) : 0 ≤ V s := SimilarQuasar.energy_nonneg hμ.le hmin' s
  have hsim' : ∀ x y, (𝔼 i, ‖(g (i, x) - G x) - (g (i, y) - G y)‖ ^ 2) ≤
      p.δ ^ 2 * ‖x - y‖ ^ 2 := by
    intro x y
    simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin, div_eq_mul_inv, mul_comm]
      using hsim x y
  have hL : 0 ≤ p.L := hμ.le.trans hμL
  have hG : Continuous G :=
    (show LipschitzWith ⟨p.L, hL⟩ G from lipschitzWith_iff_norm_sub_le.mpr hlip).continuous
  have hcomp := components_continuous g G hδ hG hsim'
  have hθ := (theta_bounds p hμ hμL hγ hδ).1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  let P : ProbabilityMeasure (Fin p.n → ℝ × Fin p.n) :=
    ⟨Measure.pi (fun _ => (sampleLaw p.n : Measure _)), inferInstance⟩
  have hepoch (s : p.E × p.E) :
      Integrable (fun a => V (epochRun p g s a)) (P : Measure _) ∧
      (∫ a, V (epochRun p g s a) ∂(P : Measure _)) ≤ q ^ p.n * V s + 0 := by
    simpa only [P, V, q, θ, ProbabilityMeasure.coe_mk, add_zero] using epoch_energy p g hp hg hlip hfull hsim' u hmin' hquasar s
  have hr := iterateSamples_integral (epochRun_continuous p g hcomp) P V hV hV0
    (pow_nonneg hq p.n) hepoch (epochs p) (p.x0, p.x0)
  have hi := SimilarQuasar.initial_energy hμ hγ hγ1 p.x0 u hgap (hqg p.x0)
  have hacc : (∫ seed, V (run p g (epochs p) (p.x0, p.x0) seed)
      ∂(samplesLaw p.n p.n (epochs p) : Measure _)) ≤ p.ε := by
    have hh := mul_le_mul_of_nonneg_left hi (pow_nonneg (pow_nonneg hq p.n) (epochs p))
    have he := epochs_accuracy p hp
    rw [pow_mul] at he
    exact hr.2.trans (by simpa only [zero_mul, add_zero] using hh.trans he)
  let R := fun seed => run p g (epochs p) (p.x0, p.x0) seed
  have hR := (iterateSamples_continuous
    (epochRun_continuous p g hcomp) (epochs p)).comp
      (show Continuous (fun seed : Fin (epochs p) → Fin p.n → ℝ × Fin p.n =>
        ((p.x0, p.x0), seed)) by fun_prop)
  change Continuous R at hR
  have hdom (seed) : F (R seed).1 - F u ≤ V (R seed) :=
    le_add_of_nonneg_right (mul_nonneg (show 0 ≤ p.μ / 2 by positivity)
      (sq_nonneg ‖(R seed).2 - u‖))
  have hFi : Integrable (fun seed => F (R seed).1 - F u)
      (samplesLaw p.n p.n (epochs p) : Measure _) := by
    apply hr.1.mono' ((hf.comp (continuous_fst.comp hR)).sub continuous_const).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro seed
    change ‖F (R seed).1 - F u‖ ≤ V (R seed)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmin' _))]
    exact hdom seed
  refine ⟨u, hmin, hFi, (integral_mono_ae hFi hr.1 ?_).trans hacc⟩
  apply Filter.Eventually.of_forall
  intro seed
  exact hdom seed

end OracleTemplate.ContinuizedSimilarQuasar.Movement
