import LongTails.Proofs.GatedEscapeSlice
import LongTails.Proofs.GatedEscapeMoments
import LongTails.Proofs.StrongGrowthAgdBlocks

namespace LongTails.Proofs.GatedEscapeMajority

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapeMoments
  LongTails.Proofs.GatedEscapeSlice OracleTemplate.StochasticGeneralized
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {g : E → Ω → E} {gf : E → E} {σ : ℝ}

lemma card_range_filter (P : ℕ → Prop) [DecidablePred P] (M : ℕ) :
    ((Finset.range M).filter P).card = (Finset.univ.filter (fun c : Fin M => P c)).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact (Fin.sum_univ_eq_sum_range (fun c => if P c then 1 else 0) M).symm

lemma integral_fst_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A)
    (γ : Measure B) [IsProbabilityMeasure γ] (F : A → ℝ) (hF : Measurable F) :
    ∫ y, F y.1 ∂(μ.prod γ) = ∫ a, F a ∂μ := by
  rw [← integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable, Measure.map_fst_prod]
  simp

variable (cfg : Config)

theorem mom_phase (hb : 0 < cfg.b) (h : Noise g gf p σ) (γ : Measure E) [IsProbabilityMeasure γ]
    (q : E) {τ : ℝ} (hτ : 0 < τ) (hvar : σ ^ 2 / cfg.b / τ ^ 2 ≤ 1 / 16) :
    ∫ β, (if cfg.M ≤ 2 * ((Finset.range cfg.M).filter
        (fun c => τ < ‖bmean cfg g q (β c).1 - gf q‖)).card then (1 : ℝ) else 0)
      ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p).prod γ) ≤
      (19 / 32) ^ cfg.M := by
  have hbm : MeasurableSet {y : (Fin cfg.b → Ω) × E | τ < ‖bmean cfg g q y.1 - gf q‖} :=
    measurableSet_lt measurable_const
      (((bmean_measurable cfg h.meas q).comp measurable_fst).sub measurable_const).norm
  have hF : Measurable (fun ω : Fin cfg.b → Ω => if τ < ‖bmean cfg g q ω - gf q‖ then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const
      ((bmean_measurable cfg h.meas q).sub measurable_const).norm) measurable_const measurable_const
  have hμ : (∫ y, (if τ < ‖bmean cfg g q y.1 - gf q‖ then (1 : ℝ) else 0)
      ∂((Measure.pi fun _ : Fin cfg.b => p).prod γ)) ≤ 1 / 16 := by
    rw [integral_fst_prod _ γ _ hF]
    exact (chebyshev cfg hb h q τ hτ).trans hvar
  have hmaj := majority_bound ((Measure.pi fun _ : Fin cfg.b => p).prod γ)
    (fun y : (Fin cfg.b → Ω) × E => τ < ‖bmean cfg g q y.1 - gf q‖) hbm hμ cfg.M
  have hpre := prefix_preserving ((Measure.pi fun _ : Fin cfg.b => p).prod γ) cfg.M
  have hHm : Measurable (fun ω : Fin cfg.M → (Fin cfg.b → Ω) × E =>
      if cfg.M ≤ 2 * (Finset.univ.filter (fun c : Fin cfg.M =>
        τ < ‖bmean cfg g q (ω c).1 - gf q‖)).card then (1 : ℝ) else 0) := by
    refine Measurable.ite ?_ measurable_const measurable_const
    have hc : Measurable (fun ω : Fin cfg.M → (Fin cfg.b → Ω) × E =>
        (Finset.univ.filter (fun c : Fin cfg.M => τ < ‖bmean cfg g q (ω c).1 - gf q‖)).card) := by
      simp_rw [Finset.card_filter]
      refine Finset.measurable_sum _ (fun c _ => ?_)
      exact Measurable.ite (hbm.preimage (measurable_pi_apply c)) measurable_const measurable_const
    exact measurableSet_le measurable_const (hc.const_mul 2)
  have hrw : (fun β : ℕ → (Fin cfg.b → Ω) × E => (if cfg.M ≤ 2 * ((Finset.range cfg.M).filter
        (fun c => τ < ‖bmean cfg g q (β c).1 - gf q‖)).card then (1 : ℝ) else 0)) =
      fun β => (fun ω : Fin cfg.M → (Fin cfg.b → Ω) × E =>
        if cfg.M ≤ 2 * (Finset.univ.filter (fun c : Fin cfg.M =>
          τ < ‖bmean cfg g q (ω c).1 - gf q‖)).card then (1 : ℝ) else 0) (fun i : Fin cfg.M => β i) := by
    funext β
    simp only
    rw [card_range_filter (fun c => τ < ‖bmean cfg g q (β c).1 - gf q‖) cfg.M]
  rw [hrw, ← integral_map hpre.measurable.aemeasurable hHm.aestronglyMeasurable, hpre.map_eq]
  exact hmaj

end LongTails.Proofs.GatedEscapeMajority
