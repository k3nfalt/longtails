import LongTails.Proofs.StrongGrowthAgdFinal
import LongTails.Proofs.IIDBlocks

namespace LongTails.Proofs.StrongGrowthAgdBridge

open MeasureTheory ProbabilityTheory LongTails.Algorithms.StrongGrowthRestartedAgd
  LongTails.Proofs.StrongGrowthAgdProcess LongTails.Proofs.StrongGrowthAgdInvariant
  LongTails.Proofs.StrongGrowthAgdBlocks LongTails.Proofs.StrongGrowthAgdEpochRun
  LongTails.Proofs.StrongGrowthAgdFinal

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω]
variable (cfg : Config) (x0 : E) (g : E → Ω → E) (f : E → ℝ)

def blocks (ξ : ℕ → Ω) : ℕ → (Fin cfg.b → Ω) := fun t i => ξ (t * cfg.b + i)

lemma blocks_measurable : Measurable (blocks cfg (Ω := Ω)) := by
  refine measurable_pi_iff.mpr (fun t => measurable_pi_iff.mpr (fun i => ?_))
  exact measurable_pi_apply _

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma run_astep_fst (sN : State E × E) (tail : ℕ → (Fin cfg.b → Ω)) :
    ∀ t, (run (astep cfg x0 g f) sN tail t).1 = run (blockStep cfg x0 g) sN.1 tail t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [run_succ, run_succ, astep_fst, ih]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma traj_eq_run (ξ : ℕ → Ω) : ∀ N, traj cfg x0 g ξ N = (run (astep cfg x0 g f) (s₀ cfg x0) (blocks cfg ξ) N).1 := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih => rw [traj_succ, run_succ, astep_fst, ih]; rfl

lemma blocks_preserving (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) p P) :
    MeasurePreserving (blocks cfg) P (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) :=
  OracleTemplate.FiniteVariance.infinite_block_law p P hIID.independent hIID.marginal cfg.b

lemma integral_blocks (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (h : (ℕ → (Fin cfg.b → Ω)) → ℝ) (hm : Measurable h) :
    ∫ ξ, h (blocks cfg ξ) ∂P = ∫ β, h β ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p)) := by
  have hmp := blocks_preserving cfg p P hIID
  rw [← hmp.map_eq, integral_map (blocks_measurable cfg).aemeasurable hm.aestronglyMeasurable]

lemma integrable_blocks (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (h : (ℕ → (Fin cfg.b → Ω)) → ℝ) (hm : Measurable h)
    (hi : Integrable h (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => p))) :
    Integrable (fun ξ => h (blocks cfg ξ)) P := by
  have hmp := blocks_preserving cfg p P hIID
  rw [← hmp.map_eq] at hi
  exact (integrable_map_measure hm.aestronglyMeasurable (blocks_measurable cfg).aemeasurable).mp hi

lemma integral_dirac_prod (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P] (h : (ℕ → Ω) → ℝ) (hm : Measurable h) :
    ∫ seed : Unit × (ℕ → Ω), h seed.2 ∂((Measure.dirac ()).prod P) = ∫ ξ, h ξ ∂P := by
  rw [Measure.dirac_prod, integral_map (f := fun seed : Unit × (ℕ → Ω) => h seed.2)
    measurable_prodMk_left.aemeasurable (hm.comp measurable_snd).aestronglyMeasurable]

lemma integrable_dirac_prod (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P] (h : (ℕ → Ω) → ℝ) (hm : Measurable h)
    (hi : Integrable h P) :
    Integrable (fun seed : Unit × (ℕ → Ω) => h seed.2) ((Measure.dirac ()).prod P) := by
  rw [Measure.dirac_prod]
  exact (integrable_map_measure (hm.comp measurable_snd).aestronglyMeasurable
    measurable_prodMk_left.aemeasurable).mpr hi

end LongTails.Proofs.StrongGrowthAgdBridge
