import LongTails.Proofs.FairExecutionMeasurable
import LongTails.Proofs.FairExpectedDescent
import LongTails.Proofs.IIDBlocks
import LongTails.Proofs.PairedOracleExecution

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory ProbabilityTheory

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma paired_output_law (cfg : Config) [Nonempty (Fin (max 1 cfg.T))]
    (hm : 0 < cfg.m) (hR : 0 < cfg.R) (hT : 0 < cfg.T) (hb : ∀ t, 0 < cfg.batch t)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E)
    (P : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) (hK : cfg.calls ≤ K) :
    let paired := P.map (fun ξ k => ξ (k / 2))
    let O : Oracle E E := { Seed := fun _ => Ω, law := paired, answer := fun _ (_, x) ω => g x ω }
    ((PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure.prod (paired : Measure _)).map
      (fun z => execute O (algorithm cfg x0) (fun _ => K) z.1 z.2) =
    ((PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure.prod (P : Measure (ℕ → Ω))).map
      (fun z : Fin (max 1 cfg.T) × (ℕ → Ω) =>
        (trajectory cfg g x0 (fun j i => z.2 (cfg.m * j + i)) z.1.val).1) := by
  dsimp only
  apply LongTails.Proofs.PairedOracleExecution.paired_stream_output_law
    (fun k (ξ : ℕ → Ω) => ξ k) (fun k => measurable_pi_apply k)
    (measurable_execute cfg hm hR hg x0 (P.map (fun ξ k => ξ (k / 2))) K)
  intro τ ξ
  exact execute_trajectory cfg hm hT hb g x0
    ({ Seed := fun _ => Ω
       law := P.map (fun ξ k => ξ (k / 2))
       answer := fun _ (_, x) ω => g x ω } : Oracle E E)
    τ (fun k => ξ (k / 2)) ξ (fun _ _ => rfl) K hK

lemma iid_grouped_output_law (cfg : Config) [Nonempty (Fin (max 1 cfg.T))]
    (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E)
    (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ => ξ k) = p) :
    ((PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure.prod P).map
      (fun z : Fin (max 1 cfg.T) × (ℕ → Ω) =>
        (trajectory cfg g x0 (fun j i => z.2 (cfg.m * j + i)) z.1.val).1) =
    ((PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin cfg.m => p)).map
      (fun z => (trajectory cfg g x0 z.2 z.1.val).1) := by
  let Q := (PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure
  have hb := FiniteVariance.infinite_block_law p P hind hmarg cfg.m
  have hp := (MeasurePreserving.id Q).prod hb
  have hout : Measurable (fun z : Fin (max 1 cfg.T) × (ℕ → Fin cfg.m → Ω) =>
      (trajectory cfg g x0 z.2 z.1.val).1) :=
    measurable_from_prod_countable_right fun τ => (measurable_trajectory cfg hm hR hg x0 τ.val).fst
  rw [← hp.map_eq, Measure.map_map hout hp.measurable]
  congr 1
  funext z
  change (trajectory cfg g x0 (fun j i => z.2 (cfg.m * j + i)) z.1.val).1 =
    (trajectory cfg g x0 (fun j i => z.2 (j * cfg.m + i)) z.1.val).1
  simp only [Nat.mul_comm]

lemma execute_identDistrib (cfg : Config) [Nonempty (Fin (max 1 cfg.T))]
    (hm : 0 < cfg.m) (hR : 0 < cfg.R) (hT : 0 < cfg.T) (hb : ∀ t, 0 < cfg.batch t)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E)
    (p : Measure Ω) [IsProbabilityMeasure p] (P : ProbabilityMeasure (ℕ → Ω))
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) (P : Measure (ℕ → Ω)))
    (hmarg : ∀ k, (P : Measure (ℕ → Ω)).map (fun ξ => ξ k) = p) (K : ℕ) (hK : cfg.calls ≤ K) :
    let paired := P.map (fun ξ k => ξ (k / 2))
    let O : Oracle E E := { Seed := fun _ => Ω, law := paired, answer := fun _ (_, x) ω => g x ω }
    IdentDistrib (fun z : Fin (max 1 cfg.T) × (ℕ → Ω) =>
      execute O (algorithm cfg x0) (fun _ => K) z.1 z.2)
      (fun z : Fin (max 1 cfg.T) × (ℕ → Fin cfg.m → Ω) => (trajectory cfg g x0 z.2 z.1.val).1)
      ((PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure.prod (paired : Measure _))
      ((PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin cfg.m => p)) := by
  dsimp only
  refine ⟨(measurable_execute cfg hm hR hg x0 (P.map (fun ξ k => ξ (k / 2))) K).aemeasurable,
    (measurable_from_prod_countable_right fun τ =>
      (measurable_trajectory cfg hm hR hg x0 τ.val).fst).aemeasurable, ?_⟩
  exact (paired_output_law cfg hm hR hT hb hg x0 P K hK).trans
    (iid_grouped_output_law cfg hm hR hg x0 p (P : Measure (ℕ → Ω)) hind hmarg)

end OracleTemplate.FairVarianceReduction
