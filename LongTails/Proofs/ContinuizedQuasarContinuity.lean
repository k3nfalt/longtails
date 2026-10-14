import LongTails.Proofs.ContinuizedQuasarStep
import LongTails.Proofs.FiniteProductIteration

namespace OracleTemplate.ContinuizedSimilarQuasar

open LongTails.Setups.ContinuizedSimilarQuasar

lemma sampleUpdate_continuous (p : Params) (g : Fin p.n × p.E → p.E)
    (hg : ∀ i, Continuous (fun x => g (i, x))) :
    Continuous (fun q : p.E × ((p.E × p.E) × (ℝ × Fin p.n)) =>
      sampleUpdate p.γ (theta p) p.μ g q.1 q.2.1 q.2.2) := by
  have hgc : Continuous g := continuous_prod_of_discrete_left.mpr hg
  unfold sampleUpdate jump FiniteSum.estimator FiniteSum.fullGradient flow flowWeight
  fun_prop

lemma parameter_iterate_continuous {T S Ω : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace Ω]
    (advance : T → S → Ω → S)
    (ha : Continuous (fun q : T × (S × Ω) => advance q.1 q.2.1 q.2.2)) (k : ℕ) :
    Continuous (fun q : T × (S × (Fin k → Ω)) =>
      iterateSamples (advance q.1) k q.2.1 q.2.2) := by
  induction k with
  | zero => exact continuous_fst.comp continuous_snd
  | succ k ih =>
      have hm : Continuous (fun q : T × (S × (Fin (k + 1) → Ω)) =>
          (q.1, (q.2.1, q.2.2 0))) := by fun_prop
      have hn : Continuous (fun q : T × (S × (Fin (k + 1) → Ω)) =>
          (q.1, (advance q.1 q.2.1 (q.2.2 0), fun i : Fin k => q.2.2 i.succ))) :=
        continuous_fst.prodMk ((ha.comp hm).prodMk
          (continuous_pi (fun i => (continuous_apply i.succ).comp
            (continuous_snd.comp continuous_snd))))
      exact ih.comp hn

lemma innerRun_continuous (p : Params) (g : Fin p.n × p.E → p.E)
    (hg : ∀ i, Continuous (fun x => g (i, x))) (k : ℕ) :
    Continuous (fun q : p.E × ((p.E × p.E) × (Fin k → ℝ × Fin p.n)) =>
      innerRun p g q.1 k q.2.1 q.2.2) :=
  parameter_iterate_continuous (sampleUpdate p.γ (theta p) p.μ g)
    (sampleUpdate_continuous p g hg) k

lemma epochRun_continuous (p : Params) (g : Fin p.n × p.E → p.E)
    (hg : ∀ i, Continuous (fun x => g (i, x))) :
    Continuous (fun q : (p.E × p.E) × (Fin (epochLength p) → ℝ × Fin p.n) =>
      epochRun p g q.1 q.2) :=
  (innerRun_continuous p g hg _).comp
    ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.prodMk continuous_snd))

end OracleTemplate.ContinuizedSimilarQuasar
