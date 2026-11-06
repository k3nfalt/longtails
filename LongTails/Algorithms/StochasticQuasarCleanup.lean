import LongTails.Algorithms.StochasticQuasarParameters

namespace OracleTemplate.StochasticQuasar

open LongTails.Algorithms.StochasticEnvelopeProgram

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def robustProxPlan (L σ D r : ℝ) (c x0 : E) (n : ℕ) :
    QueryPlan (Fin 2 × E) E E (innerCalls L σ D (innerStageCount D r) * (n + 1)) :=
  (collectPlans (n + 1) (fun _ => approximationPlan L σ D r c x0)).map MultiplicativeRobustEstimator.medoid

noncomputable def robustGradientPlan (x : E) (b n : ℕ) : QueryPlan (Fin 2 × E) E E (b * (n + 1)) :=
  (collectPlans (n + 1) (fun _ => ProjectedClippedExtragradient.meanPlan b x)).map
    MultiplicativeRobustEstimator.medoid

noncomputable def cleanupPlan (L σ D r : ℝ) (c x0 : E) (b n : ℕ) :
    QueryPlan (Fin 2 × E) E E (1 + b * (n + 1) + innerCalls L σ D (innerStageCount D r) * (n + 1)) :=
  (robustProxPlan L σ D r c x0 n).bind fun x => (robustGradientPlan x b n).bind fun raw =>
    .ask (1, x - (1 / (3 * L)) • (raw + (2 * L) • (x - c))) fun y => .done y

noncomputable def initialCleanupPlan (L : ℝ) (x0 : E) (b n : ℕ) :
    QueryPlan (Fin 2 × E) E E (1 + b * (n + 1)) :=
  (robustGradientPlan x0 b n).bind fun raw => .ask (1, x0 - (1 / (3 * L)) • raw) fun y => .done y

end OracleTemplate.StochasticQuasar
