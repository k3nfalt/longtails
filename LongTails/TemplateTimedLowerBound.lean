import LongTails.TemplateTimed

open MeasureTheory

namespace OracleTemplate

def TimedNonConvergence (S : TimedSetup) (time : S.Params → ℝ) : Prop :=
  ∀ p, S.valid p →
    ∀ A : TimedAlgorithm (S.numNodes (S.publicInput p)) (S.Query (S.publicInput p))
        (S.Reply (S.publicInput p)) (S.Output (S.publicInput p)),
      S.allowedAlgorithm (S.publicInput p) A →
        ∀ T : ℝ, T ≤ time p →
        ∃ (I : S.Instance (S.publicInput p))
          (oracles : Fin (S.numNodes (S.publicInput p)) →
            Oracle (S.Query (S.publicInput p)) (S.Reply (S.publicInput p)))
          (environment : Environment (S.numNodes (S.publicInput p))),
          S.admissible p I oracles environment ∧
            ∀ fuel : ℕ,
              ¬ S.successful p I (executeTimed oracles environment A T fuel)
                (timedLaw oracles environment A)

end OracleTemplate
