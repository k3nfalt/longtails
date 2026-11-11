import LongTails.Template

open MeasureTheory

namespace OracleTemplate

def NonConvergence (S : Setup)
    (budget : S.Params → Fin S.numOracles → ℕ) : Prop :=
  ∀ p, S.valid p →
    ∀ A : Algorithm (S.Query (S.publicInput p)) (S.Reply (S.publicInput p))
        (S.Output (S.publicInput p)) S.numOracles,
      S.allowedAlgorithm (S.publicInput p) A →
        ∃ (I : S.Instance (S.publicInput p))
          (oracle : Oracle (S.Query (S.publicInput p)) (S.Reply (S.publicInput p)) S.numOracles),
          S.admissible p I oracle ∧
            let result := fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
              execute oracle A (budget p) seed.1 seed.2
            ¬ S.successful p I result
              ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩

end OracleTemplate
