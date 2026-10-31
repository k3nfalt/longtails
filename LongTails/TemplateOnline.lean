import LongTails.Template

open MeasureTheory

namespace OracleTemplate

universe uP uD uI uQ uR uO

abbrev Horizon := ℕ

structure OnlineSetup where
  Params : Type uP
  Public : Type uD
  Instance : Public → Type uI
  Query : Public → Type uQ
  Reply : Public → Type uR
  Output : Public → Type uO
  publicInput : Params → Horizon → Public
  valid : Params → Horizon → Prop
  admissible : (p : Params) → (T : Horizon) → Instance (publicInput p T) →
    Oracle (Query (publicInput p T)) (Reply (publicInput p T)) → Prop
  successful : {Ω : Type} → [MeasurableSpace Ω] →
    (p : Params) → (T : Horizon) → Instance (publicInput p T) →
    (Ω → Output (publicInput p T) ×
      List ((Fin 1 × Query (publicInput p T)) × Reply (publicInput p T))) →
    ProbabilityMeasure Ω → ℝ → Prop
  allowedAlgorithm : (p : Public) → Algorithm (Query p) (Reply p) (Output p) → Prop :=
    fun _ _ => True

def OnlineConvergence (S : OnlineSetup) (bound : S.Params → Horizon → ℝ) : Prop :=
  ∃ makeAlgorithm : (p : S.Public) → Algorithm (S.Query p) (S.Reply p) (S.Output p),
    (∀ p T, S.valid p T →
      ∀ (I : S.Instance (S.publicInput p T))
        (oracle : Oracle (S.Query (S.publicInput p T)) (S.Reply (S.publicInput p T))),
        S.admissible p T I oracle →
          let A := makeAlgorithm (S.publicInput p T)
          let result := fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
            executeWithTrace oracle A (fun _ => T) seed.1 seed.2
          S.successful p T I result
            ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ (bound p T)) ∧
    ∀ p T, S.valid p T → S.allowedAlgorithm (S.publicInput p T) (makeAlgorithm (S.publicInput p T))

end OracleTemplate
