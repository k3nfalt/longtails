import LongTails.Template

open MeasureTheory

namespace OracleTemplate

universe uP₁ uD₁ uP₂ uD₂ uI uQ uR uO

structure Inclusion (strong : Setup.{uP₁, uD₁, uI, uQ, uR, uO})
    (weak : Setup.{uP₂, uD₂, uI, uQ, uR, uO}) where
  numOracles_eq : strong.numOracles = weak.numOracles
  mapParams : weak.Params → strong.Params
  mapPublic : weak.Public → strong.Public
  instance_eq : ∀ q, strong.Instance (mapPublic q) = weak.Instance q
  query_eq : ∀ q, strong.Query (mapPublic q) = weak.Query q
  reply_eq : ∀ q, strong.Reply (mapPublic q) = weak.Reply q
  output_eq : ∀ q, strong.Output (mapPublic q) = weak.Output q
  public_eq : ∀ p, strong.publicInput (mapParams p) = mapPublic (weak.publicInput p)
  valid : ∀ p, weak.valid p → strong.valid (mapParams p)
  admissible : ∀ p, weak.valid p → ∀ I O,
    weak.admissible p I O →
      strong.admissible (mapParams p) (cast (by rw [public_eq p, instance_eq]) I)
        (cast (by rw [public_eq p, query_eq, reply_eq, numOracles_eq]) O)
  successful : ∀ p, weak.valid p → ∀ I O,
    weak.admissible p I O →
      ∀ {Ω : Type} [MeasurableSpace Ω]
        (output : Ω → weak.Output (weak.publicInput p)) (P : ProbabilityMeasure Ω),
        strong.successful (mapParams p) (cast (by rw [public_eq p, instance_eq]) I)
          (fun ω => cast (by rw [public_eq p, output_eq]) (output ω)) P →
          weak.successful p I output P
  allowedAlgorithm : ∀ q (A : Algorithm (strong.Query (mapPublic q))
      (strong.Reply (mapPublic q)) (strong.Output (mapPublic q)) strong.numOracles),
    strong.allowedAlgorithm (mapPublic q) A →
      weak.allowedAlgorithm q
        (cast (by rw [numOracles_eq, query_eq q, reply_eq q, output_eq q]) A)

def Includes (strong : Setup.{uP₁, uD₁, uI, uQ, uR, uO})
    (weak : Setup.{uP₂, uD₂, uI, uQ, uR, uO}) : Prop :=
  Nonempty (Inclusion strong weak)

end OracleTemplate
