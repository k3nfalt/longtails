import LongTails.Algorithms.LocalizedClippedExtragradient

namespace OracleTemplate.ClippedExtragradient

variable {Ω : Type*}

def groupSamples (r k : ℕ) (ξ : Fin (r * k) → Ω) (i : Fin k) (j : Fin r) : Ω :=
  ξ ⟨r * i.val + j.val, by
    have hi := Nat.mul_le_mul_left r (Nat.succ_le_of_lt i.isLt)
    simp only [Nat.mul_succ] at hi
    have hj := j.isLt
    omega⟩


def splitBatches (n : ℕ) (ξ : Fin (n + n) → Ω) : (Fin n → Ω) × (Fin n → Ω) :=
  ((fun i => ξ ⟨i, by have hi := i.isLt; omega⟩),
   (fun i => ξ ⟨n + i, by have hi := i.isLt; omega⟩))


def splitTrial (n k : ℕ) (ξ : Fin ((n + n) * k) → Ω) :
    Fin k → (Fin n → Ω) × (Fin n → Ω) :=
  fun i => splitBatches n (groupSamples (n + n) k ξ i)


noncomputable def splitStage (t : Tuning) (s : ℕ) (ξ : Fin (stageCalls t s) → Ω) :
    StageSamples t s Ω :=
  fun i => splitTrial (batchSize t s) (innerSteps t s)
    (groupSamples ((batchSize t s + batchSize t s) * innerSteps t s) (repetitions t) ξ i)


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def blockOutput (t : Tuning) (s : ℕ) (anchor center : E)
    (g : E → Ω → E) (ξ : Fin (stageCalls t s) → Ω) : E :=
  confidenceOutput t s anchor center g (splitStage t s ξ)

abbrev StageState (E : Type*) := ℕ × E × E

noncomputable def stageCost (t : Tuning) (state : StageState E) : ℕ := stageCalls t state.1

noncomputable def blockReply (t : Tuning) (g : E → Ω → E) (n : ℕ)
    (state : StageState E) (ξ : Fin n → Ω) : E :=
  if h : n = stageCalls t state.1 then
    blockOutput t state.1 state.2.1 state.2.2 g (fun i => ξ (Fin.cast h.symm i))
  else state.2.2

noncomputable def stageNext (t : Tuning) (g : E → Ω → E) (n : ℕ)
    (state : StageState E) (ξ : Fin n → Ω) : StageState E :=
  let next := blockReply t g n state ξ
  (state.1 + 1, (1 / 2 : ℝ) • (state.2.1 + next), next)

end OracleTemplate.ClippedExtragradient
