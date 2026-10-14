import LongTails.Proofs.ClippedExtragradientOracle
import LongTails.Proofs.AdaptiveIID

open MeasureTheory

namespace OracleTemplate.ClippedExtragradient

open StochasticGeneralized (blockTrace blockAdvance)

lemma measurable_blockTrace {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {cost : S → ℕ} {next : (n : ℕ) → S → (Fin n → Ω) → S}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n))) (k : ℕ) :
    Measurable (fun w : S × (ℕ → Ω) => blockTrace cost next w.1 w.2 k) := by
  have hf (n : ℕ) : Measurable (fun w : S × (ℕ → Ω) =>
      (next n w.1 (fun i => w.2 i), fun j => w.2 (n + j))) :=
    ((hn n).comp (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop)
  have hg : Measurable (fun w : (S × (ℕ → Ω)) × ℕ =>
      (next w.2 w.1.1 (fun i => w.1.2 i), fun j => w.1.2 (w.2 + j))) :=
    measurable_from_prod_countable_left hf
  have ha : Measurable (blockAdvance cost next) :=
    hg.comp (measurable_id.prodMk (hc.comp measurable_fst))
  exact ha.iterate k

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma measurable_stageTrace {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (k : ℕ) :
    Measurable (fun w : StageState E × (ℕ → Ω) =>
      blockTrace (stageCost t) (stageNext t g) w.1 w.2 k) :=
  measurable_blockTrace ((measurable_of_countable (stageCalls t)).comp measurable_fst)
    (measurable_stageNext hg t) k

end OracleTemplate.ClippedExtragradient
