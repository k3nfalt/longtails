import LongTails.Proofs.EscapeChainCounting
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.EscapeChainMeasurable

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open scoped RealInnerProductSpace BigOperators
open EscapeChainFunction EscapeChainOracle EscapeChainSimulator EscapeChainCoin EscapeChainFamily
open EscapeChainCounting EscapeChainRun EscapeChainCertificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma gradient_continuous {f : E → ℝ} (hf : ContDiff ℝ 3 f) : Continuous (gradient f) :=
  continuous_iff_continuousAt.2 fun x =>
    ((GradientDependentLocal.derivative_chain hf).2.1 x).continuousAt

lemma mvec_continuous (K : ℕ) (u v : ℕ → E) (l : ℕ) : Continuous (mvec K u v l) :=
  gradient_continuous (smask_smooth K u v l)

lemma prob_continuous (K : ℕ) (A : ℝ) (u v : ℕ → E) (l : ℕ) : Continuous (prob K A u v l) := by
  unfold prob; exact ((mvec_continuous K u v l).norm.pow 2).div_const A

lemma start_continuous (K : ℕ) (A : ℝ) (u v : ℕ → E) (l : ℕ) : Continuous (start K A u v l) := by
  unfold start; exact continuous_finsetSum _ fun m _ => prob_continuous K A u v m

variable [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [BorelSpace E] in
lemma icoin_joint {s p : E → ℝ} (hs : Measurable s) (hp : Measurable p) :
    Measurable (fun q : E × ℝ => icoin (s q.1) (p q.1) q.2) := by
  unfold icoin
  refine Measurable.ite ?_ ((measurable_const.div (hp.comp measurable_fst))) measurable_const
  exact (measurableSet_le (hs.comp measurable_fst) measurable_snd).inter
    (measurableSet_lt measurable_snd ((hs.comp measurable_fst).add (hp.comp measurable_fst)))

lemma answerS_measurable (K j : ℕ) (A : ℝ) (u v : ℕ → E) :
    Measurable (Function.uncurry (answerS K j A u v)) := by
  have hg := (gradient_continuous (objJ_smooth K j u v)).measurable
  refine (hg.comp measurable_fst).add ?_
  refine Finset.measurable_sum _ fun l _ => ?_
  exact ((icoin_joint (start_continuous K A u v l).measurable (prob_continuous K A u v l).measurable).sub
    measurable_const).smul ((mvec_continuous K u v l).measurable.comp measurable_fst)

lemma reveals_measurableSet (K : ℕ) (A : ℝ) (u v : ℕ → E) (l : ℕ) :
    MeasurableSet {q : E × ℝ | reveals K A u v l q.1 q.2} := by
  unfold reveals
  have hs := (start_continuous K A u v l).measurable
  have hp := (prob_continuous K A u v l).measurable
  exact (measurableSet_le (hs.comp measurable_fst) measurable_snd).inter
    (measurableSet_lt measurable_snd ((hs.comp measurable_fst).add (hp.comp measurable_fst)))

variable {d : ℕ}

lemma ans_measurable (c : Ctx d) (θ : Hid c.n c.b) (j : ℕ) :
    Measurable (Function.uncurry (ans c θ j)) := by
  unfold ans
  have h := answerS_measurable c.K j c.A (U c θ) (V c θ)
  have hs : Measurable fun q : Sp d × ℝ => (c.r0⁻¹ • q.1, q.2) := by fun_prop
  exact (h.comp hs).const_smul (c.δ0 / c.r0)

end LongTails.Proofs.EscapeChainMeasurable
