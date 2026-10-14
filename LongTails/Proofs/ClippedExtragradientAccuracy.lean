import LongTails.Proofs.ClippedExtragradientFailures
import LongTails.Proofs.ClippedExtragradientProcess
import LongTails.Proofs.ClippedExtragradientExecution

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

open StochasticGeneralized (accumulated blockTrace)

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSpace Ω]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma stageTrace_accuracy (t : Tuning) (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (F : E → E) (hc : Continuous F)
    (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (t.L0 + t.L1 * M) * ‖x - y‖)
    (g : E → Ω → E) (x0 xstar : E) (hstar : F xstar = 0) (hd : ‖x0 - xstar‖ ≤ t.R)
    (ξ : ℕ → Ω)
    (hfail : accumulated (stageCost t) (stageNext t g) (stageFailure t hR hε F hc hm g)
      (stageCount t) (0, x0, x0) ξ < 1) :
    ‖F (blockTrace (stageCost t) (stageNext t g) (0, x0, x0) ξ (stageCount t)).1.2.2‖ ≤ t.ε := by
  let state := (blockTrace (stageCost t) (stageNext t g) (0, x0, x0) ξ (stageCount t)).1
  have hi : state.1 = stageCount t := by
    dsimp [state]
    simpa only [Nat.zero_add] using stageTrace_index t g (0, x0, x0) ξ (stageCount t)
  have hg := stageTrace_good t hR hε F hc hm g (0, x0, x0) ξ (stageCount t)
    (by simp) (stageGood_initial t hR hε F hc hm x0 xstar hstar hd) hfail
  have hs := stageGood_signal t hR hε F hc hm state hi.le hg
  have hdist := hg.1
  change ‖analysisRoot t hR hε F hc hm state - state.2.2‖ ≤ radius t state.1 at hdist
  rw [hi] at hdist
  have hcount : stageCount t - 1 + 1 = stageCount t := by have := stageCount_pos t; omega
  have hradius : radius t (stageCount t) = radius t (stageCount t - 1) / 2 := by
    simpa only [hcount] using radius_succ t (stageCount t - 1)
  rw [hradius, norm_sub_rev] at hdist
  exact residual_from_close_root h0 h1 hε (radius_pos t hR (stageCount t - 1)).le hc hlip
    hs hdist (final_radius_scale t h0 h1 hR hε)

lemma stageTrace_high_probability (t : Tuning) (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (hδ : 0 < t.δ)
    (F : E → E) (hc : Continuous F) (hm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (t.L0 + t.L1 * M) * ‖x - y‖)
    {g : E → Ω → E} (P : Measure Ω) [IsProbabilityMeasure P]
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g t.σ)
    (x0 xstar : E) (hstar : F xstar = 0) (hd : ‖x0 - xstar‖ ≤ t.R) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | t.ε < ‖F (blockTrace (stageCost t) (stageNext t g)
        (0, x0, x0) ξ (stageCount t)).1.2.2‖} ≤ ENNReal.ofReal t.δ := by
  apply (measure_mono ?_).trans
    (accumulated_stage_failure t h0 h1 hR hε F hc hm hlip P hg hδ (0, x0, x0))
  intro ξ hξ
  change 1 ≤ accumulated (stageCost t) (stageNext t g)
    (stageFailure t hR hε F hc hm g) (stageCount t) (0, x0, x0) ξ
  by_contra hh
  exact (not_lt_of_ge (stageTrace_accuracy t h0 h1 hR hε F hc hm hlip g x0 xstar hstar hd ξ
    (lt_of_not_ge hh))) hξ

end OracleTemplate.ClippedExtragradient
