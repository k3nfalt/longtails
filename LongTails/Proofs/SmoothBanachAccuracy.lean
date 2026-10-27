import LongTails.Proofs.SmoothBanachTerminal
import LongTails.Proofs.SmoothBanachExecution
import LongTails.Proofs.IIDBlocks

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SmoothBanachAccuracy

open LongTails.Setups.StochasticSmoothBanachFixedPoint
open LongTails.Algorithms.SmoothBanachAnchoring
open SmoothBanachProcess SmoothBanachSampling SmoothBanachTerminal

lemma block_accuracy (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (hC : 0 ≤ q.C) (hε : 0 < q.ε)
    (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator
      (p : Measure q.Ω) T g q.σ)
    (xstar : q.E) (hstar : T xstar = xstar) (hR : ‖q.x0 - xstar‖ ≤ q.R) :
    Integrable (fun ξ => ‖T (epochState q g (levels q + 1) ξ).2.2 -
      (epochState q g (levels q + 1) ξ).2.2‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)) ∧
    (∫ ξ, ‖T (epochState q g (levels q + 1) ξ).2.2 -
      (epochState q g (levels q + 1) ξ).2.2‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω))) ≤
      q.ε ^ 2 := by
  let Q := Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)
  let S := levels q + 1
  let F := fun ξ : ℕ → Fin (innerSteps q) → q.Ω =>
    ‖T (epochState q g S ξ).2.2 - (epochState q g S ξ).2.2‖ ^ 2
  let G := fun ξ => 128 * (S : ℝ) * ∑ j ∈ Finset.range S, epochError q T hT g j ξ + q.ε ^ 2 / 32
  have he (j : ℕ) := epoch_error_bound q T hT hC hε J hsmooth p g hg xstar hstar hR j
  have hsum : Integrable (fun ξ => ∑ j ∈ Finset.range S, epochError q T hT g j ξ) Q :=
    integrable_finsetSum _ (fun j _ => (he j).1)
  have hG : Integrable G Q := (hsum.const_mul _).add (integrable_const _)
  have hmT : Continuous T := (LipschitzWith.of_dist_le_mul (K := 1) (by
    intro x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hT x y)).continuous
  have hF : Measurable F :=
    ((hmT.measurable.comp (epochState_measurable q g hg.measurable S).snd.snd).sub
      (epochState_measurable q g hg.measurable S).snd.snd).norm.pow_const 2
  have hbound (ξ) : F ξ ≤ G ξ := by
    simpa only [F, G, S, Nat.cast_add, Nat.cast_one] using terminal_residual_square q T hT hε g xstar hstar hR ξ
  have hi : Integrable F Q := hG.mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => by simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ F ξ from sq_nonneg _)] using hbound ξ)
  refine ⟨hi, (integral_mono hi hG hbound).trans ?_⟩
  change (∫ ξ, G ξ ∂Q) ≤ _
  dsimp only [G]
  rw [integral_add (hsum.const_mul _) (integrable_const _), integral_const_mul,
    integral_finsetSum _ (fun j _ => (he j).1)]
  simp only [integral_const, probReal_univ, one_smul]
  have hs : (∑ j ∈ Finset.range S, ∫ ξ, epochError q T hT g j ξ ∂Q) ≤
      (S : ℝ) * (q.ε ^ 2 / (256 * (S : ℝ) ^ 2)) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, S, Nat.cast_add, Nat.cast_one] using
      Finset.sum_le_sum (s := Finset.range S) (fun j _ => (he j).2)
  have hp := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 128 * (S : ℝ))
  have hS : (S : ℝ) ≠ 0 := by dsimp [S]; positivity
  have hid : 128 * (S : ℝ) * ((S : ℝ) * (q.ε ^ 2 / (256 * (S : ℝ) ^ 2))) = q.ε ^ 2 / 2 := by
    field_simp
    ring
  rw [hid] at hp
  nlinarith [sq_nonneg q.ε]

lemma execution_accuracy (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (hC : 0 ≤ q.C) (hε : 0 < q.ε)
    (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure q.Ω) (P : Measure (ℕ → q.Ω)))
    (g : q.E → q.Ω → q.E)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator
      (p : Measure q.Ω) T g q.σ)
    (xstar : q.E) (hstar : T xstar = xstar) (hR : ‖q.x0 - xstar‖ ≤ q.R)
    (K : ℕ) (hK : (levels q + 1) * innerSteps q ≤ K) :
    let O : OracleTemplate.Oracle q.E q.E :=
      { Seed := fun _ => q.Ω
        law := P
        answer := fun _ (_, x) seed => g x seed }
    Measurable (fun ξ => output q O (fun _ => K) ξ) ∧
    Integrable (fun ξ => ‖T (output q O (fun _ => K) ξ) - output q O (fun _ => K) ξ‖ ^ 2) (P : Measure _) ∧
    (∫ ξ, ‖T (output q O (fun _ => K) ξ) - output q O (fun _ => K) ξ‖ ^ 2 ∂(P : Measure _)) ≤ q.ε ^ 2 := by
  dsimp only
  have hexec := SmoothBanachExecution.execute_epochs q g P
  simp_rw [hexec _ hC K hK]
  have hp := OracleTemplate.FiniteVariance.infinite_block_law (p : Measure q.Ω)
    (P : Measure (ℕ → q.Ω)) hIID.independent hIID.marginal (innerSteps q)
  have hout := (epochState_measurable q g hg.measurable (levels q + 1)).snd.snd
  have hi := block_accuracy q T hT hC hε J hsmooth p g hg xstar hstar hR
  refine ⟨hout.comp hp.measurable, hp.integrable_comp_of_integrable hi.1, ?_⟩
  have hmT : Continuous T := (LipschitzWith.of_dist_le_mul (K := 1) (by
    intro x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using hT x y)).continuous
  have hF := ((hmT.measurable.comp hout).sub hout).norm.pow_const 2
  have he := integral_map (μ := (P : Measure (ℕ → q.Ω))) hp.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm.trans_le hi.2

end LongTails.Proofs.SmoothBanachAccuracy
