import LongTails.Proofs.CovarianceSoftCutComposition
import LongTails.Proofs.CovarianceSoftCutBudget

open MeasureTheory

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutGuarantee

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Algorithms.CovarianceSoftCutMethod
open LongTails.Proofs.CovarianceSoftCutMethodProcess
open LongTails.Proofs.CovarianceSoftCutComposition
open LongTails.Proofs.CovarianceSoftCutTuning

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_objective (q : Params) (hL : 0 < q.L) (f : Space q → ℝ)
    (hlip : ∀ x y, |f x-f y| ≤ q.L*‖x-y‖) : Measurable f := by
  have hl : LipschitzWith q.L.toNNReal f := LipschitzWith.of_dist_le_mul (fun x y => by
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, Real.coe_toNNReal q.L hL.le] using hlip x y)
  exact hl.continuous.measurable

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma execute_method_failure (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hR : 0 < q.R)
    (hε : 0 < q.ε) (hsmall : q.ε < q.L*q.R)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : ProbabilityMeasure (ℕ → q.Ω))
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k) p (P : Measure (ℕ → q.Ω)))
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsCovarianceSubgradient q p f v g) (hlip : ∀ x y, |f x-f y| ≤ q.L*‖x-y‖)
    (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R) (N : ℕ) (hN : workCost (tunedConfig q) ≤ N) :
    let O : OracleTemplate.Oracle (Space q) (Space q) :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ point seed => g point.2 seed }
    (P : Measure _) {ξ | q.ε < f (OracleTemplate.execute O (method q (tunedConfig q)) (fun _ => N) () ξ)-f xstar} ≤
      (1/3 : ENNReal) := by
  let c := tunedConfig q
  let τ := q.ε/(2*(c.H : ℝ))
  obtain ⟨hb, hn, hm⟩ := tuned_batch_pos q
  obtain ⟨hτ, hapos, ha, hpower, hacc⟩ := tuned_accuracy_parameters q hL hR hε hsmall
  have hf := measurable_objective q hL f hlip
  have hα : 0 < c.α := by change 0 < q.ε/2; positivity
  have hαR : c.α ≤ q.L*q.R := by change q.ε/2 ≤ q.L*q.R; linarith
  have hc := method_output_failure_probability q hd hL hR c hb hn hm hα hαR τ hτ ha p
    (P : Measure _) hs f hf v g hg hlip xstar hxstar (tuned_generator_batch q hd hε)
    (tuned_height q hε hsmall).2.1 (tuned_selection_batch q hd hapos) hpower
  have herr : (selectionBlocks c.K c.H : ℝ)*Real.exp (-(c.m : ℝ)/8) ≤ 1/12 :=
    rounded_mom_failure (selectionBlocks c.K c.H)
  have hsum : c.α+(c.H : ℝ)*τ = q.ε := hacc
  rw [hsum] at hc
  dsimp only
  have he : {ξ | q.ε < f (OracleTemplate.execute
      ({ Seed := fun _ => q.Ω, law := P, answer := fun _ point seed => g point.2 seed } :
        OracleTemplate.Oracle (Space q) (Space q)) (method q c) (fun _ => N) () ξ)-f xstar} =
      {ξ | q.ε < f (selectionOutput q c.a c.K c.n c.m c.H (generatedLeaves q c g ξ)
        (selectedReplies q c g ξ))-f xstar} := by
    ext ξ
    exact (congrArg (fun y : Space q => q.ε < f y-f xstar)
      (execute_method q c hb (Nat.mul_pos hn hm) g P N hN ξ)).to_iff
  rw [he]
  apply hc.trans
  calc
    (1/4 : ENNReal)+ENNReal.ofReal ((selectionBlocks c.K c.H : ℝ)*Real.exp (-(c.m : ℝ)/8)) ≤
        1/4+ENNReal.ofReal (1/12 : ℝ) := add_le_add le_rfl (ENNReal.ofReal_le_ofReal herr)
    _ = 1/3 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num

lemma execute_zero (q : Params) (g : Space q → q.Ω → Space q)
    (P : ProbabilityMeasure (ℕ → q.Ω)) (N : ℕ) (seed : Unit) (ξ : ℕ → q.Ω) :
    let O : OracleTemplate.Oracle (Space q) (Space q) :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample }
    OracleTemplate.execute O (historyMethod q (fun _ _ => 0) (fun _ => 0)) (fun _ => N) seed ξ = 0 := by
  cases seed
  dsimp only
  exact LongTails.Proofs.CovarianceSoftCutExecution.execute_historyMethod q
    (fun _ _ => 0) (fun _ => 0) (by intros; rfl)
    { Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample }
    N ξ (fun i point => g point.2 (ξ i)) (by intros; rfl) (fun i => g 0 (ξ i))
    (by intros; rfl) (by intros; rfl)

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma successful_tuned (q : Params) (hq : spec.valid q) (N : ℕ)
    (hN : q.ε < q.L*q.R → workCost (tunedConfig q) ≤ N)
    (f : Space q → ℝ) (O : OracleTemplate.Oracle (Space q) (Space q)) (hadm : spec.admissible q f O) :
    let A := tunedMethod q
    spec.successful q f
      (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => OracleTemplate.execute O A (fun _ => N) seed.1 seed.2)
      ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hd, hL, hR, hσ, hε⟩ := hq
  obtain ⟨v, g, p, P, hs, rfl, hconv, hlip, ⟨xstar, hmin, hxstar⟩, hg⟩ := hadm
  have hf := measurable_objective q hL f hlip
  dsimp only
  by_cases hsmall : q.ε < q.L*q.R
  · have heA : tunedMethod q = method q (tunedConfig q) := by
      unfold tunedMethod
      exact ite_eq_left hsmall
    rw [heA]
    obtain ⟨hb, hn, hm⟩ := tuned_batch_pos q
    have hcost := hN hsmall
    have hmeas := measurable_execute_method q hR (tunedConfig q) hb (Nat.mul_pos hn hm) g hg.measurable P N hcost
    have hprod : Measurable (fun seed : Unit × (ℕ → q.Ω) => OracleTemplate.execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample } :
          OracleTemplate.Oracle (Space q) (Space q)) (method q (tunedConfig q)) (fun _ => N) seed.1 seed.2) :=
      hmeas.comp measurable_snd
    refine ⟨hprod, xstar, hmin, ?_⟩
    have hbad := measurableSet_lt (measurable_const (a := q.ε)) ((hf.comp hmeas).sub_const (f xstar))
    have hpre := (measurePreserving_snd (μ := (Measure.dirac () : Measure Unit))
      (ν := (P : Measure (ℕ → q.Ω)))).measure_preimage hbad.nullMeasurableSet
    exact hpre.le.trans (execute_method_failure q hd hL hR hε hsmall (p : Measure q.Ω) P hs f v g hg
      hlip xstar hxstar N hcost)
  · have heA : tunedMethod q = historyMethod q (fun _ _ => 0) (fun _ => 0) := by
      unfold tunedMethod
      exact ite_eq_right hsmall
    rw [heA]
    have he (seed : Unit × (ℕ → q.Ω)) := execute_zero q g P N seed.1 seed.2
    have hzero : f 0-f xstar ≤ q.ε := by
      have hh := hlip 0 xstar
      simp only [zero_sub, norm_neg] at hh
      have hr := mul_le_mul_of_nonneg_left hxstar hL.le
      have hgap := le_abs_self (f 0-f xstar)
      linarith
    have hfun : (fun seed : Unit × (ℕ → q.Ω) => OracleTemplate.execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample } :
          OracleTemplate.Oracle (Space q) (Space q))
        (historyMethod q (fun _ _ => 0) (fun _ => 0)) (fun _ => N) seed.1 seed.2) =
        (fun _ => (0 : Space q)) := funext he
    refine ⟨hfun.symm ▸ measurable_const, xstar, hmin, ?_⟩
    have hempty : {seed : Unit × (ℕ → q.Ω) | q.ε < f (OracleTemplate.execute
        ({ Seed := fun _ => q.Ω, law := P, answer := fun _ point sample => g point.2 sample } :
          OracleTemplate.Oracle (Space q) (Space q))
        (historyMethod q (fun _ _ => 0) (fun _ => 0)) (fun _ => N) seed.1 seed.2)-f xstar} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro seed hbad
      have hh := (congrArg (fun y : Space q => q.ε < f y-f xstar) (he seed)).to_iff.mp hbad
      exact (not_lt.mpr hzero) hh
    have hm := congrArg (fun s => ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → q.Ω))) s) hempty
    exact hm.le.trans (by simp)

end LongTails.Proofs.CovarianceSoftCutGuarantee
