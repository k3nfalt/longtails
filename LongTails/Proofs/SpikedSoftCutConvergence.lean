import LongTails.Proofs.SpikedSoftCutOuterProbability
import LongTails.Proofs.SpikedSoftCutOuterInvariant
import LongTails.Proofs.SpikedSoftCutBudget

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpikedSoftCutConvergence

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut
open LongTails.Algorithms.SpikedSoftCutMethod
open SpikedSoftCutTuning
open SpikedSoftCutEpochProcess
open SpikedSoftCutFreshness
open SpikedSoftCutEvents
open SpikedSoftCutEpochCertificate
open SpikedSoftCutOuterProbability
open SpikedSoftCutOuterInvariant

noncomputable def noiseEnvelope (q : Params) : ℝ := q.ε^2/(2^31*q.R^2*logScale q)
noncomputable def failureShare (q : Params) : ℝ := 1/(100*((tunedConfig q).K : ℝ))
noncomputable def epochRadius (q : Params) (k : ℕ) : ℝ := q.R*(5/8 : ℝ)^k

lemma tuned_good_primal (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε)
    (k : ℕ) (state : OuterState q) (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R)
    (hconvex : ConvexOn ℝ Set.univ f) (hlip : ∀ x y, |f x-f y| ≤ q.G*‖x-y‖)
    (hsupport : ∀ x y, ⟪v x,y-x⟫ ≤ f y-f x)
    (hgood : ¬badEpoch q (tunedConfig q) (noiseEnvelope q) (failureShare q) (epochRadius q k) k state g v ξ) :
    let c := tunedConfig q
    let slope := headSlope q c (center q state) v (innerSeedReplies q c (center q state) g ξ)
    f (primalOutput q c state (epochReplies q c k state g ξ))-f xstar+slope*(head q xstar-center q state) ≤ q.ε/16 ∧
      |slope| ≤ q.G ∧ |scalarEstimate q c k (epochReplies q c k state g ξ)-slope| ≤ q.ε/(8*epochRadius q k) := by
  let c := tunedConfig q
  let S := (q.m : ℝ)*Real.log (16*(q.m : ℝ)+1)+(c.T : ℝ)*Real.log (16*(c.T : ℝ)+1)+Real.log (400*(c.K : ℝ))
  let V := 128*noiseEnvelope q*S
  let W := 128*noiseEnvelope q*q.R^2*S
  let M := q.G+c.α*c.T/q.R
  let smallr := c.α/(192*M)
  have hc := tunedConfig_positive q hG hR hε
  have hK : 0 < (c.K : ℝ) := by dsimp [c]; exact_mod_cast hc.2.2.2.2.1
  have hρ : 4/failureShare q = 400*(c.K : ℝ) := by
    dsimp [failureShare,c]
    field_simp
    ring
  have hentropy : netEntropy q c (failureShare q) = S := by
    unfold netEntropy
    rw [hρ]
  have hbad := not_or.mp hgood
  have hbadInner := not_or.mp hbad.1
  have hop : ‖innerErrorMatrix q c (center q state) g v ξ‖^2 ≤ V := by
    have hh := le_of_not_gt hbadInner.1
    change ‖innerErrorMatrix q c (center q state) g v ξ‖^2 ≤ 128*noiseEnvelope q*netEntropy q c (failureShare q) at hh
    rwa [hentropy] at hh
  have hint : ‖innerErrorIntercept q c (center q state) g v ξ‖^2 ≤ W := by
    have hh := le_of_not_gt hbadInner.2
    change ‖innerErrorIntercept q c (center q state) g v ξ‖^2 ≤ 128*noiseEnvelope q*q.R^2*netEntropy q c (failureShare q) at hh
    rwa [hentropy] at hh
  have hparams := tuned_inner_parameters q hG hR hε
  change 0 ≤ V ∧ 0 ≤ W ∧ q.G+Real.sqrt V ≤ M ∧ 0 < smallr ∧ smallr ≤ q.R ∧
    (q.m : ℝ)*Real.log (q.R/smallr) ≤ (c.T : ℝ)/48 ∧ 2*smallr*M ≤ c.α/96 ∧
    (c.α/2+2*q.R*M)*c.T/c.n ≤ c.α*c.T/32 ∧ 2*(q.R^2*V+W)*c.T ≤ (c.α*c.T/32)^2 at hparams
  obtain ⟨hV,hW,hM,hr,hrR,hlog,hrM,hgrid,hnoise⟩ := hparams
  have hgrad (x : Space q) : ‖v x‖ ≤ q.G :=
    SpikedSoftCutCoordinates.subgradient_norm_le f q.G hG.le hlip x (v x) (hsupport x)
  have hcert := seeded_true_certificate q c (center q state) M V W smallr g v ξ hc.1 hR hG.le
    hc.2.1 hc.2.2.1 hc.2.2.2.1 hV hW hM hr hrR hlog hrM hgrad hgrid hop hint hnoise
  have hp := epoch_primal_certificate q c hc.2.1 hc.2.2.2.1 k state g v f ξ xstar hxstar
    (c.α/2) hconvex hsupport hcert
  have he : c.α/2 = q.ε/16 := by change (q.ε/8)/2 = q.ε/16; ring
  rw [he] at hp
  refine ⟨hp, epoch_head_bound q c hc.2.1 hc.2.2.2.1 (center q state) g v ξ hgrad, ?_⟩
  exact le_of_not_gt hbad.2

noncomputable def RunInvariant (q : Params) (f : Space q → ℝ) (xstar : Space q) (k : ℕ)
    (state : OuterState q) : Prop :=
  radius q state = epochRadius q k ∧
    (frozen q state = true → f (saved q state)-f xstar ≤ q.ε) ∧
    (frozen q state = false → |head q xstar-center q state| ≤ radius q state) ∧
    (0 < k → frozen q state = false → f (saved q state)-f xstar ≤ q.ε/16+q.G*epochRadius q (k-1))

lemma initial_invariant (q : Params) (f : Space q → ℝ) (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R) :
    RunInvariant q f xstar 0 (initialState q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [radius,initialState,epochRadius]
  · simp [frozen,initialState]
  · intro _
    simpa only [center,radius,initialState,sub_zero] using (SpikedSoftCutCoordinates.abs_head_le q xstar).trans hxstar
  · simp

lemma invariant_step (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε)
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R) (hmin : IsMinOn f Set.univ xstar)
    (hconvex : ConvexOn ℝ Set.univ f) (hlip : ∀ x y, |f x-f y| ≤ q.G*‖x-y‖)
    (hsupport : ∀ x y, ⟪v x,y-x⟫ ≤ f y-f x) (k : ℕ) (state : OuterState q) (ξ : ℕ → q.Ω)
    (hInv : RunInvariant q f xstar k state)
    (hgood : ¬badEpoch q (tunedConfig q) (noiseEnvelope q) (failureShare q) (epochRadius q k) k state g v ξ) :
    RunInvariant q f xstar (k+1) (nextState q (tunedConfig q) k state (epochReplies q (tunedConfig q) k state g ξ)) := by
  let c := tunedConfig q
  let replies := epochReplies q c k state g ξ
  let slope := headSlope q c (center q state) v (innerSeedReplies q c (center q state) g ξ)
  obtain ⟨hrad,hsaved,hloc,_⟩ := hInv
  have hr : 0 < radius q state := by rw [hrad]; dsimp [epochRadius]; positivity
  obtain ⟨hcert,hslope,hnoise⟩ := tuned_good_primal q hG hR hε k state f v g ξ xstar hxstar hconvex hlip hsupport hgood
  have hnoise' : |scalarEstimate q c k replies-slope| ≤ q.ε/(8*radius q state) := by
    rw [hrad]
    exact hnoise
  have hgap : 0 ≤ f (primalOutput q c state replies)-f xstar := sub_nonneg.mpr (hmin (Set.mem_univ _))
  have hnext := nextState_invariant q c k state replies f (f xstar) (head q xstar) slope hε hr hsaved hloc hgap hcert hnoise'
  refine ⟨?_,hnext.1,hnext.2,?_⟩
  · rw [nextState_radius,hrad]
    dsimp [epochRadius]
    rw [pow_succ]
    ring
  · intro _ hfnext
    have hf : frozen q state = false := by
      change (frozen q state || decide (|scalarEstimate q c k replies| ≤ q.ε/(2*radius q state))) = false at hfnext
      cases he : frozen q state
      · rfl
      · simp only [he,Bool.true_or] at hfnext
        contradiction
    have hh := last_saved_gap q c k state replies f (f xstar) (head q xstar) slope (q.ε/16)
      hf hG.le hcert (hloc hf) hslope
    simpa only [Nat.add_sub_cancel,hrad] using hh

lemma terminal_good_gap (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε)
    (f : Space q → ℝ) (xstar : Space q) (state : OuterState q)
    (hInv : RunInvariant q f xstar (tunedConfig q).K state) : f (saved q state)-f xstar ≤ q.ε := by
  obtain ⟨_,hsaved,_,hlast⟩ := hInv
  by_cases hf : frozen q state = true
  · exact hsaved hf
  · have hk := (tunedConfig_positive q hG hR hε).2.2.2.2.1
    have hh := hlast hk (Bool.eq_false_iff.mpr hf)
    have hr := tuned_last_radius q hG hR hε
    change q.G*q.R*(5/8 : ℝ)^((tunedConfig q).K-1) ≤ q.ε/16 at hr
    dsimp [epochRadius] at hh
    nlinarith

lemma measurable_objective (q : Params) (hG : 0 < q.G) (f : Space q → ℝ)
    (hlip : ∀ x y, |f x-f y| ≤ q.G*‖x-y‖) : Measurable f := by
  have hh : LipschitzWith q.G.toNNReal f := LipschitzWith.of_dist_le_mul (fun x y => by
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,Real.coe_toNNReal q.G hG.le] using hlip x y)
  exact hh.continuous.measurable

lemma seeded_failure_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (q : Params) (hG : 0 < q.G) (hR : 0 < q.R) (hε : 0 < q.ε)
    (hrest : 0 ≤ q.vRest) (horder : q.vRest ≤ q.vTop)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : Measure Ξ) [IsProbabilityMeasure P]
    (ξ : ℕ → Ξ → q.Ω) (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R)
    (hmin : IsMinOn f Set.univ xstar) (hconvex : ConvexOn ℝ Set.univ f)
    (hlip : ∀ x y, |f x-f y| ≤ q.G*‖x-y‖) :
    P.real {ω | q.ε < f (saved q (SpikedSoftCutSeededExecution.terminalState q (tunedConfig q) g 0
      (tunedConfig q).K (initialState q) (fun i => ξ i ω)))-f xstar} ≤ 1/50 := by
  let c := tunedConfig q
  let z : q.Ω := Classical.choice (nonempty_of_isProbabilityMeasure p)
  let B := fun ω => OracleTemplate.StochasticGeneralized.accumulated (blockCost q c) (blockNext q c g z)
    (blockIncrement q c (noiseEnvelope q) (failureShare q) (epochRadius q) g v z) c.K (0,initialState q) (fun i => ξ i ω)
  let output := fun ω => saved q (SpikedSoftCutSeededExecution.terminalState q c g 0 c.K (initialState q) (fun i => ξ i ω))
  have hc := tunedConfig_positive q hG hR hε
  have hv := SpikedSoftCutCoordinates.measurable_mean q p f v g hg
  have hprob : ∀ k state, (Measure.infinitePi fun _ : ℕ => p).real
      {seeds | badEpoch q c (noiseEnvelope q) (failureShare q) (epochRadius q k) k state g v seeds} ≤ 1/(50*(c.K : ℝ)) :=
    fun k state => tuned_badEpoch_probability q hG hR hε hrest horder k state p f v g hg
  have hmean := accumulated_bad_mean q c hR hc.2.1 hc.2.2.1 hc.2.2.2.1
    (noiseEnvelope q) (failureShare q) (1/(50*(c.K : ℝ))) (epochRadius q) g v hg.measurable hv z
    p P ξ hξ hprob c.K (0,initialState q)
  have hstream : Measurable (fun ω => fun i => ξ i ω) := Measurable.of_eval hξ.measurable
  have ho := (measurable_seeded_output q c hR g hg.measurable c.K 0 (initialState q)).comp hstream
  have hf := measurable_objective q hG f hlip
  have hE : MeasurableSet {ω | q.ε < f (output ω)-f xstar} :=
    measurableSet_lt measurable_const ((hf.comp ho).sub_const (f xstar))
  have hB : ∀ ω, 0 ≤ B ω := fun ω => accumulated_bad_nonneg q c (noiseEnvelope q) (failureShare q)
    (epochRadius q) g v z c.K (0,initialState q) (fun i => ξ i ω)
  have hgood : ∀ ω, B ω < 1 → ω ∉ {ω | q.ε < f (output ω)-f xstar} := by
    intro ω hsmall
    have hi := accumulated_small_preserves q c hc.2.1 hc.2.2.1 hc.2.2.2.1
      (noiseEnvelope q) (failureShare q) (epochRadius q) g v z (RunInvariant q f xstar)
      (invariant_step q hG hR hε f v g xstar hxstar hmin hconvex hlip hg.support)
      c.K 0 (initialState q) (fun i => ξ i ω) (initial_invariant q f xstar hxstar) hsmall
    simp only [Nat.zero_add] at hi
    have hh := terminal_good_gap q hG hR hε f xstar _ hi
    exact not_lt.mpr hh
  have hp := event_probability_of_small_success P _ hE B hmean.1 hB hgood
  have hK : 0 < (c.K : ℝ) := by dsimp [c]; exact_mod_cast hc.2.2.2.2.1
  have he : (c.K : ℝ)*(1/(50*(c.K : ℝ))) = 1/50 := by field_simp
  exact hp.trans (hmean.2.trans_eq he)

end LongTails.Proofs.SpikedSoftCutConvergence
