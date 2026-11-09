import LongTails.Proofs.FullRangeGlue
import LongTails.Proofs.FullRangeTuning
import LongTails.Proofs.FullRangeSeed
import LongTails.Proofs.IIDBlocks

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.FullRangeAccuracy

open OracleTemplate OracleTemplate.StochasticCohypomonotone
open LongTails.Algorithms.FullRangeMlmc LongTails.Algorithms.FullRangeProgram
open LongTails.Algorithms.FullRangeTuned
open LongTails.Proofs.FullRangeInner LongTails.Proofs.FullRangeExecution LongTails.Proofs.FullRangeGlue
open LongTails.Proofs.FullRangeTuning LongTails.Proofs.FullRangeOperator LongTails.Proofs.FullRangeResolvent
open LongTails.Proofs.FullRangeClip LongTails.Proofs.FullRangeEstimator
open LongTails.Setups.StochasticCohypomonotoneInclusion (Params)
open LongTails.Setups.StochasticGeneralizedMonotone (IsStochasticOperator)
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)
open OracleTemplate.LocalHiddenConvex (ballProj)

variable (q : Params) (hL : 0 < q.L) (hρ : 0 ≤ q.ρ) (hρL : q.ρ * q.L < 1) (hR0 : 0 ≤ q.R)
  (hσ : 0 ≤ q.σ) (hε : 0 < q.ε)
  {F : q.E → q.E} {G : q.E → Set q.E} {J : ℝ → q.E → q.E} (H : OpHyp F G J q.L q.ρ)
  (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E)
  (hg : IsStochasticOperator (p : Measure q.Ω) F g q.σ)
  (xs : q.E) (hxs : -F xs ∈ G xs) (hR : ‖q.x0 - xs‖ ≤ q.R)

noncomputable def thetaLaw : Measure (thetaType q) :=
  (levelLaw (top q)).prod (Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω))

instance : IsProbabilityMeasure (thetaLaw q p) := by unfold thetaLaw; infer_instance

noncomputable def Tc : q.E → q.E :=
  clippedMap H (eta_pos q hL hρ) (etaL_lt q hL hρL) (tau q) q.x0 (radius q)

include hL hρ hρL in
lemma Tc_nonexp (hε : 0 < q.ε) (hR0 : 0 ≤ q.R) (x y : q.E) :
    ‖Tc q hL hρ hρL H x - Tc q hL hρ hρL H y‖ ≤ ‖x - y‖ :=
  clip_nonexpansive (fun a b => fixedMap_nonexpansive H (eta_pos q hL hρ) (etaL_lt q hL hρL)
    (tau_pos q hρL).le (tau_eta_le q hL hρL) a b) q.x0 (radius_pos q hL hρ hρL hR0 hε).le x y

include hL hρ hρL hxs hR in
lemma Tc_fixed (hε : 0 < q.ε) : Tc q hL hρ hρL H xs = xs := by
  have hx : ‖xs - q.x0‖ ≤ radius q := by
    rw [norm_sub_rev]
    have := radius_half q hL hρ hρL hε
    have hr := radius_pos q hL hρ hρL ((norm_nonneg _).trans hR) hε
    linarith
  unfold Tc clippedMap
  rw [ballProj_of_mem q.x0 xs hx]
  exact fixedMap_of_zero H _ _ _ hxs

lemma transfer_integral {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure A} {ν : Measure B} {ρ : Measure C} (f : A → ℝ) (fb : B → ℝ) (pre : C → A) (blk : C → B)
    (hpre : MeasurePreserving pre ρ μ) (hblk : MeasurePreserving blk ρ ν) (hf : Measurable f)
    (hfb : Measurable fb) (heq : ∀ c, f (pre c) = fb (blk c)) (hi : Integrable fb ν) :
    Integrable f μ ∧ (∫ a, f a ∂μ) = ∫ b, fb b ∂ν := by
  have hcomp : f ∘ pre = fb ∘ blk := funext heq
  have hi1 : Integrable (f ∘ pre) ρ := by rw [hcomp]; exact hblk.integrable_comp_of_integrable hi
  refine ⟨(hpre.integrable_comp hf.aestronglyMeasurable).mp hi1, ?_⟩
  have e1 := integral_map (μ := ρ) hpre.measurable.aemeasurable hf.aestronglyMeasurable
  have e2 := integral_map (μ := ρ) hblk.measurable.aemeasurable hfb.aestronglyMeasurable
  rw [hpre.map_eq] at e1
  rw [hblk.map_eq] at e2
  rw [e1, e2]
  exact congrArg (fun F => ∫ c, F c ∂ρ) hcomp

noncomputable def ideal (θ : Fin (calls q) → thetaType q) : St q :=
  iterateSamples (LongTails.Proofs.FullRangeLaw.advTheta (top := top q) (callAdv J g (cfg q)))
    (calls q) (cfg q).init θ

set_option maxHeartbeats 1000000 in
include hL hρ hρL hR0 hε hg hxs hR in
theorem anchor_accuracy :
    Integrable (fun θ => ‖Tc q hL hρ hρL H (ideal q (J := J) g θ).2.2.2 - (ideal q (J := J) g θ).2.2.2‖)
      (Measure.pi fun _ : Fin (calls q) => thetaLaw q p) ∧
    (∫ θ, ‖Tc q hL hρ hρL H (ideal q (J := J) g θ).2.2.2 - (ideal q (J := J) g θ).2.2.2‖
      ∂Measure.pi fun _ : Fin (calls q) => thetaLaw q p) ≤ epsT q := by
  have hη := eta_pos q hL hρ
  have hηL := etaL_lt q hL hρL
  have ht := tau_pos q hρL
  have hr := radius_pos q hL hρ hρL hR0 hε
  have hγ : 0 < gamma0 q := by unfold gamma0; positivity
  have hx : ‖xs - q.x0‖ ≤ radius q / 2 := by
    rw [norm_sub_rev]; exact hR.trans (radius_half q hL hρ hρL hε)
  have he := epsT_pos q hL hρ hρL hε
  have hS := stages_pos q
  have hβ0 : 0 ≤ epsT q / (80 * (stages q : ℝ)) := by positivity
  have hb := callEstimate_biased (top := top q) H hη hηL p g hγ (gamma0_step q hL hρ hρL)
    (n0_pos q) (kappa_le q hL hρ hρL hR0 hε) hg ht (tau_le_one q hL hρ) (tau_eta_le q hL hρL)
    q.x0 xs hr hxs hx hβ0 (variance_tolerance q hL hρ hρL hR0 hε) (bias_tolerance q hL hρ hρL hR0 hε)
  have hP : IsProbabilityMeasure (thetaLaw q p) := by unfold thetaLaw; infer_instance
  let pA : ProbabilityMeasure (anchorParams q).Ω := ⟨thetaLaw q p, hP⟩
  have hb' : LongTails.Proofs.BiasedAnchoring.IsBiasedOperator (pA : Measure (anchorParams q).Ω)
      (Tc q hL hρ hρL H) (gA q (J := J) g) (anchorParams q).σ (epsT q / (80 * (stages q : ℝ))) := hb
  have hβε : (epsT q / (80 * (stages q : ℝ))) ^ 2 ≤ (anchorParams q).ε ^ 2 /
      (6400 * (LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q) + 1 : ℝ) ^ 2) := by
    have e : (LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q) + 1 : ℝ) = stages q := by
      simp [stages, anchorLevels, LongTails.Algorithms.SmoothBanachAnchoring.levels, anchorParams]
    rw [e]
    apply le_of_eq
    change _ = epsT q ^ 2 / _
    field_simp
    ring
  have hacc := LongTails.Proofs.BiasedAnchoring.block_accuracy (anchorParams q) (Tc q hL hρ hρL H)
    (Tc_nonexp q hL hρ hρL H hε hR0) (by norm_num [anchorParams]) he
    ((innerSL ℝ : q.E →L[ℝ] q.E →L[ℝ] ℝ))
    (fun x y => inner_smooth_sq (E := q.E) x y) pA (gA q (J := J) g) _ hβ0 hβε hb'
    xs (Tc_fixed q hL hρ hρL H xs hxs hR hε) hR
  let N := LongTails.Algorithms.SmoothBanachAnchoring.innerSteps (anchorParams q)
  let lev := LongTails.Algorithms.SmoothBanachAnchoring.levels (anchorParams q)
  let eS : (ℕ → Fin N → thetaType q) → St q := fun ζ =>
    (0, 0, 0, (LongTails.Algorithms.SmoothBanachAnchoring.epochState (anchorParams q) (gA q (J := J) g)
      (lev + 1) ζ).2.2)
  let fb : (ℕ → Fin N → thetaType q) → ℝ := fun ζ => ‖Tc q hL hρ hρL H (eS ζ).2.2.2 - (eS ζ).2.2.2‖
  have hKle : (lev + 1) * N ≤ calls q := by
    apply le_of_eq
    simp only [calls, stages, anchorLevels, lev, N, LongTails.Algorithms.SmoothBanachAnchoring.levels,
      anchorParams]
  have hiid := OracleTemplate.StochasticGeneralized.infinitePi_iid (thetaLaw q p)
  have hblock := OracleTemplate.FiniteVariance.infinite_block_law (thetaLaw q p)
    (Measure.infinitePi fun _ : ℕ => thetaLaw q p) hiid.independent hiid.marginal N
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving (thetaLaw q p) (calls q)
  have hTc : Continuous (Tc q hL hρ hρL H) := (LipschitzWith.of_dist_le_mul (K := 1) (by
    intro a b
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using Tc_nonexp q hL hρ hρL H hε hR0 a b)).continuous
  have hadvm := LongTails.Proofs.FullRangeLaw.advTheta_measurable (top := top q) (callAdv J g (cfg q))
    (fun l => callAdv_measurable q H g hg.measurable hη hγ hr.le l)
  have hidm : Measurable (ideal q (J := J) g) :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable hadvm (calls q)).comp
      (measurable_const.prodMk measurable_id)
  have hpt : Measurable (fun θ : Fin (calls q) → thetaType q => (ideal q (J := J) g θ).2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hidm))
  have hhm : Measurable (fun θ : Fin (calls q) → thetaType q =>
      ‖Tc q hL hρ hρL H (ideal q (J := J) g θ).2.2.2 - (ideal q (J := J) g θ).2.2.2‖) :=
    ((hTc.measurable.comp hpt).sub hpt).norm
  have hpath (θext : ℕ → thetaType q) :
      ‖Tc q hL hρ hρL H (ideal q (J := J) g (fun i => θext i)).2.2.2 -
        (ideal q (J := J) g (fun i => θext i)).2.2.2‖ = fb (fun k i => θext (k * N + i)) := by
    have := ideal_point q (J := J) g θext hKle
    simp only [ideal, fb, eS]
    rw [this]
  have hfbm : Measurable fb := by
    have hm := (LongTails.Proofs.SmoothBanachProcess.epochState_measurable (anchorParams q)
      (gA q (J := J) g) hb'.measurable (lev + 1)).snd.snd
    exact ((hTc.measurable.comp hm).sub hm).norm
  have hfb2 : Integrable (fun ζ => fb ζ ^ 2)
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin N => thetaLaw q p) := by
    exact hacc.1
  have hfbi : Integrable fb (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin N => thetaLaw q p) := by
    refine (hfb2.add (integrable_const 1)).mono' hfbm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ζ => ?_)
    have h0 : 0 ≤ fb ζ := norm_nonneg _
    have key : ∀ x : ℝ, 0 ≤ x → ‖x‖ ≤ x ^ 2 + 1 := fun x hx => by
      rw [Real.norm_of_nonneg hx]
      nlinarith [sq_nonneg (x - 1)]
    exact key _ h0
  have htr := transfer_integral _ fb (fun θext : ℕ → thetaType q => fun i : Fin (calls q) => θext i)
    (fun θext k i => θext (k * N + i)) hpre hblock hhm hfbm hpath hfbi
  refine ⟨htr.1, ?_⟩
  rw [htr.2]
  have hsq : (∫ ζ, fb ζ ^ 2 ∂Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin N => thetaLaw q p) ≤
      epsT q ^ 2 := hacc.2
  have := LongTails.Proofs.FullRangeCertificate.integral_le_sqrt _ (fun _ => norm_nonneg _) hfbi hfb2 hsq
  rwa [Real.sqrt_sq he.le] at this

include hL hρ hρL hR0 hσ hε hg hxs hR in
theorem cert_point (y : q.E) (hy : ‖y - q.x0‖ ≤ radius q) :
    Integrable (LongTails.Proofs.FullRangeCertificate.certResidual F J g (eta q) (gamma0 q) (n0 q)
      (levelTime (n0 q) (top q)) (batch q) y) (Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω)) ∧
    (∫ ξ, LongTails.Proofs.FullRangeCertificate.certResidual F J g (eta q) (gamma0 q) (n0 q)
      (levelTime (n0 q) (top q)) (batch q) y ξ ∂Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω)) ≤
      q.ε / 8 + q.ε / 8 +
        ‖y - fixedMap H (eta_pos q hL hρ) (etaL_lt q hL hρL) (tau q) y‖ / (tau q * eta q) := by
  have hη := eta_pos q hL hρ
  have hηL := etaL_lt q hL hρL
  have ht := tau_pos q hρL
  have hr := radius_pos q hL hρ hρL hR0 hε
  have hγ : 0 < gamma0 q := by unfold gamma0; positivity
  have hc := LongTails.Proofs.FullRangeCertificate.cert_expectation H hη hηL p g hσ hg hγ
    (gamma0_step q hL hρ hρL) (n0 := n0 q) y (levelTime (n0 q) (top q)) (batch q) (batch_pos q)
  refine ⟨hc.1, hc.2.trans ?_⟩
  set D := ‖y - resH H hη hηL y‖ with hD
  have hsub := sub_fixedMap H hη hηL (tau q) y
  have hTD : ‖y - fixedMap H hη hηL (tau q) y‖ = tau q * D := by
    rw [hsub, norm_smul, Real.norm_of_nonneg ht.le]
  have hDb : tau q * D ≤ 3 * radius q := by
    rw [← hTD]
    have hn := fixedMap_nonexpansive H hη hηL ht.le (tau_eta_le q hL hρL) y xs
    rw [fixedMap_of_zero H hη hηL _ hxs] at hn
    have hyx : ‖y - xs‖ ≤ 3 * radius q / 2 := by
      have := norm_sub_le_norm_sub_add_norm_sub y q.x0 xs
      have h2 := radius_half q hL hρ hρL hε
      linarith
    have := norm_sub_le_norm_sub_add_norm_sub y xs (fixedMap H hη hηL (tau q) y)
    rw [norm_sub_rev xs] at this
    linarith
  have hlev := level_moment H hη hηL p g y hγ (gamma0_step q hL hρ hρL) (n0_pos q)
    (kappa_le q hL hρ hρL hR0 hε) hg (top q)
  have hmse : Real.sqrt (mse H hη hηL (gamma0 q) (n0 q) p g y (levelTime (n0 q) (top q))) ≤
      Real.sqrt (Real.exp (-(gamma0 q * (1 - eta q * q.L) * n0 q)) * D ^ 2 +
        2 * (gamma0 q * (eta q ^ 2 * q.σ ^ 2) / (1 - eta q * q.L)) / (2 : ℝ) ^ top q) :=
    Real.sqrt_le_sqrt hlev
  have hp := cert_path_tolerance q hL hρ hρL hR0 hε hDb (norm_nonneg _)
  have hbt := batch_tolerance q hσ hε
  have h3 := mul_le_mul_of_nonneg_left hmse (show 0 ≤ 3 * q.L by positivity)
  have hlast : D / eta q = ‖y - fixedMap H hη hηL (tau q) y‖ / (tau q * eta q) := by
    rw [hTD]
    field_simp
  linarith

lemma thin_preserving {Ω : Type} [MeasurableSpace Ω] (p0 : Measure Ω)
    (P0 : Measure (ℕ → Ω)) [IsProbabilityMeasure P0]
    (hind : ProbabilityTheory.iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P0)
    (hmarg : ∀ k, P0.map (fun ξ => ξ k) = p0) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun k => ξ (2 * k)) P0 (Measure.infinitePi fun _ : ℕ => p0) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
  refine ⟨by fun_prop, ?_⟩
  have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun v => measurable_pi_apply (2 * v))).mp (hind.precomp hinj)
  simpa only [hmarg] using h

lemma seedCost_eq (n0 : ℕ) {K top : ℕ} (ℓ : Fin K → Fin (top + 1)) :
    seedCost n0 ℓ = 2 * LongTails.Proofs.FullRangeLaw.costOf (levelTime n0)
      (List.ofFn fun i => ((ℓ i : Fin (top + 1)) : ℕ)) := by
  induction K with
  | zero => simp [seedCost, LongTails.Proofs.FullRangeLaw.costOf]
  | succ K ih =>
      unfold seedCost at ih ⊢
      rw [Fin.sum_univ_succ, List.ofFn_succ, LongTails.Proofs.FullRangeLaw.costOf, ih (fun i => ℓ i.succ)]
      simp only [levelCost]
      ring

include H hL hρ hρL in
lemma certResidual_joint (hg : Measurable (Function.uncurry g)) :
    Measurable (fun w : q.E × (ℕ → q.Ω) => LongTails.Proofs.FullRangeCertificate.certResidual F J g
      (eta q) (gamma0 q) (n0 q) (levelTime (n0 q) (top q)) (batch q) w.1 w.2) := by
  have hη := eta_pos q hL hρ
  have ht := tau_pos q hρL
  have hγ : 0 < gamma0 q := by unfold gamma0; positivity
  have hZ := innerPath_joint_measurable H hη (n0 := n0 q) g hγ hg (levelTime (n0 q) (top q))
  have hFl : Continuous F := (LipschitzWith.of_dist_le_mul (K := Real.toNNReal q.L) (by
    intro a b
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]
    exact H.lip a b)).continuous
  have hJc : Continuous (J (eta q)) := (LipschitzWith.of_dist_le_mul (K := 1) (by
    intro a b
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using H.res_nonexp hη a b)).continuous
  have hFh : Measurable (fun w : q.E × (ℕ → q.Ω) => LongTails.Proofs.FullRangeCertificate.certFhat g
      (innerPath J g (eta q) (gamma0 q) (n0 q) w.1 (levelTime (n0 q) (top q)) w.2)
      (levelTime (n0 q) (top q)) (batch q) w.2) := by
    unfold LongTails.Proofs.FullRangeCertificate.certFhat
    refine (Finset.measurable_sum _ fun i _ => ?_).const_smul _
    exact hg.comp (hZ.prodMk ((measurable_pi_apply (levelTime (n0 q) (top q) + (i : ℕ))).comp
      measurable_snd))
  have hp : Measurable (fun w : q.E × (ℕ → q.Ω) => w.1 - eta q • LongTails.Proofs.FullRangeCertificate.certFhat g
      (innerPath J g (eta q) (gamma0 q) (n0 q) w.1 (levelTime (n0 q) (top q)) w.2)
      (levelTime (n0 q) (top q)) (batch q) w.2) := measurable_fst.sub (hFh.const_smul _)
  unfold LongTails.Proofs.FullRangeCertificate.certResidual
  exact ((hFl.measurable.comp (hJc.measurable.comp hp)).add
    ((hp.sub (hJc.measurable.comp hp)).const_smul _)).norm

section Exec

variable {Ω0 : Type} (gg : q.E → q.Ω → q.E) (JJ : ℝ → q.E → q.E)

noncomputable def thin (ξ : ℕ → q.Ω) : ℕ → q.Ω := fun k => ξ (2 * k)

noncomputable def runPt (ℓ : Fin (calls q) → Fin (top q + 1)) (ζ : ℕ → q.Ω) : q.E :=
  (LongTails.Proofs.FullRangeLaw.run (callAdv JJ gg (cfg q)) (levelTime (cfg q).n0)
    (List.ofFn fun i => ((ℓ i : Fin (top q + 1)) : ℕ)) (cfg q).init ζ).2.2.2

noncomputable def costL (ℓ : Fin (calls q) → Fin (top q + 1)) : ℕ :=
  LongTails.Proofs.FullRangeLaw.costOf (levelTime (cfg q).n0) (List.ofFn fun i => ((ℓ i : Fin (top q + 1)) : ℕ))

lemma fullProg_eval_ok (ℓ : Fin (calls q) → Fin (top q + 1)) (ξ : ℕ → q.Ω)
    (hok : seedCost (cfg q).n0 ℓ ≤ (cfg q).limit) :
    let y := ballProj q.x0 (radius q) (runPt q gg JJ ℓ (fun i => ξ (2 * i)))
    let ζ : ℕ → q.Ω := fun i => ξ (2 * costL q ℓ + 2 * i)
    let zhat := innerPath JJ gg (eta q) (gamma0 q) (n0 q) y (levelTime (n0 q) (top q)) ζ
    let pp := y - eta q • LongTails.Proofs.FullRangeCertificate.certFhat gg zhat
      (levelTime (n0 q) (top q)) (batch q) ζ
    Prog.eval (resp gg JJ ξ) (fullProg (cfg q) ℓ) 0 =
      ((JJ (eta q) pp, (eta q)⁻¹ • (pp - JJ (eta q) pp)),
        2 * costL q ℓ + 2 * levelTime (n0 q) (top q) + 2 * batch q + 1) := by
  intro y ζ zhat pp
  unfold fullProg
  split_ifs with h
  swap
  · exact absurd hok h
  rw [eval_bind, loop_eval]
  erw [cert_eval gg JJ ξ (cfg q) _ _ (batch_pos q)]
  simp only [zero_add]
  rfl

lemma fullProg_eval_bad (ℓ : Fin (calls q) → Fin (top q + 1)) (ξ : ℕ → q.Ω)
    (hbad : ¬ seedCost (cfg q).n0 ℓ ≤ (cfg q).limit) :
    let y := q.x0
    let ζ : ℕ → q.Ω := fun i => ξ (2 * i)
    let zhat := innerPath JJ gg (eta q) (gamma0 q) (n0 q) y (levelTime (n0 q) (top q)) ζ
    let pp := y - eta q • LongTails.Proofs.FullRangeCertificate.certFhat gg zhat
      (levelTime (n0 q) (top q)) (batch q) ζ
    Prog.eval (resp gg JJ ξ) (fullProg (cfg q) ℓ) 0 =
      ((JJ (eta q) pp, (eta q)⁻¹ • (pp - JJ (eta q) pp)),
        2 * levelTime (n0 q) (top q) + 2 * batch q + 1) := by
  intro y ζ zhat pp
  unfold fullProg
  split_ifs with h
  · exact absurd h hbad
  erw [cert_eval gg JJ ξ (cfg q) _ _ (batch_pos q)]
  simp only [zero_add]
  rfl

end Exec

end LongTails.Proofs.FullRangeAccuracy
