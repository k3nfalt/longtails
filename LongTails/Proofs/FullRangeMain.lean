import LongTails.Proofs.FullRangeAccuracy

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.FullRangeMain

open OracleTemplate OracleTemplate.StochasticCohypomonotone
open LongTails.Algorithms.FullRangeMlmc LongTails.Algorithms.FullRangeProgram
open LongTails.Algorithms.FullRangeTuned
open LongTails.Proofs.FullRangeExecution LongTails.Proofs.FullRangeAccuracy LongTails.Proofs.FullRangeGlue
open LongTails.Setups.StochasticCohypomonotoneInclusion (Params reply)

variable (q : Params) (g : q.E → q.Ω → q.E) (J : ℝ → q.E → q.E)

noncomputable def oracleOf (P : ProbabilityMeasure (ℕ → q.Ω)) : Oracle (q.E ⊕ (ℝ × q.E)) q.E :=
  { Seed := fun _ => q.Ω
    law := P
    answer := fun _ qq => reply g J qq.2 }

lemma cost_le (ℓ : Fin (calls q) → Fin (top q + 1)) (ξ : ℕ → q.Ω) :
    (Prog.eval (resp g J ξ) (fullProg (cfg q) ℓ) 0).2 ≤ totalCalls q := by
  by_cases hok : seedCost (cfg q).n0 ℓ ≤ (cfg q).limit
  · rw [fullProg_eval_ok q g J ℓ ξ hok]
    simp only
    have h := seedCost_eq (cfg q).n0 ℓ
    have h2 : 2 * costL q ℓ ≤ seedLimit q := by
      unfold costL
      rw [← h]
      exact hok
    unfold totalCalls
    omega
  · rw [fullProg_eval_bad q g J ℓ ξ hok]
    simp only
    unfold totalCalls
    omega

lemma execute_eq (P : ProbabilityMeasure (ℕ → q.Ω)) (K : ℕ) (hK : totalCalls q ≤ K)
    (ℓ : Fin (calls q) → Fin (top q + 1)) (ξ : ℕ → q.Ω) :
    execute (oracleOf q g J P) (algorithm q) (fun _ => K) ℓ ξ =
      (Prog.eval (resp g J ξ) (fullProg (cfg q) ℓ) 0).1 := by
  rw [StochasticGradient.execute_advance_of_answer (oracleOf q g J P) (algorithm q) K ℓ ξ
    (fun k qq => resp g J ξ k qq.2) (fun _ _ => rfl)]
  have hc := cost_le q g J ℓ ξ
  have hK' : K = (Prog.eval (resp g J ξ) (fullProg (cfg q) ℓ) 0).2 - 0 + (K -
      (Prog.eval (resp g J ξ) (fullProg (cfg q) ℓ) 0).2) := by omega
  change stateOutput q.x0 (StochasticGradient.advance
    (fun k st => stateUpdate st (resp g J ξ k (stateQuery q.x0 st).2)) K 0 (fullProg (cfg q) ℓ)) = _
  rw [hK', stateAdvance]
  rfl

noncomputable def certOut (y : q.E) (ζ : ℕ → q.Ω) : q.E × q.E :=
  let zhat := LongTails.Algorithms.FullRangeMlmc.innerPath J g (eta q) (gamma0 q) (n0 q) y
    (levelTime (n0 q) (top q)) ζ
  let pp := y - eta q • LongTails.Proofs.FullRangeCertificate.certFhat g zhat
    (levelTime (n0 q) (top q)) (batch q) ζ
  (J (eta q) pp, (eta q)⁻¹ • (pp - J (eta q) pp))

noncomputable def outRt (ℓ : Fin (calls q) → Fin (top q + 1)) (ζ : ℕ → q.Ω) : q.E × q.E :=
  if seedCost (cfg q).n0 ℓ ≤ (cfg q).limit then
    certOut q g J (OracleTemplate.LocalHiddenConvex.ballProj q.x0 (radius q) (runPt q g J ℓ ζ))
      (LongTails.Proofs.FullRangeLaw.shift (costL q ℓ) ζ)
  else certOut q g J q.x0 ζ

lemma out_eq (ℓ : Fin (calls q) → Fin (top q + 1)) (ξ : ℕ → q.Ω) :
    (Prog.eval (resp g J ξ) (fullProg (cfg q) ℓ) 0).1 = outRt q g J ℓ (thin q ξ) := by
  unfold outRt
  by_cases hok : seedCost (cfg q).n0 ℓ ≤ (cfg q).limit
  · rw [ite_eq_left hok, fullProg_eval_ok q g J ℓ ξ hok]
    have hz : (fun i => ξ (2 * costL q ℓ + 2 * i)) =
        LongTails.Proofs.FullRangeLaw.shift (costL q ℓ) (thin q ξ) := by
      funext i
      simp only [LongTails.Proofs.FullRangeLaw.shift, thin]
      congr 1
      ring
    simp only
    rw [hz]
    rfl
  · rw [ite_eq_right hok, fullProg_eval_bad q g J ℓ ξ hok]
    rfl

lemma certResidual_eq (F : q.E → q.E) (y : q.E) (ζ : ℕ → q.Ω) :
    ‖F (certOut q g J y ζ).1 + (certOut q g J y ζ).2‖ =
      LongTails.Proofs.FullRangeCertificate.certResidual F J g (eta q) (gamma0 q) (n0 q)
        (levelTime (n0 q) (top q)) (batch q) y ζ := rfl

section Main

variable (hL : 0 < q.L) (hρ : 0 ≤ q.ρ) (hρL : q.ρ * q.L < 1) (hR0 : 0 ≤ q.R)
  (hσ : 0 ≤ q.σ) (hε : 0 < q.ε)
  {F : q.E → q.E} {G : q.E → Set q.E} (H : OpHyp F G J q.L q.ρ)
  (p : ProbabilityMeasure q.Ω)
  (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator (p : Measure q.Ω) F g q.σ)
  (xs : q.E) (hxs : -F xs ∈ G xs) (hR : ‖q.x0 - xs‖ ≤ q.R)

include H hL hρ hρL hg in
lemma certOut_joint :
    Measurable (fun w : q.E × (ℕ → q.Ω) => certOut q g J w.1 w.2) := by
  have hη := LongTails.Proofs.FullRangeTuning.eta_pos q hL hρ
  have ht := LongTails.Proofs.FullRangeTuning.tau_pos q hρL
  have hγ : 0 < gamma0 q := by unfold gamma0; positivity
  have hZ := LongTails.Proofs.FullRangeOperator.innerPath_joint_measurable H hη (n0 := n0 q) g hγ
    hg.measurable (levelTime (n0 q) (top q))
  have hJc : Continuous (J (eta q)) := (LipschitzWith.of_dist_le_mul (K := 1) (by
    intro a b
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using H.res_nonexp hη a b)).continuous
  have hFh : Measurable (fun w : q.E × (ℕ → q.Ω) => LongTails.Proofs.FullRangeCertificate.certFhat g
      (LongTails.Algorithms.FullRangeMlmc.innerPath J g (eta q) (gamma0 q) (n0 q) w.1
        (levelTime (n0 q) (top q)) w.2) (levelTime (n0 q) (top q)) (batch q) w.2) := by
    unfold LongTails.Proofs.FullRangeCertificate.certFhat
    refine (Finset.measurable_sum _ fun i _ => ?_).const_smul _
    exact hg.measurable.comp (hZ.prodMk ((measurable_pi_apply (levelTime (n0 q) (top q) + (i : ℕ))).comp
      measurable_snd))
  have hp : Measurable (fun w : q.E × (ℕ → q.Ω) => w.1 - eta q • LongTails.Proofs.FullRangeCertificate.certFhat g
      (LongTails.Algorithms.FullRangeMlmc.innerPath J g (eta q) (gamma0 q) (n0 q) w.1
        (levelTime (n0 q) (top q)) w.2) (levelTime (n0 q) (top q)) (batch q) w.2) :=
    measurable_fst.sub (hFh.const_smul _)
  unfold certOut
  exact (hJc.measurable.comp hp).prodMk ((hp.sub (hJc.measurable.comp hp)).const_smul _)

include hL hρ hρL hε hxs hR in
lemma fixed_gap (y : q.E) (hy : ‖y - q.x0‖ ≤ radius q) :
    ‖y - LongTails.Proofs.FullRangeResolvent.fixedMap H (LongTails.Proofs.FullRangeTuning.eta_pos q hL hρ)
      (LongTails.Proofs.FullRangeTuning.etaL_lt q hL hρL) (tau q) y‖ ≤ 3 * radius q := by
  have hη := LongTails.Proofs.FullRangeTuning.eta_pos q hL hρ
  have hηL := LongTails.Proofs.FullRangeTuning.etaL_lt q hL hρL
  have ht := LongTails.Proofs.FullRangeTuning.tau_pos q hρL
  have hn := LongTails.Proofs.FullRangeResolvent.fixedMap_nonexpansive H hη hηL ht.le
    (LongTails.Proofs.FullRangeTuning.tau_eta_le q hL hρL) y xs
  rw [LongTails.Proofs.FullRangeResolvent.fixedMap_of_zero H hη hηL _ hxs] at hn
  have hyx : ‖y - xs‖ ≤ 3 * radius q / 2 := by
    have := norm_sub_le_norm_sub_add_norm_sub y q.x0 xs
    have h2 := LongTails.Proofs.FullRangeTuning.radius_half q hL hρ hρL hε
    linarith
  have := norm_sub_le_norm_sub_add_norm_sub y xs
    (LongTails.Proofs.FullRangeResolvent.fixedMap H hη hηL (tau q) y)
  rw [norm_sub_rev xs] at this
  linarith

noncomputable def Cb (hL : 0 < q.L) (hρ : 0 ≤ q.ρ) (hρL : q.ρ * q.L < 1) (H : OpHyp F G J q.L q.ρ)
    (x : q.E) : ℝ :=
  q.ε / 8 + q.ε / 8 + 4 * ‖Tc q hL hρ hρL H x - x‖ / (tau q * eta q)

noncomputable def C0 : ℝ := q.ε / 8 + q.ε / 8 + 3 * radius q / (tau q * eta q)

include H hL hρ hρL hR0 hσ hε hg hxs hR in
lemma per_seed (ℓ : Fin (calls q) → Fin (top q + 1)) :
    ∫⁻ ζ, ENNReal.ofReal ‖F (outRt q g J ℓ ζ).1 + (outRt q g J ℓ ζ).2‖
        ∂Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω)) ≤
      ∫⁻ ζ, ENNReal.ofReal (Cb q J hL hρ hρL H (runPt q g J ℓ ζ))
        ∂Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω)) +
      (if seedCost (cfg q).n0 ℓ ≤ (cfg q).limit then 0 else ENNReal.ofReal (C0 q)) := by
  let μ := Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω)
  have hη := LongTails.Proofs.FullRangeTuning.eta_pos q hL hρ
  have hηL := LongTails.Proofs.FullRangeTuning.etaL_lt q hL hρL
  have ht := LongTails.Proofs.FullRangeTuning.tau_pos q hρL
  have hr := LongTails.Proofs.FullRangeTuning.radius_pos q hL hρ hρL hR0 hε
  have hγ : 0 < gamma0 q := by unfold gamma0; positivity
  have hcert (y : q.E) (hy : ‖y - q.x0‖ ≤ radius q) :=
    cert_point q hL hρ hρL hR0 hσ hε H p g hg xs hxs hR y hy
  have hjoint := certResidual_joint q hL hρ hρL H g hg.measurable
  by_cases hok : seedCost (cfg q).n0 ℓ ≤ (cfg q).limit
  · rw [ite_eq_left hok, add_zero]
    unfold outRt
    simp only [ite_eq_left hok, certResidual_eq]
    have hP : Measurable (OracleTemplate.LocalHiddenConvex.ballProj q.x0 (radius q) : q.E → q.E) :=
      (LipschitzWith.of_dist_le_mul (K := 1) (by
        intro a b
        simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
          LongTails.Proofs.FullRangeClip.ballProj_nonexpansive q.x0 a b hr.le)).continuous.measurable
    let Ψ : St q × (ℕ → q.Ω) → ℝ≥0∞ := fun w => ENNReal.ofReal
      (LongTails.Proofs.FullRangeCertificate.certResidual F J g (eta q) (gamma0 q) (n0 q)
        (levelTime (n0 q) (top q)) (batch q)
        (OracleTemplate.LocalHiddenConvex.ballProj q.x0 (radius q) w.1.2.2.2) w.2)
    have hΨ : Measurable Ψ := ENNReal.measurable_ofReal.comp (hjoint.comp
      ((hP.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))).prodMk
        measurable_snd))
    have htail := LongTails.Proofs.FullRangeLaw.tail_lintegral (p : Measure q.Ω) (callAdv J g (cfg q))
      (levelTime (cfg q).n0) (fun l => callAdv_measurable q H g hg.measurable hη hγ hr.le l)
      (fun s l ξ ξ' h => callAdv_dep q (J := J) g s l ξ ξ' h)
      (List.ofFn fun i => ((ℓ i : Fin (top q + 1)) : ℕ)) (cfg q).init Ψ hΨ
    change ∫⁻ ζ, Ψ (LongTails.Proofs.FullRangeLaw.run (callAdv J g (cfg q)) (levelTime (cfg q).n0)
      (List.ofFn fun i => ((ℓ i : Fin (top q + 1)) : ℕ)) (cfg q).init ζ,
      LongTails.Proofs.FullRangeLaw.shift (costL q ℓ) ζ) ∂μ ≤ _
    erw [htail]
    refine lintegral_mono fun ζ => ?_
    set x := runPt q g J ℓ ζ
    set y := OracleTemplate.LocalHiddenConvex.ballProj q.x0 (radius q) x
    have hy : ‖y - q.x0‖ ≤ radius q := by
      have := OracleTemplate.LocalHiddenConvex.ballProj_mem q.x0 x hr.le
      rwa [Metric.mem_closedBall, dist_eq_norm] at this
    have hc := hcert y hy
    change ∫⁻ ζ', ENNReal.ofReal (LongTails.Proofs.FullRangeCertificate.certResidual F J g (eta q)
      (gamma0 q) (n0 q) (levelTime (n0 q) (top q)) (batch q) y ζ') ∂μ ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hc.1 (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    refine hc.2.trans ?_
    have hxs2 : ‖xs - q.x0‖ ≤ radius q / 2 := by
      rw [norm_sub_rev]; exact hR.trans (LongTails.Proofs.FullRangeTuning.radius_half q hL hρ hρL hε)
    have hclip := LongTails.Proofs.FullRangeClip.clip_terminal
      (fun a b => LongTails.Proofs.FullRangeResolvent.fixedMap_nonexpansive H hη hηL ht.le
        (LongTails.Proofs.FullRangeTuning.tau_eta_le q hL hρL) a b) q.x0 xs x hr hxs2
      (LongTails.Proofs.FullRangeResolvent.fixedMap_of_zero H hη hηL _ hxs)
    have hTc : Tc q hL hρ hρL H x = LongTails.Proofs.FullRangeResolvent.fixedMap H hη hηL (tau q) y := rfl
    unfold Cb
    rw [hTc, norm_sub_rev y]
    have hte : 0 < tau q * eta q := by positivity
    have := div_le_div_of_nonneg_right hclip hte.le
    linarith
  · rw [ite_eq_right hok]
    unfold outRt
    simp only [ite_eq_right hok, certResidual_eq]
    have hx0 : ‖q.x0 - q.x0‖ ≤ radius q := by simp [hr.le]
    have hc := hcert q.x0 hx0
    rw [← ofReal_integral_eq_lintegral_ofReal hc.1 (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    refine le_add_left (ENNReal.ofReal_le_ofReal (hc.2.trans ?_))
    have hgap := fixed_gap q J hL hρ hρL hε H xs hxs hR q.x0 hx0
    unfold C0
    have hte : 0 < tau q * eta q := by positivity
    have := div_le_div_of_nonneg_right hgap hte.le
    linarith

include H in
lemma certOut_mem (hη : 0 < eta q) (y : q.E) (ζ : ℕ → q.Ω) :
    (certOut q g J y ζ).2 ∈ G (certOut q g J y ζ).1 := by
  unfold certOut
  exact H.res _ _ hη

include H hL hρ hρL hR0 hε hg in
lemma outRt_measurable (ℓ : Fin (calls q) → Fin (top q + 1)) : Measurable (outRt q g J ℓ) := by
  have hη := LongTails.Proofs.FullRangeTuning.eta_pos q hL hρ
  have ht := LongTails.Proofs.FullRangeTuning.tau_pos q hρL
  have hr := LongTails.Proofs.FullRangeTuning.radius_pos q hL hρ hρL hR0 hε
  have hγ : 0 < gamma0 q := by unfold gamma0; positivity
  have hco := certOut_joint q g J hL hρ hρL H p hg
  unfold outRt
  by_cases hok : seedCost (cfg q).n0 ℓ ≤ (cfg q).limit
  · simp only [ite_eq_left hok]
    have hP : Measurable (OracleTemplate.LocalHiddenConvex.ballProj q.x0 (radius q) : q.E → q.E) :=
      (LipschitzWith.of_dist_le_mul (K := 1) (by
        intro a b
        simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
          LongTails.Proofs.FullRangeClip.ballProj_nonexpansive q.x0 a b hr.le)).continuous.measurable
    have hrun := (LongTails.Proofs.FullRangeLaw.run_measurable (callAdv J g (cfg q)) (levelTime (cfg q).n0)
      (fun l => callAdv_measurable q H g hg.measurable hη hγ hr.le l)
      (List.ofFn fun i => ((ℓ i : Fin (top q + 1)) : ℕ))).comp
        (measurable_const.prodMk measurable_id : Measurable (fun ζ : ℕ → q.Ω => ((cfg q).init, ζ)))
    have hpt : Measurable (runPt q g J ℓ) :=
      measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hrun))
    exact hco.comp ((hP.comp hpt).prodMk (LongTails.Proofs.FullRangeLaw.shift_measurable _))
  · simp only [ite_eq_right hok]
    exact hco.comp (measurable_const.prodMk measurable_id)

include H hL hρ hρL hR0 hσ hε hg hxs hR in
lemma main_lintegral (P : Measure (ℕ → q.Ω)) [IsProbabilityMeasure P]
    (hind : ProbabilityTheory.iIndepFun (fun k (ξ : ℕ → q.Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ => ξ k) = (p : Measure q.Ω)) :
    ∫⁻ w, ENNReal.ofReal ‖F (outRt q g J w.1 (thin q w.2)).1 + (outRt q g J w.1 (thin q w.2)).2‖
      ∂((Measure.pi fun _ : Fin (calls q) => LongTails.Proofs.FullRangeEstimator.levelLaw (top q)).prod P)
      ≤ ENNReal.ofReal q.ε := by
  let Q := Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω)
  let ν := Measure.pi fun _ : Fin (calls q) => LongTails.Proofs.FullRangeEstimator.levelLaw (top q)
  have hη := LongTails.Proofs.FullRangeTuning.eta_pos q hL hρ
  have ht := LongTails.Proofs.FullRangeTuning.tau_pos q hρL
  have hr := LongTails.Proofs.FullRangeTuning.radius_pos q hL hρ hρL hR0 hε
  have hγ : 0 < gamma0 q := by unfold gamma0; positivity
  have hte : 0 < tau q * eta q := by positivity
  have hF : Continuous F := (LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]; exact H.lip a b).continuous
  have hout := outRt_measurable q g J hL hρ hρL hR0 hε H p hg
  have hthin : MeasurePreserving (thin q) P Q := thin_preserving (p : Measure q.Ω) P hind hmarg
  let f : (Fin (calls q) → Fin (top q + 1)) → (ℕ → q.Ω) → ℝ≥0∞ := fun ℓ ζ =>
    ENNReal.ofReal ‖F (outRt q g J ℓ ζ).1 + (outRt q g J ℓ ζ).2‖
  have hf : ∀ ℓ, Measurable (f ℓ) := fun ℓ => ENNReal.measurable_ofReal.comp
    ((hF.measurable.comp (measurable_fst.comp (hout ℓ))).add (measurable_snd.comp (hout ℓ))).norm
  have hjm : Measurable (fun w : (Fin (calls q) → Fin (top q + 1)) × (ℕ → q.Ω) => f w.1 (thin q w.2)) :=
    measurable_from_prod_countable_right (fun ℓ => (hf ℓ).comp hthin.measurable)
  change ∫⁻ w, f w.1 (thin q w.2) ∂(ν.prod P) ≤ _
  rw [lintegral_prod _ hjm.aemeasurable]
  have h1 : ∀ ℓ, ∫⁻ ξ, f ℓ (thin q ξ) ∂P = ∫⁻ ζ, f ℓ ζ ∂Q := fun ℓ => hthin.lintegral_comp (hf ℓ)
  rw [lintegral_congr fun ℓ => h1 ℓ]
  -- the ideal-run part
  have hTc : Continuous (Tc q hL hρ hρL H) := (LipschitzWith.of_dist_le_mul (K := 1) (by
    intro a b
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using Tc_nonexp q hL hρ hρL H hε hR0 a b)).continuous
  have hCb : Continuous (Cb q J hL hρ hρL H) := by
    unfold Cb
    exact (continuous_const.add continuous_const).add
      ((((hTc.sub continuous_id).norm).const_smul (4 : ℝ)).div_const _)
  let Φ : St q → ℝ≥0∞ := fun s => ENNReal.ofReal (Cb q J hL hρ hρL H s.2.2.2)
  have hΦ : Measurable Φ := ENNReal.measurable_ofReal.comp
    (hCb.measurable.comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  have hA : ∫⁻ ℓ, ∫⁻ ζ, ENNReal.ofReal (Cb q J hL hρ hρL H (runPt q g J ℓ ζ)) ∂Q ∂ν ≤
      ENNReal.ofReal (q.ε / 4 + q.ε / 32) := by
    have hlev := LongTails.Proofs.FullRangeLaw.level_lintegral (p : Measure q.Ω) (callAdv J g (cfg q))
      (levelTime (cfg q).n0) (fun l => callAdv_measurable q H g hg.measurable hη hγ hr.le l)
      (fun s l ξ ξ' h => callAdv_dep q (J := J) g s l ξ ξ' h)
      (LongTails.Proofs.FullRangeEstimator.levelLaw (top q)) (calls q) (cfg q).init Φ hΦ
    change ∫⁻ ℓ, ∫⁻ ζ, Φ (LongTails.Proofs.FullRangeLaw.run (callAdv J g (cfg q)) (levelTime (cfg q).n0)
      (List.ofFn fun i => ((ℓ i : Fin (top q + 1)) : ℕ)) (cfg q).init ζ) ∂Q ∂ν ≤ _
    erw [hlev]
    obtain ⟨hi, hb⟩ := anchor_accuracy q hL hρ hρL hR0 hε H p g hg xs hxs hR
    have hci : Integrable (fun θ => Cb q J hL hρ hρL H (ideal q (J := J) g θ).2.2.2)
        (Measure.pi fun _ : Fin (calls q) => thetaLaw q p) := by
      unfold Cb
      exact ((integrable_const _).add (integrable_const _)).add ((hi.const_mul 4).div_const _)
    change ∫⁻ θ, ENNReal.ofReal (Cb q J hL hρ hρL H (ideal q (J := J) g θ).2.2.2)
      ∂(Measure.pi fun _ : Fin (calls q) => thetaLaw q p) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hci (Filter.Eventually.of_forall fun θ => by
      unfold Cb; positivity)]
    apply ENNReal.ofReal_le_ofReal
    unfold Cb
    rw [integral_add (f := fun _ => q.ε / 8 + q.ε / 8) (integrable_const _) ((hi.const_mul 4).div_const _),
      integral_div, integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hs := LongTails.Proofs.FullRangeTuning.cert_scale q hL hρ hρL hε
    have h4 : 4 * (∫ θ, ‖Tc q hL hρ hρL H (ideal q (J := J) g θ).2.2.2 - (ideal q (J := J) g θ).2.2.2‖
        ∂Measure.pi fun _ : Fin (calls q) => thetaLaw q p) / (tau q * eta q) ≤
        4 * epsT q / (tau q * eta q) := by
      apply div_le_div_of_nonneg_right _ hte.le
      linarith
    linarith
  have hB : ∫⁻ ℓ, (if seedCost (cfg q).n0 ℓ ≤ (cfg q).limit then 0 else ENNReal.ofReal (C0 q)) ∂ν ≤
      ENNReal.ofReal (q.ε / 8) := by
    have heq : (fun ℓ : Fin (calls q) → Fin (top q + 1) =>
        if seedCost (cfg q).n0 ℓ ≤ (cfg q).limit then (0 : ℝ≥0∞) else ENNReal.ofReal (C0 q)) =
        Set.indicator {ℓ | (cfg q).limit < seedCost (cfg q).n0 ℓ} (fun _ => ENNReal.ofReal (C0 q)) := by
      funext ℓ
      by_cases h : seedCost (cfg q).n0 ℓ ≤ (cfg q).limit
      · simp [h, Set.indicator, not_lt.mpr h]
      · simp [h, Set.indicator, lt_of_not_ge h]
    rw [heq, lintegral_indicator_const (Set.to_countable _).measurableSet]
    have hd := LongTails.Proofs.FullRangeTuning.failure_pos q hL hρ hρL hR0 hε
    have htl := LongTails.Proofs.FullRangeSeed.seed_tail (calls q) (top q) (n0 q) hd
    have hC0 : 0 ≤ C0 q := by unfold C0; positivity
    calc ENNReal.ofReal (C0 q) * ν {ℓ | (cfg q).limit < seedCost (cfg q).n0 ℓ}
        ≤ ENNReal.ofReal (C0 q) * ENNReal.ofReal (failureProb q) := by
          gcongr
          exact htl
      _ = ENNReal.ofReal (failureProb q * C0 q) := by rw [← ENNReal.ofReal_mul hC0, mul_comm]
      _ ≤ ENNReal.ofReal (q.ε / 8) := ENNReal.ofReal_le_ofReal
          (LongTails.Proofs.FullRangeTuning.failure_tolerance q hL hρ hρL hR0 hε)
  have hmA : Measurable (fun ℓ : Fin (calls q) → Fin (top q + 1) =>
      ∫⁻ ζ, ENNReal.ofReal (Cb q J hL hρ hρL H (runPt q g J ℓ ζ)) ∂Q) := measurable_of_countable _
  calc ∫⁻ ℓ, ∫⁻ ζ, f ℓ ζ ∂Q ∂ν
      ≤ ∫⁻ ℓ, (∫⁻ ζ, ENNReal.ofReal (Cb q J hL hρ hρL H (runPt q g J ℓ ζ)) ∂Q +
          (if seedCost (cfg q).n0 ℓ ≤ (cfg q).limit then 0 else ENNReal.ofReal (C0 q))) ∂ν :=
        lintegral_mono fun ℓ => per_seed q g J hL hρ hρL hR0 hσ hε H p hg xs hxs hR ℓ
    _ = ∫⁻ ℓ, ∫⁻ ζ, ENNReal.ofReal (Cb q J hL hρ hρL H (runPt q g J ℓ ζ)) ∂Q ∂ν +
          ∫⁻ ℓ, (if seedCost (cfg q).n0 ℓ ≤ (cfg q).limit then 0 else ENNReal.ofReal (C0 q)) ∂ν :=
        lintegral_add_left hmA _
    _ ≤ ENNReal.ofReal (q.ε / 4 + q.ε / 32) + ENNReal.ofReal (q.ε / 8) := add_le_add hA hB
    _ ≤ ENNReal.ofReal q.ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        linarith

end Main

end LongTails.Proofs.FullRangeMain
