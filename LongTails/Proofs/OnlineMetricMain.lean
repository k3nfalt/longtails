import LongTails.Proofs.OnlineMetricLedger

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} {μ fstar : ℝ}
  {xstar x0 : EuclideanSpace ℝ (Fin d)} {b0 : Fin d → ℝ}

noncomputable def macroStep [NeZero d] (fstar : ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (s : Core d) : Core d :=
  resolve fstar s (firstQuery x0 s) (f (firstQuery x0 s)) (gradient f (firstQuery x0 s))
    (f (secondQuery x0 s (firstQuery x0 s) (gradient f (firstQuery x0 s))))
    (gradient f (secondQuery x0 s (firstQuery x0 s) (gradient f (firstQuery x0 s))))

lemma macroStep_main [NeZero d] {s : Core d} (h : s.stage = d) :
    macroStep fstar x0 f s =
      mainResolve fstar s (extrapolate s) (f (extrapolate s)) (gradient f (extrapolate s))
        (f (trialPoint s (extrapolate s) (gradient f (extrapolate s))))
        (gradient f (trialPoint s (extrapolate s) (gradient f (extrapolate s)))) := by
  have hn : ¬ s.stage < d := by omega
  simp [macroStep, resolve, firstQuery, secondQuery, hn]

lemma inv_macro [NeZero d] {s : Core d} {n : ℕ} (H : Hyp f w μ fstar xstar) (hd : 1 ≤ (d : ℝ))
    (I : Inv f w μ fstar x0 b0 s n) :
    Inv f w μ fstar x0 b0 (macroStep fstar x0 f s) (n + 1) := by
  rw [macroStep_main I.stage]
  unfold mainResolve
  split_ifs with hacc hhalf hbox
  · rw [endEpoch_eq]
    cases hR : s.prev with
    | none =>
      have ht : resolvePrev fstar s (trialPoint s (extrapolate s) (gradient f (extrapolate s))) =
          s := by simp [resolvePrev, hR]
      rw [ht]
      exact inv_epochNext H hd I rfl rfl rfl I.band0 I.band1 rfl hhalf (ledger_first I hR _ _)
    | some R0 =>
      by_cases heq : R0.seg = s.seg
      · have ht : resolvePrev fstar s (trialPoint s (extrapolate s) (gradient f (extrapolate s))) =
            feedLearner s (s.ep + 1) (lossGrad (recordLoss fstar R0
              (trialPoint s (extrapolate s) (gradient f (extrapolate s)))) R0.cuts R0.φ) := by
          simp [resolvePrev, hR, heq]
        rw [ht]
        set γ := lossGrad (recordLoss fstar R0
          (trialPoint s (extrapolate s) (gradient f (extrapolate s)))) R0.cuts R0.φ
        obtain ⟨hb, hseg, -, -, hstage⟩ := feedLearner_fields s (s.ep + 1) γ
        have hbands : BandOK (feedLearner s (s.ep + 1) γ).learner0 ∧
            BandOK (feedLearner s (s.ep + 1) γ).learner1 := by
          have hlo := bandLo_le_bandHi hd
          unfold feedLearner
          split_ifs
          · exact ⟨learnerStep_band hlo _ I.band0.2 γ, I.band1⟩
          · exact ⟨I.band0, learnerStep_band hlo _ I.band1.2 γ⟩
        exact inv_epochNext H hd I hb hseg hstage hbands.1 hbands.2
          (feedLearner_other s s.ep γ) hhalf (ledger_feed H hd I hR heq _ hhalf)
      · have ht : resolvePrev fstar s (trialPoint s (extrapolate s) (gradient f (extrapolate s))) =
            s := by simp [resolvePrev, hR, heq]
        rw [ht]
        exact inv_epochNext H hd I rfl rfl rfl I.band0 I.band1 rfl hhalf
          (ledger_drop I hR heq _ _)
  · exact inv_continue H hd I hacc hhalf
  · exact inv_box H hd I hacc hbox
  · exact inv_cut H hd I hacc hbox

lemma inv_iterate [NeZero d] {s : Core d} (H : Hyp f w μ fstar xstar) (hd : 1 ≤ (d : ℝ))
    (I : Inv f w μ fstar x0 b0 s 0) (n : ℕ) :
    Inv f w μ fstar x0 b0 ((macroStep fstar x0 f)^[n] s) n := by
  induction n with
  | zero => exact I
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact inv_macro H hd ih

end OracleTemplate.OnlineMetricAccelerated
