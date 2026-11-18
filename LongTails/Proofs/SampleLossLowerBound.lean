import LongTails.Proofs.SampleLossSimulation
import LongTails.Proofs.SampleLossObservations

open MeasureTheory OracleTemplate
open LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
open LongTails.Proofs.SampleLossFrame LongTails.Proofs.SampleLossScaling
open LongTails.Proofs.SampleLossInstance LongTails.Proofs.SampleLossEpoch
open LongTails.Proofs.SampleLossSimulation LongTails.Proofs.SampleLossObservations

namespace LongTails.Proofs.SampleLossLowerBound


lemma summed_residual (q : Params) (hq : spec.valid q) (A : Method q) (b : ℕ)
    (hb : b ≤ (stages q)^3) (s : A.Seed) (ξ : ℕ → Index q) :
    2*q.ε*(Fintype.card (Hidden q) : ℝ) ≤ ∑ π : Hidden q,
      ‖gradient (objective q π) (execute (oracle q π) A (fun _ => b) s ξ)‖ := by
  classical
  let n := stages q
  have hn : 0 < n := stages_pos hq
  have hε := hq.2.2.1
  let pos := point q A s ξ b
  let stage := pointStage q (b:=b)
  have hc : Fintype.card (Point b) ≤ 2*(stages q)^3+1 := by
    simpa [Point, Nat.mul_comm, Nat.add_comm] using (show b*2+1 ≤ (stages q)^3*2+1 by omega)
  have hcnt := bad_count ξ stage pos (point_stable q hq A s ξ hb) hc (extra:=q.extraWidth) rfl
  let F (π : Hidden q) := ‖gradient (objective q π) (execute (oracle q π) A (fun _ => b) s ξ)‖
  have hnorm (π : Hidden q) : 4*q.ε * (1 - (if bad ξ stage pos π then (1:ℝ) else 0)) ≤ F π := by
    by_cases h : bad ξ stage pos π
    · simp [h,F]
    · have small := good_small ξ stage pos π h
      have he := sim_execute q hq A s ξ π b hb small
      have hl : n-1 < n := by omega
      let j : Fin n := ⟨n-1,hl⟩
      have hh := small none j le_rfl
      let out := A.output (simulated q A s ξ π b)
      have hbar := mean_barrier π (NeZero.pos _) (1+Real.sqrt (rows n)) (dilation q • out)
        ⟨j.val,j.isLt, hh.trans (by norm_num)⟩
      have hder := (stretch_gradient (amplitude q) (dilation q) (mean_differentiable π (1+Real.sqrt (rows n))) out).gradient
      change 4*q.ε*(1-(if bad ξ stage pos π then 1 else 0)) ≤ ‖gradient (objective q π) _‖
      rw [ite_eq_right h, sub_zero,mul_one,he]
      change _ ≤ ‖gradient (stretch _ _ _) out‖
      rw [hder,(scaling hq).2.2.1,norm_smul,Real.norm_of_nonneg (by positivity)]
      nlinarith [mul_pos hε (show 0 < ‖gradient (mean π (1+Real.sqrt (rows n))) (dilation q • out)‖ - 1/8 by linarith)]
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun π _ => hnorm π)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hsum
  exact le_trans (by nlinarith [mul_le_mul_of_nonneg_left hcnt hε.le]) hsum

lemma hard_instance (q : Params) (hq : spec.valid q) (A : Method q) (b : Fin 1 → ℕ)
    (hb : b 0 ≤ (stages q)^3) :
    ∃ π : Hidden q, ¬ spec.successful q (objective q π)
      (fun s : A.Seed × (ℕ → Index q) => execute (oracle q π) A b s.1 s.2)
      ⟨(A.law : Measure _).prod (tape q : Measure _), inferInstance⟩ := by
  classical
  by_contra! hall
  let μ : Measure (A.Seed × (ℕ → Index q)) := (A.law : Measure A.Seed).prod (tape q : Measure (ℕ → Index q))
  let F (π : Hidden q) (s : A.Seed × (ℕ → Index q)) :=
    ‖gradient (objective q π) (execute (oracle q π) A b s.1 s.2)‖
  have hi (π : Hidden q) : Integrable (F π) μ := (hall π).2.1
  have he (π : Hidden q) : ∫ s, F π s ∂μ ≤ q.ε := (hall π).2.2
  have hsum (s : A.Seed × (ℕ → Index q)) : 2*q.ε*(Fintype.card (Hidden q) : ℝ) ≤ ∑ π, F π s := by
    have h := summed_residual q hq A (b 0) hb s.1 s.2
    have hb' : (fun _ : Fin 1 => b 0) = b := funext fun i => congrArg b (Subsingleton.elim _ i)
    simpa only [hb',F] using h
  have low := integral_mono (μ:=μ) (integrable_const _) (integrable_finsetSum _ (fun π _ => hi π)) hsum
  rw [integral_const,probReal_univ,one_smul,integral_finsetSum _ (fun π _ => hi π)] at low
  have high := Finset.sum_le_sum (s:=Finset.univ) (fun π _ => he π)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at high
  have : Nonempty (Hidden q) := ⟨fun _ => ⟨0, Nat.zero_lt_succ _⟩⟩
  have hc : 0 < (Fintype.card (Hidden q):ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  nlinarith [mul_pos hq.2.2.1 hc]

end LongTails.Proofs.SampleLossLowerBound
