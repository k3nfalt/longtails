import LongTails.Proofs.SampleLossScaling
import LongTails.Proofs.AdaptiveIID
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory OracleTemplate
open LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
open LongTails.Proofs.SampleLossFrame LongTails.Proofs.SampleLossScaling
open LongTails.Proofs.SampleLossChain LongTails.Proofs.SampleLossRegularity

namespace LongTails.Proofs.SampleLossInstance


instance rows_nonzero (n : ℕ) : NeZero (rows n) := ⟨by unfold rows; positivity⟩

abbrev Hidden (q : Params) := Table (stages q) (rows (stages q)) (width (stages q) q.extraWidth)

abbrev Domain (q : Params) := (parameters q).E

abbrev Index (q : Params) := Fin (rows (stages q))

noncomputable def component {n m d : ℕ} (π : Table n m d) (i : Fin m) : Space n m d → ℝ :=
  sampleLoss proj (direction π) (payload π i) (1+Real.sqrt m) n

noncomputable def objective (q : Params) (π : Hidden q) : Domain q → ℝ :=
  stretch (amplitude q) (dilation q) (mean π (1+Real.sqrt (rows (stages q))))

noncomputable def loss (q : Params) (π : Hidden q) (i : Index q) : Domain q → ℝ :=
  stretch (amplitude q) (dilation q) (component π i)

noncomputable def marginal (q : Params) : ProbabilityMeasure (Index q) :=
  ⟨(PMF.uniformOfFintype _).toMeasure, inferInstance⟩

noncomputable def tape (q : Params) : ProbabilityMeasure (ℕ → Index q) :=
  ⟨Measure.infinitePi (fun _ : ℕ => (marginal q : Measure _)), inferInstance⟩

noncomputable def oracle (q : Params) (π : Hidden q) : Oracle (Domain q × Domain q) (Domain q × Domain q) where
  Seed _ := Index q
  law := tape q
  answer _ xy i := (gradient (loss q π i) xy.2.1, gradient (loss q π i) xy.2.2)

lemma loss_deriv (q : Params) (π : Hidden q) (i : Index q) (x : Domain q) :
    HasGradientAt (loss q π i)
      ((amplitude q*dilation q) • gradient (component π i) (dilation q • x)) x :=
  stretch_gradient _ _ (sampleLoss_differentiable _ _ _ _ _) _

lemma loss_smooth (q : Params) (hq : spec.valid q) (π : Hidden q) (i : Index q) (x y : Domain q) :
    ‖gradient (loss q π i) x - gradient (loss q π i) y‖ ≤ q.L * ‖x-y‖ := by
  obtain ⟨ha,hr,_,_,hL⟩ := scaling hq
  let m := rows (stages q)
  have hm : 0 < m := NeZero.pos _
  have h := sampleLoss_smooth proj (direction_le π hm) (payload_le π hm i)
    (by positivity : 0 ≤ 1+Real.sqrt m) (stages q) (fun v => (proj_energy v).le)
    (dilation q • x) (dilation q • y)
  rw [(loss_deriv q π i x).gradient,(loss_deriv q π i y).gradient,← smul_sub,norm_smul,
    Real.norm_of_nonneg (mul_pos ha hr).le]
  rw [← smul_sub,norm_smul,Real.norm_of_nonneg hr.le] at h
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_left h (mul_pos ha hr).le
    _ ≤ q.L * ‖x-y‖ := by
      convert mul_le_mul_of_nonneg_right hL (norm_nonneg (x-y)) using 1
      ring

lemma objective_integral (q : Params) (π : Hidden q) (x : Domain q) :
    objective q π x = ∫ i, loss q π i x ∂(marginal q : Measure _) := by
  let n := stages q
  let m := rows n
  have hm : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  change _ = ∫ i, loss q π i x ∂(PMF.uniformOfFintype (Fin m)).toMeasure
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    loss, stretch, component, sampleLoss, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  unfold objective stretch mean
  erw [perturbation_centered π (NeZero.pos _) (dilation q • x) (stages q)]
  field_simp
  ring

lemma admissible (q : Params) (hq : spec.valid q) (π : Hidden q) :
    spec.admissible q (objective q π) (oracle q π) := by
  refine ⟨loss q π, fun x i => gradient (loss q π i) x, marginal q, tape q,
    StochasticGeneralized.infinitePi_iid (marginal q : Measure (Index q)), rfl, ?_, ?_, ?_, ?_, fun x => (show Integrable (fun i : Index q => loss q π i x) (marginal q : Measure _) from Integrable.of_finite),
    objective_integral q π, ?_⟩
  · intro i x
    apply mul_nonneg (scaling hq).1.le
    exact sampleLoss_nonneg proj (direction_le π (NeZero.pos _)) (payload_le π (NeZero.pos _) i) (show 0 ≤ 1+Real.sqrt (rows (stages q)) by positivity) _ _
  · intro i x
    exact (loss_deriv q π i x).differentiableAt.hasGradientAt
  · exact loss_smooth q hq π
  · apply measurable_from_prod_countable_left
    intro i
    have hl : LipschitzWith (⟨q.L,hq.1.le⟩ : NNReal) (gradient (loss q π i)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [dist_eq_norm]
      exact loss_smooth q hq π i x y
    exact hl.continuous.measurable
  · change amplitude q * mean π _ (dilation q • 0) ≤ q.Δ
    rw [smul_zero]
    exact (mul_le_mul_of_nonneg_left (mean_zero_le π _) (scaling hq).1.le).trans (scaling hq).2.2.2.1

end LongTails.Proofs.SampleLossInstance
