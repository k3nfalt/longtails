import LongTails.Proofs.SphericalPreferenceOracle
import LongTails.Proofs.GapStrongGrowthIteration
import Mathlib.Analysis.Convex.Jensen

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace NNReal BigOperators

namespace LongTails.Proofs.SphericalPreferenceIteration

open OracleTemplate LongTails.Setups.SphericalRandomUtility LongTails.Algorithms.SphericalPreferenceDescent
open LongTails.Proofs.SphericalPreferenceStep LongTails.Proofs.SphericalPreferenceOracle
open OracleTemplate.ContinuizedSimilarQuasar

abbrev Acc (p : Params) := Feasible p × Point p.d × ℝ≥0

noncomputable def transition (p : Params) (n : ℕ) (f F : Point p.d → ℝ) (o : Feasible p)
    (s : Acc p) (a : Sample p) : Acc p :=
  (project p (s.1.val - (if response p n f s.1 a then stepSize p n else -(stepSize p n)) • a.1.2),
    s.2.1 + s.1.val, s.2.2 + (F s.1.val - F o.val).toNNReal)

noncomputable def start (p : Params) : Acc p := (project p 0,0,0)

noncomputable def potential (p : Params) (n : ℕ) (o : Feasible p) (s : Acc p) : ℝ :=
  ‖s.1.val-o.val‖ ^ 2 + 2*stepSize p n/(192*p.B*Real.sqrt p.d)*(s.2.2 : ℝ)

lemma transition_measurable (p : Params) (n : ℕ) (f F : Point p.d → ℝ) (o : Feasible p)
    (hm : Measurable (Function.uncurry (comparePair (p := p) f))) (hF : Measurable F) :
    Measurable (fun q : Acc p × Sample p => transition p n f F o q.1 q.2) := by
  have hp : Measurable (project p) := (measurable_clip (E := Point p.d) p.R).subtype_mk
  have hproj : Measurable (fun q : Acc p × Sample p => (q.1.1,q.2)) := by fun_prop
  have hb := (measurable_response p n f hm).comp hproj
  have hscale : Measurable (fun q : Acc p × Sample p =>
      if response p n f q.1.1 q.2 then stepSize p n else -(stepSize p n)) :=
    Measurable.ite (hb (measurableSet_singleton true)) measurable_const measurable_const
  have hx : Measurable (fun q : Acc p × Sample p => q.1.1.val) :=
    measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
  have hu : Measurable (fun q : Acc p × Sample p => q.2.1.2) := by fun_prop
  have hnext := hp.comp (hx.sub (hscale.smul hu))
  have hsum : Measurable (fun q : Acc p × Sample p => q.1.2.1+q.1.1.val) :=
    (measurable_fst.comp (measurable_snd.comp measurable_fst)).add hx
  have hcum : Measurable (fun q : Acc p × Sample p => q.1.2.2+(F q.1.1.val-F o.val).toNNReal) :=
    (measurable_snd.comp (measurable_snd.comp measurable_fst)).add
      ((show Measurable Real.toNNReal by fun_prop).comp ((hF.comp hx).sub_const _))
  exact hnext.prodMk (hsum.prodMk hcum)

lemma history (p : Params) (n : ℕ) (f F : Point p.d → ℝ) (o : Feasible p)
    (hmin : IsMinOn F (closedBall 0 p.R) o.val) (k : ℕ) (s : Acc p) (a : Fin k → Sample p) :
    ∃ y : Fin k → Feasible p,
      (iterateSamples (transition p n f F o) k s a).2.1 = s.2.1 + ∑ i, (y i).val ∧
      ((iterateSamples (transition p n f F o) k s a).2.2 : ℝ) = (s.2.2 : ℝ) + ∑ i, (F (y i).val - F o.val) := by
  induction k generalizing s with
  | zero => exact ⟨Fin.elim0, by simp [iterateSamples], by simp [iterateSamples]⟩
  | succ k ih =>
    obtain ⟨y, hy, hz⟩ := ih (transition p n f F o s (a 0)) (fun i => a i.succ)
    refine ⟨Fin.cons s.1 y, ?_, ?_⟩
    · simpa [iterateSamples, Fin.sum_univ_succ, transition, add_assoc] using hy
    · simp [iterateSamples, Fin.sum_univ_succ, transition, Real.toNNReal_of_nonneg
        (sub_nonneg.mpr (hmin s.1.property)), add_assoc] at hz ⊢
      linarith only [hz]

lemma jensen_output (p : Params) (F : Point p.d → ℝ) (hc : ConvexOn ℝ (closedBall 0 p.R) F)
    (o : Feasible p) {k : ℕ} (hk : 0 < k) (y : Fin k → Feasible p) :
    (k : ℝ) * (F (output p k (∑ i, (y i).val)).val - F o.val) ≤ ∑ i, (F (y i).val - F o.val) := by
  let w := fun _ : Fin k => (k : ℝ)⁻¹
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have h0 (i : Fin k) (_ : i ∈ Finset.univ) : 0 ≤ w i := inv_nonneg.mpr hk'.le
  have h1 : ∑ i, w i = 1 := by simp [w, hk'.ne']
  have hj := hc.map_sum_le h0 h1 (fun i _ => (y i).property)
  have hmem := hc.1.sum_mem h0 h1 (fun i _ => (y i).property)
  simp only [w, ← Finset.smul_sum] at hmem hj
  have hproj : (output p k (∑ i, (y i).val)).val = (k : ℝ)⁻¹ • ∑ i, (y i).val :=
    clip_eq_self (mem_closedBall_zero_iff.mp hmem)
  rw [hproj, Finset.sum_sub_distrib]
  simp only [smul_eq_mul] at hj
  have hh := mul_le_mul_of_nonneg_left hj hk'.le
  rw [← mul_assoc, mul_inv_cancel₀ hk'.ne', one_mul] at hh
  simpa [Finset.sum_const, nsmul_eq_mul, mul_sub] using sub_le_sub_right hh ((k : ℝ)*F o.val)

lemma bias_cost (p : Params) {n : ℕ} (hn : 0 < n) (hd : 2 ≤ p.d) (hR : 0 < p.R)
    (hB : 0 < p.B) (x o : Feasible p) :
    let η := stepSize p n
    2*η*(3*radius p n + p.B*(3*radius p n)/(192*p.B*Real.sqrt p.d) +
      2*(p.d : ℝ)*probe p n/radius p n*‖x.val-o.val‖) + η^2 ≤ 6*η^2 := by
  have ht := tuning p hn hd hR
  have hd' : 1 ≤ (p.d : ℝ) := by exact_mod_cast (show 1 ≤ p.d by omega)
  have hds := Real.one_le_sqrt.mpr hd'
  have hns : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have hdist := (norm_sub_le x.val o.val).trans (add_le_add
    (mem_closedBall_zero_iff.mp x.property) (mem_closedBall_zero_iff.mp o.property))
  have hscale : 2*(p.d : ℝ)*probe p n/radius p n = 1/(2*Real.sqrt n) := by
    unfold probe
    field_simp [ht.2.1.ne', hns.ne', show (p.d : ℝ) ≠ 0 by linarith]
    ring
  have hprobe : 2*(p.d : ℝ)*probe p n/radius p n*‖x.val-o.val‖ ≤ stepSize p n := by
    rw [hscale]
    apply (mul_le_mul_of_nonneg_left hdist (by positivity)).trans_eq
    unfold stepSize
    ring
  have hf : p.B*(3*radius p n)/(192*p.B*Real.sqrt p.d) ≤ 3*radius p n := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hds hB.le
    nlinarith only [mul_le_mul_of_nonneg_left h ht.2.1.le,
      mul_nonneg ht.2.1.le hB.le]
  dsimp only
  have hh : 3*radius p n + p.B*(3*radius p n)/(192*p.B*Real.sqrt p.d) +
      2*(p.d : ℝ)*probe p n/radius p n*‖x.val-o.val‖ ≤ 5/2*stepSize p n := by
    linarith only [hf,hprobe,show radius p n = stepSize p n / 4 from rfl]
  nlinarith only [mul_le_mul_of_nonneg_left hh ht.1.le]

lemma potential_step (p : Params) [NeZero p.d] {n : ℕ} (hn : 0 < n) (hd : 2 ≤ p.d)
    (hR : 0 < p.R) (hB : 0 < p.B) (μ : ProbabilityMeasure (Point p.d))
    (hs : Spherical (μ : Measure (Point p.d))) (hq : 1/2 ≤ (μ : Measure (Point p.d)).real (closedBall 0 (2*p.B)))
    (f F : Point p.d → ℝ) (he : EqOn f F (closedBall 0 p.R)) (hL : LipschitzWith ⟨p.B,hB.le⟩ F)
    (hc : ConvexOn ℝ (closedBall 0 p.R) F) (o : Feasible p) (hmin : IsMinOn F (closedBall 0 p.R) o.val)
    (hm : Measurable (Function.uncurry (comparePair (p := p) f))) (s : Acc p) :
    Integrable (fun a => potential p n o (transition p n f F o s a)) (sampleLaw p n μ : Measure _) ∧
      (∫ a, potential p n o (transition p n f F o s a) ∂(sampleLaw p n μ : Measure _)) ≤
        potential p n o s + 6*(stepSize p n)^2 := by
  let P : Measure (Sample p) := sampleLaw p n μ
  let η := stepSize p n
  let K := 192*p.B*Real.sqrt p.d
  let base := ‖s.1.val-o.val‖^2
  have ht := tuning p hn hd hR
  let V := fun a => potential p n o (transition p n f F o s a)
  let c := 2*η/K*((s.2.2 : ℝ)+(F s.1.val-F o.val))
  have hV (a : Sample p) : V a = ‖next p n s.1.val a.1.2 (response p n f s.1 a)-o.val‖^2+c := by
    simp [V,potential,transition,next,c,η,K,Real.toNNReal_of_nonneg (sub_nonneg.mpr (hmin s.1.property))]
  have hVm : Measurable V := by
    have ht' := (transition_measurable p n f F o hm hL.continuous.measurable).comp
      (measurable_const (a := s) |>.prodMk measurable_id)
    exact (show Measurable (potential p n o) by unfold potential; fun_prop).comp ht'
  have hVi : Integrable V P := by
    apply Integrable.of_bound hVm.aestronglyMeasurable ((2*(p.R : ℝ))^2+‖c‖)
    filter_upwards [] with a
    rw [hV]
    apply (norm_add_le _ _).trans
    apply add_le_add _ le_rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have h := norm_clip_le p.R.coe_nonneg
      (s.1.val - (if response p n f s.1 a then η else -η) • a.1.2)
    change ‖next p n s.1.val a.1.2 (response p n f s.1 a)‖ ≤ p.R at h
    exact (norm_sub_le _ _).trans (by linarith only [h,mem_closedBall_zero_iff.mp o.property])
  have hG := gain_integrable p n μ f s.1 o hm
  have hmono := integral_mono_ae hVi (((integrable_const base).sub (hG.const_mul (2*η))).add (integrable_const (η^2+c))) (by
    filter_upwards [direction_ae p n μ] with a ha
    have hd' := projected_step p n s.1.val a.1.2 o (response p n f s.1 a) ha
    rw [hV]
    change _ ≤ base - 2*η*gain p n f s.1 o a + (η^2+c)
    unfold gain
    dsimp only [base,η]
    linarith only [hd'])
  simp only [Pi.sub_apply,Pi.add_apply] at hmono
  change Integrable (gain p n f s.1 o) P at hG
  rw [integral_add (f := fun a => base-2*η*gain p n f s.1 o a) ((integrable_const base).sub (hG.const_mul (2*η))) (integrable_const _), integral_sub (integrable_const _) (hG.const_mul _), integral_const_mul] at hmono
  simp only [integral_const,probReal_univ,one_smul] at hmono
  have hg := gain_bound p hn hd hR hB μ hs hq f F he hL hc s.1 o hmin hm
  have hb := bias_cost p hn hd hR hB s.1 o
  refine ⟨hVi, ?_⟩
  change (∫ a, V a ∂P) ≤ base + 2*η/K*(s.2.2 : ℝ) + 6*η^2
  change _ ≤ ∫ a, gain p n f s.1 o a ∂P at hg
  change (∫ a, V a ∂P) ≤ base - 2*η*(∫ a, gain p n f s.1 o a ∂P) + (η^2+c) at hmono
  dsimp only [c,K,η] at *
  have h := mul_le_mul_of_nonneg_left hg (show 0 ≤ 2*stepSize p n by linarith only [ht.1])
  ring_nf at h hmono hb ⊢
  linarith only [h,hmono,hb]

end LongTails.Proofs.SphericalPreferenceIteration
