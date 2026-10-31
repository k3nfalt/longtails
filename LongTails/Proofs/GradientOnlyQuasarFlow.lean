import LongTails.Proofs.GradientOnlyQuasarWeights
import LongTails.Proofs.GradientOnlyQuasarEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GradientOnlyQuasar

open LongTails.Setups.GradientOnlyGeneralizedQuasar

lemma flow_zero {q : Params} (hv : spec.valid q) (s : ℝ × q.E × q.E) : flow q s 0 = s := by
  simp [flow, ne_of_gt (weight_pos hv s.1)]

lemma flow_primal_hasDerivAt {q : Params} (hv : spec.valid q)
    (s : ℝ × q.E × q.E) (h : ℝ) :
    HasDerivAt (fun t => (flow q s t).2.1)
      ((mirrorStep q (s.1 + h) / weight q (s.1 + h)) •
        (s.2.2 - (flow q s h).2.1)) h := by
  have hγ : q.γ ≠ 0 := ne_of_gt hv.2.2.2.2.1
  have hw0 : 0 < weight q s.1 := weight_pos hv _
  have hwt : 0 < weight q (s.1 + h) := weight_pos hv _
  have hr : 0 < weight q s.1 / weight q (s.1 + h) := div_pos hw0 hwt
  have hw : HasDerivAt (fun t => weight q (s.1 + t))
      (q.γ * mirrorStep q (s.1 + h)) h := by
    convert! (hasDerivAt_weight hv (s.1 + h)).comp h ((hasDerivAt_id h).const_add s.1) using 1
    simp
  have hd := (hasDerivAt_const h (weight q s.1)).div hw (ne_of_gt hwt)
  have hp : HasDerivAt (fun t => (weight q s.1 / weight q (s.1 + t)) ^ (1 / q.γ))
      (-(mirrorStep q (s.1 + h) / weight q (s.1 + h)) *
        (weight q s.1 / weight q (s.1 + h)) ^ (1 / q.γ)) h := by
    convert! hd.rpow_const (Or.inl (ne_of_gt hr)) using 1
    simp only [Pi.div_apply]
    rw [Real.rpow_sub_one (ne_of_gt hr)]
    field_simp
    ring
  have hh := (hp.smul_const (s.2.1 - s.2.2)).const_add s.2.2
  convert! hh using 1
  simp only [flow]
  module

lemma flow_energy_hasDerivAt {q : Params} (hv : spec.valid q) {f : q.E → ℝ}
    (hf : ∀ y, HasGradientAt f (gradient f y) y)
    (s : ℝ × q.E × q.E) (u : q.E) (h : ℝ) :
    HasDerivAt (fun t => weightedEnergy f u (weight q (s.1 + t))
      (flow q s t).2.1 s.2.2)
      (q.γ * mirrorStep q (s.1 + h) * (f (flow q s h).2.1 - f u) +
        mirrorStep q (s.1 + h) *
          ⟪gradient f (flow q s h).2.1, s.2.2 - (flow q s h).2.1⟫) h := by
  have hy := flow_primal_hasDerivAt hv s h
  have hfy := (hf (flow q s h).2.1).hasFDerivAt.comp_hasDerivAt h hy
  have hw : HasDerivAt (fun t => weight q (s.1 + t))
      (q.γ * mirrorStep q (s.1 + h)) h := by
    convert! (hasDerivAt_weight hv (s.1 + h)).comp h ((hasDerivAt_id h).const_add s.1) using 1
    simp
  have hh := (hw.mul (hfy.sub_const (f u))).add_const (‖s.2.2 - u‖ ^ 2 / 2)
  convert! hh using 1
  simp only [InnerProductSpace.toDual_apply_apply, inner_smul_right, Function.comp_apply]
  field_simp [ne_of_gt (weight_pos hv (s.1 + h))]

lemma scheduled_descent {q : Params} (hv : spec.valid q) {f : q.E → ℝ}
    (hf : ∀ y, HasGradientAt f (gradient f y) y) (hg : Continuous (gradient f))
    (hs : CompositeGeneralized.SymmetricSmooth (gradient f) q.L0 q.L1)
    {u y z : q.E} {t : ℝ} (hm : IsMinOn f univ u)
    (hP : weightedEnergy f u (weight q t) y z ≤ energyLevel q) :
    f (y - (1 / curvature q t) • gradient f y) ≤
      f y - ‖gradient f y‖ ^ 2 / (2 * curvature q t) := by
  have hgap : f y - f u ≤ energyLevel q / weight q t := by
    apply (le_div_iff₀ (weight_pos hv t)).2
    unfold weightedEnergy at hP
    nlinarith [sq_nonneg ‖z - u‖]
  have hd := local_gradient_descent hv.1 hv.2.1
    (div_nonneg (energyLevel_pos hv).le (weight_pos hv t).le) hf hg hs hm hgap
  have hdouble : 2 * curvature q t =
      256 * (q.L0 + q.L1 ^ 2 * (energyLevel q / weight q t)) := by unfold curvature; ring
  have hcurv : curvature q t =
      128 * (q.L0 + q.L1 ^ 2 * (energyLevel q / weight q t)) := by unfold curvature; ring
  rw [hdouble, hcurv]
  exact hd

lemma flow_continuous {q : Params} (hv : spec.valid q) :
    Continuous (fun v : (ℝ × q.E × q.E) × ℝ => flow q v.1 v.2) := by
  have ht : Continuous (fun v : (ℝ × q.E × q.E) × ℝ => v.1.1 + v.2) :=
    continuous_fst.fst.add continuous_snd
  have hn := (continuous_weight q).comp
    (continuous_fst.fst : Continuous (fun v : (ℝ × q.E × q.E) × ℝ => v.1.1))
  have hd := (continuous_weight q).comp ht
  have hr := hn.div hd (fun v => ne_of_gt (weight_pos hv (v.1.1 + v.2)))
  have hp := hr.rpow_const (fun _ => Or.inr (one_div_nonneg.mpr hv.2.2.2.2.1.le))
  exact ht.prodMk ((continuous_fst.snd.snd.add
    (hp.smul (continuous_fst.snd.fst.sub continuous_fst.snd.snd))).prodMk continuous_fst.snd.snd)

lemma jump_continuous {q : Params} (hv : spec.valid q) :
    Continuous (fun v : (ℝ × q.E × q.E) × q.E => jump q v.1 v.2) := by
  have ht : Continuous (fun v : (ℝ × q.E × q.E) × q.E => v.1.1) := continuous_fst.fst
  have hc : Continuous (fun v : (ℝ × q.E × q.E) × q.E => 1 / curvature q v.1.1) :=
    continuous_const.div ((continuous_curvature hv).comp ht)
      (fun v => ne_of_gt (curvature_pos hv v.1.1))
  have ha := (continuous_mirrorStep q).comp ht
  exact ht.prodMk ((continuous_fst.snd.fst.sub (hc.smul continuous_snd)).prodMk
    (continuous_fst.snd.snd.sub (ha.smul continuous_snd)))

lemma advance_continuous {q : Params} (hv : spec.valid q) {g : q.E → q.E} (hg : Continuous g) :
    Continuous (fun v : (ℝ × q.E × q.E) × ℝ => advance q g v.1 v.2) := by
  have hy : Continuous (fun v : (ℝ × q.E × q.E) × ℝ => flow q v.1 (max 0 v.2)) :=
    (flow_continuous hv).comp (continuous_fst.prodMk (continuous_const.max continuous_snd))
  exact (jump_continuous hv).comp (hy.prodMk (hg.comp hy.snd.fst))

end OracleTemplate.GradientOnlyQuasar
