import LongTails.Proofs.NoisyNewtonTuning
import LongTails.Proofs.RobustEstimatorMoments
import LongTails.Proofs.RobustEnergyConcentration
import LongTails.Proofs.RobustSampleBlocks

namespace LongTails.Proofs.NoisyNewtonEstimators

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticLocalHessianConvex
open LongTails.Algorithms.NoisyDampedNewton
open LongTails.Proofs.NoisyNewtonTuning
open OracleTemplate.RobustGradient

lemma grouped_model_failure (p : Params) (hp : spec.valid p)
    (P : Measure p.Ω) [IsProbabilityMeasure P] (V : p.Ω → Point p.d)
    (hV : Measurable V) (hVi : Integrable V P) (u : Point p.d)
    (hmean : ∫ ω, V ω ∂P = u) (hV2i : Integrable (fun ω => ‖V ω - u‖ ^ 2) P)
    (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂P) ≤ p.σ ^ 2) (a : ℝ) (ha : 0 < a) :
    (Measure.pi fun _ : Fin (modelGroups p) => Measure.pi fun _ : Fin (modelSize p a) => P)
      {ξ | modelRadius p a / 2 <
        ‖pilotCenter (modelRadius p a)
          (fun i => (1 / (modelSize p a : ℝ)) • ∑ j, V (ξ i j)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ modelGroups p) := by
  have hB := modelRadius_pos p hp a ha
  have hsize : (p.σ ^ 2 / (modelSize p a : ℝ)) / (modelRadius p a / 6) ^ 2 ≤ 1 / 16 := by
    apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < modelRadius p a / 6))).mpr
    have hh := modelSize_variance p hp a ha
    nlinarith only [hh]
  exact pilot_means_failure_probability hV hVi u hmean hV2i hvar hB
    (modelGroups p) (modelSize p a) (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) hsize

noncomputable def modelGroupsMap (p : Params) (a : ℝ) (ξ : Fin (modelCost p a) → p.Ω) :
    Fin (modelGroups p) → Fin (modelSize p a) → p.Ω :=
  fun i j => ξ ⟨i * modelSize p a + j, by
    have hi := Nat.mul_le_mul_right (modelSize p a) (Nat.succ_le_of_lt i.isLt)
    simp only [Nat.succ_mul] at hi
    have hj := j.isLt
    unfold modelCost
    omega⟩

lemma modelGroupsMap_preserving (p : Params) (a : ℝ) (P : Measure p.Ω) [IsProbabilityMeasure P] :
    MeasurePreserving (modelGroupsMap p a) (Measure.pi fun _ : Fin (modelCost p a) => P)
      (Measure.pi fun _ : Fin (modelGroups p) => Measure.pi fun _ : Fin (modelSize p a) => P) :=
  finite_groups_preserving P (modelGroups p) (modelSize p a)

lemma model_grouping (p : Params) (a : ℝ) (V : p.Ω → Point p.d)
    (ξ : Fin (modelCost p a) → p.Ω) :
    modelEstimate p a (fun j => if hj : j < modelCost p a then V (ξ ⟨j, hj⟩) else 0) =
      pilotCenter (modelRadius p a) (fun i => (1 / (modelSize p a : ℝ)) •
        ∑ j, V (modelGroupsMap p a ξ i j)) := by
  unfold modelEstimate OracleTemplate.RobustGeneralized.meanBlock
  congr 1
  funext i
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hi := Nat.mul_le_mul_right (modelSize p a) (Nat.succ_le_of_lt i.isLt)
  simp only [Nat.succ_mul] at hi
  have hj := j.isLt
  have hb : i * modelSize p a + j < modelCost p a := by unfold modelCost; omega
  simp only [dite_eq_left hb, modelGroupsMap]

lemma model_failure (p : Params) (hp : spec.valid p)
    (P : Measure p.Ω) [IsProbabilityMeasure P] (V : p.Ω → Point p.d)
    (hV : Measurable V) (hVi : Integrable V P) (u : Point p.d)
    (hmean : ∫ ω, V ω ∂P = u) (hV2i : Integrable (fun ω => ‖V ω - u‖ ^ 2) P)
    (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂P) ≤ p.σ ^ 2) (a : ℝ) (ha : 0 < a) :
    (Measure.pi fun _ : Fin (modelCost p a) => P)
      {ξ | modelRadius p a / 2 < ‖modelEstimate p a
        (fun j => if hj : j < modelCost p a then V (ξ ⟨j, hj⟩) else 0) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ modelGroups p) := by
  let F := fun ξ : Fin (modelGroups p) → Fin (modelSize p a) → p.Ω =>
    pilotCenter (modelRadius p a) (fun i => (1 / (modelSize p a : ℝ)) • ∑ j, V (ξ i j))
  have hF : Measurable F := by
    exact (measurable_pilotCenter (modelGroups p)).comp (measurable_const.prodMk (by fun_prop))
  have hset : MeasurableSet {ξ | modelRadius p a / 2 < ‖F ξ - u‖} :=
    measurableSet_lt measurable_const (hF.sub_const u).norm
  have he := (modelGroupsMap_preserving p a P).measure_preimage hset.nullMeasurableSet
  have hb := grouped_model_failure p hp P V hV hVi u hmean hV2i hvar a ha
  rw [← he] at hb
  simpa only [Set.preimage_ofPred_eq, F, model_grouping] using hb

lemma correction_moments (p : Params) (hp : spec.valid p)
    (P : Measure p.Ω) [IsProbabilityMeasure P] (V : p.Ω → Point p.d)
    (hV : Measurable V) (hVi : Integrable V P) (u : Point p.d)
    (hmean : ∫ ω, V ω ∂P = u) (hV2i : Integrable (fun ω => ‖V ω - u‖ ^ 2) P)
    (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (t : Trial (Point p.d)) (ha : 0 < actualWeight t)
    (hc : ‖u - -(t.curvature • t.displacement)‖ ≤ updateRadius p (actualWeight t) / 2) :
    let a := actualWeight t
    let m := updateSize p a
    let F := fun ξ : Fin m → p.Ω => centeredClip (updateRadius p a)
      (-(t.curvature • t.displacement)) ((1 / (m : ℝ)) • ∑ j, V (ξ j))
    Integrable F (Measure.pi fun _ : Fin m => P) ∧
      Integrable (fun ξ => ‖F ξ - u‖ ^ 2) (Measure.pi fun _ : Fin m => P) ∧
      (∫ ξ, ‖F ξ - u‖ ^ 2 ∂(Measure.pi fun _ : Fin m => P)) ≤
        p.ε / (16777216 * a * confidence p ^ 2) ∧
      ‖(∫ ξ, F ξ ∂(Measure.pi fun _ : Fin m => P)) - u‖ ≤
        2 * (p.ε / (16777216 * a * confidence p ^ 2)) / updateRadius p a := by
  let a := actualWeight t
  let m := updateSize p a
  have hm : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hB : 0 < updateRadius p a := by
    have hR := hp.2.2.2.2.2.1
    have hl := confidence_lower p hp
    unfold updateRadius
    positivity
  have hi := OracleTemplate.LightTail.finite_mean_integral hVi m hm
  have hv := finite_mean_variance hV hVi u hV2i hmean m hm
  have hb : (∫ ξ : Fin m → p.Ω, ‖(1 / (m : ℝ)) • ∑ j, V (ξ j) - u‖ ^ 2
      ∂(Measure.pi fun _ : Fin m => P)) ≤ p.ε / (16777216 * a * confidence p ^ 2) := by
    rw [hv.2]
    exact (div_le_div_of_nonneg_right hvar (Nat.cast_nonneg _)).trans
      (updateSize_variance p hp a ha)
  exact centeredClip_moments (by fun_prop) hi.1 (hi.2.trans hmean) hB hc hv.1 hb

lemma correction_error_mgf {Ω : Type*} [MeasurableSpace Ω]
    (p : Params) (hp : spec.valid p) (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → Point p.d) (hY : Measurable Y) (hYi : Integrable Y P)
    (hY2i : Integrable (fun ω => ‖Y ω‖ ^ 2) P) (a : ℝ) (ha : 0 < a)
    (z : Point p.d) (hz : ‖z‖ ≤ 5 * p.R)
    (hbound : ∀ ω, ‖Y ω‖ ≤ 3 * p.R / (512 * a * confidence p))
    (hmean : ‖∫ ω, Y ω ∂P‖ ≤ 512 * a * confidence p *
      (p.ε / (16777216 * a * confidence p ^ 2)) / p.R)
    (hsecond : (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ p.ε / (16777216 * a * confidence p ^ 2)) :
    Integrable (fun ω => Real.exp ((confidence p / p.R ^ 2) *
      (-a * ⟪z, Y ω⟫ + (1 / 2 : ℝ) * a ^ 2 * ‖Y ω‖ ^ 2))) P ∧
    (∫ ω, Real.exp ((confidence p / p.R ^ 2) *
      (-a * ⟪z, Y ω⟫ + (1 / 2 : ℝ) * a ^ 2 * ‖Y ω‖ ^ 2)) ∂P) ≤
      Real.exp (p.ε * a / (4096 * p.R ^ 2)) := by
  have hR := hp.2.2.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.1
  have hl : 1 ≤ confidence p := (by norm_num : (1 : ℝ) ≤ 100).trans (confidence_lower p hp)
  have hlp : 0 < confidence p := by linarith
  let v := p.ε / (16777216 * a * confidence p ^ 2)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsmall : (confidence p / p.R ^ 2) *
      (a * (3 * p.R / (512 * a * confidence p)) * ‖z‖ +
        (1 / 2 : ℝ) * a ^ 2 * (3 * p.R / (512 * a * confidence p)) ^ 2) ≤ 1 := by
    calc
      _ ≤ (confidence p / p.R ^ 2) *
          (a * (3 * p.R / (512 * a * confidence p)) * (5 * p.R) +
            (1 / 2 : ℝ) * a ^ 2 * (3 * p.R / (512 * a * confidence p)) ^ 2) := by gcongr
      _ ≤ 1 := correction_mgf_small p.R a (confidence p) hR ha hl
  have hh := energy_increment_mgf hY hYi hY2i ha.le ha.le (le_refl a)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity : 0 ≤ confidence p / p.R ^ 2)
    z hbound hmean hsecond hsmall
  refine ⟨hh.1, hh.2.trans (Real.exp_le_exp.mpr ?_)⟩
  calc
    _ ≤ (confidence p / p.R ^ 2) *
        (a * (5 * p.R) * (512 * a * confidence p * v / p.R) + (1 / 2 : ℝ) * a ^ 2 * v) +
        2 * (confidence p / p.R ^ 2) ^ 2 * (a ^ 2 * (5 * p.R) ^ 2 +
          (1 / 2 : ℝ) ^ 2 * a ^ 4 * (3 * p.R / (512 * a * confidence p)) ^ 2) * v := by
      change (confidence p / p.R ^ 2) *
        (a * ‖z‖ * (512 * a * confidence p * v / p.R) + (1 / 2 : ℝ) * a ^ 2 * v) +
        2 * (confidence p / p.R ^ 2) ^ 2 * (a ^ 2 * ‖z‖ ^ 2 +
          (1 / 2 : ℝ) ^ 2 * a ^ 4 * (3 * p.R / (512 * a * confidence p)) ^ 2) * v ≤ _
      gcongr
    _ ≤ 2611 * confidence p ^ 2 * a ^ 2 * v / p.R ^ 2 :=
      correction_mgf_exponent p.R a (confidence p) v hR ha hl hv
    _ ≤ p.ε * a / (4096 * p.R ^ 2) := correction_mgf_budget p.R a (confidence p) p.ε hR ha hlp hε.le

lemma correction_mgf (p : Params) (hp : spec.valid p)
    (P : Measure p.Ω) [IsProbabilityMeasure P] (V : p.Ω → Point p.d)
    (hV : Measurable V) (hVi : Integrable V P) (u : Point p.d)
    (hmean : ∫ ω, V ω ∂P = u) (hV2i : Integrable (fun ω => ‖V ω - u‖ ^ 2) P)
    (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂P) ≤ p.σ ^ 2)
    (t : Trial (Point p.d)) (ha : 0 < actualWeight t)
    (hc : ‖u - -(t.curvature • t.displacement)‖ ≤ updateRadius p (actualWeight t) / 2)
    (z : Point p.d) (hz : ‖z‖ ≤ 5 * p.R) :
    let a := actualWeight t
    let m := updateSize p a
    let F := fun ξ : Fin m → p.Ω => centeredClip (updateRadius p a)
      (-(t.curvature • t.displacement)) ((1 / (m : ℝ)) • ∑ j, V (ξ j))
    Integrable (fun ξ => Real.exp ((confidence p / p.R ^ 2) *
      (-a * ⟪z, F ξ - u⟫ + (1 / 2 : ℝ) * a ^ 2 * ‖F ξ - u‖ ^ 2))) (Measure.pi fun _ : Fin m => P) ∧
    (∫ ξ, Real.exp ((confidence p / p.R ^ 2) *
      (-a * ⟪z, F ξ - u⟫ + (1 / 2 : ℝ) * a ^ 2 * ‖F ξ - u‖ ^ 2)) ∂(Measure.pi fun _ : Fin m => P)) ≤
      Real.exp (p.ε * a / (4096 * p.R ^ 2)) := by
  let a := actualWeight t
  let m := updateSize p a
  let F := fun ξ : Fin m → p.Ω => centeredClip (updateRadius p a)
      (-(t.curvature • t.displacement)) ((1 / (m : ℝ)) • ∑ j, V (ξ j))
  have hF : Measurable F := (measurable_centeredClip _ _).comp (by fun_prop)
  obtain ⟨hFi, hF2i, hv, hb⟩ := correction_moments p hp P V hV hVi u hmean hV2i hvar t ha hc
  have hR := hp.2.2.2.2.2.1
  have hl : 0 < confidence p := lt_of_lt_of_le (by norm_num) (confidence_lower p hp)
  have hB : 0 ≤ updateRadius p a := by unfold updateRadius; positivity
  apply correction_error_mgf p hp (Measure.pi fun _ : Fin m => P) (fun ξ => F ξ - u)
    (hF.sub_const u) (hFi.sub (integrable_const u)) hF2i a ha z hz
  · intro ξ
    have hh := centeredClip_error_bounded hB hc ((1 / (m : ℝ)) • ∑ j, V (ξ j))
    exact hh.trans_eq (by unfold updateRadius; ring)
  · rw [integral_sub hFi (integrable_const u)]
    simp only [integral_const, probReal_univ, one_smul]
    exact hb.trans_eq (by unfold updateRadius; field_simp [show a ≠ 0 from ha.ne']; ring)
  · exact hv

end LongTails.Proofs.NoisyNewtonEstimators
