import LongTails.Proofs.HeavyTailedClipping
import LongTails.Proofs.RobustPilotConfidence
import LongTails.Proofs.FiniteVarianceBatch
import Mathlib.Probability.Moments.Variance
import LongTails.Proofs.ScalarSearchBudget
import LongTails.Proofs.AdaptiveIID

open MeasureTheory Classical

namespace OracleTemplate.ScalarHeavyTailEstimator

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
lemma moment_tail {X : Ω → ℝ} {r p v : ℝ} (hr : 0 < r) (hp : 0 ≤ p)
    (hi : Integrable (fun ω => |X ω| ^ p) P)
    (hm : (∫ ω, |X ω| ^ p ∂P) ≤ v) :
    P.real {ω | r < |X ω|} ≤ v / r ^ p := by
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr _
  have h := (hi.div_const (r ^ p)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg
      (Real.rpow_nonneg (abs_nonneg _) _) hrp.le))
    (s := {ω | r < |X ω|}) (by
      intro ω hω
      exact (one_le_div hrp).mpr (Real.rpow_le_rpow hr.le hω.le hp))
  have hv : 0 ≤ v := (integral_nonneg
    (fun ω => Real.rpow_nonneg (abs_nonneg (X ω)) p)).trans hm
  have hb : P {ω | r < |X ω|} ≤ ENNReal.ofReal (v / r ^ p) := by
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    exact div_le_div_of_nonneg_right hm hrp.le
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def, ENNReal.toReal_ofReal (div_nonneg hv hrp.le)] using ht

lemma centered_clip_bias {X : Ω → ℝ} (hX : Measurable X) (hi : Integrable X P)
    {u c B p σ : ℝ} (hm : (∫ ω, X ω ∂P) = u)
    (hB : 0 < B) (hp : 1 ≤ p) (hc : |u - c| ≤ B / 2)
    (hpi : Integrable (fun ω => |X ω - u| ^ p) P)
    (hpbound : (∫ ω, |X ω - u| ^ p ∂P) ≤ σ ^ p) :
    |(∫ ω, RobustGradient.centeredClip B c (X ω) ∂P) - u| ≤
      σ ^ p / (B / 2) ^ (p - 1) := by
  have hci := integrable_clip (P := P) (hX.sub_const c) hB.le
  have he (ω : Ω) : X ω - c - (u - c) = X ω - u := by ring
  have hmean : (∫ ω, X ω - c ∂P) = u - c := by
    rw [integral_sub hi (integrable_const c), hm]
    simp
  have h := clipped_bias_bound (hX.sub_const c) (hi.sub (integrable_const c))
    hmean hB hp (by simpa using hc)
    (by simpa only [he, Real.norm_eq_abs] using hpi)
    (by simpa only [he, Real.norm_eq_abs] using hpbound)
  simp only [RobustGradient.centeredClip]
  rw [integral_add (integrable_const c) hci]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  convert h using 1; simp only [Real.norm_eq_abs]; congr 1; ring

omit [IsProbabilityMeasure P] in
lemma centered_clip_second_moment {X : Ω → ℝ} (hX : Measurable X)
    {u c B p σ : ℝ} (hB : 0 ≤ B) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hc : |u - c| ≤ B)
    (hpi : Integrable (fun ω => |X ω - u| ^ p) P)
    (hpbound : (∫ ω, |X ω - u| ^ p ∂P) ≤ σ ^ p) :
    (∫ ω, |RobustGradient.centeredClip B c (X ω) - u| ^ 2 ∂P) ≤
      (2 * B) ^ (2 - p) * σ ^ p := by
  have he (ω : Ω) : X ω - c - (u - c) = X ω - u := by ring
  have h := clipped_second_moment_bound (P := P) (hX.sub_const c) hB hp hp2
    (by simpa using hc)
    (by simpa only [he, Real.norm_eq_abs] using hpi)
    (by simpa only [he, Real.norm_eq_abs] using hpbound)
  have he' (ω : Ω) : RobustGradient.centeredClip B c (X ω) - u =
      clip B (X ω - c) - (u - c) := by
    simp only [RobustGradient.centeredClip]
    ring
  simpa only [he', Real.norm_eq_abs] using h

lemma majority_tail {A : Set Ω} (hA : MeasurableSet A) {c : ℝ}
    (hc : 1 ≤ c) (hp : P.real A ≤ 1 / c ^ 2) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | k ≤ 2 * (Finset.univ.filter (fun i => ξ i ∈ A)).card} ≤
      ENNReal.ofReal ((2 / c) ^ k) := by
  classical
  have hc0 : 0 < c := by linarith
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  let F : Ω → ℝ := fun ω => if ω ∈ A then c ^ 2 else 1
  have hFm : Measurable F := Measurable.ite hA measurable_const measurable_const
  have hFi : Integrable F P := Integrable.of_bound hFm.aestronglyMeasurable (c ^ 2)
    (Filter.Eventually.of_forall (fun ω => by
      dsimp [F]
      split_ifs
      · simp only [abs_of_nonneg (sq_nonneg c), le_refl]
      · simpa only [Real.norm_eq_abs, abs_one] using hc2))
  have hFe : (∫ ω, F ω ∂P) = 1 + (c ^ 2 - 1) * P.real A := by
    have he : F = fun ω => 1 + (c ^ 2 - 1) * A.indicator (fun _ => (1 : ℝ)) ω := by
      ext ω
      by_cases h : ω ∈ A <;> simp [F, h]
    rw [he, integral_add (integrable_const 1)
      (((integrable_const 1).indicator hA).const_mul (c ^ 2 - 1)), integral_const_mul]
    change (∫ a, (1 : ℝ) ∂P) + (c ^ 2 - 1) * (∫ a, A.indicator 1 a ∂P) = _
    rw [integral_indicator_one hA]
    simp
  have hFnonneg : 0 ≤ ∫ ω, F ω ∂P := integral_nonneg
    (fun ω => by dsimp [F]; split_ifs <;> positivity)
  have hFbound : (∫ ω, F ω ∂P) ≤ 2 := by
    rw [hFe]
    have ha : 0 ≤ P.real A := measureReal_nonneg
    have h := mul_le_mul_of_nonneg_left hp (sq_nonneg c)
    have hcne : c ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hc0)
    field_simp at h
    nlinarith
  let W : (Fin k → Ω) → ℝ := fun ξ => ∏ i, F (ξ i)
  have hWm : Measurable W := by dsimp [W]; fun_prop
  have hWnonneg (ξ : Fin k → Ω) : 0 ≤ W ξ := by
    apply Finset.prod_nonneg
    intro i _
    dsimp [F]
    split_ifs <;> positivity
  have hWbound (ξ : Fin k → Ω) : W ξ ≤ (c ^ 2) ^ k := by
    calc
      _ ≤ ∏ _i : Fin k, c ^ 2 := Finset.prod_le_prod₀
        (fun i _ => by dsimp [F]; split_ifs <;> positivity)
        (fun i _ => by dsimp [F]; split_ifs <;> linarith)
      _ = _ := by simp
  have hWi : Integrable W (Measure.pi fun _ : Fin k => P) :=
    Integrable.of_bound hWm.aestronglyMeasurable ((c ^ 2) ^ k)
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg ξ)]
        exact hWbound ξ))
  have hWe (ξ : Fin k → Ω) :
      W ξ = (c ^ 2) ^ (Finset.univ.filter (fun i => ξ i ∈ A)).card := by
    simp only [W, F, ← Finset.prod_filter, Finset.prod_const]
  have h := (hWi.div_const (c ^ k)).measure_le_integral
    (Filter.Eventually.of_forall (fun ξ => div_nonneg (hWnonneg ξ) (by positivity)))
    (s := {ξ | k ≤ 2 * (Finset.univ.filter (fun i => ξ i ∈ A)).card}) (by
      intro ξ hξ
      apply (one_le_div (by positivity : 0 < c ^ k)).mpr
      rw [hWe, ← pow_mul]
      exact pow_le_pow_right₀ hc hξ)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div, show W = fun ξ => ∏ i : Fin k, F (ξ i) from rfl,
    integral_fintype_prod_eq_pow, Fintype.card_fin]
  calc
    _ ≤ 2 ^ k / c ^ k := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hFnonneg hFbound k) (by positivity)
    _ = _ := by rw [div_pow]

lemma bounded_mean_tail {X : Ω → ℝ} (hX : Measurable X) {C v μ u : ℝ}
    (hbound : ∀ ω, |X ω| ≤ C) (hu : 0 < u)
    (hbias : |(∫ ω, X ω ∂P) - μ| ≤ u / 2)
    (hsecond : (∫ ω, (X ω - μ) ^ 2 ∂P) ≤ v)
    (n : ℕ) (hn : 0 < n) :
    (Measure.pi fun _ : Fin n => P).real
      {ξ | u < |(1 / (n : ℝ)) * ∑ i, X (ξ i) - μ|} ≤
        (v / n) / (u / 2) ^ 2 := by
  let m := ∫ ω, X ω ∂P
  have hXi : Integrable X P := Integrable.of_bound hX.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => by simpa using hbound ω))
  have hcent (a : ℝ) : Integrable (fun ω => ‖X ω - a‖ ^ 2) P := by
    apply Integrable.of_bound ((hX.sub_const a).norm.pow_const 2).aestronglyMeasurable
      ((C + |a|) ^ 2)
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs]
    apply pow_le_pow_left₀ (abs_nonneg _) _ 2
    have hb := hbound ω
    have ha := abs_sub (X ω) a
    linarith
  have hvar : (∫ ω, (X ω - m) ^ 2 ∂P) ≤ v := by
    have h := ProbabilityTheory.variance_le_expectation_sq (μ := P) (hX.sub_const μ).aestronglyMeasurable
    rw [ProbabilityTheory.variance_sub_const hX.aestronglyMeasurable μ,
      ProbabilityTheory.variance_eq_integral hX.aemeasurable] at h
    exact h.trans hsecond
  have hmean := RobustGradient.finite_mean_variance hX hXi m (hcent m) rfl n hn
  have ht := RobustGradient.norm_tail_le_second_moment hmean.1
    (r := u / 2) (v := v / n) (by positivity) (by
      rw [hmean.2]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      simpa only [Real.norm_eq_abs, sq_abs] using hvar)
  apply le_trans (measureReal_mono ?_) ht
  intro ξ hξ
  change u < |(1 / (n : ℝ)) * ∑ i, X (ξ i) - μ| at hξ
  change u / 2 < ‖(1 / (n : ℝ)) • ∑ i, X (ξ i) - m‖
  rw [Real.norm_eq_abs, smul_eq_mul]
  by_contra he
  have he' := le_of_not_gt he
  have htri := abs_add_le ((1 / (n : ℝ)) * ∑ i, X (ξ i) - m) (m - μ)
  have hid : (1 / (n : ℝ)) * ∑ i, X (ξ i) - m + (m - μ) =
      (1 / (n : ℝ)) * ∑ i, X (ξ i) - μ := by ring
  rw [hid] at htri
  have hb : |m - μ| ≤ u / 2 := hbias
  exact (not_le_of_gt hξ) (by linarith)

lemma pilot_tail {X : Ω → ℝ} (hX : Measurable X) (μ u : ℝ) {c : ℝ}
    (hc : 1 ≤ c) (hp : P.real {ω | u < |X ω - μ|} ≤ 1 / c ^ 2) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | 3 * u < |RobustGradient.pilotCenter (6 * u) (fun i => X (ξ i)) - μ|} ≤
      ENNReal.ofReal ((2 / c) ^ k) := by
  apply (measure_mono ?_).trans (majority_tail
    (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hX.sub_const μ))) hc hp k)
  intro ξ hξ
  change 3 * u < |RobustGradient.pilotCenter (6 * u) (fun i => X (ξ i)) - μ| at hξ
  have hgood : ¬ k < 2 * (Finset.univ.filter (fun i => |X (ξ i) - μ| ≤ u)).card := by
    intro hg
    have h := RobustGradient.pilotCenter_accuracy (fun i => X (ξ i)) μ
      (B := 6 * u) (by simpa only [Real.norm_eq_abs, mul_div_cancel_left₀ _ (by norm_num : (6 : ℝ) ≠ 0)] using hg)
    have he : 6 * u / 2 = 3 * u := by ring
    rw [Real.norm_eq_abs, he] at h
    exact (not_le_of_gt hξ) h
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k))) (p := fun i => |X (ξ i) - μ| ≤ u)
  simp only [Finset.card_univ, Fintype.card_fin, not_le] at hcard
  change k ≤ 2 * (Finset.univ.filter (fun i => u < |X (ξ i) - μ|)).card
  omega

lemma clipped_batch_tail {X : Ω → ℝ} (hX : Measurable X) (hi : Integrable X P)
    {μ c σ p u : ℝ} (hm : (∫ ω, X ω ∂P) = μ)
    (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hc : |μ - c| ≤ radius σ p u / 2)
    (hpi : Integrable (fun ω => |X ω - μ| ^ p) P)
    (hmoment : (∫ ω, |X ω - μ| ^ p ∂P) ≤ σ ^ p) :
    (Measure.pi fun _ : Fin (batchSize σ p u) => P).real
      {ξ | u < |(1 / (batchSize σ p u : ℝ)) *
        ∑ i, RobustGradient.centeredClip (radius σ p u) c (X (ξ i)) - μ|} ≤ 1 / 4096 := by
  let C := radius σ p u
  have hC : 0 < C := radius_pos hσ hu
  let Y := fun ω => RobustGradient.centeredClip C c (X ω)
  have hY : Measurable Y := (RobustGradient.measurable_centeredClip C c).comp hX
  have hbound (ω : Ω) : |Y ω| ≤ |c| + C := by
    have h := norm_clip_le hC.le (X ω - c)
    have ha := abs_add_le c (clip C (X ω - c))
    simpa only [Y, RobustGradient.centeredClip, Real.norm_eq_abs] using
      ha.trans (by simpa only [Real.norm_eq_abs] using add_le_add (le_refl |c|) h)
  have hb : |(∫ ω, Y ω ∂P) - μ| ≤ u / 2 := by
    have h := centered_clip_bias hX hi hm hC hp.le hc hpi hmoment
    exact (h.trans (radius_bias hσ hu hp)).trans (by linarith)
  have hsecond : (∫ ω, (Y ω - μ) ^ 2 ∂P) ≤ (2 * C) ^ (2 - p) * σ ^ p := by
    simpa only [Y, sq_abs] using centered_clip_second_moment hX hC.le
      (by linarith : 0 ≤ p) hp2 (by linarith : |μ - c| ≤ C) hpi hmoment
  have hn : 0 < batchSize σ p u := by unfold batchSize; omega
  exact (bounded_mean_tail hY hbound hu hb hsecond _ hn).trans (batch_variance hu)

omit [IsProbabilityMeasure P] in
lemma moment_tail_ratio {X : Ω → ℝ} {σ p r δ : ℝ}
    (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hr : 0 < r) (hδ : δ ≤ 1)
    (hratio : σ / r ≤ δ)
    (hi : Integrable (fun ω => |X ω| ^ p) P)
    (hm : (∫ ω, |X ω| ^ p ∂P) ≤ σ ^ p) :
    P.real {ω | r < |X ω|} ≤ δ := by
  apply (moment_tail hr (by linarith) hi hm).trans
  rw [← Real.div_rpow hσ hr.le]
  exact (Real.rpow_le_self_of_le_one (div_nonneg hσ hr.le)
    (hratio.trans hδ) hp).trans hratio

lemma conditional_failure {Ξ : Type*} [MeasurableSpace Ξ] {Q : Measure Ξ}
    [IsProbabilityMeasure Q] {A : Set Ω} {B : Set (Ω × Ξ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {a b : ℝ} (hb : 0 ≤ b)
    (hfirst : P.real A ≤ a)
    (hsecond : ∀ ω ∉ A, Q.real {ξ | (ω, ξ) ∈ B} ≤ b) :
    (P.prod Q).real B ≤ a + b := by
  have hBi : Integrable (B.indicator (fun _ => (1 : ℝ))) (P.prod Q) :=
    (integrable_const 1).indicator hB
  rw [← integral_indicator_one hB]
  change (∫ z, B.indicator (fun _ => (1 : ℝ)) z ∂P.prod Q) ≤ _
  rw [integral_prod _ hBi]
  have hAi : Integrable (A.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator hA
  have hpoint (ω : Ω) : (∫ ξ, B.indicator (fun _ => (1 : ℝ)) (ω, ξ) ∂Q) ≤
      A.indicator (fun _ => (1 : ℝ)) ω + b := by
    have hs : MeasurableSet {ξ | (ω, ξ) ∈ B} := hB.preimage measurable_prodMk_left
    change (∫ ξ, ({ξ | (ω, ξ) ∈ B}).indicator (fun _ => (1 : ℝ)) ξ ∂Q) ≤ _
    change (∫ ξ, ({ξ | (ω, ξ) ∈ B}).indicator 1 ξ ∂Q) ≤ _
    rw [integral_indicator_one hs]
    by_cases ha : ω ∈ A
    · simp only [Set.indicator_of_mem ha]
      exact measureReal_le_one.trans (by linarith)
    · simpa only [Set.indicator_of_notMem ha, zero_add] using hsecond ω ha
  have h := integral_mono hBi.integral_prod_left (hAi.add (integrable_const b)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hAi (integrable_const b)] at h
  change (∫ x, ∫ y, B.indicator (fun _ => (1 : ℝ)) (x, y) ∂Q ∂P) ≤
    (∫ x, A.indicator 1 x ∂P) + (∫ x, b ∂P) at h
  rw [integral_indicator_one hA] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  linarith

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
lemma anchored_batch_tail {X : Ω → ℝ} (hX : Measurable X) (hi : Integrable X P)
    {μ σ p u : ℝ} (hm : (∫ ω, X ω ∂P) = μ)
    (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hpi : Integrable (fun ω => |X ω - μ| ^ p) P)
    (hmoment : (∫ ω, |X ω - μ| ^ p ∂P) ≤ σ ^ p) :
    (P.prod (Measure.pi fun _ : Fin (batchSize σ p u) => P)).real
      {w | u < |(1 / (batchSize σ p u : ℝ)) *
        ∑ i, RobustGradient.centeredClip (radius σ p u) (X w.1) (X (w.2 i)) - μ|} ≤ 1 / 64 := by
  let C := radius σ p u
  let m := batchSize σ p u
  let A := {ω | C / 2 < |X ω - μ|}
  let Y : Ω × (Fin m → Ω) → ℝ := fun w => (1 / (m : ℝ)) *
    ∑ i, RobustGradient.centeredClip C (X w.1) (X (w.2 i))
  have hC : 0 < C := radius_pos hσ hu
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (hX.sub_const μ))
  have hY : Measurable Y := by
    apply Measurable.const_mul
    apply Finset.measurable_fun_sum
    intro i _
    exact (hX.comp measurable_fst).add ((measurable_clip C).comp
      ((hX.comp ((measurable_pi_apply i).comp measurable_snd)).sub (hX.comp measurable_fst)))
  have hB : MeasurableSet {w | u < |Y w - μ|} := measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (hY.sub_const μ))
  have hfirst : P.real A ≤ 1 / 256 := by
    apply moment_tail_ratio hσ hp.le (by positivity) (by norm_num) _ hpi hmoment
    apply (div_le_iff₀ (by positivity : 0 < C / 2)).mpr
    have hlarge := radius_large hσ hu hp hp2
    change 256 * (σ + u) ≤ C / 2 at hlarge
    linarith
  have hsecond (ω : Ω) (hω : ω ∉ A) :
      (Measure.pi fun _ : Fin m => P).real {ξ | u < |Y (ω, ξ) - μ|} ≤ 1 / 4096 := by
    have hc : |μ - X ω| ≤ C / 2 := by
      rw [abs_sub_comm]
      change ¬ C / 2 < |X ω - μ| at hω
      exact le_of_not_gt hω
    exact clipped_batch_tail (P := P) (μ := μ) (c := X ω)
      (σ := σ) (p := p) (u := u) hX hi hm hσ hu hp hp2 hc hpi hmoment
  have h := conditional_failure hA hB (by norm_num : (0 : ℝ) ≤ 1 / 4096) hfirst hsecond
  exact h.trans (by norm_num)

@[fun_prop]
lemma measurable_centered_clip_pair (C : ℝ) :
    Measurable (fun z : ℝ × ℝ => RobustGradient.centeredClip C z.1 z.2) :=
  measurable_fst.add ((measurable_clip C).comp (measurable_snd.sub measurable_fst))

lemma anchor_samples_preserving (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => (ξ 0, fun i : Fin n => ξ (i + 1)))
      (Measure.infinitePi fun _ : ℕ => P) (P.prod (Measure.pi fun _ : Fin n => P)) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).comp
    (StochasticGeneralized.prefix_preserving P (n + 1))
  simpa only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply,
    Fin.insertNthEquiv_symm_apply, Fin.removeNth_zero, Fin.tail_def, Fin.val_succ, Fin.val_zero] using h

lemma measurable_block {X : Ω → ℝ} (hX : Measurable X) (σ p u : ℝ) :
    Measurable (fun ξ : ℕ → Ω => block σ p u (fun j => X (ξ j))) := by
  unfold block
  split_ifs
  · exact hX.comp (measurable_pi_apply 0)
  · apply Measurable.const_mul
    apply Finset.measurable_fun_sum
    intro i _
    exact (measurable_centered_clip_pair _).comp
      ((hX.comp (measurable_pi_apply 0)).prodMk (hX.comp (measurable_pi_apply (i.val + 1))))

lemma block_tail {X : Ω → ℝ} (hX : Measurable X) (hi : Integrable X P)
    {μ σ p u : ℝ} (hm : (∫ ω, X ω ∂P) = μ)
    (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (hpi : Integrable (fun ω => |X ω - μ| ^ p) P)
    (hmoment : (∫ ω, |X ω - μ| ^ p ∂P) ≤ σ ^ p) :
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | u < |block σ p u (fun j => X (ξ j)) - μ|} ≤ 1 / 64 := by
  unfold block
  split_ifs with hr
  · let A := {ω | u < |X ω - μ|}
    have hA : MeasurableSet A := measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (hX.sub_const μ))
    have hmarg : MeasurePreserving (fun ξ : ℕ → Ω => ξ 0)
        (Measure.infinitePi fun _ : ℕ => P) P :=
      ⟨measurable_pi_apply 0, Measure.infinitePi_map_eval _ _⟩
    change (Measure.infinitePi fun _ : ℕ => P).real ((fun ξ => ξ 0) ⁻¹' A) ≤ _
    unfold Measure.real
    rw [hmarg.measure_preimage hA.nullMeasurableSet]
    have h := moment_tail_ratio hσ hp.le hu (by norm_num : (1 / 128 : ℝ) ≤ 1)
      (by apply (div_le_iff₀ hu).mpr; linarith) hpi hmoment
    exact h.trans (by norm_num)
  · let m := batchSize σ p u
    let B : Set (Ω × (Fin m → Ω)) := {w | u < |(1 / (m : ℝ)) *
      ∑ i, RobustGradient.centeredClip (radius σ p u) (X w.1) (X (w.2 i)) - μ|}
    have hY : Measurable (fun w : Ω × (Fin m → Ω) => (1 / (m : ℝ)) *
        ∑ i, RobustGradient.centeredClip (radius σ p u) (X w.1) (X (w.2 i))) := by
      apply Measurable.const_mul
      apply Finset.measurable_fun_sum
      intro i _
      exact (measurable_centered_clip_pair _).comp
        ((hX.comp measurable_fst).prodMk (hX.comp ((measurable_pi_apply i).comp measurable_snd)))
    have hB : MeasurableSet B := measurableSet_lt measurable_const
      (continuous_abs.measurable.comp (hY.sub_const μ))
    change (Measure.infinitePi fun _ : ℕ => P).real
      ((fun ξ : ℕ → Ω => (ξ 0, fun i : Fin m => ξ (i + 1))) ⁻¹' B) ≤ _
    unfold Measure.real
    rw [(anchor_samples_preserving (P := P) m).measure_preimage hB.nullMeasurableSet]
    exact anchored_batch_tail hX hi hm hσ hu hp hp2 hpi hmoment

end OracleTemplate.ScalarHeavyTailEstimator
