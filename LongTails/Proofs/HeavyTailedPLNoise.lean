import LongTails.Proofs.TerminalClippingConcentration

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.HeavyTailedPL

variable {E : Type*} [NormedAddCommGroup E]

noncomputable def clip (M : ℝ) (e : E) : E := if ‖e‖ ≤ M then e else 0

lemma clip_of_le {M : ℝ} {e : E} (h : ‖e‖ ≤ M) : clip M e = e := by simp [clip, h]

lemma norm_clip_le {M : ℝ} (hM : 0 ≤ M) (e : E) : ‖clip M e‖ ≤ M := by
  unfold clip
  split_ifs with h
  · exact h
  · simpa using hM

lemma norm_clip_le_norm (M : ℝ) (e : E) : ‖clip M e‖ ≤ ‖e‖ := by
  unfold clip
  split_ifs
  · exact le_rfl
  · simp

lemma measurable_clip [MeasurableSpace E] [BorelSpace E] (M : ℝ) :
    Measurable (clip (E := E) M) := by
  unfold clip
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id
    measurable_const

lemma norm_sub_clip (M : ℝ) (e : E) :
    ‖e - clip M e‖ = if ‖e‖ ≤ M then 0 else ‖e‖ := by
  unfold clip
  split_ifs <;> simp

lemma exceed_le {M q a : ℝ} (hM : 0 < M) (hq : 0 < q) (ha : 0 ≤ a) :
    (if M < a then (1 : ℝ) else 0) ≤ a ^ q / M ^ q := by
  split_ifs with h
  · rw [le_div_iff₀ (Real.rpow_pos_of_pos hM q), one_mul]
    exact Real.rpow_le_rpow hM.le h.le hq.le
  · positivity

lemma tail_mass_le {M q a : ℝ} (hM : 0 < M) (hq : 1 ≤ q) (ha : 0 ≤ a) :
    (if a ≤ M then 0 else a) ≤ a ^ q / M ^ (q - 1) := by
  split_ifs with h
  · positivity
  · push Not at h
    have hpos : 0 < a := hM.trans h
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hM _)]
    have h1 : M ^ (q - 1) ≤ a ^ (q - 1) := Real.rpow_le_rpow hM.le h.le (by linarith)
    have h2 : a * a ^ (q - 1) = a ^ q := by
      rw [← Real.rpow_one_add' hpos.le (by linarith)]
      · congr 1; ring
    calc a * M ^ (q - 1) ≤ a * a ^ (q - 1) := mul_le_mul_of_nonneg_left h1 ha
      _ = a ^ q := h2

lemma tail_mass_le_sq {M a c : ℝ} (hc : 0 < c) :
    (if a ≤ M then 0 else a) ≤ a ^ 2 / (2 * c) + c / 2 * (if M < a then 1 else 0) := by
  by_cases h : a ≤ M
  · rw [ite_eq_left h]
    split_ifs <;> positivity
  · have h' : M < a := lt_of_not_ge h
    rw [ite_eq_right h, ite_eq_left h', mul_one, div_add_div _ _ (by positivity) (by norm_num),
      le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a - c)]

section Moments

variable [InnerProductSpace ℝ E] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma integrable_clip {e : Ω → E} (he : Measurable e) {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun ω => clip M (e ω)) P :=
  Integrable.of_bound ((measurable_clip M).comp he).aestronglyMeasurable M
    (Filter.Eventually.of_forall (fun ω => norm_clip_le hM (e ω)))

omit [CompleteSpace E] in
lemma clip_bias {M σ ν q : ℝ} {e : Ω → E} (he : Measurable e) (hi : Integrable e P)
    (hzero : ∫ ω, e ω ∂P = 0)
    (h2i : Integrable (fun ω => ‖e ω‖ ^ 2) P) (hqi : Integrable (fun ω => ‖e ω‖ ^ q) P)
    (hM : 0 < M) (hσ : 0 < σ) (hν : 0 < ν) (hq : 1 ≤ q)
    (h2 : ∫ ω, ‖e ω‖ ^ 2 ∂P ≤ σ ^ 2) (hqm : ∫ ω, ‖e ω‖ ^ q ∂P ≤ ν ^ q) :
    ‖∫ ω, clip M (e ω) ∂P‖ ≤ ν ^ q / M ^ (q - 1) ∧
      ‖∫ ω, clip M (e ω) ∂P‖ ^ 2 ≤ σ ^ 2 * (ν ^ q / M ^ q) := by
  have hci := integrable_clip (P := P) he hM.le
  have hdi : Integrable (fun ω => e ω - clip M (e ω)) P := hi.sub hci
  have heq : ∫ ω, clip M (e ω) ∂P = -∫ ω, (e ω - clip M (e ω)) ∂P := by
    rw [integral_sub hi hci, hzero]; simp
  let tail := fun ω => if ‖e ω‖ ≤ M then (0 : ℝ) else ‖e ω‖
  have htail_eq (ω : Ω) : ‖e ω - clip M (e ω)‖ = tail ω := norm_sub_clip M (e ω)
  have htm : Measurable tail :=
    Measurable.ite (measurableSet_le (measurable_norm.comp he) measurable_const)
      measurable_const (measurable_norm.comp he)
  have hti : Integrable tail P := by
    refine hdi.norm.congr (Filter.Eventually.of_forall (fun ω => htail_eq ω))
  have hnorm : ‖∫ ω, clip M (e ω) ∂P‖ ≤ ∫ ω, tail ω ∂P := by
    rw [heq, norm_neg]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => htail_eq ω))
  have hMq : 0 < M ^ q := Real.rpow_pos_of_pos hM q
  constructor
  · refine hnorm.trans ?_
    have hb := integral_mono hti (hqi.div_const (M ^ (q - 1)))
      (fun ω => tail_mass_le hM hq (norm_nonneg (e ω)))
    rw [integral_div] at hb
    exact hb.trans (div_le_div_of_nonneg_right hqm (Real.rpow_pos_of_pos hM _).le)
  · set p := ν ^ q / M ^ q with hp
    have hp0 : 0 < p := div_pos (Real.rpow_pos_of_pos hν q) hMq
    set c := σ / Real.sqrt p with hc
    have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
    have hc0 : 0 < c := div_pos hσ hsp
    let ind := fun ω => if M < ‖e ω‖ then (1 : ℝ) else 0
    have hindm : Measurable ind :=
      Measurable.ite (measurableSet_lt measurable_const (measurable_norm.comp he))
        measurable_const measurable_const
    have hindi : Integrable ind P :=
      Integrable.of_bound hindm.aestronglyMeasurable 1 (Filter.Eventually.of_forall
        (fun ω => by simp only [ind]; split_ifs <;> simp))
    have hind : ∫ ω, ind ω ∂P ≤ p := by
      have hb := integral_mono hindi (hqi.div_const (M ^ q))
        (fun ω => exceed_le hM (by linarith) (norm_nonneg (e ω)))
      rw [integral_div] at hb
      exact hb.trans (div_le_div_of_nonneg_right hqm hMq.le)
    have hbound := integral_mono hti ((h2i.div_const (2 * c)).add (hindi.const_mul (c / 2)))
      (fun ω => tail_mass_le_sq (M := M) (a := ‖e ω‖) hc0)
    simp only [Pi.add_apply] at hbound
    rw [integral_add (h2i.div_const _) (hindi.const_mul _), integral_div,
      integral_const_mul] at hbound
    have hval : σ ^ 2 / (2 * c) + c / 2 * p = σ * Real.sqrt p := by
      rw [hc]
      have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
      field_simp
      nlinarith [hsq]
    have hfin : ∫ ω, tail ω ∂P ≤ σ * Real.sqrt p := by
      have h1 : (∫ ω, ‖e ω‖ ^ 2 ∂P) / (2 * c) ≤ σ ^ 2 / (2 * c) :=
        div_le_div_of_nonneg_right h2 (by positivity)
      have h3 : c / 2 * ∫ ω, ind ω ∂P ≤ c / 2 * p :=
        mul_le_mul_of_nonneg_left hind (by positivity)
      linarith
    have hn := hnorm.trans hfin
    have hsq : (σ * Real.sqrt p) ^ 2 = σ ^ 2 * p := by
      rw [mul_pow, Real.sq_sqrt hp0.le]
    calc ‖∫ ω, clip M (e ω) ∂P‖ ^ 2 ≤ (σ * Real.sqrt p) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = σ ^ 2 * p := hsq

end Moments

end OracleTemplate.HeavyTailedPL
