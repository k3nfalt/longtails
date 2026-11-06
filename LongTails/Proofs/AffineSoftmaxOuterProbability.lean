import LongTails.Proofs.AffineSoftmaxOuterStopping

namespace LongTails.Proofs.AffineSoftmaxOuterProbability

open MeasureTheory
open scoped ENNReal

lemma nonnegative_tail {Ω : Type*} [MeasurableSpace Ω] (Q : ProbabilityMeasure Ω)
    (f : Ω → ℝ) (hi : Integrable f (Q : Measure Ω)) (hn : ∀ ω, 0 ≤ f ω)
    {threshold bound : ℝ} (ht : 0 < threshold) (hb : (∫ ω, f ω ∂(Q : Measure Ω)) ≤ bound) :
    (Q : Measure Ω) {ω | threshold < f ω} ≤ ENNReal.ofReal (bound / threshold) := by
  have h := (hi.div_const threshold).measure_le_integral
    (Filter.Eventually.of_forall fun ω => div_nonneg (hn ω) ht.le)
    (s := {ω | threshold < f ω}) (fun ω hω => (one_le_div ht).2 hω.le)
  apply h.trans
  rw [integral_div]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hb ht.le)

lemma energy_accuracy_failure {Ω : Type*} [MeasurableSpace Ω] (Q : ProbabilityMeasure Ω)
    (potential movement weight gap : Ω → ℝ) {D ε : ℝ} (hD : 0 < D) (hε : 0 < ε)
    (hpi : Integrable potential (Q : Measure Ω)) (hmi : Integrable movement (Q : Measure Ω))
    (hpn : ∀ ω, 0 ≤ potential ω) (hmn : ∀ ω, 0 ≤ movement ω)
    (henergy : (∫ ω, potential ω ∂(Q : Measure Ω)) + (∫ ω, movement ω ∂(Q : Measure Ω)) ≤ 5 * D ^ 2)
    (hstop : ∀ ω, movement ω ≤ 60 * D ^ 2 → 100 * D ^ 2 / ε ≤ weight ω)
    (hgap : ∀ ω, weight ω * gap ω ≤ potential ω) :
    (Q : Measure Ω) {ω | ε < gap ω} ≤ ENNReal.ofReal (2 / 15 : ℝ) := by
  have hpmean : (∫ ω, potential ω ∂(Q : Measure Ω)) ≤ 5 * D ^ 2 := by
    have h : 0 ≤ (∫ ω, movement ω ∂(Q : Measure Ω)) := integral_nonneg hmn
    linarith
  have hmmean : (∫ ω, movement ω ∂(Q : Measure Ω)) ≤ 5 * D ^ 2 := by
    have h : 0 ≤ (∫ ω, potential ω ∂(Q : Measure Ω)) := integral_nonneg hpn
    linarith
  have hp := nonnegative_tail Q potential hpi hpn (show 0 < 100 * D ^ 2 by positivity) hpmean
  have hm := nonnegative_tail Q movement hmi hmn (show 0 < 60 * D ^ 2 by positivity) hmmean
  have heP : 5 * D ^ 2 / (100 * D ^ 2) = (1 / 20 : ℝ) := by field_simp; norm_num
  have heM : 5 * D ^ 2 / (60 * D ^ 2) = (1 / 12 : ℝ) := by field_simp; norm_num
  rw [heP] at hp
  rw [heM] at hm
  have hsubset : {ω | ε < gap ω} ⊆ {ω | 60 * D ^ 2 < movement ω} ∪ {ω | 100 * D ^ 2 < potential ω} := by
    intro ω hω
    by_cases hmove : 60 * D ^ 2 < movement ω
    · exact Or.inl hmove
    · apply Or.inr
      have hw := hstop ω (le_of_not_gt hmove)
      have hwpos : 0 < weight ω := (show 0 < 100 * D ^ 2 / ε by positivity).trans_le hw
      have hs := (div_le_iff₀ hε).1 hw
      have hg := mul_lt_mul_of_pos_left hω hwpos
      have hp := hgap ω
      exact hs.trans_lt (hg.trans_le hp)
  calc
    _ ≤ (Q : Measure Ω) ({ω | 60 * D ^ 2 < movement ω} ∪ {ω | 100 * D ^ 2 < potential ω}) := measure_mono hsubset
    _ ≤ (Q : Measure Ω) {ω | 60 * D ^ 2 < movement ω} + (Q : Measure Ω) {ω | 100 * D ^ 2 < potential ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / 12 : ℝ) + ENNReal.ofReal (1 / 20 : ℝ) := add_le_add hm hp
    _ = ENNReal.ofReal (2 / 15 : ℝ) := by rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

lemma coupled_failure {S Ω : Type*} [MeasurableSpace Ω] (Q : ProbabilityMeasure Ω)
    (actual ideal : Ω → S) (bad : S → Prop) {p q : ℝ≥0∞}
    (hideal : (Q : Measure Ω) {ω | bad (ideal ω)} ≤ p)
    (hcouple : (Q : Measure Ω) {ω | actual ω ≠ ideal ω} ≤ q) :
    (Q : Measure Ω) {ω | bad (actual ω)} ≤ p + q := by
  have hsub : {ω | bad (actual ω)} ⊆ {ω | bad (ideal ω)} ∪ {ω | actual ω ≠ ideal ω} := by
    intro ω hω
    by_cases he : actual ω = ideal ω
    · exact Or.inl (by simpa only [Set.mem_ofPred_eq, he] using hω)
    · exact Or.inr he
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hideal hcouple))

end LongTails.Proofs.AffineSoftmaxOuterProbability
