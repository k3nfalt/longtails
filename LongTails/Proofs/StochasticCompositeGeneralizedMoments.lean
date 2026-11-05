import LongTails.Proofs.HeavyTailedClipping
import LongTails.Proofs.RobustEstimatorMoments
import LongTails.Proofs.ScalarHeavyTailEstimator

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RobustGradient

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma pilotCenter_constant {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B) (u : E) :
    pilotCenter B (fun _ : Fin n => u) = u := by
  classical
  have h : ∃ i ∈ List.finRange n,
      n < 2 * (neighbors B (fun _ : Fin n => u) i).card := by
    refine ⟨⟨0, hn⟩, by simp, ?_⟩
    simp only [neighbors, sub_self, norm_zero]
    have hb : 0 ≤ B / 3 := by positivity
    simp only [hb, Finset.filter_true, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i, _, _, hi⟩ := firstPilot_selected B (fun _ : Fin n => u) (List.finRange n) h
  exact hi

lemma centeredClip_at_center {B : ℝ} (hB : 0 ≤ B) (u : E) : centeredClip B u u = u := by
  simp [centeredClip, clip, hB]


end


lemma zero_central_moment_ae {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} {V : Ω → E} {u : E} {p : ℝ} (hp : p ≠ 0)
    (hi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ 0) : V =ᵐ[P] fun _ => u := by
  have hn : ∀ ω, 0 ≤ ‖V ω - u‖ ^ p := fun ω => Real.rpow_nonneg (norm_nonneg _) _
  have hz : (∫ ω, ‖V ω - u‖ ^ p ∂P) = 0 := le_antisymm hm (integral_nonneg hn)
  have he := (integral_eq_zero_iff_of_nonneg hn hi).mp hz
  filter_upwards [he] with ω hω
  exact sub_eq_zero.mp (norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg _) hp).mp hω))

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

omit [SecondCountableTopology E] in
lemma squared_sum_increment_mgf {X : Ω → E} (hX : Measurable X) (hi : Integrable X P)
    (hi2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) (hz : ∫ ω, X ω ∂P = 0)
    {K v t : ℝ} (ht : 0 ≤ t) (s : E) (hb : ∀ ω, ‖X ω‖ ≤ K)
    (hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v)
    (hs : t * (2 * K * ‖s‖ + K ^ 2) ≤ 1) :
    Integrable (fun ω => Real.exp (t * (2 * ⟪s, X ω⟫ + ‖X ω‖ ^ 2))) P ∧
    (∫ ω, Real.exp (t * (2 * ⟪s, X ω⟫ + ‖X ω‖ ^ 2)) ∂P) ≤
      Real.exp (t * v + 2 * t ^ 2 * (4 * ‖s‖ ^ 2 + K ^ 2) * v) := by
  have h := energy_increment_mgf hX hi hi2
    (a := 2) (b := 2) (c := 1 / 4) (d := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ht (-s) hb
    (by simp [hz]) hv (by norm_num; exact hs)
  norm_num [inner_neg_left] at h
  exact h

lemma centeredClip_heavy_bias {V : Ω → E} (hV : Measurable V) (hi : Integrable V P)
    {u c : E} (hmean : ∫ ω, V ω ∂P = u) {B p σ : ℝ} (hB : 0 < B) (hp : 1 ≤ p)
    (hc : ‖u - c‖ ≤ B / 2) (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p) :
    ‖(∫ ω, centeredClip B c (V ω) ∂P) - u‖ ≤ σ ^ p / (B / 2) ^ (p - 1) := by
  have he : ∀ ω, (V ω - c) - (u - c) = V ω - u := fun ω => by abel
  have hmean' : (∫ ω, V ω - c ∂P) = u - c := by
    rw [integral_sub hi (integrable_const c), hmean, integral_const]
    simp
  have hb := clipped_bias_bound (hV.sub_const c) (hi.sub (integrable_const c))
    hmean' hB hp hc (by simpa only [he] using hmi) (by simpa only [he] using hm)
  have hci := integrable_clip (P := P) (hV.sub_const c) hB.le
  have heq : (∫ ω, centeredClip B c (V ω) ∂P) = c + ∫ ω, clip B (V ω - c) ∂P := by
    simp only [centeredClip, integral_add (integrable_const c) hci, integral_const,
      probReal_univ, one_smul]
  rw [heq]
  convert hb using 1
  congr 1
  abel

omit [CompleteSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma centeredClip_heavy_second {V : Ω → E} (hV : Measurable V)
    {u c : E} {B p σ : ℝ} (hB : 0 ≤ B) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hc : ‖u - c‖ ≤ B) (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p) :
    (∫ ω, ‖centeredClip B c (V ω) - u‖ ^ 2 ∂P) ≤ (2 * B) ^ (2 - p) * σ ^ p := by
  have he : ∀ ω, (V ω - c) - (u - c) = V ω - u := fun ω => by abel
  have hb := clipped_second_moment_bound (hV.sub_const c) hB hp hp2 hc
    (by simpa only [he] using hmi) (by simpa only [he] using hm)
  have heq : ∀ ω, centeredClip B c (V ω) - u = clip B (V ω - c) - (u - c) := by
    intro ω
    unfold centeredClip
    abel
  simpa only [heq] using hb

lemma guardedError_heavy_moments {V : Ω → E} (hV : Measurable V) (hi : Integrable V P)
    {u : E} (hmean : ∫ ω, V ω ∂P = u) {B p σ : ℝ} (hB : 0 < B)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p) (c : E) :
    Integrable (fun ω => guardedError B u c (V ω)) P ∧
    Integrable (fun ω => ‖guardedError B u c (V ω)‖ ^ 2) P ∧
    (∫ ω, ‖guardedError B u c (V ω)‖ ^ 2 ∂P) ≤ (2 * B) ^ (2 - p) * σ ^ p ∧
    ‖∫ ω, guardedError B u c (V ω) ∂P‖ ≤ σ ^ p / (B / 2) ^ (p - 1) := by
  have hY : Measurable (fun ω => guardedError B u c (V ω)) := measurable_guardedError.comp (measurable_const.prodMk
    (measurable_const.prodMk (measurable_const.prodMk hV)))
  have hYi : Integrable (fun ω => guardedError B u c (V ω)) P :=
    Integrable.of_bound hY.aestronglyMeasurable (3 * B / 2)
      (Filter.Eventually.of_forall (fun ω => guardedError_bound hB.le u c (V ω)))
  have hYi2 : Integrable (fun ω => ‖guardedError B u c (V ω)‖ ^ 2) P := by
    apply Integrable.of_bound (hY.norm.pow_const 2).aestronglyMeasurable ((3 * B / 2) ^ 2)
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (guardedError_bound hB.le u c (V ω)) 2
  refine ⟨hYi, hYi2, ?_⟩
  by_cases hc : ‖u - c‖ ≤ B / 2
  · simp only [guardedError_eq hc]
    refine ⟨centeredClip_heavy_second hV hB.le (by linarith) hp2 (by linarith) hmi hm, ?_⟩
    have hci : Integrable (fun ω => centeredClip B c (V ω)) P :=
      (integrable_const c).add (integrable_clip (hV.sub_const c) hB.le)
    rw [integral_sub hci (integrable_const u), integral_const]
    simp only [probReal_univ, one_smul]
    exact centeredClip_heavy_bias hV hi hmean hB hp hc hmi hm
  · have hσ : 0 ≤ σ ^ p := (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _)).trans hm
    simp only [guardedError, hc, ↓reduceIte, norm_zero, zero_pow (by decide : 2 ≠ 0),
      integral_zero, norm_zero]
    exact ⟨mul_nonneg (Real.rpow_nonneg (by positivity) _) hσ,
      div_nonneg hσ (Real.rpow_nonneg (by positivity) _)⟩

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma pilotCenter_heavy_failure {V : Ω → E} (hV : Measurable V) (u : E)
    {B p σ : ℝ} (hB : 0 < B) (hp : 0 ≤ p)
    (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p)
    (hsize : σ ^ p / (B / 6) ^ p ≤ 1 / 16) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | B / 2 < ‖pilotCenter B (fun i => V (ξ i)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  apply pilotCenter_failure_probability hV u B _ k
  have ht := ScalarHeavyTailEstimator.moment_tail
    (X := fun ω => ‖V ω - u‖) (by positivity : 0 < B / 6) hp
    (by simpa only [abs_of_nonneg (norm_nonneg _)] using hmi)
    (by simpa only [abs_of_nonneg (norm_nonneg _)] using hm)
  simp only [abs_of_nonneg (norm_nonneg _)] at ht
  exact ht.trans hsize

end OracleTemplate.RobustGradient
