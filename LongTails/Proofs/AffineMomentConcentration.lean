import LongTails.Proofs.AffineMomentAcceleratedGeometry
import LongTails.Proofs.RobustEnergyConcentration

open MeasureTheory
open LongTails.Algorithms.AffineMomentAccelerated
open LongTails.Proofs.AffineMomentAcceleratedGeometry

namespace LongTails.Proofs.AffineMomentConcentration

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma centered_square_le {Z : Ω → ℝ} (hZi : Integrable Z P)
    (hZ2i : Integrable (fun ω => (Z ω) ^ 2) P) (c : ℝ) :
    (∫ ω, (Z ω - ∫ z, Z z ∂P) ^ 2 ∂P) ≤ ∫ ω, (Z ω - c) ^ 2 ∂P := by
  have he (b : ℝ) : (∫ ω, (Z ω - b) ^ 2 ∂P) =
      (∫ ω, (Z ω) ^ 2 ∂P) - 2 * b * (∫ ω, Z ω ∂P) + b ^ 2 := by
    have hf : (fun ω => (Z ω - b) ^ 2) =
        (fun ω => (Z ω) ^ 2 - (2 * b) * Z ω + b ^ 2) := by funext ω; ring
    have hi : Integrable (fun ω => (Z ω) ^ 2 - (2 * b) * Z ω) P := hZ2i.sub (hZi.const_mul _)
    rw [hf, integral_add hi (integrable_const _),
      integral_sub hZ2i (hZi.const_mul _), integral_const_mul, integral_const]
    simp
  rw [he, he]
  nlinarith [sq_nonneg ((∫ ω, Z ω ∂P) - c)]

lemma unit_range_centered_mgf {Z : Ω → ℝ} (hZ : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω) (hZ2 : ∀ ω, Z ω ≤ 2) {c v t : ℝ}
    (hv : (∫ ω, (Z ω - c) ^ 2 ∂P) ≤ v) (ht : 0 ≤ t) (ht2 : t ≤ 1 / 2) :
    Integrable (fun ω => Real.exp (t * (Z ω - ∫ z, Z z ∂P))) P ∧
    (∫ ω, Real.exp (t * (Z ω - ∫ z, Z z ∂P)) ∂P) ≤ Real.exp (t ^ 2 * v) := by
  have hZi : Integrable Z P := Integrable.of_bound hZ.aestronglyMeasurable 2
    (Filter.Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs, abs_of_nonneg (hZ0 ω)] using hZ2 ω)
  have hZ2i : Integrable (fun ω => (Z ω) ^ 2) P := Integrable.of_bound
    (hZ.pow_const 2).aestronglyMeasurable 4 (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hZ0 ω, hZ2 ω])
  have hm0 : 0 ≤ ∫ ω, Z ω ∂P := integral_nonneg hZ0
  have hm2 : (∫ ω, Z ω ∂P) ≤ 2 := by
    have h := integral_mono hZi (integrable_const (2 : ℝ)) hZ2
    simpa using h
  have hb (ω : Ω) : |t * (Z ω - ∫ z, Z z ∂P)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ht]
    have hz : |Z ω - ∫ z, Z z ∂P| ≤ 2 := abs_le.mpr ⟨by linarith [hZ0 ω], by linarith [hZ2 ω]⟩
    nlinarith
  have hmean : (∫ ω, t * (Z ω - ∫ z, Z z ∂P) ∂P) = 0 := by
    rw [integral_const_mul, integral_sub hZi (integrable_const _), integral_const]
    simp
  have hsecond : (∫ ω, (t * (Z ω - ∫ z, Z z ∂P)) ^ 2 ∂P) ≤ t ^ 2 * v := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left ((centered_square_le hZi hZ2i c).trans hv) (sq_nonneg t)
  simpa only [zero_add, Pi.sub_apply] using OracleTemplate.RobustGradient.bounded_increment_mgf
    (hZ.sub measurable_const |>.const_mul t) hb hmean.le hsecond

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] [SecondCountableTopology E] [InnerProductSpace ℝ E] in
lemma measurable_energy (u : E) : Measurable (energy u) := by
  unfold energy
  fun_prop

omit [CompleteSpace E] in
lemma measurable_mirrorStep (a : ℝ) (v : E) : Measurable (mirrorStep a v) := by
  exact (OracleTemplate.measurable_clip 1).comp (measurable_const.sub (measurable_const.smul measurable_id))

omit [CompleteSpace E] in
lemma mirror_centered_mgf {p a t m : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (ht2 : t ≤ 1 / 2)
    (u v : E) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) {G : Ω → E} (hG : Measurable G)
    (hGpi : Integrable (fun ω => ‖G ω‖ ^ p) P) (hGpm : (∫ ω, ‖G ω‖ ^ p ∂P) ≤ m) :
    Integrable (fun ω => Real.exp (t * (energy u (mirrorStep a v (G ω)) -
      ∫ z, energy u (mirrorStep a v (G z)) ∂P))) P ∧
    (∫ ω, Real.exp (t * (energy u (mirrorStep a v (G ω)) -
      ∫ z, energy u (mirrorStep a v (G z)) ∂P)) ∂P) ≤
        Real.exp (4 * t ^ 2 * a ^ p * m) := by
  let Z := fun ω => energy u (mirrorStep a v (G ω))
  have hZm : Measurable Z := (measurable_energy u).comp ((measurable_mirrorStep a v).comp hG)
  have hn (ω : Ω) : ‖mirrorStep a v (G ω)‖ ≤ 1 := OracleTemplate.norm_clip_le (by norm_num) _
  have hZ0 (ω : Ω) : 0 ≤ Z ω := energy_nonneg u _
  have hZ2 (ω : Ω) : Z ω ≤ 2 := energy_le_two u _ hu (hn ω)
  have hdiffi : Integrable (fun ω => (Z ω - energy u v) ^ 2) P := by
    apply Integrable.of_bound ((hZm.sub measurable_const).pow_const 2).aestronglyMeasurable 4
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hZ0 ω
      have h2 := hZ2 ω
      have h3 := energy_nonneg u v
      have h4 := energy_le_two u v hu hv
      change (Z ω - energy u v) ^ 2 ≤ 4
      have hd : |Z ω - energy u v| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hsq := pow_le_pow_left₀ (abs_nonneg _) hd 2
      rw [sq_abs] at hsq
      norm_num at hsq
      exact hsq
  have hm : (∫ ω, (Z ω - energy u v) ^ 2 ∂P) ≤ 4 * a ^ p * m := by
    calc
      _ ≤ ∫ ω, (4 * a ^ p) * ‖G ω‖ ^ p ∂P := integral_mono hdiffi
        (hGpi.const_mul _) (fun ω => mirror_energy_square hp hp2 ha u v (G ω) hu hv)
      _ = (4 * a ^ p) * ∫ ω, ‖G ω‖ ^ p ∂P := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hGpm (by positivity)
  have h := unit_range_centered_mgf hZm hZ0 hZ2 hm ht ht2
  simpa only [Z, mul_assoc, mul_left_comm, mul_comm] using h

lemma mirror_mean_energy {p a m : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (ha : 0 ≤ a)
    (u v : E) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) {G : Ω → E} (hG : Measurable G) (hGi : Integrable G P)
    (hGpi : Integrable (fun ω => ‖G ω‖ ^ p) P) (hGpm : (∫ ω, ‖G ω‖ ^ p ∂P) ≤ m) :
    (∫ ω, energy u (mirrorStep a v (G ω)) ∂P) ≤ energy u v -
      a * inner ℝ (∫ ω, G ω ∂P) (v - u) + 4 * a ^ p * m := by
  have hZ : Measurable (fun ω => energy u (mirrorStep a v (G ω))) :=
    (measurable_energy u).comp ((measurable_mirrorStep a v).comp hG)
  have hZi : Integrable (fun ω => energy u (mirrorStep a v (G ω))) P := by
    apply Integrable.of_bound hZ.aestronglyMeasurable 2
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (energy_nonneg u _)]
      exact energy_le_two u _ hu (OracleTemplate.norm_clip_le (by norm_num) _)
  have hcrossi : Integrable (fun ω => inner ℝ (G ω) (v - u)) P := hGi.inner_const _
  have hleft : Integrable (fun ω => energy u v -
      a * inner ℝ (G ω) (v - u)) P := (integrable_const _).sub (hcrossi.const_mul a)
  have hb := integral_mono hZi (hleft.add (hGpi.const_mul (4 * a ^ p)))
    (fun ω => mirror_power hp hp2 ha u v (G ω) hu hv)
  change (∫ ω, energy u (mirrorStep a v (G ω)) ∂P) ≤
    ∫ ω, (energy u v - a * inner ℝ (G ω) (v - u)) +
      (4 * a ^ p) * ‖G ω‖ ^ p ∂P at hb
  rw [integral_add hleft (hGpi.const_mul _),
    integral_sub (integrable_const _) (hcrossi.const_mul a), integral_const,
    integral_const_mul, integral_const_mul] at hb
  have hc : (∫ ω, inner ℝ (G ω) (v - u) ∂P) =
      inner ℝ (∫ ω, G ω ∂P) (v - u) := by
    simp_rw [real_inner_comm (v - u)]
    exact integral_inner hGi _
  rw [hc] at hb
  simp only [probReal_univ, smul_eq_mul, one_mul] at hb
  have hm := mul_le_mul_of_nonneg_left hGpm (show 0 ≤ 4 * a ^ p by positivity)
  linarith

end LongTails.Proofs.AffineMomentConcentration
