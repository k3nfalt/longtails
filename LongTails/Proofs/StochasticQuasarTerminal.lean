import LongTails.Proofs.StochasticQuasarProcess
import LongTails.Proofs.StochasticQuasarTailTuning

open MeasureTheory Set
open scoped ENNReal

namespace OracleTemplate.StochasticQuasar

open GradientOnlyQuasar

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma shifted_barrier_eq_one {f : E → ℝ} {u x z : E} {A B : ℝ} {p : ℕ}
    (hB : 0 < B) (he : B ≤ weightedEnergy f u A x z) :
    shiftedEnergyBarrier f u A B p x z = 1 := by
  apply barrier_eq_one
  apply one_le_pow₀
  apply (le_div_iff₀ (by positivity : 0 < 2 * B)).mpr
  linarith

omit [InnerProductSpace ℝ E] in
lemma terminal_energy_probability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : E → ℝ} {A : ℝ → ℝ} (hf : Continuous f) (hA : Continuous A)
    (u : E) {B ρ T : ℝ} (hB : 0 < B) (hρ : 0 ≤ ρ) (p : ℕ)
    (S : Ω → ℝ × E × E) (hS : Measurable S) {v : ℝ≥0∞}
    (hm : (∫⁻ ω, ENNReal.ofReal (compensatedEnergyBarrier f u A B ρ p (S ω)) ∂μ) ≤ v) :
    μ {ω | (S ω).1 ≤ T ∧ B ≤ weightedEnergy f u (A (S ω).1) (S ω).2.1 (S ω).2.2} ≤
      ENNReal.ofReal (Real.exp (ρ * T)) * v := by
  let V := fun ω => ENNReal.ofReal (compensatedEnergyBarrier f u A B ρ p (S ω))
  have hV : Measurable V := ENNReal.measurable_ofReal.comp
    ((continuous_compensated_barrier hf hA u B ρ p).measurable.comp hS)
  have hh := meas_le_lintegral₀ (μ := μ) ((measurable_const.mul hV).aemeasurable)
    (s := {ω | (S ω).1 ≤ T ∧ B ≤ weightedEnergy f u (A (S ω).1) (S ω).2.1 (S ω).2.2})
    (f := fun ω => ENNReal.ofReal (Real.exp (ρ * T)) * V ω) (by
      intro ω hω
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.one_le_ofReal.mpr
      unfold compensatedEnergyBarrier
      rw [shifted_barrier_eq_one hB hω.2, mul_one, ← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have ht := mul_le_mul_of_nonneg_left hω.1 hρ
      linarith)
  rw [lintegral_const_mul _ hV] at hh
  apply hh.trans
  gcongr

omit [InnerProductSpace ℝ E] in
lemma initial_shifted_barrier_bound {f : E → ℝ} {u x : E} {L D : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hgap0 : 0 ≤ f x - f u)
    (hgap : f x - f u ≤ L * D ^ 2) (hdist : ‖x - u‖ ≤ D) (p : ℕ) :
    shiftedEnergyBarrier f u (1 / (4 * L)) (8 * D ^ 2) p x x ≤ 2 * (9 / 16 : ℝ) ^ p := by
  have hd := pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hg := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 1 / (4 * L))
  have he : 1 / (4 * L) * (L * D ^ 2) = D ^ 2 / 4 := by field_simp
  rw [he] at hg
  have henergy : weightedEnergy f u (1 / (4 * L)) x x ≤ 3 * D ^ 2 / 4 := by
    unfold weightedEnergy
    linarith
  have henergy0 : 0 ≤ weightedEnergy f u (1 / (4 * L)) x x := by
    unfold weightedEnergy
    positivity
  have hb : (weightedEnergy f u (1 / (4 * L)) x x + 8 * D ^ 2) / (2 * (8 * D ^ 2)) ≤ 9 / 16 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (8 * D ^ 2))).mpr
    nlinarith [sq_nonneg D]
  apply (barrier_le_twice _).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb p) (by norm_num)

lemma energy_large_of_terminal_gap {q : LongTails.Setups.StochasticConstrainedQuasar.Params}
    (hv : LongTails.Setups.StochasticConstrainedQuasar.spec.valid q)
    {f : q.E → ℝ} {u x z : q.E} {t : ℝ} (ht : 2 * outerHorizon q ≤ t)
    (hgap : q.ε / 8 < f x - f u) :
    8 * q.D ^ 2 ≤ weightedEnergy f u (outerWeight q t) x z := by
  have hL := hv.1
  have hε := hv.2.2.2.2.2.1
  have ha : 64 * q.D ^ 2 / q.ε ≤ outerWeight q t := by
    rw [outer_weight_final hv ht]
    have hh : 0 ≤ 1 / (4 * q.L) := by positivity
    linarith
  have hb := mul_le_mul_of_nonneg_right ha (by positivity : 0 ≤ q.ε / 8)
  have he : (64 * q.D ^ 2 / q.ε) * (q.ε / 8) = 8 * q.D ^ 2 := by field_simp; ring
  rw [he] at hb
  have hh := mul_le_mul_of_nonneg_left hgap.le (outer_weight_pos hv t).le
  unfold weightedEnergy
  nlinarith [sq_nonneg ‖z - u‖]

end OracleTemplate.StochasticQuasar
