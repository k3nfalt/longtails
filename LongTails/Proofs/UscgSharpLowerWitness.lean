import LongTails.Proofs.UscgSharpQuadraticPath
import LongTails.Proofs.UscgSharpShock
import LongTails.Proofs.UscgSharpLowerTuning

namespace LongTails.Proofs.UscgSharpLowerWitness

open MeasureTheory
open LongTails.Setups.UscgConstant (Space IsBallLMO Problem dualNorm)
open UscgSharpScalar UscgSharpScalarPath

structure Witness (L σ Δ ε δ α η : ℝ) (T : ℕ) (lmo : Space 1 → Space 1) where
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  law : Measure Ω
  [probability : IsProbabilityMeasure law]
  f : ℝ → ℝ
  f' : ℝ → ℝ
  noise : Ω → ℝ
  derivative : ∀ x, HasDerivAt f (f' x) x
  problem : Problem (normSeminorm ℝ (Space 1)) L L σ Δ 0
    (lift f) (oracle f' noise) law
  failure : δ < (Measure.infinitePi (fun _ : ℕ => law)).real
    {ξ | ε * T < ∑ t ∈ Finset.range T, dualNorm (normSeminorm ℝ (Space 1))
      (gradient (lift f) (trajectory α η f' noise lmo ξ t).1)}

lemma quadratic_witness {L σ Δ ε ell α η : ℝ} {T : ℕ} (lmo : Space 1 → Space 1)
    (hL : 0 < L) (he : 0 < ε) (hσ : ε ≤ σ) (hΔ : 0 ≤ Δ)
    (ha : 0 < α) (ha1 : α ≤ 1 / 2) (hη : 0 < η) (hT : 4 ≤ T)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo)
    (hell : 256 ≤ ell) (htlog : Real.log (T : ℝ) ≤ 17 * ell / 256)
    (hD : 256 ≤ L * Δ / ε ^ 2)
    (horizon : 64 * α * T ≤ Real.sqrt (L * Δ / ε ^ 2) * ell)
    (hprogress : Δ ≤ 4 * ε * η * T) :
    Nonempty (Witness L σ Δ ε (Real.exp (-ell)) α η T lmo) := by
  let δ := Real.exp (-ell)
  have hδ : 0 < δ := Real.exp_pos _
  have hTp : 0 < T := by omega
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hTp
  have hsmall := UscgSharpLowerTuning.confidence_small hell hTp htlog
  have hδsmall : 4 * δ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hTr hδ.le]
  let p : unitInterval := ⟨4 * δ, ⟨by positivity, hδsmall⟩⟩
  let B := σ / (2 * Real.sqrt δ)
  let k := UscgSharpLowerTuning.excursionLength T ell α
  have hellα : 16 * α ≤ ell := by linarith
  have hk := UscgSharpLowerTuning.length_bounds hT ha hellα
  have hkp : 0 < k := hk.1
  have hkT : k < T := hk.2.1
  have hdecay := UscgSharpLowerTuning.decay_lower ha ha1 hk.2.2.1
  have hgeometry : 16 * ε ^ 2 * (T : ℝ) ^ 2 ≤ L * Δ * (k : ℝ) ^ 2 := by
    have hh := UscgSharpLowerTuning.length_geometry hD hT ha hellα horizon
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ε)
    have hid : ε ^ 2 * (L * Δ / ε ^ 2) = L * Δ := by field_simp
    nlinarith [hid]
  have hbad : ∀ ξ ∈ UscgSharpShock.streamEvent T,
      ε * T < ∑ t ∈ Finset.range T, dualNorm (normSeminorm ℝ (Space 1))
        (gradient (lift (UscgSharpInstances.quadratic L))
          (trajectory α η (fun x => L * x) (UscgSharpShock.noise B) lmo ξ t).1) := by
    intro ξ hξ
    have hfirst : UscgSharpShock.noise B (ξ 0) = -B := by
      simpa using UscgSharpShock.stream_noise hξ B hTp
    have hzero : ∀ t, 1 ≤ t → t ≤ k → UscgSharpShock.noise B (ξ t) = 0 := by
      intro t ht htk
      simpa [show t ≠ 0 by omega] using UscgSharpShock.stream_noise hξ B (lt_of_le_of_lt htk hkT)
    have hBp : 0 < B := by dsimp [B]; exact div_pos (by linarith) (by positivity)
    by_cases hstep : L * η ≤ ε * T
    · have hshock := UscgSharpLowerTuning.shock_amplitude hσ he hL.le hη.le hTp hkT.le hstep hsmall.2 hdecay
      have hx := UscgSharpQuadraticPath.excursion (UscgSharpShock.noise B) lmo ξ ha (by linarith)
        hBp.le hL hη hkp hlmo hfirst hzero hshock
      have harea := UscgSharpQuadraticPath.gradient_area (UscgSharpShock.noise B) lmo ξ hL.le hη.le hkT hx
      have hfail := UscgSharpQuadraticPath.area_failure hL.le he hTp hprogress hgeometry
      have hpos : 0 < ε * (T : ℝ) := by positivity
      linarith
    · have hh := UscgSharpQuadraticPath.first_step_area (UscgSharpShock.noise B) lmo ξ
        ha (by linarith) hBp hL.le hη.le (by omega : 1 < T) hlmo hfirst
      exact (lt_of_not_ge hstep).trans_le hh
  have hvar : (p : ℝ) * B ^ 2 = σ ^ 2 := by
    dsimp [p, B]
    rw [div_pow, mul_pow, Real.sq_sqrt hδ.le]
    field_simp
    ring
  refine ⟨{
    Ω := Bool × Bool
    measurableΩ := inferInstance
    law := UscgSharpShock.law p
    probability := inferInstance
    f := UscgSharpInstances.quadratic L
    f' := fun x => L * x
    noise := UscgSharpShock.noise B
    derivative := UscgSharpInstances.quadratic_derivative L
    problem := UscgSharpInstances.quadratic_problem hL.le hΔ (measurable_of_countable _)
      Integrable.of_finite (UscgSharpShock.mean p B) Integrable.of_finite
      (by rw [UscgSharpShock.variance, hvar])
    failure := ?_ }⟩
  have hpEvent : 3 / 2 * δ ≤ (Measure.infinitePi fun _ : ℕ => UscgSharpShock.law p).real
      (UscgSharpShock.streamEvent T) := by
    rw [UscgSharpShock.stream_probability p hTp]
    exact UscgSharpShock.probability_lower hδ.le hδsmall hsmall.1
  have hm := measureReal_mono hbad (measure_ne_top (Measure.infinitePi fun _ : ℕ => UscgSharpShock.law p) _)
  change δ < _
  exact ((show δ < 3 / 2 * δ by linarith).trans_le hpEvent).trans_le hm

end LongTails.Proofs.UscgSharpLowerWitness
