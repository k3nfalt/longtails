import LongTails.Proofs.AdditiveFixedPointBlocks
import LongTails.Proofs.AdditiveFixedPointLowerBudget

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.AdditiveFixedPointLowerExecution

open OracleTemplate HeavyTailedProductProcess AdditiveFixedPointProcess AdditiveFixedPointBlocks
open AdditiveFixedPointTesting AdditiveFixedPointFamily AdditiveFixedPointNoise AdditiveFixedPointLowerBudget
open LongTails.Setups.AdditiveCubeFixedPoint

variable {p : Params}

noncomputable def streams (p : Params) : ProbabilityMeasure (ℕ → Point p) :=
  ⟨Measure.infinitePi (fun _ : ℕ => law (variance p) 0), inferInstance⟩

noncomputable def oracle (T : Cube p → Cube p) : Oracle (Cube p) (Point p) where
  Seed := fun _ => Point p
  law := streams p
  answer := fun _ (_, x) z => (T x).val + z

lemma admissible {T : Cube p → Cube p} (hT : LipschitzWith 1 T) (hd : 0 < p.d) :
    spec.admissible p T (oracle T) := by
  let v := variance p
  refine ⟨hT, ⟨law v 0, inferInstance⟩, streams p, StochasticGeneralized.infinitePi_iid (law (d := p.d) v 0),
    (law_memLp v 1).integrable (by simp), law_centered v, (law_memLp v 2).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0), ?_, rfl⟩
  change (∫ z : Point p, ‖z‖ ^ 2 ∂law v 0) ≤ p.σ ^ 2
  by_cases hv : v = 0
  · rw [hv]
    simp [law, ProbabilityTheory.gaussianReal_zero_var, ← Measure.infinitePi_eq_pi,
      Measure.infinitePi_dirac]
    change ‖(0 : Point p)‖ ^ 2 ≤ p.σ ^ 2
    simp [sq_nonneg]
  exact (second_moment hd hv).trans (variance_admissible p hd)

lemma recover {L : ℕ} {t : ℕ → Bool} (he : 0 < p.ε) (hd : L + 1 ≤ p.d)
    (hr : ((L + 1 : ℕ) : ℝ) * (6 * p.ε) < p.R) (x : Cube p)
    (hx : dist (map (by positivity : 0 ≤ 8 * p.ε) t (L+1) x) x ≤ 6 * p.ε) :
    guess L 1 x 0 = t L := by
  have ha := residual_recovers (by positivity : 0 ≤ 6 * p.ε) (by linarith : 6 * p.ε < 8 * p.ε)
    t hd hr x hx L (by omega)
  cases h : t L <;> simp [AdditiveFixedPointChain.orient, h] at ha <;> simp [guess, *]
  linarith

lemma success_requires_recovery {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    {L : ℕ} (t : ℕ → Bool) (he : 0 < p.ε) (hd : L + 1 ≤ p.d)
    (hr : ((L + 1 : ℕ) : ℝ) * (6 * p.ε) < p.R) (out : Ω → Cube p)
    (hs : spec.successful p (map (by positivity : 0 ≤ 8 * p.ε) t (L+1)) out P) :
    ¬ (∫⁻ z, test (fun x => guess L 1 (out x) 0) (t L) z ∂(P : Measure Ω)) ≤ 3 / 4 := by
  intro hbad
  obtain ⟨hm, hi, hacc⟩ := hs
  let F := fun z => dist (map (by positivity : 0 ≤ 8 * p.ε) t (L+1) (out z)) (out z)
  let g := fun x => guess L 1 (out x) 0
  have hm' : Measurable g := (measurable_pi_apply 0).comp ((guess_measurable L 1).comp hm)
  have hF (z) : 0 ≤ F z := dist_nonneg
  have hi' : Integrable (fun z => F z / (6 * p.ε)) (P : Measure Ω) := hi.div_const _
  have hint : ∫⁻ z, ENNReal.ofReal (F z / (6 * p.ε)) ∂(P : Measure Ω) ≤ 1 / 6 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi' (ae_of_all _ (fun z => div_nonneg (hF z) (by positivity))),
      integral_div]
    have h := (div_le_iff₀ (by positivity : 0 < 6 * p.ε)).mpr (show
      (∫ z, F z ∂(P : Measure Ω)) ≤ 1/6 * (6*p.ε) by change (∫ z, F z ∂(P : Measure Ω)) ≤ p.ε at hacc; linarith)
    simpa [ENNReal.ofReal_div_of_pos] using ENNReal.ofReal_le_ofReal h
  have hpoint (z) : 1 ≤ test g (t L) z + ENNReal.ofReal (F z / (6 * p.ε)) := by
    by_cases h : g z = t L
    · simp [test, h]
    · have hh : ¬ F z ≤ 6 * p.ε := fun h' => h (recover he hd hr (out z) h')
      simp only [test, h, ite_false, zero_add]
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ (by positivity)]
      linarith
  have hh := lintegral_mono (μ := (P : Measure Ω)) hpoint
  rw [lintegral_const, measure_univ, mul_one, lintegral_add_left (test_measurable hm' _)] at hh
  have hh' := hh.trans (add_le_add hbad hint)
  have hnum := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hh'
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hnum
  norm_num at hnum

end LongTails.Proofs.AdditiveFixedPointLowerExecution
