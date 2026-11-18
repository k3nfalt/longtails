import LongTails.Algorithms.MarkovClippedSgd
import LongTails.Proofs.MarkovClippedDrift

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.MarkovClippedTuning

open LongTails.Setups.MarkovSmoothNonconvex LongTails.Algorithms.MarkovClippedSgd MarkovClippedDrift
open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex (mixingDistance)
open HeavyTailedMarkovGradient

variable (p : Params) (hv : spec.valid p)
include hv

lemma constants :
    0 < p.σ ∧ 0 < threshold p ∧ 0 < stepSize p ∧ p.L * stepSize p ≤ 1 / 8 ∧
    8 * p.σ ≤ threshold p ∧ p.ε ≤ threshold p / 8 ∧
    2 * p.σ ^ 2 / threshold p ≤ p.ε / 32 ∧
    p.L * stepSize p * p.σ ^ 2 ≤ p.ε ^ 2 / 512 ∧ p.L * stepSize p * threshold p ≤ p.ε := by
  obtain ⟨hL, hε, _, hσ, _⟩ := hv
  have hs : 0 < p.σ := by linarith
  have hC : 0 < threshold p := by unfold threshold; positivity
  have hη : 0 < stepSize p := by unfold stepSize; positivity
  have hs' : p.ε ≤ p.σ := by linarith
  have hsq := pow_le_pow_left₀ hε.le hs' 2
  have hprod := mul_le_mul_of_nonneg_right hs' hs.le
  have hc : 8 * p.σ ≤ threshold p := by
    unfold threshold
    rw [le_div_iff₀ hε]
    nlinarith
  have he : p.ε ≤ threshold p / 8 := by linarith
  have hh : p.L * stepSize p = p.ε / (64 * threshold p) := by unfold stepSize; field_simp
  refine ⟨hs, hC, hη, ?_, hc, he, ?_, ?_, ?_⟩
  · rw [hh, div_le_iff₀ (by positivity)]; linarith
  · unfold threshold; field_simp; ring_nf; rfl
  · rw [hh]; unfold threshold; field_simp; nlinarith [sq_nonneg p.ε, sq_nonneg p.σ]
  · rw [hh]; field_simp; nlinarith

lemma period_pos_and_mix : 0 < period p ∧
    2 * Real.exp (-(period p : ℝ) / p.τ) ≤ p.ε / (64 * threshold p) := by
  obtain ⟨_, hε, hτ, hσ, _⟩ := hv
  have ht : 0 < p.τ := by linarith
  have hs : p.ε < p.σ := by linarith
  have hs' := pow_lt_pow_left₀ hs hε.le (by decide : 2 ≠ 0)
  let v := 8192 * p.σ ^ 2 / p.ε ^ 2
  have hv1 : 1 < v := by dsimp [v]; rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hn : p.τ * Real.log v ≤ (period p : ℝ) := Nat.le_ceil _
  constructor
  · exact Nat.ceil_pos.mpr (mul_pos ht (Real.log_pos hv1))
  · have hrad : -(period p : ℝ) / p.τ ≤ -Real.log v := by
      rw [div_le_iff₀ ht]; linarith
    refine (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrad) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq ?_
    rw [Real.exp_neg, Real.exp_log (by linarith : 0 < v)]
    dsimp [v, threshold]; field_simp; ring

lemma steps_suffice : p.Δ ≤ (steps p + 1 : ℕ) * stepSize p * p.ε ^ 2 / 8 := by
  obtain ⟨hL, hε, _, hσ, hreg, _⟩ := hv
  have hs : 0 < p.σ := by linarith
  have hK := Nat.le_ceil (32768 * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4)
  change _ ≤ (steps p : ℝ) at hK
  rw [div_le_iff₀ (by positivity)] at hK
  push_cast
  unfold stepSize threshold
  field_simp
  nlinarith [sq_nonneg (p.ε ^ 2)]

noncomputable def score (p : Params) (u v : Space p) : ℝ :=
  drift (p.L * stepSize p) (threshold p) u v + p.ε / 4 * ‖u‖ - p.ε ^ 2 / 8

lemma score_bound (u v : Space p) :
    |score p u v| ≤ p.L * stepSize p / 2 * (threshold p) ^ 2 +
      (threshold p + p.ε / 4) * ‖u‖ + p.ε ^ 2 / 8 := by
  obtain ⟨_, hc, hη, _⟩ := constants p hv
  have hε := hv.2.1
  have hd := drift_bound (mul_pos hv.1 hη).le hc.le u v
  unfold score
  calc
    _ ≤ |drift (p.L * stepSize p) (threshold p) u v + p.ε / 4 * ‖u‖| + |p.ε ^ 2 / 8| := abs_sub _ _
    _ ≤ _ := by
      have hh := abs_add_le (drift (p.L * stepSize p) (threshold p) u v) (p.ε / 4 * ‖u‖)
      rw [abs_of_nonneg (by positivity : 0 ≤ p.ε / 4 * ‖u‖)] at hh
      rw [abs_of_nonneg (by positivity : 0 ≤ p.ε ^ 2 / 8)]
      linarith

omit hv in
lemma score_measurable : Measurable (Function.uncurry (score p)) :=
  ((drift_measurable _ _).add (measurable_fst.norm.const_mul _)).sub_const _

set_option maxHeartbeats 800000 in
lemma score_mean {Z : Type} [MeasurableSpace Z] (π : ProbabilityMeasure Z) (ν : Measure Z)
    [IsProbabilityMeasure ν] {g : Z → Space p} {u : Space p} (hg : Measurable g)
    (hi : Integrable g (π : Measure Z)) (hmean : ∫ z, g z ∂(π : Measure Z) = u)
    (hmi : Integrable (fun z => ‖g z - u‖ ^ 2) (π : Measure Z))
    (hm : (∫ z, ‖g z - u‖ ^ 2 ∂(π : Measure Z)) ≤ p.σ ^ 2)
    (hmix : ∀ W : Z → ℝ, Measurable W → ∀ B : ℝ, 0 ≤ B → (∀ z, |W z| ≤ B) →
      |(∫ z, W z ∂ν) - ∫ z, W z ∂(π : Measure Z)| ≤ 2 * B * (p.ε / (64 * threshold p))) :
    ∫ z, score p u (g z) ∂ν ≤ 0 := by
  obtain ⟨hs, hC, hη, hγ1, hlarge, heC, hbias, hnoise, hγC⟩ := constants p hv
  have hε := hv.2.1
  let γ := p.L * stepSize p
  let C := threshold p
  have hγ : 0 ≤ γ := (mul_pos hv.1 hη).le
  let W := fun z => drift γ C u (g z)
  let B := γ / 2 * C ^ 2 + C * ‖u‖
  have hB : 0 ≤ B := add_nonneg (mul_nonneg (div_nonneg hγ (by norm_num)) (sq_nonneg C)) (mul_nonneg hC.le (norm_nonneg u))
  have hp : Measurable (fun z : Z => (u, g z)) := measurable_const.prodMk hg
  have hW := (drift_measurable (E := Space p) γ C).comp hp
  change Measurable W at hW
  have hbd (z : Z) : |W z| ≤ B := drift_bound hγ hC.le u (g z)
  have hpert := (le_abs_self _).trans (hmix W hW B hB hbd)
  have hid := stationary_drift (μ := (π : Measure Z)) (γ := γ) (C := C) (g := g) (u := u) hg hi hmean hε hs hC hγ hγ1 hlarge heC hbias hnoise hmi hm
  have hsmall : 2 * B * (p.ε / (64 * C)) ≤ p.ε ^ 2 / 64 + p.ε / 32 * ‖u‖ := by
    have he : 2 * B * (p.ε / (64 * C)) = γ * C * p.ε / 64 + p.ε / 32 * ‖u‖ := by
      dsimp only [B]; field_simp [show C ≠ 0 from hC.ne']; ring
    rw [he]
    change γ * C ≤ p.ε at hγC
    linarith only [mul_le_mul_of_nonneg_right hγC hε.le]
  have hWi : Integrable W ν := Integrable.of_bound hW.aestronglyMeasurable B (.of_forall hbd)
  change (∫ z, W z + p.ε / 4 * ‖u‖ - p.ε ^ 2 / 8 ∂ν) ≤ 0
  rw [integral_sub (f := fun z => W z + p.ε / 4 * ‖u‖) (hWi.add (integrable_const _)) (integrable_const (p.ε ^ 2 / 8)),
    integral_add hWi (integrable_const (p.ε / 4 * ‖u‖))]
  simp only [integral_const, probReal_univ, one_smul]
  change (∫ z, W z ∂(π : Measure Z)) ≤ _ at hid
  change _ ≤ 2 * B * (p.ε / (64 * C)) at hpert
  linarith only [hpert, hid, hsmall, mul_nonneg hε.le (norm_nonneg u), sq_nonneg p.ε]

end LongTails.Proofs.MarkovClippedTuning
