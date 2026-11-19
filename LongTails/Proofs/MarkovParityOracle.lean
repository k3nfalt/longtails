import LongTails.Proofs.MarkovParityChain
import LongTails.Proofs.MarkovParityParameters
import LongTails.Proofs.MarkovParitySimulation

open MeasureTheory ProbabilityTheory OracleTemplate

namespace LongTails.Proofs.MarkovParityOracle

open MarkovParityProgress MarkovParityChain MarkovParitySimulation MarkovParityParameters
open AbcHardOracle AbcHardFunction AbcHardGeometry AbcHardContinuity
open AbcLowerParameters AbcLowerAssembly OracleTemplate.MarkovProduct PolynomialMixingLowerBound
open LongTails.Setups.MarkovSmoothNonconvex
open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex (pathLaw)

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

lemma draw_law {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {q : ℝ} (hq : 0 ≤ q) (hq' : 2 * q ≤ 1) (m : ℕ) (F : ℝ → E) :
    (∫ z, F (draw m z) ∂(colorLaw q hq hq' : Measure Color)) =
      q • F 0 + (1 - q) • F 2 := by
  rw [finite_integral, Fintype.sum_option, Fintype.sum_bool]
  simp only [colorLaw_real]
  by_cases h : m % 2 = 1 <;> simp [draw, accepts, weight, h] <;> module

noncomputable def stationary (p : Params) (hv : spec.valid p) :=
  colorLaw (chance p) (chance_pos p hv).le (chance_small p hv)

noncomputable def refresh (p : Params) (hv : spec.valid p) : unitInterval :=
  ⟨1 / p.τ, by
    have ht : 1 ≤ p.τ := hv.2.2.1
    exact ⟨one_div_nonneg.mpr (by linarith), (div_le_one (by linarith : 0 < p.τ)).mpr ht⟩⟩

noncomputable def trajectory (p : Params) (hv : spec.valid p) :=
  pathLaw (refreshKernel (stationary p hv) (refresh p hv)) (stationary p hv)

noncomputable def scale (p : Params) (hv : spec.valid p) : Scale :=
  scaleOf (geometry p) hv.1 hv.2.1

noncomputable abbrev dim (p : Params) := chainDim (geometry p)

noncomputable def oracle (p : Params) (hv : spec.valid p) (π : Fin (dim p + 1) ↪ Fin p.d) :
    Oracle (Space p) (Space p) where
  Seed := fun _ => Color
  law := trajectory p hv
  answer := fun _ (_, x) z => response (scale p hv) (chance p) π p.x0 x z

set_option maxHeartbeats 800000 in
lemma admissible (p : Params) (hv : spec.valid p) (π : Fin (dim p + 1) ↪ Fin p.d) :
    spec.admissible p (objective (scale p hv) π p.x0) (oracle p hv π) := by
  obtain ⟨_, _, _, _, _, _, hg, hl, hlo, _, hgap, _⟩ :=
    AbcLowerAssembly.hard_admissible (geometry p) (geometry_valid p hv) π
  let S := scale p hv
  let q := chance p
  let law := stationary p hv
  let r := refresh p hv
  have hq : 0 < q := chance_pos p hv
  have hq' : 2 * q ≤ 1 := chance_small p hv
  have hq1 : q ≤ 1 := by linarith
  refine ⟨hg, hl, fun x => ?_, Color, colorMeasurable, refreshKernel law r,
    inferInstance, law, response S q π p.x0, rfl, refreshKernel_stationary _ _, ?_, ?_,
    fun x => finite_integrable _ _, ?_, fun x => finite_integrable _ _, ?_⟩
  · exact (sub_le_sub_left (hlo x) _).trans hgap
  · intro t z
    have h := refresh_mixing law r t z
    refine h.trans ?_
    have he : -(r : ℝ) * t = -(t : ℝ) / p.τ := by dsimp [r, refresh]; ring
    rw [he]; linarith [Real.exp_pos (-(t : ℝ) / p.τ)]
  · let m := fun x => stage (sel π (toUnit S p.x0 x))
    have hm : Measurable m := stage_measurable S π p.x0
    have hz : Measurable (fun v : Space p × Color => draw (m v.1) v.2) :=
      (measurable_of_countable (Function.uncurry draw)).comp ((hm.comp measurable_fst).prodMk measurable_snd)
    change Measurable ((Function.uncurry (reply S (fun _ => q) π p.x0)) ∘
      (fun v : Space p × Color => (v.1, draw (m v.1) v.2)))
    exact (reply_measurable S (fun _ => q) π p.x0).comp (measurable_fst.prodMk hz)
  · intro x
    let m := stage (sel π (toUnit S p.x0 x))
    rw [objective_gradient]
    change (∫ z, reply S _ π p.x0 x (draw m z) ∂(colorLaw q hq.le hq' : Measure Color)) = _
    erw [draw_law hq.le hq' m (reply S (fun _ => q) π p.x0 x)]
    simp only [reply, coin, ite_eq_left hq.le, ite_eq_right (show ¬ (2 : ℝ) ≤ q by linarith),
      zero_smul, add_zero, smul_add, smul_smul, mul_one_div_cancel hq.ne', one_smul]
    module
  · intro x
    let m := stage (sel π (toUnit S p.x0 x))
    let u := knownPart S π m p.x0 x
    let v := objGrad S π p.x0 x
    rw [objective_gradient]
    change (∫ z, ‖reply S _ π p.x0 x (draw m z) - v‖ ^ 2 ∂(colorLaw q hq.le hq' : Measure Color)) ≤ _
    erw [draw_law hq.le hq' m (fun t => ‖reply S (fun _ => q) π p.x0 x t - v‖ ^ 2)]
    change q * ‖u + coin q 0 • (v - u) - v‖ ^ 2 +
      (1 - q) * ‖u + coin q 2 • (v - u) - v‖ ^ 2 ≤ _
    have he : u + (1 / q) • (v - u) - v = (1 / q - 1) • (v - u) := by module
    simp only [coin, ite_eq_left hq.le, ite_eq_right (show ¬ (2 : ℝ) ≤ q by linarith),
      he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, zero_smul, add_zero, norm_sub_rev u v]
    have hsec := secret_norm S π p.x0 x
    have hratio : S.a / S.lam = 60 * p.ε := amplitude_ratio (geometry p) hv.1 hv.2.1
    change ‖v - u‖ ≤ _ at hsec
    rw [hratio] at hsec
    have hε := hv.2.1
    have hs : 0 < p.σ := by linarith [hv.2.2.2.1]
    have hcal : q * p.σ ^ 2 = 2 ^ 22 * p.ε ^ 2 := by
      dsimp [q, chance]
      field_simp
    have hh := pow_le_pow_left₀ (norm_nonneg _) hsec 2
    calc
      _ = (1 / q - 1) * ‖v - u‖ ^ 2 := by field_simp; ring
      _ ≤ (1 / q) * ‖v - u‖ ^ 2 := by nlinarith [sq_nonneg ‖v - u‖]
      _ ≤ p.σ ^ 2 := by
        rw [one_div_mul_eq_div, div_le_iff₀ hq]
        nlinarith [sq_nonneg p.ε]

end LongTails.Proofs.MarkovParityOracle
