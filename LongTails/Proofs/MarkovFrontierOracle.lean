import LongTails.Proofs.MarkovFrontierScales
import LongTails.Proofs.MarkovFrontierHiding
import LongTails.Proofs.MarkovFrontierOccupancy

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.MarkovFrontierOracle

attribute [-instance] Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Setups.MarkovSmoothNonconvex
open LongTails.Setups.HighDimensionalMarkovSmoothNonconvex (Valid)
open Setups.HeavyTailedMarkovSmoothAndConvex (pathLaw mixingDistance)
open MarkovFrontierScales MarkovFrontierPhases MarkovFrontierSimulation
open AbcLowerAssembly AbcLowerParameters AbcHardGeometry AbcHardFunction AbcHardOracle
open AbcHardContinuity AbcChain CountdownMarkov

noncomputable def jump (p : Params) (hv : Valid p) : unitInterval :=
  calibratedJump (halfLength p + halfLength p) (rareMass p) (by have := (half_bounds hv).1; omega)
    (mass_bounds hv).1.le (by linarith [(mass_bounds hv).2])

noncomputable abbrev chainKernel (p : Params) (hv : Valid p) :=
  kernel (halfLength p + halfLength p) (jump p hv)

noncomputable abbrev chainLaw (p : Params) (hv : Valid p) :=
  stationaryLaw (halfLength p + halfLength p) (jump p hv)

noncomputable abbrev geometry (p : Params) (hv : Valid p) :=
  scaleOf (chainParams p) hv.1 hv.2.1

noncomputable abbrev labels (p : Params) := Fin (chainDim (chainParams p) + 1) ↪ Fin p.d

noncomputable def estimator (p : Params) (hv : Valid p) (π : labels p) (x : Setups.MarkovSmoothNonconvex.Space p) (z : ℝ) :=
  response (geometry p hv) (rareMass p / 2) π p.x0 x (color (halfLength p) z)

noncomputable def hard (p : Params) (hv : Valid p) (π : labels p) :
    Oracle (Setups.MarkovSmoothNonconvex.Space p) (Setups.MarkovSmoothNonconvex.Space p) where
  Seed := fun _ => ℝ
  law := pathLaw (chainKernel p hv) (chainLaw p hv)
  answer := fun _ (_, x) z => estimator p hv π x z

lemma measurable_estimator (p : Params) (hv : Valid p) (π : labels p) :
    Measurable (Function.uncurry (estimator p hv π)) := by
  let m := fun x => stage (sel π (toUnit (geometry p hv) p.x0 x))
  have hm : Measurable m := stage_measurable _ _ _
  have hc : Measurable (fun z : (Setups.MarkovSmoothNonconvex.Space p × ℝ) × ℕ => gate z.2 (color (halfLength p) z.1.2)) := by
    apply measurable_from_prod_countable_left
    exact fun j => (measurable_of_color _ (gate j)).comp measurable_snd
  exact (reply_measurable (geometry p hv) (fun _ => rareMass p / 2) π p.x0).comp
    (measurable_fst.prodMk (hc.comp (measurable_id.prodMk (hm.comp measurable_fst))))

lemma coin_moments (h : ℕ) (hh : 0 < h) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1 / 2)
    (m : ℕ) :
    let μ := stationaryMeasure (h + h) (calibratedJump (h + h) q (by omega) hq.le hq1)
    let C := fun z => coin (q / 2) (gate m (color h z))
    (∫ z, C z ∂μ) = 1 ∧ (∫ z, (C z - 1) ^ 2 ∂μ) = 2 / q - 1 := by
  intro μ C
  have hp : parity m = 0 ∨ parity m = 1 := by
    have h := (parity m).isLt
    rcases Nat.lt_or_ge (parity m).val 1 with hl | hl
    · exact Or.inl (Fin.ext (by simp; omega))
    · exact Or.inr (Fin.ext (by simp; omega))
  have h1 := color_integral h hh q hq.le hq1 (fun c => coin (q / 2) (gate m c))
  have h2 := color_integral h hh q hq.le hq1 (fun c => (coin (q / 2) (gate m c) - 1) ^ 2)
  change (∫ z, C z ∂μ) = _ at h1
  change (∫ z, (C z - 1) ^ 2 ∂μ) = _ at h2
  rw [h1, h2]
  rcases hp with hp | hp <;> simp [gate, hp, coin, show 0 ≤ q / 2 by linarith,
    show ¬ 2 ≤ q / 2 by linarith, smul_eq_mul, hq.ne'] <;> field_simp <;> ring

lemma admissible (p : Params) (hv : Valid p) (π : labels p) :
    spec.admissible p (objective (geometry p hv) π p.x0) (hard p hv π) := by
  let S := geometry p hv
  let q := rareMass p
  let h := halfLength p
  let μ := stationaryMeasure (h + h) (jump p hv)
  have hh : 0 < h := (half_bounds hv).1
  have hq : 0 < q := (mass_bounds hv).1
  have hq1 : q ≤ 1 / 16 := by have := (mass_bounds hv).2; dsimp [q]; linarith
  obtain ⟨_, _, _, fs, _, _, hgrad, hlip, hlow, hinf, hgap, _⟩ :=
    AbcLowerAssembly.hard_admissible (chainParams p) (chain_valid hv) π
  refine ⟨estimator p hv π, chainKernel p hv, inferInstance, chainLaw p hv, fs, rfl,
    stationary _ _, ?_, ?_, hgrad, hlip, hlow, hinf, hgap, measurable_estimator p hv π,
    fun x => integrable_stationary _ _ _, ?_, fun x => integrable_stationary _ _ _, ?_⟩
  · intro t
    exact integrable_stationary _ _ _
  · intro t
    change (∫ z, mixingDistance (kernel (h+h) (jump p hv)) (stationaryLaw (h+h) (jump p hv)) t z
      ∂stationaryMeasure (h+h) (jump p hv)) ≤ _
    apply le_trans (b := Real.exp (-(t : ℝ)/p.τ)) _ (by linarith [Real.exp_pos (-(t : ℝ)/p.τ)])
    dsimp only [jump]
    simpa only [Real.rpow_one, div_one, neg_div, h, q] using calibrated_mixing (h + h) q
      (by omega) hq hq1 (by linarith [hv.2.2.1] : 0 < p.τ) (by norm_num : (0 : ℝ) < 1)
      le_rfl (by rw [one_div_one, Real.rpow_one]; push_cast; linarith [(half_bounds hv).2.2]) t
  all_goals
    intro x
    let m := stage (sel π (toUnit S p.x0 x))
    let v := objGrad S π p.x0 x - knownPart S π m p.x0 x
    let C := fun z => coin (q / 2) (gate m (color h z))
    have hc := coin_moments h hh q hq (by linarith) m
    change (∫ z, C z ∂μ) = 1 ∧ (∫ z, (C z - 1) ^ 2 ∂μ) = 2 / q - 1 at hc
    rw [objective_gradient]
  · change (∫ z, knownPart S π m p.x0 x + C z • v ∂μ) = _
    rw [integral_add (integrable_const _) (integrable_stationary _ _ _), integral_const,
      probReal_univ, one_smul, integral_smul_const, hc.1, one_smul]
    dsimp [v]
    abel
  · have he (z : ℝ) : estimator p hv π x z - objGrad S π p.x0 x = (C z - 1) • v := by
      change knownPart S π m p.x0 x + C z • v - objGrad S π p.x0 x = _
      rw [sub_smul, one_smul]
      dsimp [v]
      abel
    change (∫ z, ‖estimator p hv π x z - objGrad S π p.x0 x‖ ^ 2 ∂μ) ≤ p.σ ^ 2
    simp_rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [integral_mul_const, hc.2]
    have hratio : S.a / S.lam = 60 * p.ε := amplitude_ratio (chainParams p) hv.1 hv.2.1
    have hs : ‖v‖ ≤ 1740 * p.ε := by
      have hb := secret_norm S π p.x0 x
      rw [hratio] at hb
      dsimp only [v, m]
      linarith
    have hs' := sq_le_sq' (by linarith [norm_nonneg v, hv.2.1] : -(1740 * p.ε) ≤ ‖v‖) hs
    have hc' : 2 / q * (2048 * p.ε) ^ 2 = p.σ ^ 2 := by
      have he := hv.2.1.ne'
      have hσ : p.σ ≠ 0 := by have := ratio_large hv; have := hv.2.2.2.2.1; linarith [hv.2.1]
      unfold q rareMass
      field_simp
    calc
      _ ≤ 2 / q * ‖v‖ ^ 2 := by gcongr; linarith
      _ ≤ 2 / q * (2048 * p.ε) ^ 2 := by gcongr; linarith [hv.2.1]
      _ = _ := hc'

end LongTails.Proofs.MarkovFrontierOracle
