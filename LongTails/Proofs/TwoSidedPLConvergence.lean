import LongTails.Proofs.Execution
import LongTails.Proofs.TwoSidedPLExecution
import LongTails.Proofs.TwoSidedPLBudget

open MeasureTheory Finset
open OracleTemplate.TwoSidedPL

namespace OracleTemplate.StochasticTwoSidedPL

open LongTails.Setups.StochasticTwoSidedPL

noncomputable def stepSize (p : Params) : ℝ :=
  1 / (p.L * (3 + 2 ^ 24 * p.L * p.σ ^ 2 / (p.μx * p.μy * p.ε)))

noncomputable def windowLength (p : Params) : ℕ :=
  ⌈2 ^ 18 * p.L ^ 2 / (p.μx * p.μy) * (3 + 2 ^ 24 * p.L * p.σ ^ 2 / (p.μx * p.μy * p.ε)) *
    (2 + Real.log (1 + p.Δ / p.ε))⌉₊

noncomputable def algorithm (p : Params) : Algorithm ((p.E × p.F) ⊕ (p.E × p.F)) (p.E ⊕ p.F) (p.E × p.F) :=
  stochasticSmoothedAgda (2 * p.L) (stepSize p) (stepSize p / 32) (stepSize p * p.μy / 6144)
    (windowLength p) p.x0 p.y0

lemma uniform_fin_integral (n : ℕ) (g : Fin (n + 1) → ℝ) :
    ∫ j, g j ∂(PMF.uniformOfFintype (Fin (n + 1))).toMeasure = (∑ j, g j) / (n + 1) := by
  rw [integral_fintype (Integrable.of_finite)]
  have h : ∀ j : Fin (n + 1), ((PMF.uniformOfFintype (Fin (n + 1))).toMeasure).real {j} = 1 / (n + 1) := by
    intro j
    rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton j),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
    simp
    try exact_mod_cast (ENNReal.toReal_natCast (n + 1))
  simp only [h, smul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp

theorem convergence : Convergence spec (fun p _ => 2 * (2 * windowLength p + 1)) := by
  apply convergence_of_public_budget (S := spec) (fun p => 2 * (2 * windowLength p + 1))
  refine ⟨algorithm, ?_, fun p _ => ⟨_, _, _, _, _, rfl⟩⟩
  intro p hp f O hadm
  obtain ⟨hμx, hμxL, hμy, hμyL, hσ, hΔ, hε⟩ := hp
  obtain ⟨gx, gy, Gx, Gy, pr, hO, hgx, hgy, hlx, hly, hplx, hply, hatt, ox, oy, hΔ0⟩ := hadm
  have hO' : O = agdaOracle Gx Gy pr := hO
  subst hO'
  have hL : 0 < p.L := lt_of_lt_of_le hμx hμxL
  have H : Hyp f (fun x y => gx (x, y)) (fun x y => gy (x, y)) p.L p.μx p.μy :=
    { hL := hL, hμx := hμx, hμxL := hμxL, hμy := hμy, hμyL := hμyL
      hgx := fun x y => hgx (x, y), hgy := fun x y => hgy (x, y)
      lipx := fun x x' y y' => hlx (x, y) (x', y'), lipy := fun x x' y y' => hly (x, y) (x', y')
      plx := hplx, ply := hply, attain := hatt }
  have hK3 : 3 ≤ 3 + 2 ^ 24 * p.L * p.σ ^ 2 / (p.μx * p.μy * p.ε) := by
    have : 0 ≤ 2 ^ 24 * p.L * p.σ ^ 2 / (p.μx * p.μy * p.ε) := by positivity
    linarith
  set τ := stepSize p with hτdef
  have hτ : 0 < τ := by
    simp only [hτdef, stepSize]; positivity
  have hs : 3 * p.L * τ ≤ 1 := by
    simp only [hτdef, stepSize]
    rw [mul_one_div, div_le_one (by positivity)]
    have := mul_le_mul_of_nonneg_left hK3 hL.le
    linarith
  set n := windowLength p with hndef
  have hex : ∀ (j : Fin (n + 1)) (ξ : ℕ → p.Ω),
      execute (agdaOracle Gx Gy pr) (algorithm p) (fun _ => (2 * (2 * n + 1))) j ξ =
        ((path Gx Gy p.L p.μy τ p.x0 p.y0 ξ (n + j)).1,
          (path Gx Gy p.L p.μy τ p.x0 p.y0 ξ (n + j)).2.1) :=
    fun j ξ => execute_agda Gx Gy pr p.L p.μy τ n p.x0 p.y0 j ξ
  have hp' := measurable_path ox.measurable oy.measurable p.L p.μy τ p.x0 p.y0
  have hmeas : Measurable fun seed : Fin (n + 1) × (ℕ → p.Ω) =>
      ((path Gx Gy p.L p.μy τ p.x0 p.y0 seed.2 (n + seed.1)).1,
        (path Gx Gy p.L p.μy τ p.x0 p.y0 seed.2 (n + seed.1)).2.1) :=
    measurable_from_prod_countable_right fun j => (hp' (n + j)).fst.prodMk (hp' (n + j)).snd.fst
  set g : Fin (n + 1) × (ℕ → p.Ω) → ℝ := fun seed =>
    gapValue f (path Gx Gy p.L p.μy τ p.x0 p.y0 seed.2 (n + seed.1)) with hgdef
  have hgm : Measurable g :=
    measurable_from_prod_countable_right fun j => measurable_gap H ox oy τ p.x0 p.y0 (n + j)
  have hgi : Integrable g (((PMF.uniformOfFintype (Fin (n + 1))).toMeasure).prod
      (Measure.infinitePi fun _ : ℕ => (pr : Measure p.Ω))) := by
    rw [integrable_prod_iff hgm.aestronglyMeasurable]
    exact ⟨Filter.Eventually.of_forall fun j => gap_integrable H ox oy τ p.x0 p.y0 (n + j),
      Integrable.of_finite⟩
  have hsum : ∑ j : Fin (n + 1), ∫ ξ, g (j, ξ) ∂(Measure.infinitePi fun _ : ℕ => (pr : Measure p.Ω)) =
      ∫ ξ, ∑ t ∈ Ico n (n + (n + 1)), gapValue f (path Gx Gy p.L p.μy τ p.x0 p.y0 ξ t)
        ∂(Measure.infinitePi fun _ : ℕ => (pr : Measure p.Ω)) := by
    rw [integral_finsetSum _ fun t _ => gap_integrable H ox oy τ p.x0 p.y0 t,
      Finset.sum_Ico_eq_sum_range, show n + (n + 1) - n = n + 1 by omega]
    exact Fin.sum_univ_eq_sum_range (fun i => ∫ ξ, gapValue f
      (path Gx Gy p.L p.μy τ p.x0 p.y0 ξ (n + i)) ∂(Measure.infinitePi fun _ : ℕ => (pr : Measure p.Ω)))
      (n + 1)
  have hwin := expected_window H ox oy hτ hs p.x0 p.y0 n (p := (pr : Measure p.Ω))
  have hΔ0' : statePotential f p.L (p.x0, p.y0, p.x0) - minimaxValue f ≤ p.Δ :=
    (H.initial_potential p.x0 p.y0).trans hΔ0
  have hfb := final_bound (τ := τ) (C := 2 ^ 18 * p.L / (p.μx * p.μy * τ)) (n := n) hμx hμxL hμy
    hμyL hΔ hε hΔ0' rfl rfl rfl rfl
  have hval : ∫ seed, g seed ∂(((PMF.uniformOfFintype (Fin (n + 1))).toMeasure).prod
      (Measure.infinitePi fun _ : ℕ => (pr : Measure p.Ω))) ≤ p.ε := by
    rw [integral_prod g hgi, uniform_fin_integral, hsum]
    refine (div_le_div_of_nonneg_right hwin.2 (by positivity)).trans ?_
    exact hfb
  set out := fun seed : Fin (n + 1) × (ℕ → p.Ω) =>
    (execute (agdaOracle Gx Gy pr) (algorithm p) (fun _ => (2 * (2 * n + 1))) seed.1 seed.2) with hout
  have hfun : out = fun seed => ((path Gx Gy p.L p.μy τ p.x0 p.y0 seed.2 (n + seed.1)).1,
        (path Gx Gy p.L p.μy τ p.x0 p.y0 seed.2 (n + seed.1)).2.1) := by
    funext seed
    exact (hex seed.1 seed.2)
  refine ⟨?_, ?_, ?_⟩
  · change Measurable out
    rw [hfun]
    exact hmeas
  · change Integrable (fun seed => (maxValue f (out seed).1 - minimaxValue f) +
      (maxValue f (out seed).1 - f (out seed).1 (out seed).2))
      (((PMF.uniformOfFintype (Fin (n + 1))).toMeasure).prod
        (Measure.infinitePi fun _ : ℕ => (pr : Measure p.Ω)))
    rw [hfun]
    exact hgi
  · change ∫ seed, ((maxValue f (out seed).1 - minimaxValue f) +
      (maxValue f (out seed).1 - f (out seed).1 (out seed).2))
      ∂(((PMF.uniformOfFintype (Fin (n + 1))).toMeasure).prod
        (Measure.infinitePi fun _ : ℕ => (pr : Measure p.Ω))) ≤ p.ε
    rw [hfun]
    exact hval

end OracleTemplate.StochasticTwoSidedPL
