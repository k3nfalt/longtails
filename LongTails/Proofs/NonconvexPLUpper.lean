import LongTails.Proofs.NonconvexPLConvergence

open MeasureTheory Finset
open OracleTemplate.NonconvexPL

namespace OracleTemplate.StochasticNonconvexPL

open LongTails.Setups.StochasticTwoSidedPL (maxValue minimaxValue IsUnbiasedOracle)
open LongTails.Setups.StochasticNonconvexPL
open OracleTemplate.StochasticTwoSidedPL (uniform_fin_integral)

noncomputable def stepSize (p : Params) : ℝ :=
  1 / (p.L * (3 + 2 ^ 23 * p.L * p.σ ^ 2 / (p.μ * p.ε ^ 2)))

noncomputable def iterations (p : Params) : ℕ :=
  ⌈2 ^ 44 * p.L ^ 2 * p.Δ / (p.μ * p.ε ^ 2) * (1 + p.L * p.σ ^ 2 / (p.μ * p.ε ^ 2))⌉₊

noncomputable def algorithm (p : Params) : Algorithm (p.E × p.F) (p.E × p.F) p.E :=
  nonconvexPLSmoothedAgda (2 * p.L) (stepSize p) (stepSize p / 32) (stepSize p * p.μ / 6144)
    (iterations p) p.x0 p.y0

lemma sq_integral_le {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
    {g : X → ℝ} (hg : Integrable g ν) (hg2 : Integrable (fun x => g x ^ 2) ν) :
    (∫ x, g x ∂ν) ^ 2 ≤ ∫ x, g x ^ 2 ∂ν := by
  set c := ∫ x, g x ∂ν with hc
  have hint : Integrable (fun x => (g x - c) ^ 2) ν := by
    have e : (fun x => (g x - c) ^ 2) = fun x => g x ^ 2 - 2 * c * g x + c ^ 2 := by
      funext x; ring
    rw [e]
    exact (hg2.sub (hg.const_mul _)).add (integrable_const _)
  have h0 : 0 ≤ ∫ x, (g x - c) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have e : ∫ x, (g x - c) ^ 2 ∂ν = ∫ x, g x ^ 2 ∂ν - c ^ 2 := by
    have e1 : (fun x => (g x - c) ^ 2) = fun x => g x ^ 2 - 2 * c * g x + c ^ 2 := by
      funext x; ring
    have h1 : Integrable (fun x => 2 * c * g x) ν := hg.const_mul _
    have h2 : Integrable (fun x => g x ^ 2 - 2 * c * g x) ν := hg2.sub h1
    have e2 : ∫ x, (g x ^ 2 - 2 * c * g x + c ^ 2) ∂ν =
        ∫ x, (g x ^ 2 - 2 * c * g x) ∂ν + ∫ _ : X, c ^ 2 ∂ν :=
      integral_add h2 (integrable_const _)
    have e3 : ∫ x, (g x ^ 2 - 2 * c * g x) ∂ν = ∫ x, g x ^ 2 ∂ν - ∫ x, 2 * c * g x ∂ν :=
      integral_sub hg2 h1
    have e4 : ∫ x, 2 * c * g x ∂ν = 2 * c * ∫ x, g x ∂ν := integral_const_mul _ _
    have e5 : ∫ _ : X, c ^ 2 ∂ν = c ^ 2 := by
      rw [integral_const, probReal_univ, one_smul]
    rw [e1, e2, e3, e4, e5, ← hc]
    ring
  linarith

lemma final_scalar {L μ σ Δ ε K τ N V0 : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hε : 0 < ε)
    (hK3 : 3 ≤ K) (hKσ : 2 ^ 23 * L * σ ^ 2 ≤ K * (μ * ε ^ 2)) (hτ : 0 < τ)
    (hτK : τ * (L * K) = 1) (hN : 0 < N) (hNΔ : 2 ^ 21 * L ^ 2 * Δ * K ≤ N * (μ * ε ^ 2))
    (hV : V0 ≤ Δ) :
    2 ^ 19 * L * (V0 + N * (4 * L * τ ^ 2 * σ ^ 2)) + N * (24 * L ^ 2 * τ ^ 3 * μ * σ ^ 2) ≤
      ε ^ 2 * (μ * τ * N) := by
  have hL : 0 < L := lt_of_lt_of_le hμ hμL
  have hK : 0 < K := by linarith
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hε2 : 0 < ε ^ 2 := by positivity
  have ha : 2 ^ 19 * L * V0 ≤ ε ^ 2 * (μ * τ * N) / 4 := by
    have h1 : 2 ^ 19 * L * V0 ≤ 2 ^ 19 * L * Δ := by
      apply mul_le_mul_of_nonneg_left hV (by positivity)
    have h2 : 2 ^ 21 * L * Δ = τ * (2 ^ 21 * L ^ 2 * Δ * K) := by
      have : τ * (2 ^ 21 * L ^ 2 * Δ * K) = 2 ^ 21 * L * Δ * (τ * (L * K)) := by ring
      rw [this, hτK, mul_one]
    have h3 : τ * (2 ^ 21 * L ^ 2 * Δ * K) ≤ τ * (N * (μ * ε ^ 2)) :=
      mul_le_mul_of_nonneg_left hNΔ hτ.le
    nlinarith
  have hb : 2 ^ 19 * L * (N * (4 * L * τ ^ 2 * σ ^ 2)) ≤ ε ^ 2 * (μ * τ * N) / 4 := by
    have h1 : τ * L * (2 ^ 23 * L * σ ^ 2) ≤ τ * L * (K * (μ * ε ^ 2)) :=
      mul_le_mul_of_nonneg_left hKσ (by positivity)
    have h2 : τ * L * (K * (μ * ε ^ 2)) = μ * ε ^ 2 := by
      have : τ * L * (K * (μ * ε ^ 2)) = τ * (L * K) * (μ * ε ^ 2) := by ring
      rw [this, hτK, one_mul]
    have h3 : 2 ^ 23 * L ^ 2 * τ * σ ^ 2 ≤ μ * ε ^ 2 := by nlinarith
    have h4 : 0 ≤ τ * N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 h4]
  have hc : N * (24 * L ^ 2 * τ ^ 3 * μ * σ ^ 2) ≤ ε ^ 2 * (μ * τ * N) / 4 := by
    have h1 : 2 ^ 23 * μ * σ ^ 2 ≤ K * (μ * ε ^ 2) := by
      have : 2 ^ 23 * μ * σ ^ 2 ≤ 2 ^ 23 * L * σ ^ 2 := by nlinarith
      linarith
    have h2 : 2 ^ 23 * σ ^ 2 ≤ K * ε ^ 2 := by
      have : μ * (2 ^ 23 * σ ^ 2) ≤ μ * (K * ε ^ 2) := by nlinarith
      exact le_of_mul_le_mul_left this hμ
    have h3 : 96 * σ ^ 2 ≤ K ^ 2 * ε ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left h2 hK.le]
    have h4 : (τ * L) ^ 2 * K ^ 2 = 1 := by
      have : (τ * L) ^ 2 * K ^ 2 = (τ * (L * K)) ^ 2 := by ring
      rw [this, hτK, one_pow]
    have h5 : 96 * L ^ 2 * τ ^ 2 * σ ^ 2 ≤ ε ^ 2 := by
      have h6 : (τ * L) ^ 2 * (96 * σ ^ 2) ≤ (τ * L) ^ 2 * (K ^ 2 * ε ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      nlinarith
    have h7 : 0 ≤ μ * τ * N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h5 h7]
  have hX : 0 ≤ ε ^ 2 * (μ * τ * N) := by positivity
  have e : 2 ^ 19 * L * (V0 + N * (4 * L * τ ^ 2 * σ ^ 2)) =
      2 ^ 19 * L * V0 + 2 ^ 19 * L * (N * (4 * L * τ ^ 2 * σ ^ 2)) := by ring
  rw [e]
  linarith

theorem convergence : Convergence spec (fun p _ => 2 * iterations p) := by
  apply convergence_of_public_budget (S := spec) (fun p => 2 * iterations p)
  refine ⟨algorithm, ?_, fun p _ => trivial⟩
  intro p hp f O hadm
  obtain ⟨hμ, hμL, -, hΔ, hε⟩ := hp
  obtain ⟨gx, gy, Gx, Gy, pr, hO, hgx, hgy, hlx, hly, hply, hatt, hbdd, hJ, hΔ0⟩ := hadm
  have hO' : O = jointOracle Gx Gy pr := hO
  subst hO'
  have hL : 0 < p.L := lt_of_lt_of_le hμ hμL
  have H : Hyp f (fun x y => gx (x, y)) (fun x y => gy (x, y)) p.L p.μ :=
    { hL := hL, hμy := hμ, hμyL := hμL
      hgx := fun x y => hgx (x, y), hgy := fun x y => hgy (x, y)
      lipx := fun x x' y y' => hlx (x, y) (x', y'), lipy := fun x x' y y' => hly (x, y) (x', y')
      ply := hply, attain := hatt, bdd := hbdd }
  have ox : IsUnbiasedOracle (pr : Measure p.Ω) gx Gx p.σ :=
    { measurable := hJ.measurable_x
      integrable := hJ.integrable_x
      unbiased := hJ.unbiased_x
      variance_integrable := fun w => by
        refine (hJ.variance_integrable w).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
        · exact (((hJ.measurable_x.comp (measurable_const.prodMk measurable_id)).sub
            measurable_const).norm.pow_const 2).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have := sq_nonneg ‖Gy w ω - gy w‖
          linarith
      variance := fun w => by
        refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
          (hJ.variance_integrable w) (Filter.Eventually.of_forall fun ω => ?_)) (hJ.variance w)
        have := sq_nonneg ‖Gy w ω - gy w‖
        change ‖Gx w ω - gx w‖ ^ 2 ≤ ‖Gx w ω - gx w‖ ^ 2 + ‖Gy w ω - gy w‖ ^ 2
        linarith }
  have oy : IsUnbiasedOracle (pr : Measure p.Ω) gy Gy p.σ :=
    { measurable := hJ.measurable_y
      integrable := hJ.integrable_y
      unbiased := hJ.unbiased_y
      variance_integrable := fun w => by
        refine (hJ.variance_integrable w).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
        · exact (((hJ.measurable_y.comp (measurable_const.prodMk measurable_id)).sub
            measurable_const).norm.pow_const 2).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have := sq_nonneg ‖Gx w ω - gx w‖
          linarith
      variance := fun w => by
        refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
          (hJ.variance_integrable w) (Filter.Eventually.of_forall fun ω => ?_)) (hJ.variance w)
        have := sq_nonneg ‖Gx w ω - gx w‖
        change ‖Gy w ω - gy w‖ ^ 2 ≤ ‖Gx w ω - gx w‖ ^ 2 + ‖Gy w ω - gy w‖ ^ 2
        linarith }
  set K := 3 + 2 ^ 23 * p.L * p.σ ^ 2 / (p.μ * p.ε ^ 2) with hKdef
  have hμε : 0 < p.μ * p.ε ^ 2 := by positivity
  have hX0 : 0 ≤ 2 ^ 23 * p.L * p.σ ^ 2 / (p.μ * p.ε ^ 2) := by positivity
  have hK3 : 3 ≤ K := by rw [hKdef]; linarith
  have hKσ : 2 ^ 23 * p.L * p.σ ^ 2 ≤ K * (p.μ * p.ε ^ 2) := by
    rw [hKdef, add_mul, div_mul_cancel₀ _ hμε.ne']
    nlinarith
  set τ := stepSize p with hτdef
  have hτ : 0 < τ := by
    simp only [hτdef, stepSize]; positivity
  have hτK : τ * (p.L * K) = 1 := by
    simp only [hτdef, stepSize, hKdef]
    rw [one_div_mul_cancel]
    positivity
  have hs : 3 * p.L * τ ≤ 1 := by
    have h1 : τ * (p.L * 3) ≤ τ * (p.L * K) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK3 hL.le) hτ.le
    linarith
  set n := iterations p with hndef
  have hnge : 2 ^ 44 * p.L ^ 2 * p.Δ / (p.μ * p.ε ^ 2) * (1 + p.L * p.σ ^ 2 / (p.μ * p.ε ^ 2)) ≤
      (n : ℝ) := Nat.le_ceil _
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hNΔ : 2 ^ 21 * p.L ^ 2 * p.Δ * K ≤ ((n : ℝ) + 1) * (p.μ * p.ε ^ 2) := by
    have hY : 0 ≤ p.L ^ 2 * p.Δ / (p.μ * p.ε ^ 2) := by positivity
    have hXX : 0 ≤ p.L * p.σ ^ 2 / (p.μ * p.ε ^ 2) := by positivity
    have e1 : 2 ^ 44 * p.L ^ 2 * p.Δ / (p.μ * p.ε ^ 2) * (1 + p.L * p.σ ^ 2 / (p.μ * p.ε ^ 2)) =
        2 ^ 44 * (p.L ^ 2 * p.Δ / (p.μ * p.ε ^ 2)) * (1 + p.L * p.σ ^ 2 / (p.μ * p.ε ^ 2)) := by
      ring
    have e2 : K = 3 + 2 ^ 23 * (p.L * p.σ ^ 2 / (p.μ * p.ε ^ 2)) := by
      rw [hKdef]; ring
    have e3 : 2 ^ 21 * p.L ^ 2 * p.Δ * K =
        2 ^ 21 * (p.L ^ 2 * p.Δ / (p.μ * p.ε ^ 2)) * K * (p.μ * p.ε ^ 2) := by
      field_simp
    rw [e3]
    apply mul_le_mul_of_nonneg_right _ hμε.le
    rw [e1] at hnge
    rw [e2]
    nlinarith [mul_nonneg hY hXX]
  have hex : ∀ (j : Fin (n + 1)) (ξ : ℕ → p.Ω),
      execute (jointOracle Gx Gy pr) (algorithm p) (fun _ => 2 * n) j ξ =
        (path Gx Gy p.L p.μ τ p.x0 p.y0 ξ j).2.2 :=
    fun j ξ => execute_joint Gx Gy pr p.L p.μ τ n p.x0 p.y0 j ξ
  have hp' := measurable_path ox.measurable oy.measurable p.L p.μ τ p.x0 p.y0
  set P := Measure.infinitePi fun _ : ℕ => (pr : Measure p.Ω) with hPdef
  set U := (PMF.uniformOfFintype (Fin (n + 1))).toMeasure with hUdef
  set g : Fin (n + 1) × (ℕ → p.Ω) → ℝ := fun seed =>
    moreauResidual f p.L (path Gx Gy p.L p.μ τ p.x0 p.y0 seed.2 seed.1).2.2 with hgdef
  have hgm : Measurable g :=
    measurable_from_prod_countable_right fun j => measurable_residual H ox oy τ p.x0 p.y0 j
  have hmem : ∀ t, MemLp (fun ξ : ℕ → p.Ω =>
      moreauResidual f p.L (path Gx Gy p.L p.μ τ p.x0 p.y0 ξ t).2.2) 2 P :=
    fun t => memLp_residual H ox oy τ p.x0 p.y0 t
  have hgi : Integrable g (U.prod P) := by
    rw [integrable_prod_iff hgm.aestronglyMeasurable]
    exact ⟨Filter.Eventually.of_forall fun j => (hmem j).integrable one_le_two,
      Integrable.of_finite⟩
  have hg2i : Integrable (fun seed => g seed ^ 2) (U.prod P) := by
    rw [integrable_prod_iff (hgm.pow_const 2).aestronglyMeasurable]
    exact ⟨Filter.Eventually.of_forall fun j => (hmem j).integrable_sq, Integrable.of_finite⟩
  have hexp := expected_moreau H ox oy hτ hs p.x0 p.y0 (n + 1) (p := (pr : Measure p.Ω))
  have hΔ0' : statePotential f p.L (p.x0, p.y0, p.x0) - minimaxValue f ≤ p.Δ :=
    (H.initial_potential p.x0 p.y0).trans hΔ0
  have hfs := final_scalar (N := (n : ℝ) + 1) hμ hμL hε hK3 hKσ hτ hτK hNpos hNΔ hΔ0'
  have hsumint : ∑ t ∈ range (n + 1), ∫ ξ,
      moreauResidual f p.L (path Gx Gy p.L p.μ τ p.x0 p.y0 ξ t).2.2 ^ 2 ∂P ≤
      p.ε ^ 2 * ((n : ℝ) + 1) := by
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hexp
    rw [integral_finsetSum _ fun t _ => ((hmem t).integrable_sq).const_mul _] at hexp
    simp_rw [integral_const_mul] at hexp
    rw [← mul_sum] at hexp
    have hμτ : 0 < p.μ * τ := by positivity
    have h1 := hexp.trans hfs
    have e : p.ε ^ 2 * (p.μ * τ * ((n : ℝ) + 1)) = p.μ * τ * (p.ε ^ 2 * ((n : ℝ) + 1)) := by ring
    rw [e] at h1
    exact le_of_mul_le_mul_left h1 hμτ
  have hval2 : ∫ seed, g seed ^ 2 ∂(U.prod P) ≤ p.ε ^ 2 := by
    rw [integral_prod _ hg2i, uniform_fin_integral]
    rw [div_le_iff₀ hNpos]
    have e := Fin.sum_univ_eq_sum_range (fun i => ∫ ξ,
      moreauResidual f p.L (path Gx Gy p.L p.μ τ p.x0 p.y0 ξ i).2.2 ^ 2 ∂P) (n + 1)
    rw [e]
    exact hsumint
  have hval : ∫ seed, g seed ∂(U.prod P) ≤ p.ε := by
    have : IsProbabilityMeasure U := by rw [hUdef]; infer_instance
    have : IsProbabilityMeasure P := by rw [hPdef]; infer_instance
    have hsq := sq_integral_le hgi hg2i
    have h2 : (∫ seed, g seed ∂(U.prod P)) ^ 2 ≤ p.ε ^ 2 := hsq.trans hval2
    by_contra hc
    have hlt : p.ε < ∫ seed, g seed ∂(U.prod P) := not_le.mp hc
    have := pow_lt_pow_left₀ hlt hε.le (by norm_num : (2 : ℕ) ≠ 0)
    linarith
  set out := fun seed : Fin (n + 1) × (ℕ → p.Ω) =>
    (execute (jointOracle Gx Gy pr) (algorithm p) (fun _ => 2 * n) seed.1 seed.2) with hout
  have hfun : out = fun seed => (path Gx Gy p.L p.μ τ p.x0 p.y0 seed.2 seed.1).2.2 := by
    funext seed
    exact hex seed.1 seed.2
  refine ⟨?_, ?_, ?_⟩
  · change Measurable out
    rw [hfun]
    exact measurable_from_prod_countable_right fun j => (hp' j).snd.snd
  · change Integrable (fun seed => moreauResidual f p.L (out seed)) (U.prod P)
    rw [hfun]
    exact hgi
  · change ∫ seed, moreauResidual f p.L (out seed) ∂(U.prod P) ≤ p.ε
    rw [hfun]
    exact hval

end OracleTemplate.StochasticNonconvexPL
