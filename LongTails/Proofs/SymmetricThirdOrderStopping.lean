import LongTails.Proofs.SymmetricThirdOrderStochasticEnergy
import LongTails.Proofs.SymmetricThirdOrderBudget

namespace LongTails.Proofs.SymmetricThirdOrderStopping

open LongTails.Algorithms.SymmetricThirdOrder
open SymmetricThirdOrderStochasticEnergy SymmetricThirdOrderPhasePartition
open SymmetricThirdOrderGoodEvents

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma sampled_no_stop_count (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    {R D : ℝ} (hR : 0 ≤ R) (hball : cfg.C = Metric.closedBall cfg.x0 R)
    (hL : 0 < cfg.L) (hδ : 0 < cfg.δ) (hX : 0 < cfg.threshold) (hD : 0 ≤ D)
    (htop : cfg.δ + 32 * cfg.L * R ^ 2 ≤ cfg.δ * 4 ^ cfg.gridTop)
    (htop_upper : cfg.δ * 4 ^ cfg.gridTop ≤ 4 * (cfg.δ + 32 * cfg.L * R ^ 2))
    (T : ℕ) (hT : 1 ≤ T) (hnostop : (sampledState cfg oracle ξ T).weight < cfg.threshold)
    (hsum : (∑ t ∈ Finset.range T, activeDissipation cfg.L cfg.δ cfg.threshold
      (sampledState cfg oracle ξ t) (sampledCleanup cfg oracle ξ t).1) ≤ D) :
    (T : ℝ) ≤ 1 + 64 * Real.sqrt (cfg.δ * cfg.threshold) +
      384 * (cfg.L * D * cfg.threshold) ^ (1 / 5 : ℝ) +
      ((cfg.gridTop : ℝ) + 2) * ⌈Real.log (1 + 4 * (cfg.δ + 32 * cfg.L * R ^ 2) * cfg.threshold) / Real.log 2⌉₊ := by
  have hC : IsCompact cfg.C := by rw [hball]; exact isCompact_closedBall _ _
  have hconv : Convex ℝ cfg.C := by rw [hball]; exact convex_closedBall _ _
  have hx : cfg.x0 ∈ cfg.C := by rw [hball]; exact Metric.mem_closedBall_self hR
  have hfeas (t : ℕ) := SymmetricThirdOrderHistory.sampledState_feasible cfg oracle ξ hC hconv hx hL.le hδ t
  have hz (t : ℕ) := SymmetricThirdOrderHistory.sampledCleanup_mem cfg oracle ξ hC ⟨cfg.x0, hx⟩ t
  have hmono := SymmetricThirdOrderHistory.sampledState_weight_mono cfg oracle ξ hL.le hδ
  have hactive (t : ℕ) (ht : t ≤ T) : (sampledState cfg oracle ξ t).weight < cfg.threshold :=
    (hmono ht).trans_lt hnostop
  let S := fun t => sampledState cfg oracle ξ (t + 1)
  let z := fun t => (sampledCleanup cfg oracle ξ (t + 1)).1
  let g := fun t => OracleTemplate.QueryPlan.sampledEval oracle ξ
    (meanPlan cfg.batch (z t)) (roundCalls cfg * (t + 1 + 1) - cfg.batch) +
      (sampledCleanup cfg oracle ξ (t + 1)).2
  let Λ := cfg.δ + 32 * cfg.L * R ^ 2
  have hΛ : 0 < Λ := by dsimp [Λ]; positivity
  have hfirst : 1 / (4 * Λ) ≤ (S 0).weight := by
    change 1 / (4 * Λ) ≤ (sampledState cfg oracle ξ (0 + 1)).weight
    rw [SymmetricThirdOrderHistory.sampledState_step]
    change 1 / (4 * Λ) ≤ (outerAdvance cfg.C cfg.x0 cfg.L cfg.δ cfg.threshold cfg.gridTop
      (outerInitial cfg.x0 cfg.gridTop) _ _).weight
    rw [hball]
    exact SymmetricThirdOrderOuter.first_weight_lower cfg.x0 cfg.gridTop _ _ hL.le hδ hX hR
      (by simpa only [hball] using hz 0) htop htop_upper
  have hb : 0 < (S 0).weight := (by positivity : 0 < 1 / (4 * Λ)).trans_le hfirst
  have hrec (t : ℕ) : S (t + 1) = outerAdvance (Metric.closedBall cfg.x0 R) cfg.x0
      cfg.L cfg.δ cfg.threshold cfg.gridTop (S t) (z t) (g t) := by
    simpa only [S, z, g, hball] using SymmetricThirdOrderHistory.sampledState_step cfg oracle ξ (t + 1)
  have hraw : (∑ t ∈ Finset.range (T - 1), rawDissipation cfg.L cfg.δ (S t) (z t)) ≤ D := by
    have hseg := segment_sum_le (fun t => activeDissipation cfg.L cfg.δ cfg.threshold
      (sampledState cfg oracle ξ t) (sampledCleanup cfg oracle ξ t).1)
      (show 1 + (T - 1) ≤ T by omega)
      (fun t _ => activeDissipation_nonneg hL.le hδ _ _
        (SymmetricThirdOrderHistory.sampledState_weight_nonneg cfg oracle ξ hL.le hδ t))
    apply le_trans _ (hseg.trans hsum)
    apply Finset.sum_le_sum
    intro t ht
    have hlt := hactive (t + 1) (by have := Finset.mem_range.mp ht; omega)
    simp only [S, z, Nat.add_comm 1 t, activeDissipation, ite_eq_right (not_le.mpr hlt), le_refl]
  have hc := active_outer_count S z g cfg.x0 hδ hL hb hD hX.le hΛ hfirst rfl
    (SymmetricThirdOrderHistory.sampledState_grid_le cfg oracle ξ 1) hrec
    (fun t ht => hactive (t + 1) (by omega))
    (fun t _ => by
      simpa only [S, z, hball] using
        And.intro (hfeas (t + 1)).1 (And.intro (hfeas (t + 1)).2 (hz (t + 1)))) htop hraw
  have hcast : ((T - 1 : ℕ) : ℝ) + 1 = T := by exact_mod_cast Nat.sub_add_cancel hT
  dsimp [Λ] at hc
  linarith

lemma sufficient_count_accuracy (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω)
    (f : E → ℝ) (xstar : E) (hmin : ∀ x, f xstar ≤ f x)
    {R B ε : ℝ} (hR : 0 ≤ R) (hball : cfg.C = Metric.closedBall cfg.x0 R)
    (hL : 0 < cfg.L) (hδ : 0 < cfg.δ) (hX : 0 < cfg.threshold) (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hbudget : B ≤ cfg.threshold * ε)
    (htop : cfg.δ + 32 * cfg.L * R ^ 2 ≤ cfg.δ * 4 ^ cfg.gridTop)
    (htop_upper : cfg.δ * 4 ^ cfg.gridTop ≤ 4 * (cfg.δ + 32 * cfg.L * R ^ 2))
    (T : ℕ) (hT : 1 ≤ T)
    (hcount : 1 + 64 * Real.sqrt (cfg.δ * cfg.threshold) +
      384 * (cfg.L * ((8 / 3 : ℝ) * B) * cfg.threshold) ^ (1 / 5 : ℝ) +
      ((cfg.gridTop : ℝ) + 2) * ⌈Real.log (1 + 4 * (cfg.δ + 32 * cfg.L * R ^ 2) * cfg.threshold) / Real.log 2⌉₊ < T)
    (hs : ξ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T)
    (hE : killedEnergy cfg oracle f xstar T ξ ≤ B) :
    f (sampledState cfg oracle ξ T).point - f xstar ≤ ε := by
  have hsum := energy_controls_accumulated cfg oracle f xstar T ξ hmin hL.le hδ hs hE
  have hstop : cfg.threshold ≤ (sampledState cfg oracle ξ T).weight := by
    by_contra hn
    have hh := sampled_no_stop_count cfg oracle ξ hR hball hL hδ hX (by positivity)
      htop htop_upper T hT (lt_of_not_ge hn) hsum
    exact (not_lt_of_ge hh) hcount
  exact energy_controls_gap cfg oracle f xstar T ξ hL.le hδ hs hE hε hstop hX hbudget

lemma failure_contained (cfg : Config E) (oracle : E → Ω → Reply E)
    (f : E → ℝ) (xstar : E) (T : ℕ) (B ε : ℝ)
    (hgood : ∀ ξ, ξ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T →
      killedEnergy cfg oracle f xstar T ξ ≤ B → f (sampledState cfg oracle ξ T).point - f xstar ≤ ε) :
    {ξ | ε < f (sampledState cfg oracle ξ T).point - f xstar} ⊆
      (⋃ t : Fin T, (goodRound cfg oracle (gradient f) (fderiv ℝ (gradient f)) t)ᶜ) ∪
        {ξ | B < killedEnergy cfg oracle f xstar T ξ} := by
  intro ξ hξ
  by_cases hs : ξ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T
  · right
    by_contra he
    exact (not_lt_of_ge (hgood ξ hs (le_of_not_gt he))) hξ
  · left
    classical
    have hh : ∃ t < T, ξ ∉ goodRound cfg oracle (gradient f) (fderiv ℝ (gradient f)) t := by
      simpa only [survived, Set.mem_ofPred_eq, not_forall, exists_prop] using hs
    obtain ⟨t, ht, hf⟩ := hh
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hf⟩

open MeasureTheory
open scoped ENNReal

lemma success_probability_of_failures [MeasurableSpace Ω]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (cfg : Config E) (oracle : E → Ω → Reply E) (f : E → ℝ) (xstar : E) (T : ℕ) (B ε : ℝ)
    (hgood : ∀ ξ, ξ ∈ survived cfg oracle (gradient f) (fderiv ℝ (gradient f)) T →
      killedEnergy cfg oracle f xstar T ξ ≤ B → f (sampledState cfg oracle ξ T).point - f xstar ≤ ε)
    (hbad : P (⋃ t : Fin T, (goodRound cfg oracle (gradient f) (fderiv ℝ (gradient f)) t)ᶜ) ≤ 1 / 6)
    (htail : P {ξ | B < killedEnergy cfg oracle f xstar T ξ} ≤ 1 / 6) :
    (2 / 3 : ℝ≥0∞) ≤ P {ξ | f (sampledState cfg oracle ξ T).point - f xstar ≤ ε} := by
  let A := {ξ | f (sampledState cfg oracle ξ T).point - f xstar ≤ ε}
  have hfail : P Aᶜ ≤ (1 / 6 + 1 / 6 : ℝ≥0∞) := by
    have he : Aᶜ = {ξ | ε < f (sampledState cfg oracle ξ T).point - f xstar} := by
      ext ξ
      simp only [A, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    rw [he]
    calc
      _ ≤ P ((⋃ t : Fin T, (goodRound cfg oracle (gradient f) (fderiv ℝ (gradient f)) t)ᶜ) ∪
        {ξ | B < killedEnergy cfg oracle f xstar T ξ}) := measure_mono (failure_contained cfg oracle f xstar T B ε hgood)
      _ ≤ _ := measure_union_le _ _
      _ ≤ 1 / 6 + 1 / 6 := add_le_add hbad htail
  have hcover : (1 : ℝ≥0∞) ≤ P A + P Aᶜ := by
    simpa only [Set.union_compl_self, measure_univ] using measure_union_le (μ := P) A Aᶜ
  have hh : (1 : ℝ≥0∞) ≤ P A + (1 / 6 + 1 / 6) := hcover.trans (add_le_add le_rfl hfail)
  have ht := ENNReal.toReal_mono (by finiteness) hh
  rw [ENNReal.toReal_add (measure_ne_top P A) (by finiteness)] at ht
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at ht
  norm_num at ht
  exact (ENNReal.toReal_le_toReal (by finiteness) (measure_ne_top P A)).mp (by norm_num; linarith)

lemma tuned_accuracy [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] {P : Measure (ℕ → Ω)} [IsProbabilityMeasure P]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (x0 : E) (L R Δ ε σg σh : ℝ) (hL : 0 < L) (hR : 0 < R) (hΔ : 0 ≤ Δ)
    (hε : 0 < ε) (hσh : 0 ≤ σh)
    (f : E → ℝ) (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (xstar : E) (hmin : ∀ x, f xstar ≤ f x) (hdist : ‖x0 - xstar‖ ≤ R)
    (hgap : f x0 - f xstar ≤ Δ)
    (hthird : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hgi : ∀ z, Integrable (fun ω => (oracle z ω).1) p)
    (hmean : ∀ z, (∫ ω, (oracle z ω).1 ∂p) = gradient f z)
    (hgv : ∀ z, Integrable (fun ω => ‖(oracle z ω).1 - gradient f z‖ ^ 2) p)
    (hgm : ∀ z, (∫ ω, ‖(oracle z ω).1 - gradient f z‖ ^ 2 ∂p) ≤ σg ^ 2)
    (hhi : ∀ z, Integrable (fun ω => ‖(oracle z ω).2 - fderiv ℝ (gradient f) z‖ ^ 2) p)
    (hhm : ∀ z, (∫ ω, ‖(oracle z ω).2 - fderiv ℝ (gradient f) z‖ ^ 2 ∂p) ≤ σh ^ 2) :
    let cfg := tunedConfig x0 L R Δ ε σg σh
    let T := iterationCount L R Δ ε σh
    Measurable (fun ξ => (sampledState cfg oracle ξ T).point) ∧
      (∀ ξ, ‖(sampledState cfg oracle ξ T).point - x0‖ ≤ R) ∧
      (2 / 3 : ℝ≥0∞) ≤ P {ξ | f (sampledState cfg oracle ξ T).point - f xstar ≤ ε} := by
  let cfg := tunedConfig x0 L R Δ ε σg σh
  let T := iterationCount L R Δ ε σh
  have hp := SymmetricThirdOrderBudget.tuned_conditions x0 L R Δ ε σg σh hL hR hΔ hε hσh
  change SymmetricThirdOrderBudget.ParameterConditions cfg T R Δ ε σg at hp
  have hC : IsCompact cfg.C := isCompact_closedBall _ _
  have hconv : Convex ℝ cfg.C := convex_closedBall _ _
  have hx : cfg.x0 ∈ cfg.C := Metric.mem_closedBall_self hR.le
  have hstar : xstar ∈ cfg.C := by
    change dist xstar x0 ≤ R
    simpa only [dist_eq_norm, norm_sub_rev] using hdist
  have hd := GradientDependentLocal.derivative_chain hf
  have hg : Measurable (gradient f) :=
    (continuous_iff_continuousAt.mpr (fun x => (hd.2.1 x).continuousAt)).measurable
  have hH : Measurable (fderiv ℝ (gradient f)) :=
    (continuous_iff_continuousAt.mpr (fun x => (hd.2.2 x).continuousAt)).measurable
  have hsym := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
    (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  have hi := killedEnergy_integrable P cfg oracle ho f hf.continuous hg hH xstar hstar hmin
    hC hconv hx hL.le hp.delta_pos hp.threshold_pos.le hp.weight_floor T
  have he := killed_energy_bound p hIID cfg oracle ho f hf hc xstar hR.le rfl hmin hdist hgap
    hL hp.delta_pos hσh hp.tolerance_pos hp.hessian_floor hp.threshold_pos.le hp.weight_floor
    hthird (cfg.innerRounds - 1) (Nat.sub_add_cancel hp.inner_pos).symm hp.inner_tuning
    hp.cleanup hp.batch_pos hgi hmean hgv hgm T
  have htail := killed_energy_tail P cfg oracle f xstar T hmin hL.le hp.delta_pos hi
    (show 0 < 6 * R ^ 2 by positivity) (he.trans hp.energy)
  have hratio : R ^ 2 / (6 * R ^ 2) = (1 / 6 : ℝ) := by field_simp
  rw [hratio] at htail
  rw [ENNReal.ofReal_div_of_pos (by norm_num)] at htail
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at htail
  have hbad := all_rounds_failure_probability hIID cfg oracle ho hC ⟨cfg.x0, hx⟩ hconv
    hL.le hp.delta_pos hp.tolerance_pos hσh (gradient f) hg (fderiv ℝ (gradient f)) hH (fun z a b => (hsym z a b).symm)
    hp.batch_pos hp.batch_size hgi hmean hgv hgm hhi hhm T
  have hb := hbad.trans (ENNReal.ofReal_le_ofReal hp.pilot)
  rw [ENNReal.ofReal_div_of_pos (by norm_num)] at hb
  simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hb
  refine ⟨(SymmetricThirdOrderHistory.measurable_sampledState cfg oracle ho hC ⟨cfg.x0, hx⟩
    hconv hL.le hp.delta_pos T).point, ?_, ?_⟩
  · intro ξ
    have hh := (SymmetricThirdOrderHistory.sampledState_feasible cfg oracle ξ hC hconv hx hL.le hp.delta_pos T).1
    simpa only [cfg, tunedConfig, Metric.mem_closedBall, dist_eq_norm] using hh
  · exact success_probability_of_failures P cfg oracle f xstar T (6 * R ^ 2) ε
      (fun ξ hs he => sufficient_count_accuracy cfg oracle ξ f xstar hmin hR.le rfl hL hp.delta_pos
        hp.threshold_pos (by positivity) hε.le hp.accuracy hp.grid_lower hp.grid_upper T hp.iterations_pos
        hp.count hs he) hb htail

end LongTails.Proofs.SymmetricThirdOrderStopping
