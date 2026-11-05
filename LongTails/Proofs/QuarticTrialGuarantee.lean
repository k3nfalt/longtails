import LongTails.Proofs.QuarticTrialExecution

namespace LongTails.Proofs.QuarticTrialGuarantee

open LongTails.Algorithms.QuarticProximalTrial LongTails.Algorithms.QuarticProximal
open LongTails.Algorithms.TaylorCorrectedNewton LongTails.Setups.FiniteSumSmoothAndConvex
open LongTails.Proofs.QuarticTrialExecution LongTails.Proofs.TensorFreeModelExecution
open OracleTemplate OracleTemplate.QueryPlan
open scoped BigOperators Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [NeZero n]

lemma trial_guarantee (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {ε R Q L γ : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q)
    (hLlo : ε / R ^ 4 ≤ L) (hLhi : L ≤ ε / R ^ 4 * Q)
    (hγlo : ε / (R ^ 4 * Q) ≤ γ) (hγhi : γ ≤ ε / R ^ 4 * Q)
    (hLγ : L ≤ (n : ℝ) * γ) (hκ : L + 6 * γ ≤ γ * Q ^ 2)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (x0 xstar c : E) (hminf : ∀ x, objective f xstar ≤ objective f x)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hcenter : ‖c - xstar‖ ≤ R * Q ^ 8)
    (hG0 : ‖gradient (objective f) x0‖ ≤ ε / R * Q)
    (hH0 : ‖fderiv ℝ (gradient (objective f)) x0‖ ≤ ε / R ^ 2 * Q)
    (N : ℕ) (hN : 0 < N) (hnQ : (n : ℝ) ≤ Q) (hNQ : (N : ℝ) ≤ 256 * Q) :
    let output := fun seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q) =>
      eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
        (trial ε R Q (L + 6 * γ) γ x0 c seed)
    (∀ seed, output seed ≠ .failed → ValidAt (objective f) ε γ c xstar (output seed)) ∧
      (𝔼 seed, (if output seed = .failed then (1 : ℝ) else 0)) ≤ 1 / (4 * (N : ℝ)) := by
  classical
  let oracle := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
  let M := L + 6 * γ
  let tol := ε / (R * Q ^ 12)
  let F := fun x => objective f x + penalty γ 0 c c x
  let output := fun seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q) =>
    eval oracle (trial ε R Q M γ x0 c seed)
  change (∀ seed, output seed ≠ .failed → ValidAt (objective f) ε γ c xstar (output seed)) ∧
    (𝔼 seed, (if output seed = .failed then (1 : ℝ) else 0)) ≤ 1 / (4 * (N : ℝ))
  have hQpos : 0 < Q := by linarith
  have hγ : 0 < γ := (by positivity : 0 < ε / (R ^ 4 * Q)).trans_le hγlo
  have hL : 0 < L := (by positivity : 0 < ε / R ^ 4).trans_le hLlo
  have hM : 0 < M := by dsimp [M]; positivity
  have hMlo : ε / R ^ 4 ≤ M := by dsimp [M]; linarith
  have hMhi : M ≤ ε / R ^ 4 * Q ^ 3 := by
    have h2 : 7 ≤ Q ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right h2 (show 0 ≤ ε / R ^ 4 * Q by positivity)
    have he : ε / R ^ 4 * Q ^ 3 = Q ^ 2 * (ε / R ^ 4 * Q) := by ring
    rw [he]
    dsimp [M]
    nlinarith
  have hbase := FiniteSumThirdSmoothGeometry.objective_contDiff f hf
  have hcbase := OracleTemplate.FiniteSum.objective_convex hc
  have hF : ContDiff ℝ 3 F := hbase.add ((QuarticProximalGeometry.penalty_contDiff γ 0 c c).of_le le_top)
  have hcF : ConvexOn ℝ Set.univ F :=
    QuarticFiniteSum.component_convex (fun _ : Fin 1 => objective f) (fun _ => hbase) (fun _ => hcbase) hγ.le le_rfl c c 0
  have hTF (x y : E) : ‖fderiv ℝ (fderiv ℝ (gradient F)) x - fderiv ℝ (fderiv ℝ (gradient F)) y‖ ≤ M * ‖x - y‖ :=
    QuarticFiniteSum.component_third_lipschitz (fun _ : Fin 1 => objective f) (fun _ => hbase) hγ.le
      (fun _ => FiniteSumThirdSmoothGeometry.objective_third_lipschitz f hf hT) c c x y 0
  obtain ⟨u, hminu⟩ := QuarticFiniteSumStage.exists_quartic_min hbase.continuous hγ c xstar hminf
  have hmin : ∀ x, F u ≤ F x := by intro x; simpa [F, penalty] using hminu x
  have hradius := (QuarticTrialGeometry.prox_min_center hγ c u xstar hminf hmin).trans hcenter
  have hcenter0 : ‖c - x0‖ ≤ R * (Q ^ 8 + 1) := by
    have hh := norm_sub_le_norm_sub_add_norm_sub c xstar x0
    have hx : ‖xstar - x0‖ ≤ R := by simpa only [norm_sub_rev] using hx0
    nlinarith
  have hc0 : ‖c - x0‖ ≤ R * Q ^ 14 := by
    have h1 : 1 ≤ Q := by linarith
    have h8 : (1 : ℝ) ≤ Q ^ 8 := one_le_pow₀ h1
    have h6 : 2 ≤ Q ^ 6 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 6
      norm_num at hh
      linarith
    have hh := mul_le_mul_of_nonneg_right h6 (show 0 ≤ R * Q ^ 8 by positivity)
    have he : R * Q ^ 14 = Q ^ 6 * (R * Q ^ 8) := by ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left h8 hR.le]
  have hcut := small_tolerance_conditions hε hR hQ hγlo
  let first := eval oracle (modelSolve ε R Q M γ c c)
  have hfirst := (QuarticLocalTuning.modelSolve_certificate f hf hc hε hR hQ hL.le hγ.le hLhi hγhi
    hMlo hMhi le_rfl hT x0 c c hG0 hH0 hc0 (by simpa using (show 0 ≤ R * Q ^ 14 by positivity))).2
  by_cases hs₀ : ‖first.trueGradient‖ ≤ tol
  · have he (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q)) :
        output seed = classify γ tol c (c + first.displacement) first.trueGradient := by
      dsimp only [output]
      unfold trial
      simp only [modelCost, stagesCost, trialCost, logarithm]
      rw [eval_bind, ite_eq_left hs₀, eval_padResult]
    have hn := classify_not_failed (γ := γ) c (c + first.displacement) first.trueGradient (Or.inr hs₀)
    constructor
    · intro seed
      rw [he]
      exact classify_correct (hbase.differentiable (by norm_num)) hcbase hγ hR.le hcut.1 hcut.2
        c (c + first.displacement) xstar first.trueGradient hcenter hfirst.1
    · simp only [he, hn, ↓reduceIte, Fintype.expect_const]
      positivity
  let z0 := c + first.displacement
  have hm₀ : ‖LongTails.Algorithms.TensorFreeModel.exactGradient (gradient F c) (fderiv ℝ (gradient F) c)
      (fderiv ℝ (fderiv ℝ (gradient F)) c) M first.displacement‖ ≤ ‖gradient F z0‖ / 6 := by
    simpa only [hfirst.1] using hfirst.2.resolve_left hs₀
  have hfirstdist := QuarticTrialGeometry.model_prox_distance hbase hcbase hγ hM hQ hκ c c first.displacement u hmin hTF hm₀
  have hself : ‖z0 - u‖ ≤ Q ^ 2 * ‖z0 - u‖ := by
    have hh : 1 ≤ Q ^ 2 := by nlinarith
    nlinarith [norm_nonneg (z0 - u)]
  have hfirstpoints := QuarticTrialGeometry.initial_points_radius hR.le hQ x0 c u z0 z0 hcenter0 hradius hfirstdist hself
  let second := eval oracle (modelSolve ε R Q M γ c z0)
  have hsecond := (QuarticLocalTuning.modelSolve_certificate f hf hc hε hR hQ hL.le hγ.le hLhi hγhi
    hMlo hMhi le_rfl hT x0 c z0 hG0 hH0 hfirstpoints.2.1 hfirstpoints.2.2.1).2
  by_cases hs₁ : ‖second.trueGradient‖ ≤ tol
  · have he (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q)) :
        output seed = classify γ tol c (z0 + second.displacement) second.trueGradient := by
      dsimp only [output]
      unfold trial
      simp only [modelCost, stagesCost, trialCost, logarithm]
      rw [eval_bind, ite_eq_right hs₀, eval_bind, ite_eq_left hs₁, eval_padResult]
    have hn := classify_not_failed (γ := γ) c (z0 + second.displacement) second.trueGradient (Or.inr hs₁)
    constructor
    · intro seed
      rw [he]
      exact classify_correct (hbase.differentiable (by norm_num)) hcbase hγ hR.le hcut.1 hcut.2
        c (z0 + second.displacement) xstar second.trueGradient hcenter hsecond.1
    · simp only [he, hn, ↓reduceIte, Fintype.expect_const]
      positivity
  let y0 := z0 + second.displacement
  let Δ := 3 * (‖second.trueGradient‖ ^ 4 / γ) ^ (1 / 3 : ℝ)
  have hi := initialization_bounds hbase hcbase hγ hM hQ hR.le (by positivity : 0 ≤ tol) hκ
    x0 c u first second hmin hcenter0 hradius hTF hfirst hsecond hs₀ hs₁
  let Y := fun seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q) =>
    eval oracle (stages M γ c (24 * logarithm Q) (64 * logarithm Q) Δ y0 seed)
  let last := fun seed => eval oracle (modelSolve ε R Q M γ c (Y seed))
  have he (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q)) :
      output seed = classify γ tol c (Y seed + (last seed).displacement) (last seed).trueGradient := by
    dsimp only [output]
    unfold trial
    simp only [modelCost, stagesCost, trialCost, logarithm]
    rw [eval_bind, ite_eq_right hs₀, eval_bind, ite_eq_right hs₁, eval_bind, eval_map]
    rfl
  have hlast (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q)) :
      Certificate F M tol (Y seed) (last seed) :=
    (final_model_certificate f hf hc hε hR hQ hL.le hγ hi.1.le hLhi hγhi hMlo hMhi le_rfl hT
      x0 c y0 hG0 hH0 hi.2.2.2.2.1 hi.2.2.2.2.2 hi.2.2.2.1 _ _ seed).2
  constructor
  · intro seed
    rw [he]
    exact classify_correct (hbase.differentiable (by norm_num)) hcbase hγ hR.le hcut.1 hcut.2
      c (Y seed + (last seed).displacement) xstar (last seed).trueGradient hcenter (hlast seed).1
  · let δ := 1 / (4 * (64 * logarithm Q : ℕ) * (N : ℝ))
    have hJ : (n : ℝ) * (1 / 2 : ℝ) ^ (24 * logarithm Q) ≤ δ / 2 := by
      simpa only [δ, logarithm, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        QuarticStageTuning.stage_failure_tuning hQ hN hnQ hNQ
    have hgap0 : (objective f y0 + γ * value (y0 - c)) - (objective f u + γ * value (u - c)) ≤ Δ := by
      simpa only [F, penalty, zero_div, zero_mul, add_zero] using hi.2.1
    have hfailure := QuarticTrialStages.stages_failure f hf hc hL.le hγ (by positivity : 0 ≤ δ) hLγ hT
      c u hminu (24 * logarithm Q) hJ (64 * logarithm Q) Δ hi.1 y0 hgap0
    have hpoint (seed : Fin (64 * logarithm Q) → StageSeed n (24 * logarithm Q)) :
        (if output seed = .failed then (1 : ℝ) else 0) ≤
          (if F (Y seed) - F u > (3 / 4 : ℝ) ^ (64 * logarithm Q) * Δ then (1 : ℝ) else 0) := by
      by_cases hbad : F (Y seed) - F u > (3 / 4 : ℝ) ^ (64 * logarithm Q) * Δ
      · simp only [hbad, ↓reduceIte]
        split_ifs <;> norm_num
      · have hgood : F (Y seed) - F u ≤ Δ / Q ^ 16 := by
          apply (le_of_not_gt hbad).trans
          have hh := mul_le_mul_of_nonneg_right (QuarticStageTuning.stage_contraction hQ) hi.1.le
          change (3 / 4 : ℝ) ^ (64 * logarithm Q) * Δ ≤ (1 / Q ^ 16) * Δ at hh
          convert hh using 1; ring
        have hn := terminal_classify_success hbase hcbase hγ hM hQ hκ c u (Y seed) (last seed)
          hmin hTF hi.2.2.1 hgood (hlast seed)
        simp only [he, hn, hbad, ↓reduceIte, le_refl]
    have hmean := Finset.expect_le_expect (s := Finset.univ) (fun seed _ => hpoint seed)
    have hf' : (𝔼 seed, (if F (Y seed) - F u > (3 / 4 : ℝ) ^ (64 * logarithm Q) * Δ then (1 : ℝ) else 0)) ≤
        (64 * logarithm Q : ℕ) * δ / 46 := by
      simpa only [F, penalty, zero_div, zero_mul, add_zero] using hfailure
    apply hmean.trans (hf'.trans ?_)
    have hS : (0 : ℝ) < (64 * logarithm Q : ℕ) := by
      have hh : 0 < 64 * logarithm Q := by unfold logarithm; omega
      exact_mod_cast hh
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    dsimp [δ]
    field_simp
    norm_num

end LongTails.Proofs.QuarticTrialGuarantee
