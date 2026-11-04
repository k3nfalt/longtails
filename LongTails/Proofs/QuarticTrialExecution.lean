import LongTails.Proofs.QuarticTrialGeometry

namespace LongTails.Proofs.QuarticTrialExecution

open LongTails.Algorithms.QuarticProximalTrial LongTails.Algorithms.QuarticProximal
open LongTails.Algorithms.TaylorCorrectedNewton
open OracleTemplate OracleTemplate.QueryPlan

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

omit [FiniteDimensional ℝ E] in
lemma eval_padResult {U : Type*} (oracle : Fin n × E → Reply E) (q : Fin n × E) (k : ℕ) (u : U) :
    eval oracle (padResult q k u) = u := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

noncomputable def ValidAt (f : E → ℝ) (ε γ : ℝ) (c xstar : E) : TrialResult E → Prop
  | .accurate y => f y - f xstar ≤ ε
  | .proximal y g => g = gradient f y ∧ ‖g + γ • grad (y - c)‖ ≤ γ * ‖y - c‖ ^ 3 / 32
  | .failed => False

lemma classify_correct {f : E → ℝ} (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ Set.univ f) {γ R B tol ε : ℝ} (hγ : 0 < γ) (hR : 0 ≤ R)
    (hsmall : 32 * tol ≤ γ * R ^ 3) (haccuracy : 33 * tol * (B + R) ≤ ε)
    (c y xstar g : E) (hcstar : ‖c - xstar‖ ≤ B)
    (hg : g = gradient (fun x => f x + penalty γ 0 c c x) y) :
    classify γ tol c y g ≠ .failed → ValidAt f ε γ c xstar (classify γ tol c y g) := by
  classical
  have he : g = gradient f y + γ • grad (y - c) := by
    have hh := (QuarticProximalGeometry.add_penalty_hasGradientAt (fun x => (hf x).hasGradientAt) γ 0 c c y).gradient
    rw [hg]
    simpa [penaltyGrad] using hh
  unfold classify
  split_ifs with hres htol
  · intro _
    dsimp [ValidAt]
    constructor
    · rw [he, add_sub_cancel_right]
    · simpa only [sub_add_cancel] using hres
  · intro _
    dsimp [ValidAt]
    apply QuarticProximalBounds.small_gradient_accuracy hf hc hγ hR hsmall haccuracy c y xstar hcstar
    · rwa [← hg]
    · nlinarith
  · simp

omit [FiniteDimensional ℝ E] in
lemma classify_not_failed {γ tol : ℝ} (c y g : E)
    (h : ‖g‖ ≤ γ * ‖y - c‖ ^ 3 / 32 ∨ ‖g‖ ≤ tol) : classify γ tol c y g ≠ .failed := by
  classical
  unfold classify
  split_ifs with hres htol
  · simp
  · simp
  · rcases h with h | h
    · exact False.elim (hres h)
    · exact False.elim (htol h)

lemma trialCost_bound (n : ℕ) (Q : ℝ) : trialCost n Q ≤ 2 ^ 29 * n * logarithm Q ^ 2 := by
  have hh := QuarticStageTuning.trial_query_count n (logarithm Q) (by simp [logarithm])
  dsimp [trialCost, modelCost, stagesCost]
  convert hh using 1; ring


lemma small_tolerance_conditions {ε R Q γ : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q)
    (hγ : ε / (R ^ 4 * Q) ≤ γ) :
    32 * (ε / (R * Q ^ 12)) ≤ γ * R ^ 3 ∧
      33 * (ε / (R * Q ^ 12)) * (R * Q ^ 8 + R) ≤ ε := by
  have hQpos : 0 < Q := by linarith
  have h1 : 1 ≤ Q := by linarith
  constructor
  · have h11 : 32 ≤ Q ^ 11 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 11
      norm_num at hh
      linarith
    calc
      _ ≤ ε / (R * Q) := by
        have he : 32 * (ε / (R * Q ^ 12)) = 32 * ε / (R * Q ^ 12) := by ring
        rw [he]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have hh := mul_le_mul_of_nonneg_right h11 (show 0 ≤ ε * R * Q by positivity)
        have hp : Q ^ 12 = Q ^ 11 * Q := by ring
        rw [hp]
        nlinarith
      _ = (ε / (R ^ 4 * Q)) * R ^ 3 := by field_simp
      _ ≤ γ * R ^ 3 := mul_le_mul_of_nonneg_right hγ (by positivity)
  · have h4 : 66 ≤ Q ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hQ 4
      norm_num at hh
      linarith
    have h8 : (1 : ℝ) ≤ Q ^ 8 := one_le_pow₀ h1
    have hp : 33 * (Q ^ 8 + 1) ≤ Q ^ 12 := by
      have hh := mul_le_mul_of_nonneg_right h4 (show 0 ≤ Q ^ 8 by positivity)
      have he : Q ^ 12 = Q ^ 4 * Q ^ 8 := by ring
      rw [he]
      nlinarith
    have he : 33 * (ε / (R * Q ^ 12)) * (R * Q ^ 8 + R) = ε * (33 * (Q ^ 8 + 1)) / Q ^ 12 := by field_simp
    rw [he]
    exact (div_le_iff₀ (by positivity)).mpr (mul_le_mul_of_nonneg_left hp hε.le)

lemma initial_delta_cube {γ L a D r : ℝ} (hγ : 0 < γ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hmodel : a ^ 4 ≤ 2 * L * D ^ 3) (hgap : D ≤ 2 * L * r ^ 4) :
    γ * (3 * (a ^ 4 / γ) ^ (1 / 3 : ℝ)) ^ 3 ≤ 1000 * L ^ 4 * r ^ 12 := by
  have he := GradientOnlyExecution.rpow_third_cube (by positivity : 0 ≤ a ^ 4 / γ)
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hgap 3) (show 0 ≤ 2 * L by positivity)
  have ha : a ^ 4 ≤ 16 * L ^ 4 * r ^ 12 := by nlinarith
  rw [mul_pow, he]
  have hi : γ * (3 ^ 3 * (a ^ 4 / γ)) = 27 * a ^ 4 := by field_simp; ring
  rw [hi]
  nlinarith [show 0 ≤ L ^ 4 * r ^ 12 by positivity]


lemma final_model_certificate [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {ε R Q L M γ Δ : ℝ} (hε : 0 < ε) (hR : 0 < R) (hQ : 3 ≤ Q) (hL : 0 ≤ L) (hγ : 0 < γ) (hΔ : 0 ≤ Δ)
    (hLhi : L ≤ ε / R ^ 4 * Q) (hγhi : γ ≤ ε / R ^ 4 * Q)
    (hMlo : ε / R ^ 4 ≤ M) (hMhi : M ≤ ε / R ^ 4 * Q ^ 3) (hLM : L + 6 * γ ≤ M)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (x0 c y0 : E) (hG0 : ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) x0‖ ≤ ε / R * Q)
    (hH0 : ‖fderiv ℝ (gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f)) x0‖ ≤ ε / R ^ 2 * Q)
    (hy0 : ‖y0 - x0‖ ≤ R * Q ^ 13) (hyc : ‖y0 - c‖ ≤ R * Q ^ 13)
    (hρ : (12 * Δ / γ) ^ (1 / 4 : ℝ) ≤ R * Q ^ 10)
    (J S : ℕ) (seed : Fin S → StageSeed n J) :
    let F := fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective f x + penalty γ 0 c c x
    let oracle := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
    let y := eval oracle (stages M γ c J S Δ y0 seed)
    let last := eval oracle (modelSolve ε R Q M γ c y)
    last.accepted = true ∧ TensorFreeModelExecution.Certificate F M (ε / (R * Q ^ 12)) y last := by
  let oracle := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
  have hd := QuarticTrialStages.stages_distance oracle M hγ c J S Δ hΔ y0 seed
  have hbounds := QuarticTrialGeometry.stage_points_radius hR.le hQ x0 c y0
    (eval oracle (stages M γ c J S Δ y0 seed)) hρ hy0 hyc hd
  exact QuarticLocalTuning.modelSolve_certificate f hf hc hε hR hQ hL hγ.le hLhi hγhi
    hMlo hMhi hLM hT x0 c _ hG0 hH0 hbounds.1 hbounds.2


lemma terminal_classify_success {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {γ L Q Δ tol : ℝ} (hγ : 0 < γ) (hL : 0 < L) (hQ : 3 ≤ Q)
    (hκ : L ≤ γ * Q ^ 2) (c u y : E) (last : LongTails.Algorithms.TensorFreeModel.ModelState E)
    (hmin : ∀ x, f u + penalty γ 0 c c u ≤ f x + penalty γ 0 c c x)
    (hT : ∀ x z, ‖fderiv ℝ (fderiv ℝ (gradient (fun v => f v + penalty γ 0 c c v))) x -
      fderiv ℝ (fderiv ℝ (gradient (fun v => f v + penalty γ 0 c c v))) z‖ ≤ L * ‖x - z‖)
    (hinit : γ * Δ ^ 3 ≤ 1000 * L ^ 4 * ‖u - c‖ ^ 12)
    (hgood : (f y + penalty γ 0 c c y) - (f u + penalty γ 0 c c u) ≤ Δ / Q ^ 16)
    (hcert : TensorFreeModelExecution.Certificate (fun x => f x + penalty γ 0 c c x) L tol y last) :
    classify γ tol c (y + last.displacement) last.trueGradient ≠ .failed := by
  by_cases hs : ‖last.trueGradient‖ ≤ tol
  · exact classify_not_failed _ _ _ (Or.inr hs)
  let F := fun x => f x + penalty γ 0 c c x
  have hF : ContDiff ℝ 3 F := hf.add ((QuarticProximalGeometry.penalty_contDiff γ 0 c c).of_le le_top)
  have hcF : ConvexOn ℝ Set.univ F :=
    QuarticFiniteSum.component_convex (fun _ : Fin 1 => f) (fun _ => hf) (fun _ => hc) hγ.le le_rfl c c 0
  have hm : ‖LongTails.Algorithms.TensorFreeModel.exactGradient (gradient F y) (fderiv ℝ (gradient F) y)
      (fderiv ℝ (fderiv ℝ (gradient F)) y) L last.displacement‖ ≤ ‖gradient F (y + last.displacement)‖ / 6 := by
    rcases hcert.2 with hsmall | hmodel
    · exact False.elim (hs hsmall)
    · simpa only [hcert.1] using hmodel
  have ha4 := TensorFreeProximal.model_gap_descent hF hcF hL hT y last.displacement u hmin hm
  have ha := QuarticStageTuning.terminal_gradient_bound hγ hL.le (norm_nonneg (u - c))
    (sub_nonneg.mpr (hmin y)) hQ hκ hinit hgood ha4
  have hd := (QuarticProximalBounds.quartic_gradient_bounds
    (hf.differentiable (by norm_num)) hc hγ.le c u (y + last.displacement) hmin).1
  have htriangle : ‖u - c‖ ≤ ‖y + last.displacement - u‖ + ‖y + last.displacement - c‖ := by
    simpa only [norm_sub_rev u (y + last.displacement)] using
      norm_sub_le_norm_sub_add_norm_sub u (y + last.displacement) c
  have hres := QuarticProximalBounds.terminal_residual hγ (norm_nonneg (u - c))
    (norm_nonneg (y + last.displacement - c)) htriangle hd ha
  apply classify_not_failed _ _ _ (Or.inl ?_)
  rwa [hcert.1]


lemma initialization_bounds {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {γ L Q R tol : ℝ} (hγ : 0 < γ) (hL : 0 < L)
    (hQ : 3 ≤ Q) (hR : 0 ≤ R) (htol : 0 ≤ tol) (hκ : L ≤ γ * Q ^ 2)
    (x0 c u : E) (first second : LongTails.Algorithms.TensorFreeModel.ModelState E)
    (hmin : ∀ x, f u + penalty γ 0 c c u ≤ f x + penalty γ 0 c c x)
    (hcenter : ‖c - x0‖ ≤ R * (Q ^ 8 + 1)) (hradius : ‖u - c‖ ≤ R * Q ^ 8)
    (hT : ∀ x z, ‖fderiv ℝ (fderiv ℝ (gradient (fun v => f v + penalty γ 0 c c v))) x -
      fderiv ℝ (fderiv ℝ (gradient (fun v => f v + penalty γ 0 c c v))) z‖ ≤ L * ‖x - z‖)
    (hfirst : TensorFreeModelExecution.Certificate (fun x => f x + penalty γ 0 c c x) L tol c first)
    (hsecond : TensorFreeModelExecution.Certificate (fun x => f x + penalty γ 0 c c x) L tol (c + first.displacement) second)
    (hfirst_large : ¬‖first.trueGradient‖ ≤ tol) (hsecond_large : ¬‖second.trueGradient‖ ≤ tol) :
    let F := fun x => f x + penalty γ 0 c c x
    let y0 := c + first.displacement + second.displacement
    let Δ := 3 * (‖second.trueGradient‖ ^ 4 / γ) ^ (1 / 3 : ℝ)
    0 < Δ ∧ F y0 - F u ≤ Δ ∧ γ * Δ ^ 3 ≤ 1000 * L ^ 4 * ‖u - c‖ ^ 12 ∧
      (12 * Δ / γ) ^ (1 / 4 : ℝ) ≤ R * Q ^ 10 ∧
      ‖y0 - x0‖ ≤ R * Q ^ 13 ∧ ‖y0 - c‖ ≤ R * Q ^ 13 := by
  let F := fun x => f x + penalty γ 0 c c x
  let z0 := c + first.displacement
  let y0 := z0 + second.displacement
  let Δ := 3 * (‖second.trueGradient‖ ^ 4 / γ) ^ (1 / 3 : ℝ)
  have hF : ContDiff ℝ 3 F := hf.add ((QuarticProximalGeometry.penalty_contDiff γ 0 c c).of_le le_top)
  have hcF : ConvexOn ℝ Set.univ F :=
    QuarticFiniteSum.component_convex (fun _ : Fin 1 => f) (fun _ => hf) (fun _ => hc) hγ.le le_rfl c c 0
  have hm₀ : ‖LongTails.Algorithms.TensorFreeModel.exactGradient (gradient F c) (fderiv ℝ (gradient F) c)
      (fderiv ℝ (fderiv ℝ (gradient F)) c) L first.displacement‖ ≤ ‖gradient F z0‖ / 6 := by
    simpa only [hfirst.1] using hfirst.2.resolve_left hfirst_large
  have hm₁ : ‖LongTails.Algorithms.TensorFreeModel.exactGradient (gradient F z0) (fderiv ℝ (gradient F) z0)
      (fderiv ℝ (fderiv ℝ (gradient F)) z0) L second.displacement‖ ≤ ‖gradient F y0‖ / 6 := by
    simpa only [hsecond.1] using hsecond.2.resolve_left hsecond_large
  have hz := QuarticTrialGeometry.model_prox_distance hf hc hγ hL hQ hκ c c first.displacement u hmin hT hm₀
  have hy := QuarticTrialGeometry.model_prox_distance hf hc hγ hL hQ hκ c z0 second.displacement u hmin hT hm₁
  have hpoints := QuarticTrialGeometry.initial_points_radius hR hQ x0 c u z0 y0 hcenter hradius hz hy
  have hpositive : 0 < ‖second.trueGradient‖ := lt_of_le_of_lt htol (lt_of_not_ge hsecond_large)
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hgrad := (QuarticProximalBounds.quartic_gradient_bounds
    (hf.differentiable (by norm_num)) hc hγ.le c u y0 hmin).2
  have hgap : F y0 - F u ≤ Δ := by
    have hh := QuarticProximalBounds.computed_gap_bound hγ hgrad
    simpa only [Δ, hsecond.1] using hh
  have h₀ := (TensorFreeProximal.model_distance_bounds hF hcF hL hT c first.displacement u hmin hm₀).2
  have h₁ := TensorFreeProximal.model_gap_descent hF hcF hL hT z0 second.displacement u hmin hm₁
  have hinit : γ * Δ ^ 3 ≤ 1000 * L ^ 4 * ‖u - c‖ ^ 12 := by
    have hh := initial_delta_cube hγ hL.le (sub_nonneg.mpr (hmin z0)) h₁ h₀
    simpa only [Δ, hsecond.1, norm_sub_rev c u] using hh
  have hrpow : ((12 * Δ / γ) ^ (1 / 4 : ℝ)) ^ 4 = 12 * Δ / γ := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n := 4)
      (by positivity : 0 ≤ 12 * Δ / γ) (by decide)
  have hρ := QuarticTrialGeometry.initial_radius_factor hγ hL.le (norm_nonneg (u - c)) hQ hκ hinit hrpow
  have hρcap : (12 * Δ / γ) ^ (1 / 4 : ℝ) ≤ R * Q ^ 10 := by
    have hh := hρ.trans (mul_le_mul_of_nonneg_left hradius (by positivity))
    convert hh using 1; ring
  exact ⟨hΔ, hgap, hinit, hρcap, hpoints.2.2.2⟩

end LongTails.Proofs.QuarticTrialExecution
