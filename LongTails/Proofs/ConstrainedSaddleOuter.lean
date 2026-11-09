import LongTails.Proofs.ConstrainedSaddleTracking

open scoped RealInnerProductSpace
open Set

namespace LongTails.Proofs.ConstrainedSaddleOuter

open LongTails.Setups.ConstrainedMinimaxSecondOrder
open LongTails.Algorithms.ConstrainedSaddleCubic
open ConstrainedMinimaxEnvelope ConstrainedSaddleInner ConstrainedSaddleTracking

lemma envelope_gradient_lipschitz {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z z' : p.E) :
    ‖gradient (envelope f) z - gradient (envelope f) z'‖ ≤ 6 * p.L * ‖z - z'‖ := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hh := primal_center_distance_sq H hv z z'
  have hp : ‖primal f z - primal f z'‖ ≤ 2 * ‖z - z'‖ := by
    nlinarith [norm_nonneg (z - z')]
  rw [(envelope_hasGradient H hv z).gradient, (envelope_hasGradient H hv z').gradient,
    ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  have he : (z - primal f z) - (z' - primal f z') = (z - z') - (primal f z - primal f z') := by abel
  rw [he]
  have ht := norm_sub_le (z - z') (primal f z - primal f z')
  have hm := mul_le_mul_of_nonneg_left (ht.trans (add_le_add le_rfl hp)) (by positivity : 0 ≤ 2 * p.L)
  nlinarith

lemma model_envelope_eq {p : Params} {w : Space p} {c : ℝ} {g : Space p}
    {A : Space p →L[ℝ] Space p} (Q : Regularity p (quadraticModel w c g A))
    (hv : spec.valid p) (z : p.E) :
    modelEnvelope w c g A z = envelope (quadraticModel w c g A) z := by
  let q := quadraticModel w c g A
  have hb : BddBelow (range (fun u => value q u + p.L * ‖u - z‖ ^ 2)) := by
    refine ⟨envelope q z, ?_⟩
    rintro _ ⟨u, rfl⟩
    exact primal_min Q hv z u
  apply le_antisymm
  · exact ciInf_le hb (primal q z)
  · exact le_ciInf (fun u => primal_min Q hv z u)

lemma model_scale_positive {p : Params} (hv : spec.valid p) : 0 < modelScale p := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ := hv.1
  have hρ := hv.2.2.1
  unfold modelScale
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma smooth_function_lower {M : E → ℝ} {G : E → E} {γ : ℝ}
    (hg : ∀ x, HasGradientAt M (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ γ * ‖x - y‖) (x y : E) :
    M x - ‖G x‖ * ‖y - x‖ - γ / 2 * ‖y - x‖ ^ 2 ≤ M y := by
  have hh := OracleTemplate.Gradient.smooth_upper_bound
    (fun z => OracleTemplate.TwoSidedPL.hasGradientAt_neg' (hg z))
    (fun a b => by simpa only [neg_sub_neg, norm_sub_rev] using hlip a b) x y
  change -M y ≤ -M x + ⟪-G x, y - x⟫ + γ / 2 * ‖y - x‖ ^ 2 at hh
  have hi := real_inner_le_norm (-G x) (y - x)
  rw [norm_neg] at hi
  linarith

lemma cubic_regularized_minimum [FiniteDimensional ℝ E] {M : E → ℝ} {G : E → E}
    {γ R : ℝ} (hγ : 0 ≤ γ) (hR : 0 < R)
    (hg : ∀ x, HasGradientAt M (G x) x)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ γ * ‖x - y‖) (z0 : E) :
    ∃ z, ∀ u, M z + R * ‖z - z0‖ ^ 3 / 3 ≤ M u + R * ‖u - z0‖ ^ 3 / 3 := by
  let b := 1 + (3 * ‖G z0‖ + 3 * γ) / R
  let F := fun z => M z + R * ‖z - z0‖ ^ 3 / 3
  have hb : 0 < b := by dsimp [b]; positivity
  have hc : Continuous F := by
    have hM : Continuous M := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
    exact hM.add ((continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 3)).div_const 3)
  have hout (u : E) (hu : b ≤ ‖u - z0‖) : M z0 ≤ F u := by
    have hlo := smooth_function_lower hg hlip z0 u
    have h1 : 1 ≤ ‖u - z0‖ := by
      have hh : 0 ≤ (3 * ‖G z0‖ + 3 * γ) / R := by positivity
      dsimp [b] at hu
      linarith
    have h2 : 3 * ‖G z0‖ + 3 * γ ≤ R * ‖u - z0‖ := by
      have hh : (3 * ‖G z0‖ + 3 * γ) / R ≤ ‖u - z0‖ := by dsimp [b] at hu; linarith
      have hh' := (div_le_iff₀ hR).mp hh
      nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖u - z0‖)
    have h4 := mul_nonneg (norm_nonneg (G z0)) (show 0 ≤ ‖u - z0‖ ^ 2 - ‖u - z0‖ by nlinarith)
    dsimp [F]
    nlinarith [mul_nonneg hγ (sq_nonneg ‖u - z0‖)]
  obtain ⟨z, hz, hm⟩ := (isCompact_closedBall z0 b).exists_isMinOn
    ⟨z0, by simp [hb.le]⟩ hc.continuousOn
  refine ⟨z, fun u => ?_⟩
  change F z ≤ F u
  by_cases hu : u ∈ Metric.closedBall z0 b
  · exact hm hu
  · have hzu : b ≤ ‖u - z0‖ := by
      have hh : ¬‖u - z0‖ ≤ b := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
      exact (lt_of_not_ge hh).le
    have hh := hm (show z0 ∈ Metric.closedBall z0 b by simp [hb.le])
    have he : F z0 = M z0 := by simp [F]
    change F z ≤ F z0 at hh
    rw [he] at hh
    exact hh.trans (hout u hzu)

lemma cubic_objective_hasGradient {M : E → ℝ} {G : E → E}
    (hg : ∀ x, HasGradientAt M (G x) x) (R : ℝ) (z0 z : E) :
    HasGradientAt (fun x => M x + R * ‖x - z0‖ ^ 3 / 3)
      (G z + (R * ‖z - z0‖) • (z - z0)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hc := (CubicRegularization.cubic_hasFDerivAt (z - z0)).comp z
    ((hasFDerivAt_id z).sub_const z0)
  convert (hg z).hasFDerivAt.add (hc.const_mul R) using 1
  · funext x
    simp only [Pi.add_apply, Function.comp_apply, id_eq, CubicRegularization.cubic]
    ring
  · ext u
    simp [CubicRegularization.cubicGradient, InnerProductSpace.toDual_apply_apply]
    ring

lemma cubic_minimum_stationary {M : E → ℝ} {G : E → E}
    (hg : ∀ x, HasGradientAt M (G x) x) (R : ℝ) (z0 z : E)
    (hm : ∀ u, M z + R * ‖z - z0‖ ^ 3 / 3 ≤ M u + R * ‖u - z0‖ ^ 3 / 3) :
    G z + (R * ‖z - z0‖) • (z - z0) = 0 := by
  have hmin : IsLocalMin (fun x => M x + R * ‖x - z0‖ ^ 3 / 3) z :=
    Filter.Eventually.of_forall hm
  have hd := cubic_objective_hasGradient hg R z0 z
  have hz := hmin.hasFDerivAt_eq_zero hd.hasFDerivAt
  have hh := DFunLike.congr_fun hz (G z + (R * ‖z - z0‖) • (z - z0))
  have hn : ‖G z + (R * ‖z - z0‖) • (z - z0)‖ ^ 2 = 0 := by
    simpa only [InnerProductSpace.toDual_apply_apply, real_inner_self_eq_norm_sq,
      zero_apply] using hh
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (G z + (R * ‖z - z0‖) • (z - z0))]

lemma model_minimum_exists {p : Params} {w : Space p} {c : ℝ} {g : Space p}
    {A : Space p →L[ℝ] Space p} (Q : Regularity p (quadraticModel w c g A))
    (hv : spec.valid p) (z0 : p.E) :
    ∃ z, ∀ u, modelObjective w c g A z0 z ≤ modelObjective w c g A z0 u := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hg (z : p.E) : HasGradientAt (envelope (quadraticModel w c g A))
      (gradient (envelope (quadraticModel w c g A)) z) z := by
    rw [(envelope_hasGradient Q hv z).gradient]
    exact envelope_hasGradient Q hv z
  have hh := cubic_regularized_minimum (by positivity : 0 ≤ 6 * p.L)
    (model_scale_positive hv) hg (envelope_gradient_lipschitz Q hv) z0
  simpa only [modelObjective, model_envelope_eq Q hv] using hh

lemma cubic_center_minimum {p : Params} {w : Space p} {c : ℝ} {g : Space p}
    {A : Space p →L[ℝ] Space p} (Q : Regularity p (quadraticModel w c g A))
    (hv : spec.valid p) (z0 u : p.E) :
    modelObjective w c g A z0 (cubicCenter w c g A z0) ≤ modelObjective w c g A z0 u := by
  classical
  unfold cubicCenter
  rw [dite_eq_left (model_minimum_exists Q hv z0)]
  exact (model_minimum_exists Q hv z0).choose_spec u

lemma cubic_center_stationary {p : Params} {w : Space p} {c : ℝ} {g : Space p}
    {A : Space p →L[ℝ] Space p} (Q : Regularity p (quadraticModel w c g A))
    (hv : spec.valid p) (z0 : p.E) :
    let z := cubicCenter w c g A z0
    gradient (envelope (quadraticModel w c g A)) z +
      (modelScale p * ‖z - z0‖) • (z - z0) = 0 := by
  apply cubic_minimum_stationary
  · intro z
    rw [(envelope_hasGradient Q hv z).gradient]
    exact envelope_hasGradient Q hv z
  · intro u
    simpa only [modelObjective, model_envelope_eq Q hv] using cubic_center_minimum Q hv z0 u

open ConstrainedSaddlePerturbation

lemma tracking_residual_conditions {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (state : Space p × Space p)
    (hw : TrackingInvariant f z state) :
    state.1.snd ∈ p.Y ∧
      (gradient f state.1).fst + (2 * p.L) • (state.1.fst - z) = state.2.fst ∧
      ∀ y ∈ p.Y, ⟪(gradient f state.1).snd - state.2.snd, y - state.1.snd⟫ ≤ 0 := by
  let q := tilt f state.1 state.2
  have Q : Regularity p q := tilt_regularity H state.1 state.2
  have hp : primal q z = state.1.fst := hw.2.2.1
  have hd : dual q z = state.1.snd := hw.2.2.2
  have ha : WithLp.toLp 2 (primal q z, dual q z) = state.1 := by rw [hp, hd]; rfl
  have hm := (dual_spec Q hv z).1
  rw [hd] at hm
  refine ⟨hm, ?_, ?_⟩
  · have hh := saddle_primal_zero Q hv z
    rw [ha, hp] at hh
    change (gradient (tilt f state.1 state.2) state.1).fst + _ = 0 at hh
    rw [tilt_gradient H] at hh
    change (gradient f state.1).fst - state.2.fst + (2 * p.L) • (state.1.fst - z) = 0 at hh
    rw [← sub_eq_zero]
    convert hh using 1
    abel
  · intro y hy
    have hh := saddle_dual_normal Q hv z y hy
    rw [ha, hd] at hh
    change ⟪(gradient (tilt f state.1 state.2) state.1).snd, y - state.1.snd⟫ ≤ 0 at hh
    rw [tilt_gradient H] at hh
    exact hh

lemma corrected_model_regularity {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (w e : Space p) :
    Regularity p (quadraticModel w (f w) (gradient f w - e) (fderiv ℝ (gradient f) w)) := by
  have hh := ConstrainedSaddleModel.model_regularity (tilt_regularity H w e) hv w
  rw [tilt_jet H] at hh
  exact hh

lemma outer_step_bounds {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (state : Space p × Space p)
    (hw : TrackingInvariant f z state) :
    let z' := OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state)
    envelope f z' ≤ envelope f z - modelScale p * ‖z' - z‖ ^ 3 / 6 +
        2 * Real.sqrt (p.L / p.μ) * ‖state.2‖ * ‖z' - z‖ ∧
      ‖gradient (envelope f) z'‖ ≤ 2 * modelScale p * ‖z' - z‖ ^ 2 +
        2 * Real.sqrt (p.L / p.μ) * ‖state.2‖ := by
  let q := quadraticModel state.1 (f state.1) (gradient f state.1 - state.2)
    (fderiv ℝ (gradient f) state.1)
  let z' := cubicCenter state.1 (f state.1) (gradient f state.1 - state.2)
    (fderiv ℝ (gradient f) state.1) z
  have Q : Regularity p q := corrected_model_regularity H hv state.1 state.2
  have hc := tracking_residual_conditions H hv z state hw
  have he := corrected_model_errors H hv z z' state.1 state.2 hc.1 hc.2.1 hc.2.2
  change |(envelope f z' - envelope f z) - (envelope q z' - envelope q z)| ≤
      modelScale p * ‖z' - z‖ ^ 3 / 6 + 2 * Real.sqrt (p.L / p.μ) * ‖state.2‖ * ‖z' - z‖ ∧
    ‖gradient (envelope f) z' - gradient (envelope q) z'‖ ≤
      modelScale p * ‖z' - z‖ ^ 2 + 2 * Real.sqrt (p.L / p.μ) * ‖state.2‖ at he
  have hm := cubic_center_minimum Q hv z z
  simp only [modelObjective, model_envelope_eq Q hv, sub_self, norm_zero,
    zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div, add_zero] at hm
  change envelope q z' + modelScale p * ‖z' - z‖ ^ 3 / 3 ≤ envelope q z at hm
  have hs := cubic_center_stationary Q hv z
  change gradient (envelope q) z' + (modelScale p * ‖z' - z‖) • (z' - z) = 0 at hs
  have hn : ‖gradient (envelope q) z'‖ = modelScale p * ‖z' - z‖ ^ 2 := by
    rw [add_eq_zero_iff_eq_neg] at hs
    rw [hs, norm_neg, norm_smul, Real.norm_of_nonneg
      (mul_nonneg (model_scale_positive hv).le (norm_nonneg _))]
    ring
  change (envelope f z' ≤ envelope f z - modelScale p * ‖z' - z‖ ^ 3 / 6 +
    2 * Real.sqrt (p.L / p.μ) * ‖state.2‖ * ‖z' - z‖) ∧
    (‖gradient (envelope f) z'‖ ≤ 2 * modelScale p * ‖z' - z‖ ^ 2 +
      2 * Real.sqrt (p.L / p.μ) * ‖state.2‖)
  constructor
  · have hh := (abs_le.mp he.1).2
    change envelope f z' ≤ _
    linarith
  · have ht := norm_le_norm_add_norm_sub' (gradient (envelope f) z') (gradient (envelope q) z')
    rw [hn] at ht
    change ‖gradient (envelope f) z'‖ ≤ _
    linarith [he.2]

lemma residual_accuracy_bound {p : Params} (hv : spec.valid p) (e : Space p)
    (he : ‖e‖ ≤ residualTolerance p) :
    (p.L / p.μ + 2 * Real.sqrt (p.L / p.μ) + 1) * ‖e‖ ≤ p.ε / 128 := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ := hv.1
  have hden : 0 < 128 * (p.L / p.μ + 2 * Real.sqrt (p.L / p.μ) + 1) := by positivity
  have hh := he.trans (min_le_right _ _)
  have hd := (le_div_iff₀ hden).mp hh
  linarith

lemma residual_envelope_bound {p : Params} (hv : spec.valid p) (e : Space p)
    (he : ‖e‖ ≤ residualTolerance p) :
    2 * Real.sqrt (p.L / p.μ) * ‖e‖ ≤ p.ε / 128 := by
  have hh := residual_accuracy_bound hv e he
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ := hv.1
  have hk : 0 ≤ p.L / p.μ := by positivity
  nlinarith [mul_nonneg hk (norm_nonneg e), norm_nonneg e]

lemma outer_large_step_descent {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (state : Space p × Space p)
    (hw : TrackingInvariant f z state)
    (hstep : p.ε / (4 * modelScale p) ≤
      ‖OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state) - z‖ ^ 2) :
    let z' := OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state)
    envelope f z' ≤ envelope f z - modelScale p * ‖z' - z‖ ^ 3 / 12 := by
  let z' := OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state)
  have hb := (outer_step_bounds H hv z state hw).1
  have he := residual_envelope_bound hv state.2 hw.2.1
  have hm := mul_le_mul_of_nonneg_right he (norm_nonneg (z' - z))
  have hR := model_scale_positive hv
  have hs := (div_le_iff₀ (by positivity : 0 < 4 * modelScale p)).mp hstep
  have ht := mul_le_mul_of_nonneg_right hs (norm_nonneg (z' - z))
  change envelope f z' ≤ _
  change envelope f z' ≤ envelope f z - modelScale p * ‖z' - z‖ ^ 3 / 6 +
    2 * Real.sqrt (p.L / p.μ) * ‖state.2‖ * ‖z' - z‖ at hb
  change p.ε * ‖z' - z‖ ≤ ‖z' - z‖ ^ 2 * (4 * modelScale p) * ‖z' - z‖ at ht
  nlinarith [mul_nonneg hR.le (pow_nonneg (norm_nonneg (z' - z)) 3)]

lemma outer_large_step_path {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (state : Space p × Space p)
    (hw : TrackingInvariant f z state)
    (hstep : p.ε / (4 * modelScale p) ≤
      ‖OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state) - z‖ ^ 2) :
    let z' := OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state)
    p.ε * ‖z' - z‖ / 48 ≤ envelope f z - envelope f z' := by
  have hb := outer_large_step_descent H hv z state hw hstep
  have hR := model_scale_positive hv
  have hs := (div_le_iff₀ (by positivity : 0 < 4 * modelScale p)).mp hstep
  have ht := mul_le_mul_of_nonneg_right hs
    (norm_nonneg (OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state) - z))
  dsimp only at hb ⊢
  nlinarith

lemma outer_small_step_accuracy {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (state next : Space p × Space p)
    (hw : TrackingInvariant f z state)
    (hn : TrackingInvariant f (OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state)) next)
    (hstep : ‖OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state) - z‖ ^ 2 ≤
      p.ε / (4 * modelScale p)) : ‖gradient (value f) next.1.fst‖ ≤ p.ε := by
  have hb := (outer_step_bounds H hv z state hw).2
  have h1 := residual_envelope_bound hv state.2 hw.2.1
  have h2 := residual_accuracy_bound hv next.2 hn.2.1
  have ht := tracked_output_gradient H hv _ next hn
  have hR := model_scale_positive hv
  have hs := (le_div_iff₀ (by positivity : 0 < 4 * modelScale p)).mp hstep
  have hε := hv.2.2.2.2.2.1
  dsimp only at hb
  nlinarith

lemma cubic_decrease_threshold {R ε r : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hr : 0 ≤ r) (hs : ε / (4 * R) ≤ r ^ 2) :
    ε * Real.sqrt ε / (96 * Real.sqrt R) ≤ R * r ^ 3 / 12 := by
  have hstep := (div_le_iff₀ (by positivity : 0 < 4 * R)).mp hs
  have he : (2 * Real.sqrt R * r) ^ 2 = 4 * R * r ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hR.le]
    ring
  have hroot : Real.sqrt ε ≤ 2 * Real.sqrt R * r := by
    have hz : 0 ≤ 2 * Real.sqrt R * r := by positivity
    nlinarith [Real.sq_sqrt hε.le]
  have hm := mul_le_mul hstep hroot (Real.sqrt_nonneg ε) (by positivity : 0 ≤ r ^ 2 * (4 * R))
  apply (div_le_iff₀ (by positivity : 0 < 96 * Real.sqrt R)).mpr
  convert hm using 1
  ring

lemma outer_large_step_decrease {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (state : Space p × Space p)
    (hw : TrackingInvariant f z state)
    (hstep : p.ε / (4 * modelScale p) ≤
      ‖OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state) - z‖ ^ 2) :
    let z' := OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state)
    p.ε * Real.sqrt p.ε / (96 * Real.sqrt (modelScale p)) ≤ envelope f z - envelope f z' := by
  have hh := outer_large_step_descent H hv z state hw hstep
  have hb := cubic_decrease_threshold (model_scale_positive hv) hv.2.2.2.2.2.1 (norm_nonneg _) hstep
  dsimp only at hh ⊢
  linarith

lemma envelope_initial_gap {p : Params} {f : Space p → ℝ} (H : Assumptions p f)
    (hv : spec.valid p) (z : p.E) : envelope f p.x0 - envelope f z ≤ p.Δ := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hm := primal_min H.toRegularity hv p.x0 p.x0
  change envelope f p.x0 ≤ value f p.x0 + p.L * ‖p.x0 - p.x0‖ ^ 2 at hm
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hm
  have he : value f (primal f z) ≤ envelope f z := by
    change value f (primal f z) ≤ value f (primal f z) + p.L * ‖primal f z - z‖ ^ 2
    have hh := mul_nonneg hL.le (sq_nonneg ‖primal f z - z‖)
    linarith
  have hh := H.initial_gap (primal f z)
  linarith

end LongTails.Proofs.ConstrainedSaddleOuter
