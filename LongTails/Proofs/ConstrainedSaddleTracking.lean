import LongTails.Proofs.ConstrainedSaddleInner

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ConstrainedSaddleTracking

open LongTails.Setups.ConstrainedMinimaxSecondOrder
open LongTails.Algorithms.ConstrainedSaddleCubic
open ConstrainedMinimaxEnvelope ConstrainedSaddleInner

lemma refinement_steps_positive (p : Params) : 0 < refinementSteps p := by
  unfold refinementSteps
  omega

lemma refinement_geometric {p : Params} (hv : spec.valid p) :
    (1 / 2 : ℝ) ^ refinementSteps p ≤ 1 / (33 + 512 * p.L * p.μ / (p.ρ * p.ε)) := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hA : 0 < 33 + 512 * p.L * p.μ / (p.ρ * p.ε) := by positivity
  have hn : 2 * Real.log (33 + 512 * p.L * p.μ / (p.ρ * p.ε)) ≤ refinementSteps p := by
    have hh := Nat.le_ceil (2 * Real.log (33 + 512 * p.L * p.μ / (p.ρ * p.ε)))
    unfold refinementSteps
    push_cast
    linarith
  have hh := OracleTemplate.PLMinimax.geometric_log_bound (C := 2) (by norm_num) hA _ hn
  norm_num at hh ⊢
  exact hh

lemma refinement_power_small {p : Params} (hv : spec.valid p) :
    (1 / 2 : ℝ) ^ refinementSteps p ≤ 1 / 32 := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2.1
  apply (refinement_geometric hv).trans
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 32)
  have hh : 0 ≤ 512 * p.L * p.μ / (p.ρ * p.ε) := by positivity
  linarith

lemma refinement_residual_tuning {p : Params} (hv : spec.valid p) :
    p.μ ^ 2 / p.ρ * (1 / 2 : ℝ) ^ refinementSteps p ≤ residualTolerance p := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hε := hv.2.2.2.2.2.1
  have hk : 1 ≤ p.L / p.μ := (le_div_iff₀ hμ).mpr (by simpa using hv.2.1)
  have hk0 : 0 ≤ p.L / p.μ := by positivity
  have hs : Real.sqrt (p.L / p.μ) ≤ p.L / p.μ := by
    nlinarith [Real.sq_sqrt hk0, Real.sqrt_nonneg (p.L / p.μ)]
  apply le_min
  · have hh := mul_le_mul_of_nonneg_left (refinement_power_small hv)
      (by positivity : 0 ≤ p.μ ^ 2 / p.ρ)
    convert hh using 1
    ring
  · have hA : 0 < 33 + 512 * p.L * p.μ / (p.ρ * p.ε) := by positivity
    have hh := mul_le_mul_of_nonneg_left (refinement_geometric hv)
      (by positivity : 0 ≤ p.μ ^ 2 / p.ρ)
    apply hh.trans
    have hsmall : p.μ ^ 2 / p.ρ * (1 / (33 + 512 * p.L * p.μ / (p.ρ * p.ε))) ≤
        p.ε * p.μ / (512 * p.L) := by
      apply (le_div_iff₀ (by positivity : 0 < 512 * p.L)).mpr
      field_simp
      nlinarith [sq_nonneg p.μ]
    apply hsmall.trans
    have hden : 0 < 128 * (p.L / p.μ + 2 * Real.sqrt (p.L / p.μ) + 1) := by positivity
    apply (le_div_iff₀ hden).mpr
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 512 * p.L)).mpr
    have hc : p.μ * (p.L / p.μ + 2 * Real.sqrt (p.L / p.μ) + 1) ≤ 4 * p.L := by
      have hh := mul_le_mul_of_nonneg_left (show p.L / p.μ + 2 * Real.sqrt (p.L / p.μ) + 1 ≤
        4 * (p.L / p.μ) by linarith) hμ.le
      field_simp at hh ⊢
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hc hε.le
    nlinarith

lemma refinement_accuracy {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (state : Space p × Space p)
    (hw : ‖state.1 - WithLp.toLp 2 (primal f z, dual f z)‖ ≤ 3 * p.μ / (32 * p.ρ)) :
    let out := OracleTemplate.QueryPlan.eval (jet f) (refinePlan z (refinementSteps p) state)
    ‖out.1 - WithLp.toLp 2 (primal f z, dual f z)‖ ≤ p.μ / (32 * p.ρ) ∧
      ‖out.2‖ ≤ residualTolerance p := by
  dsimp only
  constructor
  · have he := refine_plan_error H hv z (refinementSteps p) state hw
    have hh := mul_le_mul (refinement_power_small hv) hw (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 32)
    apply he.trans (hh.trans _)
    have hμ := hv.1
    have hρ := hv.2.2.1
    have hr : 0 ≤ p.μ / (32 * p.ρ) := by positivity
    ring_nf at hr ⊢
    linarith
  · exact (refine_plan_residual_uniform H hv z (refinementSteps p) state
      (refinement_steps_positive p) hw).trans (refinement_residual_tuning hv)

lemma segment_length_positive {p : Params} (hv : spec.valid p) : 0 < segmentLength p := by
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ := hv.1
  have hρ := hv.2.2.1
  unfold segmentLength
  positivity

lemma saddle_center_distance {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z z' : p.E) :
    ‖WithLp.toLp 2 (primal f z, dual f z) - WithLp.toLp 2 (primal f z', dual f z')‖ ≤
      Real.sqrt (4 + p.L / p.μ) * ‖z - z'‖ := by
  have he := saddle_center_distance_sq H hv z z'
  have hn := WithLp.prod_norm_sq_eq_of_L2
    (WithLp.toLp 2 (primal f z, dual f z) - WithLp.toLp 2 (primal f z', dual f z'))
  change ‖WithLp.toLp 2 (primal f z, dual f z) - WithLp.toLp 2 (primal f z', dual f z')‖ ^ 2 =
    ‖primal f z - primal f z'‖ ^ 2 + ‖dual f z - dual f z'‖ ^ 2 at hn
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ := hv.1
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 4 + p.L / p.μ)
  have hb : (Real.sqrt (4 + p.L / p.μ) * ‖z - z'‖) ^ 2 =
      (4 + p.L / p.μ) * ‖z - z'‖ ^ 2 := by rw [mul_pow, hs]
  nlinarith [mul_nonneg (Real.sqrt_nonneg (4 + p.L / p.μ)) (norm_nonneg (z - z'))]

lemma warm_start {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z z' : p.E) (w : Space p)
    (hw : ‖w - WithLp.toLp 2 (primal f z, dual f z)‖ ≤ p.μ / (32 * p.ρ))
    (hz : ‖z - z'‖ ≤ segmentLength p) :
    ‖w - WithLp.toLp 2 (primal f z', dual f z')‖ ≤ 3 * p.μ / (32 * p.ρ) := by
  have hd := saddle_center_distance H hv z z'
  have hm := mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg (4 + p.L / p.μ))
  have hL : 0 < p.L := hv.1.trans_le hv.2.1
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hs : 0 < Real.sqrt (4 + p.L / p.μ) := by positivity
  have he : Real.sqrt (4 + p.L / p.μ) * segmentLength p = p.μ / (16 * p.ρ) := by
    unfold segmentLength
    field_simp
  rw [he] at hm
  have ht := norm_sub_le_norm_sub_add_norm_sub w
    (WithLp.toLp 2 (primal f z, dual f z)) (WithLp.toLp 2 (primal f z', dual f z'))
  have hh := hd.trans hm
  calc
    _ ≤ p.μ / (32 * p.ρ) + p.μ / (16 * p.ρ) := ht.trans (add_le_add hw hh)
    _ = _ := by ring

lemma segment_count_positive {p : Params} (z z' : p.E) : 0 < segmentCount z z' := by
  unfold segmentCount
  omega

lemma segment_count_bound {p : Params} (hv : spec.valid p) (z z' : p.E) :
    (segmentCount z z' : ℝ) ≤ 1 + ‖z' - z‖ / segmentLength p := by
  have ha : 0 ≤ ‖z' - z‖ / segmentLength p := div_nonneg (norm_nonneg _) (segment_length_positive hv).le
  have hh := (Nat.ceil_lt_add_one ha).le
  unfold segmentCount
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · linarith
  · linarith

lemma path_center_step {p : Params} (z z' : p.E) (m i : ℕ) (hm : 0 < m) :
    ‖pathCenter z z' m (i + 1) - pathCenter z z' m i‖ = ‖z' - z‖ / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have he : pathCenter z z' m (i + 1) - pathCenter z z' m i =
      (1 / (m : ℝ)) • (z' - z) := by
    unfold pathCenter
    push_cast
    module
  rw [he, norm_smul, Real.norm_of_nonneg (by positivity)]
  ring

lemma path_center_step_bound {p : Params} (hv : spec.valid p) (z z' : p.E) (i : ℕ) :
    ‖pathCenter z z' (segmentCount z z') i - pathCenter z z' (segmentCount z z') (i + 1)‖ ≤
      segmentLength p := by
  rw [norm_sub_rev, path_center_step z z' _ i (segment_count_positive z z')]
  have hm : (0 : ℝ) < segmentCount z z' := by exact_mod_cast segment_count_positive z z'
  apply (div_le_iff₀ hm).mpr
  have hh := Nat.le_ceil (‖z' - z‖ / segmentLength p)
  have hc : (⌈‖z' - z‖ / segmentLength p⌉₊ : ℝ) ≤ segmentCount z z' := by
    exact_mod_cast (le_max_right 1 ⌈‖z' - z‖ / segmentLength p⌉₊)
  have he := (div_le_iff₀ (segment_length_positive hv)).mp (hh.trans hc)
  nlinarith

lemma path_center_zero {p : Params} (z z' : p.E) (m : ℕ) : pathCenter z z' m 0 = z := by
  simp [pathCenter]

lemma path_center_end {p : Params} (z z' : p.E) :
    pathCenter z z' (segmentCount z z') (segmentCount z z') = z' := by
  have hm : (segmentCount z z' : ℝ) ≠ 0 := by exact_mod_cast (segment_count_positive z z').ne'
  simp [pathCenter, hm]

def TrackingInvariant {p : Params} (f : Space p → ℝ) (z : p.E)
    (state : Space p × Space p) : Prop :=
  ‖state.1 - WithLp.toLp 2 (primal f z, dual f z)‖ ≤ p.μ / (32 * p.ρ) ∧
    ‖state.2‖ ≤ residualTolerance p ∧
    primal (ConstrainedSaddlePerturbation.tilt f state.1 state.2) z = state.1.fst ∧
    dual (ConstrainedSaddlePerturbation.tilt f state.1 state.2) z = state.1.snd

lemma refinement_invariant {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (state : Space p × Space p)
    (hw : ‖state.1 - WithLp.toLp 2 (primal f z, dual f z)‖ ≤ 3 * p.μ / (32 * p.ρ)) :
    TrackingInvariant f z (OracleTemplate.QueryPlan.eval (jet f)
      (refinePlan z (refinementSteps p) state)) := by
  have ha := refinement_accuracy H hv z state hw
  exact ⟨ha.1, ha.2, refine_plan_certificate H hv z _ state (refinement_steps_positive p)⟩

lemma track_plan_invariant {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z z' : p.E) (i n : ℕ) (state : Space p × Space p)
    (hw : TrackingInvariant f (pathCenter z z' (segmentCount z z') i) state) :
    TrackingInvariant f (pathCenter z z' (segmentCount z z') (i + n))
      (OracleTemplate.QueryPlan.eval (jet f) (trackPlan z z' (segmentCount z z') i n state)) := by
  induction n generalizing i state with
  | zero => simpa [trackPlan, OracleTemplate.QueryPlan.eval] using hw
  | succ n ih =>
    have hb := warm_start H hv (pathCenter z z' (segmentCount z z') i)
      (pathCenter z z' (segmentCount z z') (i + 1)) state.1 hw.1
      (path_center_step_bound hv z z' i)
    have hr := refinement_invariant H hv _ state hb
    rw [trackPlan, OracleTemplate.QueryPlan.eval_bind]
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using ih (i + 1) _ hr

lemma tracking_complete {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z z' : p.E) (state : Space p × Space p)
    (hw : TrackingInvariant f z state) :
    TrackingInvariant f z' (OracleTemplate.QueryPlan.eval (jet f)
      (trackPlan z z' (segmentCount z z') 0 (segmentCount z z') state)) := by
  have hh := track_plan_invariant H hv z z' 0 (segmentCount z z') state
    (by simpa only [path_center_zero] using hw)
  simpa only [Nat.zero_add, path_center_end] using hh

lemma startup_invariant {p : Params} {f : Space p → ℝ} (H : Assumptions p f)
    (hv : spec.valid p) :
    let w := OracleTemplate.QueryPlan.eval (jet f)
      (initialPlan p.x0 (startupSteps p) (WithLp.toLp 2 (p.x0, p.y0)))
    TrackingInvariant f p.x0 (OracleTemplate.QueryPlan.eval (jet f)
      (refinePlan p.x0 (refinementSteps p) (w, 0))) := by
  dsimp only
  apply refinement_invariant H.toRegularity hv
  have hh := startup_accuracy H hv
  have hμ := hv.1
  have hρ := hv.2.2.1
  have hr : 0 ≤ p.μ / (32 * p.ρ) := by positivity
  apply hh.trans
  ring_nf at hr ⊢
  linarith

lemma tracked_output_gradient {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (z : p.E) (state : Space p × Space p)
    (hw : TrackingInvariant f z state) :
    ‖gradient (value f) state.1.fst‖ ≤ ‖gradient (envelope f) z‖ +
      (p.L / p.μ + 2 * Real.sqrt (p.L / p.μ) + 1) * ‖state.2‖ := by
  let q := ConstrainedSaddlePerturbation.tilt f state.1 state.2
  have Q : Regularity p q := ConstrainedSaddlePerturbation.tilt_regularity H state.1 state.2
  have hp : primal q z = state.1.fst := hw.2.2.1
  have hg : gradient (value q) state.1.fst = gradient (envelope q) z := by
    have hs := primal_stationary Q hv z
    rw [hp, add_eq_zero_iff_eq_neg] at hs
    rw [(envelope_hasGradient Q hv z).gradient, hp, hs]
    module
  have h1 := ConstrainedSaddlePerturbation.tilt_value_gradient H hv state.1 state.2 state.1.fst
  change ‖gradient (value f) state.1.fst - gradient (value q) state.1.fst‖ ≤ _ at h1
  rw [hg] at h1
  have h2 := ConstrainedSaddlePerturbation.tilt_envelope_gradient H hv state.1 state.2 z
  change ‖gradient (envelope f) z - gradient (envelope q) z‖ ≤ _ at h2
  rw [norm_sub_rev] at h2
  have ht := norm_sub_le_norm_sub_add_norm_sub (gradient (value f) state.1.fst)
    (gradient (envelope q) z) (gradient (envelope f) z)
  have hn := norm_le_norm_add_norm_sub' (gradient (value f) state.1.fst) (gradient (envelope f) z)
  nlinarith

end LongTails.Proofs.ConstrainedSaddleTracking
