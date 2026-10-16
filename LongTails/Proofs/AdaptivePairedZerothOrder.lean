import LongTails.Algorithms.AdaptivePairedZerothOrder
import LongTails.Proofs.ClippedTwoPointConvergence
import LongTails.Proofs.ClippedBatchConcentration
import LongTails.Proofs.ClippedSelection
import LongTails.Proofs.LocalPopulationModels

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.AdaptivePairedZerothOrder

open LongTails.Setups.AdaptivePairedZerothOrder
open LongTails.Algorithms.AdaptivePairedZerothOrder
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma direction_samples (p : Public) :
    let : NeZero p.d := ⟨p.dimension_pos.ne'⟩
    IID (fun i (seed : ℕ → Direction p) => seed i)
      (OracleTemplate.ZerothOrder.sphereLaw (Point p.d) : Measure _)
      (directionLaw p : Measure _) := by
  let : NeZero p.d := ⟨p.dimension_pos.ne'⟩
  change IID _ _ (Measure.infinitePi (fun _ : ℕ =>
    (OracleTemplate.ZerothOrder.sphereLaw (Point p.d) : Measure (Direction p))))
  refine ⟨fun i => measurable_pi_apply i, ?_, ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  · intro i
    exact Measure.infinitePi_map_eval _ i

lemma first_directions_measurable (p : Public) (t : ℕ) (i : Fin (batch p t)) :
    Measurable (fun seed => firstDirections p seed t i) :=
  continuous_subtype_val.measurable.comp (measurable_pi_apply _)

lemma second_directions_measurable (p : Public) (t : ℕ) (i : Fin (batch p t)) :
    Measurable (fun seed => secondDirections p seed t i) :=
  continuous_subtype_val.measurable.comp (measurable_pi_apply _)

lemma actual_value_cost (p : Public) (hN : 0 < p.N) (hT : 0 < p.T) :
    2 * p.T + LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls (batch p) p.N ≤
      6 * p.T + 4 * p.N := by
  exact PairedOracleExecution.adaptive_selection_cost hN hT

lemma execute_output {Ω : Type} [MeasurableSpace Ω] (p : Public)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → ℝ)
    (seed : ℕ → Direction p) (ξ : ℕ → Ω) (hN : 0 < p.N) (hT : 0 < p.T) :
    OracleTemplate.execute
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) w => g x w }
      (algorithm p) (fun _ => 6 * p.T + 4 * p.N) seed (fun k => ξ (k / 2)) =
        output p seed g ξ := by
  exact ClippedTwoPointExecution.adaptive_execute (directionLaw p) P p.d
    (clipRadius p) (clipRadius p) (smoothRadius p) (nonsmoothRadius p)
    (regularization p) (validationClip p) p.project (p.x0, p.x0) (batch p)
    (firstDirections p) (secondDirections p) p.N p.T (6 * p.T + 4 * p.N) g seed ξ
    (actual_value_cost p hN hT)

lemma actual_output_law {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (p : Public) (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω) (hξ : ∀ k, Measurable (ξ k))
    (g : Point p.d → Ω → ℝ) (hg : Measurable (fun z : Point p.d × Ω => g z.1 z.2))
    (hp : Continuous p.project) (hN : 0 < p.N) (hT : 0 < p.T) :
    let paired := P.map (fun z n => ξ (n / 2) z)
    let oracle : OracleTemplate.Oracle (Point p.d) ℝ :=
      { Seed := fun _ => Ω, law := paired, answer := fun _ (_, x) w => g x w }
    ((directionLaw p : Measure (ℕ → Direction p)).prod (paired : Measure (ℕ → Ω))).map
      (fun z : (ℕ → Direction p) × (ℕ → Ω) => OracleTemplate.execute oracle (algorithm p) (fun _ => 6 * p.T + 4 * p.N) z.1 z.2) =
      ((directionLaw p : Measure (ℕ → Direction p)).prod (P : Measure Ξ)).map
        (fun z => output p z.1 g (fun j => ξ j z.2)) := by
  exact PairedOracleExecution.adaptive_execution_output_law (directionLaw p) P ξ hξ p.d
    (clipRadius p) (clipRadius p) (smoothRadius p) (nonsmoothRadius p)
    (regularization p) (validationClip p) hp (p.x0, p.x0) (batch p)
    (firstDirections p) (secondDirections p) (first_directions_measurable p)
    (second_directions_measurable p) g hg p.N p.T (6 * p.T + 4 * p.N)
    (actual_value_cost p hN hT)

lemma output_feasible {Ω : Type*} (p : Public) (hQ : Convex ℝ p.Q)
    (hp : ∀ x, p.project x ∈ p.Q) (hx : p.x0 ∈ p.Q)
    (seed : ℕ → Direction p) (g : Point p.d → Ω → ℝ) (ξ : ℕ → Ω) :
    output p seed g ξ ∈ p.Q := by
  exact ClippedTwoPointExecution.adaptive_output_mem hQ hp hx hx p.d
    (clipRadius p) (clipRadius p) (smoothRadius p) (nonsmoothRadius p)
    (regularization p) (validationClip p) (batch p) (firstDirections p seed)
    (secondDirections p seed) g ξ 0 p.N p.T

lemma public_tuning_positive (p : Public) (hD : 0 < p.D) (hγ : 0 < p.γmax)
    (hε : 0 < p.ε) (hell : 0 < p.ell) (hN : 0 < p.N) (hT : 0 < p.T) :
    0 < weightTotal p ∧ 0 < scale p ∧ 0 < clipRadius p ∧ 0 < regularization p ∧
      0 < validationClip p ∧ 0 < smoothRadius p ∧ 0 < nonsmoothRadius p := by
  have hd : (0 : ℝ) < p.d := by exact_mod_cast p.dimension_pos
  have hn : (0 : ℝ) < p.N := by exact_mod_cast hN
  have ht : (0 : ℝ) < p.T := by exact_mod_cast hT
  dsimp [weightTotal, scale, clipRadius, regularization, validationClip, smoothRadius, nonsmoothRadius]
  exact ⟨by positivity, by positivity, by positivity, by positivity,
    by positivity, by positivity, by positivity⟩

lemma scale_square_identity (p : Public) (hell : 0 ≤ p.ell) :
    scale p ^ 2 = p.ε ^ 2 * p.T / (2 ^ 48 * p.D ^ 2 * (p.d + p.ell)) := by
  unfold scale
  simp only [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg p.T),
    Real.sq_sqrt (add_nonneg (Nat.cast_nonneg p.d) hell)]
  norm_num

lemma scale_lower_bound (p : Public) {M2 : ℝ} (hD : 0 < p.D) (hε : 0 < p.ε)
    (hell : 0 < p.ell)
    (hT : 2 ^ 48 * (p.d + p.ell) * (1 + M2 ^ 2 * p.D ^ 2 / p.ε ^ 2) + p.N ≤ (p.T : ℝ)) :
    M2 ^ 2 + (p.ε / p.D) ^ 2 ≤ scale p ^ 2 := by
  let K : ℝ := 2 ^ 48 * (p.d + p.ell)
  have hK : 0 < K := by dsimp [K]; positivity
  have hbase : K * (1 + M2 ^ 2 * p.D ^ 2 / p.ε ^ 2) ≤ (p.T : ℝ) := by
    dsimp [K]
    linarith only [hT, Nat.cast_nonneg (α := ℝ) p.N]
  have he := scale_square_identity p hell.le
  calc
    _ = (p.ε ^ 2 / (K * p.D ^ 2)) * (K * (1 + M2 ^ 2 * p.D ^ 2 / p.ε ^ 2)) := by
      field_simp [hK.ne', hD.ne', hε.ne']
      ring
    _ ≤ (p.ε ^ 2 / (K * p.D ^ 2)) * p.T := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = scale p ^ 2 := by
      rw [he]
      dsimp [K]
      ring

lemma corruption_scale_bound (p : Public) {M2 Δ γ : ℝ}
    (hD : 0 < p.D) (hε : 0 < p.ε) (hΔ : 0 ≤ Δ) (hγ : 0 < γ)
    (hscale : M2 ^ 2 + (p.ε / p.D) ^ 2 ≤ scale p ^ 2)
    (hnoise : Real.sqrt p.d * Δ / γ ≤ p.ε / (16384 * p.D)) :
    M2 ^ 2 + p.d * (Δ / γ) ^ 2 ≤ 2 * scale p ^ 2 := by
  have hn : Real.sqrt p.d * (Δ / γ) ≤ p.ε / p.D := by
    calc
      _ = Real.sqrt p.d * Δ / γ := by ring
      _ ≤ p.ε / (16384 * p.D) := hnoise
      _ ≤ p.ε / p.D := div_le_div_of_nonneg_left hε.le hD (by linarith)
  have hs : (p.d : ℝ) * (Δ / γ) ^ 2 ≤ (p.ε / p.D) ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg p.d)] using
      pow_le_pow_left₀ (show 0 ≤ Real.sqrt p.d * (Δ / γ) by positivity) hn 2
  linarith only [hscale, hs, sq_nonneg (scale p)]

lemma record_radius_identity (p : Public) (hD : 0 < p.D) (hε : 0 < p.ε)
    (hell : 0 < p.ell) (hT : 0 < p.T) :
    8192 * Real.sqrt ((scale p ^ 2 * weightTotal p ^ 2 / p.T) * (p.d + p.ell)) =
      p.ε * weightTotal p / (2048 * p.D) := by
  have ht : (0 : ℝ) < p.T := by exact_mod_cast hT
  have hde : (0 : ℝ) < p.d + p.ell := by positivity
  have hA : 0 ≤ weightTotal p := by unfold weightTotal; positivity
  have hr : Real.sqrt ((scale p ^ 2 * weightTotal p ^ 2 / p.T) * (p.d + p.ell)) =
      p.ε * weightTotal p / (16777216 * p.D) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), scale_square_identity p hell.le]
    field_simp [hD.ne', ht.ne', hde.ne']
    ring
  rw [hr]
  ring

lemma batch_schedule_bounds (p : Public) (hN : 0 < p.N) (hT : 0 < p.T) :
    (∀ t, 0 < batch p t) ∧
    (∀ t : Fin p.N, |(t + 1 : ℝ) / batch p t| ≤ weightTotal p / p.T) ∧
    (∑ t : Fin p.N, (batch p t : ℝ) * ((t + 1 : ℝ) / batch p t) ^ 2) ≤
      weightTotal p ^ 2 / p.T := by
  have ht : (0 : ℝ) < p.T := by exact_mod_cast hT
  have hn : (0 : ℝ) < p.N := by exact_mod_cast hN
  have ha : 0 < weightTotal p := by dsimp [weightTotal]; positivity
  have hsum : (∑ t : Fin p.N, (t + 1 : ℝ)) = weightTotal p := by
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (t + 1 : ℝ))]
    exact PairedOracleExecution.accelerated_weights_sum p.N
  refine ⟨fun t => (WeightedOracleBlocks.batch_size_bounds ht ha (by positivity)).1, ?_, ?_⟩
  · intro t
    have hw := WeightedOracleBlocks.batch_weight_bounds ht ha (show 0 < (t + 1 : ℝ) by positivity)
    change |LongTails.Algorithms.ClippedTwoPoint.batchWeight p.T (weightTotal p) (t + 1)| ≤ _
    rw [abs_of_pos hw.1]
    exact hw.2
  · exact WeightedOracleBlocks.batch_total_weight_square ht ha (fun t => by positivity) hsum

lemma solver_tuning_error_bound {ε A D R β C : ℝ} (hε : 0 < ε) (hA : 0 < A)
    (hD : 0 < D) (hR : 0 ≤ R) (hβ : 0 ≤ β)
    (hRb : R ≤ ε * A / (1024 * D)) (hβb : β ≤ ε / (8192 * D))
    (hCb : C ≤ ε * A / 8192) :
    (ε * A / (64 * D ^ 2)) * D ^ 2 / 2 +
      (R + A * β) ^ 2 / (ε * A / (64 * D ^ 2)) + C + A * β * D ≤ ε * A / 64 := by
  have hh : 0 < ε * A / (64 * D ^ 2) := by positivity
  have hsum : R + A * β ≤ ε * A / (512 * D) := by
    have hb := mul_le_mul_of_nonneg_left hβb hA.le
    have he : ε * A / (1024 * D) + A * (ε / (8192 * D)) ≤ ε * A / (512 * D) := by
      field_simp
      nlinarith
    linarith
  have he := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : 0 ≤ R + A * β) hsum 2) hh.le
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβb hA.le) hD.le
  calc
    _ ≤ (ε * A / (64 * D ^ 2)) * D ^ 2 / 2 +
        (ε * A / (512 * D)) ^ 2 / (ε * A / (64 * D ^ 2)) +
          ε * A / 8192 + A * (ε / (8192 * D)) * D := by linarith only [he, hb, hCb]
    _ ≤ ε * A / 64 := by
      field_simp
      nlinarith

lemma comparator_tuning_bound (p : Public) (hD : 0 < p.D) (hε : 0 < p.ε)
    (hell : 0 < p.ell) (hN : 0 < p.N) (hT : 0 < p.T) :
    1280 * (p.D * Real.sqrt (scale p ^ 2 * weightTotal p ^ 2 / p.T)) * Real.sqrt p.ell ≤
      p.ε * weightTotal p / 8192 := by
  have ht : (0 : ℝ) < p.T := by exact_mod_cast hT
  have hn : (0 : ℝ) < p.N := by exact_mod_cast hN
  have ha : 0 < weightTotal p := by dsimp [weightTotal]; positivity
  have hk : 0 ≤ scale p ^ 2 * weightTotal p ^ 2 / p.T := by positivity
  have hr := record_radius_identity p hD hε hell hT
  rw [Real.sqrt_mul hk] at hr
  have hs : Real.sqrt p.ell ≤ Real.sqrt ((p.d : ℝ) + p.ell) :=
    Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) p.d])
  calc
    _ ≤ 1280 * (p.D * Real.sqrt (scale p ^ 2 * weightTotal p ^ 2 / p.T)) *
        Real.sqrt ((p.d : ℝ) + p.ell) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (5 * p.D / 32) * (8192 * (Real.sqrt (scale p ^ 2 * weightTotal p ^ 2 / p.T) *
        Real.sqrt ((p.d : ℝ) + p.ell))) := by ring
    _ = 5 * p.ε * weightTotal p / 65536 := by rw [hr]; field_simp; ring
    _ ≤ p.ε * weightTotal p / 8192 := by nlinarith [mul_pos hε ha]

lemma smooth_horizon_tuning {L D ε γ : ℝ} {N : ℕ}
    (hL : 0 ≤ L) (hD : 0 < D) (hε : 0 < ε) (hN : 0 < N)
    (hγ : 0 ≤ γ) (hγb : γ ≤ D / N)
    (hbudget : 32 * (1 + Real.sqrt (L * D ^ 2 / ε)) ≤ (N : ℝ)) :
    4 * L ≤ ε * ((N : ℝ) * (N + 1) / 2) / (64 * D ^ 2) ∧
      L * γ ^ 2 / 2 ≤ ε / 2048 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ L * D ^ 2 / ε := by positivity
  have hs := Real.sq_sqrt hx
  have hsqrt := Real.sqrt_nonneg (L * D ^ 2 / ε)
  have hr : L * D ^ 2 / ε ≤ (N : ℝ) ^ 2 / 1024 := by nlinarith
  have hb := (div_le_iff₀ hε).mp hr
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 64 * D ^ 2)).mpr
    nlinarith
  · have hsq := pow_le_pow_left₀ hγ hγb 2
    have hmul := mul_le_mul_of_nonneg_left hsq hL
    have he : L * (D / (N : ℝ)) ^ 2 / 2 ≤ ε / 2048 := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      rw [div_pow, ← mul_div_assoc]
      apply (div_le_iff₀ (sq_pos_of_pos hn)).mpr
      nlinarith
    linarith

lemma clipping_bias_tuning_bound (p : Public) {M2 Δ γ : ℝ}
    (hD : 0 < p.D) (hε : 0 < p.ε) (hell : 0 < p.ell) (hT : 0 < p.T)
    (hvar : M2 ^ 2 ≤ scale p ^ 2)
    (hcorrupt : Real.sqrt p.d * (Δ / γ) ≤ p.ε / (16384 * p.D)) :
    15 * M2 ^ 2 / (Real.sqrt p.d * clipRadius p) + Real.sqrt p.d * (Δ / γ) ≤
      p.ε / (8192 * p.D) := by
  have hd : (0 : ℝ) < p.d := by exact_mod_cast p.dimension_pos
  have ht : (0 : ℝ) < p.T := by exact_mod_cast hT
  have hsum : 0 < (p.d : ℝ) + p.ell := by positivity
  have hsd := (Real.sqrt_pos.mpr hd).ne'
  have hst := (Real.sqrt_pos.mpr ht).ne'
  have hsl := (Real.sqrt_pos.mpr hell).ne'
  have hss := (Real.sqrt_pos.mpr hsum).ne'
  have hclip : 0 < clipRadius p := by dsimp [clipRadius, scale]; positivity
  have hratio : scale p ^ 2 / (Real.sqrt p.d * clipRadius p) =
      p.ε * Real.sqrt p.ell / (2 ^ 24 * p.D * Real.sqrt ((p.d : ℝ) + p.ell)) := by
    dsimp [clipRadius, scale]
    rw [Real.sqrt_div ht.le, Real.sqrt_mul hd.le]
    field_simp
    ring
  have hs : Real.sqrt p.ell ≤ Real.sqrt ((p.d : ℝ) + p.ell) :=
    Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) p.d])
  have hratbound : scale p ^ 2 / (Real.sqrt p.d * clipRadius p) ≤ p.ε / (2 ^ 24 * p.D) := by
    rw [hratio]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ p.ε * (2 ^ 24 * p.D) by positivity)]
  have hnoise := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvar (by norm_num : (0 : ℝ) ≤ 15))
    (show 0 ≤ Real.sqrt p.d * clipRadius p by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hratbound (by norm_num : (0 : ℝ) ≤ 15)
  have hsum' : 15 * (p.ε / (2 ^ 24 * p.D)) + p.ε / (16384 * p.D) ≤ p.ε / (8192 * p.D) := by
    field_simp
    nlinarith
  rw [← mul_div_assoc] at hscaled
  linarith

lemma public_solver_error_bound (p : Public) {M2 Δ γ : ℝ}
    (hD : 0 < p.D) (hε : 0 < p.ε) (hell : 0 < p.ell) (hN : 0 < p.N) (hT : 0 < p.T)
    (hΔ : 0 ≤ Δ) (hγ : 0 < γ) (hvar : M2 ^ 2 ≤ scale p ^ 2)
    (hcorrupt : Real.sqrt p.d * (Δ / γ) ≤ p.ε / (16384 * p.D)) :
    let R := 8192 * Real.sqrt ((scale p ^ 2 * weightTotal p ^ 2 / p.T) * (p.d + p.ell))
    let β := 15 * M2 ^ 2 / (Real.sqrt p.d * clipRadius p) + Real.sqrt p.d * (Δ / γ)
    let C := 1280 * (p.D * Real.sqrt (scale p ^ 2 * weightTotal p ^ 2 / p.T)) * Real.sqrt p.ell
    regularization p * p.D ^ 2 / 2 + (R + weightTotal p * β) ^ 2 / regularization p +
      C + weightTotal p * β * p.D ≤ p.ε * weightTotal p / 64 := by
  have hn : (0 : ℝ) < p.N := by exact_mod_cast hN
  have ht : (0 : ℝ) < p.T := by exact_mod_cast hT
  have hd : (0 : ℝ) < p.d := by exact_mod_cast p.dimension_pos
  have ha : 0 < weightTotal p := by dsimp [weightTotal]; positivity
  have hclip : 0 < clipRadius p := by dsimp [clipRadius, scale]; positivity
  apply solver_tuning_error_bound hε ha hD (by positivity) (by positivity)
  · rw [record_radius_identity p hD hε hell hT]
    exact div_le_div_of_nonneg_left (mul_pos hε ha).le (by positivity) (by nlinarith)
  · exact clipping_bias_tuning_bound p hD hε hell hT hvar hcorrupt
  · exact comparator_tuning_bound p hD hε hell hN hT

lemma nonsmooth_horizon_tuning {M D ε r q : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hD : 0 < D) (hε : 0 < ε) (hr : 0 < r) (hq : 0 < q) (hN : 0 < N)
    (hbudget : 1024 * (1 + q * M * D / ε + q * D * Real.sqrt (M / (r * ε))) ≤ (N : ℝ)) :
    4 * (q ^ 2 * M / min r (q * D / N)) ≤ ε * ((N : ℝ) * (N + 1) / 2) / (64 * D ^ 2) ∧
      M * min r (q * D / N) ≤ ε / 1024 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ M / (r * ε) := by positivity
  have hs := Real.sq_sqrt hx
  have hsqrt := Real.sqrt_nonneg (M / (r * ε))
  have ht1 : 0 ≤ q * M * D / ε := by positivity
  have ht2 : 0 ≤ q * D * Real.sqrt (M / (r * ε)) := by positivity
  have hfirst : q * M * D / ε ≤ (N : ℝ) / 1024 := by linarith
  have hb := (div_le_iff₀ hε).mp hfirst
  have hsecond : 32 * q * D * Real.sqrt (M / (r * ε)) ≤ (N : ℝ) := by nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 32 * q * D * Real.sqrt (M / (r * ε))) hsecond 2
  have he : (32 * q * D * Real.sqrt (M / (r * ε))) ^ 2 = 1024 * q ^ 2 * D ^ 2 * (M / (r * ε)) := by
    simp only [mul_pow, hs]
    ring
  rw [he] at hsq
  have hratio : q ^ 2 * D ^ 2 * M / (r * ε) ≤ (N : ℝ) ^ 2 / 1024 := by
    rw [mul_div_assoc]
    nlinarith only [hsq]
  have hscale := (div_le_iff₀ (mul_pos hr hε)).mp hratio
  constructor
  · rcases le_total r (q * D / N) with hcase | hcase
    · rw [min_eq_left hcase, ← mul_div_assoc]
      apply (div_le_div_iff₀ hr (by positivity)).mpr
      nlinarith only [hscale, show 0 ≤ ε * r * (N : ℝ) ^ 2 by positivity,
        show 0 ≤ ε * r * (N : ℝ) by positivity]
    · rw [min_eq_right hcase, ← mul_div_assoc]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hmult := mul_le_mul_of_nonneg_left hb (show 0 ≤ q * D * (N : ℝ) by positivity)
      field_simp
      nlinarith
  · calc
      _ ≤ M * (q * D / N) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM
      _ ≤ ε / 1024 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hn).mpr
        nlinarith only [hb]

lemma winning_radius_corruption_bound (p : Public) {Δ : ℝ} (branch : Bool)
    (hD : 0 < p.D) (hε : 0 < p.ε) (hmax : 0 < p.γmax) (hN : 0 < p.N)
    (htol : Real.sqrt p.d * Δ / (if branch then smoothRadius p else nonsmoothRadius p) ≤
      p.ε / (16384 * p.D)) : Δ ≤ p.ε / 16384 := by
  have hd : (0 : ℝ) < p.d := by exact_mod_cast p.dimension_pos
  have hn : (1 : ℝ) ≤ p.N := by exact_mod_cast hN
  have hd1 : (1 : ℝ) ≤ p.d := by exact_mod_cast p.dimension_pos
  have hroot : 1 ≤ Real.sqrt (p.d : ℝ) := by simpa using Real.sqrt_le_sqrt hd1
  have hq : Real.sqrt (Real.sqrt (p.d : ℝ)) ≤ Real.sqrt (p.d : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hroot)
  have hrad : (if branch then smoothRadius p else nonsmoothRadius p) ≤ Real.sqrt p.d * p.D := by
    cases branch
    · dsimp [nonsmoothRadius]
      apply (min_le_right _ _).trans
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < p.N)).mpr
      have h1 := mul_le_mul_of_nonneg_right hq hD.le
      have h2 := mul_le_mul_of_nonneg_left hn (show 0 ≤ Real.sqrt p.d * p.D by positivity)
      nlinarith
    · dsimp [smoothRadius]
      apply (min_le_right _ _).trans
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < p.N)).mpr
      have h1 := mul_le_mul_of_nonneg_right hroot hD.le
      have h2 := mul_le_mul_of_nonneg_left hn (show 0 ≤ Real.sqrt p.d * p.D by positivity)
      nlinarith
  have hγ : 0 < if branch then smoothRadius p else nonsmoothRadius p := by
    cases branch <;> dsimp [smoothRadius, nonsmoothRadius] <;> positivity
  have hcross := (div_le_div_iff₀ hγ (by positivity : 0 < 16384 * p.D)).mp htol
  have hupper := mul_le_mul_of_nonneg_left hrad hε.le
  apply (mul_le_mul_iff_right₀ (show 0 < Real.sqrt p.d * p.D by positivity)).mp
  nlinarith only [hcross, hupper]

lemma selection_tuning_bounds (p : Public) {M2 Δ : ℝ}
    (hD : 0 < p.D) (hε : 0 < p.ε) (hell : 0 < p.ell) (hT : 0 < p.T)
    (hvar : M2 ^ 2 ≤ scale p ^ 2) (hbase : (p.ε / p.D) ^ 2 ≤ scale p ^ 2)
    (hΔ : Δ ≤ p.ε / 16384) :
    0 < scale p * p.D ∧ Δ ≤ (scale p * p.D) / 4 ∧
      p.D ^ 2 * M2 ^ 2 ≤ (scale p * p.D) ^ 2 ∧
      (p.T : ℝ) * (scale p * p.D) ^ 2 = validationClip p ^ 2 * p.ell ∧
      4097 * validationClip p * p.ell / p.T + 2 * Δ ≤ p.ε / 32 := by
  have ht : (0 : ℝ) < p.T := by exact_mod_cast hT
  have hd : (0 : ℝ) < p.d := by exact_mod_cast p.dimension_pos
  have hsc : 0 < scale p := by dsimp [scale]; positivity
  have hprod := mul_le_mul_of_nonneg_right hbase (sq_nonneg p.D)
  have he : (p.ε / p.D) ^ 2 * p.D ^ 2 = p.ε ^ 2 := by field_simp
  rw [he] at hprod
  have hH : p.ε ≤ scale p * p.D := by nlinarith [mul_pos hsc hD]
  have hmoment := mul_le_mul_of_nonneg_left hvar (sq_nonneg p.D)
  have hsT := (Real.sqrt_pos.mpr ht).ne'
  have hsL := (Real.sqrt_pos.mpr hell).ne'
  have hsDL := (Real.sqrt_pos.mpr (show 0 < (p.d : ℝ) + p.ell by positivity)).ne'
  have hid : validationClip p * p.ell / p.T =
      p.ε * Real.sqrt p.ell / (2 ^ 24 * Real.sqrt ((p.d : ℝ) + p.ell)) := by
    dsimp [validationClip, scale]
    rw [Real.sqrt_div ht.le]
    field_simp
    ring_nf
    simp only [Real.sq_sqrt ht.le, Real.sq_sqrt hell.le]
    ring
  have hsqrt : Real.sqrt p.ell ≤ Real.sqrt ((p.d : ℝ) + p.ell) :=
    Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) p.d])
  have hratio : validationClip p * p.ell / p.T ≤ p.ε / 2 ^ 24 := by
    rw [hid]
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2 ^ 24)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hε.le]
  refine ⟨mul_pos hsc hD, by linarith, by nlinarith only [hmoment], ?_, ?_⟩
  · dsimp [validationClip]
    simp only [mul_pow, Real.sq_sqrt (div_nonneg ht.le hell.le)]
    field_simp
  · have hh := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4097)
    rw [← mul_div_assoc, ← mul_assoc] at hh
    linarith

lemma execute_feasible {Ω : Type} [MeasurableSpace Ω] (p : Public)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → ℝ)
    (hQ : Convex ℝ p.Q) (hp : ∀ x, p.project x ∈ p.Q) (hx : p.x0 ∈ p.Q)
    (hN : 0 < p.N) (hT : 0 < p.T) (seed : ℕ → Direction p) (ξ : ℕ → Ω) :
    OracleTemplate.execute
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) w => g x w }
      (algorithm p) (fun _ => 6 * p.T + 4 * p.N) seed ξ ∈ p.Q := by
  exact LongTails.Proofs.ClippedTwoPointExecution.adaptive_execute_mem (directionLaw p) P
    (initial := (p.x0, p.x0)) hQ hp hx hx p.d (clipRadius p) (clipRadius p)
    (smoothRadius p) (nonsmoothRadius p) (regularization p) (validationClip p) (batch p)
    (firstDirections p) (secondDirections p) p.N p.T (6 * p.T + 4 * p.N) g seed ξ
    (actual_value_cost p hN hT)

lemma execute_measurable {Ω : Type} [MeasurableSpace Ω] (p : Public)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → ℝ)
    (hg : Measurable (fun z : Point p.d × Ω => g z.1 z.2))
    (hp : Continuous p.project) (hN : 0 < p.N) (hT : 0 < p.T) :
    Measurable (fun z : (ℕ → Direction p) × (ℕ → Ω) => OracleTemplate.execute
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) w => g x w }
      (algorithm p) (fun _ => 6 * p.T + 4 * p.N) z.1 z.2) := by
  have hm := LongTails.Proofs.ClippedTwoPointExecution.adaptive_plan_measurable p.d
    (clipRadius p) (clipRadius p) (smoothRadius p) (nonsmoothRadius p)
    (regularization p) (validationClip p) hp (p.x0, p.x0) (batch p)
    (fun z : (ℕ → Direction p) × (ℕ → Ω) => firstDirections p z.1)
    (fun z => secondDirections p z.1)
    (fun t i => (first_directions_measurable p t i).comp measurable_fst)
    (fun t i => (second_directions_measurable p t i).comp measurable_fst)
    g hg (fun j z => z.2 j) (fun j => (measurable_pi_apply j).comp measurable_snd) 0 p.N p.T
  convert hm using 1
  funext z
  exact OracleTemplate.QueryPlan.execute_sampledPlan_of_le (directionLaw p) P p.x0 p.x0
    (2 * p.T + LongTails.Algorithms.ClippedTwoPoint.dualSolverCalls (batch p) p.N)
    (6 * p.T + 4 * p.N)
    (fun seed => LongTails.Algorithms.ClippedTwoPoint.adaptiveSelectionPlan p.d
      (clipRadius p) (clipRadius p) (smoothRadius p) (nonsmoothRadius p)
      (regularization p) (validationClip p) p.project (p.x0, p.x0) (batch p)
      (firstDirections p seed) (secondDirections p seed) p.N p.T) g z.1 z.2
    (actual_value_cost p hN hT)

section PopulationModel

open Set OracleTemplate.ZerothOrder LocalPopulationModels LocalPopulationSmoothing
open scoped RealInnerProductSpace Pointwise

lemma winning_population_model (p : LongTails.Setups.AdaptivePairedZerothOrder.Params) [NeZero p.d] (hv : LongTails.Setups.AdaptivePairedZerothOrder.spec.valid p)
    (f : Point p.d → ℝ) (hc : ConvexOn ℝ (domain p.toPublic) f)
    (hlip : ∀ x ∈ domain p.toPublic, ∀ y ∈ domain p.toPublic,
      |f x - f y| ≤ p.M * ‖x - y‖)
    (hsmooth : p.smooth = true → ∃ grad : Point p.d → Point p.d,
      (∀ x ∈ interior (domain p.toPublic),
        HasGradientWithinAt f (grad x) (interior (domain p.toPublic)) x) ∧
      (∀ x ∈ interior (domain p.toPublic), ∀ y ∈ interior (domain p.toPublic),
        ‖grad x - grad y‖ ≤ p.L * ‖x - y‖)) :
    let γ := if p.smooth then smoothRadius p.toPublic else nonsmoothRadius p.toPublic
    ∃ population : Point p.d → ℝ, ∃ L : ℝ,
      Continuous population ∧ EqOn f population (domain p.toPublic) ∧
      0 ≤ L ∧ 4 * L ≤ regularization p.toPublic ∧
      (∀ x ∈ p.Q, ∀ y ∈ p.Q,
        ballSmooth population γ x + ⟪boundaryField population γ x, y - x⟫ ≤
          ballSmooth population γ y) ∧
      (∀ x ∈ p.Q, ∀ y ∈ p.Q, ballSmooth population γ y ≤
        ballSmooth population γ x + ⟪boundaryField population γ x, y - x⟫ +
          L / 2 * ‖y - x‖ ^ 2) ∧
      (∀ x ∈ p.Q, f x ≤ ballSmooth population γ x ∧
        ballSmooth population γ x ≤ f x + p.ε / 1024) := by
  intro γ
  rcases hv with ⟨hD, hmax, heps, hell, hN, hT, hM, hM2, hL, hdelta,
    hcompact, hQ, hx0, hdiam, hproj, hnearest, hbudget, hhorizon, hnoise⟩
  have hd : (0 : ℝ) < p.d := by exact_mod_cast p.dimension_pos
  have hγ : 0 < γ := by
    dsimp [γ, smoothRadius, nonsmoothRadius]
    split_ifs <;> positivity
  have hγmax : γ ≤ p.γmax := by
    dsimp [γ, smoothRadius, nonsmoothRadius]
    split_ifs <;> exact min_le_left _ _
  have hQC : p.Q ⊆ interior (domain p.toPublic) := by
    intro x hx
    exact thickening_ball_interior hx p.γmax (by simpa using hmax)
  have hLip : LipschitzOnWith ⟨p.M, hM⟩ f (domain p.toPublic) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq, dist_eq_norm]
    exact hlip x hx y hy
  obtain ⟨pop, hpop, heq, hmodels, hbias, hsmodel⟩ := local_extension_models hLip hc
    (thickening_compact hcompact p.γmax).isClosed ⟨p.x0, hQC hx0⟩ hQ hQC hγ
    (fun x hx => thickening_closed_ball hx hγmax)
  by_cases hb : p.smooth = true
  · have hγeq : γ = smoothRadius p.toPublic := by simp [γ, hb]
    obtain ⟨grad, hgrad, hgradlip⟩ := hsmooth hb
    obtain ⟨hupper, hsbi⟩ := hsmodel grad p.L hL hgrad hgradlip
    have htune := smooth_horizon_tuning hL hD heps hN hγ.le
      (show γ ≤ p.D / p.N by rw [hγeq]; exact min_le_right _ _)
      (by simpa [hb] using hhorizon)
    refine ⟨pop, p.L, hpop.continuous, heq, hL, htune.1, ?_, hupper, ?_⟩
    · exact fun x hx y hy => (hmodels x hx y hy).1
    · intro x hx
      exact ⟨(hbias x hx).1, (hsbi x hx).trans (by linarith [htune.2])⟩
  · have hbf : p.smooth = false := Bool.eq_false_iff.mpr hb
    have hγeq : γ = nonsmoothRadius p.toPublic := by simp [γ, hbf]
    have hd : (0 : ℝ) < p.d := by exact_mod_cast p.dimension_pos
    have htune := nonsmooth_horizon_tuning hM hD heps hmax
      (show 0 < Real.sqrt (Real.sqrt (p.d : ℝ)) by positivity) hN
      (by simpa [hbf] using hhorizon)
    rw [Real.sq_sqrt (Real.sqrt_nonneg (p.d : ℝ))] at htune
    refine ⟨pop, Real.sqrt p.d * p.M / γ, hpop.continuous, heq, by positivity, ?_,
      (fun x hx y hy => (hmodels x hx y hy).1),
      (fun x hx y hy => (hmodels x hx y hy).2), ?_⟩
    · simpa only [hγeq, nonsmoothRadius, regularization, weightTotal] using htune.1
    · intro x hx
      refine ⟨(hbias x hx).1, (hbias x hx).2.trans ?_⟩
      have ht : p.M * γ ≤ p.ε / 1024 := by simpa only [hγeq, nonsmoothRadius] using htune.2
      change f x + p.M * γ ≤ f x + p.ε / 1024
      linarith only [ht]


open scoped ContDiff
open LongTails.Algorithms.ClippedTwoPoint
lemma public_solver_confidence {Z : Type*} [MeasurableSpace Z]
    (p : LongTails.Setups.AdaptivePairedZerothOrder.Params) [NeZero p.d] (hv : LongTails.Setups.AdaptivePairedZerothOrder.spec.valid p)
    (f : Point p.d → ℝ) (xstar : Point p.d) (hxstar : xstar ∈ p.Q)
    (hc : ConvexOn ℝ (domain p.toPublic) f)
    (hlip : ∀ x ∈ domain p.toPublic, ∀ y ∈ domain p.toPublic,
      |f x - f y| ≤ p.M * ‖x - y‖)
    (hsmooth : p.smooth = true → ∃ grad : Point p.d → Point p.d,
      (∀ x ∈ interior (domain p.toPublic),
        HasGradientWithinAt f (grad x) (interior (domain p.toPublic)) x) ∧
      (∀ x ∈ interior (domain p.toPublic), ∀ y ∈ interior (domain p.toPublic),
        ‖grad x - grad y‖ ≤ p.L * ‖x - y‖))
    (P : Measure p.Ω) [IsProbabilityMeasure P] (μ : Measure Z) [IsProbabilityMeasure μ]
    (ξ : ℕ → Z → Direction p.toPublic × p.Ω)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ((sphereLaw (Point p.d) : Measure (Direction p.toPublic)).prod P) μ)
    (F : Point p.d × p.Ω → ℝ) (G : Point p.d × p.Ω → Point p.d)
    (δ : Point p.d → ℝ) (hFm : Measurable F) (hGm : Measurable G) (hδm : Measurable δ)
    (hδ : ∀ x ∈ domain p.toPublic, |δ x| ≤ p.Δ)
    (hfi : ∀ x ∈ domain p.toPublic, Integrable (fun w => F (x, w)) P)
    (hfmean : ∀ x ∈ domain p.toPublic, (∫ w, F (x, w) ∂P) = f x)
    (hweak : ∀ᵐ w ∂P, ContinuousOn (fun x => F (x, w)) (domain p.toPublic) ∧
      LocallyIntegrableOn (fun x => G (x, w)) (interior (domain p.toPublic)) volume ∧
      ∀ ψ : Point p.d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ interior (domain p.toPublic) → ∀ v : Point p.d,
          (∫ x, F (x, w) * (fderiv ℝ ψ x) v) = -∫ x, ⟪G (x, w), v⟫ * ψ x)
    (hi : ∀ x ∈ interior (domain p.toPublic), Integrable (fun w => ‖G (x, w)‖ ^ 2) P)
    (hb : ∀ x ∈ interior (domain p.toPublic), (∫ w, ‖G (x, w)‖ ^ 2 ∂P) ≤ p.M2 ^ 2) :
    let g := fun x w => F (x, w) + δ x
    let states := fun z => dualSolverState p.d (clipRadius p.toPublic) (clipRadius p.toPublic)
      (smoothRadius p.toPublic) (nonsmoothRadius p.toPublic) (regularization p.toPublic)
      p.project (p.x0, p.x0) (batch p.toPublic)
      (fun t i => (ξ (2 * (∑ j ∈ Finset.range t, batch p.toPublic j) + i) z).1.val)
      (fun t i => (ξ (2 * (∑ j ∈ Finset.range t, batch p.toPublic j) + batch p.toPublic t + i) z).1.val)
      g (fun i => (ξ i z).2) 0 p.N
    μ.real {z | p.ε / 32 < f (if p.smooth then (states z).1.1 else (states z).2.1) - f xstar} ≤
      3 * Real.exp (-p.ell) := by
  intro g states
  obtain ⟨pop, L, hpop, heq, hLmodel, hcoef, hsupport, hmodel, hbias⟩ :=
    winning_population_model p hv f hc hlip hsmooth
  rcases hv with ⟨hD, hmax, heps, hell0, hN, hT, hM, hM2, hL, hdelta,
    hcompact, hQ, hx0, hdiam, hproj, hnearest, hbudget, hhorizon, hnoise⟩
  have hell : 0 < p.ell := (Real.log_pos (by norm_num : (1 : ℝ) < 8)).trans_le hell0
  obtain ⟨hA, hscale, hclip, hreg, hval, hgs, hgn⟩ :=
    public_tuning_positive p.toPublic hD hmax heps hell hN hT
  let γ := if p.smooth then smoothRadius p.toPublic else nonsmoothRadius p.toPublic
  have hγ : 0 < γ := by dsimp [γ]; split_ifs <;> assumption
  have hγmax : γ ≤ p.γmax := by
    dsimp [γ, smoothRadius, nonsmoothRadius]; split_ifs <;> exact min_le_left _ _
  have hscale2 := scale_lower_bound p.toPublic hD heps hell hbudget
  have hBM := corruption_scale_bound p.toPublic hD heps hdelta hγ hscale2 hnoise
  have hp : Continuous p.project := (nearest_projection_lipschitz hQ hproj hnearest).continuous
  obtain ⟨hbatch, hw, hsum⟩ := batch_schedule_bounds p.toPublic hN hT
  have hmean (x : Point p.d) (hx : x ∈ domain p.toPublic) :
      (∫ w, F (x, w) ∂P) = pop x := (hfmean x hx).trans (heq hx)
  have hball (x : Point p.d) (hx : x ∈ p.Q) : Metric.closedBall x γ ⊆ domain p.toPublic :=
    thickening_closed_ball hx hγmax
  have hu (x : Point p.d) (hx : x ∈ p.Q) : Metric.ball x γ ⊆ interior (domain p.toPublic) :=
    (Metric.ball_subset_ball hγmax).trans (thickening_ball_interior hx p.γmax)
  have hprob := LongTails.Proofs.ClippedBatchConcentration.dual_solver_smoothed_gap_confidence
    (initial := (p.x0, p.x0)) (vstar := xstar) hξ (thickening_compact hcompact p.γmax) interior_subset hFm hGm hweak hQ hp hproj
    hx0 hx0 hxstar p.smooth hγ (sq_nonneg p.M2) hscale hA
    (show (0 : ℝ) < p.T by exact_mod_cast hT) hell hD hdiam hu hball hi hb δ hδm hδ hBM
    hN (batch p.toPublic) hw hsum (fun t _ => hbatch t) hdelta pop (ballSmooth pop γ) hpop hfi hmean
    hLmodel hreg hcoef hnearest hsupport hmodel
  have htune := public_solver_error_bound p.toPublic (M2 := p.M2) (Δ := p.Δ) (γ := γ) hD heps hell hN hT hdelta hγ
    (by linarith only [hscale2, sq_nonneg (p.ε / p.D)]) (by simpa only [mul_div_assoc] using hnoise)
  apply (measureReal_mono (μ := μ) ?_).trans hprob
  intro z hz
  have hmem := LongTails.Proofs.ClippedTwoPointExecution.dual_solver_state_mem (initial := (p.x0, p.x0)) hQ hproj hx0 hx0
    p.d (clipRadius p.toPublic) (clipRadius p.toPublic) (smoothRadius p.toPublic)
    (nonsmoothRadius p.toPublic) (regularization p.toPublic) (batch p.toPublic)
    (fun t i => (ξ (2 * (∑ j ∈ Finset.range t, batch p.toPublic j) + i) z).1.val)
    (fun t i => (ξ (2 * (∑ j ∈ Finset.range t, batch p.toPublic j) + batch p.toPublic t + i) z).1.val)
    g (fun i => (ξ i z).2) 0 p.N
  have hx : (if p.smooth then (states z).1.1 else (states z).2.1) ∈ p.Q := by
    dsimp only [states]
    split_ifs
    · exact hmem.1.1
    · exact hmem.2.1
  have hlo := (hbias _ hx).1
  have hhi := (hbias xstar hxstar).2
  have hgap : p.ε / 64 < ballSmooth pop γ
      (if p.smooth then (states z).1.1 else (states z).2.1) - ballSmooth pop γ xstar := by
    change p.ε / 32 < _ at hz
    dsimp only [γ] at ⊢
    linarith
  have hmul := mul_lt_mul_of_pos_left hgap hA
  dsimp only at ⊢
  have hfinal : _ < weightTotal p.toPublic * (ballSmooth pop γ
      (if p.smooth then (states z).1.1 else (states z).2.1) - ballSmooth pop γ xstar) :=
    lt_of_le_of_lt htune (by nlinarith only [hmul])
  simpa only [Set.mem_ofPred_eq, γ, states, g, clipRadius, weightTotal, apply_ite] using hfinal


open scoped ContDiff
open LongTails.Algorithms.ClippedTwoPoint
lemma public_output_confidence {Z : Type*} [MeasurableSpace Z]
    (p : LongTails.Setups.AdaptivePairedZerothOrder.Params) [NeZero p.d] (hv : LongTails.Setups.AdaptivePairedZerothOrder.spec.valid p)
    (f : Point p.d → ℝ) (xstar : Point p.d) (hxstar : xstar ∈ p.Q)
    (hc : ConvexOn ℝ (domain p.toPublic) f)
    (hlip : ∀ x ∈ domain p.toPublic, ∀ y ∈ domain p.toPublic,
      |f x - f y| ≤ p.M * ‖x - y‖)
    (hsmooth : p.smooth = true → ∃ grad : Point p.d → Point p.d,
      (∀ x ∈ interior (domain p.toPublic),
        HasGradientWithinAt f (grad x) (interior (domain p.toPublic)) x) ∧
      (∀ x ∈ interior (domain p.toPublic), ∀ y ∈ interior (domain p.toPublic),
        ‖grad x - grad y‖ ≤ p.L * ‖x - y‖))
    (P : Measure p.Ω) [IsProbabilityMeasure P] (μ : Measure Z) [IsProbabilityMeasure μ]
    (ξ : ℕ → Z → Direction p.toPublic × p.Ω)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ((sphereLaw (Point p.d) : Measure (Direction p.toPublic)).prod P) μ)
    (F : Point p.d × p.Ω → ℝ) (G : Point p.d × p.Ω → Point p.d)
    (δ : Point p.d → ℝ) (hFm : Measurable F) (hGm : Measurable G) (hδm : Measurable δ)
    (hδ : ∀ x ∈ domain p.toPublic, |δ x| ≤ p.Δ)
    (hfi : ∀ x ∈ domain p.toPublic, Integrable (fun w => F (x, w)) P)
    (hfmean : ∀ x ∈ domain p.toPublic, (∫ w, F (x, w) ∂P) = f x)
    (hweak : ∀ᵐ w ∂P, ContinuousOn (fun x => F (x, w)) (domain p.toPublic) ∧
      LocallyIntegrableOn (fun x => G (x, w)) (interior (domain p.toPublic)) volume ∧
      ∀ ψ : Point p.d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ interior (domain p.toPublic) → ∀ v : Point p.d,
          (∫ x, F (x, w) * (fderiv ℝ ψ x) v) = -∫ x, ⟪G (x, w), v⟫ * ψ x)
    (hi : ∀ x ∈ interior (domain p.toPublic), Integrable (fun w => ‖G (x, w)‖ ^ 2) P)
    (hb : ∀ x ∈ interior (domain p.toPublic), (∫ w, ‖G (x, w)‖ ^ 2 ∂P) ≤ p.M2 ^ 2) :
    let g := fun x w => F (x, w) + δ x
    let _states := fun z => dualSolverState p.d (clipRadius p.toPublic) (clipRadius p.toPublic)
      (smoothRadius p.toPublic) (nonsmoothRadius p.toPublic) (regularization p.toPublic)
      p.project (p.x0, p.x0) (batch p.toPublic)
      (fun t i => (ξ (2 * (∑ j ∈ Finset.range t, batch p.toPublic j) + i) z).1.val)
      (fun t i => (ξ (2 * (∑ j ∈ Finset.range t, batch p.toPublic j) + batch p.toPublic t + i) z).1.val)
      g (fun i => (ξ i z).2) 0 p.N
    let out := fun z => adaptiveOutput p.d (clipRadius p.toPublic) (clipRadius p.toPublic)
      (smoothRadius p.toPublic) (nonsmoothRadius p.toPublic) (regularization p.toPublic)
      (validationClip p.toPublic) p.project (p.x0, p.x0) (batch p.toPublic)
      (fun t i => (ξ (2 * (∑ j ∈ Finset.range t, batch p.toPublic j) + i) z).1.val)
      (fun t i => (ξ (2 * (∑ j ∈ Finset.range t, batch p.toPublic j) + batch p.toPublic t + i) z).1.val)
      g (fun i => (ξ i z).2) 0 p.N p.T
    μ.real {z | p.ε < f (out z) - f xstar} ≤ 5 * Real.exp (-p.ell) := by
  intro g states out
  have hsolver := public_solver_confidence p hv f xstar hxstar hc hlip hsmooth P μ ξ hξ
    F G δ hFm hGm hδm hδ hfi hfmean hweak hi hb
  rcases hv with ⟨hD, hmax, heps, hell0, hN, hT, hM, hM2, hL, hdelta,
    hcompact, hQ, hx0, hdiam, hproj, hnearest, hbudget, hhorizon, hnoise⟩
  have hell : 0 < p.ell := (Real.log_pos (by norm_num : (1 : ℝ) < 8)).trans_le hell0
  obtain ⟨hA, hscale, hclip, hreg, hval, hgs, hgn⟩ :=
    public_tuning_positive p.toPublic hD hmax heps hell hN hT
  have hscale2 := scale_lower_bound p.toPublic hD heps hell hbudget
  have hvar : p.M2 ^ 2 ≤ scale p.toPublic ^ 2 := by
    linarith only [hscale2, sq_nonneg (p.ε / p.D)]
  have hbase : (p.ε / p.D) ^ 2 ≤ scale p.toPublic ^ 2 := by
    linarith only [hscale2, sq_nonneg p.M2]
  have hdeltaeps := winning_radius_corruption_bound p.toPublic p.smooth hD heps hmax hN hnoise
  obtain ⟨hH, hdeltaH, hBH, hsc, herr⟩ :=
    selection_tuning_bounds p.toPublic hD heps hell hT hvar hbase hdeltaeps
  have hp : Continuous p.project := (nearest_projection_lipschitz hQ hproj hnearest).continuous
  have hselector := LongTails.Proofs.ClippedSelection.adaptive_weak_oracle_selection
    (d := p.d) (initial := (p.x0, p.x0)) hξ Prod.snd measurePreserving_snd
    (thickening_compact hcompact p.γmax) interior_subset hQ hFm hGm hweak
    (sq_nonneg p.M2) hD.le (show 0 < p.γmax / 2 by positivity) hdelta hdeltaH hBH
    (fun x hx => thickening_uniform_margin hx (show p.γmax / 2 < p.γmax by linarith))
    hdiam hi hb f δ hδm hδ hfi hfmean p.N p.T hT hval hell hsc
    (clipRadius p.toPublic) (clipRadius p.toPublic) (smoothRadius p.toPublic)
    (nonsmoothRadius p.toPublic) (regularization p.toPublic) hp hproj hx0 hx0
    (batch p.toPublic) (fun z : Direction p.toPublic × p.Ω => z.1.val)
    (continuous_subtype_val.measurable.comp measurable_fst)
  let A := {z | p.ε / 32 < f (if p.smooth then (states z).1.1 else (states z).2.1) - f xstar}
  let B := {z | min (f (states z).1.1) (f (states z).2.1) +
      (4097 * validationClip p.toPublic * p.ell / p.T + 2 * p.Δ) < f (out z)}
  have hAprob : μ.real A ≤ 3 * Real.exp (-p.ell) := hsolver
  have hBprob : μ.real B ≤ 2 * Real.exp (-p.ell) := hselector
  have hsubset : {z | p.ε < f (out z) - f xstar} ⊆ A ∪ B := by
    intro z hz
    by_contra hn
    have hnA : ¬ z ∈ A := fun ha => hn (Or.inl ha)
    have hnB : ¬ z ∈ B := fun hb => hn (Or.inr hb)
    have ha : f (if p.smooth then (states z).1.1 else (states z).2.1) - f xstar ≤ p.ε / 32 :=
      le_of_not_gt hnA
    have hb' : f (out z) ≤ min (f (states z).1.1) (f (states z).2.1) +
        (4097 * validationClip p.toPublic * p.ell / p.T + 2 * p.Δ) := le_of_not_gt hnB
    have hm : min (f (states z).1.1) (f (states z).2.1) ≤
        f (if p.smooth then (states z).1.1 else (states z).2.1) := by
      split_ifs
      · exact min_le_left _ _
      · exact min_le_right _ _
    change p.ε < f (out z) - f xstar at hz
    linarith
  exact (measureReal_mono (μ := μ) hsubset).trans ((measureReal_union_le A B).trans
    (by linarith only [hAprob, hBprob]))

end PopulationModel

section FrameworkCompletion

open Set LocalPopulationModels

lemma successful_execution (p : LongTails.Setups.AdaptivePairedZerothOrder.Params) (hv : LongTails.Setups.AdaptivePairedZerothOrder.spec.valid p) (I : LongTails.Setups.AdaptivePairedZerothOrder.Instance p.toPublic)
    (O : OracleTemplate.Oracle (Point p.d) ℝ) (hadm : LongTails.Setups.AdaptivePairedZerothOrder.spec.admissible p I O) :
    LongTails.Setups.AdaptivePairedZerothOrder.spec.successful p I
      (fun z : (algorithm p.toPublic).Seed × ((k : ℕ) → O.Seed k) =>
        OracleTemplate.execute O (algorithm p.toPublic) (fun _ => 6 * p.T + 4 * p.N) z.1 z.2)
      ⟨((algorithm p.toPublic).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  let : NeZero p.d := ⟨p.dimension_pos.ne'⟩
  rcases hadm with ⟨hxstar, hmin, hc, hlip, hsmooth, F, G, δ, sampleLaw, sourceLaw, ξ,
    hξ, hO, hFm, hGm, hδm, hδ, hfi, hfmean, hweak, hi, hb⟩
  subst O
  have hv0 := hv
  rcases hv with ⟨hD, hmax, heps, hell0, hN, hT, hM, hM2, hL, hdelta,
    hcompact, hQ, hx0, hdiam, hproj, hnearest, hbudget, hhorizon, hnoise⟩
  let g := fun x w => F (x, w) + δ x
  have hg : Measurable (fun z : Point p.d × p.Ω => g z.1 z.2) := hFm.add (hδm.comp measurable_fst)
  have hp : Continuous p.project := (nearest_projection_lipschitz hQ hproj hnearest).continuous
  let paired := sourceLaw.map (fun z n => ξ (n / 2) z)
  let oracle : OracleTemplate.Oracle (Point p.d) ℝ :=
    { Seed := fun _ => p.Ω, law := paired, answer := fun _ (_, x) w => g x w }
  let raw := fun z : (ℕ → Direction p.toPublic) × (ℕ → p.Ω) =>
    OracleTemplate.execute oracle (algorithm p.toPublic) (fun _ => 6 * p.T + 4 * p.N) z.1 z.2
  let selected := fun z : (ℕ → Direction p.toPublic) × p.Ξ =>
    output p.toPublic z.1 g (fun i => ξ i z.2)
  have hm : Measurable raw := execute_measurable p.toPublic paired g hg hp hN hT
  have hfeas (z) : raw z ∈ p.Q := execute_feasible p.toPublic paired g hQ hproj hx0 hN hT z.1 z.2
  have hselected (z) : selected z ∈ p.Q := output_feasible p.toPublic hQ hproj hx0 z.1 g (fun i => ξ i z.2)
  have hQC : p.Q ⊆ domain p.toPublic := by
    intro x hx
    exact interior_subset (thickening_ball_interior hx p.γmax (by simpa using hmax))
  obtain ⟨pop, L, hpop, heq, hmodel⟩ := winning_population_model p hv0 I.f hc hlip hsmooth
  have hgap : Measurable (fun z => I.f (raw z) - I.f I.xstar) := by
    have he : (fun z => I.f (raw z) - I.f I.xstar) =
        (fun z => pop (raw z) - I.f I.xstar) := by
      funext z
      rw [heq (hQC (hfeas z))]
    rw [he]
    exact (hpop.measurable.comp hm).sub_const _
  refine ⟨hm, hfeas, hgap, ?_⟩
  have hrecords := LongTails.Proofs.PairedOracleExecution.product_iid (direction_samples p.toPublic) hξ
  have hprob := public_output_confidence p hv0 I.f I.xstar hxstar hc hlip hsmooth
    (sampleLaw : Measure _) ((directionLaw p.toPublic : Measure _).prod (sourceLaw : Measure _))
    (fun i (z : (ℕ → Direction p.toPublic) × p.Ξ) => (z.1 i, ξ i z.2)) hrecords F G δ hFm hGm hδm hδ hfi hfmean hweak hi hb
  have hmselected : Measurable selected := by
    exact LongTails.Proofs.ClippedTwoPointExecution.adaptive_output_measurable p.d
      (clipRadius p.toPublic) (clipRadius p.toPublic) (smoothRadius p.toPublic)
      (nonsmoothRadius p.toPublic) (regularization p.toPublic) (validationClip p.toPublic)
      hp (p.x0, p.x0) (batch p.toPublic)
      (fun z : (ℕ → Direction p.toPublic) × p.Ξ => firstDirections p.toPublic z.1)
      (fun z => secondDirections p.toPublic z.1)
      (fun t i => (first_directions_measurable p.toPublic t i).comp measurable_fst)
      (fun t i => (second_directions_measurable p.toPublic t i).comp measurable_fst)
      g hg (fun i z => ξ i z.2) (fun i => (hξ.measurable i).comp measurable_snd) 0 p.N p.T
  let V := {x | p.ε < pop x - I.f I.xstar}
  have hV : MeasurableSet V := measurableSet_lt measurable_const (hpop.measurable.sub_const _)
  have hrawset : {z | p.ε < I.f (raw z) - I.f I.xstar} = raw ⁻¹' V := by
    ext z
    change (p.ε < I.f (raw z) - I.f I.xstar) ↔ (p.ε < pop (raw z) - I.f I.xstar)
    rw [heq (hQC (hfeas z))]
  have hselectedset : {z | p.ε < I.f (selected z) - I.f I.xstar} = selected ⁻¹' V := by
    ext z
    change (p.ε < I.f (selected z) - I.f I.xstar) ↔ (p.ε < pop (selected z) - I.f I.xstar)
    rw [heq (hQC (hselected z))]
  have hlaw := actual_output_law p.toPublic sourceLaw ξ hξ.measurable g hg hp hN hT
  change ((directionLaw p.toPublic : Measure _).prod (paired : Measure _)).real
    {z | p.ε < I.f (raw z) - I.f I.xstar} ≤ 8 * Real.exp (-p.ell)
  rw [hrawset, ← map_measureReal_apply hm hV, hlaw, map_measureReal_apply hmselected hV,
    ← hselectedset]
  exact hprob.trans (by nlinarith [Real.exp_pos (-p.ell)])

end FrameworkCompletion

end LongTails.Proofs.AdaptivePairedZerothOrder
