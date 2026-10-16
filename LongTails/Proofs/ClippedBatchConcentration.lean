import LongTails.Proofs.LocalPopulationSmoothing
import LongTails.Proofs.ClippedVectorMoments
import LongTails.Proofs.WeightedOracleBlocks
import LongTails.Proofs.PairedOracleExecution
import LongTails.Proofs.ClippedTwoPointConvergence
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open MeasureTheory Set Metric
open scoped RealInnerProductSpace ContDiff

set_option maxHeartbeats 2000000

namespace LongTails.Proofs.ClippedBatchConcentration

open LongTails.Algorithms.ClippedTwoPoint LongTails.Proofs.ClippedVectorMoments

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "S" => Metric.sphere (0 : H) 1
local notation "Q" => (OracleTemplate.ZerothOrder.sphereLaw H : Measure S)

lemma weak_clipped_fiber_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (x : H) {γ B τ h : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    {c : S × Ω → ℝ} (hc : Measurable c) (hcb : ∀ z, |c z| ≤ h) :
    let a := fun z : S × Ω =>
      (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)
    let V := fun z => directionEstimate d τ (z.1 : H) (a z + c z)
    let Y := fun z => V z - ∫ w, V w ∂(Q).prod P
    (∀ z, ‖Y z‖ ≤ 2 * (d : ℝ) * τ) ∧
      (Integrable (fun z => ‖Y z‖ ^ 2) ((Q).prod P) ∧
        (∫ z, ‖Y z‖ ^ 2 ∂(Q).prod P) ≤ 10 * (d : ℝ) * (B + d * h ^ 2)) ∧
      (∀ θ : ℝ, ∀ v : H, (256 * Real.sqrt d * τ) * |θ| * ‖v‖ < 1 →
        Integrable (fun z => Real.exp (θ * ⟪v, Y z⟫)) ((Q).prod P) ∧
          (∫ z, Real.exp (θ * ⟪v, Y z⟫) ∂(Q).prod P) ≤
            Real.exp ((131072 * (B + d * h ^ 2)) * ‖v‖ ^ 2 * θ ^ 2 /
              (1 - (256 * Real.sqrt d * τ) * |θ| * ‖v‖))) := by
  let a := fun z : S × Ω =>
    (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)
  have hu : Measurable (fun z : S × Ω => (z.1 : H)) :=
    continuous_subtype_val.measurable.comp measurable_fst
  have hunit : ∀ z : S × Ω, ‖(z.1 : H)‖ = 1 := by
    intro z
    simpa only [mem_sphere_iff_norm, sub_zero] using z.1.property
  have ha : Measurable a :=
    ((hFm.comp ((measurable_const.add (hu.const_smul γ)).prodMk measurable_snd)).sub
      (hFm.comp ((measurable_const.sub (hu.const_smul γ)).prodMk measurable_snd))).div_const _
  have hbase := WeakGradientSegments.weak_spherical_directional_moment hC hUC hFm hG hF x
    hγ hB hU hCU hi hb (0 : H) 0
  have hbase' : Integrable (fun z => a z ^ 2) ((Q).prod P) ∧
      (d : ℝ) * (∫ z, a z ^ 2 ∂(Q).prod P) ≤ 5 * B := by
    simpa only [Nat.zero_add, Nat.mul_zero, pow_zero, pow_one, mul_one, Nat.factorial_zero,
      Nat.cast_one] using hbase
  refine ⟨fun z => centered_direction_estimate_norm_le (P := (Q).prod P)
      (a := fun z => a z + c z) hunit d hτ z,
    perturbed_centered_direction_estimate_trace hu ha hc hunit d hτ hcb hbase'.1 hbase'.2, ?_⟩
  intro θ v hsmall
  have hs : 256 * |θ| * (Real.sqrt d * τ * ‖v‖) < 1 := by
    convert hsmall using 1
    ring
  have hm := spherical_centered_direction_mgf ha hc hτ hB hcb v
    (fun k => WeakGradientSegments.weak_spherical_directional_moment hC hUC hFm hG hF x
      hγ hB hU hCU hi hb v (k + 1)) hs
  have he : 131072 * ((B + d * h ^ 2) * ‖v‖ ^ 2) * θ ^ 2 /
      (1 - 256 * |θ| * (Real.sqrt d * τ * ‖v‖)) =
      (131072 * (B + d * h ^ 2)) * ‖v‖ ^ 2 * θ ^ 2 /
      (1 - (256 * Real.sqrt d * τ) * |θ| * ‖v‖) := by ring
  simpa only [he] using hm

lemma weak_clipped_population_bias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H} {f : H → ℝ}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (hfcont : Continuous f)
    (hfi : ∀ z ∈ C, Integrable (fun ξ => F (z, ξ)) P)
    (hfmean : ∀ z ∈ C, (∫ ξ, F (z, ξ) ∂P) = f z)
    (x : H) {γ B τ h : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B) (hτ : 0 < τ) (hh : 0 ≤ h)
    (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    {c : S × Ω → ℝ} (hc : Measurable c) (hcb : ∀ z, |c z| ≤ h) :
    let a := fun z : S × Ω => (F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)
    ‖(∫ z, directionEstimate d τ (z.1 : H) (a z + c z) ∂(Q).prod P) -
      LocalPopulationSmoothing.boundaryField f γ x‖ ≤
        15 * B / (Real.sqrt d * τ) + Real.sqrt d * h := by
  have hbase := WeakGradientSegments.weak_spherical_directional_moment hC hUC hFm hG hF x
    hγ hB hU hCU hi hb (0 : H) 0
  have hsecond : Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2)
        ((Q).prod P) := by
    simpa only [Nat.mul_zero, pow_zero, mul_one] using hbase.1
  have hp (u : S) : x + γ • (u : H) ∈ C := by
    apply hCU
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hγ]
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using u.property
    rw [hu, mul_one]
  have hn (u : S) : x - γ • (u : H) ∈ C := by
    apply hCU
    rw [mem_closedBall, dist_eq_norm]
    have he : x - γ • (u : H) - x = -(γ • (u : H)) := by abel
    rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using u.property
    rw [hu, mul_one]
  have hm := LocalPopulationSmoothing.paired_population_mean hFm hfi hfmean x γ hp hn hsecond
  rw [LocalPopulationSmoothing.paired_sphere_mean_eq_boundary hfcont] at hm
  have hbias := weak_clipped_direction_bias hC hUC hFm hG hF x hγ hB hτ hh hU hCU hi hb hc hcb
  dsimp only at hbias ⊢
  rw [hm] at hbias
  exact hbias

lemma weak_clipped_adaptive_block_confidence {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ξ → S × Ω}
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ((Q).prod P) μ)
    {F : H × Ω → ℝ} {G : H × Ω → H} {C U : Set H}
    (hC : IsCompact C) (hUC : U ⊆ C) (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    {x : (n : ℕ) → (Fin n → S × Ω) → H} (hx : ∀ i, Measurable (x i))
    {γ B M A T ell h : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hM : 0 < M) (hA : 0 < A) (hT : 0 < T) (hell : 0 < ell)
    (hU : ∀ i a, ball (x i a) γ ⊆ U) (hCU : ∀ i a, closedBall (x i a) γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    {c : (n : ℕ) → (Fin n → S × Ω) × (S × Ω) → ℝ}
    (hc : ∀ i, Measurable (c i)) (hcb : ∀ i a z, |c i (a, z)| ≤ h)
    (hBM : B + d * h ^ 2 ≤ 2 * M ^ 2)
    {N : ℕ} (block : ℕ → Fin N) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i, |w i| ≤ A / T) (hs : (∑ i ∈ Finset.range n, w i ^ 2) ≤ A ^ 2 / T) :
    let τ := M * Real.sqrt (T / ((d : ℝ) * ell))
    let a := fun i (az : (Fin i → S × Ω) × (S × Ω)) =>
      (F (x i az.1 + γ • (az.2.1 : H), az.2.2) -
        F (x i az.1 - γ • (az.2.1 : H), az.2.2)) / (2 * γ)
    let V := fun i az => directionEstimate d τ (az.2.1 : H) (a i az + c i az)
    let Y := fun i az => V i az - ∫ z, V i (az.1, z) ∂(Q).prod P
    μ.real {ζ | 8192 * Real.sqrt ((M ^ 2 * A ^ 2 / T) * ((d : ℝ) + ell)) <
      ‖∑ i ∈ Finset.range n, w i •
        (PiLp.single 2 (block i) (Y i ((fun j => ξ j ζ), ξ i ζ)) : PiLp 2 (fun _ : Fin N => H))‖} ≤
          2 * Real.exp (-ell) := by
  let τ := M * Real.sqrt (T / ((d : ℝ) * ell))
  let a := fun i (az : (Fin i → S × Ω) × (S × Ω)) =>
    (F (x i az.1 + γ • (az.2.1 : H), az.2.2) -
      F (x i az.1 - γ • (az.2.1 : H), az.2.2)) / (2 * γ)
  let V := fun i az => directionEstimate d τ (az.2.1 : H) (a i az + c i az)
  let Y := fun i az => V i az - ∫ z, V i (az.1, z) ∂(Q).prod P
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hB0 : 0 ≤ B + d * h ^ 2 := by positivity
  have hpars := WeightedOracleBlocks.clipping_weighted_parameters hM hA hT hd hell hB0 hBM w n hw hs
  have hK := (WeightedOracleBlocks.clipping_schedule_scales hM hA hT hd hell).1
  have hYm : ∀ i, Measurable (Y i) := by
    intro i
    have hu : Measurable (fun z : (Fin i → S × Ω) × (S × Ω) => (z.2.1 : H)) :=
      continuous_subtype_val.measurable.comp (measurable_fst.comp measurable_snd)
    have hsample : Measurable (fun z : (Fin i → S × Ω) × (S × Ω) => z.2.2) :=
      measurable_snd.comp measurable_snd
    have hcenter := (hx i).comp (measurable_fst : Measurable (fun z : (Fin i → S × Ω) × (S × Ω) => z.1))
    have ha : Measurable (a i) :=
      ((hFm.comp ((hcenter.add (hu.const_smul γ)).prodMk hsample)).sub
        (hFm.comp ((hcenter.sub (hu.const_smul γ)).prodMk hsample))).div_const _
    exact centered_direction_estimate_joint_measurable hu (ha.add (hc i)) d τ
  have hstats (i : ℕ) (a₀ : Fin i → S × Ω) :=
    weak_clipped_fiber_bounds hC hUC hFm hG hF (x i a₀) hγ hB hτ (hU i a₀) (hCU i a₀) hi hb
      ((hc i).comp (measurable_const.prodMk measurable_id)) (hcb i a₀)
  have hcap : ∀ i a₀ z, w i ^ 2 * ‖Y i (a₀, z)‖ ^ 2 ≤
      4 * (d : ℝ) * (M ^ 2 * A ^ 2 / T) / ell := by
    intro i a₀ z
    have hh := pow_le_pow_left₀ (norm_nonneg _) ((hstats i a₀).1 z) 2
    exact (mul_le_mul_of_nonneg_left hh (sq_nonneg (w i))).trans (hpars.1 i)
  have hv : ∀ i a₀, Integrable (fun z => ‖Y i (a₀, z)‖ ^ 2) ((Q).prod P) ∧
      (∫ z, ‖Y i (a₀, z)‖ ^ 2 ∂(Q).prod P) ≤ 10 * (d : ℝ) * (B + d * h ^ 2) :=
    fun i a₀ => (hstats i a₀).2.1
  have hm : ∀ i a₀ θ v, (256 * Real.sqrt d * τ) * |θ| * ‖v‖ < 1 →
      Integrable (fun z => Real.exp (θ * ⟪v, Y i (a₀, z)⟫)) ((Q).prod P) ∧
        (∫ z, Real.exp (θ * ⟪v, Y i (a₀, z)⟫) ∂(Q).prod P) ≤
          Real.exp ((131072 * (B + d * h ^ 2)) * ‖v‖ ^ 2 * θ ^ 2 /
            (1 - (256 * Real.sqrt d * τ) * |θ| * ‖v‖)) :=
    fun i a₀ θ v hv => (hstats i a₀).2.2 θ v hv
  exact WeightedOracleBlocks.iid_weighted_block_confidence h_samples.measurable h_samples.independent
    h_samples.marginal hYm block w (fun _ => 10 * (d : ℝ) * (B + d * h ^ 2)) n hK hd hell
    (by positivity) (by positivity) hcap hv hpars.2.1 hpars.2.2.1 hpars.2.2.2 hm

omit [NeZero d] in
lemma fixed_corruption_difference_measurable {Z : Type*} [MeasurableSpace Z]
    {x u : Z → H} (hx : Measurable x) (hu : Measurable u) {δ : H → ℝ}
    (hδ : Measurable δ) (γ : ℝ) :
    Measurable (fun z => (δ (x z + γ • u z) - δ (x z - γ • u z)) / (2 * γ)) :=
  ((hδ.comp (hx.add (hu.const_smul γ))).sub
    (hδ.comp (hx.sub (hu.const_smul γ)))).div_const (2 * γ)

omit [NeZero d] in
lemma fixed_corruption_difference_bound {C : Set H} {δ : H → ℝ} {Δ γ : ℝ}
    (hγ : 0 < γ) (hδ : ∀ x ∈ C, |δ x| ≤ Δ) {x u : H}
    (hp : x + γ • u ∈ C) (hn : x - γ • u ∈ C) :
    |(δ (x + γ • u) - δ (x - γ • u)) / (2 * γ)| ≤ Δ / γ := by
  have hab : |δ (x + γ • u) - δ (x - γ • u)| ≤
      |δ (x + γ • u)| + |δ (x - γ • u)| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (δ (x + γ • u)) (-δ (x - γ • u))
  have hb := hab.trans (add_le_add (hδ _ hp) (hδ _ hn))
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * γ)]
  calc
    _ ≤ (Δ + Δ) / (2 * γ) := div_le_div_of_nonneg_right hb (by positivity)
    _ = Δ / γ := by field_simp; ring

omit [NeZero d] in
lemma fixed_corruption_estimate {W : Type*} (F : H × W → ℝ) (δ : H → ℝ)
    (τ γ : ℝ) (x u : H) (ξ : W) :
    estimate d τ γ u (F (x + γ • u, ξ) + δ (x + γ • u))
      (F (x - γ • u, ξ) + δ (x - γ • u)) =
      directionEstimate d τ u ((F (x + γ • u, ξ) - F (x - γ • u, ξ)) / (2 * γ) +
        (δ (x + γ • u) - δ (x - γ • u)) / (2 * γ)) := by
  unfold estimate
  congr 1
  ring

lemma weak_clipped_adaptive_comparator_confidence {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ξ → S × Ω}
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ((Q).prod P) μ)
    {F : H × Ω → ℝ} {G : H × Ω → H} {C U : Set H}
    (hC : IsCompact C) (hUC : U ⊆ C) (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    {x : (n : ℕ) → (Fin n → S × Ω) → H} (hx : ∀ i, Measurable (x i))
    {γ B M A T ell h : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hM : 0 < M) (hA : 0 < A) (hT : 0 < T) (hell : 0 < ell)
    (hU : ∀ i a, ball (x i a) γ ⊆ U) (hCU : ∀ i a, closedBall (x i a) γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    {c : (n : ℕ) → (Fin n → S × Ω) × (S × Ω) → ℝ}
    (hc : ∀ i, Measurable (c i)) (hcb : ∀ i a z, |c i (a, z)| ≤ h)
    (hBM : B + d * h ^ 2 ≤ 2 * M ^ 2)
    {v : (n : ℕ) → (Fin n → S × Ω) → H} (hv : ∀ i, Measurable (v i))
    {D : ℝ} (hD : 0 < D) (hvb : ∀ i a, ‖v i a‖ ≤ D)
    (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i, |w i| ≤ A / T) (hs : (∑ i ∈ Finset.range n, w i ^ 2) ≤ A ^ 2 / T) :
    let τ := M * Real.sqrt (T / ((d : ℝ) * ell))
    let a := fun i (az : (Fin i → S × Ω) × (S × Ω)) =>
      (F (x i az.1 + γ • (az.2.1 : H), az.2.2) -
        F (x i az.1 - γ • (az.2.1 : H), az.2.2)) / (2 * γ)
    let V := fun i az => directionEstimate d τ (az.2.1 : H) (a i az + c i az)
    let Y := fun i az => V i az - ∫ z, V i (az.1, z) ∂(Q).prod P
    μ.real {ζ | 1280 * (D * Real.sqrt (M ^ 2 * A ^ 2 / T)) * Real.sqrt ell ≤
      ∑ i ∈ Finset.range n, w i * ⟪v i (fun j => ξ j ζ), Y i ((fun j => ξ j ζ), ξ i ζ)⟫} ≤
          Real.exp (-ell) := by
  let τ := M * Real.sqrt (T / ((d : ℝ) * ell))
  let a := fun i (az : (Fin i → S × Ω) × (S × Ω)) =>
    (F (x i az.1 + γ • (az.2.1 : H), az.2.2) -
      F (x i az.1 - γ • (az.2.1 : H), az.2.2)) / (2 * γ)
  let V := fun i az => directionEstimate d τ (az.2.1 : H) (a i az + c i az)
  let Y := fun i az => V i az - ∫ z, V i (az.1, z) ∂(Q).prod P
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hB0 : 0 ≤ B + d * h ^ 2 := by positivity
  have hpars := WeightedOracleBlocks.clipping_weighted_parameters hM hA hT hd hell hB0 hBM w n hw hs
  have hK := (WeightedOracleBlocks.clipping_schedule_scales hM hA hT hd hell).1
  have hYm : ∀ i, Measurable (Y i) := by
    intro i
    have hu : Measurable (fun z : (Fin i → S × Ω) × (S × Ω) => (z.2.1 : H)) :=
      continuous_subtype_val.measurable.comp (measurable_fst.comp measurable_snd)
    have hsample : Measurable (fun z : (Fin i → S × Ω) × (S × Ω) => z.2.2) :=
      measurable_snd.comp measurable_snd
    have hcenter := (hx i).comp (measurable_fst : Measurable (fun z : (Fin i → S × Ω) × (S × Ω) => z.1))
    have ha : Measurable (a i) :=
      ((hFm.comp ((hcenter.add (hu.const_smul γ)).prodMk hsample)).sub
        (hFm.comp ((hcenter.sub (hu.const_smul γ)).prodMk hsample))).div_const _
    exact centered_direction_estimate_joint_measurable hu (ha.add (hc i)) d τ
  have hstats (i : ℕ) (a₀ : Fin i → S × Ω) :=
    weak_clipped_fiber_bounds hC hUC hFm hG hF (x i a₀) hγ hB hτ (hU i a₀) (hCU i a₀) hi hb
      ((hc i).comp (measurable_const.prodMk measurable_id)) (hcb i a₀)
  have hm : ∀ i a₀ θ v, (256 * Real.sqrt d * τ) * |θ| * ‖v‖ < 1 →
      Integrable (fun z => Real.exp (θ * ⟪v, Y i (a₀, z)⟫)) ((Q).prod P) ∧
        (∫ z, Real.exp (θ * ⟪v, Y i (a₀, z)⟫) ∂(Q).prod P) ≤
          Real.exp ((131072 * (B + d * h ^ 2)) * ‖v‖ ^ 2 * θ ^ 2 /
            (1 - (256 * Real.sqrt d * τ) * |θ| * ‖v‖)) :=
    fun i a₀ θ v hv => (hstats i a₀).2.2 θ v hv
  exact WeightedOracleBlocks.iid_weighted_direction_confidence h_samples.measurable h_samples.independent
    h_samples.marginal hYm hv w n hK hD hell (by positivity) (by positivity) hvb
    hpars.2.2.1 hpars.2.2.2 hm

lemma fixed_corruption_population_bias {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H} {f : H → ℝ}
    {C U : Set H} (hC : IsCompact C) (hUC : U ⊆ C)
    (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    (hfcont : Continuous f)
    (hfi : ∀ z ∈ C, Integrable (fun ξ => F (z, ξ)) P)
    (hfmean : ∀ z ∈ C, (∫ ξ, F (z, ξ) ∂P) = f z)
    (x : H) {γ B τ Δ : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B) (hτ : 0 < τ) (hΔ : 0 ≤ Δ)
    (hU : ball x γ ⊆ U) (hCU : closedBall x γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (δ : H → ℝ) (hδm : Measurable δ) (hδ : ∀ z ∈ C, |δ z| ≤ Δ) :
    ‖(∫ z : S × Ω, estimate d τ γ (z.1 : H)
      (F (x + γ • (z.1 : H), z.2) + δ (x + γ • (z.1 : H)))
      (F (x - γ • (z.1 : H), z.2) + δ (x - γ • (z.1 : H))) ∂(Q).prod P) -
      LocalPopulationSmoothing.boundaryField f γ x‖ ≤
        15 * B / (Real.sqrt d * τ) + Real.sqrt d * (Δ / γ) := by
  let c := fun z : S × Ω => (δ (x + γ • (z.1 : H)) - δ (x - γ • (z.1 : H))) / (2 * γ)
  have hu : Measurable (fun z : S × Ω => (z.1 : H)) :=
    continuous_subtype_val.measurable.comp measurable_fst
  have hc : Measurable c := fixed_corruption_difference_measurable
    (measurable_const : Measurable (fun _ : S × Ω => x)) hu hδm γ
  have hp (u : S) : x + γ • (u : H) ∈ C := by
    apply hCU
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hγ]
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using u.property
    rw [hu, mul_one]
  have hn (u : S) : x - γ • (u : H) ∈ C := by
    apply hCU
    rw [mem_closedBall, dist_eq_norm]
    rw [show x - γ • (u : H) - x = -(γ • (u : H)) by abel,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using u.property
    rw [hu, mul_one]
  have hcb (z : S × Ω) : |c z| ≤ Δ / γ :=
    fixed_corruption_difference_bound hγ hδ (hp z.1) (hn z.1)
  have hbias := weak_clipped_population_bias hC hUC hFm hG hF hfcont hfi hfmean x
    hγ hB hτ (div_nonneg hΔ hγ.le) hU hCU hi hb hc hcb
  dsimp only at hbias
  simpa only [fixed_corruption_estimate, c] using hbias

lemma fixed_corruption_record_confidence {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ξ → S × Ω}
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ((Q).prod P) μ)
    {F : H × Ω → ℝ} {G : H × Ω → H} {C U : Set H}
    (hC : IsCompact C) (hUC : U ⊆ C) (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    {x : (n : ℕ) → (Fin n → S × Ω) → H} (hx : ∀ i, Measurable (x i))
    {γ B M A T ell Δ : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hM : 0 < M) (hA : 0 < A) (hT : 0 < T) (hell : 0 < ell)
    (hU : ∀ i a, ball (x i a) γ ⊆ U) (hCU : ∀ i a, closedBall (x i a) γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (δ : H → ℝ) (hδm : Measurable δ) (hδ : ∀ z ∈ C, |δ z| ≤ Δ)
    (hBM : B + d * (Δ / γ) ^ 2 ≤ 2 * M ^ 2)
    {v : (n : ℕ) → (Fin n → S × Ω) → H} (hv : ∀ i, Measurable (v i))
    {D : ℝ} (hD : 0 < D) (hvb : ∀ i a, ‖v i a‖ ≤ D)
    {N : ℕ} (block : ℕ → Fin N) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i, |w i| ≤ A / T) (hs : (∑ i ∈ Finset.range n, w i ^ 2) ≤ A ^ 2 / T) :
    let τ := M * Real.sqrt (T / ((d : ℝ) * ell))
    let V := fun i (az : (Fin i → S × Ω) × (S × Ω)) =>
      estimate d τ γ (az.2.1 : H)
        (F (x i az.1 + γ • (az.2.1 : H), az.2.2) + δ (x i az.1 + γ • (az.2.1 : H)))
        (F (x i az.1 - γ • (az.2.1 : H), az.2.2) + δ (x i az.1 - γ • (az.2.1 : H)))
    let Y := fun i az => V i az - ∫ z, V i (az.1, z) ∂(Q).prod P
    μ.real {ζ | 8192 * Real.sqrt ((M ^ 2 * A ^ 2 / T) * ((d : ℝ) + ell)) <
        ‖∑ i ∈ Finset.range n, w i •
          (PiLp.single 2 (block i) (Y i ((fun j => ξ j ζ), ξ i ζ)) : PiLp 2 (fun _ : Fin N => H))‖ ∨
      1280 * (D * Real.sqrt (M ^ 2 * A ^ 2 / T)) * Real.sqrt ell ≤
        ∑ i ∈ Finset.range n, w i * ⟪v i (fun j => ξ j ζ), Y i ((fun j => ξ j ζ), ξ i ζ)⟫} ≤
      3 * Real.exp (-ell) := by
  let c := fun i (az : (Fin i → S × Ω) × (S × Ω)) =>
    (δ (x i az.1 + γ • (az.2.1 : H)) - δ (x i az.1 - γ • (az.2.1 : H))) / (2 * γ)
  have hc (i : ℕ) : Measurable (c i) :=
    fixed_corruption_difference_measurable ((hx i).comp measurable_fst)
      (continuous_subtype_val.measurable.comp (measurable_fst.comp measurable_snd)) hδm γ
  have hp (i : ℕ) (a : Fin i → S × Ω) (u : S) : x i a + γ • (u : H) ∈ C := by
    apply hCU i a
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using u.property
    rw [hu, mul_one]
  have hn (i : ℕ) (a : Fin i → S × Ω) (u : S) : x i a - γ • (u : H) ∈ C := by
    apply hCU i a
    rw [mem_closedBall, dist_eq_norm]
    rw [show x i a - γ • (u : H) - x i a = -(γ • (u : H)) by abel,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
    have hu : ‖(u : H)‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using u.property
    rw [hu, mul_one]
  have hcb (i : ℕ) (a : Fin i → S × Ω) (z : S × Ω) : |c i (a, z)| ≤ Δ / γ :=
    fixed_corruption_difference_bound hγ hδ (hp i a z.1) (hn i a z.1)
  have hbprob := weak_clipped_adaptive_block_confidence h_samples hC hUC hFm hG hF hx
    hγ hB hM hA hT hell hU hCU hi hb hc hcb hBM block w n hw hs
  have hcprob := weak_clipped_adaptive_comparator_confidence h_samples hC hUC hFm hG hF hx
    hγ hB hM hA hT hell hU hCU hi hb hc hcb hBM hv hD hvb w n hw hs
  dsimp only at hbprob hcprob ⊢
  simp only [fixed_corruption_estimate, c] at hbprob hcprob ⊢
  rw [Set.ofPred_or]
  exact (measureReal_union_le _ _).trans (by linarith only [hbprob, hcprob])

lemma fixed_corruption_batch_confidence {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ξ → S × Ω}
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ((Q).prod P) μ)
    {F : H × Ω → ℝ} {G : H × Ω → H} {C U : Set H}
    (hC : IsCompact C) (hUC : U ⊆ C) (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    {x : (n : ℕ) → (Fin n → S × Ω) → H} (hx : ∀ i, Measurable (x i))
    {γ B M A T ell Δ : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hM : 0 < M) (hA : 0 < A) (hT : 0 < T) (hell : 0 < ell)
    (hU : ∀ i a, ball (x i a) γ ⊆ U) (hCU : ∀ i a, closedBall (x i a) γ ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ξ => ‖G (z, ξ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ξ, ‖G (z, ξ)‖ ^ 2 ∂P) ≤ B)
    (δ : H → ℝ) (hδm : Measurable δ) (hδ : ∀ z ∈ C, |δ z| ≤ Δ)
    (hBM : B + d * (Δ / γ) ^ 2 ≤ 2 * M ^ 2)
    {v : (n : ℕ) → (Fin n → S × Ω) → H} (hv : ∀ i, Measurable (v i))
    {D : ℝ} (hD : 0 < D) (hvb : ∀ i a, ‖v i a‖ ≤ D)
    {N : ℕ} (block : ℕ → Fin N) (w : ℕ → ℝ) (n : ℕ)
    (hw : ∀ i, |w i| ≤ A / T) (hs : (∑ i ∈ Finset.range n, w i ^ 2) ≤ A ^ 2 / T)
    (batches : ℕ → ℕ) (a : Fin N → ℝ) (branch : Bool)
    (hn : n = ∑ t : Fin N, 2 * batches t)
    (center direction : Ξ → Fin N → H)
    (hxlink : ∀ ζ (j : Fin (∑ t : Fin N, 2 * batches t)),
      x j (fun i => ξ i ζ) = center ζ (batchRecord (fun t : Fin N => 2 * batches t) j).1)
    (hvlink : ∀ ζ (j : Fin (∑ t : Fin N, 2 * batches t)),
      v j (fun i => ξ i ζ) = direction ζ (batchRecord (fun t : Fin N => 2 * batches t) j).1)
    (hwlink : ∀ j : Fin (∑ t : Fin N, 2 * batches t),
      let r := batchRecord (fun t : Fin N => 2 * batches t) j
      block j = r.1 ∧ w j =
        (if (r.2 : ℕ) < batches r.1 then (if branch then a r.1 / batches r.1 else 0)
          else (if branch then 0 else a r.1 / batches r.1))) :
    let τ := M * Real.sqrt (T / ((d : ℝ) * ell))
    let kernel := fun (c : H) (z : S × Ω) => estimate d τ γ (z.1 : H)
      (F (c + γ • (z.1 : H), z.2) + δ (c + γ • (z.1 : H)))
      (F (c - γ • (z.1 : H), z.2) + δ (c - γ • (z.1 : H)))
    let noise := fun ζ (t : Fin N) => (batches t : ℝ)⁻¹ •
      (∑ i : Fin (batches t), (kernel (center ζ t)
        (ξ (2 * (∑ k ∈ Finset.range t, batches k) + ((if branch then 0 else batches t) + i)) ζ) -
          ∫ fresh, kernel (center ζ t) fresh ∂(Q).prod P))
    μ.real {ζ | 8192 * Real.sqrt ((M ^ 2 * A ^ 2 / T) * ((d : ℝ) + ell)) <
        ‖∑ t : Fin N, a t • (PiLp.single 2 t (noise ζ t) : PiLp 2 (fun _ : Fin N => H))‖ ∨
      1280 * (D * Real.sqrt (M ^ 2 * A ^ 2 / T)) * Real.sqrt ell ≤
        ∑ t : Fin N, a t * ⟪noise ζ t, direction ζ t⟫} ≤ 3 * Real.exp (-ell) := by
  have hp := fixed_corruption_record_confidence h_samples hC hUC hFm hG hF hx
    hγ hB hM hA hT hell hU hCU hi hb δ hδm hδ hBM hv hD hvb block w n hw hs
  dsimp only
  apply (measureReal_mono (μ := μ) ?_).trans hp
  intro ζ hζ
  have he := PairedOracleExecution.interleaved_batch_error_identities ((Q).prod P)
    batches a branch (fun i => ξ i ζ)
    (fun (c : H) (z : S × Ω) => estimate d (M * Real.sqrt (T / ((d : ℝ) * ell))) γ (z.1 : H)
      (F (c + γ • (z.1 : H), z.2) + δ (c + γ • (z.1 : H)))
      (F (c - γ • (z.1 : H), z.2) + δ (c - γ • (z.1 : H))))
    x v (center ζ) (direction ζ) block w (hxlink ζ) (hvlink ζ) hwlink
  dsimp only at he
  change _ ∨ _ at hζ ⊢
  rw [hn, he.1, he.2]
  exact hζ

lemma dual_solver_noise_confidence {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ξ → S × Ω}
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ((Q).prod P) μ)
    {F : H × Ω → ℝ} {G : H × Ω → H} {C U : Set H}
    (hC : IsCompact C) (hUC : U ⊆ C) (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    {K : Set H} (hK : Convex ℝ K) {project : H → H}
    (hp : Continuous project) (hproject : ∀ x, project x ∈ K)
    {initial : H × H} (hx0 : initial.1 ∈ K) (hz0 : initial.2 ∈ K)
    {vstar : H} (hvstar : vstar ∈ K)
    {γ₁ γ₂ h B M A T ell Δ D : ℝ} (branch : Bool)
    (hγ : 0 < if branch then γ₁ else γ₂) (hB : 0 ≤ B)
    (hM : 0 < M) (hA : 0 < A) (hT : 0 < T) (hell : 0 < ell) (hD : 0 < D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hU : ∀ x ∈ K, ball x (if branch then γ₁ else γ₂) ⊆ U)
    (hCU : ∀ x ∈ K, closedBall x (if branch then γ₁ else γ₂) ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ζ => ‖G (z, ζ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ζ, ‖G (z, ζ)‖ ^ 2 ∂P) ≤ B)
    (δ : H → ℝ) (hδm : Measurable δ) (hδ : ∀ z ∈ C, |δ z| ≤ Δ)
    (hBM : B + d * (Δ / (if branch then γ₁ else γ₂)) ^ 2 ≤ 2 * M ^ 2)
    {N : ℕ} (hN : 0 < N) (batches : ℕ → ℕ) (a : Fin N → ℝ)
    (hw : ∀ t, |a t / batches t| ≤ A / T)
    (hs : (∑ t : Fin N, (batches t : ℝ) * (a t / batches t) ^ 2) ≤ A ^ 2 / T) :
    let τ := M * Real.sqrt (T / ((d : ℝ) * ell))
    let γ := if branch then γ₁ else γ₂
    let g := fun c ζ => F (c, ζ) + δ c
    let states := fun ζ => dualSolverState d τ τ γ₁ γ₂ h project initial batches
      (fun t i => (ξ (2 * (∑ k ∈ Finset.range t, batches k) + i) ζ).1.val)
      (fun t i => (ξ (2 * (∑ k ∈ Finset.range t, batches k) + batches t + i) ζ).1.val)
      g (fun i => (ξ i ζ).2) 0
    let state := fun ζ t => if branch then (states ζ t).1 else (states ζ t).2
    let center := fun ζ (t : Fin N) => acceleratedMix t (state ζ t).1 (state ζ t).2
    let kernel := fun (c : H) (z : S × Ω) => estimate d τ γ (z.1 : H)
      (g (c + γ • (z.1 : H)) z.2) (g (c - γ • (z.1 : H)) z.2)
    let noise := fun ζ (t : Fin N) => (batches t : ℝ)⁻¹ •
      (∑ i : Fin (batches t), (kernel (center ζ t)
        (ξ (2 * (∑ k ∈ Finset.range t, batches k) + ((if branch then 0 else batches t) + i)) ζ) -
          ∫ fresh, kernel (center ζ t) fresh ∂(Q).prod P))
    μ.real {ζ | 8192 * Real.sqrt ((M ^ 2 * A ^ 2 / T) * ((d : ℝ) + ell)) <
        ‖∑ t : Fin N, a t • (PiLp.single 2 t (noise ζ t) : PiLp 2 (fun _ : Fin N => H))‖ ∨
      1280 * (D * Real.sqrt (M ^ 2 * A ^ 2 / T)) * Real.sqrt ell ≤
        ∑ t : Fin N, a t * ⟪noise ζ t, vstar - (state ζ t).2⟫} ≤ 3 * Real.exp (-ell) := by
  classical
  let τ := M * Real.sqrt (T / ((d : ℝ) * ell))
  let g := fun c ζ => F (c, ζ) + δ c
  have hg : Measurable (fun p : H × Ω => g p.1 p.2) := hFm.add (hδm.comp measurable_fst)
  let fallback : S × Ω := (nonempty_of_isProbabilityMeasure ((Q).prod P)).some
  obtain ⟨x, z, hxm, hzm, hmem, hlink⟩ :=
    PairedOracleExecution.interleaved_predictable_centers hK hp hproject hx0 hz0
      d τ τ γ₁ γ₂ h batches N branch
      (fun r : S × Ω => (r.1 : H)) Prod.snd
      (continuous_subtype_val.measurable.comp measurable_fst) measurable_snd fallback g hg
  obtain ⟨block, w, hwcap, hwsum, hwlink⟩ :=
    PairedOracleExecution.interleaved_schedule_bounds hN (fun t : Fin N => batches t)
      (fun t => a t / batches t) branch (div_nonneg hA.le hT.le) hw hs
  let states := fun ζ => dualSolverState d τ τ γ₁ γ₂ h project initial batches
      (fun t i => (ξ (2 * (∑ k ∈ Finset.range t, batches k) + i) ζ).1.val)
      (fun t i => (ξ (2 * (∑ k ∈ Finset.range t, batches k) + batches t + i) ζ).1.val)
      g (fun i => (ξ i ζ).2) 0
  let state := fun ζ t => if branch then (states ζ t).1 else (states ζ t).2
  let center := fun ζ (t : Fin N) => acceleratedMix t (state ζ t).1 (state ζ t).2
  let direction := fun ζ (t : Fin N) => vstar - (state ζ t).2
  have hxlink (ζ : Ξ) (j : Fin (∑ t : Fin N, 2 * batches t)) :
      x j (fun i => ξ i ζ) = center ζ
        (batchRecord (fun t : Fin N => 2 * batches t) j).1 := by
    exact (hlink j (fun i => ξ i ζ)).1
  have hvlink (ζ : Ξ) (j : Fin (∑ t : Fin N, 2 * batches t)) :
      vstar - z j (fun i => ξ i ζ) = direction ζ
        (batchRecord (fun t : Fin N => 2 * batches t) j).1 := by
    exact congrArg (fun y => vstar - y) (hlink j (fun i => ξ i ζ)).2
  exact fixed_corruption_batch_confidence h_samples hC hUC hFm hG hF hxm
    hγ hB hM hA hT hell (fun i q => hU _ (hmem i q).1)
    (fun i q => hCU _ (hmem i q).1) hi hb δ hδm hδ hBM
    (fun i => measurable_const.sub (hzm i)) hD
    (fun i q => hdiam vstar hvstar _ (hmem i q).2) block w
    (∑ t : Fin N, 2 * batches t) hwcap hwsum batches a branch rfl center direction
    hxlink hvlink hwlink

lemma dual_solver_smoothed_gap_confidence {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {ξ : ℕ → Ξ → S × Ω}
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ((Q).prod P) μ)
    {F : H × Ω → ℝ} {G : H × Ω → H} {C U : Set H}
    (hC : IsCompact C) (hUC : U ⊆ C) (hFm : Measurable F) (hG : Measurable G)
    (hF : ∀ᵐ ξ ∂P, ContinuousOn (fun z => F (z, ξ)) C ∧
      LocallyIntegrableOn (fun z => G (z, ξ)) U volume ∧
      ∀ ψ : H → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
        ∀ v : H, (∫ z, F (z, ξ) * (fderiv ℝ ψ z) v) = -∫ z, ⟪G (z, ξ), v⟫ * ψ z)
    {K : Set H} (hK : Convex ℝ K) {project : H → H}
    (hp : Continuous project) (hproject : ∀ x, project x ∈ K)
    {initial : H × H} (hx0 : initial.1 ∈ K) (hz0 : initial.2 ∈ K)
    {vstar : H} (hvstar : vstar ∈ K)
    {γ₁ γ₂ h B M A T ell Δ D : ℝ} (branch : Bool)
    (hγ : 0 < if branch then γ₁ else γ₂) (hB : 0 ≤ B)
    (hM : 0 < M) (hA : 0 < A) (hT : 0 < T) (hell : 0 < ell) (hD : 0 < D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hU : ∀ x ∈ K, ball x (if branch then γ₁ else γ₂) ⊆ U)
    (hCU : ∀ x ∈ K, closedBall x (if branch then γ₁ else γ₂) ⊆ C)
    (hi : ∀ z ∈ U, Integrable (fun ζ => ‖G (z, ζ)‖ ^ 2) P)
    (hb : ∀ z ∈ U, (∫ ζ, ‖G (z, ζ)‖ ^ 2 ∂P) ≤ B)
    (δ : H → ℝ) (hδm : Measurable δ) (hδ : ∀ z ∈ C, |δ z| ≤ Δ)
    (hBM : B + d * (Δ / (if branch then γ₁ else γ₂)) ^ 2 ≤ 2 * M ^ 2)
    {N : ℕ} (hN : 0 < N) (batches : ℕ → ℕ)
    (hw : ∀ t : Fin N, |(t + 1 : ℝ) / batches t| ≤ A / T)
    (hs : (∑ t : Fin N, (batches t : ℝ) * ((t + 1 : ℝ) / batches t) ^ 2) ≤ A ^ 2 / T)
    (hbatch : ∀ t < N, 0 < batches t) (hΔ : 0 ≤ Δ)
    (population target : H → ℝ) (hfcont : Continuous population)
    (hfi : ∀ x ∈ C, Integrable (fun ζ => F (x, ζ)) P)
    (hfmean : ∀ x ∈ C, (∫ ζ, F (x, ζ) ∂P) = population x)
    {L : ℝ} (hL : 0 ≤ L) (hh : 0 < h) (hcoef : 4 * L ≤ h)
    (hnearest : ∀ x, ‖x - project x‖ = ⨅ w : K, ‖x - w‖)
    (hconvex : ∀ x ∈ K, ∀ y ∈ K,
      target x + ⟪LocalPopulationSmoothing.boundaryField population (if branch then γ₁ else γ₂) x,
        y - x⟫ ≤ target y)
    (hmodel : ∀ x ∈ K, ∀ y ∈ K,
      target y ≤ target x + ⟪LocalPopulationSmoothing.boundaryField population (if branch then γ₁ else γ₂) x,
        y - x⟫ + L / 2 * ‖y - x‖ ^ 2) :
    let τ := M * Real.sqrt (T / ((d : ℝ) * ell))
    let γ := if branch then γ₁ else γ₂
    let g := fun c ζ => F (c, ζ) + δ c
    let states := fun ζ => dualSolverState d τ τ γ₁ γ₂ h project initial batches
      (fun t i => (ξ (2 * (∑ k ∈ Finset.range t, batches k) + i) ζ).1.val)
      (fun t i => (ξ (2 * (∑ k ∈ Finset.range t, batches k) + batches t + i) ζ).1.val)
      g (fun i => (ξ i ζ).2) 0
    let state := fun ζ t => if branch then (states ζ t).1 else (states ζ t).2
    let radius := 8192 * Real.sqrt ((M ^ 2 * A ^ 2 / T) * ((d : ℝ) + ell))
    let β := 15 * B / (Real.sqrt d * τ) + Real.sqrt d * (Δ / γ)
    let comparator := 1280 * (D * Real.sqrt (M ^ 2 * A ^ 2 / T)) * Real.sqrt ell
    μ.real {ζ | h * D ^ 2 / 2 + (radius + ((N : ℝ) * (N + 1) / 2) * β) ^ 2 / h +
      comparator + ((N : ℝ) * (N + 1) / 2) * β * D <
        ((N : ℝ) * (N + 1) / 2) * (target (state ζ N).1 - target vstar)} ≤
      3 * Real.exp (-ell) := by
  classical
  intro τ γ g states state radius β comparator
  let center := fun ζ t => acceleratedMix t (state ζ t).1 (state ζ t).2
  let kernel := fun (c : H) (z : S × Ω) => estimate d τ γ (z.1 : H)
    (g (c + γ • (z.1 : H)) z.2) (g (c - γ • (z.1 : H)) z.2)
  let noise := fun ζ t => (batches t : ℝ)⁻¹ •
    (∑ i : Fin (batches t), (kernel (center ζ t)
      (ξ (2 * (∑ k ∈ Finset.range t, batches k) + ((if branch then 0 else batches t) + i)) ζ) -
        ∫ fresh, kernel (center ζ t) fresh ∂(Q).prod P))
  have hnoise := dual_solver_noise_confidence (h := h) h_samples hC hUC hFm hG hF hK hp hproject
    hx0 hz0 hvstar branch hγ hB hM hA hT hell hD hdiam hU hCU hi hb δ hδm hδ hBM
    hN batches (fun t : Fin N => (t + 1 : ℝ)) hw hs
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hmean (x : H) (hx : x ∈ K) :
      ‖(∫ z, kernel x z ∂(Q).prod P) - LocalPopulationSmoothing.boundaryField population γ x‖ ≤ β :=
    fixed_corruption_population_bias hC hUC hFm hG hF hfcont hfi hfmean x
      hγ hB hτ hΔ (hU x hx) (hCU x hx) hi hb δ hδm hδ
  apply (measureReal_mono (μ := μ) ?_).trans hnoise
  intro ζ hbad
  change _ ∨ _
  by_contra hgood
  have hn : ‖∑ t : Fin N, (t + 1 : ℝ) •
      (PiLp.single 2 t (noise ζ t) : PiLp 2 (fun _ : Fin N => H))‖ ≤ radius :=
    le_of_not_gt (not_or.mp hgood).1
  have hc : (∑ t ∈ Finset.range N, (t + 1 : ℝ) * ⟪noise ζ t, vstar - (state ζ t).2⟫) ≤
      comparator := by
    have hc' := (lt_of_not_ge (not_or.mp hgood).2).le
    rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => (t + 1 : ℝ) * ⟪noise ζ t, vstar - (state ζ t).2⟫)] at hc'
    exact hc'
  have hbound := ClippedTwoPointConvergence.dual_branch_centered_error_bound ((Q).prod P)
    hK hproject hnearest hL hh hcoef hβ hdiam hconvex hmodel hx0 hz0 hvstar
    d τ γ₁ γ₂ batches (fun z : S × Ω => (z.1 : H)) Prod.snd g (fun i => ξ i ζ) N branch
    hbatch hmean hn hc
  exact (not_lt_of_ge hbound) hbad

end LongTails.Proofs.ClippedBatchConcentration
