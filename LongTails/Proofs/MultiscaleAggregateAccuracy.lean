import LongTails.Proofs.MultiscaleAggregateConvergence

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MultiscaleAggregateAccuracy

open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultiscaleAggregate
open MultiscaleAggregateHistory MultiscaleAggregateTrajectory MultiscaleAggregateBudget
open MultiscaleAggregateSampling MultiscaleAggregateCodec MultiscaleAggregateConvergence

variable {p : Params}

lemma average_gradient (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun j (s : Samples p) => s i j) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hh : ∀ i, 0 < p.h i) (hε : 0 < p.ε)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hL : 0 < p.L) (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x)
    (hgap : objective p f p.x0 - lower ≤ p.Δ) :
    (∑ k ∈ Finset.range (rounds p), ∫ s, ‖gradient (objective p f) (point g s k)‖ ∂P) ≤
      (rounds p : ℝ) * p.ε := by
  let F := objective p f
  let η := precision p / p.L
  let loss := fun k => ∫ s, F (point g s k) ∂P
  let grad := fun k => ∫ s, ‖gradient F (point g s k)‖ ∂P
  have hp := precision_pos hε
  have hη : 0 < η := div_pos hp hL
  have hgrad (x) : HasGradientAt F (gradient F x) x := by
    rw [(objective_gradient f hg x).gradient]
    exact objective_gradient f hg x
  have hm := fun i => (hsg i).measurable
  have hfi (k) : Integrable (fun s => F (point g s k)) P :=
    image_integrable P g hm (fun m => F m.point) k
  have hgi (k) : Integrable (fun s => ‖gradient F (point g s k)‖) P :=
    image_integrable P g hm (fun m => ‖gradient F m.point‖) k
  have hs (k) (hk : k < rounds p) :
      η * grad k ≤ loss k - loss (k + 1) + 397 * η * precision p := by
    let err := fun s => ‖estimate g s k - gradient F (point g s k)‖
    have hE : Integrable err P ∧ (∫ s, err s ∂P) ≤ 198 * precision p :=
      estimate_mean_error P μ hw hIID g f hsg hg hh hε hlip hL lower hlower hgap k hk
    have hdiff : Integrable (fun s => F (point g s k) - η * ‖gradient F (point g s k)‖) P :=
      (hfi k).sub ((hgi k).const_mul _)
    have hadd : Integrable (fun s => F (point g s k) - η * ‖gradient F (point g s k)‖ +
        2 * η * err s) P := hdiff.add (hE.1.const_mul _)
    have hd (s) := HeavyTailedSospDescent.normalized_step_descent hL.le hη.le hgrad hlip
      (point g s k) (estimate g s k)
    have hStep (s) : F (point g s (k + 1)) ≤ F (point g s k) - η * ‖gradient F (point g s k)‖ +
        2 * η * err s + p.L * η ^ 2 / 2 := by
      rw [point_succ]
      simpa only [OracleTemplate.NormalizedStorm.stormStep, η, div_eq_mul_inv, smul_smul,
        norm_sub_rev (gradient F (point g s k)), err] using hd s
    have ht := integral_mono (hfi (k + 1)) (hadd.add (integrable_const (p.L * η ^ 2 / 2))) hStep
    simp only [Pi.add_apply] at ht
    rw [integral_add hadd (integrable_const _), integral_add hdiff (hE.1.const_mul _),
      integral_sub (hfi k) ((hgi k).const_mul _), integral_const_mul, integral_const_mul,
      integral_const, probReal_univ, one_smul] at ht
    have hhη : p.L * η = precision p := by dsimp [η]; field_simp
    dsimp only [loss, grad]
    nlinarith [mul_le_mul_of_nonneg_left hE.2 hη.le,
      congrArg (fun x : ℝ => x * η) hhη, mul_nonneg hη.le hp.le]
  have hsum (k : ℕ) (hk : k ≤ rounds p) :
      η * ∑ j ∈ Finset.range k, grad j ≤ loss 0 - loss k + k * (397 * η * precision p) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, Nat.cast_succ]
      linarith [ih (by omega), hs k (by omega)]
  have hlast : lower ≤ loss (rounds p) := by
    have h := integral_mono (integrable_const (μ := P) lower) (hfi (rounds p))
      (fun s => hlower (point g s (rounds p)))
    simpa [loss] using h
  have hzero : loss 0 = F p.x0 := by simp [loss, point, trajectory, initialModel]
  have h := hsum (rounds p) le_rfl
  rw [hzero] at h
  have hK := (div_le_iff₀ (sq_pos_of_pos hp)).mp (round_count_lower (p := p))
  have hgap' : p.Δ ≤ (rounds p : ℝ) * η * precision p := by
    dsimp [η]
    field_simp
    nlinarith [mul_nonneg (show 0 ≤ (rounds p : ℝ) by positivity) (sq_nonneg (precision p))]
  change (∑ k ∈ Finset.range (rounds p), grad k) ≤ _
  apply le_of_mul_le_mul_left (a := η) _ hη
  change F p.x0 - lower ≤ p.Δ at hgap
  have he : p.ε = 512 * precision p := by dsimp [precision]; ring
  rw [he]
  nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ (rounds p : ℝ) by positivity) hη.le) hp.le]

lemma output_integral (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (g : Fin p.n → Point p → p.Ω → Point p) (hm : ∀ i, Measurable (Function.uncurry (g i)))
    (F : Point p → ℝ)
    (h : (∑ k ∈ Finset.range (rounds p), ∫ s, ‖gradient F (point g s k)‖ ∂P) ≤ (rounds p : ℝ) * p.ε)
    [NeZero (rounds p)] :
    let Q := (PMF.uniformOfFintype (Indices p)).toMeasure.prod P
    Measurable (output p g) ∧ Integrable (fun seed => ‖gradient F (output p g seed)‖) Q ∧
      (∫ seed, ‖gradient F (output p g seed)‖ ∂Q) ≤ p.ε := by
  let Q := (PMF.uniformOfFintype (Indices p)).toMeasure.prod P
  have hmeas {E : Type} [MeasurableSpace E] (φ : Point p → E) :
      Measurable (fun seed => φ (output p g seed)) := by
    apply measurable_from_prod_countable_right
    intro i
    exact measurable_trajectory_image p g hm i.val (fun m => φ m.point)
  have hfinite (φ : Point p → ℝ) : (Set.range (fun seed => φ (output p g seed))).Finite := by
    apply (Set.finite_iUnion (fun i : Indices p =>
      finite_trajectory_image p g i.val (fun m => φ m.point))).subset
    rintro _ ⟨⟨i, s⟩, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, s, rfl⟩
  have hI := DistributedBatchedSgd.integrable_finite_range Q _
    (hmeas (fun x => ‖gradient F x‖)) (hfinite (fun x => ‖gradient F x‖))
  refine ⟨hmeas id, hI, ?_⟩
  change (∫ seed, ‖gradient F (output p g seed)‖ ∂Q) ≤ _
  rw [integral_prod _ hI, integral_fintype hI.integral_prod_left]
  have hmass (i : Indices p) : (PMF.uniformOfFintype (Indices p)).toMeasure.real {i} =
      1 / (rounds p : ℝ) := by
    simp [measureReal_def, PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _), Indices]
  simp only [hmass, smul_eq_mul, ← Finset.mul_sum, output]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫ s, ‖gradient F (point g s k)‖ ∂P)]
  have hr : (0 : ℝ) < rounds p := by exact_mod_cast Nat.two_pow_pos (depth p)
  field_simp
  simpa [mul_comm] using h

end LongTails.Proofs.MultiscaleAggregateAccuracy
