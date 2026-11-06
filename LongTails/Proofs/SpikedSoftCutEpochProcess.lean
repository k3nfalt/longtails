import LongTails.Proofs.SpikedSoftCutMethodExecution
import LongTails.Proofs.SoftCutPredictableBatches
import LongTails.Proofs.SpikedSoftCutCoordinates
import LongTails.Proofs.SoftCutBatchConcentration
import LongTails.Proofs.StratifiedSubGaussianSampling

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpikedSoftCutEpochProcess

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut
open LongTails.Algorithms.SpikedSoftCutMethod
open CovarianceSoftCutProcess
open CovarianceSoftCutTrajectory
open SpikedSoftCutMethodExecution


noncomputable def innerOracle (q : Params) (a : ℝ) (g : Space q → q.Ω → Space q)
    (y : InnerSpace q) (ω : q.Ω) : InnerSpace q := tail q (g (join q a y) ω)

noncomputable def innerSeedPoint (q : Params) (c : Config) (a : ℝ)
    (g : Space q → q.Ω → Space q) (t : ℕ) (ξ : ℕ → q.Ω) : InnerSpace q :=
  samplePoint (innerParams q c.α) c.α (2/c.α) c.b (innerOracle q a g) t ξ

noncomputable def innerSeedReplies (q : Params) (c : Config) (a : ℝ)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (i : ℕ) : Space q :=
  g (join q a (innerSeedPoint q c a g (i/c.b) ξ)) (ξ i)

noncomputable def epochReplies (q : Params) (c : Config) (k : ℕ) (state : OuterState q)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (i : ℕ) : Space q :=
  if i < c.T*c.b then innerSeedReplies q c (center q state) g ξ i
  else g (scalarQuery q c k state (innerSeedReplies q c (center q state) g ξ) (i-c.T*c.b)) (ξ i)

lemma innerSeedReplies_tail (q : Params) (c : Config) (a : ℝ)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) :
    (fun i => tail q (innerSeedReplies q c a g ξ i)) =
      sampleReplies (innerParams q c.α) c.α (2/c.α) c.b (innerOracle q a g) ξ := rfl

lemma innerSeedPoint_generator (q : Params) (c : Config) (hb : 0 < c.b) (a : ℝ)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (t : ℕ) :
    innerSeedPoint q c a g t ξ = LongTails.Algorithms.CovarianceSoftCut.generatorPoint
      (innerParams q c.α) c.α (2/c.α) c.b t (fun i => tail q (innerSeedReplies q c a g ξ i)) := by
  exact samplePoint_eq_generatorPoint (innerParams q c.α) c.α (2/c.α) c.b hb (innerOracle q a g) ξ t

lemma epochReplies_inner_prefix (q : Params) (c : Config) (k : ℕ) (state : OuterState q)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (i : ℕ) (hi : i < c.T*c.b) :
    epochReplies q c k state g ξ i = innerSeedReplies q c (center q state) g ξ i := by
  simp only [epochReplies, ite_eq_left hi]

lemma epochReplies_response (q : Params) (c : Config) (hb : 0 < c.b)
    (k : ℕ) (state : OuterState q) (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω)
    (i : ℕ) (hi : i < epochCost c k) :
    g (queryFrom q c k 1 state (epochReplies q c k state g ξ) i) (ξ i) =
      epochReplies q c k state g ξ i := by
  by_cases hg : i < c.T*c.b
  · simp only [queryFrom, hg, ite_true, epochReplies_inner_prefix q c k state g ξ i hg]
    unfold innerSeedReplies
    rw [innerSeedPoint_generator q c hb]
    congr 2
    apply generatorPoint_eq_of_prefix
    intro j hj
    apply congrArg (tail q)
    exact epochReplies_inner_prefix q c k state g ξ j
      (lt_of_lt_of_le hj ((Nat.div_mul_le_self i c.b).trans hg.le))
  · have hre : epochReplies q c k state g ξ i =
        g (scalarQuery q c k state (innerSeedReplies q c (center q state) g ξ) (i-c.T*c.b)) (ξ i) := by
      simp only [epochReplies, ite_eq_right hg]
    rw [hre]
    simp only [queryFrom, hg, ite_false, hi, ite_true]
    rw [scalarQuery_prefix q c k state (epochReplies q c k state g ξ)
      (innerSeedReplies q c (center q state) g ξ)
      (epochReplies_inner_prefix q c k state g ξ)]

lemma innerSeedPoint_seed_prefix (q : Params) (c : Config) (a : ℝ)
    (g : Space q → q.Ω → Space q) (t : ℕ) (ξ ζ : ℕ → q.Ω)
    (h : ∀ i, i < t*c.b → ξ i = ζ i) :
    innerSeedPoint q c a g t ξ = innerSeedPoint q c a g t ζ := by
  unfold innerSeedPoint samplePoint
  rw [sampleCuts_eq_of_prefix (innerParams q c.α) c.α (2/c.α) c.b t (innerOracle q a g) ξ ζ h]

lemma innerSeedReplies_seed_prefix (q : Params) (c : Config) (a : ℝ)
    (g : Space q → q.Ω → Space q) (N : ℕ) (ξ ζ : ℕ → q.Ω)
    (h : ∀ i, i < N → ξ i = ζ i) (i : ℕ) (hi : i < N) :
    innerSeedReplies q c a g ξ i = innerSeedReplies q c a g ζ i := by
  unfold innerSeedReplies
  rw [h i hi, innerSeedPoint_seed_prefix q c a g (i/c.b) ξ ζ
    (fun j hj => h j (lt_of_le_of_lt (le_trans hj.le (Nat.div_mul_le_self i c.b)) hi))]

lemma scalarEstimate_epochReplies (q : Params) (c : Config) (k : ℕ) (state : OuterState q)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) :
    let r := innerSeedReplies q c (center q state) g ξ
    scalarEstimate q c k (epochReplies q c k state g ξ) =
      ∑ i : Fin c.T, weights q c r i / sampleCount q c k r i *
        ∑ j ∈ Finset.range (sampleCount q c k r i),
          head q (g (join q (center q state) (supportPoints q c r i))
            (ξ (c.T*c.b+sampleStart q c k r i+j))) := by
  dsimp only
  let r := innerSeedReplies q c (center q state) g ξ
  have hp := epochReplies_inner_prefix q c k state g ξ
  unfold scalarEstimate
  rw [weights_prefix q c _ r hp, sampleCount_prefix q c k _ r hp, sampleStart_prefix q c k _ r hp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hnot : ¬ c.T*c.b+sampleStart q c k r i+j < c.T*c.b := by omega
  have hsub : c.T*c.b+sampleStart q c k r i+j-c.T*c.b = sampleStart q c k r i+j := by omega
  unfold epochReplies
  rw [ite_eq_right hnot, hsub, scalarQuery_at_sample q c k state r i j (Finset.mem_range.mp hj)]

lemma measurable_innerOracle (q : Params) (a : ℝ) (g : Space q → q.Ω → Space q)
    (hg : Measurable (Function.uncurry g)) : Measurable (Function.uncurry (innerOracle q a g)) := by
  have hx : Measurable (fun z : InnerSpace q × q.Ω => join q a z.1) :=
    (SpikedSoftCutCoordinates.continuous_join q).measurable.comp (measurable_const.prodMk measurable_fst)
  exact (SpikedSoftCutCoordinates.continuous_tail q).measurable.comp
    (hg.comp (hx.prodMk measurable_snd))

lemma innerOracle_directional_mgf (q : Params) (a : ℝ) (p : Measure q.Ω)
    [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsSubGaussianSubgradient q p f v g)
    (x u : InnerSpace q) (t : ℝ) :
    Integrable (fun ω => Real.exp (t*⟪innerOracle q a g x ω-tail q (v (join q a x)), u⟫)) p ∧
    (∫ ω, Real.exp (t*⟪innerOracle q a g x ω-tail q (v (join q a x)), u⟫) ∂p) ≤
      Real.exp (q.vRest*‖u‖^2*t^2/2) := by
  have hh := SpikedSoftCutCoordinates.tail_direction_exp q p f v g hg (join q a x) u t
  simp only [SpikedSoftCutCoordinates.tail_sub] at hh
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  congr 1
  ring

lemma measurable_innerMean (q : Params) (a : ℝ) (p : Measure q.Ω)
    [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsSubGaussianSubgradient q p f v g) :
    Measurable (fun x : InnerSpace q => tail q (v (join q a x))) :=
  (SpikedSoftCutCoordinates.continuous_tail q).measurable.comp
    ((SpikedSoftCutCoordinates.measurable_mean q p f v g hg).comp
      ((SpikedSoftCutCoordinates.continuous_join q).measurable.comp (measurable_const.prodMk measurable_id)))

noncomputable def innerErrorMatrix (q : Params) (c : Config) (a : ℝ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (ξ : ℕ → q.Ω) :
    EuclideanSpace ℝ (Fin c.T) →L[ℝ] InnerSpace q :=
  SubGaussianNetProbability.columnOperator (fun i : Fin c.T =>
    SoftCutPredictableBatches.batchError (innerParams q c.α) c.α (2/c.α) c.b
      (innerOracle q a g) (fun x => tail q (v (join q a x))) i ξ)

noncomputable def innerErrorIntercept (q : Params) (c : Config) (a : ℝ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (ξ : ℕ → q.Ω) :
    EuclideanSpace ℝ (Fin c.T) :=
  WithLp.toLp 2 (fun i : Fin c.T =>
    ⟪SoftCutPredictableBatches.batchError (innerParams q c.α) c.α (2/c.α) c.b
      (innerOracle q a g) (fun x => tail q (v (join q a x))) i ξ,
      innerSeedPoint q c a g i ξ⟫)

lemma inner_error_probability {Ξ : Type*} [MeasurableSpace Ξ]
    (q : Params) (c : Config) (a : ℝ) (hR : 0 < q.R) (hb : 0 < c.b) (hrest : 0 ≤ q.vRest)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : Measure Ξ) [IsProbabilityMeasure P]
    (ξ : ℕ → Ξ → q.Ω) (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) (ν ρ : ℝ)
    (hν : 0 < ν) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hvariance : q.vRest/(c.b : ℝ) ≤ ν) :
    let S := (q.m : ℝ)*Real.log (16*(q.m : ℝ)+1) +
      (c.T : ℝ)*Real.log (16*(c.T : ℝ)+1) + Real.log (4/ρ)
    P.real {ω | 128*ν*S < ‖innerErrorMatrix q c a g v (fun j => ξ j ω)‖^2 ∨
      128*ν*q.R^2*S < ‖innerErrorIntercept q c a g v (fun j => ξ j ω)‖^2} ≤ ρ := by
  classical
  let z : q.Ω := Classical.choice (nonempty_of_isProbabilityMeasure p)
  let qp : LongTails.Setups.CovarianceBoundedConvex.Params :=
    { d := q.m, Ω := q.Ω, L := q.G, R := q.R/2, σ := 0, ε := c.α }
  have hRp : 0 < (innerParams q c.α).R := by dsimp [innerParams]; positivity
  have hgm := measurable_innerOracle q a g hg.measurable
  have hvm := measurable_innerMean q a p f v g hg
  apply SubGaussianNetProbability.joint_net_square_tail q.m c.T
    (fun ω => innerErrorMatrix q c a g v (fun j => ξ j ω))
    (fun ω => innerErrorIntercept q c a g v (fun j => ξ j ω)) ν q.R ρ hν hR hρ hρ1
  · intro u hu w hw
    have hh := SoftCutBatchConcentration.batch_matrix_mgf qp hRp c.α (2/c.α) c.b hb
      (innerOracle q a g) (fun x => tail q (v (join q a x))) hgm hvm p P ξ
      hξ.measurable hξ.independent hξ.marginal z q.vRest hrest
      (innerOracle_directional_mgf q a p f v g hg) c.T u w
      (EuclideanGridNet.grid_norm c.T u hu) (EuclideanGridNet.grid_norm q.m w hw)
    apply StratifiedSubGaussianSampling.weaken_proxy hh
    change 16*q.vRest/(c.b : ℝ) ≤ 16*ν
    calc
      16*q.vRest/(c.b : ℝ) = 16*(q.vRest/(c.b : ℝ)) := by ring
      _ ≤ 16*ν := mul_le_mul_of_nonneg_left hvariance (by norm_num)
  · intro u hu
    have hh := SoftCutBatchConcentration.batch_intercept_mgf qp hRp c.α (2/c.α) c.b hb
      (innerOracle q a g) (fun x => tail q (v (join q a x))) hgm hvm p P ξ
      hξ.measurable hξ.independent hξ.marginal z q.vRest hrest
      (innerOracle_directional_mgf q a p f v g hg) c.T u (EuclideanGridNet.grid_norm c.T u hu)
    apply StratifiedSubGaussianSampling.weaken_proxy hh
    change 16*q.vRest*(q.R/2)^2/(c.b : ℝ) ≤ 16*ν*q.R^2
    calc
      16*q.vRest*(q.R/2)^2/(c.b : ℝ) = 4*(q.vRest/(c.b : ℝ))*q.R^2 := by ring
      _ ≤ 4*ν*q.R^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hvariance (by norm_num)) (sq_nonneg q.R)
      _ ≤ 16*ν*q.R^2 := by nlinarith [mul_nonneg hν.le (sq_nonneg q.R)]

end LongTails.Proofs.SpikedSoftCutEpochProcess
