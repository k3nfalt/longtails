import LongTails.Proofs.SpikedSoftCutFreshness
import LongTails.Proofs.SpikedSoftCutEpochCertificate

open MeasureTheory

namespace LongTails.Proofs.SpikedSoftCutEvents

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut
open LongTails.Algorithms.SpikedSoftCutMethod
open SpikedSoftCutEpochProcess
open SpikedSoftCutFreshness

noncomputable def netEntropy (q : Params) (c : Config) (ρ : ℝ) : ℝ :=
  (q.m : ℝ)*Real.log (16*(q.m : ℝ)+1)+(c.T : ℝ)*Real.log (16*(c.T : ℝ)+1)+Real.log (4/ρ)

noncomputable def badEpoch (q : Params) (c : Config) (ν ρ r : ℝ) (k : ℕ)
    (s : OuterState q) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (ξ : ℕ → q.Ω) : Prop :=
  (128*ν*netEntropy q c ρ < ‖innerErrorMatrix q c (center q s) g v ξ‖^2 ∨
    128*ν*q.R^2*netEntropy q c ρ < ‖innerErrorIntercept q c (center q s) g v ξ‖^2) ∨
      q.ε/(8*r) < |epochScalarError q c k s g v ξ|

lemma measurableSet_badEpoch (q : Params) (c : Config) (hR : 0 < q.R)
    (ν ρ r : ℝ) (k : ℕ) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) :
    MeasurableSet {z : OuterState q × (ℕ → q.Ω) | badEpoch q c ν ρ r k z.1 g v z.2} := by
  have harg : Measurable (fun z : OuterState q × (ℕ → q.Ω) => (center q z.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hm := (measurable_innerErrorMatrix q c hR g v hg hv).comp harg
  have hi := (measurable_innerErrorIntercept q c hR g v hg hv).comp harg
  have hs := measurable_epochScalarError q c hR k g v hg hv
  exact ((measurableSet_lt measurable_const (hm.norm.pow_const 2)).union
    (measurableSet_lt measurable_const (hi.norm.pow_const 2))).union
    (measurableSet_lt measurable_const (continuous_abs.measurable.comp hs))

lemma badEpoch_probability (q : Params) (c : Config) (hR : 0 < q.R)
    (hT : 0 < c.T) (hb : 0 < c.b) (hn : 0 < c.n) (k : ℕ) (hN : 0 < c.N k)
    (state : OuterState q) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) (hrest : 0 ≤ q.vRest) (hTop : 0 ≤ q.vTop)
    (ν ρ r K : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hvariance : q.vRest/(c.b : ℝ) ≤ ν) (hε : 0 < q.ε) (hr : 0 < r) (hK : 1 ≤ K)
    (hscalar : q.vTop/(c.N k : ℝ) ≤ q.ε^2/(8192*K*r^2)) :
    (Measure.infinitePi fun _ : ℕ => p).real {ξ | badEpoch q c ν ρ r k state g v ξ} ≤ ρ+1/(128*K) := by
  let P := Measure.infinitePi fun _ : ℕ => p
  let : IsProbabilityMeasure P := inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ => p))
  have hi := inner_error_probability q c (center q state) hR hb hrest p P (fun j ξ => ξ j)
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p) f v g hg ν ρ hν hρ hρ1 hvariance
  have hs := epoch_scalar_probability q c hR hT hn k hN state p f v g hg hTop r K hε hr hK hscalar
  have hu := measureReal_union_le (μ := P)
    {ξ | 128*ν*netEntropy q c ρ < ‖innerErrorMatrix q c (center q state) g v ξ‖^2 ∨
      128*ν*q.R^2*netEntropy q c ρ < ‖innerErrorIntercept q c (center q state) g v ξ‖^2}
    {ξ | q.ε/(8*r) < |epochScalarError q c k state g v ξ|}
  exact hu.trans (add_le_add hi hs)

lemma epochReplies_seed_prefix (q : Params) (c : Config) (k : ℕ) (state : OuterState q)
    (g : Space q → q.Ω → Space q) (ξ ζ : ℕ → q.Ω)
    (h : ∀ i, i < epochCost c k → ξ i = ζ i) :
    ∀ i, i < epochCost c k → epochReplies q c k state g ξ i = epochReplies q c k state g ζ i := by
  have hinner : ∀ i, i < c.T*c.b →
      innerSeedReplies q c (center q state) g ξ i = innerSeedReplies q c (center q state) g ζ i := by
    intro i hi
    apply innerSeedReplies_seed_prefix q c (center q state) g (epochCost c k) ξ ζ h i
    unfold epochCost
    omega
  intro i hi
  by_cases hg : i < c.T*c.b
  · simp only [epochReplies, hg, ite_true]
    exact hinner i hg
  · simp only [epochReplies, hg, ite_false]
    rw [SpikedSoftCutMethodExecution.scalarQuery_prefix q c k state _ _ hinner, h i hi]

lemma epochScalarError_seed_prefix (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (k : ℕ) (state : OuterState q) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (ξ ζ : ℕ → q.Ω) (h : ∀ i, i < epochCost c k → ξ i = ζ i) :
    epochScalarError q c k state g v ξ = epochScalarError q c k state g v ζ := by
  have hi : ∀ i, i < c.T*c.b →
      innerSeedReplies q c (center q state) g ξ i = innerSeedReplies q c (center q state) g ζ i := by
    intro i hi
    apply innerSeedReplies_seed_prefix q c (center q state) g (epochCost c k) ξ ζ h i
    unfold epochCost
    omega
  unfold epochScalarError
  rw [SpikedSoftCutMethodExecution.scalarEstimate_prefix q c hT hn k _ _ (epochReplies_seed_prefix q c k state g ξ ζ h),
    headSlope_prefix q c (center q state) v _ _ hi]

lemma inner_batch_error_seed_prefix (q : Params) (c : Config) (hb : 0 < c.b) (a : ℝ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (ξ ζ : ℕ → q.Ω)
    (h : ∀ i, i < c.T*c.b → ξ i = ζ i) (i : Fin c.T) :
    SoftCutPredictableBatches.batchError (innerParams q c.α) c.α (2/c.α) c.b
      (innerOracle q a g) (fun x => tail q (v (join q a x))) i ξ =
    SoftCutPredictableBatches.batchError (innerParams q c.α) c.α (2/c.α) c.b
      (innerOracle q a g) (fun x => tail q (v (join q a x))) i ζ := by
  have hi := innerSeedReplies_seed_prefix q c a g (c.T*c.b) ξ ζ h
  rw [← SpikedSoftCutEpochCertificate.seeded_inner_errors q c hb a g v ξ i,
    ← SpikedSoftCutEpochCertificate.seeded_inner_errors q c hb a g v ζ i]
  have he := SpikedSoftCutMethodExecution.innerEstimates_prefix q c _ _ hi
  have hp := SpikedSoftCutMethodExecution.supportPoints_prefix q c _ _ hi
  unfold supportPoints at hp
  rw [he, hp]

lemma innerErrorMatrix_seed_prefix (q : Params) (c : Config) (hb : 0 < c.b) (a : ℝ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (ξ ζ : ℕ → q.Ω)
    (h : ∀ i, i < c.T*c.b → ξ i = ζ i) :
    innerErrorMatrix q c a g v ξ = innerErrorMatrix q c a g v ζ := by
  unfold innerErrorMatrix
  apply congrArg SubGaussianNetProbability.columnOperator
  funext i
  exact inner_batch_error_seed_prefix q c hb a g v ξ ζ h i

lemma innerErrorIntercept_seed_prefix (q : Params) (c : Config) (hb : 0 < c.b) (a : ℝ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (ξ ζ : ℕ → q.Ω)
    (h : ∀ i, i < c.T*c.b → ξ i = ζ i) :
    innerErrorIntercept q c a g v ξ = innerErrorIntercept q c a g v ζ := by
  unfold innerErrorIntercept
  apply congrArg (WithLp.toLp 2)
  funext i
  rw [inner_batch_error_seed_prefix q c hb a g v ξ ζ h i,
    innerSeedPoint_seed_prefix q c a g i ξ ζ]
  intro j hj
  exact h j (lt_of_lt_of_le hj (Nat.mul_le_mul_right c.b i.isLt.le))

lemma badEpoch_seed_prefix (q : Params) (c : Config) (hT : 0 < c.T) (hb : 0 < c.b) (hn : 0 < c.n)
    (ν ρ r : ℝ) (k : ℕ) (state : OuterState q)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (ξ ζ : ℕ → q.Ω)
    (h : ∀ i, i < epochCost c k → ξ i = ζ i) :
    badEpoch q c ν ρ r k state g v ξ ↔ badEpoch q c ν ρ r k state g v ζ := by
  have hi : ∀ i, i < c.T*c.b → ξ i = ζ i := by
    intro i hi
    apply h
    unfold epochCost
    omega
  unfold badEpoch
  rw [innerErrorMatrix_seed_prefix q c hb (center q state) g v ξ ζ hi,
    innerErrorIntercept_seed_prefix q c hb (center q state) g v ξ ζ hi,
    epochScalarError_seed_prefix q c hT hn k state g v ξ ζ h]

noncomputable def badIndicator (q : Params) (c : Config) (ν ρ r : ℝ) (k : ℕ)
    (s : OuterState q) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (z : q.Ω) (n : ℕ) (b : Fin n → q.Ω) : ℝ := by
  classical
  exact if badEpoch q c ν ρ r k s g v (SoftCutPredictableBatches.prefixStream z n b) then 1 else 0

lemma badIndicator_bounds (q : Params) (c : Config) (ν ρ r : ℝ) (k : ℕ)
    (s : OuterState q) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (z : q.Ω) (n : ℕ) (b : Fin n → q.Ω) :
    0 ≤ badIndicator q c ν ρ r k s g v z n b ∧ badIndicator q c ν ρ r k s g v z n b ≤ 1 := by
  unfold badIndicator
  split <;> norm_num

lemma measurable_badIndicator (q : Params) (c : Config) (hR : 0 < q.R)
    (ν ρ r : ℝ) (k : ℕ) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) (z : q.Ω) (n : ℕ) :
    Measurable (fun x : OuterState q × (Fin n → q.Ω) => badIndicator q c ν ρ r k x.1 g v z n x.2) := by
  have hm : Measurable (fun x : OuterState q × (Fin n → q.Ω) =>
      (x.1, SoftCutPredictableBatches.prefixStream z n x.2)) :=
    measurable_fst.prodMk ((SoftCutPredictableBatches.measurable_prefixStream z n).comp measurable_snd)
  have hE := hm (measurableSet_badEpoch q c hR ν ρ r k g v hg hv)
  exact Measurable.ite hE measurable_const measurable_const

lemma badIndicator_integrable (q : Params) (c : Config) (hR : 0 < q.R)
    (ν ρ r : ℝ) (k : ℕ) (state : OuterState q) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) (z : q.Ω) (n : ℕ)
    (p : Measure q.Ω) [IsProbabilityMeasure p] :
    Integrable (badIndicator q c ν ρ r k state g v z n) (Measure.pi fun _ : Fin n => p) := by
  have hm := (measurable_badIndicator q c hR ν ρ r k g v hg hv z n).comp
    (show Measurable (fun b : Fin n → q.Ω => (state,b)) from measurable_prodMk_left)
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro b
  have hb := badIndicator_bounds q c ν ρ r k state g v z n b
  change |badIndicator q c ν ρ r k state g v z n b| ≤ 1
  rw [abs_of_nonneg hb.1]
  exact hb.2

lemma badIndicator_mean (q : Params) (c : Config) (hR : 0 < q.R)
    (hT : 0 < c.T) (hb : 0 < c.b) (hn : 0 < c.n)
    (ν ρ r δ : ℝ) (k : ℕ) (state : OuterState q) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) (z : q.Ω)
    (p : Measure q.Ω) [IsProbabilityMeasure p]
    (hprob : (Measure.infinitePi fun _ : ℕ => p).real {ξ | badEpoch q c ν ρ r k state g v ξ} ≤ δ) :
    (∫ b, badIndicator q c ν ρ r k state g v z (epochCost c k) b
      ∂Measure.pi (fun _ : Fin (epochCost c k) => p)) ≤ δ := by
  let E : Set (Fin (epochCost c k) → q.Ω) :=
    {b | badEpoch q c ν ρ r k state g v (SoftCutPredictableBatches.prefixStream z (epochCost c k) b)}
  have hm : Measurable (fun b : Fin (epochCost c k) → q.Ω =>
      (state, SoftCutPredictableBatches.prefixStream z (epochCost c k) b)) :=
    measurable_const.prodMk (SoftCutPredictableBatches.measurable_prefixStream z (epochCost c k))
  have hE : MeasurableSet E := hm (measurableSet_badEpoch q c hR ν ρ r k g v hg hv)
  have heq : (fun ξ : ℕ → q.Ω => fun i : Fin (epochCost c k) => ξ i) ⁻¹' E =
      {ξ | badEpoch q c ν ρ r k state g v ξ} := by
    ext ξ
    apply badEpoch_seed_prefix q c hT hb hn ν ρ r k state g v _ ξ
    intro i hi
    simp only [SoftCutPredictableBatches.prefixStream, hi, dite_true]
  have hp := (OracleTemplate.StochasticGeneralized.prefix_preserving p (epochCost c k)).measureReal_preimage hE.nullMeasurableSet
  rw [heq] at hp
  have he : badIndicator q c ν ρ r k state g v z (epochCost c k) = E.indicator (fun _ => (1 : ℝ)) := by
    funext b
    rfl
  rw [he, integral_indicator_const (1 : ℝ) hE]
  simpa only [smul_eq_mul, mul_one, ← hp] using hprob

lemma tuned_badEpoch_probability (q : Params) (hG : 0 < q.G) (hR : 0 < q.R)
    (hε : 0 < q.ε) (hrest : 0 ≤ q.vRest) (horder : q.vRest ≤ q.vTop)
    (k : ℕ) (state : OuterState q) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) :
    (Measure.infinitePi fun _ : ℕ => p).real {ξ |
      badEpoch q (tunedConfig q) (q.ε^2/(2^31*q.R^2*SpikedSoftCutTuning.logScale q))
        (1/(100*((tunedConfig q).K : ℝ))) (q.R*(5/8 : ℝ)^k) k state g v ξ} ≤
      1/(50*((tunedConfig q).K : ℝ)) := by
  have hc := SpikedSoftCutTuning.tunedConfig_positive q hG hR hε
  have hK : 1 ≤ ((tunedConfig q).K : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hc.2.2.2.2.1
  have hKp : 0 < ((tunedConfig q).K : ℝ) := by linarith
  have hQ := SpikedSoftCutTuning.logScale_ge_one q hG hR hε
  have hQp : 0 < SpikedSoftCutTuning.logScale q := by linarith
  have hν : 0 < q.ε^2/(2^31*q.R^2*SpikedSoftCutTuning.logScale q) := by positivity
  have hρ : 0 < 1/(100*((tunedConfig q).K : ℝ)) := by positivity
  have hρ1 : 1/(100*((tunedConfig q).K : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hv : q.vRest/((tunedConfig q).b : ℝ) ≤ q.ε^2/(2^31*q.R^2*SpikedSoftCutTuning.logScale q) :=
    SpikedSoftCutTuning.batch_proxy_envelope q.vRest q.R q.ε (SpikedSoftCutTuning.logScale q) hR hε hQp
  have hh := badEpoch_probability q (tunedConfig q) hR hc.2.1 hc.2.2.1 hc.2.2.2.1 k (hc.2.2.2.2.2 k)
    state p f v g hg hrest (hrest.trans horder) _ _ _ ((tunedConfig q).K : ℝ) hν hρ hρ1 hv hε
    (by positivity) hK (SpikedSoftCutTuning.tuned_scalar_variance q hG hR hε k)
  apply hh.trans
  have he : 1/(100*((tunedConfig q).K : ℝ))+1/(128*((tunedConfig q).K : ℝ)) =
      (57/3200 : ℝ)/((tunedConfig q).K : ℝ) := by ring
  rw [he]
  apply (div_le_div_iff₀ hKp (by positivity)).mpr
  nlinarith

end LongTails.Proofs.SpikedSoftCutEvents
