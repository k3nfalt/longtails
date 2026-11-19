import LongTails.Proofs.WeightedInterpolationAllocation

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.WeightedInterpolationBatch

open MeasureTheory ProbabilityTheory
open LongTails.Setups.DistributedWeakInterpolation
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.WeightedInterpolationSgd LongTails.Algorithms.WeakInterpolationDesign

variable {p : Params}

local notation "B" => Algorithms.DistributedBatchedSgd.batchMean
local notation "raw" => rawParams p

noncomputable def quantizer (p : Params) (T : DistributedTemplate.Time) (x v : Point p) : Point p :=
  Algorithms.DistributedBatchedSgd.decode (rawParams p) (rawConfig p T) x
    (Algorithms.DistributedBatchedSgd.encode (rawParams p) (rawConfig p T) x v)

noncomputable def errorRadius (p : Params) (T : DistributedTemplate.Time) (x : Point p) : ℝ :=
  Real.sqrt (p.d * Algorithms.DistributedBatchedSgd.spacing (rawParams p) (rawConfig p T) x ^ 2)

noncomputable def localMean (p : Params) (k : ℕ) (f : Functions p) (x : Point p) (i : Fin p.n) : Point p :=
  (stepSize p k * weights p i / fraction p i) • gradient (f i) x

noncomputable def message (p : Params) (T : DistributedTemplate.Time) (k : ℕ) (g : LocalOracle p)
    (x : Point p) (i : Fin p.n) (s : Samples p) := quantizer p T x
      (Algorithms.DistributedBatchedSgd.batchMean (rawParams p) (rawConfig p T) (scaled p g k) x 0 s i)

lemma quantizer_error (hp : spec.valid p) (T : DistributedTemplate.Time) (x v : Point p) :
    ‖quantizer p T x v - OracleTemplate.clip (Algorithms.DistributedBatchedSgd.radius raw x) v‖ ≤
      errorRadius p T x :=
  Real.le_sqrt_of_sq_le (DistributedBatchedSgd.encoding_error (rawConfig p T) (by change (0:ℝ) ≤ 1; norm_num)
    hp.2.2.2.2.2.2 x v)

private lemma measurable_roundtrip (q : LongTails.Setups.DistributedSmoothNonconvex.Params)
    (cfg : Algorithms.DistributedBatchedSgd.Config q) (x : LongTails.Setups.DistributedSmoothNonconvex.Point q) :
    Measurable (fun v => Algorithms.DistributedBatchedSgd.decode q cfg x (Algorithms.DistributedBatchedSgd.encode q cfg x v)) := by
  have h := (DistributedBatchedSgd.measurable_encoded_gradient cfg).comp
    ((measurable_const : Measurable (fun _ : LongTails.Setups.DistributedSmoothNonconvex.Point q => x)).prodMk measurable_id)
  simpa only [Function.comp_def, id_eq] using h

lemma measurable_quantizer (T : DistributedTemplate.Time) (x : Point p) : Measurable (quantizer p T x) :=
  measurable_roundtrip raw (rawConfig p T) x

lemma measurable_scaled (g : LocalOracle p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (k : ℕ) (i : Fin p.n) : Measurable (Function.uncurry (scaled p g k i)) :=
  (hg i).fun_const_smul _

lemma message_moments (hp : spec.valid p) (T : DistributedTemplate.Time) (k : ℕ)
    (g : LocalOracle p) (f : Functions p) (x : Point p)
    (P : Measure (Samples p)) (ν : Fin p.n → ProbabilityMeasure p.Ω)
    (hi : ∀ i, IID (fun j (s : Samples p) => s i j) (ν i : Measure _) P)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (ν i) (f i) (g i) p.σ)
    (i : Fin p.n) (hu : ‖localMean p k f x i‖ < Algorithms.DistributedBatchedSgd.radius raw x) :
    let Q := message p T k g x i
    let u := localMean p k f x i
    let a := stepSize p k * weights p i / fraction p i
    let V := (a * p.σ) ^ 2 / batch p i
    let δ := errorRadius p T x
    Integrable Q P ∧ Integrable (fun s => ‖Q s - u‖^2) P ∧
      (∫ s, ‖Q s - u‖^2 ∂P) ≤ 2 * V + 2 * δ^2 ∧
      ‖(∫ s, Q s ∂P) - u‖ ≤ V / (Algorithms.DistributedBatchedSgd.radius raw x - ‖u‖) + δ := by
  let b := batch p i
  let a := stepSize p k * weights p i / fraction p i
  let u := gradient (f i) x
  let Z := fun ω => a • g i x ω
  let μ := (ν i : Measure p.Ω)
  have hm : Measurable Z := ((hsg i).measurable.comp measurable_prodMk_left).fun_const_smul _
  have hiZ : Integrable Z μ := ((hsg i).integrable x).fun_smul _
  have hZ : ∫ ω, Z ω ∂μ = a • u := by simp [Z, μ, u, integral_smul, (hsg i).unbiased x]
  have he (ω) : ‖Z ω - a • u‖ ^ 2 = a^2 * ‖g i x ω - u‖ ^ 2 := by
    simp only [Z, ← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hiE : Integrable (fun ω => ‖Z ω - a • u‖^2) μ := by
    simp_rw [he]; exact ((hsg i).variance_integrable x).const_mul _
  have hV : ∫ ω, ‖Z ω - a • u‖^2 ∂μ ≤ (a * p.σ)^2 := by
    simp_rw [he, integral_const_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left ((hsg i).variance x) (sq_nonneg _)
  let mean := fun ξ : Fin b → p.Ω => (1 / (b : ℝ)) • ∑ j, Z (ξ j)
  have hb : 0 < b := WeightedInterpolationAllocation.batch_pos p i
  obtain ⟨hmi,hmean⟩ := OracleTemplate.LightTail.finite_mean_integral hiZ b hb
  obtain ⟨hmi2,hvar⟩ := OracleTemplate.RobustGradient.finite_mean_variance hm hiZ (a • u) hiE hZ b hb
  have hmm : Measurable mean :=
    (Finset.measurable_sum _ (fun j _ => hm.comp (measurable_pi_apply j))).fun_const_smul _
  have hcontrol := DistributedBatchedSgd.quantized_gradient_control (p := raw)
    (Measure.pi (fun _ : Fin b => μ)) (Algorithms.DistributedBatchedSgd.radius raw x)
    (errorRadius p T x) ((a * p.σ)^2 / b) (a • u) hu (Real.sqrt_nonneg _)
    mean hmm hmi hmi2 (hmean.trans hZ)
    (hvar.trans_le (div_le_div_of_nonneg_right hV (Nat.cast_nonneg _)))
    (quantizer p T x) (measurable_quantizer T x) (quantizer_error hp T x)
  obtain ⟨hI,hI2,hE,hbias⟩ := hcontrol
  have law := DistributedSampling.worker_batch_law raw (rawConfig p T) P ν hi 0 i
  have heq (s : Samples p) :
      quantizer p T x (mean (fun j => s i (0 * (rawConfig p T).batch i + j.val))) = message p T k g x i s := by
    unfold mean message Algorithms.DistributedBatchedSgd.batchMean
    simp only [one_div]
    apply congrArg (quantizer p T x)
    apply congrArg (fun y : Point p => (b : ℝ)⁻¹ • y)
    exact Fin.sum_univ_eq_sum_range (fun j => Z (s i (0 * batch p i + j))) b
  have h1 := law.integrable_comp hI
  have h2 := law.integrable_comp hI2
  have h3 := law.integral_comp hI2.aestronglyMeasurable
  have h4 := law.integral_comp hI.aestronglyMeasurable
  simp only [Function.comp_def] at h1 h2 h3 h4
  dsimp only
  rw [show message p T k g x i = _ from funext (fun s => (heq s).symm)]
  exact ⟨h1,h2,h3.trans_le hE,(congrArg (fun z : Point p => ‖z - a • u‖) h4).trans_le hbias⟩

end LongTails.Proofs.WeightedInterpolationBatch
