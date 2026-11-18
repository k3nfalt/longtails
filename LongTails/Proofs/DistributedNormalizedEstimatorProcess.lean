import LongTails.Proofs.DistributedNormalizedEstimator

open MeasureTheory

namespace LongTails.Proofs.DistributedNormalizedEstimatorProcess

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink
open LongTails.Algorithms.DistributedNormalizedCompression
open DistributedNormalizedEstimator
open DistributedNormalizedBlocks
open DistributedNormalizedAdaptive

lemma uplinkCodec_norm (p : Params) (cfg : Config) (x : Point p) (θ : ℕ → Fin p.d × ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hx : ‖x‖ ≤ B) (hs : 0 < cfg.uplinkSpacing)
    (hcap : (if cfg.fullUplink then 1 else (p.d : ℝ)) * B ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    ‖uplinkCodec p cfg x θ‖ ≤ ((p.d : ℝ) + 1) * (B + cfg.uplinkSpacing) := by
  cases h : cfg.fullUplink
  · simp only [h, Bool.false_eq_true, ↓reduceIte] at hcap
    have hc (j : Fin p.d) : |(p.d : ℝ) * x j| ≤ cfg.uplinkSpacing *
        (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg p.d)]
      have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
      exact (mul_le_mul_of_nonneg_left (hj.trans hx) (Nat.cast_nonneg p.d)).trans hcap
    have ht := DistributedNormalizedCompression.sparse_message_norm cfg.uplinkWidth cfg.uplinkCount
      cfg.uplinkCount.pos hs x (fun j => (θ j.val).1) (fun j => (θ j.val).2) [] hc
    simp only [List.append_nil] at ht
    unfold uplinkCodec
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    apply ht.trans
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hx hd, mul_nonneg hd hs.le]
  · simp only [h, ↓reduceIte, one_mul] at hcap
    have hc (j : Fin p.d) : |x j| ≤ cfg.uplinkSpacing *
        (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1) := by
      have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j
      exact (hj.trans hx).trans hcap
    have ht := DistributedNormalizedCompression.full_message_error_sq p.d cfg.uplinkWidth hs x
      (fun j => (θ j.val).2) [] hc
    simp only [List.append_nil] at ht
    have he : ‖uplinkCodec p cfg x θ - x‖ ^ 2 ≤ p.d * cfg.uplinkSpacing ^ 2 := by
      simpa only [uplinkCodec, h, ↓reduceIte] using ht
    have hnorm : ‖uplinkCodec p cfg x θ - x‖ ≤ ((p.d : ℝ) + 1) * cfg.uplinkSpacing := by
      have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
      have hsq : (p.d : ℝ) * cfg.uplinkSpacing ^ 2 ≤
          (((p.d : ℝ) + 1) * cfg.uplinkSpacing) ^ 2 := by
        nlinarith [sq_nonneg ((p.d : ℝ) * cfg.uplinkSpacing), mul_nonneg hd (sq_nonneg cfg.uplinkSpacing)]
      have hpos : 0 ≤ ((p.d : ℝ) + 1) * cfg.uplinkSpacing := by positivity
      nlinarith [he.trans hsq, norm_nonneg (uplinkCodec p cfg x θ - x)]
    have htri := norm_le_norm_add_norm_sub x (uplinkCodec p cfg x θ)
    rw [norm_sub_rev x] at htri
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    nlinarith [mul_nonneg hd hB]

lemma workerReply_norm (p : Params) (cfg : Config) (g : Point p → p.Ω → Point p)
    (x : Point p) (z : (Fin cfg.batch → p.Ω) × (ℕ → Fin p.d × ℝ))
    (hB : 0 ≤ cfg.clipRadius) (hs : 0 < cfg.uplinkSpacing)
    (hcap : (if cfg.fullUplink then 1 else (p.d : ℝ)) * cfg.clipRadius ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    ‖workerReply p cfg g x z‖ ≤ ((p.d : ℝ) + 1) * (cfg.clipRadius + cfg.uplinkSpacing) := by
  apply uplinkCodec_norm p cfg _ _ cfg.clipRadius hB _ hs hcap
  exact OracleTemplate.norm_clip_le hB _

lemma roundEstimator_norm (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (x : Fin p.n → Point p)
    (z : RoundBlock p cfg) (hB : 0 ≤ cfg.clipRadius) (hs : 0 < cfg.uplinkSpacing)
    (hcap : (if cfg.fullUplink then 1 else (p.d : ℝ)) * cfg.clipRadius ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    ‖roundEstimator p cfg g x z‖ ≤ ((p.d : ℝ) + 1) * (cfg.clipRadius + cfg.uplinkSpacing) := by
  unfold roundEstimator
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (p.n : ℝ)⁻¹ * ∑ i, ‖workerReply p cfg (g i) (x i) (z.1 i, z.2.1 i)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (p.n : ℝ)⁻¹ * ∑ _i : Fin p.n, ((p.d : ℝ) + 1) * (cfg.clipRadius + cfg.uplinkSpacing) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => workerReply_norm p cfg (g i) (x i)
        (z.1 i, z.2.1 i) hB hs hcap) (by positivity)
    _ = _ := by
      have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

attribute [local irreducible] roundEstimator workerReply uplinkCodec finiteBatch

set_option maxHeartbeats 800000 in
lemma estimator_prefix_integral (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (f : Point p → ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (hgrad : Measurable (gradient f))
    (k : ℕ) (S : (ℕ → RoundBlock p cfg) → State p) (hS : Measurable S)
    (hdep : ∀ ξ ξ' : ℕ → RoundBlock p cfg, (∀ j, j < k → ξ j = ξ' j) → S ξ = S ξ')
    (G : ℝ) (hG : ∀ ξ, ‖gradient f (S ξ).1‖ ≤ G)
    (hB : 0 ≤ cfg.clipRadius) (hs : 0 < cfg.uplinkSpacing)
    (hcap : (if cfg.fullUplink then 1 else (p.d : ℝ)) * cfg.clipRadius ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1)) :
    let Q := (roundLaw p cfg μ : Measure (RoundBlock p cfg))
    let P := Measure.infinitePi fun _ : ℕ => Q
    Integrable (fun ξ => ‖roundEstimator p cfg g (S ξ).2 (ξ k) - gradient f (S ξ).1‖) P ∧
      (∫ ξ, ‖roundEstimator p cfg g (S ξ).2 (ξ k) - gradient f (S ξ).1‖ ∂P) =
        ∫ ξ, (∫ z, ‖roundEstimator p cfg g (S ξ).2 z - gradient f (S ξ).1‖ ∂Q) ∂P := by
  intro Q P
  let Φ : State p → RoundBlock p cfg → ℝ := fun s z => ‖roundEstimator p cfg g s.2 z - gradient f s.1‖
  have he : Measurable (fun z : State p × RoundBlock p cfg => roundEstimator p cfg g z.1.2 z.2) :=
    (measurable_roundEstimator_joint p cfg g hg).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hΦ : Measurable (Function.uncurry Φ) :=
    (he.sub (hgrad.comp (measurable_fst.comp measurable_fst))).norm
  have hmap : Measurable (fun ξ : ℕ → RoundBlock p cfg => ((S ξ).2, ξ k)) :=
    (measurable_snd.comp hS).prodMk (measurable_pi_apply k)
  have hest : Measurable (fun ξ : ℕ → RoundBlock p cfg => roundEstimator p cfg g (S ξ).2 (ξ k)) :=
    (measurable_roundEstimator_joint p cfg g hg).comp hmap
  have hgradS : Measurable (fun ξ : ℕ → RoundBlock p cfg => gradient f (S ξ).1) :=
    hgrad.comp (measurable_fst.comp hS)
  have hm : Measurable (fun ξ : ℕ → RoundBlock p cfg => Φ (S ξ) (ξ k)) :=
    (hest.sub hgradS).norm
  have hi : Integrable (fun ξ : ℕ → RoundBlock p cfg => Φ (S ξ) (ξ k)) P := by
    apply (integrable_const (((p.d : ℝ) + 1) * (cfg.clipRadius + cfg.uplinkSpacing) + G)).mono' hm.aestronglyMeasurable
    filter_upwards [] with ξ
    simp only [Φ, norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add
      (roundEstimator_norm p cfg g (S ξ).2 (ξ k) hB hs hcap) (hG ξ))
  exact ⟨hi, OracleTemplate.TwoSidedPL.integral_prefix_dep (Y := State p) (Ω := RoundBlock p cfg) Q k S hS hdep Φ hΦ hi⟩

lemma integral_sqrt_bound {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (T : Z → ℝ) (hT : Measurable T) (hT0 : ∀ z, 0 ≤ T z) (hTi : Integrable T P)
    {V : ℝ} (hV : (∫ z, T z ∂P) ≤ V) :
    Integrable (fun z => Real.sqrt (T z)) P ∧
      (∫ z, Real.sqrt (T z) ∂P) ≤ Real.sqrt V := by
  have hm : Measurable (fun z => Real.sqrt (T z)) := Real.continuous_sqrt.measurable.comp hT
  have he (z : Z) : ‖Real.sqrt (T z)‖ ^ 2 = T z := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hT0 z)]
  have h2 : Integrable (fun z => ‖Real.sqrt (T z)‖ ^ 2) P := by simpa only [he] using hTi
  have hi : Integrable (fun z => Real.sqrt (T z)) P :=
    ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr h2).integrable (by norm_num)
  have hb := OracleTemplate.NormalizedStorm.integral_norm_le_sqrt hm.aestronglyMeasurable h2
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hT0 _)] at hb
  exact ⟨hi, hb.trans (Real.sqrt_le_sqrt hV)⟩

lemma trace_error_bound {Z : Type*} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (p : Params) (S : Z → State p) (hS : Measurable S) {V : ℝ}
    (hE2 : ∀ i, Integrable (fun z => ‖workerError p i (S z)‖ ^ 2) P)
    (hV : ∀ i, (∫ z, ‖workerError p i (S z)‖ ^ 2 ∂P) ≤ V) :
    Integrable (fun z => Real.sqrt (DistributedNormalizedDrift.traceError p (S z))) P ∧
      (∫ z, Real.sqrt (DistributedNormalizedDrift.traceError p (S z)) ∂P) ≤ Real.sqrt V := by
  have hm : Measurable (fun z => DistributedNormalizedDrift.traceError p (S z)) :=
    (DistributedNormalizedDrift.measurable_traceError p).comp hS
  have h0 (z : Z) : 0 ≤ DistributedNormalizedDrift.traceError p (S z) := by
    unfold DistributedNormalizedDrift.traceError
    positivity
  have hi : Integrable (fun z => DistributedNormalizedDrift.traceError p (S z)) P :=
    (integrable_finsetSum Finset.univ (fun i _ => hE2 i)).const_mul (p.n : ℝ)⁻¹
  apply integral_sqrt_bound P (fun z => DistributedNormalizedDrift.traceError p (S z)) hm h0 hi
  simp only [DistributedNormalizedDrift.traceError]
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hE2 i)]
  calc
    _ ≤ (p.n : ℝ)⁻¹ * ∑ _i : Fin p.n, V :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hV i) (by positivity)
    _ = _ := by
      have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

set_option maxHeartbeats 800000 in
lemma expected_estimator_error (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (f : Point p → ℝ)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) p.Ω (μ i) f (g i) p.σ)
    (k : ℕ) (S : (ℕ → RoundBlock p cfg) → State p) (hS : Measurable S)
    (hdep : ∀ ξ ξ' : ℕ → RoundBlock p cfg, (∀ j, j < k → ξ j = ξ' j) → S ξ = S ξ')
    (G a L V D : ℝ) (hG : 0 ≤ G) (ha : 0 < a) (hL : 0 ≤ L)
    (hroot : ∀ ξ, ‖gradient f (S ξ).1‖ ≤ G)
    (hworkers : ∀ ξ i, ‖gradient f ((S ξ).2 i)‖ ≤ G)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hclip : cfg.clipRadius = G + a) (hs : 0 < cfg.uplinkSpacing)
    (hcap : (if cfg.fullUplink then 1 else (p.d : ℝ)) * (G + a) ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hE2 : ∀ i, Integrable (fun ξ => ‖workerError p i (S ξ)‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg))))
    (hV : ∀ i, (∫ ξ, ‖workerError p i (S ξ)‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg)))) ≤ V)
    (hDi : Integrable (fun ξ => ‖DistributedNormalizedDrift.disagreement p (gradient f) (S ξ)‖)
      (Measure.infinitePi fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg))))
    (hD : (∫ ξ, ‖DistributedNormalizedDrift.disagreement p (gradient f) (S ξ)‖
      ∂Measure.infinitePi (fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg)))) ≤ D) :
    let P := Measure.infinitePi fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg))
    Integrable (fun ξ => ‖roundEstimator p cfg g (S ξ).2 (ξ k) - gradient f (S ξ).1‖) P ∧
      (∫ ξ, ‖roundEstimator p cfg g (S ξ).2 (ξ k) - gradient f (S ξ).1‖ ∂P) ≤
        Real.sqrt (2 * relativeVariance p cfg / p.n) * (∫ ξ, ‖gradient f (S ξ).1‖ ∂P) +
        L * Real.sqrt (2 * relativeVariance p cfg / p.n) * Real.sqrt V + D +
        (Real.sqrt ((1 + relativeVariance p cfg) * (p.σ ^ 2 / cfg.batch) / p.n) +
          Real.sqrt (gridVariance p cfg / p.n) + (p.σ ^ 2 / cfg.batch) / (4 * a)) := by
  intro P
  have hgc : LipschitzWith ⟨L, hL⟩ (gradient f) := lipschitzWith_iff_norm_sub_le.mpr hlip
  have hB : 0 ≤ cfg.clipRadius := by rw [hclip]; positivity
  have hc : (if cfg.fullUplink then 1 else (p.d : ℝ)) * cfg.clipRadius ≤ cfg.uplinkSpacing *
      (((2 ^ cfg.uplinkWidth - 1 : ℕ) : ℝ) / 2 - 1) := by simpa only [hclip] using hcap
  obtain ⟨hi, he⟩ := estimator_prefix_integral p cfg μ f g (fun i => (hg i).measurable)
    hgc.continuous.measurable k S hS hdep G hroot hB hs hc
  have hgi : Integrable (fun ξ => ‖gradient f (S ξ).1‖) P := by
    apply Integrable.of_bound (hgc.continuous.measurable.comp (measurable_fst.comp hS)).norm.aestronglyMeasurable G
    filter_upwards [] with ξ
    simpa only [norm_norm, Function.comp_def] using hroot ξ
  obtain ⟨hsi, hsv⟩ := trace_error_bound P p S hS hE2 hV
  let β := Real.sqrt (2 * relativeVariance p cfg / p.n)
  let C := Real.sqrt ((1 + relativeVariance p cfg) * (p.σ ^ 2 / cfg.batch) / p.n) +
    Real.sqrt (gridVariance p cfg / p.n) + (p.σ ^ 2 / cfg.batch) / (4 * a)
  have h12 : Integrable (fun ξ => β * ‖gradient f (S ξ).1‖ +
      (L * β) * Real.sqrt (DistributedNormalizedDrift.traceError p (S ξ))) P :=
    (hgi.const_mul β).add (hsi.const_mul (L * β))
  have h123 : Integrable (fun ξ => β * ‖gradient f (S ξ).1‖ +
      (L * β) * Real.sqrt (DistributedNormalizedDrift.traceError p (S ξ)) +
      ‖DistributedNormalizedDrift.disagreement p (gradient f) (S ξ)‖) P := h12.add hDi
  have hW : Integrable (fun ξ => β * ‖gradient f (S ξ).1‖ +
      (L * β) * Real.sqrt (DistributedNormalizedDrift.traceError p (S ξ)) +
      ‖DistributedNormalizedDrift.disagreement p (gradient f) (S ξ)‖ + C) P :=
    h123.add (integrable_const C)
  refine ⟨hi, ?_⟩
  rw [he]
  have hb : (∫ ξ, (∫ z, ‖roundEstimator p cfg g (S ξ).2 z - gradient f (S ξ).1‖
      ∂(roundLaw p cfg μ : Measure (RoundBlock p cfg))) ∂P) ≤
      ∫ ξ, (β * ‖gradient f (S ξ).1‖ +
        (L * β) * Real.sqrt (DistributedNormalizedDrift.traceError p (S ξ)) +
        ‖DistributedNormalizedDrift.disagreement p (gradient f) (S ξ)‖ + C) ∂P :=
    integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ξ => integral_nonneg fun _ => norm_nonneg _) hW
    (Filter.Eventually.of_forall fun ξ => by
      have ht := (conditional_norm_error p cfg μ f g hg (S ξ) G a L hG ha hL
        (hworkers ξ) hlip hclip hs hcap).2
      dsimp only [β, C]
      linarith)
  rw [integral_add h123 (integrable_const C), integral_add h12 hDi,
    integral_add (hgi.const_mul β) (hsi.const_mul (L * β)),
    integral_const_mul, integral_const_mul, integral_const] at hb
  simp only [probReal_univ, one_smul] at hb
  have hv := mul_le_mul_of_nonneg_left hsv (mul_nonneg hL (Real.sqrt_nonneg (2 * relativeVariance p cfg / p.n)))
  exact hb.trans (add_le_add (add_le_add (add_le_add le_rfl hv) hD) le_rfl)

end LongTails.Proofs.DistributedNormalizedEstimatorProcess
