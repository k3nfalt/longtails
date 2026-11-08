import LongTails.Proofs.BirchNonEuclideanEnergy
import LongTails.Proofs.RingmasterStochastic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BirchNonEuclideanMoments

open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Setups.UscgConstant (dualNorm)
open OracleTemplate.NormBallLMO
open LongTails.Proofs.BirchNonEuclideanEnergy

lemma seminorm_add_sq {d : ℕ} (N : Seminorm ℝ (Point d)) (x y : Point d) :
    N (x + y) ^ 2 ≤ 2 * N x ^ 2 + 2 * N y ^ 2 := by
  have h := (sq_le_sq₀ (apply_nonneg N (x + y))
    (add_nonneg (apply_nonneg N x) (apply_nonneg N y))).mpr (map_add_le_add N x y)
  nlinarith [sq_nonneg (N x - N y)]

lemma seminorm_sq_add_integrable {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    (N : Seminorm ℝ (Point d)) (P : Measure Ξ) (X Y : Ξ → Point d)
    (hX : Measurable X) (hY : Measurable Y)
    (hX2 : Integrable (fun ω => N (X ω) ^ 2) P)
    (hY2 : Integrable (fun ω => N (Y ω) ^ 2) P) :
    Integrable (fun ω => N (X ω + Y ω) ^ 2) P := by
  apply ((hX2.const_mul 2).add (hY2.const_mul 2)).mono'
    (((seminorm_continuous N).measurable.comp (hX.add hY)).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact seminorm_add_sq N _ _)

lemma regular_inner_bound {d : ℕ} {N : Seminorm ℝ (Point d)} {κ : ℝ}
    (w : DualRegularityWitness N κ) (x y : Point d) :
    |inner ℝ (w.derivative x) y| ≤ w.auxiliary x ^ 2 / 2 +
      w.smoothness / 2 * w.auxiliary y ^ 2 := by
  have hp := w.smooth x y
  have hn := w.smooth x (-y)
  rw [map_neg_eq_map, inner_neg_right] at hn
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (w.auxiliary (x + y)),
    sq_nonneg (w.auxiliary (x + -y))]

lemma regular_inner_integrable {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    {N : Seminorm ℝ (Point d)} {κ : ℝ} (w : DualRegularityWitness N κ)
    (P : Measure Ξ) (X Y : Ξ → Point d) (hX : Measurable X) (hY : Measurable Y)
    (hX2 : Integrable (fun ω => w.auxiliary (X ω) ^ 2) P)
    (hY2 : Integrable (fun ω => w.auxiliary (Y ω) ^ 2) P) :
    Integrable (fun ω => inner ℝ (w.derivative (X ω)) (Y ω)) P := by
  apply ((hX2.div_const 2).add (hY2.const_mul (w.smoothness / 2))).mono'
    (((w.derivative_continuous.measurable.comp hX).inner hY).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs]
    exact regular_inner_bound w _ _)

lemma regular_sum_bound {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    {N : Seminorm ℝ (Point d)} {κ R : ℝ} (w : DualRegularityWitness N κ)
    (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (P : Measure Ξ) (X : ℕ → Ξ → Point d)
    (hX : ∀ k, Measurable (X k))
    (hX2 : ∀ k, Integrable (fun ω => dualNorm N (X k ω) ^ 2) P)
    (hmean : ∀ k, (∫ ω, inner ℝ (w.derivative (∑ j ∈ Finset.range k, X j ω)) (X k ω) ∂P) = 0)
    (K : ℕ) :
    Integrable (fun ω => dualNorm N (∑ k ∈ Finset.range K, X k ω) ^ 2) P ∧
      (∫ ω, dualNorm N (∑ k ∈ Finset.range K, X k ω) ^ 2 ∂P) ≤
        κ * ∑ k ∈ Finset.range K, ∫ ω, dualNorm N (X k ω) ^ 2 ∂P := by
  have hspos : 0 < w.smoothness := lt_of_lt_of_le (by norm_num) w.smoothness_lower
  have hXm (k : ℕ) : Integrable (fun ω => w.auxiliary (X k ω) ^ 2) P := by
    apply ((hX2 k).const_mul (κ / w.smoothness)).mono'
      ((w.continuous.measurable.comp (hX k)).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact w.upper _)
  have hSm (k : ℕ) : Measurable (fun ω => ∑ j ∈ Finset.range k, X j ω) := by
    fun_prop
  have hSi (k : ℕ) : Integrable (fun ω => w.auxiliary (∑ j ∈ Finset.range k, X j ω) ^ 2) P := by
    induction k with
    | zero => simp
    | succ k ih =>
        simp only [Finset.sum_range_succ]
        exact seminorm_sq_add_integrable w.auxiliary P _ _ (hSm k) (hX k) ih (hXm k)
  have hbound (k : ℕ) :
      (∫ ω, w.auxiliary (∑ j ∈ Finset.range k, X j ω) ^ 2 ∂P) ≤
        w.smoothness * ∑ j ∈ Finset.range k, ∫ ω, w.auxiliary (X j ω) ^ 2 ∂P := by
    induction k with
    | zero => simp
    | succ k ih =>
        have hi := regular_inner_integrable w P _ _ (hSm k) (hX k) (hSi k) (hXm k)
        have hleft : Integrable (fun ω => (1 / 2 : ℝ) *
            w.auxiliary (∑ j ∈ Finset.range k, X j ω) ^ 2 +
              inner ℝ (w.derivative (∑ j ∈ Finset.range k, X j ω)) (X k ω)) P :=
          ((hSi k).const_mul (1 / 2 : ℝ)).add hi
        have hm := integral_mono ((hSi (k + 1)).const_mul (1 / 2 : ℝ))
          ((((hSi k).const_mul (1 / 2 : ℝ)).add hi).add
            ((hXm k).const_mul (w.smoothness / 2))) (fun ω => by
              simpa only [Finset.sum_range_succ, Pi.add_apply] using
                w.smooth (∑ j ∈ Finset.range k, X j ω) (X k ω))
        simp only [Pi.add_apply] at hm
        rw [integral_const_mul, integral_add hleft
          ((hXm k).const_mul (w.smoothness / 2)),
          integral_add ((hSi k).const_mul (1 / 2 : ℝ)) hi,
          integral_const_mul, integral_const_mul, hmean k] at hm
        rw [Finset.sum_range_succ]
        nlinarith
  have hd : Integrable (fun ω => dualNorm N (∑ k ∈ Finset.range K, X k ω) ^ 2) P := by
    apply (hSi K).mono'
      (((continuous_dualNorm hR hR0).measurable.comp (hSm K)).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact w.lower _)
  refine ⟨hd, (integral_mono hd (hSi K) (fun ω => w.lower _)).trans ((hbound K).trans ?_)⟩
  calc
    w.smoothness * ∑ j ∈ Finset.range K, ∫ ω, w.auxiliary (X j ω) ^ 2 ∂P ≤
        w.smoothness * ∑ j ∈ Finset.range K, κ / w.smoothness *
          ∫ ω, dualNorm N (X j ω) ^ 2 ∂P := by
      apply mul_le_mul_of_nonneg_left _ hspos.le
      apply Finset.sum_le_sum
      intro j _
      have hh := integral_mono (hXm j) ((hX2 j).const_mul (κ / w.smoothness))
        (fun ω => w.upper (X j ω))
      rwa [integral_const_mul] at hh
    _ = κ * ∑ j ∈ Finset.range K, ∫ ω, dualNorm N (X j ω) ^ 2 ∂P := by
      rw [← Finset.mul_sum]
      field_simp

lemma regular_sq_integrable {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]
    {N : Seminorm ℝ (Point d)} {κ : ℝ} (w : DualRegularityWitness N κ)
    (P : Measure Ξ) (X : Ξ → Point d) (hX : Measurable X)
    (hX2 : Integrable (fun ω => dualNorm N (X ω) ^ 2) P) :
    Integrable (fun ω => w.auxiliary (X ω) ^ 2) P := by
  apply (hX2.const_mul (κ / w.smoothness)).mono'
    ((w.continuous.measurable.comp hX).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact w.upper _)

lemma seminorm_sum_sq_integrable {d : ℕ} {Ξ ι : Type*} [MeasurableSpace Ξ]
    (N : Seminorm ℝ (Point d)) (P : Measure Ξ) (s : Finset ι) (X : ι → Ξ → Point d)
    (hX : ∀ i, Measurable (X i)) (hX2 : ∀ i, Integrable (fun ω => N (X i ω) ^ 2) P) :
    Integrable (fun ω => N (∑ i ∈ s, X i ω) ^ 2) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact seminorm_sq_add_integrable N P _ _ (hX i) (by fun_prop) (hX2 i) ih

lemma past_noise_moment {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d)
    (ho : StochasticGradient p (μ : Measure Ω) f g)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (k : ℕ) (Z : (ℕ → Ω) → Point p.d) (hZ : Measurable Z)
    (hpast : ∀ ξ ξ', (∀ j < k, ξ j = ξ' j) → Z ξ = Z ξ') :
    Integrable (fun ξ => dualNorm p.N (g (Z ξ) (ξ k) - gradient f (Z ξ)) ^ 2)
      (P : Measure (ℕ → Ω)) ∧
    (∫ ξ, dualNorm p.N (g (Z ξ) (ξ k) - gradient f (Z ξ)) ^ 2
      ∂(P : Measure (ℕ → Ω))) ≤ p.σ ^ 2 := by
  have hmeas : Measurable (fun z : (ℕ → Ω) × Ω =>
      dualNorm p.N (g (Z z.1) z.2 - gradient f (Z z.1)) ^ 2) :=
    ((continuous_dualNorm hR hR0).measurable.comp
      ((ho.measurable.comp ((hZ.comp measurable_fst).prodMk measurable_snd)).sub
        ((measurable_gradient_space f).comp (hZ.comp measurable_fst)))).pow_const 2
  have hh := OracleTemplate.RingmasterAsgd.step_bound μ P (fun j ξ => ξ j) hiid k
    (fun ξ b => dualNorm p.N (g (Z ξ) b - gradient f (Z ξ)) ^ 2) hmeas
    (fun ξ ξ' b h => by rw [hpast ξ ξ' h])
    (fun _ _ => sq_nonneg _) (fun ξ => ho.variance_integrable (Z ξ))
    (fun _ => p.σ ^ 2) (integrable_const _) (fun ξ => ho.variance (Z ξ))
  simpa using hh

lemma past_noise_inner_zero {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d)
    (ho : StochasticGradient p (μ : Measure Ω) f g)
    (k : ℕ) (c : ℝ) (Z U : (ℕ → Ω) → Point p.d) (hZ : Measurable Z) (hU : Measurable U)
    (hZpast : ∀ ξ ξ', (∀ j < k, ξ j = ξ' j) → Z ξ = Z ξ')
    (hUpast : ∀ ξ ξ', (∀ j < k, ξ j = ξ' j) → U ξ = U ξ')
    (hint : Integrable (fun ξ => inner ℝ (U ξ) (c • (g (Z ξ) (ξ k) - gradient f (Z ξ))))
      (P : Measure (ℕ → Ω))) :
    (∫ ξ, inner ℝ (U ξ) (c • (g (Z ξ) (ξ k) - gradient f (Z ξ)))
      ∂(P : Measure (ℕ → Ω))) = 0 := by
  have hmeas : Measurable (fun z : (ℕ → Ω) × Ω =>
      inner ℝ (U z.1) (c • (g (Z z.1) z.2 - gradient f (Z z.1)))) :=
    (hU.comp measurable_fst).inner
      (((ho.measurable.comp ((hZ.comp measurable_fst).prodMk measurable_snd)).sub
        ((measurable_gradient_space f).comp (hZ.comp measurable_fst))).const_smul c)
  have hh := OracleTemplate.RingmasterAsgd.step_integral μ P (fun j ξ => ξ j) hiid k
    (fun ξ b => inner ℝ (U ξ) (c • (g (Z ξ) b - gradient f (Z ξ)))) hmeas
    (fun ξ ξ' b h => by rw [hZpast ξ ξ' h, hUpast ξ ξ' h])
  rw [hh.2 hint]
  have hzero (ξ : ℕ → Ω) :
      (∫ b, inner ℝ (U ξ) (c • (g (Z ξ) b - gradient f (Z ξ))) ∂(μ : Measure Ω)) = 0 := by
    have hgi : Integrable (fun b => g (Z ξ) b - gradient f (Z ξ)) (μ : Measure Ω) :=
      (ho.integrable (Z ξ)).sub (integrable_const _)
    simp only [inner_smul_right]
    rw [integral_const_mul, integral_inner hgi,
      integral_sub (ho.integrable (Z ξ)) (integrable_const _), ho.unbiased (Z ξ)]
    simp
  simp only [hzero, integral_zero]

lemma iid_indexed_noise_bound {Ω : Type} [MeasurableSpace Ω] (p : Params)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d)
    (ho : StochasticGradient p (μ : Measure Ω) f g)
    (w : DualRegularityWitness p.N p.κ)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (index : ℕ → ℕ) (Z : ℕ → (ℕ → Ω) → Point p.d) (hZ : ∀ k, Measurable (Z k))
    (hpast : ∀ k ξ ξ', (∀ j < index k, ξ j = ξ' j) → Z k ξ = Z k ξ')
    (c : ℕ → ℝ) (hindex : ∀ j k, j < k → c j ≠ 0 → c k ≠ 0 → index j < index k) (K : ℕ) :
    Integrable (fun ξ => dualNorm p.N (∑ k ∈ Finset.range K,
      c k • (g (Z k ξ) (ξ (index k)) - gradient f (Z k ξ))) ^ 2) (P : Measure (ℕ → Ω)) ∧
    (∫ ξ, dualNorm p.N (∑ k ∈ Finset.range K,
      c k • (g (Z k ξ) (ξ (index k)) - gradient f (Z k ξ))) ^ 2 ∂(P : Measure (ℕ → Ω))) ≤
      p.κ * p.σ ^ 2 * ∑ k ∈ Finset.range K, c k ^ 2 := by
  let X : ℕ → (ℕ → Ω) → Point p.d := fun k ξ =>
    c k • (g (Z k ξ) (ξ (index k)) - gradient f (Z k ξ))
  have hXm (k : ℕ) : Measurable (X k) :=
    ((ho.measurable.comp ((hZ k).prodMk (measurable_pi_apply (index k)))).sub
      ((measurable_gradient_space f).comp (hZ k))).const_smul (c k)
  have hXi (k : ℕ) : Integrable (fun ξ => dualNorm p.N (X k ξ) ^ 2) (P : Measure (ℕ → Ω)) ∧
      (∫ ξ, dualNorm p.N (X k ξ) ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ c k ^ 2 * p.σ ^ 2 := by
    obtain ⟨hi, hb⟩ := past_noise_moment p μ P hiid f g ho hR hR0 (index k) (Z k) (hZ k) (hpast k)
    have hdom (ξ : ℕ → Ω) : dualNorm p.N (X k ξ) ^ 2 ≤
        c k ^ 2 * dualNorm p.N (g (Z k ξ) (ξ (index k)) - gradient f (Z k ξ)) ^ 2 := by
      have hh := (sq_le_sq₀ (dualNorm_nonneg hR (X k ξ))
        (mul_nonneg (abs_nonneg (c k)) (dualNorm_nonneg hR _))).mpr
        (dualNorm_smul_le hR (c k) (g (Z k ξ) (ξ (index k)) - gradient f (Z k ξ)))
      simpa only [mul_pow, sq_abs] using hh
    have hI : Integrable (fun ξ => dualNorm p.N (X k ξ) ^ 2) (P : Measure (ℕ → Ω)) := by
      apply (hi.const_mul (c k ^ 2)).mono'
        (((continuous_dualNorm hR hR0).measurable.comp (hXm k)).pow_const 2).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hdom ξ)
    refine ⟨hI, ?_⟩
    have hh := integral_mono hI (hi.const_mul (c k ^ 2)) hdom
    rw [integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hb (sq_nonneg _))
  have haux (k : ℕ) : Integrable (fun ξ => w.auxiliary (X k ξ) ^ 2) (P : Measure (ℕ → Ω)) :=
    regular_sq_integrable w _ (X k) (hXm k) (hXi k).1
  have hmean (k : ℕ) : (∫ ξ, inner ℝ (w.derivative (∑ j ∈ Finset.range k, X j ξ))
      (X k ξ) ∂(P : Measure (ℕ → Ω))) = 0 := by
    by_cases hc : c k = 0
    · simp [X, hc]
    apply past_noise_inner_zero p μ P hiid f g ho (index k) (c k) (Z k)
      (fun ξ => w.derivative (∑ j ∈ Finset.range k, X j ξ)) (hZ k)
      (w.derivative_continuous.measurable.comp (by fun_prop)) (hpast k)
    · intro ξ ξ' hh
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjk := Finset.mem_range.mp hj
      by_cases hcj : c j = 0
      · simp [X, hcj]
      have hij := hindex j k hjk hcj hc
      dsimp only [X]
      rw [hpast j ξ ξ' (fun i hi => hh i (hi.trans hij)), hh (index j) hij]
    · exact regular_inner_integrable w _ _ _ (by fun_prop) (hXm k)
        (seminorm_sum_sq_integrable w.auxiliary _ _ X hXm haux) (haux k)
  obtain ⟨hi, hb⟩ := regular_sum_bound w hR hR0 (P : Measure (ℕ → Ω)) X hXm
    (fun k => (hXi k).1) hmean K
  refine ⟨hi, hb.trans ?_⟩
  have hκ : 0 ≤ p.κ := (show (0 : ℝ) ≤ 1 by norm_num).trans
    (w.smoothness_lower.trans w.smoothness_upper)
  calc
    p.κ * ∑ j ∈ Finset.range K, ∫ ξ, dualNorm p.N (X j ξ) ^ 2 ∂(P : Measure (ℕ → Ω)) ≤
        p.κ * ∑ j ∈ Finset.range K, c j ^ 2 * p.σ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => (hXi j).2)) hκ
    _ = p.κ * p.σ ^ 2 * ∑ j ∈ Finset.range K, c j ^ 2 := by
      rw [← Finset.sum_mul]
      ring

end LongTails.Proofs.BirchNonEuclideanMoments
