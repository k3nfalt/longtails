import LongTails.Proofs.MuonDescent
import LongTails.Proofs.RingmasterStochastic
import LongTails.Setups.StochasticSmoothAndConvex

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.Muon

variable {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]

theorem noise_sq (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Mat m n → ℝ) (g : Mat m n → Ω → Mat m n) (σ : ℝ)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat m n) Ω (μ : Measure Ω) f g σ)
    (hgm : Measurable (gradient f)) (k : ℕ) (Y : (ℕ → Ω) → Mat m n) (hYm : Measurable Y)
    (hYk : ∀ s s', (∀ j < k, s j = s' j) → Y s = Y s') :
    Integrable (fun s => ‖g (Y s) (s k) - gradient f (Y s)‖ ^ 2) (P : Measure (ℕ → Ω)) ∧
      (∫ s, ‖g (Y s) (s k) - gradient f (Y s)‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ σ ^ 2 := by
  let Φ : (ℕ → Ω) → Ω → ℝ := fun s b => ‖g (Y s) b - gradient f (Y s)‖ ^ 2
  have hΦ : Measurable (Function.uncurry Φ) :=
    ((ho.measurable.comp ((hYm.comp measurable_fst).prodMk measurable_snd)).sub
      (hgm.comp (hYm.comp measurable_fst))).norm.pow_const 2
  have h := RingmasterAsgd.step_bound μ P (fun k (s : ℕ → Ω) => s k) hiid k Φ hΦ
    (fun s s' b h => by simp only [Φ]; rw [hYk s s' h]) (fun _ _ => sq_nonneg _)
    (fun s => ho.variance_integrable (Y s)) (fun _ => σ ^ 2) (integrable_const _)
    (fun s => ho.variance (Y s))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  exact h

theorem noise_cross (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Mat m n → ℝ) (g : Mat m n → Ω → Mat m n) (σ : ℝ)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat m n) Ω (μ : Measure Ω) f g σ)
    (hgm : Measurable (gradient f)) (k : ℕ) (X Y : (ℕ → Ω) → Mat m n) (hXm : Measurable X)
    (hYm : Measurable Y) (hXk : ∀ s s', (∀ j < k, s j = s' j) → X s = X s')
    (hYk : ∀ s s', (∀ j < k, s j = s' j) → Y s = Y s')
    (hX2 : Integrable (fun s => ‖X s‖ ^ 2) (P : Measure (ℕ → Ω))) :
    Integrable (fun s => ⟪X s, g (Y s) (s k) - gradient f (Y s)⟫) (P : Measure (ℕ → Ω)) ∧
      (∫ s, ⟪X s, g (Y s) (s k) - gradient f (Y s)⟫ ∂(P : Measure (ℕ → Ω))) = 0 := by
  let Φ : (ℕ → Ω) → Ω → ℝ := fun s b => (inner ℝ (X s) (g (Y s) b - gradient f (Y s)))
  have hnm : Measurable (fun z : (ℕ → Ω) × Ω => g (Y z.1) z.2 - gradient f (Y z.1)) :=
    (ho.measurable.comp ((hYm.comp measurable_fst).prodMk measurable_snd)).sub
      (hgm.comp (hYm.comp measurable_fst))
  have hΦ : Measurable (Function.uncurry Φ) := Measurable.inner (hXm.comp measurable_fst) hnm
  have hk : ∀ s s' b, (∀ j < k, s j = s' j) → Φ s b = Φ s' b := by
    intro s s' b h
    simp only [Φ]
    rw [hXk s s' h, hYk s s' h]
  obtain ⟨hNi, -⟩ := noise_sq μ P hiid f g σ ho hgm k Y hYm hYk
  have hS : Measurable (fun s : ℕ → Ω => (s, s k)) := measurable_id.prodMk (measurable_pi_apply k)
  have hI : Integrable (fun s => Φ s (s k)) (P : Measure (ℕ → Ω)) := by
    refine (hX2.add hNi).mono' (hΦ.comp hS).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => ?_))
    have h1 := abs_real_inner_le_norm (X s) (g (Y s) (s k) - gradient f (Y s))
    rw [Real.norm_eq_abs]
    change |(inner ℝ (X s) (g (Y s) (s k) - gradient f (Y s)))| ≤ ‖X s‖ ^ 2 + ‖g (Y s) (s k) - gradient f (Y s)‖ ^ 2
    nlinarith [sq_nonneg (‖X s‖ - ‖g (Y s) (s k) - gradient f (Y s)‖)]
  refine ⟨hI, ?_⟩
  rw [(RingmasterAsgd.step_integral μ P (fun k (s : ℕ → Ω) => s k) hiid k Φ hΦ hk).2 hI]
  have hz (s : ℕ → Ω) : (∫ b, Φ s b ∂(μ : Measure Ω)) = 0 := by
    change (∫ b, (inner ℝ (X s) (g (Y s) b - gradient f (Y s))) ∂(μ : Measure Ω)) = 0
    have hgi : Integrable (fun b => g (Y s) b - gradient f (Y s)) (μ : Measure Ω) :=
      (ho.integrable (Y s)).sub (integrable_const _)
    rw [integral_inner hgi, integral_sub (ho.integrable (Y s)) (integrable_const _), ho.unbiased]
    simp
  simp only [hz, integral_zero]

theorem batch_noise (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Mat m n → ℝ) (g : Mat m n → Ω → Mat m n) (σ : ℝ)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat m n) Ω (μ : Measure Ω) f g σ)
    (hgm : Measurable (gradient f)) (k0 : ℕ) (Y : (ℕ → Ω) → Mat m n) (hYm : Measurable Y)
    (hYk : ∀ s s', (∀ j < k0, s j = s' j) → Y s = Y s') (b : ℕ) :
    Measurable (fun s => ∑ j ∈ Finset.range b, (g (Y s) (s (k0 + j)) - gradient f (Y s))) ∧
    (∀ s s', (∀ j < k0 + b, s j = s' j) →
      ∑ j ∈ Finset.range b, (g (Y s) (s (k0 + j)) - gradient f (Y s)) =
        ∑ j ∈ Finset.range b, (g (Y s') (s' (k0 + j)) - gradient f (Y s'))) ∧
    Integrable (fun s => ‖∑ j ∈ Finset.range b, (g (Y s) (s (k0 + j)) - gradient f (Y s))‖ ^ 2)
      (P : Measure (ℕ → Ω)) ∧
    (∫ s, ‖∑ j ∈ Finset.range b, (g (Y s) (s (k0 + j)) - gradient f (Y s))‖ ^ 2
      ∂(P : Measure (ℕ → Ω))) ≤ b * σ ^ 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    obtain ⟨ihm, ihk, ihi, ihle⟩ := ih
    set S : (ℕ → Ω) → Mat m n := fun s => ∑ j ∈ Finset.range b, (g (Y s) (s (k0 + j)) - gradient f (Y s))
    have hYk' : ∀ s s', (∀ j < k0 + b, s j = s' j) → Y s = Y s' :=
      fun s s' h => hYk s s' (fun j hj => h j (by omega))
    obtain ⟨hci, hce⟩ := noise_cross μ P hiid f g σ ho hgm (k0 + b) S Y ihm hYm ihk hYk' ihi
    obtain ⟨hni, hnle⟩ := noise_sq μ P hiid f g σ ho hgm (k0 + b) Y hYm hYk'
    have hsplit : ∀ s, ‖∑ j ∈ Finset.range (b + 1), (g (Y s) (s (k0 + j)) - gradient f (Y s))‖ ^ 2 =
        ‖S s‖ ^ 2 + 2 * (inner ℝ (S s) (g (Y s) (s (k0 + b)) - gradient f (Y s))) +
          ‖g (Y s) (s (k0 + b)) - gradient f (Y s)‖ ^ 2 := by
      intro s
      rw [Finset.sum_range_succ, norm_add_sq_real]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Finset.measurable_sum _ (fun j _ =>
        (ho.measurable.comp (hYm.prodMk (measurable_pi_apply _))).sub (hgm.comp hYm))
    · intro s s' h
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ihk s s' (fun j hj => h j (by omega)),
        hYk' s s' (fun j hj => h j (by omega)), h (k0 + b) (by omega)]
    · simp only [hsplit]
      exact (ihi.add (hci.const_mul 2)).add hni
    · simp only [hsplit]
      have hA : Integrable (fun s => ‖S s‖ ^ 2) (P : Measure (ℕ → Ω)) := ihi
      have hAle : (∫ s, ‖S s‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ b * σ ^ 2 := ihle
      have hB : Integrable (fun s => 2 * (inner ℝ (S s) (g (Y s) (s (k0 + b)) - gradient f (Y s))))
          (P : Measure (ℕ → Ω)) := hci.const_mul 2
      have hAB : Integrable (fun s => ‖S s‖ ^ 2 + 2 * (inner ℝ (S s) (g (Y s) (s (k0 + b)) - gradient f (Y s))))
          (P : Measure (ℕ → Ω)) := hA.add hB
      rw [integral_add hAB hni, integral_add hA hB, integral_const_mul, hce]
      push_cast
      linarith

theorem batch_mean_sub (B : ℕ) (hB : 1 ≤ B) (x : ℕ → Mat m n) (y : Mat m n) :
    (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, x j - y = (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, (x j - y) := by
  rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, one_div, inv_mul_cancel₀ (by exact_mod_cast (show B ≠ 0 by omega)), one_smul]

theorem momentum_noise (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (s : ℕ → Ω) => s k)
      (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (f : Mat m n → ℝ) (g : Mat m n → Ω → Mat m n) (σ : ℝ)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Mat m n) Ω (μ : Measure Ω) f g σ)
    (hgm : Measurable (gradient f)) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (B : ℕ) (hB : 1 ≤ B)
    (W : ℕ → (ℕ → Ω) → Mat m n) (hWm : ∀ t, Measurable (W t))
    (hWk : ∀ t s s', (∀ j < t * B, s j = s' j) → W t s = W t s')
    (D : ℕ → (ℕ → Ω) → Mat m n)
    (hD0 : ∀ s, D 0 s = (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, g (W 0 s) (s (0 * B + j)) - gradient f (W 0 s))
    (hD : ∀ t s, D (t + 1) s = β • D t s + (1 - β) • ((1 / (B : ℝ)) •
      ∑ j ∈ Finset.range B, g (W (t + 1) s) (s ((t + 1) * B + j)) - gradient f (W (t + 1) s)))
    (t : ℕ) :
    Measurable (D t) ∧ (∀ s s', (∀ j < (t + 1) * B, s j = s' j) → D t s = D t s') ∧
    Integrable (fun s => ‖D t s‖ ^ 2) (P : Measure (ℕ → Ω)) ∧
    (∫ s, ‖D t s‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤
      σ ^ 2 / B * ((1 - β) / (1 + β) + (1 - (1 - β) / (1 + β)) * β ^ (2 * t)) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  let N : ℕ → (ℕ → Ω) → Mat m n := fun t s =>
    (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, (g (W t s) (s (t * B + j)) - gradient f (W t s))
  have hN : ∀ t s, (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, g (W t s) (s (t * B + j)) - gradient f (W t s) =
      N t s := fun t s => batch_mean_sub B hB _ _
  have hNprops : ∀ t, Measurable (N t) ∧ (∀ s s', (∀ j < (t + 1) * B, s j = s' j) → N t s = N t s') ∧
      Integrable (fun s => ‖N t s‖ ^ 2) (P : Measure (ℕ → Ω)) ∧
      (∫ s, ‖N t s‖ ^ 2 ∂(P : Measure (ℕ → Ω))) ≤ σ ^ 2 / B := by
    intro t
    obtain ⟨hm, hk, hi, hle⟩ := batch_noise μ P hiid f g σ ho hgm (t * B) (W t) (hWm t) (hWk t) B
    have hsq : ∀ s, ‖N t s‖ ^ 2 = (1 / (B : ℝ)) ^ 2 *
        ‖∑ j ∈ Finset.range B, (g (W t s) (s (t * B + j)) - gradient f (W t s))‖ ^ 2 := by
      intro s
      simp only [N, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hBpos)]
    refine ⟨Measurable.smul (measurable_const (a := (1 / (B : ℝ)))) hm, fun s s' h => ?_, ?_, ?_⟩
    · simp only [N]
      rw [hk s s' (fun j hj => h j (by rw [add_mul, one_mul]; exact hj))]
    · simp only [hsq]
      exact hi.const_mul _
    · simp only [hsq]
      rw [integral_const_mul]
      calc (1 / (B : ℝ)) ^ 2 * ∫ s, ‖∑ j ∈ Finset.range B,
            (g (W t s) (s (t * B + j)) - gradient f (W t s))‖ ^ 2 ∂(P : Measure (ℕ → Ω)) ≤
            (1 / (B : ℝ)) ^ 2 * (B * σ ^ 2) := mul_le_mul_of_nonneg_left hle (sq_nonneg _)
        _ = σ ^ 2 / B := by field_simp
  have hcross : ∀ t, Measurable (D t) → (∀ s s', (∀ j < (t + 1) * B, s j = s' j) → D t s = D t s') →
      Integrable (fun s => ‖D t s‖ ^ 2) (P : Measure (ℕ → Ω)) →
      Integrable (fun s => (inner ℝ (D t s) (N (t + 1) s))) (P : Measure (ℕ → Ω)) ∧
        (∫ s, (inner ℝ (D t s) (N (t + 1) s)) ∂(P : Measure (ℕ → Ω))) = 0 := by
    intro t hm hk hi
    have hterm : ∀ j ∈ Finset.range B,
        Integrable (fun s => (inner ℝ (D t s) (g (W (t + 1) s) (s ((t + 1) * B + j)) - gradient f (W (t + 1) s))))
          (P : Measure (ℕ → Ω)) ∧
        (∫ s, (inner ℝ (D t s) (g (W (t + 1) s) (s ((t + 1) * B + j)) - gradient f (W (t + 1) s)))
          ∂(P : Measure (ℕ → Ω))) = 0 := by
      intro j _
      exact noise_cross μ P hiid f g σ ho hgm ((t + 1) * B + j) (D t) (W (t + 1)) hm (hWm (t + 1))
        (fun s s' h => hk s s' (fun i hi => h i (by omega)))
        (fun s s' h => hWk (t + 1) s s' (fun i hi => h i (by omega))) hi
    have hexp : ∀ s, (inner ℝ (D t s) (N (t + 1) s)) = (1 / (B : ℝ)) * ∑ j ∈ Finset.range B,
        (inner ℝ (D t s) (g (W (t + 1) s) (s ((t + 1) * B + j)) - gradient f (W (t + 1) s))) := by
      intro s
      simp only [N, inner_smul_right, inner_sum]
    simp only [hexp]
    refine ⟨(integrable_finsetSum _ (fun j hj => (hterm j hj).1)).const_mul _, ?_⟩
    rw [integral_const_mul, integral_finsetSum _ (fun j hj => (hterm j hj).1),
      Finset.sum_eq_zero (fun j hj => (hterm j hj).2), mul_zero]
  have h1b : 0 < 1 + β := by linarith
  have hrec_a : β ^ 2 * ((1 - β) / (1 + β)) + (1 - β) ^ 2 = (1 - β) / (1 + β) := by
    field_simp; ring
  induction t with
  | zero =>
    have e : D 0 = N 0 := funext fun s => by rw [hD0]; exact hN 0 s
    obtain ⟨hm, hk, hi, hle⟩ := hNprops 0
    rw [e]
    refine ⟨hm, hk, hi, hle.trans (le_of_eq ?_)⟩
    simp only [mul_zero, pow_zero, mul_one]
    ring
  | succ t ih =>
    obtain ⟨hm, hk, hi, hle⟩ := ih
    obtain ⟨hNm, hNk, hNi, hNle⟩ := hNprops (t + 1)
    obtain ⟨hci, hce⟩ := hcross t hm hk hi
    have e : D (t + 1) = fun s => β • D t s + (1 - β) • N (t + 1) s :=
      funext fun s => by rw [hD, hN]
    have hb1 : 0 ≤ 1 - β := by linarith
    have hsq : ∀ s, ‖β • D t s + (1 - β) • N (t + 1) s‖ ^ 2 = β ^ 2 * ‖D t s‖ ^ 2 +
        2 * (β * (1 - β)) * (inner ℝ (D t s) (N (t + 1) s)) + (1 - β) ^ 2 * ‖N (t + 1) s‖ ^ 2 := by
      intro s
      rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hβ0, abs_of_nonneg hb1, conj_trivial]
      ring
    rw [e]
    have hA : Integrable (fun s => β ^ 2 * ‖D t s‖ ^ 2) (P : Measure (ℕ → Ω)) := hi.const_mul _
    have hB : Integrable (fun s => 2 * (β * (1 - β)) * (inner ℝ (D t s) (N (t + 1) s))) (P : Measure (ℕ → Ω)) :=
      hci.const_mul _
    have hC : Integrable (fun s => (1 - β) ^ 2 * ‖N (t + 1) s‖ ^ 2) (P : Measure (ℕ → Ω)) :=
      hNi.const_mul _
    have hAB : Integrable (fun s => β ^ 2 * ‖D t s‖ ^ 2 + 2 * (β * (1 - β)) * (inner ℝ (D t s) (N (t + 1) s)))
        (P : Measure (ℕ → Ω)) := hA.add hB
    refine ⟨by fun_prop, fun s s' h => ?_, ?_, ?_⟩
    · simp only
      rw [hk s s' (fun j hj => h j (by nlinarith)), hNk s s' h]
    · simp only [hsq]
      exact hAB.add hC
    · simp only [hsq]
      rw [integral_add hAB hC, integral_add hA hB, integral_const_mul, integral_const_mul,
        integral_const_mul, hce]
      have hσ : 0 ≤ σ ^ 2 / B := by positivity
      have h1 := mul_le_mul_of_nonneg_left hle (sq_nonneg β)
      have h2 := mul_le_mul_of_nonneg_left hNle (sq_nonneg (1 - β))
      have hpow : β ^ (2 * (t + 1)) = β ^ 2 * β ^ (2 * t) := by ring
      rw [hpow]
      nlinarith [hrec_a]

omit [MeasurableSpace Ω] in
theorem integral_norm_le_sqrt {mΞ : MeasurableSpace Ω} (Q : Measure Ω) [IsProbabilityMeasure Q]
    (X : Ω → Mat m n) (hXm : Measurable X) (hX2 : Integrable (fun s => ‖X s‖ ^ 2) Q) :
    Integrable (fun s => ‖X s‖) Q ∧ (∫ s, ‖X s‖ ∂Q) ≤ Real.sqrt (∫ s, ‖X s‖ ^ 2 ∂Q) := by
  have hI : Integrable (fun s => ‖X s‖) Q := by
    refine ((hX2.add (integrable_const 1)).div_const 2).mono' hXm.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    change ‖X s‖ ≤ (‖X s‖ ^ 2 + 1) / 2
    nlinarith [sq_nonneg (‖X s‖ - 1)]
  refine ⟨hI, ?_⟩
  set c := ∫ s, ‖X s‖ ∂Q
  have hc0 : 0 ≤ c := integral_nonneg (fun s => norm_nonneg _)
  have hexp : ∀ s, (‖X s‖ - c) ^ 2 = ‖X s‖ ^ 2 - 2 * c * ‖X s‖ + c ^ 2 := fun s => by ring
  have hnn : 0 ≤ ∫ s, (‖X s‖ - c) ^ 2 ∂Q := integral_nonneg (fun s => sq_nonneg _)
  have hA : Integrable (fun s => ‖X s‖ ^ 2 - 2 * c * ‖X s‖) Q := hX2.sub (hI.const_mul _)
  simp only [hexp] at hnn
  rw [integral_add hA (integrable_const _), integral_sub hX2 (hI.const_mul _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hnn
  rw [Real.le_sqrt hc0 (integral_nonneg (fun s => sq_nonneg _))]
  nlinarith

theorem momentum_sqrt_le (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.sqrt ((1 - β) / (1 + β) + (1 - (1 - β) / (1 + β)) * y ^ 2) ≤
      Real.sqrt ((1 - β) / (1 + β)) + β * y := by
  set a := (1 - β) / (1 + β)
  have h1b : 0 < 1 + β := by linarith
  have ha0 : 0 ≤ a := div_nonneg (by linarith) h1b.le
  set q := Real.sqrt a
  have hq0 : 0 ≤ q := Real.sqrt_nonneg a
  have hqq : q ^ 2 = a := Real.sq_sqrt ha0
  have h1a : 1 - a = 2 * β / (1 + β) := by simp only [a]; field_simp; ring
  have hkey : q * (2 + β) ≤ 2 := by
    have hsq : (q * (2 + β)) ^ 2 ≤ 2 ^ 2 := by
      rw [mul_pow, hqq]
      simp only [a]
      rw [div_mul_eq_mul_div, div_le_iff₀ h1b]
      nlinarith [sq_nonneg β, mul_nonneg hβ0 (sq_nonneg β)]
    nlinarith [sq_nonneg (q * (2 + β) - 2), sq_nonneg (q * (2 + β) + 2), mul_nonneg hq0 (by linarith : (0:ℝ) ≤ 2 + β)]
  have hcoef : 1 - a - β ^ 2 ≤ 2 * q * β := by
    have : 1 - a - β ^ 2 = β * (a * (2 + β)) := by
      rw [h1a]; simp only [a]; field_simp; ring
    rw [this, ← hqq]
    nlinarith [mul_le_mul_of_nonneg_left hkey (mul_nonneg hβ0 hq0)]
  rw [Real.sqrt_le_left (by positivity)]
  rw [← hqq] at hcoef ⊢
  have : (1 - q ^ 2 - β ^ 2) * y ≤ 2 * q * β := by
    rcases le_total 0 (1 - q ^ 2 - β ^ 2) with h | h
    · nlinarith [mul_le_mul_of_nonneg_left hy1 h]
    · nlinarith [mul_nonneg (mul_nonneg hq0 hβ0) (by norm_num : (0:ℝ) ≤ 2), mul_nonpos_of_nonpos_of_nonneg h hy0]
  nlinarith [mul_le_mul_of_nonneg_left this hy0]

end OracleTemplate.Muon
