import LongTails.Proofs.AdaptiveEntropicAssembly
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma analysis_cap_power {T K σ A p : ℝ} (hT : 0 ≤ T) (hK : 0 < K)
    (hσ : 0 ≤ σ) (hp : 1 ≤ p)
    (hscale : 4096 * σ * (T ^ (p + 1) / K) ^ (1 / p) ≤ A) :
    4096 * T ^ (p + 1) * σ ^ p ≤ K * A ^ p := by
  have hp0 : 0 < p := by linarith
  have hz : 0 ≤ T ^ (p + 1) / K := by positivity
  have hc : 0 ≤ σ * (T ^ (p + 1) / K) ^ (1 / p) := by positivity
  have hroot : ((T ^ (p + 1) / K) ^ (1 / p)) ^ p = T ^ (p + 1) / K := by
    rw [← Real.rpow_mul hz]
    rw [one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hcPow : (σ * (T ^ (p + 1) / K) ^ (1 / p)) ^ p =
      σ ^ p * (T ^ (p + 1) / K) := by
    rw [Real.mul_rpow hσ (by positivity), hroot]
  have h4096 : (4096 : ℝ) ≤ (4096 : ℝ) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4096) hp
  have hraise : (4096 * (σ * (T ^ (p + 1) / K) ^ (1 / p))) ^ p ≤ A ^ p := by
    apply Real.rpow_le_rpow (by positivity) _ hp0.le
    simpa only [mul_assoc] using hscale
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4096) hc, hcPow] at hraise
  have hfirst := mul_le_mul_of_nonneg_right h4096
    (show 0 ≤ σ ^ p * (T ^ (p + 1) / K) by positivity)
  have h := mul_le_mul_of_nonneg_left (hfirst.trans hraise) hK.le
  have he : K * (4096 * (σ ^ p * (T ^ (p + 1) / K))) =
      4096 * T ^ (p + 1) * σ ^ p := by field_simp
  rw [he] at h
  exact h

lemma cap_moment_bounds {T K σ A U p : ℝ} (hT : 0 ≤ T) (hK : 0 < K)
    (hσ : 0 ≤ σ) (hA : 0 < A) (hAU : A ≤ U) (hp : 1 ≤ p)
    (hpower : 4096 * T ^ (p + 1) * σ ^ p ≤ K * A ^ p) :
    T * (130 * T ^ p * σ ^ p / A ^ p) ≤ K / 31 ∧
    130 * T ^ (p + 1) * σ ^ p / A ^ (p - 1) ≤ K * A / 31 ∧
    T * (16 * U ^ (2 - p) * T ^ p * σ ^ p) ≤ K * U ^ 2 / 256 := by
  have hU : 0 < U := hA.trans_le hAU
  have hp0 : 0 ≤ p := by linarith
  have hTp : T ^ (p + 1) = T ^ p * T := by
    rw [Real.rpow_add_of_nonneg hT hp0 (by norm_num : (0 : ℝ) ≤ 1), Real.rpow_one]
  have hn : 0 ≤ T ^ (p + 1) * σ ^ p := by positivity
  have hcount : 130 * T ^ (p + 1) * σ ^ p ≤ K * A ^ p / 31 := by
    nlinarith only [hpower, hn]
  have hAp : 0 < A ^ p := Real.rpow_pos_of_pos hA p
  have hAm : 0 < A ^ (p - 1) := Real.rpow_pos_of_pos hA (p - 1)
  have hApEq : A ^ p = A ^ (p - 1) * A := by
    conv_lhs => rw [show p = (p - 1) + 1 by ring]
    rw [Real.rpow_add hA, Real.rpow_one]
  constructor
  · rw [show T * (130 * T ^ p * σ ^ p / A ^ p) =
        (T * 130 * T ^ p * σ ^ p) / A ^ p by ring]
    apply (div_le_iff₀ hAp).mpr
    rw [hTp] at hcount
    nlinarith only [hcount]
  constructor
  · apply (div_le_iff₀ hAm).mpr
    rw [hApEq] at hcount
    nlinarith only [hcount]
  · have hAU_P := Real.rpow_le_rpow hA.le hAU hp0
    have hpowerU : 4096 * T ^ (p + 1) * σ ^ p ≤ K * U ^ p :=
      hpower.trans (mul_le_mul_of_nonneg_left hAU_P hK.le)
    have hmul := mul_le_mul_of_nonneg_left hpowerU
      (show 0 ≤ U ^ (2 - p) by positivity)
    have he : U ^ (2 - p) * U ^ p = U ^ 2 := by
      rw [← Real.rpow_add hU, sub_add_cancel, Real.rpow_two]
    have hmul' : 4096 * (U ^ (2 - p) * (T ^ (p + 1) * σ ^ p)) ≤ K * U ^ 2 := by
      calc
        _ = U ^ (2 - p) * (4096 * T ^ (p + 1) * σ ^ p) := by ring
        _ ≤ U ^ (2 - p) * (K * U ^ p) := hmul
        _ = _ := by rw [show U ^ (2 - p) * (K * U ^ p) = K * (U ^ (2 - p) * U ^ p) by ring, he]
    rw [hTp] at hmul'
    nlinarith only [hmul']

lemma confidence_le_trimCount (q : Public) : confidence q ≤ (trimCount q : ℝ) / 64 := by
  have hc : 64 * (geometry q + confidence q) ≤ (⌈64 * (geometry q + confidence q)⌉₊ : ℝ) := Nat.le_ceil _
  have ht : (⌈64 * (geometry q + confidence q)⌉₊ : ℝ) ≤ (trimCount q : ℝ) := by
    exact_mod_cast (le_max_right 1 _)
  have hD := (geometry_pos q).le
  linarith only [hc, ht, hD]

lemma centers_prefix_of_not_failure (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) (T : ℕ) (ξ : ℕ → Ω)
    (hc : ξ ∉ ⋃ i ∈ Finset.range T, {ξ | ¬ centerGood q μ σ
      (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ (preload q + i)).1}) :
    ∀ j < preload q + T,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → centerGood q μ σ s := by
  intro j hj
  dsimp only
  intro hw
  have hs := (blockTrace_structure q g ξ j).2.2.1
  have hm : preload q ≤ j := by omega
  have hi : j - preload q < T := by omega
  have he : preload q + (j - preload q) = j := by omega
  by_contra hn
  apply hc
  apply Set.mem_iUnion.mpr
  refine ⟨j - preload q, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hi, ?_⟩⟩
  simpa only [Set.mem_ofPred_eq, he] using hn

lemma actual_energy_on_good_path (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {f : Vector q.d → ℝ} (hL : 0 < q.L) (hH : 2 ≤ confidence q)
    (hf : ConvexOn ℝ (simplex q.d) f)
    (hgrad : ∀ x ∈ simplex q.d, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ simplex q.d, ∀ y ∈ simplex q.d,
      dualNorm (gradient f x - gradient f y) ≤ q.L * oneNorm (x - y))
    (hμ : Measurable (fun x : simplex q.d => gradient f x))
    {σ A U p : ℝ} (hσ : 0 ≤ σ) (hA : 0 < A) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - gradient f x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - gradient f x) ^ p ∂P) ≤ σ ^ p)
    (hgi : ∀ x, Integrable (g x) P) (hgu : ∀ x, (∫ ω, g x ω ∂P) = gradient f x)
    (T : ℕ) (xstar : simplex q.d) (ξ : ℕ → Ω)
    (hUeq : U = 24 * q.L * window q (T + 1) + A)
    (hV : T * (16 * U ^ (2 - p) * (T : ℝ) ^ p * σ ^ p) ≤ (trimCount q : ℝ) * U ^ 2 / 256)
    (hR : 130 * (T : ℝ) ^ (p + 1) * σ ^ p / A ^ (p - 1) ≤ (trimCount q : ℝ) * A / 31)
    (hc : ∀ j < preload q + T,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → centerGood q (fun x => gradient f x) σ s)
    (hQ : empiricalQuantile q (macroState q g ξ T) ≤ A)
    (hW : (macroState q g ξ T).variation ≤ (trimCount q : ℝ) * U ^ 2)
    (hX : StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (linearNoiseScore q g (fun x => gradient f x) σ A T P xstar)
      (preload q + T) (initialState q) ξ ≤ 4 * U * confidence q +
        (T * (16 * U ^ (2 - p) * (T : ℝ) ^ p * σ ^ p)) / U)
    (hY : 2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (quadraticNoiseScore q g (fun x => gradient f x) σ A T P)
      (preload q + T) (initialState q) ξ ≤
        16 * Real.sqrt (geometry q) * Real.sqrt ((macroState q g ξ T).variation) +
          20 * (U * geometry q / trimCount q) * confidence q)
    (hC : StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (fun n s (_ : Fin n → Ω) => ∫ b, firstScore (cappedBiasScore q g
        (fun x => gradient f x) σ A) n s b ∂Measure.pi (fun _ : Fin n => P))
      (preload q + T) (initialState q) ξ ≤ 2 * (trimCount q : ℝ) + 4 * confidence q) :
    (T : ℝ) * (T + 1) / 2 * (f (macroState q g ξ T).y - f xstar) ≤
      170 * (trimCount q : ℝ) * U := by
  have hw : 0 ≤ q.L * (window q (T + 1) : ℝ) := by positivity
  have hAU : A ≤ U := by rw [hUeq]; nlinarith only [hw]
  have hU : 0 < U := hA.trans_le hAU
  have hK : 0 < (trimCount q : ℝ) := by
    have hn : 1 ≤ trimCount q := le_max_left _ _
    exact_mod_cast (show 0 < trimCount q by omega)
  have hH0 : 0 ≤ confidence q := by linarith only [hH]
  have hBw : q.L * window q ((macroState q g ξ T).completed + 1) ≤ U := by
    rw [(macroState_structure q g ξ T).2.2, hUeq]
    nlinarith only [hw, hA]
  have hB := regularization_entropy_bound q hH0 (macroState q g ξ T) xstar
    hU.le hBw (hQ.trans hAU) hW
  have he := actual_energy_from_scores q hg hL hH hf hgrad hlip hμ hσ hA hp hp2
    hi hm hgi hgu T xstar ξ hc hQ
  apply energy_envelope hK hU hA.le hAU (geometry_pos q).le
    (geometry_le_trimCount q hH0) hH0 (confidence_le_trimCount q) hV hW hB hX _ hC hR he
  convert hY using 1; ring

lemma noise_scale_identity {T K p : ℝ} (hT : 0 < T) (hK : 0 < K) (hp : 0 < p) :
    K * (T ^ (p + 1) / K) ^ (1 / p) / T ^ 2 = (K / T) ^ ((p - 1) / p) := by
  have heK : 1 - 1 / p = (p - 1) / p := by field_simp
  have heT : (p + 1) * (1 / p) - 2 = -((p - 1) / p) := by field_simp; ring
  calc
    _ = (K / K ^ (1 / p)) * (T ^ ((p + 1) * (1 / p)) / T ^ 2) := by
      rw [Real.div_rpow (Real.rpow_nonneg hT.le _) hK.le, ← Real.rpow_mul hT.le]
      ring
    _ = K ^ (1 - 1 / p) * T ^ ((p + 1) * (1 / p) - 2) := by
      rw [Real.rpow_sub hK, Real.rpow_sub hT, Real.rpow_one, Real.rpow_two]
    _ = K ^ ((p - 1) / p) * T ^ (-((p - 1) / p)) := by rw [heK, heT]
    _ = _ := by rw [Real.rpow_neg hT.le, Real.div_rpow hK.le hT.le]; ring

lemma noise_envelope_rate {T K σ p : ℝ} (hT : 0 < T) (hK : 0 < K) (hp : 0 < p) :
    340 * K * (4096 * σ * (T ^ (p + 1) / K) ^ (1 / p)) / T ^ 2 =
      1392640 * σ * (K / T) ^ ((p - 1) / p) := by
  calc
    _ = 1392640 * σ * (K * (T ^ (p + 1) / K) ^ (1 / p) / T ^ 2) := by ring
    _ = _ := by rw [noise_scale_identity hT hK hp]

lemma objective_gap_from_energy {T K U gap : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    (hU : 0 ≤ U) (he : T * (T + 1) / 2 * gap ≤ 170 * K * U) :
    gap ≤ 340 * K * U / T ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
  by_cases hg : 0 ≤ gap
  · have hm := mul_nonneg hT.le hg
    nlinarith only [he, hm]
  · have hg0 := lt_of_not_ge hg
    have hm := mul_nonpos_of_nonpos_of_nonneg hg0.le (sq_nonneg T)
    have hr : 0 ≤ 340 * K * U := by positivity
    exact hm.trans hr

lemma analytic_envelope_rate (q : Public) (hL : 0 ≤ q.L) (hH : 2 ≤ confidence q)
    {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 0 < p) {T : ℕ} (hT : 0 < T) :
    340 * (trimCount q : ℝ) * (48 * q.L * window q (T + 1) +
      4096 * σ * ((T : ℝ) ^ (p + 1) / trimCount q) ^ (1 / p)) / (T : ℝ) ^ 2 ≤
      16777216 * (q.L * trimCount q * window q T / (T : ℝ) ^ 2 +
        σ * ((trimCount q : ℝ) / T) ^ ((p - 1) / p)) := by
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hK : 0 < (trimCount q : ℝ) := by
    have hn : 1 ≤ trimCount q := le_max_left _ _
    exact_mod_cast (show 0 < trimCount q by omega)
  have hw := window_succ_le_twice q hH T
  have hwR : (window q (T + 1) : ℝ) ≤ 2 * (window q T : ℝ) := by exact_mod_cast hw
  have hdet : 340 * (trimCount q : ℝ) * (48 * q.L * window q (T + 1)) / (T : ℝ) ^ 2 ≤
      32640 * (q.L * trimCount q * window q T / (T : ℝ) ^ 2) := by
    rw [show 32640 * (q.L * trimCount q * window q T / (T : ℝ) ^ 2) =
        (32640 * (q.L * trimCount q * window q T)) / (T : ℝ) ^ 2 by ring]
    apply div_le_div_of_nonneg_right _ (sq_nonneg (T : ℝ))
    have h := mul_le_mul_of_nonneg_left hwR (show 0 ≤ 16320 * (trimCount q : ℝ) * q.L by positivity)
    nlinarith only [h]
  have hn := noise_envelope_rate (σ := σ) hTr hK hp
  have hsplit : 340 * (trimCount q : ℝ) * (48 * q.L * window q (T + 1) +
      4096 * σ * ((T : ℝ) ^ (p + 1) / trimCount q) ^ (1 / p)) / (T : ℝ) ^ 2 =
      340 * (trimCount q : ℝ) * (48 * q.L * window q (T + 1)) / (T : ℝ) ^ 2 +
      1392640 * σ * ((trimCount q : ℝ) / T) ^ ((p - 1) / p) := by
    rw [show 340 * (trimCount q : ℝ) * (48 * q.L * window q (T + 1) +
        4096 * σ * ((T : ℝ) ^ (p + 1) / trimCount q) ^ (1 / p)) / (T : ℝ) ^ 2 =
        340 * (trimCount q : ℝ) * (48 * q.L * window q (T + 1)) / (T : ℝ) ^ 2 +
        340 * (trimCount q : ℝ) * (4096 * σ * ((T : ℝ) ^ (p + 1) / trimCount q) ^ (1 / p)) /
          (T : ℝ) ^ 2 by ring, hn]
  rw [hsplit]
  have hd0 : 0 ≤ q.L * trimCount q * window q T / (T : ℝ) ^ 2 := by positivity
  have hn0 : 0 ≤ σ * ((trimCount q : ℝ) / T) ^ ((p - 1) / p) := by positivity
  nlinarith only [hdet, hd0, hn0]

lemma confidence_failure (q : Public) (hδ : 0 < q.δ) :
    7 * ENNReal.ofReal (Real.exp (-confidence q)) ≤ ENNReal.ofReal q.δ := by
  have he : Real.exp (-confidence q) = q.δ / 100 := by
    unfold confidence
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 100 / q.δ)]
    field_simp
  rw [he]
  have hseven : (7 : ENNReal) = ENNReal.ofReal (7 : ℝ) := by norm_num
  rw [hseven, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7)]
  apply ENNReal.ofReal_le_ofReal
  linarith only [hδ]

noncomputable def analysisCap (q : Public) (σ p : ℝ) (T : ℕ) : ℝ :=
  24 * q.L * window q (T + 1) +
    4096 * σ * ((T : ℝ) ^ (p + 1) / trimCount q) ^ (1 / p)

lemma analysisCap_pos (q : Public) (hL : 0 < q.L) (hH : 2 ≤ confidence q)
    {σ p : ℝ} (hσ : 0 ≤ σ) (T : ℕ) : 0 < analysisCap q σ p T := by
  have hlog : 0 ≤ Real.log (((T + 1 : ℕ) : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (T + 1); linarith)
  have hw : 0 < window q (T + 1) := by
    unfold window
    apply Nat.ceil_pos.mpr
    nlinarith only [hH, hlog]
  unfold analysisCap
  positivity

lemma analysisCap_controls (q : Public) (hL : 0 < q.L) (hH : 2 ≤ confidence q)
    {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) (T : ℕ) :
    let A := analysisCap q σ p T
    let U := 24 * q.L * window q (T + 1) + A
    T * (130 * (T : ℝ) ^ p * σ ^ p / A ^ p) ≤ (trimCount q : ℝ) / 31 ∧
    130 * (T : ℝ) ^ (p + 1) * σ ^ p / A ^ (p - 1) ≤ (trimCount q : ℝ) * A / 31 ∧
    T * (16 * U ^ (2 - p) * (T : ℝ) ^ p * σ ^ p) ≤ (trimCount q : ℝ) * U ^ 2 / 256 := by
  intro A U
  have hA : 0 < A := analysisCap_pos q hL hH hσ T
  have hK : 0 < (trimCount q : ℝ) := by
    have hn : 1 ≤ trimCount q := le_max_left _ _
    exact_mod_cast (show 0 < trimCount q by omega)
  have hAU : A ≤ U := by
    dsimp [U]
    have hw : 0 ≤ 24 * q.L * window q (T + 1) := by positivity
    linarith only [hw]
  have hscale : 4096 * σ * ((T : ℝ) ^ (p + 1) / trimCount q) ^ (1 / p) ≤ A := by
    dsimp [A, analysisCap]
    have hw : 0 ≤ 24 * q.L * window q (T + 1) := by positivity
    linarith only [hw]
  exact cap_moment_bounds (Nat.cast_nonneg T) hK hσ hA hAU hp
    (analysis_cap_power (Nat.cast_nonneg T) hK hσ hp hscale)

end OracleTemplate.AdaptiveHeavyTailSimplex
