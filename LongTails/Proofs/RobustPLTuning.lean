import LongTails.Proofs.RobustPLContraction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LongTails.Proofs.GdPL

namespace OracleTemplate.RobustPLPotential

lemma thresholds {μ ε a ρ : ℝ} (hμ : 0 < μ) (hε : 0 < ε) (ha : 0 < a) :
    let t := (36864 * ρ ^ 2 / μ ^ 3 + 1 / (a * ε))⁻¹
    let ν := (2 ^ 17 / ε + 3200 * a / t)⁻¹
    0 < t ∧ 36864 * ρ ^ 2 * t ≤ μ ^ 3 ∧ 0 < ν ∧
    ν ≤ ε / 2 ^ 17 ∧ ν ≤ t / (3200 * a) ∧
    ν = ((2 ^ 17 + 3200) / ε + 117964800 * a * ρ ^ 2 / μ ^ 3)⁻¹ := by
  let t := (36864 * ρ ^ 2 / μ ^ 3 + 1 / (a * ε))⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have hD : 0 < 2 ^ 17 / ε + 3200 * a / t := by positivity
  have hlocal : 36864 * ρ ^ 2 * t ≤ μ ^ 3 := by
    have hd : 0 < 36864 * ρ ^ 2 / μ ^ 3 + 1 / (a * ε) := by positivity
    have he : t * (36864 * ρ ^ 2 / μ ^ 3 + 1 / (a * ε)) = 1 := inv_mul_cancel₀ hd.ne'
    have hn : 0 ≤ t * (1 / (a * ε)) := by positivity
    have hh : (36864 * ρ ^ 2 * t) / μ ^ 3 ≤ 1 := by
      have he' : t * (36864 * ρ ^ 2 / μ ^ 3) + t * (1 / (a * ε)) = 1 := by
        simpa only [mul_add] using he
      calc
        _ = t * (36864 * ρ ^ 2 / μ ^ 3) := by ring
        _ ≤ 1 := by linarith
    exact (div_le_one (by positivity : 0 < μ ^ 3)).mp hh
  have hfirst : (2 ^ 17 / ε + 3200 * a / t)⁻¹ ≤ ε / 2 ^ 17 := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < (2 : ℝ) ^ 17 / ε)
      (le_add_of_nonneg_right (by positivity : 0 ≤ 3200 * a / t))
    simpa only [one_div, inv_div] using hh
  have hsecond : (2 ^ 17 / ε + 3200 * a / t)⁻¹ ≤ t / (3200 * a) := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < 3200 * a / t)
      (le_add_of_nonneg_left (by positivity : 0 ≤ (2 : ℝ) ^ 17 / ε))
    simpa only [one_div, inv_div] using hh
  refine ⟨ht, hlocal, inv_pos.mpr hD, hfirst, hsecond, ?_⟩
  congr 1
  field_simp
  ring

lemma balanced_moments {A h τ p μ η : ℝ} (hτ : 0 < τ)
    (hA : A = h * τ ^ p) (hh : h = μ * η) :
    (A * τ ^ (1 - p)) ^ 2 = μ * η * (A * τ ^ (2 - p)) ∧
    μ * η ^ 2 * (A * τ ^ (4 - p)) = η * (A * τ ^ (2 - p)) ^ 2 := by
  have he (k : ℕ) : A * τ ^ ((k : ℝ) - p) = h * τ ^ k := by
    rw [hA, mul_assoc, ← Real.rpow_add hτ]
    simp only [add_sub_cancel, Real.rpow_natCast]
  have h1 := he 1
  have h2 := he 2
  have h4 := he 4
  norm_num only [Nat.cast_one, Nat.cast_ofNat] at h1 h2 h4
  rw [h1, h2, h4, hh]
  constructor <;> ring

lemma moment_constraints {μ L η lam s a t ν B V Q : ℝ}
    (hμ : 0 < μ) (hη : 0 < η)
    (hs : 1 ≤ s) (hsq : s ^ 2 * μ = L) (ha : a = s ^ 5)
    (hlameq : lam * μ = 32 * s)
    (hV : 0 ≤ V) (hnoise : η * V ≤ ν) (hν : ν ≤ t / (3200 * a))
    (hB : B ^ 2 ≤ μ * η * V) (hQ : μ * η ^ 2 * Q = η * V ^ 2) :
    96 * lam * L * η * V ≤ t ∧
    4 * lam * L ^ 2 * η ^ 2 * Q ≤ t * V ∧ B ^ 2 ≤ μ * η * V := by
  have hs0 : 0 < s := by linarith
  have ha0 : 0 < a := by rw [ha]; positivity
  have hbound : 3200 * a * (η * V) ≤ t := by
    have hh := hnoise.trans hν
    have hb := (le_div_iff₀ (by positivity : 0 < 3200 * a)).mp hh
    nlinarith only [hb]
  have hpower : s ^ 3 ≤ s ^ 5 := by
    exact pow_le_pow_right₀ hs (by omega)
  have hfirst : 96 * lam * L ≤ 3200 * a := by
    have he : 96 * lam * L = 3072 * s ^ 3 := by rw [← hsq]; nlinarith [hlameq]
    rw [he, ha]
    nlinarith [pow_nonneg hs0.le 5]
  have hsecond : 4 * lam * L ^ 2 / μ ≤ 3200 * a := by
    have he : 4 * lam * L ^ 2 = 128 * s ^ 5 * μ := by
      rw [← hsq]
      nlinarith [hlameq]
    rw [he, mul_div_cancel_right₀ _ hμ.ne', ha]
    nlinarith [pow_nonneg hs0.le 5]
  refine ⟨?_, ?_, hB⟩
  · have hh := mul_le_mul_of_nonneg_right hfirst (show 0 ≤ η * V by positivity)
    nlinarith
  · have he : 4 * lam * L ^ 2 * η ^ 2 * Q = (4 * lam * L ^ 2 / μ) * (η * V) * V := by
      calc
        _ = (4 * lam * L ^ 2 / μ) * (μ * η ^ 2 * Q) := by field_simp
        _ = (4 * lam * L ^ 2 / μ) * (η * V ^ 2) := by rw [hQ]
        _ = _ := by ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hsecond (show 0 ≤ η * V by positivity)
    have hh' := mul_le_mul_of_nonneg_right (hh.trans hbound) hV
    exact hh'

lemma inverse_power_noise {A d b r : ℝ} (hA : 0 ≤ A) (hd : 0 < d)
    (hb : 0 < b) (hr : 0 < r) :
    let h := (d + (A / b) ^ (1 / r))⁻¹
    0 < h ∧ h ≤ 1 / d ∧ A * h ^ r ≤ b := by
  let h := (d + (A / b) ^ (1 / r))⁻¹
  have hD : 0 < d + (A / b) ^ (1 / r) :=
    add_pos_of_pos_of_nonneg hd (Real.rpow_nonneg (div_nonneg hA hb.le) _)
  have hh : 0 < h := inv_pos.mpr hD
  refine ⟨hh, ?_, ?_⟩
  · simpa only [one_div] using one_div_le_one_div_of_le hd
      (le_add_of_nonneg_right (Real.rpow_nonneg (div_nonneg hA hb.le) (1 / r)))
  · by_cases hAz : A = 0
    · simp only [hAz, zero_mul]; exact hb.le
    have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    have hx : 0 < (A / b) ^ (1 / r) := Real.rpow_pos_of_pos (by positivity) _
    have hhx : h ≤ ((A / b) ^ (1 / r))⁻¹ := by
      simpa only [one_div, h] using one_div_le_one_div_of_le hx (le_add_of_nonneg_left hd.le)
    have hhpow := Real.rpow_le_rpow hh.le hhx hr.le
    have he : (((A / b) ^ (1 / r))⁻¹) ^ r = b / A := by
      rw [Real.inv_rpow (by positivity), ← Real.rpow_mul (by positivity),
        one_div_mul_cancel hr.ne', Real.rpow_one, inv_div]
    rw [he] at hhpow
    have hm := mul_le_mul_of_nonneg_left hhpow hA
    have he' : A * (b / A) = b := by field_simp
    exact hm.trans_eq he'

lemma clipping_scale {σ C h p : ℝ} (hσ : 0 < σ) (hC : 0 < C) (hh : 0 < h)
    (hhC : h ≤ C) (hp : 0 < p) :
    let τ := σ * (C / h) ^ (1 / p)
    0 < τ ∧ σ ≤ τ ∧ C * σ ^ p = h * τ ^ p ∧
    h ^ 2 * τ ^ 2 = C ^ (2 / p) * σ ^ 2 * h ^ (2 - 2 / p) := by
  let τ := σ * (C / h) ^ (1 / p)
  have hc : 0 < C / h := div_pos hC hh
  have ht : 0 < τ := mul_pos hσ (Real.rpow_pos_of_pos hc _)
  have hch : 1 ≤ C / h := (le_div_iff₀ hh).mpr (by simpa using hhC)
  have hpow : 1 ≤ (C / h) ^ (1 / p) := Real.one_le_rpow hch (by positivity)
  refine ⟨ht, ?_, ?_, ?_⟩
  · nlinarith
  · rw [Real.mul_rpow hσ.le (by positivity), ← Real.rpow_mul hc.le,
      one_div_mul_cancel hp.ne', Real.rpow_one]
    field_simp
  · have he : τ ^ 2 = σ ^ 2 * (C / h) ^ (2 / p) := by
      dsimp [τ]
      rw [mul_pow, ← Real.rpow_natCast ((C / h) ^ (1 / p)) 2,
        ← Real.rpow_mul hc.le]
      congr 2
      norm_num
      ring
    rw [he, Real.div_rpow hC.le hh.le, Real.rpow_sub hh,
      Real.rpow_two]
    ring

lemma deterministic_constraints {μ L η h s : ℝ} (hs : 1 ≤ s)
    (hsq : s ^ 2 * μ = L) (hh : h = μ * η) (hh0 : 0 ≤ h)
    (hsmall : h ≤ 1 / (8 * s ^ (5 / 2 : ℝ))) :
    8 * L * η ≤ 1 ∧ 32 * s * η ^ 2 * L ^ 2 ≤ 1 := by
  have hs0 : 0 < s := by linarith
  have hp : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
  have hb : h * (8 * s ^ (5 / 2 : ℝ)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp hsmall
  have hpow : s ^ 2 ≤ s ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
  have hsqpow : (s ^ (5 / 2 : ℝ)) ^ 2 = s ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs0.le]
    norm_num
  have hbsq : (h * (8 * s ^ (5 / 2 : ℝ))) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hh0 hp.le]
  rw [mul_pow, mul_pow, hsqpow] at hbsq
  constructor
  · have hb' := mul_le_mul_of_nonneg_left hpow hh0
    have he : 8 * L * η = 8 * h * s ^ 2 := by rw [← hsq, hh]; ring
    rw [he]
    nlinarith only [hb, hb']
  · have he : 32 * s * η ^ 2 * L ^ 2 = 32 * h ^ 2 * s ^ 5 := by
      rw [← hsq, hh]
      ring
    rw [he]
    nlinarith [sq_nonneg h, pow_nonneg hs0.le 5]

lemma estimator_tuning {σ C d μ ν p : ℝ} (hσ : 0 ≤ σ) (hC : 1 ≤ C)
    (hd : 1 ≤ d) (hμ : 0 < μ) (hν : 0 < ν) (hp : 1 < p) :
    let h := (d + (C ^ (2 / p) * σ ^ 2 / (μ * ν)) ^ (1 / (2 - 2 / p)))⁻¹
    let η := h / μ
    let τ := σ * (C / h) ^ (1 / p)
    let B := C * σ ^ p * τ ^ (1 - p)
    let V := C * σ ^ p * τ ^ (2 - p)
    let Q := C * σ ^ p * τ ^ (4 - p)
    0 < h ∧ h ≤ 1 / d ∧ 0 ≤ τ ∧ σ ≤ τ ∧ η * V ≤ ν ∧
    B ^ 2 = μ * η * V ∧ μ * η ^ 2 * Q = η * V ^ 2 := by
  let h := (d + (C ^ (2 / p) * σ ^ 2 / (μ * ν)) ^ (1 / (2 - 2 / p)))⁻¹
  let η := h / μ
  let τ := σ * (C / h) ^ (1 / p)
  have hp0 : 0 < p := by linarith
  have hd0 : 0 < d := by linarith
  have hC0 : 0 < C := by linarith
  have hr : 0 < 2 - 2 / p := by
    have hh : 2 / p < 2 := (div_lt_iff₀ hp0).mpr (by linarith)
    linarith
  obtain ⟨hh, hhd, hnoise⟩ := inverse_power_noise
    (show 0 ≤ C ^ (2 / p) * σ ^ 2 by positivity) hd0 (mul_pos hμ hν) hr
  have hh0 : 0 < h := hh
  have hhC : h ≤ C := by
    have hd1 : 1 / d ≤ 1 := (div_le_one hd0).mpr hd
    exact hhd.trans (hd1.trans hC)
  have hη : h = μ * η := by dsimp [η]; field_simp
  by_cases hσ0 : σ = 0
  · refine ⟨hh, hhd, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hσ0, Real.zero_rpow hp0.ne', hν.le]
  have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
  obtain ⟨hτ, hστ, hbalance, hscale⟩ := clipping_scale hσpos hC0 hh0 hhC hp0
  change C * σ ^ p = h * τ ^ p at hbalance
  change 0 < τ at hτ
  change h ^ 2 * τ ^ 2 = C ^ (2 / p) * σ ^ 2 * h ^ (2 - 2 / p) at hscale
  have hV : C * σ ^ p * τ ^ (2 - p) = h * τ ^ 2 := by
    rw [hbalance, mul_assoc, ← Real.rpow_add hτ]
    norm_num
  have hm := balanced_moments hτ hbalance hη
  refine ⟨hh, hhd, hτ.le, hστ, ?_, hm.1, hm.2⟩
  change η * (C * σ ^ p * τ ^ (2 - p)) ≤ ν
  rw [hV]
  have he : η * (h * τ ^ 2) = h ^ 2 * τ ^ 2 / μ := by dsimp [η]; ring
  rw [he, hscale]
  exact (div_le_iff₀ hμ).mpr (by nlinarith only [hnoise])

noncomputable def threshold (L μ ρ ε : ℝ) : ℝ :=
  (36864 * ρ ^ 2 / μ ^ 3 + 1 / (Real.sqrt (L / μ) ^ 5 * ε))⁻¹

noncomputable def noiseLevel (L μ ρ ε : ℝ) : ℝ :=
  (2 ^ 17 / ε + 3200 * Real.sqrt (L / μ) ^ 5 / threshold L μ ρ ε)⁻¹

noncomputable def stepFraction (L μ ρ σ p ε : ℝ) : ℝ :=
  (8 * Real.sqrt (L / μ) ^ (5 / 2 : ℝ) +
    ((2 ^ 64 : ℝ) ^ (2 / p) * σ ^ 2 / (μ * noiseLevel L μ ρ ε)) ^ (1 / (2 - 2 / p)))⁻¹

noncomputable def clipRadius (L μ ρ σ p ε : ℝ) : ℝ :=
  σ * (2 ^ 64 / stepFraction L μ ρ σ p ε) ^ (1 / p)

lemma tuning_conditions {L μ ρ σ p ε : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hσ : 0 ≤ σ) (hp : 1 < p) (hε : 0 < ε) :
    let t := threshold L μ ρ ε
    let ν := noiseLevel L μ ρ ε
    let h := stepFraction L μ ρ σ p ε
    let η := h / μ
    let τ := clipRadius L μ ρ σ p ε
    let lam := 32 * Real.sqrt (L / μ) / μ
    let B := 2 ^ 64 * σ ^ p * τ ^ (1 - p)
    let V := 2 ^ 64 * σ ^ p * τ ^ (2 - p)
    let Q := 2 ^ 64 * σ ^ p * τ ^ (4 - p)
    0 < t ∧ 0 < ν ∧ 0 < h ∧ h ≤ 1 ∧ 0 < η ∧ 0 ≤ τ ∧ σ ≤ τ ∧
    36864 * ρ ^ 2 * t ≤ μ ^ 3 ∧ 8 * L * η ≤ 1 ∧
    32 * Real.sqrt (L / μ) * η ^ 2 * L ^ 2 ≤ 1 ∧
    96 * lam * L * η * V ≤ t ∧ 4 * lam * L ^ 2 * η ^ 2 * Q ≤ t * V ∧
    B ^ 2 ≤ μ * η * V ∧ η * V ≤ ν ∧ ν ≤ ε / 2 ^ 17 := by
  let s := Real.sqrt (L / μ)
  have hk : 1 ≤ L / μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  have hs : 1 ≤ s := by simpa [s] using Real.sqrt_le_sqrt hk
  have hs0 : 0 < s := by linarith
  have hsq : s ^ 2 * μ = L := by
    dsimp [s]
    rw [Real.sq_sqrt (by linarith : 0 ≤ L / μ)]
    field_simp
  have ha : 0 < s ^ 5 := by positivity
  obtain ⟨ht, hlocal, hν, hνε, hνt, _⟩ := thresholds hμ hε ha (ρ := ρ)
  have hd : 1 ≤ 8 * s ^ (5 / 2 : ℝ) := by
    have hh := Real.one_le_rpow hs (by norm_num : (0 : ℝ) ≤ 5 / 2)
    linarith
  obtain ⟨hh, hhd, hτ, hστ, hnoise, hB, hQ⟩ := estimator_tuning hσ
    (by norm_num : (1 : ℝ) ≤ 2 ^ 64) hd hμ hν hp
  let h := stepFraction L μ ρ σ p ε
  let η := h / μ
  let τ := clipRadius L μ ρ σ p ε
  let V := 2 ^ 64 * σ ^ p * τ ^ (2 - p)
  have hh0 : 0 < h := hh
  have hη : 0 < η := div_pos hh0 hμ
  have he : h = μ * η := by dsimp [η]; field_simp
  obtain ⟨hstep, hsmall⟩ := deterministic_constraints hs hsq he hh0.le hhd
  have hVV : 0 ≤ V := by dsimp [V]; positivity
  have hlam : (32 * s / μ) * μ = 32 * s := by field_simp
  have hc := moment_constraints hμ hη hs hsq rfl hlam hVV hnoise hνt hB.le hQ
  have hh1 : h ≤ 1 := hhd.trans ((div_le_one (by linarith : 0 < 8 * s ^ (5 / 2 : ℝ))).mpr hd)
  exact ⟨ht, hν, hh0, hh1, hη, hτ, hστ, hlocal, hstep, hsmall,
    hc.1, hc.2.1, hc.2.2, hnoise, hνε⟩

lemma window_noise_accuracy {μ η ε ν : ℝ} {m : ℕ}
    (hμ : 0 < μ) (hη : 0 < η) (hε : 0 < ε) (hν : 0 ≤ ν)
    (hsmall : ν ≤ ε / 2 ^ 17) (hm : 8 / (μ * η) ≤ (m : ℝ) + 1) :
    2 * ((ε + 18560 * ν) / μ) / η / (m + 1) + 580 * ν ≤ ε := by
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hden : 8 ≤ μ * η * (m + 1) := by
    have hh := (div_le_iff₀ (mul_pos hμ hη)).mp hm
    nlinarith only [hh]
  have hn : 0 ≤ 2 * (ε + 18560 * ν) := by positivity
  have hh := div_le_div_of_nonneg_left hn (by norm_num : (0 : ℝ) < 8) hden
  have he : 2 * ((ε + 18560 * ν) / μ) / η / (m + 1) =
      (2 * (ε + 18560 * ν)) / (μ * η * (m + 1)) := by
    field_simp
  rw [he]
  norm_num at hsmall
  linarith

lemma warmup_decay {μ h s Δ ε : ℝ} (hμ : 0 < μ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hs : 0 ≤ s) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (1 - h / 64) ^ ⌈64 / h * Real.log (1 + 48 * s * Δ / ε)⌉₊ *
      (48 * s * Δ / μ) ≤ ε / μ := by
  have he : (48 * s * Δ / μ) / (ε / μ) = 48 * s * Δ / ε := by field_simp
  have hg := PLGradient.geometric_budget 64 h (48 * s * Δ / μ) (ε / μ)
    hh (by linarith) (by positivity) (div_pos hε hμ)
  simpa only [he] using hg

lemma warmup_potential {μ η s Δ ε V ν W : ℝ}
    (hμ : 0 < μ) (hη : 0 < η) (hh1 : μ * η ≤ 1)
    (hs : 0 ≤ s) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hW : W ≤ 48 * s * Δ / μ) (hnoise : η * V ≤ ν) :
    (1 - μ * η / 64) ^ ⌈64 / (μ * η) * Real.log (1 + 48 * s * Δ / ε)⌉₊ * W +
      (290 * η ^ 2 * V) / (μ * η / 64) ≤ (ε + 18560 * ν) / μ := by
  have hd := warmup_decay hμ (mul_pos hμ hη) hh1 hs hΔ hε
  have hcoef : 0 ≤ (1 - μ * η / 64) ^
      ⌈64 / (μ * η) * Real.log (1 + 48 * s * Δ / ε)⌉₊ :=
    pow_nonneg (by linarith) _
  have hw := (mul_le_mul_of_nonneg_left hW hcoef).trans hd
  have he : (290 * η ^ 2 * V) / (μ * η / 64) = 18560 * (η * V) / μ := by
    field_simp
    ring
  rw [he]
  have hn := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnoise (by norm_num : (0 : ℝ) ≤ 18560)) hμ.le
  calc
    _ ≤ ε / μ + 18560 * ν / μ := add_le_add hw hn
    _ = _ := by ring

lemma rounded_calls {h A D : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (hD : 1 / h ≤ D) :
    ⌈64 / h * Real.log (1 + A)⌉₊ + ⌈8 / h⌉₊ ≤
      ⌈64 * D * (Real.log (1 + A) + 1)⌉₊ + 1 := by
  have hl : 0 ≤ Real.log (1 + A) := Real.log_nonneg (by linarith)
  have hn := Nat.ceil_lt_add_one (show 0 ≤ 64 / h * Real.log (1 + A) by positivity)
  have hm := Nat.ceil_lt_add_one (show 0 ≤ 8 / h by positivity)
  have hb := Nat.le_ceil (64 * D * (Real.log (1 + A) + 1))
  have hd := mul_le_mul_of_nonneg_right hD (show 0 ≤ 64 * (Real.log (1 + A) + 1) by positivity)
  have he : 64 / h * Real.log (1 + A) + 8 / h ≤ 64 * D * (Real.log (1 + A) + 1) := by
    have h8 : 0 ≤ 56 / h := by positivity
    simp only [div_eq_mul_inv] at hd h8 ⊢
    nlinarith only [hd, h8]
  have hlt : ((⌈64 / h * Real.log (1 + A)⌉₊ + ⌈8 / h⌉₊ : ℕ) : ℝ) <
      ((⌈64 * D * (Real.log (1 + A) + 1)⌉₊ : ℕ) : ℝ) + 2 := by
    push_cast
    linarith
  have hnat : ⌈64 / h * Real.log (1 + A)⌉₊ + ⌈8 / h⌉₊ <
      ⌈64 * D * (Real.log (1 + A) + 1)⌉₊ + 2 := by exact_mod_cast hlt
  omega

lemma inverse_step_formula {L μ ρ σ p ε : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hε : 0 < ε) :
    1 / stepFraction L μ ρ σ p ε =
      8 * Real.sqrt (L / μ) ^ (5 / 2 : ℝ) +
      ((2 ^ 64 : ℝ) ^ (2 / p) * σ ^ 2 *
        (134272 / (μ * ε) + 117964800 * Real.sqrt (L / μ) ^ 5 * ρ ^ 2 / μ ^ 4)) ^
          (1 / (2 - 2 / p)) := by
  have hk : 0 < L / μ := div_pos (hμ.trans_le hμL) hμ
  have ha : 0 < Real.sqrt (L / μ) ^ 5 := pow_pos (Real.sqrt_pos.mpr hk) _
  have hν := (thresholds hμ hε ha (ρ := ρ)).2.2.2.2.2
  change noiseLevel L μ ρ ε = _ at hν
  rw [stepFraction, one_div, inv_inv, hν]
  congr 2
  norm_num
  field_simp

lemma parameter_powers {κ p : ℝ} (hκ : 0 ≤ κ) (hp : 1 < p) :
    Real.sqrt κ ^ (5 / 2 : ℝ) = κ ^ (5 / 4 : ℝ) ∧
    Real.sqrt κ ^ 5 = κ ^ (5 / 2 : ℝ) ∧ 1 / (2 - 2 / p) = p / (2 * (p - 1)) := by
  have hp0 : p ≠ 0 := by linarith
  have hp1 : p - 1 ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hκ]
    norm_num
  · rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hκ]
    norm_num
  · field_simp

lemma inverse_step_bound {L μ ρ σ p ε : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hp : 1 < p) (hε : 0 < ε) :
    1 / stepFraction L μ ρ σ p ε ≤ 8 * ((L / μ) ^ (5 / 4 : ℝ) +
      (((2 ^ 64 : ℝ) ^ (2 / p) * 2 ^ 27) * σ ^ 2 *
        (1 / (μ * ε) + (L / μ) ^ (5 / 2 : ℝ) * ρ ^ 2 / μ ^ 4)) ^ (p / (2 * (p - 1)))) := by
  have hk : 0 ≤ L / μ := (div_pos (hμ.trans_le hμL) hμ).le
  obtain ⟨he1, he2, he3⟩ := parameter_powers hk hp
  rw [inverse_step_formula hμ hμL hε, he1, he2, he3]
  have hq : 0 ≤ p / (2 * (p - 1)) := by
    have hp0 : 0 < p := by linarith
    have hp1 : 0 < p - 1 := by linarith
    positivity
  have h1 : 0 ≤ 1 / (μ * ε) := by positivity
  have h2 : 0 ≤ (L / μ) ^ (5 / 2 : ℝ) * ρ ^ 2 / μ ^ 4 := by positivity
  have ha : 134272 / (μ * ε) + 117964800 * (L / μ) ^ (5 / 2 : ℝ) * ρ ^ 2 / μ ^ 4 ≤
      2 ^ 27 * (1 / (μ * ε) + (L / μ) ^ (5 / 2 : ℝ) * ρ ^ 2 / μ ^ 4) := by
    simp only [div_eq_mul_inv] at h1 h2 ⊢
    norm_num at h1 h2 ⊢
    nlinarith only [h1, h2]
  have hc : 0 ≤ (2 ^ 64 : ℝ) ^ (2 / p) * σ ^ 2 := by positivity
  have hb := mul_le_mul_of_nonneg_left ha hc
  have hb' : (2 ^ 64 : ℝ) ^ (2 / p) * σ ^ 2 *
      (134272 / (μ * ε) + 117964800 * (L / μ) ^ (5 / 2 : ℝ) * ρ ^ 2 / μ ^ 4) ≤
      (((2 ^ 64 : ℝ) ^ (2 / p) * 2 ^ 27) * σ ^ 2 *
        (1 / (μ * ε) + (L / μ) ^ (5 / 2 : ℝ) * ρ ^ 2 / μ ^ 4)) := by
    nlinarith only [hb]
  have hpw := Real.rpow_le_rpow (by positivity) hb' hq
  have hn : 0 ≤ ((((2 ^ 64 : ℝ) ^ (2 / p) * 2 ^ 27) * σ ^ 2 *
        (1 / (μ * ε) + (L / μ) ^ (5 / 2 : ℝ) * ρ ^ 2 / μ ^ 4)) ^ (p / (2 * (p - 1)))) := by positivity
  linarith

lemma coefficient_power (p : ℝ) :
    (2 ^ 64 : ℝ) ^ (2 / p) * 2 ^ 27 = (2 : ℝ) ^ (128 / p + 27) := by
  rw [← Real.rpow_natCast (2 : ℝ) 64, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_natCast (2 : ℝ) 27, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

lemma total_iterations {L μ ρ σ p Δ ε : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hσ : 0 ≤ σ) (hp : 1 < p) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    let h := stepFraction L μ ρ σ p ε
    ⌈64 / h * Real.log (1 + 48 * Real.sqrt (L / μ) * Δ / ε)⌉₊ + ⌈8 / h⌉₊ ≤
    ⌈512 * ((L / μ) ^ (5 / 4 : ℝ) +
      ((2 : ℝ) ^ (128 / p + 27) * σ ^ 2 *
        (1 / (μ * ε) + (L / μ) ^ (5 / 2 : ℝ) * ρ ^ 2 / μ ^ 4)) ^ (p / (2 * (p - 1)))) *
      (Real.log (1 + 48 * Real.sqrt (L / μ) * Δ / ε) + 1)⌉₊ + 1 := by
  have hh := (tuning_conditions hμ hμL hσ hp hε (ρ := ρ)).2.2.1
  have hb := inverse_step_bound hμ hμL hp hε (ρ := ρ) (σ := σ)
  rw [coefficient_power] at hb
  have hr := rounded_calls hh (show 0 ≤ 48 * Real.sqrt (L / μ) * Δ / ε by positivity) hb
  convert hr using 1
  congr 2
  ring

end OracleTemplate.RobustPLPotential
