import LongTails.Proofs.AdamGeneralizedAnalysis
import LongTails.Proofs.AdamCenteredProcess

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamGeneralizedDescent

open OracleTemplate.Adam AdamGeneralizedPath
open LongTails.Algorithms.GeneralizedSmoothAdam AdamGeneralizedAnalysis
open AdamGeneralizedTrajectory AdamGeneralizedNoise AdamNormalizedMoments

lemma signal_path {d : ℕ} {f : Point d → ℝ} {h : Point d → Point d}
    {L0 L1 lower K M β η τ ρ B C : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K) (hLK : L1 ≤ K) (hM : 1 ≤ M)
    (hcurv : L0 + 2 * L1 * K ≤ K ^ 2)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hρq : 1 / 4 ≤ 1 - ρ) (hbρ : (1 + β) / 2 ≤ 1 - ρ)
    (hf : ∀ x, HasGradientAt f (h x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 → ‖h y - h x‖ ≤ (L0 + L1 * ‖h x‖) * ‖y - x‖)
    (hbound : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower))
    (s : ℕ → Point d × Point d × Point d) (g Q signal : ℕ → Point d)
    (hv : ∀ t i, 0 < (s t).2.2 i) (hm0 : (s 0).2.1 = 0)
    (hm : ∀ t, (s (t + 1)).2.1 = β • (s t).2.1 + (1 - β) • g t)
    (hrec : ∀ t i, (s (t + 1)).2.2 i = (1 - ρ) * (s t).2.2 i + ρ * (g t i) ^ 2)
    (hx : ∀ t, (s (t + 1)).1 = (s t).1 - η • direction τ (s (t + 1)).2.1 (s (t + 1)).2.2)
    (hmnorm : ∀ t i, ρ * ((s t).2.1 i) ^ 2 ≤ (s t).2.2 i)
    (n : ℕ) (hB : 1 ≤ B) (hvn : ∀ i, (s n).2.2 i ≤ (s 0).2.2 i * B)
    (hlog : -(n : ℝ) * Real.log (1 - ρ) ≤ 2)
    (hheight : ∀ t < n, 1 + f (s t).1 - lower ≤ M)
    (hsmall : K * (1 + 4 * (β / (1 - β))) * (η / Real.sqrt ρ) * Real.sqrt d ≤ 1 / 2)
    (hbias : ∀ t < n, ‖Q t - signal t‖ ≤ C) :
    η * (∑ t ∈ Finset.range n, ⟪h (s t).1, signal t⟫) ≤ f (s 0).1 - lower +
      (∑ t ∈ Finset.range n, -η * ⟪h (s t).1, direction τ (g t) (s (t + 1)).2.2 - Q t⟫) +
      n * η * (2 * K * M) * C +
      M * (K ^ 2 * (1 + (β / (1 - β)) ^ 2) * η ^ 2 * d / ρ +
        6 * K * (β / (1 - β)) * (η / Real.sqrt ρ) * d) * (2 + Real.log B) := by
  let z := fun t => auxiliaryPoint β η τ (s t)
  let q := fun t => direction τ (g t) (s (t + 1)).2.2
  let e := fun t => residual β η τ (s t) (s (t + 1)).2.2
  let a := η / Real.sqrt ρ * Real.sqrt d
  let r := β / (1 - β)
  let R := (1 + 4 * r) * a
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hz0 : z 0 = (s 0).1 := by
    have he : direction τ (s 0).2.1 (s 0).2.2 = 0 := by
      apply PiLp.ext
      intro i
      simp [direction, hm0]
    simp only [z, auxiliaryPoint, he, smul_zero, sub_zero]
  have hz (t) : z (t + 1) = z t - η • q t + e t := by
    have hh := auxiliary_update (η := η) (ne_of_lt hβ1) hτ (s t) (g t) (s (t + 1)).2.2 (hv t) (hv (t + 1))
    have he : s (t + 1) = ((s t).1 - η • direction τ (β • (s t).2.1 + (1 - β) • g t)
        (s (t + 1)).2.2, β • (s t).2.1 + (1 - β) • g t, (s (t + 1)).2.2) := by
      apply Prod.ext
      · rw [hx t, hm t]
      · exact Prod.ext (hm t) rfl
    dsimp [z, q, e]
    rw [he]
    exact hh
  have hdecay (t i) : (1 - ρ) * (s t).2.2 i ≤ (s (t + 1)).2.2 i := by
    rw [hrec t i]
    exact le_add_of_nonneg_right (mul_nonneg hρ.le (sq_nonneg _))
  have hnear (t) : ‖z t - (s t).1‖ ≤ R ∧ ‖z t - η • q t - (s t).1‖ ≤ R ∧
      ‖z t - η • q t + e t - (s t).1‖ ≤ R := by
    have hzd := auxiliary_distance hβ hβ1 hη hτ hρ (s t) (hv t) (hmnorm t)
    have hqd := direction_norm_bound hρ hτ (g t) (s (t + 1)).2.2 (hv (t + 1)) (fun i => by
      rw [hrec t i]
      have hp := mul_nonneg (sub_nonneg.2 hρ1.le) (hv t i).le
      linarith)
    have hed := residual_norm hβ hβ1 hη hτ hρ hρq (s t) (s (t + 1)).2.2
      (hv t) (hv (t + 1)) (hdecay t) (hmnorm t)
    apply shifted_radius ha hr
    · convert hzd using 1; dsimp [r, a]; ring
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
      have hh := mul_le_mul_of_nonneg_left hqd hη
      convert hh using 1; dsimp [a]; ring
    · convert hed using 1; dsimp [r, a]; ring
  have hR : K * R ≤ 1 / 2 := by dsimp [R, r, a]; nlinarith [hsmall]
  have hp := AdamAuxiliaryDescent.local_signal_path hL0 hL1 hK hLK hM hcurv hη hf hlower hs hbound
    (fun t => (s t).1) z q Q signal e n hz0 (fun t _ => hz t) hheight hR
    (fun t _ => (hnear t).1) (fun t _ => (hnear t).2.1) (fun t _ => (hnear t).2.2) hbias
  have hpaths := normalized_path_sums (g := g) (m := fun t => (s t).2.1)
    (v := fun t => (s t).2.2) hβ hβ1 hρ hρ1 hbρ hτ (hv 0) hm0 hm hrec n
    (by linarith : 0 < B) hvn hlog
  have haux := auxiliary_path_sum s β η τ n hm0 hpaths.2
  have hres := residual_path_sum s hβ hβ1 hη hτ hρ hρq hv hmnorm hdecay n hB hvn hlog
  have hM0 : 0 ≤ M := by linarith
  calc
    _ ≤ f (s 0).1 - lower + (∑ t ∈ Finset.range n, -η * ⟪h (s t).1, q t - Q t⟫) +
        n * η * (2 * K * M) * C +
        (K ^ 2 * M) / 2 * (η * β / (1 - β)) ^ 2 * (2 * d * ((2 + Real.log B) / ρ)) +
        (K ^ 2 * M) * η ^ 2 * (d * ((2 + Real.log B) / ρ)) +
        (2 * K * M) * (3 * (β / (1 - β)) * (η / Real.sqrt ρ) * d * (2 + Real.log B)) := by
      apply hp.trans
      have h1 := mul_le_mul_of_nonneg_left haux (by positivity : 0 ≤ (K ^ 2 * M) / 2)
      have h2 := mul_le_mul_of_nonneg_left hpaths.1 (by positivity : 0 ≤ K ^ 2 * M * η ^ 2)
      have h3 := mul_le_mul_of_nonneg_left hres (by positivity : 0 ≤ 2 * K * M)
      dsimp [z, q, e] at h1 h2 h3 ⊢
      nlinarith
    _ = _ := by dsimp [q]; ring

lemma original_prefix {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {f : Point d → ℝ} {h : Point d → Point d} {L0 L1 lower K M β η τ vinit σ : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K) (hLK : L1 ≤ K) (hM : 1 ≤ M)
    (hf : ∀ x, HasGradientAt f (h x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 → ‖h y - h x‖ ≤ (L0 + L1 * ‖h x‖) * ‖y - x‖)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower)) (hcurv : L0 + 2 * L1 * K ≤ K ^ 2)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hvinit : 0 < vinit)
    (hg : Measurable (Function.uncurry g)) (hi : ∀ x, Integrable (g x) P)
    (hmean : ∀ x, (∫ ω, g x ω ∂P) = h x)
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - h x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - h x‖ ^ 2 ∂P) ≤ σ ^ 2)
    {T n : ℕ} (hT : 2 ≤ T) (hn : n ≤ T) (hbmem : (1 + β) / 2 ≤ 1 - 1 / (T : ℝ))
    (x0 : Point d) (ξ : ℕ → Ω)
    (hheight : ∀ t < n, 1 + f (trajectory g β (1 / T) η τ vinit x0 ξ t).1 - lower ≤ M)
    (hsmall : K * (1 + 4 * (β / (1 - β))) * (η / Real.sqrt (1 / (T : ℝ))) * Real.sqrt d ≤ 1 / 2) :

    η * (∑ t ∈ Finset.range n, ⟪h (trajectory g β (1 / T) η τ vinit x0 ξ t).1,
      normalized (fun i => (1 - 1 / (T : ℝ)) * (trajectory g β (1 / T) η τ vinit x0 ξ t).2.2 i)
        (1 / T) τ (h (trajectory g β (1 / T) η τ vinit x0 ξ t).1)⟫) ≤
      f x0 - lower +
      AdamExponentialProcess.partialSum (stateTransition g β (1 / T) η τ)
        (innovation P g h (vinit / 4) (1 / T) τ η)
        (x0, 0, WithLp.toLp 2 (fun _ => vinit)) ξ n +
      n * η * (2 * K * M) * (12 * Real.sqrt (1 / (T : ℝ)) / vinit * σ ^ 2) +
      M * (K ^ 2 * (1 + (β / (1 - β)) ^ 2) * η ^ 2 * d / (1 / (T : ℝ)) +
        6 * K * (β / (1 - β)) * (η / Real.sqrt (1 / (T : ℝ))) * d) *
          (2 + Real.log (energyEnvelope g β (1 / T) η τ vinit x0 ξ n)) := by
  let ρ : ℝ := 1 / T
  let s := trajectory g β ρ η τ vinit x0 ξ
  let u := h
  let Q := fun t => meanResponse P g ρ τ (s t)
  let signal := fun t => normalized (fun i => (1 - ρ) * (s t).2.2 i) ρ τ (h (s t).1)
  let replies := fun t => g (s t).1 (ξ t)
  let B := energyEnvelope g β ρ η τ vinit x0 ξ n
  have ht : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have htpos : (0 : ℝ) < T := by linarith
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρT : ρ * T = 1 := by dsimp [ρ]; field_simp
  have hρhalf : ρ ≤ 1 / 2 := by nlinarith
  have hρ1 : ρ < 1 := by linarith
  have hρq : 1 / 4 ≤ 1 - ρ := by linarith
  have hbρ : β ≤ 1 - ρ := by dsimp [ρ]; linarith
  have hv (t i) : 0 < (s t).2.2 i := secondMoment_pos g β η τ hvinit hρ.le hρ1 x0 ξ t i
  have hm0 : (s 0).2.1 = 0 := rfl
  have hm (t) : (s (t + 1)).2.1 = β • (s t).2.1 + (1 - β) • replies t := rfl
  have hr (t i) : (s (t + 1)).2.2 i = (1 - ρ) * (s t).2.2 i + ρ * (replies t i) ^ 2 := rfl
  have hx (t) : (s (t + 1)).1 = (s t).1 - η • direction τ (s (t + 1)).2.1 (s (t + 1)).2.2 := rfl
  have hmn (t i) : ρ * ((s t).2.1 i) ^ 2 ≤ (s t).2.2 i :=
    momentum_normalized g η τ hβ hβ1.le hρ.le hρ1 hbρ hvinit x0 ξ t i
  have hB : 1 ≤ B := by
    dsimp [B, energyEnvelope]
    have hnz : 0 ≤ ∑ t ∈ Finset.range n, ‖g (trajectory g β ρ η τ vinit x0 ξ t).1 (ξ t)‖ ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg hρ.le hvinit.le) hnz)
  have hBn (i) : (s n).2.2 i ≤ (s 0).2.2 i * B :=
    AdamGeneralizedPath.coordinate_accumulator_upper (v := fun t => (s t).2.2)
      (g := replies) hρ.le hρ1 hvinit (fun _ => rfl) hr n i
  have hlog : -(n : ℝ) * Real.log (1 - ρ) ≤ 2 := by
    have hb := AdamAccumulator.decay_log_bound hT
    have hlogneg : Real.log (1 - ρ) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    have hnr : (n : ℝ) ≤ T := by exact_mod_cast hn
    dsimp [ρ] at hlogneg ⊢
    nlinarith
  have hbi (t : ℕ) (h_t : t < n) : ‖Q t - signal t‖ ≤ 12 * Real.sqrt ρ / vinit * σ ^ 2 := by
    have htT : t < T := Nat.lt_of_lt_of_le h_t hn
    have hh := response_bias P hg (s t) (h (s t).1) (hi _) (hmean _) (h2 _)
      (by positivity : 0 < vinit / 4)
      (fun i => predictable_secondMoment_lower g β η τ hvinit hT htT x0 ξ i) hρ.le hτ (hvar _)
    convert hh using 1; ring
  have hresult := signal_path hL0 hL1 hK hLK hM hcurv hβ hβ1 hη hτ hρ hρ1 hρq hbmem
    hf hlower hs hgrad s replies Q signal hv hm0 hm hr hx hmn n hB hBn hlog hheight hsmall hbi
  have hsum : (∑ t ∈ Finset.range n, -η * ⟪u (s t).1,
      direction τ (replies t) (s (t + 1)).2.2 - Q t⟫) =
      AdamExponentialProcess.partialSum (stateTransition g β ρ η τ)
        (innovation P g u (vinit / 4) ρ τ η) (x0, 0, WithLp.toLp 2 (fun _ => vinit)) ξ n := by
    unfold AdamExponentialProcess.partialSum
    apply Finset.sum_congr rfl
    intro t ht
    have htT : t < T := Nat.lt_of_lt_of_le (Finset.mem_range.1 ht) hn
    rw [AdamGeneralizedTrajectory.stateAt_initial]
    dsimp [innovation]
    rw [flooredResponse_trajectory g β η τ hvinit hT htT x0 ξ (ξ t),
      flooredMean_trajectory P g β η τ hvinit hT htT x0 ξ, response_direction]
    rfl
  rw [hsum] at hresult
  exact hresult

lemma original_calibrated {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {f : Point d → ℝ} {h : Point d → Point d} {L0 L1 lower K β a σ : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K) (hLK : L1 ≤ K)
    (hf : ∀ x, HasGradientAt f (h x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 → ‖h y - h x‖ ≤ (L0 + L1 * ‖h x‖) * ‖y - x‖)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower)) (hcurv : L0 + 2 * L1 * K ≤ K ^ 2)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (ha : 0 ≤ a)
    (hg : Measurable (Function.uncurry g)) (hi : ∀ x, Integrable (g x) P)
    (hmean : ∀ x, (∫ ω, g x ω ∂P) = h x)
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - h x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - h x‖ ^ 2 ∂P) ≤ σ ^ 2)
    {T : ℕ} (hT : 2 ≤ T) (hbmem : (1 + β) / 2 ≤ 1 - 1 / (T : ℝ))
    (hscale : a * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ))
    (hrscale : (β / (1 - β) * a) * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ))
    (x0 : Point d) (ξ : ℕ → Ω) :
    let η := a / Real.sqrt T
    let s := trajectory g β (1 / T) η 1 (1 + σ ^ 2) x0 ξ
    let M := height f lower g β (1 / T) η 1 (1 + σ ^ 2) x0 ξ T
    let B := energyEnvelope g β (1 / T) η 1 (1 + σ ^ 2) x0 ξ T
    let N := AdamExponentialProcess.partialSum (stateTransition g β (1 / T) η 1)
      (innovation P g h ((1 + σ ^ 2) / 4) (1 / T) 1 η)
      (x0, 0, WithLp.toLp 2 (fun _ => 1 + σ ^ 2)) ξ T
    let D := η * ∑ t ∈ Finset.range T, ⟪h (s t).1,
      normalized (fun i => (1 - 1 / (T : ℝ)) * (s t).2.2 i) (1 / T) 1 (h (s t).1)⟫
    0 ≤ D ∧ D ≤ f x0 - lower + M * (2 + Real.log B) + M + N := by
  let η := a / Real.sqrt T
  let v := 1 + σ ^ 2
  let r := β / (1 - β)
  let s := trajectory g β (1 / T) η 1 v x0 ξ
  let M := height f lower g β (1 / T) η 1 v x0 ξ T
  let B := energyEnvelope g β (1 / T) η 1 v x0 ξ T
  let N := AdamExponentialProcess.partialSum (stateTransition g β (1 / T) η 1)
    (innovation P g h (v / 4) (1 / T) 1 η) (x0, 0, WithLp.toLp 2 (fun _ => v)) ξ T
  let D := η * ∑ t ∈ Finset.range T, ⟪h (s t).1,
    normalized (fun i => (1 - 1 / (T : ℝ)) * (s t).2.2 i) (1 / T) 1 (h (s t).1)⟫
  change 0 ≤ D ∧ D ≤ f x0 - lower + M * (2 + Real.log B) + M + N
  have htpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2 htpos
  have hv : 0 < v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hηρ : η / Real.sqrt (1 / (T : ℝ)) = a := by
    dsimp [η]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
    field_simp
  have hη2 : η ^ 2 / (1 / (T : ℝ)) = a ^ 2 := by
    dsimp [η]
    rw [div_pow, Real.sq_sqrt htpos.le]
    field_simp
  have hηroot : η * Real.sqrt (1 / (T : ℝ)) = a / T := by
    dsimp [η]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, div_mul_div_comm, mul_one, ← pow_two, Real.sq_sqrt htpos.le]
  have hM : 1 ≤ M := by
    have hh := AdamLogMoments.le_prefixMaximum (fun t => 1 + f (s t).1 - lower) (Nat.zero_le T)
    have hl := hlower (s 0).1
    exact (by linarith : 1 ≤ 1 + f (s 0).1 - lower).trans hh
  have hB : 1 ≤ B := by
    dsimp [B, energyEnvelope]
    exact le_add_of_nonneg_right (by positivity)
  have hc := AdamGeneralizedParameters.original_calibration ha hr hK hscale hrscale
  have hsmall : K * (1 + 4 * r) * (η / Real.sqrt (1 / (T : ℝ))) * Real.sqrt d ≤ 1 / 2 := by
    rw [hηρ]
    exact hc.2.2
  have hp := original_prefix P hL0 hL1 hK hLK hM hf hlower hs hgrad hcurv hβ hβ1 hη
    (by norm_num : (0 : ℝ) ≤ 1) hv hg hi hmean h2 hvar hT le_rfl hbmem x0 ξ
    (fun t ht => AdamLogMoments.le_prefixMaximum (fun t => 1 + f (s t).1 - lower) ht.le) hsmall
  have hcoeff : K ^ 2 * (1 + r ^ 2) * η ^ 2 * d / (1 / (T : ℝ)) +
      6 * K * r * (η / Real.sqrt (1 / (T : ℝ))) * d = d * (K ^ 2 * (1 + r ^ 2) * a ^ 2 + 6 * K * r * a) := by
    calc
      _ = d * (K ^ 2 * (1 + r ^ 2) * (η ^ 2 / (1 / (T : ℝ))) +
        6 * K * r * (η / Real.sqrt (1 / (T : ℝ)))) := by ring
      _ = _ := by rw [hη2, hηρ]
  have hbias : (T : ℝ) * η * (2 * K * M) * (12 * Real.sqrt (1 / (T : ℝ)) / v * σ ^ 2) ≤ M := by
    have hnv : σ ^ 2 / v ≤ 1 := (div_le_one hv).2 (by dsimp [v]; linarith)
    have he : (T : ℝ) * η * (2 * K * M) * (12 * Real.sqrt (1 / (T : ℝ)) / v * σ ^ 2) =
        M * (24 * K * a) * (σ ^ 2 / v) := by
      calc
        _ = 24 * T * K * M * (η * Real.sqrt (1 / (T : ℝ))) * (σ ^ 2 / v) := by ring
        _ = _ := by rw [hηroot]; field_simp
    rw [he]
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hc.2.1 (by linarith : 0 ≤ M)) hnv
      (div_nonneg (sq_nonneg σ) hv.le) (by linarith : 0 ≤ M * 1)
    simpa using hh
  have hR : 0 ≤ 2 + Real.log B := by linarith [Real.log_nonneg hB]
  have hcoeffBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc.1 (by linarith : 0 ≤ M)) hR
  dsimp only [r] at hcoeff
  rw [hcoeff] at hp
  refine ⟨mul_nonneg hη (Finset.sum_nonneg (fun t _ => inner_normalized_nonneg (by norm_num) _)), ?_⟩
  change D ≤ f x0 - lower + N + _ + _ at hp
  dsimp only [r] at hcoeffBound
  nlinarith

end LongTails.Proofs.AdamGeneralizedDescent
