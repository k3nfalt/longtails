import LongTails.Proofs.AdamGeneralizedParameters
import LongTails.Proofs.AdamGeneralizedLogPath
import LongTails.Proofs.AdamGeneralizedNoise
import LongTails.Proofs.AdamLogMoments

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamGeneralizedAnalysis

open OracleTemplate.Adam LongTails.Algorithms.GeneralizedSmoothAdam
open AdamGeneralizedTrajectory AdamGeneralizedNoise AdamNormalizedMoments

noncomputable def energyEnvelope {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (β ρ η τ vinit : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (n : ℕ) : ℝ :=
  1 + ρ / vinit * ∑ t ∈ Finset.range n, ‖g (trajectory g β ρ η τ vinit x0 ξ t).1 (ξ t)‖ ^ 2

lemma logarithmic_prefix {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {f : Point d → ℝ} {h : Point d → Point d} {L0 L1 lower K β η τ vinit σ : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K)
    (hf : ∀ x, HasGradientAt f (h x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 → ‖h y - h x‖ ≤ (L0 + L1 * ‖h x‖) * ‖y - x‖)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower)) (hcurv : L0 + L1 * K ≤ K ^ 2)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hvinit : 0 < vinit)
    (hg : Measurable (Function.uncurry g)) (hi : ∀ x, Integrable (g x) P)
    (hmean : ∀ x, (∫ ω, g x ω ∂P) = h x)
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - h x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - h x‖ ^ 2 ∂P) ≤ σ ^ 2)
    {T n : ℕ} (hT : 2 ≤ T) (hn : n ≤ T) (hbmem : (1 + β) / 2 ≤ 1 - 1 / (T : ℝ))
    (x0 : Point d) (ξ : ℕ → Ω) :
    Real.log (1 + f (trajectory g β (1 / T) η τ vinit x0 ξ n).1 - lower) ≤
      Real.log (1 + f x0 - lower) +
      AdamExponentialProcess.partialSum (stateTransition g β (1 / T) η τ)
        (innovation P g (fun x => (1 + f x - lower)⁻¹ • h x) (vinit / 4) (1 / T) τ η)
        (x0, 0, WithLp.toLp 2 (fun _ => vinit)) ξ n +
      n * η * K * (12 * Real.sqrt (1 / (T : ℝ)) / vinit * σ ^ 2) +
      (3 * K ^ 2 * (1 + (β / (1 - β)) ^ 2) * η ^ 2 * d / (1 / (T : ℝ)) +
        3 * K * (β / (1 - β)) * (η / Real.sqrt (1 / (T : ℝ))) * d) *
          (2 + Real.log (energyEnvelope g β (1 / T) η τ vinit x0 ξ n)) +
      K * (η * β / (1 - β)) * (Real.sqrt d / Real.sqrt (1 / (T : ℝ))) := by
  let ρ : ℝ := 1 / T
  let s := trajectory g β ρ η τ vinit x0 ξ
  let u := fun x => (1 + f x - lower)⁻¹ • h x
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
  have hu (x) : ‖u x‖ ≤ K := by
    have hp : 0 < 1 + f x - lower := by linarith [hlower x]
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)]
    calc
      _ ≤ (1 + f x - lower)⁻¹ * (K * (1 + f x - lower)) :=
        mul_le_mul_of_nonneg_left (hgrad x) (inv_nonneg.2 hp.le)
      _ = K := by field_simp
  have hsig (t) : 0 ≤ ⟪u (s t).1, signal t⟫ := by
    dsimp [u, signal]
    rw [real_inner_smul_left]
    exact mul_nonneg (inv_nonneg.2 (by linarith [hlower (s t).1])) (inner_normalized_nonneg hτ _)
  have hbi (t : ℕ) (h_t : t < n) : ‖Q t - signal t‖ ≤ 12 * Real.sqrt ρ / vinit * σ ^ 2 := by
    have htT : t < T := Nat.lt_of_lt_of_le h_t hn
    have hh := response_bias P hg (s t) (h (s t).1) (hi _) (hmean _) (h2 _)
      (by positivity : 0 < vinit / 4)
      (fun i => predictable_secondMoment_lower g β η τ hvinit hT htT x0 ξ i) hρ.le hτ (hvar _)
    convert hh using 1; ring
  have hresult := AdamGeneralizedLogPath.centered_path (A := 3 * K ^ 2) (by positivity) hK
    hβ hβ1 hη hτ hρ hρ1 hρq hbmem
    (AdamLogGeometry.log_gradient hf hlower)
    (fun x y => AdamLogGeometry.log_gradient_lipschitz hL0 hL1 hK hf hlower hs hgrad hcurv y x)
    (fun x y => AdamLogGeometry.log_lipschitz hf hlower hgrad y x)
    s replies Q signal hv hm0 hm hr hx hmn n hB hBn hlog (fun t _ => hu (s t).1)
    (fun t _ => hsig t) hbi
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

noncomputable def height {d : ℕ} {Ω : Type*} (f : Point d → ℝ) (lower : ℝ)
    (g : Point d → Ω → Point d) (β ρ η τ vinit : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (T : ℕ) : ℝ :=
  AdamLogMoments.prefixMaximum (fun t => 1 + f (trajectory g β ρ η τ vinit x0 ξ t).1 - lower) T

noncomputable def noiseEnergy {d : ℕ} {Ω : Type*} (h : Point d → Point d)
    (g : Point d → Ω → Point d) (β ρ η τ vinit : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, ‖g (trajectory g β ρ η τ vinit x0 ξ t).1 (ξ t) -
    h (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2) / (T * vinit)

lemma energyEnvelope_mono {d : ℕ} {Ω : Type*} (g : Point d → Ω → Point d)
    (β η τ : ℝ) {ρ vinit : ℝ} (hρ : 0 ≤ ρ) (hvinit : 0 < vinit)
    (x0 : Point d) (ξ : ℕ → Ω) {n T : ℕ} (hn : n ≤ T) :
    energyEnvelope g β ρ η τ vinit x0 ξ n ≤ energyEnvelope g β ρ η τ vinit x0 ξ T := by
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hρ hvinit.le)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun _ _ _ => sq_nonneg _)

lemma height_feedback {d : ℕ} {Ω : Type*} {f : Point d → ℝ} {h : Point d → Point d}
    {lower K : ℝ} (hK : 0 ≤ K) (hlower : ∀ x, lower ≤ f x)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower))
    (g : Point d → Ω → Point d) (β η τ : ℝ) {vinit : ℝ} (hvinit : 1 ≤ vinit)
    (x0 : Point d) (ξ : ℕ → Ω) {T : ℕ} (hT : 0 < T) :
    energyEnvelope g β (1 / T) η τ vinit x0 ξ T ≤
      (1 + 2 * K ^ 2) * (height f lower g β (1 / T) η τ vinit x0 ξ T) ^ 2 *
        (1 + 2 * noiseEnergy h g β (1 / T) η τ vinit x0 ξ T) := by
  let s := trajectory g β (1 / T) η τ vinit x0 ξ
  let M := height f lower g β (1 / T) η τ vinit x0 ξ T
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hM : 1 ≤ M := by
    have hh := AdamLogMoments.le_prefixMaximum
      (fun t => 1 + f (s t).1 - lower) (Nat.zero_le T)
    have hl := hlower (s 0).1
    dsimp [M, height, s] at hh ⊢
    linarith
  have hgrowth (t : ℕ) (ht : t < T) : ‖h (s t).1‖ ≤ K * M :=
    (hgrad (s t).1).trans (mul_le_mul_of_nonneg_left
      (AdamLogMoments.le_prefixMaximum (fun t => 1 + f (s t).1 - lower) ht.le) hK)
  have henergy := AdamGeneralizedPath.gradient_energy_bound (g := fun t => g (s t).1 (ξ t))
    (h := fun t => h (s t).1) T hgrowth
  have hh := AdamLogMoments.accumulator_feedback ht hvinit
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hM henergy
  dsimp [energyEnvelope, noiseEnergy, M, s] at hh ⊢
  convert hh using 1; ring

set_option maxHeartbeats 800000 in
lemma logarithmic_height {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {f : Point d → ℝ} {h : Point d → Point d} {L0 L1 lower K β a σ : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K)
    (hf : ∀ x, HasGradientAt f (h x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 → ‖h y - h x‖ ≤ (L0 + L1 * ‖h x‖) * ‖y - x‖)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower)) (hcurv : L0 + L1 * K ≤ K ^ 2)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (ha : 0 ≤ a)
    (hg : Measurable (Function.uncurry g)) (hi : ∀ x, Integrable (g x) P)
    (hmean : ∀ x, (∫ ω, g x ω ∂P) = h x)
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - h x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - h x‖ ^ 2 ∂P) ≤ σ ^ 2)
    {T : ℕ} (hT : 2 ≤ T) (hbmem : (1 + β) / 2 ≤ 1 - 1 / (T : ℝ))
    (hcal : K * (β / (1 - β)) * a * Real.sqrt d + 12 * K * a +
      (d * (3 * K ^ 2 * (1 + (β / (1 - β)) ^ 2) * a ^ 2 + 3 * K * (β / (1 - β)) * a)) *
        (2 + Real.log (1 + 2 * K ^ 2)) ≤ 1)
    (x0 : Point d) (ξ : ℕ → Ω) :
    let η := a / Real.sqrt T
    let M := height f lower g β (1 / T) η 1 (1 + σ ^ 2) x0 ξ T
    let Z := noiseEnergy h g β (1 / T) η 1 (1 + σ ^ 2) x0 ξ T
    let S := AdamExponentialProcess.partialMax (stateTransition g β (1 / T) η 1)
      (innovation P g (fun x => (1 + f x - lower)⁻¹ • h x) ((1 + σ ^ 2) / 4) (1 / T) 1 η)
      (x0, 0, WithLp.toLp 2 (fun _ => 1 + σ ^ 2)) ξ T
    let c := d * (3 * K ^ 2 * (1 + (β / (1 - β)) ^ 2) * a ^ 2 + 3 * K * (β / (1 - β)) * a)
    Real.log M ≤ Real.log (1 + f x0 - lower) + 1 + 2 * c * Real.log M + c * Real.log (1 + 2 * Z) + S := by
  let η := a / Real.sqrt T
  let v := 1 + σ ^ 2
  let r := β / (1 - β)
  let s := trajectory g β (1 / T) η 1 v x0 ξ
  let M := height f lower g β (1 / T) η 1 v x0 ξ T
  let Z := noiseEnergy h g β (1 / T) η 1 v x0 ξ T
  let B := energyEnvelope g β (1 / T) η 1 v x0 ξ T
  let U := innovation P g (fun x => (1 + f x - lower)⁻¹ • h x) (v / 4) (1 / T) 1 η
  let initial : Point d × Point d × Point d := (x0, 0, WithLp.toLp 2 (fun _ : Fin d => v))
  let S := AdamExponentialProcess.partialMax (stateTransition g β (1 / T) η 1) U initial ξ T
  let c := d * (3 * K ^ 2 * (1 + r ^ 2) * a ^ 2 + 3 * K * r * a)
  change Real.log M ≤ Real.log (1 + f x0 - lower) + 1 + 2 * c * Real.log M + c * Real.log (1 + 2 * Z) + S
  have htpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2 htpos
  have hv : 0 < v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
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
  have hZ : 0 ≤ Z := by dsimp [Z, noiseEnergy]; positivity
  have hB : 1 ≤ B := by
    dsimp [B, energyEnvelope]
    exact le_add_of_nonneg_right (by positivity)
  obtain ⟨n, hn, heM⟩ := AdamLogMoments.prefixMaximum_attained
    (fun t => 1 + f (s t).1 - lower) T
  have hp := logarithmic_prefix P hL0 hL1 hK hf hlower hs hgrad hcurv hβ hβ1 hη
    (by norm_num : (0 : ℝ) ≤ 1) hv hg hi hmean h2 hvar hT hn hbmem x0 ξ
  have hnoise : AdamExponentialProcess.partialSum (stateTransition g β (1 / T) η 1) U initial ξ n ≤ S :=
    (AdamExponentialProcess.partialSum_le_partialMax _ _ _ _ n).trans
      (AdamExponentialProcess.partialMax_mono _ _ _ _ hn)
  have hcoeff : 3 * K ^ 2 * (1 + r ^ 2) * η ^ 2 * d / (1 / (T : ℝ)) +
      3 * K * r * (η / Real.sqrt (1 / (T : ℝ))) * d = c := by
    calc
      _ = d * (3 * K ^ 2 * (1 + r ^ 2) * (η ^ 2 / (1 / (T : ℝ))) +
        3 * K * r * (η / Real.sqrt (1 / (T : ℝ)))) := by ring
      _ = c := by rw [hη2, hηρ]
  have hend : K * (η * β / (1 - β)) * (Real.sqrt d / Real.sqrt (1 / (T : ℝ))) =
      K * r * a * Real.sqrt d := by
    calc
      _ = K * r * (η / Real.sqrt (1 / (T : ℝ))) * Real.sqrt d := by dsimp [r]; ring
      _ = _ := by rw [hηρ]
  have hbias : (n : ℝ) * η * K * (12 * Real.sqrt (1 / (T : ℝ)) / v * σ ^ 2) ≤ 12 * K * a := by
    have hnt : (n : ℝ) / T ≤ 1 := (div_le_one htpos).2 (by exact_mod_cast hn)
    have hnv : σ ^ 2 / v ≤ 1 := (div_le_one hv).2 (by dsimp [v]; linarith)
    have he : (n : ℝ) * η * K * (12 * Real.sqrt (1 / (T : ℝ)) / v * σ ^ 2) =
        (12 * K * a) * ((n : ℝ) / T) * (σ ^ 2 / v) := by
      calc
        _ = 12 * n * K * (η * Real.sqrt (1 / (T : ℝ))) * (σ ^ 2 / v) := by ring
        _ = _ := by rw [hηroot]; ring
    rw [he]
    have hp' := mul_le_mul_of_nonneg_left hnt (by positivity : 0 ≤ 12 * K * a)
    have hp'' := mul_le_mul hp' hnv (div_nonneg (sq_nonneg σ) hv.le) (by positivity : 0 ≤ 12 * K * a * 1)
    simpa using hp''
  have hBlog := Real.log_le_log (by
      dsimp [energyEnvelope]
      positivity : 0 < energyEnvelope g β (1 / T) η 1 v x0 ξ n)
    (energyEnvelope_mono g β η 1 (by positivity) hv x0 ξ hn)
  have hBlog' := mul_le_mul_of_nonneg_left hBlog hc
  have hpath : Real.log M ≤ Real.log (1 + f x0 - lower) +
      (K * r * a * Real.sqrt d + 12 * K * a) + c * (2 + Real.log B) + S := by
    change M = 1 + f (s n).1 - lower at heM
    change Real.log (1 + f (s n).1 - lower) ≤ _ at hp
    rw [← heM, hcoeff, hend] at hp
    nlinarith
  exact AdamLogMoments.logarithmic_feedback hM hZ hB hc
    (height_feedback hK hlower hgrad g β η 1 (by dsimp [v]; nlinarith [sq_nonneg σ]) x0 ξ (by omega)) hpath hcal

lemma height_sixteenth_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {f : Point d → ℝ} {h : Point d → Point d} {L0 L1 lower K β a σ : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK : 0 ≤ K)
    (hf : ∀ x, HasGradientAt f (h x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 → ‖h y - h x‖ ≤ (L0 + L1 * ‖h x‖) * ‖y - x‖)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower)) (hcurv : L0 + L1 * K ≤ K ^ 2)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (ha : 0 ≤ a)
    (hg : Measurable (Function.uncurry g)) (hi : ∀ x, Integrable (g x) P)
    (hmean : ∀ x, (∫ ω, g x ω ∂P) = h x)
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - h x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - h x‖ ^ 2 ∂P) ≤ σ ^ 2)
    {T : ℕ} (hT : 2 ≤ T) (hbmem : (1 + β) / 2 ≤ 1 - 1 / (T : ℝ))
    (hscale : a * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ))
    (hrscale : ((β / (1 - β)) * a) * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ))
    (x0 : Point d) (ω0 : Ω) :
    Integrable (fun ξ => (height f lower g β (1 / T) (a / Real.sqrt T) 1 (1 + σ ^ 2) x0 ξ T) ^ 16)
      (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, (height f lower g β (1 / T) (a / Real.sqrt T) 1 (1 + σ ^ 2) x0 ξ T) ^ 16
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 16 ^ 16 * (1 + f x0 - lower) ^ 32 := by
  let η := a / Real.sqrt T
  let v := 1 + σ ^ 2
  let r := β / (1 - β)
  let M := fun ξ => height f lower g β (1 / T) η 1 v x0 ξ T
  let Z := fun ξ => noiseEnergy h g β (1 / T) η 1 v x0 ξ T
  let u := fun x => (1 + f x - lower)⁻¹ • h x
  let U := innovation P g u (v / 4) (1 / T) 1 η
  let initial : Point d × Point d × Point d := (x0, 0, WithLp.toLp 2 (fun _ => v))
  let S := fun ξ => AdamExponentialProcess.partialMax (stateTransition g β (1 / T) η 1) U initial ξ T
  let c := d * (3 * K ^ 2 * (1 + r ^ 2) * a ^ 2 + 3 * K * r * a)
  have ht : 0 < T := by omega
  have htpos : (0 : ℝ) < T := by exact_mod_cast ht
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hcal := AdamGeneralizedParameters.log_calibration ha hr hK hscale hrscale
  have hfcont : Continuous f := continuous_iff_continuousAt.2 (fun x => (hf x).differentiableAt.continuousAt)
  have hhcont : Continuous h := AdamLogGeometry.gradient_continuous hL1 hs
  have hum : Measurable u := by dsimp [u]; fun_prop
  have huk (x) : ‖u x‖ ≤ K := by
    have hp : 0 < 1 + f x - lower := by linarith [hlower x]
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)]
    calc
      _ ≤ (1 + f x - lower)⁻¹ * (K * (1 + f x - lower)) :=
        mul_le_mul_of_nonneg_left (hgrad x) (inv_nonneg.2 hp.le)
      _ = K := by field_simp
  have hmtraj (t) := measurable_trajectory hg β (1 / T) η 1 v x0 t
  have hMm : Measurable M := AdamLogMoments.measurable_prefixMaximum
    (fun t => ((hfcont.measurable.comp (hmtraj t).fst).const_add 1).sub_const lower) T
  have hZm : Measurable Z := by
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro t _
    exact (((hg.comp ((hmtraj t).fst.prodMk (measurable_pi_apply t))).sub
      (hhcont.measurable.comp (hmtraj t).fst)).norm.pow_const 2)
  have hUm := measurable_innovation P hg hum (v / 4) (1 / T) 1 η
  have hn := measurable_stateTransition hg β (1 / T) η 1
  have hSm : Measurable S := AdamExponentialProcess.measurable_partialMax hn hUm initial T
  have hM (ξ) : 1 ≤ M ξ := by
    have hh := AdamLogMoments.le_prefixMaximum
      (fun t => 1 + f (trajectory g β (1 / T) η 1 v x0 ξ t).1 - lower) (Nat.zero_le T)
    have hl := hlower x0
    have hstart : 1 ≤ 1 + f (trajectory g β (1 / T) η 1 v x0 ξ 0).1 - lower := by
      simpa only [LongTails.Algorithms.GeneralizedSmoothAdam.trajectory] using (show 1 ≤ 1 + f x0 - lower by linarith)
    exact hstart.trans hh
  have hZ (ξ) : 0 ≤ Z ξ := by dsimp [Z, noiseEnergy]; positivity
  have hZi := trajectory_noise_average P hg hhcont.measurable h2 hvar β (1 / T) η 1 v x0 ω0 ht
  have hsmall : 128 * (2 * η * K * (Real.sqrt d / Real.sqrt (1 / (T : ℝ)))) ≤ 1 := by
    have he : η / Real.sqrt (1 / (T : ℝ)) = a := by
      dsimp [η]
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
      field_simp
    have he' : 128 * (2 * η * K * (Real.sqrt d / Real.sqrt (1 / (T : ℝ)))) =
        128 * (2 * a * K * Real.sqrt d) := by
      calc
        _ = 128 * (2 * (η / Real.sqrt (1 / (T : ℝ))) * K * Real.sqrt d) := by ring
        _ = _ := by rw [he]
    rw [he']
    exact hcal.2.2.2.1
  have hSexp := innovation_maximum P hg hum h hi h2 (by positivity : 0 < v / 4)
    (by positivity : 0 < 1 / (T : ℝ)) (by norm_num : (0 : ℝ) ≤ 1) hη (by norm_num : (0 : ℝ) ≤ 128)
    huk hvar hsmall hn initial ω0 T
  have hSexpi : Integrable (fun ξ => Real.exp (64 * S ξ)) (Measure.infinitePi (fun _ : ℕ => P)) := by
    simpa only [S, U, show (128 : ℝ) / 2 = 64 by norm_num] using hSexp.1
  have hSexpe : (∫ ξ, Real.exp (64 * S ξ) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 3 := by
    have hh := AdamGeneralizedParameters.variance_scale ht a K σ
    have hvsmall := hh.trans hcal.2.2.2.2
    have he := AdamGeneralizedParameters.exponential_small (by positivity) hvsmall
    have hb := hSexp.2.trans he
    simpa only [S, U, show (128 : ℝ) / 2 = 64 by norm_num] using hb
  have hmom := AdamLogMoments.sixteenth_moment (Measure.infinitePi (fun _ : ℕ => P))
    hMm hZm hSm hM (by linarith [hlower x0]) hZ hcal.2.1 hZi.1 hZi.2 hSexpi hSexpe
    (fun ξ => logarithmic_height P hL0 hL1 hK hf hlower hs hgrad hcurv hβ hβ1 ha hg hi hmean h2 hvar
      hT hbmem hcal.2.2.1 x0 ξ)
  refine ⟨hmom.1, hmom.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right AdamLogMoments.exponential_constant (by positivity)

lemma original_noise_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {f : Point d → ℝ} {h : Point d → Point d} {lower K β a σ C : ℝ} (hK : 0 ≤ K)
    (hg : Measurable (Function.uncurry g)) (hh : Measurable h)
    (hi : ∀ x, Integrable (g x) P) (h2 : ∀ x, Integrable (fun ω => ‖g x ω - h x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - h x‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower))
    {T : ℕ} (hT : 0 < T) (x0 : Point d) (ω0 : Ω)
    (hiM : Integrable (fun ξ => (height f lower g β (1 / T) (a / Real.sqrt T) 1 (1 + σ ^ 2) x0 ξ T) ^ 2)
      (Measure.infinitePi (fun _ : ℕ => P)))
    (hEM : (∫ ξ, (height f lower g β (1 / T) (a / Real.sqrt T) 1 (1 + σ ^ 2) x0 ξ T) ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ C ^ 2) :
    let N := fun ξ => AdamExponentialProcess.partialSum (stateTransition g β (1 / T) (a / Real.sqrt T) 1)
      (innovation P g h ((1 + σ ^ 2) / 4) (1 / T) 1 (a / Real.sqrt T))
      (x0, 0, WithLp.toLp 2 (fun _ => 1 + σ ^ 2)) ξ T
    Integrable (fun ξ => N ξ ^ 2) (Measure.infinitePi (fun _ : ℕ => P)) ∧
      (∫ ξ, N ξ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 4 * a ^ 2 * K ^ 2 * C ^ 2 := by
  let η := a / Real.sqrt T
  let v := 1 + σ ^ 2
  let M := fun ξ => height f lower g β (1 / T) η 1 v x0 ξ T
  let initial : Point d × Point d × Point d := (x0, 0, WithLp.toLp 2 (fun _ => v))
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hv : 0 < v := by dsimp [v]; positivity
  have hm := measurable_stateTransition hg β (1 / T) η 1
  have hbound (ξ : ℕ → Ω) (t : ℕ) (htt : t < T) :
      ‖h (AdamHeavyTailedProcess.stateAt (stateTransition g β (1 / T) η 1) initial ξ t).1‖ ≤ K * M ξ := by
    rw [AdamGeneralizedTrajectory.stateAt_initial]
    exact (hgrad _).trans (mul_le_mul_of_nonneg_left
      (AdamLogMoments.le_prefixMaximum (fun t => 1 + f (trajectory g β (1 / T) η 1 v x0 ξ t).1 - lower) htt.le) hK)
  have hn := innovation_sum_square P hg hh h hi h2 (by positivity : 0 < v / 4)
    (by positivity : 0 < 1 / (T : ℝ)) (by norm_num : (0 : ℝ) ≤ 1) hvar hm initial ω0 T M hiM hEM hbound
    (α := η)
  refine ⟨hn.1, hn.2.trans ?_⟩
  have he : (T : ℝ) * (η ^ 2 * K ^ 2 * σ ^ 2 / (v / 4)) * C ^ 2 =
      (4 * a ^ 2 * K ^ 2 * C ^ 2) * (σ ^ 2 / v) := by
    dsimp [η]
    rw [div_pow, Real.sq_sqrt ht.le]
    field_simp
  rw [he]
  have hb : σ ^ 2 / v ≤ 1 := (div_le_one hv).2 (by dsimp [v]; linarith)
  simpa using mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4 * a ^ 2 * K ^ 2 * C ^ 2)

lemma energyEnvelope_additive {d : ℕ} {Ω : Type*} {f : Point d → ℝ} {h : Point d → Point d}
    {lower K : ℝ} (hK : 0 ≤ K)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower))
    (g : Point d → Ω → Point d) (β η τ : ℝ) {vinit : ℝ} (hvinit : 0 < vinit)
    (x0 : Point d) (ξ : ℕ → Ω) {T : ℕ} (hT : 0 < T) :
    vinit * energyEnvelope g β (1 / T) η τ vinit x0 ξ T ≤
      vinit + 2 * K ^ 2 * (height f lower g β (1 / T) η τ vinit x0 ξ T) ^ 2 +
        2 * vinit * noiseEnergy h g β (1 / T) η τ vinit x0 ξ T := by
  let s := trajectory g β (1 / T) η τ vinit x0 ξ
  let M := height f lower g β (1 / T) η τ vinit x0 ξ T
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hgrowth (t : ℕ) (htt : t < T) : ‖h (s t).1‖ ≤ K * M :=
    (hgrad (s t).1).trans (mul_le_mul_of_nonneg_left
      (AdamLogMoments.le_prefixMaximum (fun t => 1 + f (s t).1 - lower) htt.le) hK)
  have hp := AdamGeneralizedPath.gradient_energy_bound (g := fun t => g (s t).1 (ξ t))
    (h := fun t => h (s t).1) T hgrowth
  have hh := div_le_div_of_nonneg_right hp ht.le
  have he1 : vinit * energyEnvelope g β (1 / T) η τ vinit x0 ξ T =
      vinit + (∑ t ∈ Finset.range T, ‖g (s t).1 (ξ t)‖ ^ 2) / T := by
    dsimp [energyEnvelope, s]
    field_simp
  have he2 : (2 * T * (K * M) ^ 2 + 2 * ∑ t ∈ Finset.range T, ‖g (s t).1 (ξ t) - h (s t).1‖ ^ 2) / T =
      2 * K ^ 2 * M ^ 2 + 2 * vinit * noiseEnergy h g β (1 / T) η τ vinit x0 ξ T := by
    dsimp [noiseEnergy, s]
    field_simp
  rw [he1]
  rw [he2] at hh
  dsimp only [M] at hh
  linarith

end LongTails.Proofs.AdamGeneralizedAnalysis
