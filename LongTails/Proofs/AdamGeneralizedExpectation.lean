import LongTails.Proofs.AdamGeneralizedDescent

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamGeneralizedExpectation

open OracleTemplate.Adam LongTails.Algorithms.GeneralizedSmoothAdam
open AdamGeneralizedAnalysis AdamGeneralizedNoise AdamNormalizedMoments

noncomputable def signalTotal {d : ℕ} {Ω : Type*} (h : Point d → Point d)
    (g : Point d → Ω → Point d) (β ρ η τ vinit : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (T : ℕ) : ℝ :=
  η * ∑ t ∈ Finset.range T, ⟪h (trajectory g β ρ η τ vinit x0 ξ t).1,
    normalized (fun i => (1 - ρ) * (trajectory g β ρ η τ vinit x0 ξ t).2.2 i)
      ρ τ (h (trajectory g β ρ η τ vinit x0 ξ t).1)⟫

lemma measurable_signalTotal {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {h : Point d → Point d} {g : Point d → Ω → Point d}
    (hh : Measurable h) (hg : Measurable (Function.uncurry g))
    (β ρ η τ vinit : ℝ) (x0 : Point d) (T : ℕ) :
    Measurable (fun ξ => signalTotal h g β ρ η τ vinit x0 ξ T) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro t _
  have hs := AdamGeneralizedTrajectory.measurable_trajectory hg β ρ η τ vinit x0 t
  have hht := hh.comp hs.fst
  have hn : Measurable (fun ξ => normalized
      (fun i => (1 - ρ) * (trajectory g β ρ η τ vinit x0 ξ t).2.2 i) ρ τ
      (h (trajectory g β ρ η τ vinit x0 ξ t).1)) := by
    apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
    apply Measurable.of_eval
    intro i
    have hhi := (measurable_coordinate i).comp hht
    have hvi := (measurable_coordinate i).comp hs.snd.snd
    exact hhi.div (((Real.continuous_sqrt.measurable.comp
      ((hvi.const_mul (1 - ρ)).add ((hhi.pow_const 2).const_mul ρ))).add_const τ))
  exact continuous_inner.measurable.comp (hht.prodMk hn)

lemma measurable_energyEnvelope {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Point d → Ω → Point d} (hg : Measurable (Function.uncurry g))
    (β ρ η τ vinit : ℝ) (x0 : Point d) (T : ℕ) :
    Measurable (fun ξ => energyEnvelope g β ρ η τ vinit x0 ξ T) := by
  apply Measurable.const_add
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro t _
  have hs := AdamGeneralizedTrajectory.measurable_trajectory hg β ρ η τ vinit x0 t
  exact (hg.comp (hs.fst.prodMk (measurable_pi_apply t))).norm.pow_const 2

set_option maxHeartbeats 800000 in
lemma signal_square_integral {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {f : Point d → ℝ} {h : Point d → Point d} {L0 L1 lower K β a σ : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK4 : 4 ≤ K) (hLK : L1 ≤ K)
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
    (x0 : Point d) (ω0 : Ω) :
    let D := fun ξ => signalTotal h g β (1 / T) (a / Real.sqrt T) 1 (1 + σ ^ 2) x0 ξ T
    Integrable (fun ξ => D ξ ^ 2) (Measure.infinitePi (fun _ : ℕ => P)) ∧
      (∫ ξ, D ξ ^ 2 ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
        (2048 * K ^ 2 * (1 + f x0 - lower) ^ 4) ^ 2 := by
  let η := a / Real.sqrt T
  let v := 1 + σ ^ 2
  let Φ := 1 + f x0 - lower
  let C := 16 * Φ ^ 2
  let M := fun ξ => height f lower g β (1 / T) η 1 v x0 ξ T
  let Z := fun ξ => noiseEnergy h g β (1 / T) η 1 v x0 ξ T
  let B := fun ξ => energyEnvelope g β (1 / T) η 1 v x0 ξ T
  let R := fun ξ => 2 + Real.log (B ξ)
  let L := fun ξ => Real.log (1 + 2 * Z ξ)
  let N := fun ξ => AdamExponentialProcess.partialSum (stateTransition g β (1 / T) η 1)
    (innovation P g h (v / 4) (1 / T) 1 η) (x0, 0, WithLp.toLp 2 (fun _ => v)) ξ T
  let D := fun ξ => signalTotal h g β (1 / T) η 1 v x0 ξ T
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  have hK : 0 ≤ K := by linarith
  have ht : 0 < T := by omega
  have hΦ : 1 ≤ Φ := by dsimp [Φ]; linarith [hlower x0]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hh : Continuous h := AdamLogGeometry.gradient_continuous hL1 hs
  have hfc : Continuous f := continuous_iff_continuousAt.2 (fun x => (hf x).differentiableAt.continuousAt)
  have hmtraj (t) := AdamGeneralizedTrajectory.measurable_trajectory hg β (1 / T) η 1 v x0 t
  have hMm : Measurable M := AdamLogMoments.measurable_prefixMaximum
    (fun t => ((hfc.measurable.comp (hmtraj t).fst).const_add 1).sub_const lower) T
  have hZm : Measurable Z := by
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro t _
    exact (((hg.comp ((hmtraj t).fst.prodMk (measurable_pi_apply t))).sub
      (hh.measurable.comp (hmtraj t).fst)).norm.pow_const 2)
  have hBm : Measurable B := measurable_energyEnvelope hg β (1 / T) η 1 v x0 T
  have hRm : Measurable R := hBm.log.const_add 2
  have hLm : Measurable L := (hZm.const_mul 2 |>.const_add 1).log
  have hDm : Measurable D := measurable_signalTotal hh.measurable hg β (1 / T) η 1 v x0 T
  have hM (ξ) : 1 ≤ M ξ := by
    have hp := AdamLogMoments.le_prefixMaximum
      (fun t => 1 + f (trajectory g β (1 / T) η 1 v x0 ξ t).1 - lower) (Nat.zero_le T)
    exact (show 1 ≤ 1 + f (trajectory g β (1 / T) η 1 v x0 ξ 0).1 - lower by
      simpa only [LongTails.Algorithms.GeneralizedSmoothAdam.trajectory] using hΦ).trans hp
  have hZ (ξ) : 0 ≤ Z ξ := by dsimp [Z, noiseEnergy]; positivity
  have hB (ξ) : 1 ≤ B ξ := by
    dsimp [B, energyEnvelope]
    exact le_add_of_nonneg_right (by positivity)
  have hR (ξ) : 0 ≤ R ξ := by dsimp [R]; linarith [Real.log_nonneg (hB ξ)]
  have hcurv' : L0 + L1 * K ≤ K ^ 2 := by nlinarith only [hcurv, mul_nonneg hL1 hK]
  have hm16 := height_sixteenth_moment P hL0 hL1 hK hf hlower hs hgrad hcurv' hβ hβ1 ha
    hg hi hmean h2 hvar hT hbmem hscale hrscale x0 ω0
  have h16 : (∫ ξ, M ξ ^ 16 ∂Q) ≤ C ^ 16 := by
    dsimp only [C]
    rw [mul_pow, ← pow_mul]
    exact hm16.2
  have hmom := AdamLogMoments.lower_height_moments Q hMm hC hm16.1 h16
  have hz := AdamGeneralizedTrajectory.trajectory_noise_average P hg hh.measurable h2 hvar β (1 / T) η 1 v x0 ω0 ht
  have hl := AdamLogMoments.log_noise_fourth Q hZm hZ hz.1 hz.2
  have hrb (ξ) : R ξ ≤ 8 * K * M ξ + L ξ :=
    AdamLogMoments.envelope_log_bound (hB ξ) (by linarith) (hM ξ) (hZ ξ)
      (AdamGeneralizedParameters.log_curvature_scale hK)
      (height_feedback hK hlower hgrad g β η 1 (by dsimp only [v]; exact le_add_of_nonneg_right (sq_nonneg σ)) x0 ξ ht)
  have hmr := AdamLogMoments.weighted_log_square Q hMm hRm hLm hR hmom.1.1 hl.1 hmom.1.2 hl.2 hrb
  have hn := original_noise_moment P hK hg hh.measurable hi h2 hvar hgrad ht x0 ω0 hmom.2.1 hmom.2.2
  have hd (ξ) := AdamGeneralizedDescent.original_calibrated P hL0 hL1 hK hLK hf hlower hs hgrad hcurv hβ hβ1 ha
    hg hi hmean h2 hvar hT hbmem hscale hrscale x0 ξ
  have hfinal := AdamLogMoments.signal_second_moment Q hDm (fun ξ => (hd ξ).1)
    hmr.1 hmom.2.1 hn.1 hmr.2 hmom.2.2 hn.2 (fun ξ => (hd ξ).2)
  refine ⟨hfinal.1, hfinal.2.trans ?_⟩
  have haK := (AdamGeneralizedParameters.scale_controls ha hK (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 20) hscale).1
  have hc := AdamGeneralizedParameters.signal_moment_constant hK4 hΦ ha (by linarith : a * K ≤ 1)
  have hgap : f x0 - lower = Φ - 1 := by dsimp [Φ]; ring
  rw [hgap]
  exact hc

noncomputable def denominatorEnvelope {d : ℕ} {Ω : Type*} (f : Point d → ℝ) (lower K : ℝ)
    (g : Point d → Ω → Point d) (β η vinit : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (T : ℕ) : ℝ :=
  1 + Real.sqrt (vinit * energyEnvelope g β (1 / T) η 1 vinit x0 ξ T +
    K ^ 2 * (height f lower g β (1 / T) η 1 vinit x0 ξ T) ^ 2 / T)

lemma denominator_gradient_bound {d : ℕ} {Ω : Type*} {f : Point d → ℝ} {h : Point d → Point d}
    {lower K β η vinit : ℝ} (hK : 0 ≤ K) (hη : 0 ≤ η) (hvinit : 0 < vinit)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower)) (g : Point d → Ω → Point d)
    {T : ℕ} (hT : 2 ≤ T) (x0 : Point d) (ξ : ℕ → Ω) :
    η * (∑ t ∈ Finset.range T, ‖h (trajectory g β (1 / T) η 1 vinit x0 ξ t).1‖ ^ 2) ≤
      denominatorEnvelope f lower K g β η vinit x0 ξ T * signalTotal h g β (1 / T) η 1 vinit x0 ξ T := by
  let ρ : ℝ := 1 / T
  let s := trajectory g β ρ η 1 vinit x0 ξ
  let M := height f lower g β ρ η 1 vinit x0 ξ T
  let B := energyEnvelope g β ρ η 1 vinit x0 ξ T
  have ht : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have ht0 : (0 : ℝ) < T := by linarith
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; exact (div_lt_one ht0).2 (by linarith)
  have hv (t i) : 0 < (s t).2.2 i :=
    AdamGeneralizedTrajectory.secondMoment_pos g β η 1 hvinit hρ hρ1 x0 ξ t i
  have hvB (t : ℕ) (htt : t < T) (i) : (s t).2.2 i ≤ vinit * B := by
    have hp := AdamGeneralizedPath.coordinate_accumulator_upper (v := fun t => (s t).2.2)
      (g := fun t => g (s t).1 (ξ t)) hρ hρ1 hvinit (fun _ => rfl) (fun _ _ => rfl) t i
    have hb := energyEnvelope_mono g β η 1 hρ hvinit x0 ξ htt.le
    exact hp.trans (mul_le_mul_of_nonneg_left hb hvinit.le)
  have hgrowth (t : ℕ) (htt : t < T) : ‖h (s t).1‖ ≤ K * M :=
    (hgrad (s t).1).trans (mul_le_mul_of_nonneg_left
      (AdamLogMoments.le_prefixMaximum (fun t => 1 + f (s t).1 - lower) htt.le) hK)
  have hden (t : ℕ) (htt : t < T) (i) : Real.sqrt ((1 - ρ) * (s t).2.2 i + ρ * (h (s t).1 i) ^ 2) + 1 ≤
      denominatorEnvelope f lower K g β η vinit x0 ξ T := by
    have hp := AdamGeneralizedPath.signal_denominator_bound hρ (fun i => (hv t i).le) (hvB t htt)
      (h (s t).1) (hgrowth t htt) i
    have he : ρ * (K * M) ^ 2 = K ^ 2 * M ^ 2 / T := by dsimp [ρ]; ring
    change _ ≤ 1 + Real.sqrt (vinit * B + K ^ 2 * M ^ 2 / T)
    rw [← he]
    exact hp
  have hs := AdamGeneralizedPath.signal_gradient_sum (fun t => h (s t).1) (fun t => (s t).2.2) ρ T hden
  have hp := mul_le_mul_of_nonneg_left hs hη
  convert hp using 1; dsimp [signalTotal, s, ρ]; ring

lemma denominator_square_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {f : Point d → ℝ} {h : Point d → Point d} {lower K β η σ Φ : ℝ}
    (hK : 1 ≤ K) (hΦ : 1 ≤ Φ) (hf : Measurable f) (hh : Measurable h)
    (hg : Measurable (Function.uncurry g))
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - h x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - h x‖ ^ 2 ∂P) ≤ σ ^ 2)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower))
    {T : ℕ} (hT : 0 < T) (x0 : Point d) (ω0 : Ω)
    (hiM : Integrable (fun ξ => (height f lower g β (1 / T) η 1 (1 + σ ^ 2) x0 ξ T) ^ 2)
      (Measure.infinitePi (fun _ : ℕ => P)))
    (hEM : (∫ ξ, (height f lower g β (1 / T) η 1 (1 + σ ^ 2) x0 ξ T) ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 256 * Φ ^ 4) :
    Integrable (fun ξ => (denominatorEnvelope f lower K g β η (1 + σ ^ 2) x0 ξ T) ^ 2)
      (Measure.infinitePi (fun _ : ℕ => P)) ∧
    (∫ ξ, (denominatorEnvelope f lower K g β η (1 + σ ^ 2) x0 ξ T) ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ (64 * K * Real.sqrt (1 + σ ^ 2) * Φ ^ 2) ^ 2 := by
  let v := 1 + σ ^ 2
  let M := fun ξ => height f lower g β (1 / T) η 1 v x0 ξ T
  let Z := fun ξ => noiseEnergy h g β (1 / T) η 1 v x0 ξ T
  let B := fun ξ => energyEnvelope g β (1 / T) η 1 v x0 ξ T
  let X := fun ξ => v * B ξ + K ^ 2 * M ξ ^ 2 / T
  have hv : 1 ≤ v := by dsimp only [v]; exact le_add_of_nonneg_right (sq_nonneg σ)
  have hK0 : 0 ≤ K := by linarith
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast (Nat.succ_le_iff.2 hT)
  have hmtraj (t) := AdamGeneralizedTrajectory.measurable_trajectory hg β (1 / T) η 1 v x0 t
  have hMm : Measurable M := AdamLogMoments.measurable_prefixMaximum
    (fun t => ((hf.comp (hmtraj t).fst).const_add 1).sub_const lower) T
  have hBm : Measurable B := measurable_energyEnvelope hg β (1 / T) η 1 v x0 T
  have hXm : Measurable X := (hBm.const_mul v).add (((hMm.pow_const 2).const_mul (K ^ 2)).div_const T)
  have hX (ξ) : 0 ≤ X ξ := by dsimp [X, B, energyEnvelope]; positivity
  have hbound (ξ) : X ξ ≤ v + 3 * K ^ 2 * M ξ ^ 2 + 2 * v * Z ξ := by
    have he := energyEnvelope_additive hK0 hgrad g β η 1 (by linarith : 0 < v) x0 ξ hT
    have hd : K ^ 2 * M ξ ^ 2 / T ≤ K ^ 2 * M ξ ^ 2 := div_le_self (by positivity) ht
    dsimp only [X]
    dsimp only [M, Z, B] at hd ⊢
    linarith
  have hz := AdamGeneralizedTrajectory.trajectory_noise_average P hg hh h2 hvar β (1 / T) η 1 v x0 ω0 hT
  exact AdamLogMoments.denominator_square_integral (Measure.infinitePi (fun _ : ℕ => P))
    hK hv hΦ hXm hX hiM hz.1 hEM hz.2 hbound

noncomputable def gradientAverage {d : ℕ} {Ω : Type*} (h : Point d → Point d)
    (g : Point d → Ω → Point d) (β ρ η τ vinit : ℝ) (x0 : Point d) (ξ : ℕ → Ω) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, ‖h (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2) / T

lemma gradient_average_from_moments {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure (ℕ → Ω)) {g : Point d → Ω → Point d}
    {f : Point d → ℝ} {h : Point d → Point d} {lower K β η vinit U V : ℝ}
    (hK : 0 ≤ K) (hη : 0 < η) (hvinit : 0 < vinit)
    (hf : Measurable f) (hh : Measurable h) (hg : Measurable (Function.uncurry g))
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower))
    {T : ℕ} (hT : 2 ≤ T) (x0 : Point d) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hiH : Integrable (fun ξ => (denominatorEnvelope f lower K g β η vinit x0 ξ T) ^ 2) P)
    (hiD : Integrable (fun ξ => (signalTotal h g β (1 / T) η 1 vinit x0 ξ T) ^ 2) P)
    (hEH : (∫ ξ, (denominatorEnvelope f lower K g β η vinit x0 ξ T) ^ 2 ∂P) ≤ U ^ 2)
    (hED : (∫ ξ, (signalTotal h g β (1 / T) η 1 vinit x0 ξ T) ^ 2 ∂P) ≤ V ^ 2) :
    Integrable (fun ξ => gradientAverage h g β (1 / T) η 1 vinit x0 ξ T) P ∧
      (∫ ξ, gradientAverage h g β (1 / T) η 1 vinit x0 ξ T ∂P) ≤ U * V / (η * T) := by
  let H := fun ξ => denominatorEnvelope f lower K g β η vinit x0 ξ T
  let D := fun ξ => signalTotal h g β (1 / T) η 1 vinit x0 ξ T
  let A := fun ξ => gradientAverage h g β (1 / T) η 1 vinit x0 ξ T
  have ht : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hmtraj (t) := AdamGeneralizedTrajectory.measurable_trajectory hg β (1 / T) η 1 vinit x0 t
  have hM := AdamLogMoments.measurable_prefixMaximum
    (fun t => ((hf.comp (hmtraj t).fst).const_add 1).sub_const lower) T
  have hB := measurable_energyEnvelope hg β (1 / T) η 1 vinit x0 T
  have hHm : Measurable H := by
    exact ((Real.continuous_sqrt.measurable.comp ((hB.const_mul vinit).add
      (((hM.pow_const 2).const_mul (K ^ 2)).div_const T))).const_add 1)
  have hDm : Measurable D := measurable_signalTotal hh hg β (1 / T) η 1 vinit x0 T
  have hAm : Measurable A := by
    apply Measurable.div_const
    exact Finset.measurable_sum _ (fun t _ => (hh.comp (hmtraj t).fst).norm.pow_const 2)
  have hH0 (ξ) : 0 ≤ H ξ := by dsimp [H, denominatorEnvelope]; positivity
  have hD0 (ξ) : 0 ≤ D ξ := by
    apply mul_nonneg hη.le
    exact Finset.sum_nonneg (fun t _ => inner_normalized_nonneg (by norm_num) _)
  have hA0 (ξ) : 0 ≤ A ξ := by dsimp [A, gradientAverage]; positivity
  have hb (ξ) : |A ξ| ≤ (1 / (η * T)) * (H ξ * D ξ) := by
    rw [abs_of_nonneg (hA0 ξ)]
    have hp := denominator_gradient_bound (β := β) hK hη.le hvinit hgrad g hT x0 ξ
    have he : η * T * A ξ = η * (∑ t ∈ Finset.range T,
        ‖h (trajectory g β (1 / T) η 1 vinit x0 ξ t).1‖ ^ 2) := by
      dsimp [A, gradientAverage]
      field_simp
    have hd : 0 < η * T := mul_pos hη ht
    have hp' : A ξ ≤ (H ξ * D ξ) / (η * T) := (le_div_iff₀ hd).2 (by rw [mul_comm, he]; exact hp)
    simpa only [one_div_mul_eq_div] using hp'
  have hp := AdamHeavyTailedHistory.integral_abs_product_bound P (by positivity : 0 ≤ 1 / (η * T))
    hAm hHm hDm hH0 hD0 hiH hiD hb
  refine ⟨hp.1, ?_⟩
  have hu : Real.sqrt (∫ ξ, H ξ ^ 2 ∂P) ≤ U := by
    simpa only [Real.sqrt_sq hU] using Real.sqrt_le_sqrt hEH
  have hv : Real.sqrt (∫ ξ, D ξ ^ 2 ∂P) ≤ V := by
    simpa only [Real.sqrt_sq hV] using Real.sqrt_le_sqrt hED
  have hprod := mul_le_mul hu hv (Real.sqrt_nonneg _) hU
  have he := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 1 / (η * T))
  have habs : (fun ξ => |A ξ|) = A := funext (fun ξ => abs_of_nonneg (hA0 ξ))
  rw [habs] at hp
  exact hp.2.trans (by simpa only [one_div_mul_eq_div] using he)

set_option maxHeartbeats 800000 in
lemma trajectory_gradient_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : Point d → Ω → Point d}
    {f : Point d → ℝ} {h : Point d → Point d} {L0 L1 lower K β a σ : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hK4 : 4 ≤ K) (hLK : L1 ≤ K)
    (hf : ∀ x, HasGradientAt f (h x) x) (hlower : ∀ x, lower ≤ f x)
    (hs : ∀ x y, L1 * ‖y - x‖ ≤ 1 → ‖h y - h x‖ ≤ (L0 + L1 * ‖h x‖) * ‖y - x‖)
    (hgrad : ∀ x, ‖h x‖ ≤ K * (1 + f x - lower)) (hcurv : L0 + 2 * L1 * K ≤ K ^ 2)
    (hβ : 0 ≤ β) (hβ1 : β < 1) (ha : 0 < a)
    (hg : Measurable (Function.uncurry g)) (hi : ∀ x, Integrable (g x) P)
    (hmean : ∀ x, (∫ ω, g x ω ∂P) = h x)
    (h2 : ∀ x, Integrable (fun ω => ‖g x ω - h x‖ ^ 2) P)
    (hvar : ∀ x, (∫ ω, ‖g x ω - h x‖ ^ 2 ∂P) ≤ σ ^ 2)
    {T : ℕ} (hT : 2 ≤ T) (hbmem : (1 + β) / 2 ≤ 1 - 1 / (T : ℝ))
    (hscale : a * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ))
    (hrscale : (β / (1 - β) * a) * (d + 1) * (1 + K) ^ 2 ≤ (1 / 2 ^ 20 : ℝ))
    (x0 : Point d) (ω0 : Ω) :
    Integrable (fun ξ => gradientAverage h g β (1 / T) (a / Real.sqrt T) 1 (1 + σ ^ 2) x0 ξ T)
      (Measure.infinitePi (fun _ : ℕ => P)) ∧
      (∫ ξ, gradientAverage h g β (1 / T) (a / Real.sqrt T) 1 (1 + σ ^ 2) x0 ξ T
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
          2 ^ 17 * K ^ 3 * Real.sqrt (1 + σ ^ 2) * (1 + f x0 - lower) ^ 6 / (a * Real.sqrt T) := by
  let η := a / Real.sqrt T
  let v := 1 + σ ^ 2
  let Φ := 1 + f x0 - lower
  let M := fun ξ => height f lower g β (1 / T) η 1 v x0 ξ T
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  have hK : 0 ≤ K := by linarith
  have ht : 0 < T := by omega
  have htr : (0 : ℝ) < T := by exact_mod_cast ht
  have hη : 0 < η := by dsimp [η]; positivity
  have hΦ : 1 ≤ Φ := by dsimp [Φ]; linarith [hlower x0]
  have hh : Continuous h := AdamLogGeometry.gradient_continuous hL1 hs
  have hfc : Continuous f := continuous_iff_continuousAt.2 (fun x => (hf x).differentiableAt.continuousAt)
  have hmtraj (t) := AdamGeneralizedTrajectory.measurable_trajectory hg β (1 / T) η 1 v x0 t
  have hMm : Measurable M := AdamLogMoments.measurable_prefixMaximum
    (fun t => ((hfc.measurable.comp (hmtraj t).fst).const_add 1).sub_const lower) T
  have hcurv' : L0 + L1 * K ≤ K ^ 2 := by nlinarith only [hcurv, mul_nonneg hL1 hK]
  have hm16 := height_sixteenth_moment P hL0 hL1 hK hf hlower hs hgrad hcurv' hβ hβ1 ha.le
    hg hi hmean h2 hvar hT hbmem hscale hrscale x0 ω0
  have h16 : (∫ ξ, M ξ ^ 16 ∂Q) ≤ (16 * Φ ^ 2) ^ 16 := by
    rw [mul_pow, ← pow_mul]
    exact hm16.2
  have hmom := AdamLogMoments.lower_height_moments Q hMm (by positivity : 0 ≤ 16 * Φ ^ 2) hm16.1 h16
  have hm2 : (∫ ξ, M ξ ^ 2 ∂Q) ≤ 256 * Φ ^ 4 := by
    convert hmom.2.2 using 1; ring
  have hd := signal_square_integral P hL0 hL1 hK4 hLK hf hlower hs hgrad hcurv hβ hβ1 ha.le
    hg hi hmean h2 hvar hT hbmem hscale hrscale x0 ω0
  have hden := denominator_square_bound P (by linarith : 1 ≤ K) hΦ hfc.measurable hh.measurable hg h2 hvar hgrad
    ht x0 ω0 hmom.2.1 hm2
  have hp := gradient_average_from_moments Q (β := β) (vinit := v) hK hη (by dsimp [v]; positivity) hfc.measurable hh.measurable hg hgrad
    hT x0 (by positivity : 0 ≤ 64 * K * Real.sqrt v * Φ ^ 2)
    (by positivity : 0 ≤ 2048 * K ^ 2 * Φ ^ 4) hden.1 hd.1 hden.2 hd.2
  refine ⟨hp.1, hp.2.trans_eq ?_⟩
  have he : η * T = a * Real.sqrt T := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_eq_iff (Real.sqrt_pos.2 htr).ne']
    calc
      a * T = a * (Real.sqrt T) ^ 2 := by rw [Real.sq_sqrt htr.le]
      _ = _ := by ring
  rw [he]
  dsimp only [v, Φ]
  ring

lemma integrable_individual_square {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure (ℕ → Ω)) {g : Point d → Ω → Point d} {h : Point d → Point d}
    (hg : Measurable (Function.uncurry g)) (hh : Measurable h)
    (β ρ η τ vinit : ℝ) (x0 : Point d) {T : ℕ} (hT : 0 < T)
    (hi : Integrable (fun ξ => gradientAverage h g β ρ η τ vinit x0 ξ T) P)
    {t : ℕ} (ht : t < T) : Integrable (fun ξ => ‖h (trajectory g β ρ η τ vinit x0 ξ t).1‖ ^ 2) P := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hm := (hh.comp (AdamGeneralizedTrajectory.measurable_trajectory hg β ρ η τ vinit x0 t).fst).norm.pow_const 2
  apply (hi.const_mul (T : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have he : (T : ℝ) * gradientAverage h g β ρ η τ vinit x0 ξ T =
      ∑ k ∈ Finset.range T, ‖h (trajectory g β ρ η τ vinit x0 ξ k).1‖ ^ 2 := by
    dsimp [gradientAverage]
    field_simp
  rw [he]
  exact Finset.single_le_sum (f := fun k => ‖h (trajectory g β ρ η τ vinit x0 ξ k).1‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_range.2 ht)

end LongTails.Proofs.AdamGeneralizedExpectation
