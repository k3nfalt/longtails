import LongTails.Proofs.HeavyTailedFreshProcess
import LongTails.Proofs.HeavyTailedSpectralPath
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedSpectralProcess

abbrev UnitVector (d : ℕ) := {v : EuclideanSpace ℝ (Fin d) // ‖v‖ = 1}

noncomputable def transition {d : ℕ} {Ω : Type*}
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η : ℝ) (fallback : UnitVector d) (v : UnitVector d) (ω : Ω) : UnitVector d :=
  ⟨LongTails.Algorithms.HeavyTailedEnergyProbe.normalize fallback.val (v.val + η • B ω v.val),
    HeavyTailedProbeGeometry.normalize_norm fallback.property _⟩

noncomputable def logNoise {d : ℕ} {Ω : Type*}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η : ℝ) (v : UnitVector d) (ω : Ω) : ℝ :=
  η * ⟪v.val + η • A v.val, B ω v.val - A v.val⟫ / ‖v.val + η • A v.val‖ ^ 2

lemma transition_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) (η : ℝ) (fallback : UnitVector d) :
    Measurable (Function.uncurry (transition B η fallback)) := by
  have happ : Measurable (fun t : UnitVector d × Ω => B t.2 t.1.val) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
      (F := EuclideanSpace ℝ (Fin d))).continuous.measurable.comp
      ((hB.comp measurable_snd).prodMk (measurable_subtype_coe.comp measurable_fst))
  exact (HeavyTailedProbeGeometry.normalize_measurable.comp
    (measurable_const.prodMk ((measurable_subtype_coe.comp measurable_fst).add
      (happ.const_smul η)))).subtype_mk

lemma logNoise_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) (η : ℝ) : Measurable (Function.uncurry (logNoise A B η)) := by
  have happ : Measurable (fun t : UnitVector d × Ω => B t.2 t.1.val) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
      (F := EuclideanSpace ℝ (Fin d))).continuous.measurable.comp
      ((hB.comp measurable_snd).prodMk (measurable_subtype_coe.comp measurable_fst))
  have hval : Measurable (fun t : UnitVector d × Ω => t.1.val) :=
    measurable_subtype_coe.comp measurable_fst
  have hA : Measurable (fun t : UnitVector d × Ω => A t.1.val) := A.measurable.comp hval
  have hw := hval.add (hA.const_smul η)
  exact (measurable_const.mul (hw.inner (happ.sub hA))).div (hw.norm.pow_const 2)

lemma transition_trajectory {d : ℕ} {Ω : Type*}
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η : ℝ) (fallback v : UnitVector d) (n : ℕ) (ξ : ℕ → Ω) :
    (HeavyTailedProductProcess.trajectory (transition B η fallback) n v ξ).val =
      HeavyTailedProbeGeometry.normalizedPath
        (fun k => ContinuousLinearMap.id ℝ _ + η • B (ξ k)) fallback.val v.val n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [HeavyTailedProductProcess.trajectory_succ_last]
      simp only [transition, HeavyTailedProbeGeometry.normalizedPath, add_apply,
        ContinuousLinearMap.id_apply, smul_apply, ih]

lemma logNoise_sum_eq_path {d : ℕ} {Ω : Type*}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η : ℝ) (fallback v : UnitVector d) (n : ℕ) (ξ : ℕ → Ω) :
    let path := HeavyTailedProbeGeometry.normalizedPath
      (fun k => ContinuousLinearMap.id ℝ _ + η • B (ξ k)) fallback.val v.val
    HeavyTailedFreshProcess.noiseSum (transition B η fallback) (logNoise A B η) n v 0 ξ =
      ∑ k ∈ Finset.range n,
        η * ⟪path k + η • A (path k), B (ξ k) (path k) - A (path k)⟫ /
          ‖path k + η • A (path k)‖ ^ 2 := by
  intro path
  rw [HeavyTailedFreshProcess.noiseSum_eq_sum, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [logNoise, transition_trajectory]
  rfl

lemma remainder_sum_eq_path {d : ℕ} {Ω : Type*}
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η p : ℝ) (fallback v : UnitVector d) (n : ℕ) (ξ : ℕ → Ω) :
    let path := HeavyTailedProbeGeometry.normalizedPath
      (fun k => ContinuousLinearMap.id ℝ _ + η • B (ξ k)) fallback.val v.val
    HeavyTailedFreshProcess.noiseSum (transition B η fallback)
      (fun (w : UnitVector d) ω => 2 * η ^ p * ‖B ω w.val - A w.val‖ ^ p) n v 0 ξ =
      2 * η ^ p * ∑ k ∈ Finset.range n, ‖B (ξ k) (path k) - A (path k)‖ ^ p := by
  intro path
  rw [HeavyTailedFreshProcess.noiseSum_eq_sum, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [transition_trajectory]
  rfl

lemma logNoise_control {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {η p σ : ℝ} (hη : 0 ≤ η) (hp : 0 ≤ p)
    (hpos : ∀ v, 0 ≤ ⟪v, A v⟫)
    (hi : ∀ v, Integrable (fun ω => B ω v) P)
    (hm : ∀ v, (∫ ω, B ω v ∂P) = A v)
    (hpi : ∀ v, Integrable (fun ω => ‖B ω v - A v‖ ^ p) P)
    (hpb : ∀ v, (∫ ω, ‖B ω v - A v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p)
    (v : UnitVector d) :
    Integrable (logNoise A B η v) P ∧ (∫ ω, logNoise A B η v ω ∂P) = 0 ∧
      Integrable (fun ω => ‖logNoise A B η v ω‖ ^ p) P ∧
      (∫ ω, ‖logNoise A B η v ω‖ ^ p ∂P) ≤ η ^ p * σ ^ p := by
  let w := v.val + η • A v.val
  let c := (η / ‖w‖ ^ 2) • w
  have he : Integrable (fun ω => B ω v.val - A v.val) P :=
    (hi v.val).sub (integrable_const _)
  have hem : (∫ ω, B ω v.val - A v.val ∂P) = 0 := by
    rw [integral_sub (hi v.val) (integrable_const _), integral_const, hm v.val]
    simp
  have hb : (∫ ω, ‖B ω v.val - A v.val‖ ^ p ∂P) ≤ σ ^ p := by
    simpa only [v.property, Real.one_rpow, mul_one] using hpb v.val
  have hc : ‖c‖ ≤ η := HeavyTailedSpectralMoments.log_coefficient_norm v.property hη (hpos v.val)
  have hproj := HeavyTailedSpectralMoments.projection_moment_control c hp hη hc he hem (hpi v.val) hb
  have heq (ω) : ⟪c, B ω v.val - A v.val⟫ = logNoise A B η v ω := by
    simp only [c, logNoise, w, real_inner_smul_left]
    ring
  simpa only [heq] using hproj

lemma logNoise_sum_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) {η p σ : ℝ} (hη : 0 ≤ η) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hpos : ∀ v, 0 ≤ ⟪v, A v⟫)
    (hi : ∀ v, Integrable (fun ω => B ω v) P)
    (hm : ∀ v, (∫ ω, B ω v ∂P) = A v)
    (hpi : ∀ v, Integrable (fun ω => ‖B ω v - A v‖ ^ p) P)
    (hpb : ∀ v, (∫ ω, ‖B ω v - A v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p)
    (fallback v : UnitVector d) (n : ℕ) :
    let X := HeavyTailedFreshProcess.noiseSum (transition B η fallback) (logNoise A B η) n v 0
    Integrable (fun ξ => ‖X ξ‖ ^ p) (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, ‖X ξ‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 6 * n * (η ^ p * σ ^ p) := by
  have hc := logNoise_control P A B hη (by linarith : 0 ≤ p) hpos hi hm hpi hpb
  have hh := HeavyTailedFreshProcess.noiseSum_moment P
    (transition_measurable B hB η fallback) (logNoise_measurable A B hB η) hp hp2
    (fun v => (hc v).1) (fun v => (hc v).2.1) (fun v => (hc v).2.2.1)
    (fun v => (hc v).2.2.2) n v 0
  simpa only [norm_zero, Real.zero_rpow (by linarith : p ≠ 0), zero_add] using hh

lemma remainder_sum_mean {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) {η p σ : ℝ} (hη : 0 ≤ η)
    (hpi : ∀ v, Integrable (fun ω => ‖B ω v - A v‖ ^ p) P)
    (hpb : ∀ v, (∫ ω, ‖B ω v - A v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p)
    (fallback v : UnitVector d) (n : ℕ) :
    let reward := fun (v : UnitVector d) ω => 2 * η ^ p * ‖B ω v.val - A v.val‖ ^ p
    let R := HeavyTailedFreshProcess.noiseSum (transition B η fallback) reward n v 0
    Integrable R (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, R ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ n * (2 * η ^ p * σ ^ p) := by
  intro reward R
  have happ : Measurable (fun t : UnitVector d × Ω => B t.2 t.1.val) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
      (F := EuclideanSpace ℝ (Fin d))).continuous.measurable.comp
      ((hB.comp measurable_snd).prodMk (measurable_subtype_coe.comp measurable_fst))
  have he : Measurable (Function.uncurry reward) :=
    ((happ.sub (A.measurable.comp (measurable_subtype_coe.comp measurable_fst))).norm.pow_const p).const_mul _
  have hi (v : UnitVector d) : Integrable (reward v) P := (hpi v.val).const_mul _
  have hb (v : UnitVector d) : (∫ ω, reward v ω ∂P) ≤ 2 * η ^ p * σ ^ p := by
    dsimp only [reward]
    rw [integral_const_mul]
    have hh := hpb v.val
    rw [v.property, Real.one_rpow, mul_one] at hh
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  have hh := HeavyTailedFreshProcess.noiseSum_nonnegative_integral P
    (transition_measurable B hB η fallback) he
    (fun v ω => by dsimp only [reward]; positivity) hi hb n v (le_refl 0)
  simpa only [zero_add] using hh

end LongTails.Proofs.HeavyTailedSpectralProcess
