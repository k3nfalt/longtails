import LongTails.Proofs.HeavyTailedSpectralProcess
import LongTails.Proofs.HeavyTailedSpectralProbability

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Proofs.HeavyTailedSpectralProcess

namespace LongTails.Proofs.HeavyTailedSpectralEnergy

noncomputable def signInitial {d : ℕ} (hd : 0 < d) (s : Fin d → Bool) : UnitVector d :=
  ⟨LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector s,
    HeavyTailedProbeGeometry.initialVector_norm hd s⟩

noncomputable def initialPath {d : ℕ} {Ω : Type*}
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η : ℝ) (z : (Fin d → Bool) × (ℕ → Ω)) : ℕ → EuclideanSpace ℝ (Fin d) :=
  HeavyTailedProbeGeometry.normalizedPath
    (fun k => ContinuousLinearMap.id ℝ _ + η • B (z.2 k))
    (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.1)
    (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.1)

lemma initialPath_norm {d : ℕ} {Ω : Type*} (hd : 0 < d)
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η : ℝ) (z : (Fin d → Bool) × (ℕ → Ω)) (k : ℕ) : ‖initialPath B η z k‖ = 1 :=
  HeavyTailedProbeGeometry.normalizedPath_norm _
    (HeavyTailedProbeGeometry.initialVector_norm hd z.1)
    (HeavyTailedProbeGeometry.initialVector_norm hd z.1) k

lemma initialPath_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) (η : ℝ) (k : ℕ) :
    Measurable (fun z => initialPath B η z k) := by
  have hi : Measurable (fun z : (Fin d → Bool) × (ℕ → Ω) =>
      LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.1) :=
    (measurable_of_finite (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector (d := d))).comp measurable_fst
  exact HeavyTailedProbeGeometry.normalizedPath_measurable _
    (fun k => measurable_const.add ((hB.comp ((measurable_pi_apply k).comp measurable_snd)).const_smul η))
    _ _ hi hi k

lemma initialProduct_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) (η : ℝ) (n : ℕ) :
    Measurable (fun z : (Fin d → Bool) × (ℕ → Ω) =>
      HeavyTailedProbeGeometry.linearProduct
        (fun k => ContinuousLinearMap.id ℝ _ + η • B (z.2 k)) n
        (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.1)) := by
  have hp := HeavyTailedProbeGeometry.linearProduct_measurable
    (fun z : (Fin d → Bool) × (ℕ → Ω) =>
      fun k => ContinuousLinearMap.id ℝ _ + η • B (z.2 k))
    (fun k => measurable_const.add ((hB.comp ((measurable_pi_apply k).comp measurable_snd)).const_smul η)) n
  exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
    (F := EuclideanSpace ℝ (Fin d))).continuous.measurable.comp
    (hp.prodMk ((measurable_of_finite (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector (d := d))).comp measurable_fst))

noncomputable def initialLogNoise {d : ℕ} {Ω : Type*} (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η : ℝ) (n : ℕ) (z : (Fin d → Bool) × (ℕ → Ω)) : ℝ :=
  HeavyTailedFreshProcess.noiseSum (transition B η (signInitial hd z.1))
    (logNoise A B η) n (signInitial hd z.1) 0 z.2

noncomputable def initialRemainder {d : ℕ} {Ω : Type*} (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (η p : ℝ) (n : ℕ) (z : (Fin d → Bool) × (ℕ → Ω)) : ℝ :=
  HeavyTailedFreshProcess.noiseSum (transition B η (signInitial hd z.1))
    (fun (v : UnitVector d) ω => 2 * η ^ p * ‖B ω v.val - A v.val‖ ^ p)
    n (signInitial hd z.1) 0 z.2

lemma initialLogNoise_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) (η : ℝ) (n : ℕ) : Measurable (initialLogNoise hd A B η n) := by
  apply measurable_from_prod_countable_right
  intro s
  exact (HeavyTailedFreshProcess.noiseSum_measurable
    (transition_measurable B hB η (signInitial hd s)) (logNoise_measurable A B hB η) n).comp
    (show Measurable (fun ξ : ℕ → Ω => ((signInitial hd s, (0 : ℝ)), ξ)) from
      measurable_const.prodMk measurable_id)

lemma initialLogNoise_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) {η p σ : ℝ} (hη : 0 ≤ η) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hpos : ∀ v, 0 ≤ ⟪v, A v⟫)
    (hi : ∀ v, Integrable (fun ω => B ω v) P)
    (hm : ∀ v, (∫ ω, B ω v ∂P) = A v)
    (hpi : ∀ v, Integrable (fun ω => ‖B ω v - A v‖ ^ p) P)
    (hpb : ∀ v, (∫ ω, ‖B ω v - A v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p) (n : ℕ) :
    let Q := (PMF.uniformOfFintype (Fin d → Bool)).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => P)
    Integrable (fun z => ‖initialLogNoise hd A B η n z‖ ^ p) Q ∧
      (∫ z, ‖initialLogNoise hd A B η n z‖ ^ p ∂Q) ≤ 6 * n * (η ^ p * σ ^ p) := by
  intro Q
  have hFi := fun s => logNoise_sum_moment P A B hB hη hp hp2 hpos hi hm hpi hpb
    (signInitial hd s) (signInitial hd s) n
  have hF := ((initialLogNoise_measurable hd A B hB η n).norm.pow_const p).stronglyMeasurable
  have hh := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := (PMF.uniformOfFintype (Fin d → Bool)).toMeasure) hF (fun z => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall (fun s => (hFi s).1))
    (integrable_const (6 * n * (η ^ p * σ ^ p)))
    (Filter.Eventually.of_forall (fun s => (hFi s).2))
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

lemma initialRemainder_measurable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) (η p : ℝ) (n : ℕ) : Measurable (initialRemainder hd A B η p n) := by
  have happ : Measurable (fun t : UnitVector d × Ω => B t.2 t.1.val) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
      (F := EuclideanSpace ℝ (Fin d))).continuous.measurable.comp
      ((hB.comp measurable_snd).prodMk (measurable_subtype_coe.comp measurable_fst))
  have hr : Measurable (fun t : UnitVector d × Ω => 2 * η ^ p * ‖B t.2 t.1.val - A t.1.val‖ ^ p) :=
    ((happ.sub (A.measurable.comp (measurable_subtype_coe.comp measurable_fst))).norm.pow_const p).const_mul _
  apply measurable_from_prod_countable_right
  intro s
  exact (HeavyTailedFreshProcess.noiseSum_measurable
    (noise := fun (v : UnitVector d) ω => 2 * η ^ p * ‖B ω v.val - A v.val‖ ^ p)
    (transition_measurable B hB η (signInitial hd s)) hr n).comp
    (show Measurable (fun ξ : ℕ → Ω => ((signInitial hd s, (0 : ℝ)), ξ)) from
      measurable_const.prodMk measurable_id)

lemma initialRemainder_nonnegative {d : ℕ} {Ω : Type*} (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    {η : ℝ} (hη : 0 ≤ η) (p : ℝ) (n : ℕ) (z : (Fin d → Bool) × (ℕ → Ω)) :
    0 ≤ initialRemainder hd A B η p n z :=
  HeavyTailedFreshProcess.noiseSum_nonnegative (fun v ω => by positivity) n
    (signInitial hd z.1) (le_refl 0) z.2

lemma initialRemainder_mean {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) {η p σ : ℝ} (hη : 0 ≤ η)
    (hpi : ∀ v, Integrable (fun ω => ‖B ω v - A v‖ ^ p) P)
    (hpb : ∀ v, (∫ ω, ‖B ω v - A v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p) (n : ℕ) :
    let Q := (PMF.uniformOfFintype (Fin d → Bool)).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => P)
    Integrable (initialRemainder hd A B η p n) Q ∧
      (∫ z, initialRemainder hd A B η p n z ∂Q) ≤ n * (2 * η ^ p * σ ^ p) := by
  intro Q
  have hFi := fun s => remainder_sum_mean P A B hB hη hpi hpb
    (signInitial hd s) (signInitial hd s) n
  have hh := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := (PMF.uniformOfFintype (Fin d → Bool)).toMeasure)
    (initialRemainder_measurable hd A B hB η p n).stronglyMeasurable
    (initialRemainder_nonnegative hd A B hη p n)
    (Filter.Eventually.of_forall (fun s => (hFi s).1))
    (integrable_const (n * (2 * η ^ p * σ ^ p)))
    (Filter.Eventually.of_forall (fun s => (hFi s).2))
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

lemma energy_from_growth_probability {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) {η p σ ell γ c : ℝ} (hη : 0 < η) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hell : 0 ≤ ell) (hηell : η * ell ≤ 1) (hγ : 0 < γ)
    (hpos : ∀ v, 0 ≤ ⟪v, A v⟫) (hbound : ∀ v, ‖A v‖ ≤ ell * ‖v‖)
    (hi : ∀ v, Integrable (fun ω => B ω v) P)
    (hm : ∀ v, (∫ ω, B ω v ∂P) = A v)
    (hpi : ∀ v, Integrable (fun ω => ‖B ω v - A v‖ ^ p) P)
    (hpb : ∀ v, (∫ ω, ‖B ω v - A v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p)
    (n : ℕ) [NeZero n]
    (htune : 8 * (Real.log (2 * Real.sqrt (2 * d)) + 2) ≤ η * n * γ)
    (hgrowth : c ≤ ((PMF.uniformOfFintype (Fin d → Bool)).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => P)).real
      {z | ((1 + η * ell) ^ n / 2) ^ 2 / (2 * d) ≤
        ‖HeavyTailedProbeGeometry.linearProduct
          (fun k => ContinuousLinearMap.id ℝ _ + η • B (z.2 k)) n
          (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.1)‖ ^ 2}) :
    (c - 8 * n * (η ^ p * σ ^ p)) / 2 ≤
      (((PMF.uniformOfFintype (Fin d → Bool)).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => P)).prod
        (PMF.uniformOfFintype (Fin n)).toMeasure).real
      {z | ell - ⟪initialPath B η z.1 z.2.val, A (initialPath B η z.1 z.2.val)⟫ ≤ γ} := by
  let Q := (PMF.uniformOfFintype (Fin d → Bool)).toMeasure.prod
    (Measure.infinitePi fun _ : ℕ => P)
  let G := {z : (Fin d → Bool) × (ℕ → Ω) |
    ((1 + η * ell) ^ n / 2) ^ 2 / (2 * d) ≤
      ‖HeavyTailedProbeGeometry.linearProduct
        (fun k => ContinuousLinearMap.id ℝ _ + η • B (z.2 k)) n
        (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.1)‖ ^ 2}
  let M := initialLogNoise hd A B η n
  let R := initialRemainder hd A B η p n
  let good := {z | z ∈ G ∧ M z ≤ 1 ∧ R z ≤ 1}
  have hG : MeasurableSet G := measurableSet_le measurable_const
    ((initialProduct_measurable B hB η n).norm.pow_const 2)
  have hgood : MeasurableSet good := hG.inter
    ((measurableSet_le (initialLogNoise_measurable hd A B hB η n) measurable_const).inter
      (measurableSet_le (initialRemainder_measurable hd A B hB η p n) measurable_const))
  have hM := initialLogNoise_moment P hd A B hB hη.le hp hp2 hpos hi hm hpi hpb n
  have hR := initialRemainder_mean P hd A B hB hη.le hpi hpb n
  have hMb : (∫ z, ‖M z‖ ^ p ∂Q) ≤ 6 * (n * (η ^ p * σ ^ p)) := by
    convert hM.2 using 1
    ring
  have hRb : (∫ z, R z ∂Q) ≤ 2 * (n * (η ^ p * σ ^ p)) := by
    convert hR.2 using 1
    ring
  have hgoodmass := HeavyTailedSpectralProbability.log_error_intersection Q
    (by linarith : 0 ≤ p) hM.1 hMb hR.1 (initialRemainder_nonnegative hd A B hη.le p n) hRb hgrowth
  let X := fun (z : (Fin d → Bool) × (ℕ → Ω)) (i : Fin n) =>
    ell - ⟪initialPath B η z i.val, A (initialPath B η z i.val)⟫
  have hpath : Measurable (fun z : ((Fin d → Bool) × (ℕ → Ω)) × Fin n =>
      initialPath B η z.1 z.2.val) :=
    measurable_from_prod_countable_left (fun i => initialPath_measurable B hB η i.val)
  have hX : Measurable (Function.uncurry X) :=
    measurable_const.sub (hpath.inner (A.measurable.comp hpath))
  have hXpos (z) (i : Fin n) : 0 ≤ X z i := by
    have hunit := initialPath_norm hd B η z i.val
    have hh := real_inner_le_norm (initialPath B η z i.val) (A (initialPath B η z i.val))
    have hAv := hbound (initialPath B η z i.val)
    rw [hunit, one_mul] at hh
    rw [hunit, mul_one] at hAv
    exact sub_nonneg.mpr (hh.trans hAv)
  have hsum (z) (hz : z ∈ good) : ∑ i, X z i ≤ n * γ / 2 := by
    rcases hz with ⟨hg, hm', hr'⟩
    change initialLogNoise hd A B η n z ≤ 1 at hm'
    change initialRemainder hd A B η p n z ≤ 1 at hr'
    dsimp only [initialLogNoise] at hm'
    dsimp only [initialRemainder] at hr'
    rw [logNoise_sum_eq_path] at hm'
    rw [remainder_sum_eq_path] at hr'
    have hinit := HeavyTailedProbeGeometry.initialVector_norm hd z.1
    have havg := HeavyTailedSpectralPath.average_deficit_of_growth hd A (fun k => B (z.2 k))
      hη hell hηell hp hp2 hpos hbound _ _ hinit hinit n htune hg hm' hr'
    dsimp only [X]
    rw [Fin.sum_univ_eq_sum_range (fun k => ell - ⟪initialPath B η z k, A (initialPath B η z k)⟫)]
    exact havg
  have htarget := HeavyTailedSpectralProbability.random_target_good_probability Q X hX
    hgood hγ hXpos hsum
  change (c - 8 * n * (η ^ p * σ ^ p)) / 2 ≤ _
  change c - 8 * (n * (η ^ p * σ ^ p)) ≤ Q.real good at hgoodmass
  linarith

lemma spectral_energy_probability {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) {η p q σ ell γ : ℝ} (hη : 0 < η) (hpq : p.HolderConjugate q) (hp2 : p ≤ 2)
    (hell : 0 ≤ ell) (hηell : η * ell ≤ 1) (hγ : 0 < γ) (hσ : 0 ≤ σ)
    (hpos : ∀ v, 0 ≤ ⟪v, A v⟫) (hA : ‖A‖ ≤ ell)
    (hi : ∀ v, Integrable (fun ω => B ω v) P)
    (hm : ∀ v, (∫ ω, B ω v ∂P) = A v)
    (hpi : ∀ v, Integrable (fun ω => ‖B ω v - A v‖ ^ p) P)
    (hpb : ∀ v, (∫ ω, ‖B ω v - A v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p)
    {u : EuclideanSpace ℝ (Fin d)} (hu : A u = ell • u) (hunit : ‖u‖ = 1)
    (n : ℕ) [NeZero n]
    (htune : 8 * (Real.log (2 * Real.sqrt (2 * d)) + 2) ≤ η * n * γ)
    (hsmall : ((1 + η * ell) ^ p + 6 * η ^ p * σ ^ p) ^ n ≤
      (2 * (1 + η * ell) ^ n) ^ p)
    (hnoise : n * (η ^ p * σ ^ p) ≤ (1 / 4 : ℝ) ^ q / 256) :
    (1 / 4 : ℝ) ^ q / 64 ≤
      (((PMF.uniformOfFintype (Fin d → Bool)).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => P)).prod
        (PMF.uniformOfFintype (Fin n)).toMeasure).real
      {z | ell - ⟪initialPath B η z.1 z.2.val, A (initialPath B η z.1 z.2.val)⟫ ≤ γ} := by
  have hg := HeavyTailedSpectralProbability.random_initial_growth_probability P hd A B hB
    hpq hp2 hη.le hell hA hi hm hpi hpb hσ hu hunit n hsmall
  let G := {z : (ℕ → Ω) × (Fin d → Bool) |
    ((1 + η * ell) ^ n / 2) ^ 2 / (2 * d) ≤
      ‖HeavyTailedProbeGeometry.linearProduct
        (fun k => ContinuousLinearMap.id ℝ _ + η • B (z.1 k)) n
        (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.2)‖ ^ 2}
  have hG : MeasurableSet G := measurableSet_le measurable_const
    (((initialProduct_measurable B hB η n).comp measurable_swap).norm.pow_const 2)
  have heq := (Measure.measurePreserving_swap
    (μ := (PMF.uniformOfFintype (Fin d → Bool)).toMeasure)
    (ν := Measure.infinitePi fun _ : ℕ => P)).measureReal_preimage hG.nullMeasurableSet
  change (1 / 4 : ℝ) ^ q / 16 ≤
    ((Measure.infinitePi fun _ : ℕ => P).prod
      (PMF.uniformOfFintype (Fin d → Bool)).toMeasure).real G at hg
  rw [← heq] at hg
  have hbound (v : EuclideanSpace ℝ (Fin d)) : ‖A v‖ ≤ ell * ‖v‖ :=
    (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v))
  have hh := energy_from_growth_probability P hd A B hB hη hpq.lt.le hp2 hell hηell hγ
    hpos hbound hi hm hpi hpb n htune hg
  nlinarith

end LongTails.Proofs.HeavyTailedSpectralEnergy
