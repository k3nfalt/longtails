import LongTails.Proofs.HeavyTailedRademacherInitialization
import LongTails.Proofs.HeavyTailedProductProcess

open MeasureTheory

namespace LongTails.Proofs.HeavyTailedSpectralProbability

lemma product_event_lower {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {G : Set Ω} {S : Set (Ω × Ξ)} (hG : MeasurableSet G) (hS : MeasurableSet S)
    {c : ℝ} (hf : ∀ x ∈ G, c ≤ Q.real (Prod.mk x ⁻¹' S)) :
    c * P.real G ≤ (P.prod Q).real S := by
  let F : Ω × Ξ → ℝ := S.indicator 1
  have hFi : Integrable F (P.prod Q) := (integrable_const (1 : ℝ)).indicator hS
  have hinner (x : Ω) : (∫ y, F (x, y) ∂Q) = Q.real (Prod.mk x ⁻¹' S) := by
    change (∫ y, (Prod.mk x ⁻¹' S).indicator 1 y ∂Q) = _
    exact integral_indicator_one (hS.preimage measurable_prodMk_left)
  have hb := integral_mono ((integrable_const c).indicator hG) hFi.integral_prod_left
    (fun x => show G.indicator (fun _ => c) x ≤ ∫ y, F (x, y) ∂Q from by
      rw [hinner]
      by_cases hx : x ∈ G
      · simpa only [Set.indicator_of_mem hx] using hf x hx
      · simp only [Set.indicator_of_notMem hx]
        exact measureReal_nonneg)
  rw [integral_indicator_const c hG, smul_eq_mul] at hb
  rw [← integral_prod F hFi, integral_indicator_one hS] at hb
  nlinarith

lemma random_sign_product_growth {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : 0 < d)
    (M : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hM : Measurable M) (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    {b : ℝ} (hb : 0 < b) :
    P.real {ω | b ≤ ‖M ω u‖} / 16 ≤
      (P.prod (PMF.uniformOfFintype (Fin d → Bool)).toMeasure).real
        {z | b ^ 2 / (2 * d) ≤
          ‖M z.1 (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.2)‖ ^ 2} := by
  let G := {ω | b ≤ ‖M ω u‖}
  let S := {z : Ω × (Fin d → Bool) | b ^ 2 / (2 * d) ≤
    ‖M z.1 (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.2)‖ ^ 2}
  have hG : MeasurableSet G := measurableSet_le measurable_const (hM.apply_continuousLinearMap u).norm
  have happ : Measurable (fun z : Ω × (Fin d → Bool) =>
      M z.1 (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.2)) := by
    have hi : Measurable (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector
        (d := d)) := measurable_of_finite _
    exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
      (F := EuclideanSpace ℝ (Fin d))).continuous.measurable.comp
      ((hM.comp measurable_fst).prodMk (hi.comp measurable_snd))
  have hS : MeasurableSet S := measurableSet_le measurable_const (happ.norm.pow_const 2)
  have hf (ω : Ω) (hω : ω ∈ G) :
      (1 / 16 : ℝ) ≤ ((PMF.uniformOfFintype (Fin d → Bool)).toMeasure).real
        (Prod.mk ω ⁻¹' S) := by
    change b ≤ ‖M ω u‖ at hω
    have hMu : M ω u ≠ 0 := norm_pos_iff.mp (hb.trans_le hω)
    apply (HeavyTailedRademacherInitialization.sign_image_amplification hd (M ω) u hu hMu).trans
    apply measureReal_mono (μ := (PMF.uniformOfFintype (Fin d → Bool)).toMeasure)
      (s₂ := Prod.mk ω ⁻¹' S)
    intro s hs
    have hsq : b ^ 2 ≤ ‖M ω u‖ ^ 2 := by nlinarith [norm_nonneg (M ω u)]
    exact (div_le_div_of_nonneg_right hsq (by positivity)).trans hs
  have hh := product_event_lower P (PMF.uniformOfFintype (Fin d → Bool)).toMeasure hG hS hf
  change P.real G / 16 ≤ _
  convert hh using 1
  ring

lemma random_initial_growth_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (hd : 0 < d)
    (A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hB : Measurable B) {p q η ell σ : ℝ} (hpq : p.HolderConjugate q) (hp2 : p ≤ 2)
    (hη : 0 ≤ η) (hell : 0 ≤ ell) (hA : ‖A‖ ≤ ell)
    (hi : ∀ v, Integrable (fun ω => B ω v) P)
    (hm : ∀ v, (∫ ω, B ω v ∂P) = A v)
    (hpi : ∀ v, Integrable (fun ω => ‖B ω v - A v‖ ^ p) P)
    (hpb : ∀ v, (∫ ω, ‖B ω v - A v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p)
    (hσ : 0 ≤ σ) {u : EuclideanSpace ℝ (Fin d)} (hu : A u = ell • u) (hunit : ‖u‖ = 1)
    (n : ℕ)
    (hsmall : ((1 + η * ell) ^ p + 6 * η ^ p * σ ^ p) ^ n ≤
      (2 * (1 + η * ell) ^ n) ^ p) :
    (1 / 4 : ℝ) ^ q / 16 ≤
      ((Measure.infinitePi fun _ : ℕ => P).prod
        (PMF.uniformOfFintype (Fin d → Bool)).toMeasure).real
        {z | ((1 + η * ell) ^ n / 2) ^ 2 / (2 * d) ≤
          ‖HeavyTailedProbeGeometry.linearProduct
            (fun k => ContinuousLinearMap.id ℝ _ + η • B (z.1 k)) n
            (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector z.2)‖ ^ 2} := by
  let step := fun v ω => v + η • B ω v
  let M := ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)) + η • A
  have hs : Measurable (Function.uncurry step) := by
    have happ : Measurable (fun t : EuclideanSpace ℝ (Fin d) × Ω => B t.2 t.1) :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
        (F := EuclideanSpace ℝ (Fin d))).continuous.measurable.comp
        ((hB.comp measurable_snd).prodMk measurable_fst)
    exact measurable_fst.add (happ.const_smul η)
  have hsi (v) : Integrable (step v) P := (integrable_const v).add ((hi v).smul η)
  have hsm (v) : (∫ ω, step v ω ∂P) = M v := by
    have hism : Integrable (fun ω => η • B ω v) P := (hi v).smul η
    rw [show step v = fun ω => v + η • B ω v from rfl,
      integral_add (integrable_const v) hism, integral_const, integral_smul, hm v]
    simp [M]
  have hc := fun v => HeavyTailedSpectralMoments.action_moment_control A B v
    hpq.lt.le hp2 hη hell hA (hi v) (hm v) (hpi v) (hpb v)
  have ha : 0 < 1 + η * ell := by positivity
  have heu : M u = (1 + η * ell) • u := by
    simp only [M, add_apply, smul_apply, ContinuousLinearMap.id_apply, hu, smul_smul]
    rw [add_smul, one_smul]
  have hg := HeavyTailedProductProcess.trajectory_growth_probability P hs M hsi hsm hpq
    (by positivity) ha (fun v => (hc v).1) (fun v => (hc v).2) heu hunit n hsmall
  let product := fun ξ : ℕ → Ω => HeavyTailedProbeGeometry.linearProduct
    (fun k => ContinuousLinearMap.id ℝ _ + η • B (ξ k)) n
  have hproduct : Measurable product :=
    HeavyTailedProbeGeometry.linearProduct_measurable _
      (fun k => measurable_const.add ((hB.comp (measurable_pi_apply k)).const_smul η)) n
  have heq (ξ : ℕ → Ω) : HeavyTailedProductProcess.trajectory step n u ξ = product ξ u := by
    exact HeavyTailedProductProcess.trajectory_linearProduct
      (fun ω => ContinuousLinearMap.id ℝ _ + η • B ω) n u ξ
  simp_rw [heq] at hg
  have hsign := random_sign_product_growth (Measure.infinitePi fun _ : ℕ => P)
    hd product hproduct u hunit (div_pos (pow_pos ha n) (by norm_num : (0 : ℝ) < 2))
  exact (div_le_div_of_nonneg_right hg (by norm_num : (0 : ℝ) ≤ 16)).trans hsign

lemma half_mass_below_twice_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hi : Integrable X P) (hpos : ∀ ω, 0 ≤ X ω)
    {γ : ℝ} (hγ : 0 < γ) (hmean : (∫ ω, X ω ∂P) ≤ γ / 2) :
    (1 / 2 : ℝ) ≤ P.real {ω | X ω ≤ γ} := by
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hpos) hi γ
  have hbad : P.real {ω | γ ≤ X ω} ≤ 1 / 2 := by nlinarith
  have hsub : {ω | X ω ≤ γ}ᶜ ⊆ {ω | γ ≤ X ω} := by
    intro ω hω
    change ¬ X ω ≤ γ at hω
    exact le_of_lt (lt_of_not_ge hω)
  have hc := measureReal_mono (μ := P) hsub
  rw [measureReal_compl (measurableSet_le hX measurable_const), probReal_univ] at hc
  linarith

lemma uniform_half_small {n : ℕ} [NeZero n] (X : Fin n → ℝ)
    (hpos : ∀ k, 0 ≤ X k) {γ : ℝ} (hγ : 0 < γ)
    (hsum : ∑ k, X k ≤ n * γ / 2) :
    (1 / 2 : ℝ) ≤ ((PMF.uniformOfFintype (Fin n)).toMeasure).real {k | X k ≤ γ} := by
  apply half_mass_below_twice_mean _ (measurable_of_finite X) Integrable.of_finite hpos hγ
  rw [OracleTemplate.FiniteSum.uniform_integral, Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast NeZero.pos n)).mpr
  linarith

lemma random_target_good_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    (X : Ω → Fin n → ℝ) (hX : Measurable (Function.uncurry X))
    {G : Set Ω} (hG : MeasurableSet G) {γ : ℝ} (hγ : 0 < γ)
    (hpos : ∀ ω k, 0 ≤ X ω k) (hgood : ∀ ω ∈ G, ∑ k, X ω k ≤ n * γ / 2) :
    P.real G / 2 ≤ (P.prod (PMF.uniformOfFintype (Fin n)).toMeasure).real
      {z | X z.1 z.2 ≤ γ} := by
  have hS : MeasurableSet {z : Ω × Fin n | X z.1 z.2 ≤ γ} :=
    measurableSet_le hX measurable_const
  have hh := product_event_lower P (PMF.uniformOfFintype (Fin n)).toMeasure hG hS
    (fun ω hω => uniform_half_small (X ω) (hpos ω) hγ (hgood ω hω))
  linarith

lemma log_error_intersection {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {M R : Ω → ℝ} {p z c : ℝ}
    (hp : 0 ≤ p) (hMp : Integrable (fun ω => ‖M ω‖ ^ p) P)
    (hMb : (∫ ω, ‖M ω‖ ^ p ∂P) ≤ 6 * z)
    (hRi : Integrable R P) (hRp : ∀ ω, 0 ≤ R ω) (hRb : (∫ ω, R ω ∂P) ≤ 2 * z)
    {G : Set Ω} (hG : c ≤ P.real G) :
    c - 8 * z ≤ P.real {ω | ω ∈ G ∧ M ω ≤ 1 ∧ R ω ≤ 1} := by
  have hMm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (norm_nonneg (M ω)) p)) hMp 1
  have hMi : P.real {ω | 1 < M ω} ≤ 6 * z := by
    have hsub : {ω | 1 < M ω} ⊆ {ω | 1 ≤ ‖M ω‖ ^ p} := by
      intro ω hω
      exact Real.one_le_rpow ((le_abs_self (M ω)).trans' (le_of_lt hω)) hp
    have hh := measureReal_mono (μ := P) hsub
    simp only [one_mul] at hMm
    exact hh.trans (hMm.trans hMb)
  have hRm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hRp) hRi 1
  have hRi' : P.real {ω | 1 < R ω} ≤ 2 * z := by
    have hh := measureReal_mono (μ := P)
      (show {ω | 1 < R ω} ⊆ {ω | 1 ≤ R ω} from fun ω h => (show 1 < R ω from h).le)
    simp only [one_mul] at hRm
    exact hh.trans (hRm.trans hRb)
  let bad := {ω | 1 < M ω} ∪ {ω | 1 < R ω}
  have hbad : P.real bad ≤ 8 * z := by
    have hh := measureReal_union_le (μ := P) {ω | 1 < M ω} {ω | 1 < R ω}
    dsimp only [bad]
    linarith
  have hd := le_measureReal_sdiff (μ := P) (s₁ := G) (s₂ := bad)
  have heq : G \ bad = {ω | ω ∈ G ∧ M ω ≤ 1 ∧ R ω ≤ 1} := by
    ext ω
    simp only [bad, Set.mem_sdiff, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt]
  rw [heq] at hd
  linarith

end LongTails.Proofs.HeavyTailedSpectralProbability
