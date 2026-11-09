import LongTails.Proofs.AffineSoftmaxSampling
import LongTails.Proofs.SmoothFiniteMaximumGeometry
import LongTails.Proofs.AffineSoftmaxExecution

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineSoftmaxMoments

open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxQueries
open LongTails.Proofs.AffineSoftmaxResidual
open LongTails.Proofs.AffineSoftmaxSampling

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma normalized_correction (q w : ι → ℝ) (g a : ι → E)
    (hq : ∑ i, q i = 1) (hZ : (∑ i, q i * w i) ≠ 0) :
    (∑ i, q i • a i) + (∑ i, q i * w i)⁻¹ •
      (∑ i, q i • correction (w i) (g i) (a i) (∑ j, q j • a j)) =
      ∑ i, (q i * w i / ∑ j, q j * w j) • g i := by
  rw [weighted_correction q w g a hq]
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ hZ, one_smul]
  rw [← add_sub_assoc, add_sub_cancel_left]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  ring

lemma gibbs_correction_mean [Nonempty ι] (τ : ℝ) (v w : ι → ℝ) (g a : ι → E) :
    let q := gibbsWeight τ v
    let weights := fun i => Real.exp ((w i - v i) / τ)
    (∑ i, q i • a i) + (∑ i, q i * weights i)⁻¹ •
      (∑ i, q i • correction (weights i) (g i) (a i) (∑ j, q j • a j)) =
      ∑ i, gibbsWeight τ w i • g i := by
  dsimp only
  have hZ : 0 < ∑ i, gibbsWeight τ v i * Real.exp ((w i - v i) / τ) :=
    Finset.sum_pos (fun i _ => mul_pos (gibbsWeight_pos τ v i) (Real.exp_pos _))
      Finset.univ_nonempty
  rw [normalized_correction _ _ g a (gibbsWeight_sum τ v) hZ.ne']
  simp_rw [gibbs_reweight]


lemma reciprocal_row_measurable (w : unitInterval → ℝ) (hw : Measurable w) (k : ℕ) :
    Measurable (fun row : Fin k → unitInterval => reciprocal (List.ofFn (fun j => w (row j)))) := by
  simp_rw [reciprocal_ofFn]
  apply Finset.measurable_prod
  intro i _
  exact measurable_const.sub (hw.comp (measurable_pi_apply i))

lemma reciprocal_rows_integrable (w : unitInterval → ℝ) (hw : Measurable w)
    (hbound : ∀ u, 1 ≤ w u ∧ w u ≤ 2) :
    Integrable (fun z : ℕ × Rows => reciprocal (List.ofFn (fun j => w (z.2 z.1 j))))
      ((countLaw : Measure ℕ).prod (rowsLaw : Measure Rows)) := by
  have hm := selected_row_measurable _ (reciprocal_row_measurable w hw)
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have hb := reciprocal_bounds (List.ofFn (fun j => w (z.2 z.1 j))) (by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hbound _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

lemma reciprocal_rows_mean (w : unitInterval → ℝ) (hw : Measurable w)
    (hbound : ∀ u, 1 ≤ w u ∧ w u ≤ 2) {Z : ℝ}
    (hmean : (∫ u : unitInterval, 2 - w u) = 2 - Z) (hZ : 1 ≤ Z) (hZ2 : Z ≤ 2) :
    (∫ z : ℕ × Rows, reciprocal (List.ofFn (fun j => w (z.2 z.1 j)))
      ∂(countLaw : Measure ℕ).prod (rowsLaw : Measure Rows)) = 1 / Z := by
  rw [integral_prod _ (reciprocal_rows_integrable w hw hbound)]
  have hi (k : ℕ) : (∫ rows, reciprocal (List.ofFn (fun j => w (rows k j)))
      ∂(rowsLaw : Measure Rows)) = (2 - Z) ^ k := by
    rw [rows_integral k _ (reciprocal_row_measurable w hw k)]
    have hh := reciprocal_fixed_mean (⟨volume, inferInstance⟩ : ProbabilityMeasure unitInterval) w k
    change (∫ row : Fin k → unitInterval, reciprocal (List.ofFn (fun j => w (row j)))
      ∂Measure.pi (fun _ => (volume : Measure unitInterval))) = (∫ u : unitInterval, 2 - w u) ^ k at hh
    rw [hmean] at hh
    exact hh
  simp_rw [hi]
  exact reciprocal_mean hZ hZ2


lemma step_correction_mean [CompleteSpace E] (R : ℕ × Rows → ℝ) (N : unitInterval → E) (b : E)
    (hR : Integrable R ((countLaw : Measure ℕ).prod (rowsLaw : Measure Rows)))
    (hN : Integrable N (volume : Measure unitInterval)) :
    (∫ s : StepSeed, b + R (s.1, s.2.2) • N s.2.1 ∂(stepLaw : Measure StepSeed)) =
      b + (∫ z, R z ∂(countLaw : Measure ℕ).prod (rowsLaw : Measure Rows)) •
        (∫ u : unitInterval, N u) := by
  let e : StepSeed ≃ᵐ (ℕ × Rows) × unitInterval :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℕ)
      (MeasurableEquiv.prodComm : unitInterval × Rows ≃ᵐ Rows × unitInterval)).trans
        (MeasurableEquiv.prodAssoc : (ℕ × Rows) × unitInterval ≃ᵐ ℕ × Rows × unitInterval).symm
  have hs := (MeasurePreserving.id (countLaw : Measure ℕ)).prod
    (Measure.measurePreserving_swap (μ := (volume : Measure unitInterval)) (ν := (rowsLaw : Measure Rows)))
  have ha := (measurePreserving_prodAssoc (countLaw : Measure ℕ) (rowsLaw : Measure Rows)
    (volume : Measure unitInterval)).symm
  have he : MeasurePreserving e (stepLaw : Measure StepSeed)
      (((countLaw : Measure ℕ).prod (rowsLaw : Measure Rows)).prod (volume : Measure unitInterval)) :=
    ha.comp hs
  calc
    _ = ∫ z : (ℕ × Rows) × unitInterval, b + R z.1 • N z.2
        ∂((countLaw : Measure ℕ).prod (rowsLaw : Measure Rows)).prod (volume : Measure unitInterval) :=
      he.integral_comp' (fun z => b + R z.1 • N z.2)
    _ = _ := independent_correction_mean
      (⟨(countLaw : Measure ℕ).prod (rowsLaw : Measure Rows), inferInstance⟩ : ProbabilityMeasure (ℕ × Rows))
      (⟨volume, inferInstance⟩ : ProbabilityMeasure unitInterval) R N b hR hN


lemma seeded_estimator_mean [CompleteSpace E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ : ℝ) (x : E)
    (reply : ι × E → ℝ × E)
    (hweights : ∀ i, 1 ≤ Real.exp (((reply (i, x)).1 - affine s i x) / τ) ∧
      Real.exp (((reply (i, x)).1 - affine s i x) / τ) ≤ 2) :
    (∫ seed : StepSeed, OracleTemplate.ComponentEnvelope.Program.eval reply
      (seededEstimatorPlan s τ x seed) ∂(stepLaw : Measure StepSeed)) =
      ∑ i, gibbsWeight τ (fun j => (reply (j, x)).1) i • (reply (i, x)).2 := by
  let v := fun i => affine s i x
  let w := fun i => (reply (i, x)).1
  let a := fun i => Real.exp ((w i - v i) / τ)
  let q := gibbsWeight τ v
  let d := LongTails.Algorithms.FiniteCategoricalSampler.draw ι (gibbsWeights τ v)
  let Z := ∑ i, q i * a i
  let N := fun u : unitInterval => numerator s τ x (d u) (reply (d u, x))
  let R := fun z : ℕ × Rows => reciprocal (List.ofFn (fun j => a (d (z.2 z.1 j))))
  have hd : Measurable d := (categorical_draw_measurable ι).comp
    (measurable_const.prodMk measurable_id)
  have ha : Measurable (fun u : unitInterval => a (d u)) := (measurable_of_finite a).comp hd
  have hb : ∀ u : unitInterval, 1 ≤ a (d u) ∧ a (d u) ≤ 2 := fun u => hweights (d u)
  have hq : ∑ i, q i = 1 := gibbsWeight_sum τ v
  have hq0 : ∀ i, 0 ≤ q i := fun i => (gibbsWeight_pos τ v i).le
  have hZ : 1 ≤ Z := by
    calc
      1 = ∑ i, q i := hq.symm
      _ ≤ Z := Finset.sum_le_sum (fun i _ => by
        have hh := mul_le_mul_of_nonneg_left (hweights i).1 (hq0 i)
        simpa only [mul_one] using hh)
  have hZ2 : Z ≤ 2 := by
    calc
      Z ≤ ∑ i, q i * 2 := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hweights i).2 (hq0 i))
      _ = 2 := by rw [← Finset.sum_mul, hq, one_mul]
  have hwm : (∫ u : unitInterval, 2 - a (d u)) = 2 - Z := by
    have hh := gibbs_draw_integral ι τ v (fun i => 2 - a i)
    change (∫ u : unitInterval, 2 - a (d u)) = ∑ i, q i * (2 - a i) at hh
    simpa only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq, one_mul] using hh
  have hRi : Integrable R ((countLaw : Measure ℕ).prod (rowsLaw : Measure Rows)) :=
    reciprocal_rows_integrable (fun u => a (d u)) ha hb
  have hRm : (∫ z, R z ∂(countLaw : Measure ℕ).prod (rowsLaw : Measure Rows)) = 1 / Z :=
    reciprocal_rows_mean (fun u => a (d u)) ha hb hwm hZ hZ2
  have hNi : Integrable N (volume : Measure unitInterval) :=
    categorical_draw_integrable ι (gibbsWeights τ v) (fun i => numerator s τ x i (reply (i, x)))
  have hNm : (∫ u : unitInterval, N u) = ∑ i, q i • numerator s τ x i (reply (i, x)) :=
    gibbs_draw_integral ι τ v (fun i => numerator s τ x i (reply (i, x)))
  have he (seed : StepSeed) : OracleTemplate.ComponentEnvelope.Program.eval reply
      (seededEstimatorPlan s τ x seed) = base s τ x + R (seed.1, seed.2.2) • N seed.2.1 := by
    simp only [seededEstimatorPlan, sampledEstimatorPlan, AffineSoftmaxExecution.estimatorPlan_eval,
      estimate, List.map_ofFn]
    rfl
  simp_rw [he]
  rw [step_correction_mean R N (base s τ x) hRi hNi, hRm, hNm, one_div]
  exact gibbs_correction_mean τ v w (fun i => (reply (i, x)).2) s.field


lemma variance_of_bounded_correction {Ω : Type*} [MeasurableSpace Ω]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ProbabilityMeasure Ω) (H : Ω → E) (b target : E) {V : ℝ}
    (hH : Measurable H) (hbound : ∀ ω, ‖H ω - b‖ ^ 2 ≤ V)
    (hmean : (∫ ω, H ω ∂(μ : Measure Ω)) = target) :
    Integrable H (μ : Measure Ω) ∧
      Integrable (fun ω => ‖H ω - target‖ ^ 2) (μ : Measure Ω) ∧
      (∫ ω, ‖H ω - target‖ ^ 2 ∂(μ : Measure Ω)) ≤ V := by
  let X := fun ω => H ω - b
  have hm : Measurable X := hH.sub measurable_const
  have hXi : Integrable X (μ : Measure Ω) := by
    apply (integrable_const (V + 1)).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    have hh := hbound ω
    change ‖H ω - b‖ ≤ V + 1
    nlinarith [sq_nonneg (‖H ω - b‖ - 1 / 2)]
  have hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) (μ : Measure Ω) := by
    apply (integrable_const V).mono' (hm.norm.pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound ω
  have hHi : Integrable H (μ : Measure Ω) := by
    apply (hXi.add (integrable_const b)).congr
    exact Filter.Eventually.of_forall (fun ω => sub_add_cancel (H ω) b)
  have htarget : Integrable (fun ω => ‖H ω - target‖ ^ 2) (μ : Measure Ω) := by
    have hLp : MemLp X 2 (μ : Measure Ω) :=
      (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2 hX2
    have hsum := hLp.add (memLp_const (b - target))
    have heq : (fun ω => X ω + (b - target)) = (fun ω => H ω - target) := by
      funext ω
      dsimp [X]
      abel
    change MemLp (fun ω => X ω + (b - target)) 2 (μ : Measure Ω) at hsum
    rw [heq] at hsum
    exact (memLp_two_iff_integrable_sq_norm (hH.sub measurable_const).aestronglyMeasurable).1 hsum
  refine ⟨hHi, htarget, ?_⟩
  have hXm : (∫ ω, X ω ∂(μ : Measure Ω)) = target - b := by
    rw [show X = (fun ω => H ω - b) from rfl, integral_sub hHi (integrable_const b), hmean]
    simp
  have hh := centered_second_moment μ X hXi hX2
  rw [hXm] at hh
  have he (ω : Ω) : X ω - (target - b) = H ω - target := by dsimp [X]; abel
  simp_rw [he] at hh
  apply hh.trans
  have hi := integral_mono hX2 (integrable_const V) hbound
  simpa using hi


lemma truthful_numerator_sq_le [Nonempty ι] [CompleteSpace E]
    {C : Set E} (f : ι → E → ℝ) (g : ι → E → E) (s : Snapshot ι E)
    {L G r τ : ℝ} (hL : 0 ≤ L) (hG : 0 ≤ G) (hr : 0 ≤ r) (hτ : 0 < τ)
    (hcap : L * r ^ 2 ≤ τ) (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i z, z ∈ C → HasGradientAt (f i) (g i z) z)
    (hlip : ∀ i z x, z ∈ C → x ∈ C → ‖g i z - g i x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ C → ‖g i z‖ ≤ G)
    (hvalue : ∀ i, s.value i = f i s.anchor) (hfield : ∀ i, s.field i = g i s.anchor)
    (hz : s.anchor ∈ C) {x : E} (hx : x ∈ C) (hd : ‖x - s.anchor‖ ≤ r) (i : ι) :
    ‖numerator s τ x i (f i x, g i x)‖ ^ 2 ≤
      8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2) := by
  let c := (f i x - affine s i x) / τ
  have ha : affine s i x = f i s.anchor + ⟪g i s.anchor, x - s.anchor⟫ := by
    simp only [affine, hvalue, hfield]
  have hres := SmoothFiniteMaximumGeometry.affine_residual_bounds (hc i) (hg i) (fun z hz x hx => hlip i z x hz hx) hz hx
  rw [← ha] at hres
  have hcs := SmoothFiniteMaximumGeometry.residual_exponent_bounds
    (hc i) (hg i) (fun z hz x hx => hlip i z x hz hx) hL hr hτ hcap hz hx hd
  rw [← ha] at hcs
  have hd2 : ‖x - s.anchor‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (x - s.anchor)]
  have hcu : c ≤ L * r ^ 2 / (2 * τ) := by
    calc
      c ≤ (L / 2 * r ^ 2) / τ := div_le_div_of_nonneg_right
        (hres.2.trans (mul_le_mul_of_nonneg_left hd2 (by positivity))) hτ.le
      _ = _ := by ring
  have hexp := exp_small_residual hcs.1 hcs.2
  have hb : ‖base s τ x‖ ≤ G := base_norm_le s τ x (fun j => by rw [hfield]; exact hbound j _ hz)
  have hga : ‖g i x - s.field i‖ ≤ L * r := by
    rw [hfield]
    exact (hlip i x s.anchor hx hz).trans (mul_le_mul_of_nonneg_left hd hL)
  have hab : ‖s.field i - base s τ x‖ ≤ 2 * G := by
    have hh := norm_sub_le (s.field i) (base s τ x)
    have ha' : ‖s.field i‖ ≤ G := by rw [hfield]; exact hbound i _ hz
    linarith
  have hcorr := correction_sq_le hexp.1 hexp.2.1
    (show Real.exp c - 1 ≤ 2 * (L * r ^ 2 / (2 * τ)) by linarith [hexp.2.2])
    (mul_nonneg hL hr) hG hga hab
  change ‖correction (Real.exp c) (g i x) (s.field i) (base s τ x)‖ ^ 2 ≤ _
  apply hcorr.trans_eq
  field_simp
  ring


lemma seeded_estimator_variance [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι] (s : Snapshot ι E) (τ : ℝ) (x : E)
    (reply : ι × E → ℝ × E) {V : ℝ}
    (hweights : ∀ i, 1 ≤ Real.exp (((reply (i, x)).1 - affine s i x) / τ) ∧
      Real.exp (((reply (i, x)).1 - affine s i x) / τ) ≤ 2)
    (hN2 : ∀ i, ‖numerator s τ x i (reply (i, x))‖ ^ 2 ≤ V) :
    Integrable (fun seed => OracleTemplate.ComponentEnvelope.Program.eval reply
      (seededEstimatorPlan s τ x seed)) (stepLaw : Measure StepSeed) ∧
    Integrable (fun seed => ‖OracleTemplate.ComponentEnvelope.Program.eval reply
      (seededEstimatorPlan s τ x seed) -
      (∑ i, gibbsWeight τ (fun j => (reply (j, x)).1) i • (reply (i, x)).2)‖ ^ 2)
      (stepLaw : Measure StepSeed) ∧
    (∫ seed : StepSeed, ‖OracleTemplate.ComponentEnvelope.Program.eval reply
      (seededEstimatorPlan s τ x seed) -
      (∑ i, gibbsWeight τ (fun j => (reply (j, x)).1) i • (reply (i, x)).2)‖ ^ 2
      ∂(stepLaw : Measure StepSeed)) ≤ V := by
  let v := fun i => affine s i x
  let d := LongTails.Algorithms.FiniteCategoricalSampler.draw ι (gibbsWeights τ v)
  let a := fun i => Real.exp (((reply (i, x)).1 - affine s i x) / τ)
  let N := fun u : unitInterval => numerator s τ x (d u) (reply (d u, x))
  let R := fun z : ℕ × Rows => reciprocal (List.ofFn (fun j => a (d (z.2 z.1 j))))
  let H := fun seed : StepSeed => OracleTemplate.ComponentEnvelope.Program.eval reply
    (seededEstimatorPlan s τ x seed)
  have hd : Measurable d := (categorical_draw_measurable ι).comp
    (measurable_const.prodMk measurable_id)
  have ha : Measurable (fun u : unitInterval => a (d u)) := (measurable_of_finite a).comp hd
  have hNm : Measurable N := (measurable_of_finite (fun i => numerator s τ x i (reply (i, x)))).comp hd
  have hRm : Measurable R := selected_row_measurable _ (reciprocal_row_measurable _ ha)
  have he (seed : StepSeed) : H seed = base s τ x + R (seed.1, seed.2.2) • N seed.2.1 := by
    simp only [H, seededEstimatorPlan, sampledEstimatorPlan, AffineSoftmaxExecution.estimatorPlan_eval,
      estimate, List.map_ofFn]
    rfl
  have hHm : Measurable H := by
    simp_rw [show H = (fun seed : StepSeed => base s τ x + R (seed.1, seed.2.2) • N seed.2.1) from funext he]
    exact measurable_const.add ((hRm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).smul
      (hNm.comp (measurable_fst.comp measurable_snd)))
  apply variance_of_bounded_correction stepLaw H (base s τ x) _ hHm _
    (seeded_estimator_mean s τ x reply hweights)
  intro seed
  rw [he, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hb : 0 ≤ R (seed.1, seed.2.2) ∧ R (seed.1, seed.2.2) ≤ 1 := by
    apply reciprocal_bounds
    intro b hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    exact hweights _
  rw [abs_of_nonneg hb.1, mul_pow]
  have hs : R (seed.1, seed.2.2) ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
  calc
    _ ≤ 1 * ‖N seed.2.1‖ ^ 2 := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ ≤ V := by simpa only [one_mul] using hN2 (d seed.2.1)

end LongTails.Proofs.AffineSoftmaxMoments
