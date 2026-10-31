import LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian
import LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift
import LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution

namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronProbability
open Classical MeasureTheory ProbabilityTheory
open LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian
lemma batch_zero_output_measure (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hσ : P.noiseScale ≠ 0) (t : ℕ) :
    (P.noise.law : Measure P.noise.Ω)
      {ω | (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point.ofLp.2 = 0} = 0 := by
  let w := fun ω => (trajectory P data η ω ((P.count : ℕ) * t)).point
  let a : Weights P.dimension → ℝ := fun z =>
    (z + (η / (P.count : ℝ)) • (∑ i : Fin P.count,
      if (answer (data i) z).margin ≤ 0 then (answer (data i) z).direction else 0)).ofLp.2
  have ha : Measurable a := by
    have hsum := Finset.measurable_sum Finset.univ (fun i _ => measurable_wrong_direction P data i)
    have hc : Measurable (fun z : Weights P.dimension => z.ofLp.2) := by fun_prop
    exact hc.comp (measurable_id.add (hsum.const_smul (η / (P.count : ℝ))))
  let L : StrongDual ℝ (Weights P.dimension) := WithLp.sndL ..
  have hL : L ≠ 0 := by
    intro he
    have hh := congrArg (fun f : StrongDual ℝ (Weights P.dimension) => f (WithLp.toLp 2 (0, 1))) he
    change (1 : ℝ) = 0 at hh
    norm_num at hh
  have hn := independent_gaussian_affine_zero (P.noise.law : Measure P.noise.Ω) w
    (P.noise.sample t) (measurable_batch_point P data η h.measurable t) (h.measurable t)
    (independent_batch_next P data η t h.measurable h.independent) (h.marginal t)
    a ha L hL P.noiseScale hσ
  apply measure_mono_null _ hn
  intro ω hzero
  change (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point.ofLp.2 = 0 at hzero
  rw [batch_recurrence] at hzero
  change (if Separates data (w ω) then w ω else _).ofLp.2 = 0 at hzero
  split_ifs at hzero with hs
  · have hh := hs 0
    change 0 < (w ω).ofLp.2 * inner ℝ (data 0) (w ω).ofLp.1 at hh
    rw [hzero, zero_mul] at hh
    exact (lt_irrefl 0 hh).elim
  · exact hzero
lemma batch_nonzero_output_ae (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hσ : P.noiseScale ≠ 0) :
    ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω), ∀ t : ℕ,
      (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point.ofLp.2 ≠ 0 := by
  rw [ae_all_iff]
  intro t
  rw [ae_iff]
  simpa only [not_not] using batch_zero_output_measure P data η h hσ t
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry

lemma integrable_batch_potential (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16) (hR : ∀ i, ‖data i‖ ≤ P.radius) (t : ℕ) :
    Integrable (fun ω => potential data η
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2)
      (P.noise.law : Measure P.noise.Ω) :=
  integrable_potential P data η _
    (memLp_batch_point P data η h.measurable (memLp_noise_sample P h) t) hη hsmall hR

lemma stopped_drift_sum (Q A S : ℕ → ℝ) (c : ℝ)
    (h : ∀ t, Q (t + 1) + A (t + 1) + c * S t ≤ Q t) (n : ℕ) :
    Q n + (∑ t ∈ Finset.range n, A (t + 1)) + c * (∑ t ∈ Finset.range n, S t) ≤ Q 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith [h n]
lemma stopped_drift_tail (Q A S : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hQ : ∀ n, 0 ≤ Q n) (hA : ∀ n, 0 ≤ A n)
    (hS : Antitone S) (h : ∀ t, Q (t + 1) + A (t + 1) + c * S t ≤ Q t) (n : ℕ) :
    c * n * S n ≤ Q 0 := by
  have hs : (n : ℝ) * S n ≤ ∑ t ∈ Finset.range n, S t := by
    calc
      _ = ∑ _t ∈ Finset.range n, S n := by simp
      _ ≤ _ := Finset.sum_le_sum fun t ht => hS (Finset.mem_range.mp ht).le
  have hh := stopped_drift_sum Q A S c h n
  have ha := Finset.sum_nonneg (s := Finset.range n) (fun t _ => hA (t + 1))
  have hcS := mul_le_mul_of_nonneg_left hs hc
  nlinarith [hQ n]

open LongTails.Proofs.NoisyBatchQuadraticPerceptronDrift
open scoped RealInnerProductSpace

def Retained {P : Public} (data : Data P) (η : ℝ) (w : Weights P.dimension) : Prop :=
  ¬Separates data w ∧ w.ofLp.2 ≠ 0 ∧
    48 * P.noiseScale ^ 2 * (P.dimension + 1) <
      η ^ 2 * (positive data w.ofLp.1 * negative data w.ofLp.1 + P.radius ^ 2 * w.ofLp.2 ^ 2) ∧
    ¬Escape data η w.ofLp.1 w.ofLp.2 ∧
    ¬Escape data η (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2)
      (w.ofLp.2 + η * inner ℝ (selected data w.ofLp.1 w.ofLp.2) w.ofLp.1)

lemma retained_kernel_drift (P : Public) (data : Data P) (η : ℝ) (t : ℕ)
    (x : Fin t → Weights P.dimension) (hη : 0 < η)
    (hsmall : η * P.radius ≤ 1 / 16) (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hr : Retained data η (pastPoint P data η t x)) :
    (∫ z : Weights P.dimension,
      potential data η (pastPoint P data η (t + 1) (Fin.snoc x z)).ofLp.1
        (pastPoint P data η (t + 1) (Fin.snoc x z)).ofLp.2 ∂stdGaussian (Weights P.dimension)) ≤
      potential data η (pastPoint P data η t x).ofLp.1 (pastPoint P data η t x).ofLp.2 -
        6 * P.noiseScale ^ 2 * (P.dimension + 1) := by
  rcases hr with ⟨hs, hv, hgood, hcur, hnext⟩
  simp_rw [pastPoint_snoc, ite_eq_right hs, deterministic_proposal]
  have h := gaussian_step_drift P data η P.noiseScale
    (pastPoint P data η t x).ofLp.1 (pastPoint P data η t x).ofLp.2 hv hη hsmall hk hcur hnext hR
  dsimp only at h
  linarith
lemma measurableSet_escape (P : Public) (data : Data P) (η : ℝ) :
    MeasurableSet {w : Weights P.dimension | Escape data η w.ofLp.1 w.ofLp.2} := by
  have hp : Measurable (fun w : Weights P.dimension => positive data w.ofLp.1) := by
    unfold positive
    fun_prop
  have hq : Measurable (fun w : Weights P.dimension => negative data w.ofLp.1) := by
    unfold negative
    fun_prop
  have hv : Measurable (fun w : Weights P.dimension => w.ofLp.2) := by fun_prop
  exact ((measurableSet_lt measurable_const hv).inter
    (measurableSet_le hq (hv.const_mul (4 * η * P.radius ^ 2)))).union
    ((measurableSet_lt hv measurable_const).inter
      (measurableSet_le hp (hv.neg.const_mul (4 * η * P.radius ^ 2))))

lemma measurableSet_retained (P : Public) (data : Data P) (η : ℝ) :
    MeasurableSet {w : Weights P.dimension | Retained data η w} := by
  have hp : Measurable (fun w : Weights P.dimension => positive data w.ofLp.1) := by
    unfold positive
    fun_prop
  have hq : Measurable (fun w : Weights P.dimension => negative data w.ofLp.1) := by
    unfold negative
    fun_prop
  have hv : Measurable (fun w : Weights P.dimension => w.ofLp.2) := by fun_prop
  have hg : Measurable (fun w : Weights P.dimension =>
      η ^ 2 * (positive data w.ofLp.1 * negative data w.ofLp.1 + P.radius ^ 2 * w.ofLp.2 ^ 2)) :=
    ((hp.mul hq).add ((hv.pow_const 2).const_mul (P.radius ^ 2))).const_mul (η ^ 2)
  let F := fun w : Weights P.dimension => WithLp.toLp 2
    (w.ofLp.1 + (η * w.ofLp.2) • selected data w.ofLp.1 w.ofLp.2,
      w.ofLp.2 + η * inner ℝ (selected data w.ofLp.1 w.ofLp.2) w.ofLp.1)
  have hF : Measurable F := by
    have he : F = fun w => w + (η / (P.count : ℝ)) • (∑ i : Fin P.count,
        if (answer (data i) w).margin ≤ 0 then (answer (data i) w).direction else 0) :=
      funext fun w => (deterministic_proposal P data η w).symm
    rw [he]
    exact measurable_id.add ((Finset.measurable_sum Finset.univ
      (fun i _ => measurable_wrong_direction P data i)).const_smul (η / (P.count : ℝ)))
  exact (measurableSet_separates P data).compl.inter
    ((measurableSet_eq_fun hv measurable_const).compl.inter
      ((measurableSet_lt measurable_const hg).inter
        ((measurableSet_escape P data η).compl.inter
          (((measurableSet_escape P data η).preimage hF).compl))))

lemma integral_indicator_sub_const {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Set Ω) (hS : MeasurableSet S)
    (f : Ω → ℝ) (hf : Integrable f μ) (c : ℝ) :
    (∫ ω, S.indicator (fun ω => f ω - c) ω ∂μ) =
      (∫ ω, S.indicator f ω ∂μ) - c * μ.real S := by
  rw [integral_indicator hS, integral_sub hf.restrict (integrable_const c),
    ← integral_indicator hS, setIntegral_const]
  simp [mul_comm]

lemma tested_drift (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (t : ℕ) (A : Set (Fin t → Weights P.dimension)) (hA : MeasurableSet A)
    (hret : ∀ x ∈ A, Retained data η (pastPoint P data η t x)) :
    let S := {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}
    (∫ ω, S.indicator (fun ω => potential data η
      (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point.ofLp.1
      (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point.ofLp.2) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ≤
    (∫ ω, S.indicator (fun ω => potential data η
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2) ω
      ∂(P.noise.law : Measure P.noise.Ω)) -
        6 * P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real S := by
  dsimp only
  let V := fun w : Weights P.dimension => potential data η w.ofLp.1 w.ofLp.2
  let H := fun z : (Fin t → Weights P.dimension) × Weights P.dimension =>
    if z.1 ∈ A then V (pastPoint P data η (t + 1) (Fin.snoc z.1 z.2)) else 0
  let B := fun x : Fin t → Weights P.dimension =>
    if x ∈ A then V (pastPoint P data η t x) - 6 * P.noiseScale ^ 2 * (P.dimension + 1) else 0
  have hV : Measurable V := (continuous_potential P data η).measurable
  have hH : Measurable H := Measurable.ite (hA.preimage measurable_fst)
    (hV.comp ((measurable_pastPoint P data η (t + 1)).comp (measurable_snoc t))) measurable_const
  have hB : Measurable B := Measurable.ite hA
    ((hV.comp (measurable_pastPoint P data η t)).sub_const _) measurable_const
  have hS : MeasurableSet {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A} :=
    hA.preimage (Measurable.of_eval fun j => h.measurable j)
  have heH : (fun ω => H ((fun j : Fin t => P.noise.sample j ω), P.noise.sample t ω)) =
      {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}.indicator
        (fun ω => V (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point) := by
    funext ω
    dsimp only [H]
    rw [sample_snoc, ← batch_point_factor]
    rfl
  have heB : (fun ω => B (fun j : Fin t => P.noise.sample j ω)) =
      {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}.indicator
        (fun ω => V (trajectory P data η ω ((P.count : ℕ) * t)).point -
          6 * P.noiseScale ^ 2 * (P.dimension + 1)) := by
    funext ω
    dsimp only [B]
    rw [← batch_point_factor]
    rfl
  have hHi : Integrable (fun ω => H ((fun j : Fin t => P.noise.sample j ω), P.noise.sample t ω))
      (P.noise.law : Measure P.noise.Ω) := by
    rw [heH]
    exact (integrable_batch_potential P data η h hη.le hsmall hR (t + 1)).indicator hS
  have hBi : Integrable (fun ω => B (fun j : Fin t => P.noise.sample j ω))
      (P.noise.law : Measure P.noise.Ω) := by
    rw [heB]
    exact ((integrable_batch_potential P data η h hη.le hsmall hR t).sub (integrable_const _)).indicator hS
  have hb (x : Fin t → Weights P.dimension) :
      (∫ z, H (x, z) ∂stdGaussian (Weights P.dimension)) ≤ B x := by
    by_cases hx : x ∈ A
    · simp only [H, B, hx, ite_eq_left]
      exact retained_kernel_drift P data η t x hη hsmall hk hR (hret x hx)
    · simp [H, B, hx]
  have hd := integral_past_next_le (P.noise.law : Measure P.noise.Ω)
    (stdGaussian (Weights P.dimension)) P.noise.sample h.measurable h.independent t (h.marginal t)
    H hH hHi B hB hBi hb
  rw [heH, heB] at hd
  rw [integral_indicator_sub_const (P.noise.law : Measure P.noise.Ω) _ hS _
    (integrable_batch_potential P data η h hη.le hsmall hR t)] at hd
  exact hd
def survivalEvent (P : Public) (data : Data P) (η : ℝ) (r t : ℕ) : Set P.noise.Ω :=
  {ω | ∀ k, r ≤ k → k ≤ t → Retained data η (trajectory P data η ω ((P.count : ℕ) * k)).point}

def survivalHistory (P : Public) (data : Data P) (η : ℝ) (r t : ℕ) :
    Set (Fin t → Weights P.dimension) :=
  {x | ∀ k : Fin (t + 1), r ≤ k.val → Retained data η
    (pastPoint P data η k.val (fun j => x (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)))}

lemma measurableSet_survivalHistory (P : Public) (data : Data P) (η : ℝ) (r t : ℕ) :
    MeasurableSet (survivalHistory P data η r t) := by
  have he : survivalHistory P data η r t = ⋂ k : Fin (t + 1),
      {x | r ≤ k.val → Retained data η
        (pastPoint P data η k.val (fun j => x (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)))} := by
    ext x
    simp [survivalHistory]
  rw [he]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : r ≤ k.val
  · simp only [hk, true_implies]
    apply (measurableSet_retained P data η).preimage
    exact (measurable_pastPoint P data η k.val).comp
      (Measurable.of_eval fun j => measurable_pi_apply _)
  · simp [hk]

lemma survivalEvent_factor (P : Public) (data : Data P) (η : ℝ) (r t : ℕ) :
    {ω | (fun j : Fin t => P.noise.sample j ω) ∈ survivalHistory P data η r t} =
      survivalEvent P data η r t := by
  ext ω
  constructor
  · intro h k hr hk
    have hh := h ⟨k, Nat.lt_succ_of_le hk⟩ hr
    simp only [Fin.val_castLE] at hh
    rw [batch_point_factor]
    exact hh
  · intro h k hr
    have hh := h k.val hr (Nat.le_of_lt_succ k.isLt)
    simpa only [batch_point_factor, Fin.val_castLE] using hh

lemma measurableSet_survivalEvent (P : Public) (data : Data P) (η : ℝ) (r t : ℕ)
    (hξ : ∀ j, Measurable (P.noise.sample j)) :
    MeasurableSet (survivalEvent P data η r t) := by
  rw [← survivalEvent_factor]
  exact (measurableSet_survivalHistory P data η r t).preimage
    (Measurable.of_eval fun j => hξ j)

lemma survivalHistory_retained (P : Public) (data : Data P) (η : ℝ) (r t : ℕ)
    (hrt : r ≤ t) (x : Fin t → Weights P.dimension)
    (hx : x ∈ survivalHistory P data η r t) : Retained data η (pastPoint P data η t x) := by
  have h := hx (Fin.last t) hrt
  simpa using h

lemma survivalEvent_antitone (P : Public) (data : Data P) (η : ℝ) (r : ℕ) :
    Antitone (survivalEvent P data η r) := by
  intro s t hst ω ht k hr hk
  exact ht k hr (hk.trans hst)
lemma survival_tested_drift (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r t : ℕ) (hrt : r ≤ t) :
    (∫ ω, (survivalEvent P data η r t).indicator (fun ω => potential data η
      (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point.ofLp.1
      (trajectory P data η ω ((P.count : ℕ) * (t + 1))).point.ofLp.2) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ≤
    (∫ ω, (survivalEvent P data η r t).indicator (fun ω => potential data η
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2) ω
      ∂(P.noise.law : Measure P.noise.Ω)) -
        6 * P.noiseScale ^ 2 * (P.dimension + 1) *
          (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r t) := by
  have hd := tested_drift P data η h hη hsmall hk hR t (survivalHistory P data η r t)
    (measurableSet_survivalHistory P data η r t) (survivalHistory_retained P data η r t hrt)
  dsimp only at hd
  rw [survivalEvent_factor] at hd
  exact hd
lemma integral_indicator_partition {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S T : Set Ω) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hsub : T ⊆ S) (f : Ω → ℝ) (hf : Integrable f μ) :
    (∫ ω, S.indicator f ω ∂μ) = (∫ ω, T.indicator f ω ∂μ) +
      ∫ ω, (S \ T).indicator f ω ∂μ := by
  rw [← integral_add (hf.indicator hT) (hf.indicator (hS.diff hT))]
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases ht : ω ∈ T
  · have hs := hsub ht
    simp [Set.indicator, ht, hs]
  · by_cases hs : ω ∈ S <;> simp [Set.indicator, ht, hs]

noncomputable def batchPotential (P : Public) (data : Data P) (η : ℝ) (t : ℕ)
    (ω : P.noise.Ω) : ℝ := potential data η
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2

lemma survival_drift_split (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r t : ℕ) (hrt : r ≤ t) :
    (∫ ω, (survivalEvent P data η r (t + 1)).indicator (batchPotential P data η (t + 1)) ω
      ∂(P.noise.law : Measure P.noise.Ω)) +
      (∫ ω, (survivalEvent P data η r t \ survivalEvent P data η r (t + 1)).indicator
        (batchPotential P data η (t + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) +
      6 * P.noiseScale ^ 2 * (P.dimension + 1) *
        (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r t) ≤
    ∫ ω, (survivalEvent P data η r t).indicator (batchPotential P data η t) ω
      ∂(P.noise.law : Measure P.noise.Ω) := by
  have hd := survival_tested_drift P data η h hη hsmall hk hR r t hrt
  change (∫ ω, (survivalEvent P data η r t).indicator (batchPotential P data η (t + 1)) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ≤
    (∫ ω, (survivalEvent P data η r t).indicator (batchPotential P data η t) ω
      ∂(P.noise.law : Measure P.noise.Ω)) - _ at hd
  rw [integral_indicator_partition (P.noise.law : Measure P.noise.Ω)
    (survivalEvent P data η r t) (survivalEvent P data η r (t + 1))
    (measurableSet_survivalEvent P data η r t h.measurable)
    (measurableSet_survivalEvent P data η r (t + 1) h.measurable)
    (survivalEvent_antitone P data η r (Nat.le_succ t)) (batchPotential P data η (t + 1))
    (integrable_batch_potential P data η h hη.le hsmall hR (t + 1))] at hd
  linarith
lemma batchPotential_nonneg (P : Public) (data : Data P) (η : ℝ)
    (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (t : ℕ) (ω : P.noise.Ω) : 0 ≤ batchPotential P data η t ω := by
  have h := (potential_bounds P data η
    (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1
    (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2 hη hsmall hR).1
  unfold batchPotential
  nlinarith [sq_nonneg ‖(trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.1‖,
    sq_nonneg ((trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2)]
lemma survival_stopped_sum (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r n : ℕ) :
    (∫ ω, (survivalEvent P data η r (r + n)).indicator (batchPotential P data η (r + n)) ω
      ∂(P.noise.law : Measure P.noise.Ω)) +
      (∑ k ∈ Finset.range n, ∫ ω,
        (survivalEvent P data η r (r + k) \ survivalEvent P data η r (r + k + 1)).indicator
          (batchPotential P data η (r + k + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) +
      6 * P.noiseScale ^ 2 * (P.dimension + 1) *
        (∑ k ∈ Finset.range n, (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + k))) ≤
    ∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    have hi := integrable_batch_potential P data η h hη.le hsmall hR r
    apply integral_mono (hi.indicator (measurableSet_survivalEvent P data η r r h.measurable)) hi
    intro ω
    by_cases hh : ω ∈ survivalEvent P data η r r
    · simp [Set.indicator, hh]
    · rw [Set.indicator_of_notMem hh]
      exact batchPotential_nonneg P data η hη.le hsmall hR r ω
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hd := survival_drift_split P data η h hη hsmall hk hR r (r + n) (Nat.le_add_right r n)
    simp only [Nat.add_assoc] at hd ih ⊢
    linarith
lemma survival_probability_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r n : ℕ) :
    6 * P.noiseScale ^ 2 * (P.dimension + 1) * n *
      (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + n)) ≤
    ∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω) := by
  have hi (t : ℕ) (S : Set P.noise.Ω) :
      0 ≤ ∫ ω, S.indicator (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω) :=
    integral_nonneg fun ω => Set.indicator_nonneg
      (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR t ω) ω
  have hs : (n : ℝ) * (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + n)) ≤
      ∑ k ∈ Finset.range n, (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + k)) := by
    calc
      _ = ∑ _k ∈ Finset.range n,
          (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + n)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun k hk => measureReal_mono
        (survivalEvent_antitone P data η r (Nat.add_le_add_left (Finset.mem_range.mp hk).le r))
  have hc : 0 ≤ 6 * P.noiseScale ^ 2 * (P.dimension + 1) := by positivity
  have hcs := mul_le_mul_of_nonneg_left hs hc
  have hh := survival_stopped_sum P data η h hη hsmall hk hR r n
  have hq := hi (r + n) (survivalEvent P data η r (r + n))
  have ha := Finset.sum_nonneg (s := Finset.range n) (fun k _ => hi (r + k + 1)
    (survivalEvent P data η r (r + k) \ survivalEvent P data η r (r + k + 1)))
  nlinarith
lemma eventually_not_retained_ae (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (r : ℕ) :
    ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω), ∃ t, r ≤ t ∧
      ¬Retained data η (trajectory P data η ω ((P.count : ℕ) * t)).point := by
  let μ : Measure P.noise.Ω := P.noise.law
  let T := {ω | ¬∃ t, r ≤ t ∧ ¬Retained data η (trajectory P data η ω ((P.count : ℕ) * t)).point}
  let c : ℝ := 6 * P.noiseScale ^ 2 * (P.dimension + 1)
  let C : ℝ := ∫ ω, batchPotential P data η r ω ∂μ
  have hc : 0 < c := by dsimp [c]; positivity
  have hsub (n : ℕ) : T ⊆ survivalEvent P data η r (r + n) := by
    intro ω hω k hr _
    by_contra hh
    exact hω ⟨k, hr, hh⟩
  have hz : μ.real T = 0 := by
    apply le_antisymm _ measureReal_nonneg
    by_contra! ha
    obtain ⟨n, hn⟩ := exists_nat_gt (C / (c * μ.real T))
    have hb := survival_probability_bound P data η h hη hsmall hk hR r n
    have hm : μ.real T ≤ μ.real (survivalEvent P data η r (r + n)) := measureReal_mono (hsub n)
    have hmul := mul_le_mul_of_nonneg_left hm (mul_nonneg hc.le (Nat.cast_nonneg n))
    have hlt := (div_lt_iff₀ (mul_pos hc ha)).mp hn
    change c * n * μ.real (survivalEvent P data η r (r + n)) ≤ C at hb
    nlinarith
  rw [ae_iff]
  exact (measureReal_eq_zero_iff).mp hz

lemma survival_stopped_sum_sharp (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r n : ℕ) :
    (∫ ω, (survivalEvent P data η r (r + n)).indicator (batchPotential P data η (r + n)) ω
      ∂(P.noise.law : Measure P.noise.Ω)) +
      (∑ k ∈ Finset.range n, ∫ ω,
        (survivalEvent P data η r (r + k) \ survivalEvent P data η r (r + k + 1)).indicator
          (batchPotential P data η (r + k + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) +
      6 * P.noiseScale ^ 2 * (P.dimension + 1) *
        (∑ k ∈ Finset.range n, (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + k))) ≤
    ∫ ω, (survivalEvent P data η r r).indicator (batchPotential P data η r) ω
      ∂(P.noise.law : Measure P.noise.Ω) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hd := survival_drift_split P data η h hη hsmall hk hR r (r + n) (Nat.le_add_right r n)
    simp only [Nat.add_assoc] at hd ih ⊢
    linarith

lemma survival_cost_summable (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r : ℕ) :
    let cost := fun k => (∫ ω,
      (survivalEvent P data η r (r + k) \ survivalEvent P data η r (r + k + 1)).indicator
        (batchPotential P data η (r + k + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) +
      6 * P.noiseScale ^ 2 * (P.dimension + 1) *
        (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + k))
    Summable cost ∧ (∑' k, cost k) ≤
      ∫ ω, (survivalEvent P data η r r).indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω) := by
  dsimp only
  let cost := fun k => (∫ ω,
      (survivalEvent P data η r (r + k) \ survivalEvent P data η r (r + k + 1)).indicator
        (batchPotential P data η (r + k + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) +
      6 * P.noiseScale ^ 2 * (P.dimension + 1) *
        (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + k))
  have hnon (k : ℕ) : 0 ≤ cost k := by
    have hi : 0 ≤ ∫ ω,
        (survivalEvent P data η r (r + k) \ survivalEvent P data η r (r + k + 1)).indicator
          (batchPotential P data η (r + k + 1)) ω ∂(P.noise.law : Measure P.noise.Ω) :=
      integral_nonneg fun ω => Set.indicator_nonneg
        (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR (r + k + 1) ω) ω
    dsimp [cost]
    positivity
  have hsum (n : ℕ) : ∑ k ∈ Finset.range n, cost k ≤
      ∫ ω, (survivalEvent P data η r r).indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω) := by
    have hb := survival_stopped_sum_sharp P data η h hη hsmall hk hR r n
    have hi : 0 ≤ ∫ ω, (survivalEvent P data η r (r + n)).indicator
        (batchPotential P data η (r + n)) ω ∂(P.noise.law : Measure P.noise.Ω) :=
      integral_nonneg fun ω => Set.indicator_nonneg
        (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR (r + n) ω) ω
    dsimp [cost]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith
  exact ⟨summable_of_sum_range_le hnon hsum, Real.tsum_le_of_sum_range_le hnon hsum⟩
def exitEvent (P : Public) (data : Data P) (η : ℝ) (r : ℕ) : ℕ → Set P.noise.Ω
  | 0 => (survivalEvent P data η r r)ᶜ
  | k + 1 => survivalEvent P data η r (r + k) \ survivalEvent P data η r (r + k + 1)
lemma measurableSet_exitEvent (P : Public) (data : Data P) (η : ℝ) (r k : ℕ)
    (hm : ∀ j, Measurable (P.noise.sample j)) :
    MeasurableSet (exitEvent P data η r k) := by
  cases k with
  | zero => exact (measurableSet_survivalEvent P data η r r hm).compl
  | succ k =>
    exact (measurableSet_survivalEvent P data η r (r + k) hm).diff
      (measurableSet_survivalEvent P data η r (r + k + 1) hm)
lemma mem_exitEvent_iff (P : Public) (data : Data P) (η : ℝ) (r k : ℕ) (ω : P.noise.Ω) :
    ω ∈ exitEvent P data η r k ↔
      ¬Retained data η (trajectory P data η ω ((P.count : ℕ) * (r + k))).point ∧
      ∀ j < k, Retained data η (trajectory P data η ω ((P.count : ℕ) * (r + j))).point := by
  cases k with
  | zero =>
    simp only [exitEvent, Set.mem_compl_iff, Nat.add_zero, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true, and_true]
    have he : ω ∈ survivalEvent P data η r r ↔
        Retained data η (trajectory P data η ω ((P.count : ℕ) * r)).point := by
      constructor
      · intro hh; exact hh r le_rfl le_rfl
      · intro hh t ht ht'
        have he : t = r := by omega
        simpa [he] using hh
    exact not_congr he
  | succ k =>
    change (ω ∈ survivalEvent P data η r (r + k) ∧
      ω ∉ survivalEvent P data η r (r + k + 1)) ↔ _
    constructor
    · rintro ⟨ha, hb⟩
      constructor
      · intro hx
        apply hb
        intro t ht htk
        by_cases he : t = r + k + 1
        · simpa [he, Nat.add_assoc] using hx
        · exact ha t ht (by omega)
      · intro j hj
        exact ha (r + j) (by omega) (by omega)
    · rintro ⟨ha, hb⟩
      constructor
      · intro t ht htk
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ht
        exact hb j (by omega)
      · intro hx
        exact ha (hx (r + (k + 1)) (by omega) (by omega))
lemma exitEvent_disjoint (P : Public) (data : Data P) (η : ℝ) (r : ℕ) :
    Pairwise (fun i j => Disjoint (exitEvent P data η r i) (exitEvent P data η r j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro ω hi hj
  rw [mem_exitEvent_iff] at hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hi.1 (hj.2 i hlt)
  · exact hj.1 (hi.2 j hgt)
lemma mem_iUnion_exitEvent (P : Public) (data : Data P) (η : ℝ) (r : ℕ) (ω : P.noise.Ω) :
    ω ∈ ⋃ k, exitEvent P data η r k ↔ ∃ t, r ≤ t ∧
      ¬Retained data η (trajectory P data η ω ((P.count : ℕ) * t)).point := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h
    exact ⟨r + k, by omega, ((mem_exitEvent_iff P data η r k ω).mp hk).1⟩
  · rintro ⟨t, ht, hf⟩
    have hex : ∃ k, ¬Retained data η (trajectory P data η ω ((P.count : ℕ) * (r + k))).point := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
      exact ⟨k, hf⟩
    apply Set.mem_iUnion.mpr
    refine ⟨Nat.find hex, (mem_exitEvent_iff P data η r (Nat.find hex) ω).mpr ⟨Nat.find_spec hex, ?_⟩⟩
    intro j hj
    exact not_not.mp (Nat.find_min hex hj)
lemma exit_potential_partial_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r n : ℕ) :
    (∫ ω, (exitEvent P data η r 0).indicator (batchPotential P data η r) ω
      ∂(P.noise.law : Measure P.noise.Ω)) +
    (∑ k ∈ Finset.range n, ∫ ω, (exitEvent P data η r (k + 1)).indicator
      (batchPotential P data η (r + k + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) ≤
      ∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω) := by
  have hb := survival_stopped_sum_sharp P data η h hη hsmall hk hR r n
  have hq : 0 ≤ ∫ ω, (survivalEvent P data η r (r + n)).indicator
      (batchPotential P data η (r + n)) ω ∂(P.noise.law : Measure P.noise.Ω) :=
    integral_nonneg fun ω => Set.indicator_nonneg
      (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR (r + n) ω) ω
  have hc : 0 ≤ 6 * P.noiseScale ^ 2 * (P.dimension + 1) *
      (∑ k ∈ Finset.range n, (P.noise.law : Measure P.noise.Ω).real
        (survivalEvent P data η r (r + k))) := by positivity
  have hi := integral_indicator_partition (P.noise.law : Measure P.noise.Ω) Set.univ
    (survivalEvent P data η r r) MeasurableSet.univ
    (measurableSet_survivalEvent P data η r r h.measurable)
    (Set.subset_univ _) (batchPotential P data η r)
    (integrable_batch_potential P data η h hη.le hsmall hR r)
  simp only [Set.indicator_univ, Set.sdiff_eq, Set.univ_inter] at hi
  dsimp only [exitEvent]
  linarith
lemma exit_potential_summable (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r : ℕ) :
    let flux := fun k => ∫ ω, (exitEvent P data η r k).indicator
      (batchPotential P data η (r + k)) ω ∂(P.noise.law : Measure P.noise.Ω)
    Summable flux ∧ (∑' k, flux k) ≤
      ∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω) := by
  dsimp only
  let flux := fun k => ∫ ω, (exitEvent P data η r k).indicator
    (batchPotential P data η (r + k)) ω ∂(P.noise.law : Measure P.noise.Ω)
  have hn (k : ℕ) : 0 ≤ flux k :=
    integral_nonneg fun ω => Set.indicator_nonneg
      (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR (r + k) ω) ω
  have hb (n : ℕ) : ∑ k ∈ Finset.range n, flux k ≤
      ∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω) := by
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact integral_nonneg (batchPotential_nonneg P data η hη.le hsmall hR r)
    | succ n =>
      rw [Finset.sum_range_succ']
      have he := exit_potential_partial_bound P data η h hη hsmall hk hR r n
      dsimp only [flux]
      simpa only [Nat.add_assoc, Nat.add_zero, add_comm] using he
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

lemma integrable_disjoint_partition {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : ℕ → Set Ω) (f : Ω → ℝ) (g : ℕ → Ω → ℝ)
    (hm : ∀ k, MeasurableSet (S k)) (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (he : ∀ k, Set.EqOn f (g k) (S k)) (hoff : ∀ ω ∉ ⋃ k, S k, f ω = 0)
    (hi : ∀ k, Integrable (g k) μ) (hn : ∀ k ω, 0 ≤ g k ω)
    (hs : Summable (fun k => ∫ ω, (S k).indicator (g k) ω ∂μ)) :
    Integrable f μ ∧ (∫ ω, f ω ∂μ) = ∑' k, ∫ ω, (S k).indicator (g k) ω ∂μ := by
  have hOn (k : ℕ) : IntegrableOn f (S k) μ :=
    (integrableOn_congr_fun (he k) (hm k)).mpr (hi k).integrableOn
  have heNorm (k : ℕ) : (∫ ω in S k, ‖f ω‖ ∂μ) = ∫ ω, (S k).indicator (g k) ω ∂μ := by
    rw [integral_indicator (hm k)]
    apply setIntegral_congr_fun (hm k)
    intro ω hω
    change ‖f ω‖ = _
    rw [he k hω, Real.norm_of_nonneg (hn k ω)]
  have hsum : Summable (fun k => ∫ ω in S k, ‖f ω‖ ∂μ) := by
    simp_rw [heNorm]
    exact hs
  have hu := integrableOn_iUnion_of_summable_integral_norm hOn hsum
  have hU : MeasurableSet (⋃ k, S k) := MeasurableSet.iUnion hm
  have hid : (⋃ k, S k).indicator f = f := by
    funext ω
    by_cases hω : ω ∈ ⋃ k, S k
    · exact Set.indicator_of_mem hω f
    · rw [Set.indicator_of_notMem hω]
      exact (hoff ω hω).symm
  have hf : Integrable f μ := by simpa only [hid] using hu.integrable_indicator hU
  refine ⟨hf, ?_⟩
  calc
    _ = ∫ ω in ⋃ k, S k, f ω ∂μ := by rw [← integral_indicator hU, hid]
    _ = ∑' k, ∫ ω in S k, f ω ∂μ := integral_iUnion hm hd hu
    _ = _ := tsum_congr fun k => by
      rw [integral_indicator (hm k)]
      exact setIntegral_congr_fun (hm k) (he k)

noncomputable def hittingPotential (P : Public) (data : Data P) (η : ℝ) (r : ℕ) (ω : P.noise.Ω) : ℝ :=
  if h : ∃ k, ω ∈ exitEvent P data η r k then
    batchPotential P data η (r + Nat.find h) ω else 0
lemma hittingPotential_on_exit (P : Public) (data : Data P) (η : ℝ) (r k : ℕ)
    (ω : P.noise.Ω) (hk : ω ∈ exitEvent P data η r k) :
    hittingPotential P data η r ω = batchPotential P data η (r + k) ω := by
  have hex : ∃ j, ω ∈ exitEvent P data η r j := ⟨k, hk⟩
  have he : Nat.find hex = k := by
    by_contra hne
    exact Set.disjoint_left.mp (exitEvent_disjoint P data η r hne) (Nat.find_spec hex) hk
  simp [hittingPotential, hex, he]
lemma hittingPotential_off_union (P : Public) (data : Data P) (η : ℝ) (r : ℕ)
    (ω : P.noise.Ω) (hk : ω ∉ ⋃ k, exitEvent P data η r k) :
    hittingPotential P data η r ω = 0 := by
  have he : ¬∃ k, ω ∈ exitEvent P data η r k := by simpa only [Set.mem_iUnion] using hk
  simp [hittingPotential, he]
lemma hittingPotential_integrable_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r : ℕ) :
    Integrable (hittingPotential P data η r) (P.noise.law : Measure P.noise.Ω) ∧
    (∫ ω, hittingPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω)) ≤
      ∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω) := by
  have hs := exit_potential_summable P data η h hη hsmall hk hR r
  dsimp only at hs
  have hh := integrable_disjoint_partition (P.noise.law : Measure P.noise.Ω)
    (exitEvent P data η r) (hittingPotential P data η r)
    (fun k => batchPotential P data η (r + k))
    (fun k => measurableSet_exitEvent P data η r k h.measurable)
    (exitEvent_disjoint P data η r)
    (fun k ω hω => hittingPotential_on_exit P data η r k ω hω)
    (hittingPotential_off_union P data η r)
    (fun k => integrable_batch_potential P data η h hη.le hsmall hR (r + k))
    (fun k => batchPotential_nonneg P data η hη.le hsmall hR (r + k)) hs.1
  exact ⟨hh.1, hh.2.trans_le hs.2⟩
noncomputable def hittingOffset (P : Public) (data : Data P) (η : ℝ) (r : ℕ) (ω : P.noise.Ω) : ℕ :=
  if h : ∃ k, ω ∈ exitEvent P data η r k then Nat.find h else 0
lemma hittingOffset_on_exit (P : Public) (data : Data P) (η : ℝ) (r k : ℕ)
    (ω : P.noise.Ω) (hk : ω ∈ exitEvent P data η r k) :
    hittingOffset P data η r ω = k := by
  have hex : ∃ j, ω ∈ exitEvent P data η r j := ⟨k, hk⟩
  have he : Nat.find hex = k := by
    by_contra hne
    exact Set.disjoint_left.mp (exitEvent_disjoint P data η r hne) (Nat.find_spec hex) hk
  simp [hittingOffset, hex, he]
lemma hittingOffset_spec_ae (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (r : ℕ) :
    ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω),
      ω ∈ exitEvent P data η r (hittingOffset P data η r ω) ∧
      hittingPotential P data η r ω =
        batchPotential P data η (r + hittingOffset P data η r ω) ω := by
  filter_upwards [eventually_not_retained_ae P data η h hη hsmall hk hR hσ r] with ω hω
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ((mem_iUnion_exitEvent P data η r ω).mpr hω)
  rw [hittingOffset_on_exit P data η r k ω hk]
  exact ⟨hk, hittingPotential_on_exit P data η r k ω hk⟩
lemma actual_hitting_potential_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (r : ℕ) :
    Integrable (fun ω => batchPotential P data η (r + hittingOffset P data η r ω) ω)
      (P.noise.law : Measure P.noise.Ω) ∧
    (∫ ω, batchPotential P data η (r + hittingOffset P data η r ω) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ≤
      ∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω) := by
  have he : hittingPotential P data η r =ᵐ[(P.noise.law : Measure P.noise.Ω)]
      (fun ω => batchPotential P data η (r + hittingOffset P data η r ω) ω) := by
    filter_upwards [hittingOffset_spec_ae P data η h hη hsmall hk hR hσ r] with ω hω
    exact hω.2
  have hh := hittingPotential_integrable_bound P data η h hη hsmall hk hR r
  exact ⟨hh.1.congr he, (integral_congr_ae he).symm.trans_le hh.2⟩
lemma exit_mass_identity (P : Public) (data : Data P) (η : ℝ) (r n : ℕ)
    (hm : ∀ j, Measurable (P.noise.sample j)) :
    (∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) *
      (P.noise.law : Measure P.noise.Ω).real (exitEvent P data η r (k + 1))) +
      n * (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + n)) =
    ∑ k ∈ Finset.range n, (P.noise.law : Measure P.noise.Ω).real
      (survivalEvent P data η r (r + k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (P.noise.law : Measure P.noise.Ω).real (exitEvent P data η r (n + 1)) =
        (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + n)) -
        (P.noise.law : Measure P.noise.Ω).real (survivalEvent P data η r (r + n + 1)) := by
      exact measureReal_sdiff (survivalEvent_antitone P data η r (by omega))
        (measurableSet_survivalEvent P data η r (r + n + 1) hm)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, he]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc] at ih ⊢
    nlinarith
lemma exit_time_partial_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (r n : ℕ) :
    (∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) *
      (P.noise.law : Measure P.noise.Ω).real (exitEvent P data η r (k + 1))) ≤
    (∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω)) /
      (6 * P.noiseScale ^ 2 * (P.dimension + 1)) := by
  have hc : 0 < 6 * P.noiseScale ^ 2 * (P.dimension + 1) := by positivity
  rw [le_div_iff₀ hc]
  have hb := survival_stopped_sum P data η h hη hsmall hk hR r n
  have he := exit_mass_identity P data η r n h.measurable
  have hi (t : ℕ) (S : Set P.noise.Ω) :
      0 ≤ ∫ ω, S.indicator (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω) :=
    integral_nonneg fun ω => Set.indicator_nonneg
      (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR t ω) ω
  have hq := hi (r + n) (survivalEvent P data η r (r + n))
  have ha := Finset.sum_nonneg (s := Finset.range n) (fun k _ => hi (r + k + 1)
    (survivalEvent P data η r (r + k) \ survivalEvent P data η r (r + k + 1)))
  have hn : 0 ≤ (n : ℝ) * (P.noise.law : Measure P.noise.Ω).real
      (survivalEvent P data η r (r + n)) := by positivity
  nlinarith
lemma exit_time_summable (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (r : ℕ) :
    let flux := fun k : ℕ => (k : ℝ) *
      (P.noise.law : Measure P.noise.Ω).real (exitEvent P data η r k)
    Summable flux ∧ (∑' k, flux k) ≤
      (∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω)) /
        (6 * P.noiseScale ^ 2 * (P.dimension + 1)) := by
  dsimp only
  let flux := fun k : ℕ => (k : ℝ) *
    (P.noise.law : Measure P.noise.Ω).real (exitEvent P data η r k)
  have hn (k : ℕ) : 0 ≤ flux k := by dsimp [flux]; positivity
  have hb (n : ℕ) : ∑ k ∈ Finset.range n, flux k ≤
      (∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω)) /
        (6 * P.noiseScale ^ 2 * (P.dimension + 1)) := by
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      apply div_nonneg
      · exact integral_nonneg (batchPotential_nonneg P data η hη.le hsmall hR r)
      · positivity
    | succ n =>
      rw [Finset.sum_range_succ']
      simpa only [flux, Nat.cast_zero, zero_mul, add_zero] using
        exit_time_partial_bound P data η h hη hsmall hk hR hσ r n
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩
lemma hittingOffset_integrable_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (r : ℕ) :
    Integrable (fun ω => (hittingOffset P data η r ω : ℝ)) (P.noise.law : Measure P.noise.Ω) ∧
    (∫ ω, (hittingOffset P data η r ω : ℝ) ∂(P.noise.law : Measure P.noise.Ω)) ≤
      (∫ ω, batchPotential P data η r ω ∂(P.noise.law : Measure P.noise.Ω)) /
        (6 * P.noiseScale ^ 2 * (P.dimension + 1)) := by
  have hs := exit_time_summable P data η h hη hsmall hk hR hσ r
  dsimp only at hs
  have he : (fun k => ∫ ω, (exitEvent P data η r k).indicator (fun _ => (k : ℝ)) ω
      ∂(P.noise.law : Measure P.noise.Ω)) = (fun k : ℕ => (k : ℝ) *
        (P.noise.law : Measure P.noise.Ω).real (exitEvent P data η r k)) := by
    funext k
    rw [integral_indicator (measurableSet_exitEvent P data η r k h.measurable), setIntegral_const]
    simp [mul_comm]
  have hs' : Summable (fun k => ∫ ω, (exitEvent P data η r k).indicator (fun _ => (k : ℝ)) ω
      ∂(P.noise.law : Measure P.noise.Ω)) := by rw [he]; exact hs.1
  have hh := integrable_disjoint_partition (P.noise.law : Measure P.noise.Ω)
    (exitEvent P data η r) (fun ω => (hittingOffset P data η r ω : ℝ))
    (fun k _ => (k : ℝ)) (fun k => measurableSet_exitEvent P data η r k h.measurable)
    (exitEvent_disjoint P data η r)
    (fun k ω hω => by
      change (hittingOffset P data η r ω : ℝ) = (k : ℝ)
      rw [hittingOffset_on_exit P data η r k ω hω])
    (fun ω hω => by
      have hn : ¬∃ k, ω ∈ exitEvent P data η r k := by simpa only [Set.mem_iUnion] using hω
      simp [hittingOffset, hn])
    (fun k => integrable_const (k : ℝ)) (fun k _ => Nat.cast_nonneg k) hs'
  rw [he] at hh
  exact ⟨hh.1, hh.2.trans_le hs.2⟩

lemma weighted_survival_tested_drift (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r t : ℕ) (hrt : r ≤ t) (A : Set (Fin r → Weights P.dimension)) (hA : MeasurableSet A) :
    let S := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A} ∩ survivalEvent P data η r t
    (∫ ω, S.indicator (batchPotential P data η (t + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) ≤
    (∫ ω, S.indicator (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) -
      6 * P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real S := by
  let B : Set (Fin t → Weights P.dimension) :=
    {x | (fun j : Fin r => x (Fin.castLE hrt j)) ∈ A} ∩ survivalHistory P data η r t
  have hm : Measurable (fun x : Fin t → Weights P.dimension => fun j : Fin r => x (Fin.castLE hrt j)) :=
    Measurable.of_eval fun j => measurable_pi_apply (Fin.castLE hrt j)
  have hB : MeasurableSet B :=
    (hA.preimage hm).inter (measurableSet_survivalHistory P data η r t)
  have hb : ∀ x ∈ B, Retained data η (pastPoint P data η t x) := fun x hx =>
    survivalHistory_retained P data η r t hrt x hx.2
  have hd := tested_drift P data η h hη hsmall hk hR t B hB hb
  have he : {ω | (fun j : Fin t => P.noise.sample j ω) ∈ B} =
      {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A} ∩ survivalEvent P data η r t := by
    rw [← survivalEvent_factor P data η r t]
    rfl
  dsimp only at hd ⊢
  rw [he] at hd
  exact hd
lemma weighted_survival_drift_split (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r t : ℕ) (hrt : r ≤ t) (A : Set (Fin r → Weights P.dimension)) (hA : MeasurableSet A) :
    let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
    let S := fun t => F ∩ survivalEvent P data η r t
    (∫ ω, (S (t + 1)).indicator (batchPotential P data η (t + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) +
    (∫ ω, (S t \ S (t + 1)).indicator (batchPotential P data η (t + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) +
      6 * P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real (S t) ≤
    ∫ ω, (S t).indicator (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω) := by
  let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
  let S := fun t => F ∩ survivalEvent P data η r t
  have hF : MeasurableSet F := hA.preimage (Measurable.of_eval fun j => h.measurable j)
  have hS (k : ℕ) : MeasurableSet (S k) := hF.inter (measurableSet_survivalEvent P data η r k h.measurable)
  have hsub : S (t + 1) ⊆ S t := fun _ hx => ⟨hx.1, survivalEvent_antitone P data η r (Nat.le_succ t) hx.2⟩
  have hd := weighted_survival_tested_drift P data η h hη hsmall hk hR r t hrt A hA
  change (∫ ω, (S t).indicator (batchPotential P data η (t + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) ≤
    (∫ ω, (S t).indicator (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) - _ at hd
  rw [integral_indicator_partition (P.noise.law : Measure P.noise.Ω) (S t) (S (t + 1))
    (hS t) (hS (t + 1)) hsub (batchPotential P data η (t + 1))
    (integrable_batch_potential P data η h hη.le hsmall hR (t + 1))] at hd
  change _ + _ + _ ≤ _
  linarith
lemma weighted_survival_stopped_sum (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r n : ℕ) (A : Set (Fin r → Weights P.dimension)) (hA : MeasurableSet A) :
    let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
    let S := fun t => F ∩ survivalEvent P data η r t
    (∫ ω, (S (r + n)).indicator (batchPotential P data η (r + n)) ω ∂(P.noise.law : Measure P.noise.Ω)) +
    (∑ k ∈ Finset.range n, ∫ ω, (S (r + k) \ S (r + k + 1)).indicator
      (batchPotential P data η (r + k + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) +
      6 * P.noiseScale ^ 2 * (P.dimension + 1) *
        (∑ k ∈ Finset.range n, (P.noise.law : Measure P.noise.Ω).real (S (r + k))) ≤
    ∫ ω, (S r).indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω) := by
  dsimp only
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hd := weighted_survival_drift_split P data η h hη hsmall hk hR r (r + n)
      (Nat.le_add_right r n) A hA
    dsimp only at hd
    simp only [Nat.add_assoc] at hd ih ⊢
    linarith
lemma weighted_exit_potential_partial_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r n : ℕ) (A : Set (Fin r → Weights P.dimension)) (hA : MeasurableSet A) :
    let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
    (∫ ω, (F ∩ exitEvent P data η r 0).indicator (batchPotential P data η r) ω
      ∂(P.noise.law : Measure P.noise.Ω)) +
    (∑ k ∈ Finset.range n, ∫ ω, (F ∩ exitEvent P data η r (k + 1)).indicator
      (batchPotential P data η (r + k + 1)) ω ∂(P.noise.law : Measure P.noise.Ω)) ≤
    ∫ ω, F.indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω) := by
  let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
  have hF : MeasurableSet F := hA.preimage (Measurable.of_eval fun j => h.measurable j)
  have hb := weighted_survival_stopped_sum P data η h hη hsmall hk hR r n A hA
  have hq : 0 ≤ ∫ ω, (F ∩ survivalEvent P data η r (r + n)).indicator
      (batchPotential P data η (r + n)) ω ∂(P.noise.law : Measure P.noise.Ω) :=
    integral_nonneg fun ω => Set.indicator_nonneg
      (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR (r + n) ω) ω
  have hc : 0 ≤ 6 * P.noiseScale ^ 2 * (P.dimension + 1) *
      (∑ k ∈ Finset.range n, (P.noise.law : Measure P.noise.Ω).real
        (F ∩ survivalEvent P data η r (r + k))) := by positivity
  have hi := integral_indicator_partition (P.noise.law : Measure P.noise.Ω) F
    (F ∩ survivalEvent P data η r r) hF
    (hF.inter (measurableSet_survivalEvent P data η r r h.measurable))
    Set.inter_subset_left (batchPotential P data η r)
    (integrable_batch_potential P data η h hη.le hsmall hR r)
  have he0 : F \ (F ∩ survivalEvent P data η r r) = F ∩ exitEvent P data η r 0 := by
    ext ω; simp only [exitEvent, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]; tauto
  have he (k : ℕ) : (F ∩ survivalEvent P data η r (r + k)) \
      (F ∩ survivalEvent P data η r (r + k + 1)) = F ∩ exitEvent P data η r (k + 1) := by
    ext ω; simp only [exitEvent, Set.mem_sdiff, Set.mem_inter_iff]; tauto
  dsimp only at hb ⊢
  change _ ≤ _
  dsimp only [F] at he
  simp_rw [he] at hb
  rw [he0] at hi
  linarith
lemma weighted_exit_potential_summable (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (r : ℕ) (A : Set (Fin r → Weights P.dimension)) (hA : MeasurableSet A) :
    let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
    let flux := fun k => ∫ ω, (F ∩ exitEvent P data η r k).indicator
      (batchPotential P data η (r + k)) ω ∂(P.noise.law : Measure P.noise.Ω)
    Summable flux ∧ (∑' k, flux k) ≤
      ∫ ω, F.indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω) := by
  let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
  dsimp only
  let flux := fun k => ∫ ω, (F ∩ exitEvent P data η r k).indicator
    (batchPotential P data η (r + k)) ω ∂(P.noise.law : Measure P.noise.Ω)
  have hn (k : ℕ) : 0 ≤ flux k :=
    integral_nonneg fun ω => Set.indicator_nonneg
      (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR (r + k) ω) ω
  have hb (n : ℕ) : ∑ k ∈ Finset.range n, flux k ≤
      ∫ ω, F.indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω) := by
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact integral_nonneg fun ω => Set.indicator_nonneg
        (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR r ω) ω
    | succ n =>
      rw [Finset.sum_range_succ']
      have he := weighted_exit_potential_partial_bound P data η h hη hsmall hk hR r n A hA
      dsimp only [flux]
      simpa only [Nat.add_assoc, Nat.add_zero, add_comm] using he
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

lemma weighted_exit_mass_identity (P : Public) (data : Data P) (η : ℝ) (r n : ℕ)
    (hm : ∀ j, Measurable (P.noise.sample j)) (F : Set P.noise.Ω) (hF : MeasurableSet F) :
    (∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) *
      (P.noise.law : Measure P.noise.Ω).real (F ∩ exitEvent P data η r (k + 1))) +
      n * (P.noise.law : Measure P.noise.Ω).real (F ∩ survivalEvent P data η r (r + n)) =
    ∑ k ∈ Finset.range n, (P.noise.law : Measure P.noise.Ω).real
      (F ∩ survivalEvent P data η r (r + k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hset : F ∩ exitEvent P data η r (n + 1) =
        (F ∩ survivalEvent P data η r (r + n)) \
        (F ∩ survivalEvent P data η r (r + n + 1)) := by
      ext ω; simp only [exitEvent, Set.mem_sdiff, Set.mem_inter_iff]; tauto
    have he : (P.noise.law : Measure P.noise.Ω).real (F ∩ exitEvent P data η r (n + 1)) =
        (P.noise.law : Measure P.noise.Ω).real (F ∩ survivalEvent P data η r (r + n)) -
        (P.noise.law : Measure P.noise.Ω).real (F ∩ survivalEvent P data η r (r + n + 1)) := by
      rw [hset]
      exact measureReal_sdiff
        (fun _ hx => ⟨hx.1, survivalEvent_antitone P data η r (by omega) hx.2⟩)
        (hF.inter (measurableSet_survivalEvent P data η r (r + n + 1) hm))
    rw [Finset.sum_range_succ, Finset.sum_range_succ, he]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc] at ih ⊢
    nlinarith
lemma weighted_exit_time_partial_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (r n : ℕ)
    (A : Set (Fin r → Weights P.dimension)) (hA : MeasurableSet A) :
    let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
    (∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) *
      (P.noise.law : Measure P.noise.Ω).real (F ∩ exitEvent P data η r (k + 1))) ≤
    (∫ ω, F.indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω)) /
      (6 * P.noiseScale ^ 2 * (P.dimension + 1)) := by
  let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
  have hF : MeasurableSet F := hA.preimage (Measurable.of_eval fun j => h.measurable j)
  have hc : 0 < 6 * P.noiseScale ^ 2 * (P.dimension + 1) := by positivity
  dsimp only
  rw [le_div_iff₀ hc]
  have hb := weighted_survival_stopped_sum P data η h hη hsmall hk hR r n A hA
  have he := weighted_exit_mass_identity P data η r n h.measurable F hF
  have hi (t : ℕ) (S : Set P.noise.Ω) :
      0 ≤ ∫ ω, S.indicator (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω) :=
    integral_nonneg fun ω => Set.indicator_nonneg
      (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR t ω) ω
  have hq := hi (r + n) (F ∩ survivalEvent P data η r (r + n))
  have ha := Finset.sum_nonneg (s := Finset.range n) (fun k _ => hi (r + k + 1)
    ((F ∩ survivalEvent P data η r (r + k)) \ (F ∩ survivalEvent P data η r (r + k + 1))))
  have hn : 0 ≤ (n : ℝ) * (P.noise.law : Measure P.noise.Ω).real
      (F ∩ survivalEvent P data η r (r + n)) := by positivity
  have hint := integrable_batch_potential P data η h hη.le hsmall hR r
  have hle : (∫ ω, (F ∩ survivalEvent P data η r r).indicator (batchPotential P data η r) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ≤
      ∫ ω, F.indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω) := by
    apply integral_mono (hint.indicator (hF.inter (measurableSet_survivalEvent P data η r r h.measurable)))
      (hint.indicator hF)
    intro ω
    by_cases hw : ω ∈ F ∩ survivalEvent P data η r r
    · simp only [Set.indicator_of_mem hw, Set.indicator_of_mem hw.1, le_refl]
    · rw [Set.indicator_of_notMem hw]
      exact Set.indicator_nonneg (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR r ω) ω
  dsimp only at hb
  nlinarith
lemma weighted_exit_time_summable (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (r : ℕ)
    (A : Set (Fin r → Weights P.dimension)) (hA : MeasurableSet A) :
    let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
    let flux := fun k : ℕ => (k : ℝ) *
      (P.noise.law : Measure P.noise.Ω).real (F ∩ exitEvent P data η r k)
    Summable flux ∧ (∑' k, flux k) ≤
      (∫ ω, F.indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω)) /
        (6 * P.noiseScale ^ 2 * (P.dimension + 1)) := by
  let F := {ω | (fun j : Fin r => P.noise.sample j ω) ∈ A}
  dsimp only
  let flux := fun k : ℕ => (k : ℝ) *
    (P.noise.law : Measure P.noise.Ω).real (F ∩ exitEvent P data η r k)
  have hn (k : ℕ) : 0 ≤ flux k := by dsimp [flux]; positivity
  have hb (n : ℕ) : ∑ k ∈ Finset.range n, flux k ≤
      (∫ ω, F.indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω)) /
        (6 * P.noiseScale ^ 2 * (P.dimension + 1)) := by
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      apply div_nonneg
      · exact integral_nonneg fun ω => Set.indicator_nonneg
          (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR r ω) ω
      · positivity
    | succ n =>
      rw [Finset.sum_range_succ']
      simpa only [flux, Nat.cast_zero, zero_mul, add_zero] using
        weighted_exit_time_partial_bound P data η h hη hsmall hk hR hσ r n A hA
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

def HistoryEvent (P : Public) (t : ℕ) (S : Set P.noise.Ω) : Prop :=
  ∃ A : Set (Fin t → Weights P.dimension), MeasurableSet A ∧
    S = {ω | (fun j : Fin t => P.noise.sample j ω) ∈ A}
lemma historyEvent_mono (P : Public) {r t : ℕ} (hrt : r ≤ t) {S : Set P.noise.Ω}
    (hS : HistoryEvent P r S) : HistoryEvent P t S := by
  rcases hS with ⟨A, hA, rfl⟩
  refine ⟨(fun x : Fin t → Weights P.dimension => fun j : Fin r => x (Fin.castLE hrt j)) ⁻¹' A,
    hA.preimage (Measurable.of_eval fun j => measurable_pi_apply (Fin.castLE hrt j)), rfl⟩
lemma historyEvent_inter (P : Public) (t : ℕ) {S T : Set P.noise.Ω}
    (hS : HistoryEvent P t S) (hT : HistoryEvent P t T) : HistoryEvent P t (S ∩ T) := by
  rcases hS with ⟨A, hA, rfl⟩
  rcases hT with ⟨B, hB, rfl⟩
  exact ⟨A ∩ B, hA.inter hB, rfl⟩
lemma historyEvent_compl (P : Public) (t : ℕ) {S : Set P.noise.Ω}
    (hS : HistoryEvent P t S) : HistoryEvent P t Sᶜ := by
  rcases hS with ⟨A, hA, rfl⟩
  exact ⟨Aᶜ, hA.compl, rfl⟩
lemma historyEvent_survival (P : Public) (data : Data P) (η : ℝ) (r t : ℕ) :
    HistoryEvent P t (survivalEvent P data η r t) :=
  ⟨survivalHistory P data η r t, measurableSet_survivalHistory P data η r t,
    (survivalEvent_factor P data η r t).symm⟩
lemma historyEvent_exit (P : Public) (data : Data P) (η : ℝ) (r k : ℕ) :
    HistoryEvent P (r + k) (exitEvent P data η r k) := by
  cases k with
  | zero => simpa only [Nat.add_zero, exitEvent] using
      historyEvent_compl P r (historyEvent_survival P data η r r)
  | succ k =>
    have hs := historyEvent_mono P (show r + k ≤ r + (k + 1) by omega)
      (historyEvent_survival P data η r (r + k))
    have ht := historyEvent_compl P (r + (k + 1)) (historyEvent_survival P data η r (r + (k + 1)))
    simpa only [exitEvent, Set.sdiff_eq, Nat.add_assoc] using historyEvent_inter P (r + (k + 1)) hs ht
lemma historyEvent_measurable (P : Public) (t : ℕ) {S : Set P.noise.Ω}
    (hS : HistoryEvent P t S) (hm : ∀ j, Measurable (P.noise.sample j)) : MeasurableSet S := by
  rcases hS with ⟨A, hA, rfl⟩
  exact hA.preimage (Measurable.of_eval fun j => hm j)
lemma historyEvent_iUnion (P : Public) (t : ℕ) {ι : Type*} [Countable ι]
    (S : ι → Set P.noise.Ω) (hS : ∀ i, HistoryEvent P t (S i)) :
    HistoryEvent P t (⋃ i, S i) := by
  classical
  choose A hA he using hS
  refine ⟨⋃ i, A i, MeasurableSet.iUnion hA, ?_⟩
  ext ω
  simp only [Set.mem_iUnion, he, Set.mem_ofPred_eq]

lemma past_centered_gaussian_block_lower {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) (ξ : ℕ → Ω → E) (hξ : ∀ j, Measurable (ξ j))
    (hi : iIndepFun ξ μ) (hp : ∀ j, μ.map (ξ j) = stdGaussian E)
    (hD : 0 < Module.finrank ℝ E) (t B : ℕ) (A : Set (Fin t → E)) (hA : MeasurableSet A)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {ω | (fun j : Fin t => ξ j ω) ∈ A} *
      ENNReal.ofReal (((ε / (2 * Real.sqrt (Module.finrank ℝ E))) ^ Module.finrank ℝ E *
        Real.exp (-ε ^ 2)) ^ B) ≤
    μ ({ω | (fun j : Fin t => ξ j ω) ∈ A} ∩ {ω | ∀ j : Fin B, ‖ξ (t + j) ω‖ ≤ ε}) := by
  have hb := gaussian_ball_lower (0 : E) ε 0 hD hε (by norm_num) (by simp)
  simp only [neg_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at hb
  have he := past_block_event_probability μ (stdGaussian E) ξ hξ hi hp t B A hA
    (Metric.closedBall 0 ε) Metric.isClosed_closedBall.measurableSet
  simp only [Metric.mem_closedBall, dist_zero_right] at he
  rw [he, ENNReal.ofReal_pow (by positivity)]
  gcongr

end LongTails.Proofs.NoisyBatchQuadraticPerceptronProbability
