import LongTails.Proofs.NoisyBatchQuadraticPerceptronSuccess
import LongTails.Proofs.NoisyBatchQuadraticPerceptronProbability
import LongTails.Proofs.NoisyBatchQuadraticPerceptronMoments
import Mathlib.Data.Nat.Pairing
import LongTails.Proofs.NoisyBatchQuadraticPerceptronBudget
namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronRegeneration
open LongTails.Proofs.NoisyBatchQuadraticPerceptronProbability
open MeasureTheory
lemma weighted_partition_mass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (A : Set Ω) (hA : MeasurableSet A) (E : ℕ → Set Ω)
    (hE : ∀ k, MeasurableSet (E k)) (hdis : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : ∀ᵐ ω ∂μ, ∃ k, ω ∈ E k) :
    (∑' k, μ.real (A ∩ E k)) = μ.real A := by
  have hd : Pairwise (fun i j => Disjoint (A ∩ E i) (A ∩ E j)) := by
    intro i j hij
    exact (hdis hij).mono Set.inter_subset_right Set.inter_subset_right
  have hm : μ (⋃ k, A ∩ E k) = μ A := by
    apply measure_congr
    filter_upwards [hcover] with ω hω
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    apply propext
    exact ⟨fun ⟨_, ha, _⟩ => ha, fun ha => hω.imp fun _ he => ⟨ha, he⟩⟩
  change (∑' k, (μ (A ∩ E k)).toReal) = (μ A).toReal
  rw [← ENNReal.tsum_toReal_eq (fun k => measure_ne_top μ _),
    ← measure_iUnion hd (fun k => hA.inter (hE k)), hm]
lemma weighted_partition_mass_summable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (A : Set Ω) (hA : MeasurableSet A) (E : ℕ → Set Ω)
    (hE : ∀ k, MeasurableSet (E k)) (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Summable (fun k => μ.real (A ∩ E k)) := by
  apply ENNReal.summable_toReal
  have hd : Pairwise (fun i j => Disjoint (A ∩ E i) (A ∩ E j)) := by
    intro i j hij
    exact (hdis hij).mono Set.inter_subset_right Set.inter_subset_right
  rw [← measure_iUnion hd (fun k => hA.inter (hE k))]
  exact measure_ne_top μ _
open ProbabilityTheory LongTails.Setups.NoisyBatchQuadraticPerceptron
lemma weighted_exit_mass_total (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (r : ℕ) (A : Set P.noise.Ω) (hA : MeasurableSet A) :
    Summable (fun k => (P.noise.law : Measure P.noise.Ω).real (A ∩ exitEvent P data η r k)) ∧
    (∑' k, (P.noise.law : Measure P.noise.Ω).real (A ∩ exitEvent P data η r k)) =
      (P.noise.law : Measure P.noise.Ω).real A := by
  have hm := fun k => measurableSet_exitEvent P data η r k h.measurable
  have hd := exitEvent_disjoint P data η r
  refine ⟨weighted_partition_mass_summable _ A hA _ hm hd,
    weighted_partition_mass _ A hA _ hm hd ?_⟩
  filter_upwards [hittingOffset_spec_ae P data η h hη hsmall hk hR hσ r] with ω hω
  exact ⟨_, hω.1⟩
open LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
lemma historyEvent_batch_preimage (P : Public) (data : Data P) (η : ℝ) (t : ℕ)
    (S : Set (Weights P.dimension)) (hS : MeasurableSet S) :
    HistoryEvent P t {ω | (trajectory P data η ω ((P.count : ℕ) * t)).point ∈ S} := by
  refine ⟨pastPoint P data η t ⁻¹' S,
    hS.preimage (measurable_pastPoint P data η t), ?_⟩
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  rw [batch_point_factor]
lemma historyEvent_separates (P : Public) (data : Data P) (η : ℝ) (t : ℕ) :
    HistoryEvent P t {ω | Separates data (trajectory P data η ω ((P.count : ℕ) * t)).point} :=
  historyEvent_batch_preimage P data η t _ (measurableSet_separates P data)
lemma historyEvent_zero_output (P : Public) (data : Data P) (η : ℝ) (t : ℕ) :
    HistoryEvent P t {ω | (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2 = 0} := by
  apply historyEvent_batch_preimage P data η t {w | w.ofLp.2 = 0}
  exact measurableSet_eq_fun (by fun_prop) measurable_const
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronProbability
noncomputable def hitEvents (P : Public) (data : Data P) (η : ℝ)
    (S : ℕ → Set P.noise.Ω) (t : ℕ) : Set P.noise.Ω :=
  ⋃ r : Fin (t + 1), S r ∩ exitEvent P data η r (t - r)
lemma mem_hitEvents (P : Public) (data : Data P) (η : ℝ)
    (S : ℕ → Set P.noise.Ω) (t : ℕ) (ω : P.noise.Ω) :
    ω ∈ hitEvents P data η S t ↔
      ∃ r ≤ t, ω ∈ S r ∧ ω ∈ exitEvent P data η r (t - r) := by
  simp only [hitEvents, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · rintro ⟨r, hr, he⟩
    exact ⟨r, by omega, hr, he⟩
  · rintro ⟨r, hr, hs, he⟩
    exact ⟨⟨r, by omega⟩, hs, he⟩
lemma historyEvent_hitEvents (P : Public) (data : Data P) (η : ℝ)
    (S : ℕ → Set P.noise.Ω) (hS : ∀ r, HistoryEvent P r (S r)) (t : ℕ) :
    HistoryEvent P t (hitEvents P data η S t) := by
  apply historyEvent_iUnion
  intro r
  have hr : (r : ℕ) ≤ t := by omega
  apply historyEvent_inter
  · exact historyEvent_mono P hr (hS r)
  · simpa only [Nat.add_sub_of_le hr] using historyEvent_exit P data η r (t - r)
lemma hitEvents_disjoint (P : Public) (data : Data P) (η : ℝ)
    (S : ℕ → Set P.noise.Ω) (hS : Pairwise (fun r s => Disjoint (S r) (S s))) :
    Pairwise (fun t u => Disjoint (hitEvents P data η S t) (hitEvents P data η S u)) := by
  intro t u htu
  rw [Set.disjoint_left]
  intro ω ht hu
  obtain ⟨r, hrt, hSr, hEr⟩ := (mem_hitEvents P data η S t ω).1 ht
  obtain ⟨s, hsu, hSs, hEs⟩ := (mem_hitEvents P data η S u ω).1 hu
  have hrs : r = s := by
    by_contra hne
    exact Set.disjoint_left.mp (hS hne) hSr hSs
  subst s
  exact Set.disjoint_left.mp (exitEvent_disjoint P data η r (by omega : t - r ≠ u - r)) hEr hEs
def timeOffsetEquiv : (Σ t : ℕ, Fin (t + 1)) ≃ ℕ × ℕ where
  toFun z := (z.2, z.1 - z.2)
  invFun z := ⟨z.1 + z.2, ⟨z.1, by omega⟩⟩
  left_inv z := by
    rcases z with ⟨t, r⟩
    simp only
    have h : (r : ℕ) + (t - r) = t := by omega
    apply Sigma.ext h
    exact (Fin.heq_ext_iff (congrArg (· + 1) h)).2 rfl
  right_inv z := by simp
lemma tsum_time_offsets (f : ℕ → ℕ → ℝ≥0∞) :
    (∑' t : ℕ, ∑ r : Fin (t + 1), f r (t - r)) = ∑' r : ℕ, ∑' k : ℕ, f r k := by
  have he := timeOffsetEquiv.tsum_eq (fun z : ℕ × ℕ => f z.1 z.2)
  rw [ENNReal.tsum_prod] at he
  change (∑' c : Σ t : ℕ, Fin (t + 1), f c.2 (c.1 - c.2)) = _ at he
  rw [ENNReal.tsum_sigma (fun (t : ℕ) (r : Fin (t + 1)) => f r (t - r))] at he
  simpa only [timeOffsetEquiv, Equiv.coe_fn_mk, tsum_fintype] using he
lemma hitEvents_mass (P : Public) (data : Data P) (η : ℝ)
    (hm : ∀ j, Measurable (P.noise.sample j)) (S : ℕ → Set P.noise.Ω)
    (hS : ∀ r, MeasurableSet (S r)) (hd : Pairwise (fun r s => Disjoint (S r) (S s)))
    (t : ℕ) :
    (P.noise.law : Measure P.noise.Ω) (hitEvents P data η S t) =
      ∑ r : Fin (t + 1), (P.noise.law : Measure P.noise.Ω)
        (S r ∩ exitEvent P data η r (t - r)) := by
  have hdis : Pairwise (fun r s : Fin (t + 1) =>
      Disjoint (S r ∩ exitEvent P data η r (t - r))
        (S s ∩ exitEvent P data η s (t - s))) := by
    intro r s hrs
    exact (hd (Fin.val_ne_of_ne hrs)).mono Set.inter_subset_left Set.inter_subset_left
  rw [hitEvents, measure_iUnion hdis (fun r => (hS r).inter
    (measurableSet_exitEvent P data η r (t - r) hm)), tsum_fintype]
lemma hitEvents_total_mass (P : Public) (data : Data P) (η : ℝ)
    (hm : ∀ j, Measurable (P.noise.sample j)) (S : ℕ → Set P.noise.Ω)
    (hS : ∀ r, MeasurableSet (S r)) (hd : Pairwise (fun r s => Disjoint (S r) (S s))) :
    (∑' t, (P.noise.law : Measure P.noise.Ω) (hitEvents P data η S t)) =
      ∑' r, ∑' k, (P.noise.law : Measure P.noise.Ω) (S r ∩ exitEvent P data η r k) := by
  simp_rw [hitEvents_mass P data η hm S hS hd]
  exact tsum_time_offsets (fun r k => (P.noise.law : Measure P.noise.Ω)
    (S r ∩ exitEvent P data η r k))
lemma weighted_exit_measure_total (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (r : ℕ) (A : Set P.noise.Ω) (hA : MeasurableSet A) :
    (∑' k, (P.noise.law : Measure P.noise.Ω) (A ∩ exitEvent P data η r k)) =
      (P.noise.law : Measure P.noise.Ω) A := by
  have hd : Pairwise (fun i j => Disjoint (A ∩ exitEvent P data η r i)
      (A ∩ exitEvent P data η r j)) := by
    intro i j hij
    exact (exitEvent_disjoint P data η r hij).mono Set.inter_subset_right Set.inter_subset_right
  rw [← measure_iUnion hd (fun k => hA.inter (measurableSet_exitEvent P data η r k h.measurable))]
  apply measure_congr
  filter_upwards [hittingOffset_spec_ae P data η h hη hsmall hk hR hσ r] with ω hω
  apply propext
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  exact ⟨fun ⟨_, ha, _⟩ => ha, fun ha => ⟨_, ha, hω.1⟩⟩
lemma hitEvents_preserve_mass (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (S : ℕ → Set P.noise.Ω)
    (hS : ∀ r, MeasurableSet (S r)) (hd : Pairwise (fun r s => Disjoint (S r) (S s))) :
    (∑' t, (P.noise.law : Measure P.noise.Ω) (hitEvents P data η S t)) =
      ∑' r, (P.noise.law : Measure P.noise.Ω) (S r) := by
  rw [hitEvents_total_mass P data η h.measurable S hS hd]
  apply tsum_congr
  intro r
  exact weighted_exit_measure_total P data η h hη hsmall hk hR hσ r (S r) (hS r)
lemma hitEvents_preserve_real_mass (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (S : ℕ → Set P.noise.Ω)
    (hS : ∀ r, MeasurableSet (S r)) (hd : Pairwise (fun r s => Disjoint (S r) (S s))) :
    (∑' t, (P.noise.law : Measure P.noise.Ω).real (hitEvents P data η S t)) =
      ∑' r, (P.noise.law : Measure P.noise.Ω).real (S r) := by
  have he := congrArg ENNReal.toReal (hitEvents_preserve_mass P data η h hη hsmall hk hR hσ S hS hd)
  simpa only [measureReal_def, ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)] using he
noncomputable def cycleStarts (P : Public) (data : Data P) (η : ℝ) (B : ℕ) :
    ℕ → ℕ → Set P.noise.Ω
  | 0, t => if t = 1 then Set.univ else ∅
  | j + 1, t => if B ≤ t then
      hitEvents P data η (cycleStarts P data η B j) (t - B) ∩
        {ω | ¬Separates data (trajectory P data η ω ((P.count : ℕ) * t)).point}
      else ∅
lemma historyEvent_empty (P : Public) (t : ℕ) : HistoryEvent P t ∅ := by
  exact ⟨∅, MeasurableSet.empty, by ext; simp⟩
lemma historyEvent_univ (P : Public) (t : ℕ) : HistoryEvent P t Set.univ := by
  exact ⟨Set.univ, MeasurableSet.univ, by ext; simp⟩
lemma historyEvent_cycleStarts (P : Public) (data : Data P) (η : ℝ) (B j t : ℕ) :
    HistoryEvent P t (cycleStarts P data η B j t) := by
  induction j generalizing t with
  | zero =>
    by_cases ht : t = 1
    · simpa only [cycleStarts, ite_eq_left ht] using historyEvent_univ P t
    · simpa only [cycleStarts, ite_eq_right ht] using historyEvent_empty P t
  | succ j ih =>
    by_cases ht : B ≤ t
    · rw [cycleStarts, ite_eq_left ht]
      apply historyEvent_inter
      · exact historyEvent_mono P (Nat.sub_le t B) (historyEvent_hitEvents P data η _ ih (t - B))
      · exact historyEvent_compl P t (historyEvent_separates P data η t)
    · simpa only [cycleStarts, ite_eq_right ht] using historyEvent_empty P t
lemma cycleStarts_disjoint (P : Public) (data : Data P) (η : ℝ) (B j : ℕ) :
    Pairwise (fun t u => Disjoint (cycleStarts P data η B j t) (cycleStarts P data η B j u)) := by
  induction j with
  | zero =>
    intro t u htu
    by_cases ht : t = 1
    · have hu : u ≠ 1 := by omega
      simp [cycleStarts, ht, hu]
    · simp [cycleStarts, ht]
  | succ j ih =>
    intro t u htu
    by_cases ht : B ≤ t
    · by_cases hu : B ≤ u
      · rw [cycleStarts, ite_eq_left ht, cycleStarts, ite_eq_left hu]
        exact (hitEvents_disjoint P data η _ ih (by omega : t - B ≠ u - B)).mono
          Set.inter_subset_left Set.inter_subset_left
      · simp [cycleStarts, hu]
    · simp [cycleStarts, ht]
lemma cycleStarts_succ_shift (P : Public) (data : Data P) (η : ℝ) (B j t : ℕ) :
    cycleStarts P data η B (j + 1) (t + B) =
      hitEvents P data η (cycleStarts P data η B j) t ∩
        {ω | ¬Separates data (trajectory P data η ω ((P.count : ℕ) * (t + B))).point} := by
  simp [cycleStarts]
lemma cycleStarts_succ_early (P : Public) (data : Data P) (η : ℝ) (B j t : ℕ)
    (ht : t < B) : cycleStarts P data η B (j + 1) t = ∅ := by
  simp [cycleStarts, Nat.not_le.mpr ht]
lemma cycleStarts_positive (P : Public) (data : Data P) (η : ℝ) (B j t : ℕ)
    (hB : 0 < B) (ω : P.noise.Ω) (hω : ω ∈ cycleStarts P data η B j t) : 0 < t := by
  by_contra ht
  have he : t = 0 := by omega
  subst t
  cases j with
  | zero => simp [cycleStarts] at hω
  | succ j => simp only [cycleStarts_succ_early P data η B j 0 hB, Set.mem_empty_iff_false] at hω
open LongTails.Proofs.NoisyBatchQuadraticPerceptronSuccess
open scoped RealInnerProductSpace
lemma tested_nonretained_block_success (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (t K B : ℕ) (S : Set P.noise.Ω)
    (ht : 0 < t) (hS : HistoryEvent P t S)
    (hstate : ∀ ω ∈ S, ¬Retained data η (trajectory P data η ω ((P.count : ℕ) * t)).point)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2) :
    ENNReal.ofReal (Real.exp (-25000 * (P.dimension + 1) ^ 2 *
      (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) *
        (P.noise.law : Measure P.noise.Ω) S ≤
      (P.noise.law : Measure P.noise.Ω) (S ∩
        {ω | Separates data (trajectory P data η ω ((P.count : ℕ) * (t + B))).point}) := by
  have hnz : ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω),
      (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2 ≠ 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
    filter_upwards [batch_nonzero_output_ae P data η h hσ.ne'] with ω hω
    exact hω k
  let T : Set P.noise.Ω := S ∩
    {ω | (trajectory P data η ω ((P.count : ℕ) * t)).point.ofLp.2 ≠ 0}
  have hT : HistoryEvent P t T := historyEvent_inter P t hS
    (historyEvent_compl P t (historyEvent_zero_output P data η t))
  have heq : T =ᵐ[(P.noise.law : Measure P.noise.Ω)] S := by
    filter_upwards [hnz] with ω hh
    apply propext
    exact ⟨fun hω => hω.1, fun hω => ⟨hω, hh⟩⟩
  have hm := measure_congr heq
  have hh := tested_exit_block_success P data η h u t K B T hT
    (fun ω hω => ⟨hω.2, hstate ω hω.1⟩) hσ hδ hδR hR hu hmargin htune hK hB
  rw [hm] at hh
  apply hh.trans
  apply measure_mono
  intro ω hω
  exact ⟨hω.1.1, hω.2⟩
lemma hitEvents_not_retained (P : Public) (data : Data P) (η : ℝ)
    (S : ℕ → Set P.noise.Ω) (t : ℕ) (ω : P.noise.Ω) (hω : ω ∈ hitEvents P data η S t) :
    ¬Retained data η (trajectory P data η ω ((P.count : ℕ) * t)).point := by
  obtain ⟨r, hr, _, he⟩ := (mem_hitEvents P data η S t ω).1 hω
  have hh := ((mem_exitEvent_iff P data η r (t - r) ω).1 he).1
  simpa only [Nat.add_sub_of_le hr] using hh
lemma hitEvents_positive (P : Public) (data : Data P) (η : ℝ)
    (S : ℕ → Set P.noise.Ω) (hS : ∀ r ω, ω ∈ S r → 0 < r)
    (t : ℕ) (ω : P.noise.Ω) (hω : ω ∈ hitEvents P data η S t) : 0 < t := by
  obtain ⟨r, hr, hs, _⟩ := (mem_hitEvents P data η S t ω).1 hω
  exact lt_of_lt_of_le (hS r ω hs) hr
lemma cycle_hit_success (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (t K B j : ℕ)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2) :
    ENNReal.ofReal (Real.exp (-25000 * (P.dimension + 1) ^ 2 *
      (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) *
        (P.noise.law : Measure P.noise.Ω) (hitEvents P data η (cycleStarts P data η B j) t) ≤
      (P.noise.law : Measure P.noise.Ω) (hitEvents P data η (cycleStarts P data η B j) t ∩
        {ω | Separates data (trajectory P data η ω ((P.count : ℕ) * (t + B))).point}) := by
  by_cases ht : 0 < t
  · exact tested_nonretained_block_success P data η h u t K B _ ht
      (historyEvent_hitEvents P data η _ (historyEvent_cycleStarts P data η B j) t)
      (fun ω hω => hitEvents_not_retained P data η _ t ω hω)
      hσ hδ hδR hR hu hmargin htune hK hB
  · have he : hitEvents P data η (cycleStarts P data η B j) t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hp := hitEvents_positive P data η (cycleStarts P data η B j)
        (fun r ω hr => cycleStarts_positive P data η B j r (by omega) ω hr) t ω hω
      exact ht hp
    simp only [he, measure_empty, mul_zero, Set.empty_inter, le_refl]
lemma failure_measure_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (S T : Set Ω) (hT : MeasurableSet T) (p : ℝ) (hp : 0 ≤ p)
    (hprob : ENNReal.ofReal p * μ S ≤ μ (S ∩ T)) :
    μ.real (S \ T) ≤ (1 - p) * μ.real S := by
  have hr := ENNReal.toReal_mono (measure_ne_top μ _) hprob
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp] at hr
  change p * μ.real S ≤ μ.real (S ∩ T) at hr
  have he := measureReal_inter_add_sdiff (μ := μ) (s := S) hT
  nlinarith
lemma cycle_failure_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (t K B j : ℕ)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2) :
    (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B (j + 1) (t + B)) ≤
      (1 - Real.exp (-25000 * (P.dimension + 1) ^ 2 *
        (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) *
        (P.noise.law : Measure P.noise.Ω).real (hitEvents P data η (cycleStarts P data η B j) t) := by
  have hp := cycle_hit_success P data η h u t K B j hσ hδ hδR hR hu hmargin htune hK hB
  have hm := historyEvent_measurable P (t + B) (historyEvent_separates P data η (t + B)) h.measurable
  have hf := failure_measure_bound (P.noise.law : Measure P.noise.Ω)
    (hitEvents P data η (cycleStarts P data η B j) t) _ hm _ (Real.exp_pos _).le hp
  rw [cycleStarts_succ_shift]
  simpa only [Set.sdiff_eq, Set.compl_ofPred] using hf
lemma disjoint_real_mass_summable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (E : ℕ → Set Ω) (hE : ∀ k, MeasurableSet (E k))
    (hd : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Summable (fun k => μ.real (E k)) := by
  simpa only [Set.univ_inter] using weighted_partition_mass_summable μ Set.univ MeasurableSet.univ E hE hd
lemma tsum_shift_of_prefix_zero (f : ℕ → ℝ) (hf : Summable f) (B : ℕ)
    (hz : ∀ t < B, f t = 0) : (∑' t, f (t + B)) = ∑' t, f t := by
  have hs : ∑ t ∈ Finset.range B, f t = 0 := Finset.sum_eq_zero fun t ht => hz t (Finset.mem_range.mp ht)
  simpa only [hs, zero_add] using hf.sum_add_tsum_nat_add B
lemma cycleStarts_mass_summable (P : Public) (data : Data P) (η : ℝ) (B j : ℕ)
    (hm : ∀ k, Measurable (P.noise.sample k)) :
    Summable (fun t => (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B j t)) :=
  disjoint_real_mass_summable _ _
    (fun t => historyEvent_measurable P t (historyEvent_cycleStarts P data η B j t) hm)
    (cycleStarts_disjoint P data η B j)
lemma cycleHits_mass_summable (P : Public) (data : Data P) (η : ℝ) (B j : ℕ)
    (hm : ∀ k, Measurable (P.noise.sample k)) :
    Summable (fun t => (P.noise.law : Measure P.noise.Ω).real
      (hitEvents P data η (cycleStarts P data η B j) t)) :=
  disjoint_real_mass_summable _ _
    (fun t => historyEvent_measurable P t
      (historyEvent_hitEvents P data η _ (historyEvent_cycleStarts P data η B j) t) hm)
    (hitEvents_disjoint P data η _ (cycleStarts_disjoint P data η B j))
lemma cycle_mass_step (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (K B j : ℕ)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2) :
    (∑' t, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B (j + 1) t)) ≤
      (1 - Real.exp (-25000 * (P.dimension + 1) ^ 2 *
        (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) *
        (∑' t, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B j t)) := by
  have hn : 1 ≤ (P.count : ℝ) := by exact_mod_cast P.count.property
  have hs := LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialConstants.tuned_step_bounds
    P.count P.radius P.margin η hn hδ hδR htune
  have hRp : 0 < P.radius := lt_of_lt_of_le hδ hδR
  have hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256 := by
    have hq := (sq_le_sq₀ (mul_nonneg hs.1.le hRp.le) (by norm_num : (0 : ℝ) ≤ 1 / 16)).2 hs.2.1
    nlinarith
  have hsn := cycleStarts_mass_summable P data η B (j + 1) h.measurable
  have hsh := cycleHits_mass_summable P data η B j h.measurable
  have hz : ∀ t < B, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B (j + 1) t) = 0 := by
    intro t ht
    rw [cycleStarts_succ_early P data η B j t ht, measureReal_empty]
  rw [← tsum_shift_of_prefix_zero _ hsn B hz]
  have hineq := Summable.tsum_le_tsum
    (fun t => cycle_failure_bound P data η h u t K B j hσ hδ hδR hR hu hmargin htune hK hB)
    (hsn.comp_injective (fun a b hab => Nat.add_right_cancel hab))
    (hsh.mul_left (1 - Real.exp (-25000 * (P.dimension + 1) ^ 2 *
      (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)))
  rw [tsum_mul_left] at hineq
  rw [hitEvents_preserve_real_mass P data η h hs.1 hs.2.1 hk hR hσ _
    (fun t => historyEvent_measurable P t (historyEvent_cycleStarts P data η B j t) h.measurable)
    (cycleStarts_disjoint P data η B j)] at hineq
  exact hineq
lemma cycle_mass_initial (P : Public) (data : Data P) (η : ℝ) (B : ℕ) :
    (∑' t, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B 0 t)) = 1 := by
  have he (t : ℕ) : (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B 0 t) =
      if t = 1 then 1 else 0 := by
    by_cases ht : t = 1 <;> simp [cycleStarts, ht]
  simp_rw [he]
  simp
lemma cycle_mass_geometric (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (K B j : ℕ)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2) :
    (∑' t, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B j t)) ≤
      (1 - Real.exp (-25000 * (P.dimension + 1) ^ 2 *
        (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) ^ j := by
  have hq : 0 ≤ 1 - Real.exp (-25000 * (P.dimension + 1) ^ 2 *
      (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    have hp : 0 ≤ 25000 * (P.dimension + 1 : ℝ) ^ 2 *
        (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2 := by positivity
    nlinarith
  induction j with
  | zero => rw [cycle_mass_initial, pow_zero]
  | succ j ih =>
    have hh := cycle_mass_step P data η h u K B j hσ hδ hδR hR hu hmargin htune hK hB
    have hi := mul_le_mul_of_nonneg_left ih hq
    apply hh.trans
    simpa only [pow_succ, mul_comm] using hi
lemma never_separates_cycle_membership (P : Public) (data : Data P) (η : ℝ) (B : ℕ)
    (ω : P.noise.Ω) (hfinite : ∀ r, ∃ k, ω ∈ exitEvent P data η r k)
    (hnever : ∀ t, ¬Separates data (trajectory P data η ω ((P.count : ℕ) * t)).point)
    (j : ℕ) : ∃ t, ω ∈ cycleStarts P data η B j t := by
  induction j with
  | zero => exact ⟨1, by simp [cycleStarts]⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨k, hk⟩ := hfinite r
    refine ⟨r + k + B, ?_⟩
    rw [cycleStarts_succ_shift]
    refine ⟨?_, hnever _⟩
    apply (mem_hitEvents P data η _ (r + k) ω).2
    exact ⟨r, by omega, hr, by simpa only [Nat.add_sub_cancel_left] using hk⟩
lemma batch_separates_ae (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (K B : ℕ)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2) :
    ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω),
      ∃ t, Separates data (trajectory P data η ω ((P.count : ℕ) * t)).point := by
  have hn : 1 ≤ (P.count : ℝ) := by exact_mod_cast P.count.property
  have hs := LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialConstants.tuned_step_bounds
    P.count P.radius P.margin η hn hδ hδR htune
  have hRp : 0 < P.radius := lt_of_lt_of_le hδ hδR
  have hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256 := by
    have hq := (sq_le_sq₀ (mul_nonneg hs.1.le hRp.le) (by norm_num : (0 : ℝ) ≤ 1 / 16)).2 hs.2.1
    nlinarith
  have hf : ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω), ∀ r, ∃ k, ω ∈ exitEvent P data η r k := by
    rw [ae_all_iff]
    intro r
    filter_upwards [hittingOffset_spec_ae P data η h hs.1 hs.2.1 hk hR hσ r] with ω hω
    exact ⟨_, hω.1⟩
  let A : Set P.noise.Ω := {ω | ∀ t, ¬Separates data (trajectory P data η ω ((P.count : ℕ) * t)).point}
  let q : ℝ := 1 - Real.exp (-25000 * (P.dimension + 1) ^ 2 *
    (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)
  have hq0 : 0 ≤ q := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    have hp : 0 ≤ 25000 * (P.dimension + 1 : ℝ) ^ 2 *
        (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2 := by positivity
    nlinarith
  have hq1 : q < 1 := by dsimp [q]; linarith [Real.exp_pos (-25000 * (P.dimension + 1 : ℝ) ^ 2 *
    (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)]
  have hb (j : ℕ) : (P.noise.law : Measure P.noise.Ω).real A ≤ q ^ j := by
    have hsub : ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω),
        ω ∈ A → ω ∈ ⋃ t, cycleStarts P data η B j t := by
      filter_upwards [hf] with ω hω
      intro ha
      exact Set.mem_iUnion.mpr (never_separates_cycle_membership P data η B ω hω ha j)
    have hm := ENNReal.toReal_mono (measure_ne_top (P.noise.law : Measure P.noise.Ω) _)
      (measure_mono_ae hsub)
    change (P.noise.law : Measure P.noise.Ω).real A ≤
      (P.noise.law : Measure P.noise.Ω).real (⋃ t, cycleStarts P data η B j t) at hm
    have he : (P.noise.law : Measure P.noise.Ω).real (⋃ t, cycleStarts P data η B j t) =
        ∑' t, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B j t) := by
      rw [measureReal_def, measure_iUnion (cycleStarts_disjoint P data η B j)
        (fun t => historyEvent_measurable P t (historyEvent_cycleStarts P data η B j t) h.measurable),
        ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
      rfl
    rw [he] at hm
    exact hm.trans (cycle_mass_geometric P data η h u K B j hσ hδ hδR hR hu hmargin htune hK hB)
  have hz : (P.noise.law : Measure P.noise.Ω).real A = 0 :=
    le_antisymm (ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
      (Filter.Eventually.of_forall hb)) (measureReal_nonneg)
  have hz' : (P.noise.law : Measure P.noise.Ω) A = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top (P.noise.law : Measure P.noise.Ω) A)).mp hz
  rw [ae_iff]
  simpa only [A, not_exists] using hz'
lemma output_eventually_constant_separating_ae (P : Public) (data : Data P) (η : ℝ)
    (O : OracleTemplate.Oracle (Query P) (Reply P.dimension))
    (hO : ∀ history q ξ, O.answer history (0, q) ξ = answer (data q.1) q.2)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (K B : ℕ)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2) :
    ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω), ∃ w : Weights P.dimension,
      Separates data w ∧ ∃ N : ℕ, ∀ L ≥ N, ∀ ξ : (k : ℕ) → O.Seed k,
        LongTails.Algorithms.NoisyBatchQuadraticPerceptron.output P O η L ω ξ = w := by
  filter_upwards [batch_separates_ae P data η h u K B hσ hδ hδR hR hu hmargin htune hK hB] with ω hω
  obtain ⟨t, ht⟩ := hω
  refine ⟨(trajectory P data η ω ((P.count : ℕ) * t)).point, ht, (P.count : ℕ) * (t + 1), ?_⟩
  intro L hL ξ
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hL
  obtain ⟨hf, hp⟩ := frozen_after_separating_batch P data η ω t ht
  rw [execute_trajectory P data O hO, frozen_trajectory P data η ω _ j hf, hp]
lemma real_time_offsets (f : ℕ → ℕ → ℝ)
    (hf : Summable (fun z : ℕ × ℕ => f z.1 z.2)) :
    Summable (fun t => ∑ r : Fin (t + 1), f r (t - r)) ∧
      (∑' t, ∑ r : Fin (t + 1), f r (t - r)) = ∑' r, ∑' k, f r k := by
  have hs : Summable (fun z : Σ t : ℕ, Fin (t + 1) => f z.2 (z.1 - z.2)) :=
    timeOffsetEquiv.summable_iff.mpr hf
  refine ⟨by simpa only [tsum_fintype] using hs.sigma, ?_⟩
  have he := timeOffsetEquiv.tsum_eq (fun z : ℕ × ℕ => f z.1 z.2)
  change (∑' z : Σ t : ℕ, Fin (t + 1), f z.2 (z.1 - z.2)) = _ at he
  rw [hs.tsum_sigma, hf.tsum_prod] at he
  simpa only [tsum_fintype] using he
lemma nonnegative_flux_bound (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hn : ∀ r k, 0 ≤ f r k) (hr : ∀ r, Summable (f r))
    (hb : ∀ r, (∑' k, f r k) ≤ g r) (hg : Summable g) :
    Summable (fun t => ∑ r : Fin (t + 1), f r (t - r)) ∧
      (∑' t, ∑ r : Fin (t + 1), f r (t - r)) ≤ ∑' r, g r := by
  have hs : Summable (fun r => ∑' k, f r k) :=
    Summable.of_nonneg_of_le (fun r => tsum_nonneg (hn r)) hb hg
  have hp : Summable (fun z : ℕ × ℕ => f z.1 z.2) :=
    (summable_prod_of_nonneg (fun z => hn z.1 z.2)).2 ⟨hr, hs⟩
  obtain ⟨hdiag, he⟩ := real_time_offsets f hp
  refine ⟨hdiag, ?_⟩
  rw [he]
  exact Summable.tsum_le_tsum hb hs hg
open MeasureTheory ProbabilityTheory
open LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronProbability
lemma hitEvents_integral (P : Public) (data : Data P) (η : ℝ)
    (hm : ∀ j, Measurable (P.noise.sample j)) (S : ℕ → Set P.noise.Ω)
    (hS : ∀ r, MeasurableSet (S r)) (hd : Pairwise (fun r s => Disjoint (S r) (S s)))
    (t : ℕ) (f : P.noise.Ω → ℝ) (hf : Integrable f (P.noise.law : Measure P.noise.Ω)) :
    (∫ ω, (hitEvents P data η S t).indicator f ω ∂(P.noise.law : Measure P.noise.Ω)) =
      ∑ r : Fin (t + 1), ∫ ω, (S r ∩ exitEvent P data η r (t - r)).indicator f ω
        ∂(P.noise.law : Measure P.noise.Ω) := by
  have hmeas (r : Fin (t + 1)) := (hS r).inter (measurableSet_exitEvent P data η r (t - r) hm)
  have hdis : Pairwise (fun r s : Fin (t + 1) =>
      Disjoint (S r ∩ exitEvent P data η r (t - r))
        (S s ∩ exitEvent P data η s (t - s))) := by
    intro r s hrs
    exact (hd (Fin.val_ne_of_ne hrs)).mono Set.inter_subset_left Set.inter_subset_left
  rw [hitEvents, integral_indicator (MeasurableSet.iUnion hmeas),
    integral_iUnion_fintype hmeas hdis (fun _ => hf.integrableOn)]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_indicator (hmeas r)]
lemma hitEvents_potential_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (S : ℕ → Set P.noise.Ω) (hS : ∀ r, HistoryEvent P r (S r))
    (hd : Pairwise (fun r s => Disjoint (S r) (S s)))
    (hQ : Summable (fun r => ∫ ω, (S r).indicator (batchPotential P data η r) ω
      ∂(P.noise.law : Measure P.noise.Ω))) :
    Summable (fun t => ∫ ω, (hitEvents P data η S t).indicator (batchPotential P data η t) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ∧
    (∑' t, ∫ ω, (hitEvents P data η S t).indicator (batchPotential P data η t) ω
      ∂(P.noise.law : Measure P.noise.Ω)) ≤
      ∑' r, ∫ ω, (S r).indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω) := by
  let f := fun r k => ∫ ω, (S r ∩ exitEvent P data η r k).indicator
    (batchPotential P data η (r + k)) ω ∂(P.noise.law : Measure P.noise.Ω)
  let g := fun r => ∫ ω, (S r).indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω)
  have hn (r k : ℕ) : 0 ≤ f r k := integral_nonneg fun ω =>
    Set.indicator_nonneg (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR (r + k) ω) ω
  have hr (r : ℕ) : Summable (f r) ∧ (∑' k, f r k) ≤ g r := by
    rcases hS r with ⟨A, hA, he⟩
    dsimp [f, g]
    rw [he]
    exact weighted_exit_potential_summable P data η h hη hsmall hk hR r A hA
  have hh := nonnegative_flux_bound f g hn (fun r => (hr r).1) (fun r => (hr r).2) hQ
  have hm (r : ℕ) := historyEvent_measurable P r (hS r) h.measurable
  have he (t : ℕ) : (∫ ω, (hitEvents P data η S t).indicator (batchPotential P data η t) ω
      ∂(P.noise.law : Measure P.noise.Ω)) = ∑ r : Fin (t + 1), f r (t - r) := by
    rw [hitEvents_integral P data η h.measurable S hm hd t (batchPotential P data η t)
      (integrable_batch_potential P data η h hη.le hsmall hR t)]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [f]
    rw [Nat.add_sub_of_le (show (r : ℕ) ≤ t by omega)]
  simpa only [he] using hh
lemma hitEvents_wait_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (S : ℕ → Set P.noise.Ω) (hS : ∀ r, HistoryEvent P r (S r))
    (hQ : Summable (fun r => ∫ ω, (S r).indicator (batchPotential P data η r) ω
      ∂(P.noise.law : Measure P.noise.Ω))) :
    Summable (fun t => ∑ r : Fin (t + 1), ((t - r : ℕ) : ℝ) *
      (P.noise.law : Measure P.noise.Ω).real (S r ∩ exitEvent P data η r (t - r))) ∧
    (∑' t, ∑ r : Fin (t + 1), ((t - r : ℕ) : ℝ) *
      (P.noise.law : Measure P.noise.Ω).real (S r ∩ exitEvent P data η r (t - r))) ≤
      (∑' r, ∫ ω, (S r).indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω)) /
        (6 * P.noiseScale ^ 2 * (P.dimension + 1)) := by
  let f := fun r k : ℕ => (k : ℝ) * (P.noise.law : Measure P.noise.Ω).real (S r ∩ exitEvent P data η r k)
  let g := fun r => (∫ ω, (S r).indicator (batchPotential P data η r) ω
    ∂(P.noise.law : Measure P.noise.Ω)) / (6 * P.noiseScale ^ 2 * (P.dimension + 1))
  have hn (r k : ℕ) : 0 ≤ f r k := by dsimp [f]; positivity
  have hr (r : ℕ) : Summable (f r) ∧ (∑' k, f r k) ≤ g r := by
    rcases hS r with ⟨A, hA, he⟩
    dsimp [f, g]
    rw [he]
    exact weighted_exit_time_summable P data η h hη hsmall hk hR hσ r A hA
  have hh := nonnegative_flux_bound f g hn (fun r => (hr r).1) (fun r => (hr r).2)
    (hQ.div_const (6 * P.noiseScale ^ 2 * (P.dimension + 1)))
  simpa only [f, g, tsum_div_const] using hh
lemma history_block_potential_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (t B : ℕ) (S : Set P.noise.Ω) (hS : HistoryEvent P t S)
    (hB : B * (η ^ 2 * P.radius ^ 2) ≤ 3) :
    (∫ ω, S.indicator (batchPotential P data η (t + B)) ω ∂(P.noise.law : Measure P.noise.Ω)) ≤
      128 * (∫ ω, S.indicator (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) +
      64 * B * P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real S := by
  rcases hS with ⟨A, hA, rfl⟩
  exact LongTails.Proofs.NoisyBatchQuadraticPerceptronMoments.tested_block_potential_bound
    P data η h hη hsmall hR t B A hA hB
lemma cycle_trial_potential_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (t B j : ℕ) (hB : B * (η ^ 2 * P.radius ^ 2) ≤ 3) :
    (∫ ω, (cycleStarts P data η B (j + 1) (t + B)).indicator
      (batchPotential P data η (t + B)) ω ∂(P.noise.law : Measure P.noise.Ω)) ≤
    128 * (∫ ω, (hitEvents P data η (cycleStarts P data η B j) t).indicator
      (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) +
    64 * B * P.noiseScale ^ 2 * (P.dimension + 1) * (P.noise.law : Measure P.noise.Ω).real
      (hitEvents P data η (cycleStarts P data η B j) t) := by
  have hh := historyEvent_hitEvents P data η _ (historyEvent_cycleStarts P data η B j) t
  have hi := integrable_batch_potential P data η h hη hsmall hR (t + B)
  have hm := historyEvent_measurable P t hh h.measurable
  apply le_trans _ (history_block_potential_bound P data η h hη hsmall hR t B _ hh hB)
  apply integral_mono
    (hi.indicator (historyEvent_measurable P (t + B)
      (historyEvent_cycleStarts P data η B (j + 1) (t + B)) h.measurable)) (hi.indicator hm)
  intro ω
  rw [cycleStarts_succ_shift]
  by_cases hω : ω ∈ hitEvents P data η (cycleStarts P data η B j) t
  · by_cases hs : Separates data (trajectory P data η ω ((P.count : ℕ) * (t + B))).point
    · simpa [hω, hs, batchPotential] using batchPotential_nonneg P data η hη hsmall hR (t + B) ω
    · simp [hω, hs]
  · simp [hω]
lemma cycle_potential_step (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (B j : ℕ) (hB : B * (η ^ 2 * P.radius ^ 2) ≤ 3)
    (hQ : Summable (fun t => ∫ ω, (cycleStarts P data η B j t).indicator
      (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω))) :
    Summable (fun t => ∫ ω, (cycleStarts P data η B (j + 1) t).indicator
      (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) ∧
    (∑' t, ∫ ω, (cycleStarts P data η B (j + 1) t).indicator
      (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) ≤
    128 * (∑' t, ∫ ω, (cycleStarts P data η B j t).indicator
      (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) +
    64 * B * P.noiseScale ^ 2 * (P.dimension + 1) *
      (∑' t, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B j t)) := by
  let f := fun t => ∫ ω, (cycleStarts P data η B (j + 1) t).indicator
    (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)
  let q := fun t => ∫ ω, (hitEvents P data η (cycleStarts P data η B j) t).indicator
    (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)
  let m := fun t => (P.noise.law : Measure P.noise.Ω).real
    (hitEvents P data η (cycleStarts P data η B j) t)
  let c : ℝ := 64 * B * P.noiseScale ^ 2 * (P.dimension + 1)
  have hq := hitEvents_potential_bound P data η h hη hsmall hk hR _
    (historyEvent_cycleStarts P data η B j) (cycleStarts_disjoint P data η B j) hQ
  have hm := cycleHits_mass_summable P data η B j h.measurable
  have hn (t : ℕ) : 0 ≤ f t := integral_nonneg fun ω => Set.indicator_nonneg
    (fun ω _ => batchPotential_nonneg P data η hη.le hsmall hR t ω) ω
  have hb (t : ℕ) : f (t + B) ≤ 128 * q t + c * m t :=
    cycle_trial_potential_bound P data η h hη.le hsmall hR t B j hB
  have hsum : Summable (fun t => 128 * q t + c * m t) := (hq.1.mul_left 128).add (hm.mul_left c)
  have hfs : Summable (fun t => f (t + B)) := Summable.of_nonneg_of_le (fun t => hn (t+B)) hb hsum
  have hf : Summable f := (summable_nat_add_iff B).mp hfs
  refine ⟨hf, ?_⟩
  change (∑' t, f t) ≤ _
  have hz (t : ℕ) (ht : t < B) : f t = 0 := by
    dsimp [f]
    rw [cycleStarts_succ_early P data η B j t ht]
    simp
  rw [← tsum_shift_of_prefix_zero f hf B hz]
  have hi := Summable.tsum_le_tsum hb hfs hsum
  rw [Summable.tsum_add (hq.1.mul_left 128) (hm.mul_left c), tsum_mul_left, tsum_mul_left] at hi
  have he := hitEvents_preserve_real_mass P data η h hη hsmall hk hR hσ _
    (fun t => historyEvent_measurable P t (historyEvent_cycleStarts P data η B j t) h.measurable)
    (cycleStarts_disjoint P data η B j)
  change (∑' t, m t) = _ at he
  rw [he] at hi
  exact hi.trans (add_le_add (mul_le_mul_of_nonneg_left hq.2 (by norm_num : (0 : ℝ) ≤ 128)) le_rfl)
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian
open LongTails.Proofs.NoisyBatchQuadraticPerceptronMoments
lemma cycle_potential_initial (P : Public) (data : Data P) (η : ℝ) (B : ℕ) :
    Summable (fun t => ∫ ω, (cycleStarts P data η B 0 t).indicator
      (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) ∧
    (∑' t, ∫ ω, (cycleStarts P data η B 0 t).indicator
      (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) =
    ∫ ω, batchPotential P data η 1 ω ∂(P.noise.law : Measure P.noise.Ω) := by
  have he (t : ℕ) : (∫ ω, (cycleStarts P data η B 0 t).indicator
      (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) =
      if t = 1 then ∫ ω, batchPotential P data η 1 ω ∂(P.noise.law : Measure P.noise.Ω) else 0 := by
    by_cases ht : t = 1 <;> simp [cycleStarts, ht]
  simp_rw [he]
  exact ⟨(hasSum_ite_eq 1 _).summable, (hasSum_ite_eq 1 _).tsum_eq⟩
lemma initial_potential_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1) (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    (∫ ω, batchPotential P data η 1 ω ∂(P.noise.law : Measure P.noise.Ω)) ≤
      4 * ‖P.start‖ ^ 2 + 2 * P.noiseScale ^ 2 * (P.dimension + 1) := by
  have he := tested_energy_growth P data η h hη hR 0 Set.univ MeasurableSet.univ
  have hp := event_potential_energy_bounds (P.noise.law : Measure P.noise.Ω) P data η
    (fun ω => (trajectory P data η ω ((P.count : ℕ) * 1)).point)
    (memLp_batch_point P data η h.measurable (memLp_noise_sample P h) 1)
    hη hsmall hR Set.univ MeasurableSet.univ
  simp only [Set.mem_univ, Set.ofPred_true, Set.indicator_univ, Nat.zero_add,
    Nat.mul_zero, trajectory, initial, integral_const, probReal_univ, one_smul] at he
  simp only [Set.indicator_univ] at hp
  have hp1 := hp.1
  change (∫ ω, batchPotential P data η 1 ω ∂(P.noise.law : Measure P.noise.Ω)) ≤ _ at hp1
  nlinarith [hp1, mul_nonneg (sub_nonneg.mpr hk) (sq_nonneg ‖P.start‖)]
lemma cycle_mass_le_one (P : Public) (data : Data P) (η : ℝ) (B j : ℕ)
    (hm : ∀ k, Measurable (P.noise.sample k)) :
    (∑' t, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B j t)) ≤ 1 := by
  have he : (P.noise.law : Measure P.noise.Ω).real (⋃ t, cycleStarts P data η B j t) =
      ∑' t, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B j t) := by
    rw [measureReal_def, measure_iUnion (cycleStarts_disjoint P data η B j)
      (fun t => historyEvent_measurable P t (historyEvent_cycleStarts P data η B j t) hm),
      ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
    rfl
  rw [← he]
  exact measureReal_le_one
lemma geometric_offset_bound (x : ℕ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ j, x (j + 1) ≤ 128 * x j + 64 * b) (j : ℕ) :
    x j + b ≤ 128 ^ j * (x 0 + b) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hi := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 128)
    have hs := h j
    rw [pow_succ]
    nlinarith
open Classical
lemma cycle_potential_summable (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (B j : ℕ) (hB : B * (η ^ 2 * P.radius ^ 2) ≤ 3) :
    Summable (fun t => ∫ ω, (cycleStarts P data η B j t).indicator
      (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) := by
  induction j with
  | zero => exact (cycle_potential_initial P data η B).1
  | succ j ih => exact (cycle_potential_step P data η h hη hsmall hk hR hσ B j hB ih).1
lemma cycle_potential_geometric (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (B j : ℕ) (hB : B * (η ^ 2 * P.radius ^ 2) ≤ 3) :
    (∑' t, ∫ ω, (cycleStarts P data η B j t).indicator
      (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)) ≤
    128 ^ j * (4 * ‖P.start‖ ^ 2 + 2 * P.noiseScale ^ 2 * (P.dimension + 1) +
      B * P.noiseScale ^ 2 * (P.dimension + 1)) := by
  let x := fun j => ∑' t, ∫ ω, (cycleStarts P data η B j t).indicator
    (batchPotential P data η t) ω ∂(P.noise.law : Measure P.noise.Ω)
  let b : ℝ := B * P.noiseScale ^ 2 * (P.dimension + 1)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hr (j : ℕ) : x (j + 1) ≤ 128 * x j + 64 * b := by
    have hs := (cycle_potential_step P data η h hη hsmall hk hR hσ B j hB
      (cycle_potential_summable P data η h hη hsmall hk hR hσ B j hB)).2
    have hm := cycle_mass_le_one P data η B j h.measurable
    have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 64 * b by positivity)
    dsimp [x, b] at *
    nlinarith
  have hi := geometric_offset_bound x b hb hr j
  have h0 := initial_potential_bound P data η h hη.le hsmall (by linarith : η^2 * P.radius^2 ≤ 1) hR
  have he := (cycle_potential_initial P data η B).2
  change x 0 = _ at he
  rw [← he] at h0
  have hc := mul_le_mul_of_nonneg_left (add_le_add h0 (le_refl b))
    (show (0 : ℝ) ≤ 128 ^ j by positivity)
  change x j ≤ _
  dsimp [b] at hi hc hb
  linarith
noncomputable def cyclePiece (P : Public) (data : Data P) (η : ℝ) (B j l : ℕ) : Set P.noise.Ω :=
  cycleStarts P data η B j (Nat.unpair l).1 ∩
    exitEvent P data η (Nat.unpair l).1 (Nat.unpair l).2
lemma cyclePiece_pair (P : Public) (data : Data P) (η : ℝ) (B j r k : ℕ) :
    cyclePiece P data η B j (Nat.pair r k) =
      cycleStarts P data η B j r ∩ exitEvent P data η r k := by
  simp [cyclePiece]
lemma cyclePiece_disjoint (P : Public) (data : Data P) (η : ℝ) (B j : ℕ) :
    Pairwise (fun l m => Disjoint (cyclePiece P data η B j l) (cyclePiece P data η B j m)) := by
  intro l m hlm
  by_cases hr : (Nat.unpair l).1 = (Nat.unpair m).1
  · have hk : (Nat.unpair l).2 ≠ (Nat.unpair m).2 := by
      intro hk
      have he : Nat.unpair l = Nat.unpair m := Prod.ext hr hk
      exact hlm (Nat.pairEquiv.symm.injective he)
    unfold cyclePiece
    rw [hr]
    exact (exitEvent_disjoint P data η (Nat.unpair m).1 hk).mono
      Set.inter_subset_right Set.inter_subset_right
  · exact (cycleStarts_disjoint P data η B j hr).mono
      Set.inter_subset_left Set.inter_subset_left
lemma measurableSet_cyclePiece (P : Public) (data : Data P) (η : ℝ) (B j l : ℕ)
    (hm : ∀ k, Measurable (P.noise.sample k)) : MeasurableSet (cyclePiece P data η B j l) :=
  (historyEvent_measurable P _ (historyEvent_cycleStarts P data η B j _) hm).inter
    (measurableSet_exitEvent P data η _ _ hm)
noncomputable def cycleDuration (P : Public) (data : Data P) (η : ℝ) (B j : ℕ) (ω : P.noise.Ω) : ℕ :=
  if h : ∃ l, ω ∈ cyclePiece P data η B j l then (Nat.unpair (Nat.find h)).2 + B else 0
lemma cycleDuration_on_piece (P : Public) (data : Data P) (η : ℝ) (B j l : ℕ)
    (ω : P.noise.Ω) (hl : ω ∈ cyclePiece P data η B j l) :
    cycleDuration P data η B j ω = (Nat.unpair l).2 + B := by
  have hex : ∃ m, ω ∈ cyclePiece P data η B j m := ⟨l, hl⟩
  have he : Nat.find hex = l := by
    by_contra hne
    exact Set.disjoint_left.mp (cyclePiece_disjoint P data η B j hne) (Nat.find_spec hex) hl
  simp [cycleDuration, hex, he]
lemma cycleDuration_on_exit (P : Public) (data : Data P) (η : ℝ) (B j r k : ℕ)
    (ω : P.noise.Ω) (hr : ω ∈ cycleStarts P data η B j r) (hk : ω ∈ exitEvent P data η r k) :
    cycleDuration P data η B j ω = k + B := by
  have hp : ω ∈ cyclePiece P data η B j (Nat.pair r k) := by rw [cyclePiece_pair]; exact ⟨hr, hk⟩
  simpa only [Nat.unpair_pair] using cycleDuration_on_piece P data η B j (Nat.pair r k) ω hp
lemma cycleDuration_off_union (P : Public) (data : Data P) (η : ℝ) (B j : ℕ)
    (ω : P.noise.Ω) (hω : ω ∉ ⋃ l, cyclePiece P data η B j l) :
    cycleDuration P data η B j ω = 0 := by
  have he : ¬∃ l, ω ∈ cyclePiece P data η B j l := by simpa only [Set.mem_iUnion] using hω
  simp [cycleDuration, he]
noncomputable def cycleClock (P : Public) (data : Data P) (η : ℝ) (B J : ℕ) (ω : P.noise.Ω) : ℕ :=
  1 + ∑ j ∈ Finset.range J, cycleDuration P data η B j ω
lemma cycleClock_zero (P : Public) (data : Data P) (η : ℝ) (B : ℕ) (ω : P.noise.Ω) :
    cycleClock P data η B 0 ω = 1 := by simp [cycleClock]
lemma cycleClock_succ (P : Public) (data : Data P) (η : ℝ) (B J : ℕ) (ω : P.noise.Ω) :
    cycleClock P data η B (J + 1) ω = cycleClock P data η B J ω + cycleDuration P data η B J ω := by
  simp [cycleClock, Finset.sum_range_succ, Nat.add_assoc]
lemma cycle_hit_from_exit (P : Public) (data : Data P) (η : ℝ) (B j r k : ℕ)
    (ω : P.noise.Ω) (hr : ω ∈ cycleStarts P data η B j r) (hk : ω ∈ exitEvent P data η r k) :
    ω ∈ hitEvents P data η (cycleStarts P data η B j) (r + k) := by
  rw [mem_hitEvents]
  exact ⟨r, by omega, hr, by simpa using hk⟩
lemma cycle_next_absent_of_separating_hit (P : Public) (data : Data P) (η : ℝ) (B j t : ℕ)
    (ω : P.noise.Ω) (ht : ω ∈ hitEvents P data η (cycleStarts P data η B j) t)
    (hs : Separates data (trajectory P data η ω ((P.count : ℕ) * (t + B))).point) :
    ∀ r, ω ∉ cycleStarts P data η B (j + 1) r := by
  intro r hr
  by_cases hB : B ≤ r
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hB
    rw [Nat.add_comm B s, cycleStarts_succ_shift] at hr
    have he : s = t := by
      by_contra hne
      exact Set.disjoint_left.mp
        (hitEvents_disjoint P data η _ (cycleStarts_disjoint P data η B j) hne) hr.1 ht
    subst s
    exact hr.2 hs
  · rw [cycleStarts_succ_early P data η B j r (by omega)] at hr
    exact hr
lemma cycle_absent_propagates (P : Public) (data : Data P) (η : ℝ) (B j : ℕ)
    (ω : P.noise.Ω) (ha : ∀ r, ω ∉ cycleStarts P data η B j r) :
    cycleDuration P data η B j ω = 0 ∧ ∀ r, ω ∉ cycleStarts P data η B (j + 1) r := by
  constructor
  · apply cycleDuration_off_union
    intro hω
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hω
    exact ha _ hl.1
  · intro r hr
    by_cases hB : B ≤ r
    · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hB
      rw [Nat.add_comm B s, cycleStarts_succ_shift] at hr
      obtain ⟨t, _, ht, _⟩ := (mem_hitEvents P data η _ s ω).mp hr.1
      exact ha t ht
    · rw [cycleStarts_succ_early P data η B j r (by omega)] at hr
      exact hr
lemma cycleClock_path_invariant (P : Public) (data : Data P) (η : ℝ) (B J : ℕ)
    (ω : P.noise.Ω) (hf : ∀ r, ∃ k, ω ∈ exitEvent P data η r k) :
    ω ∈ cycleStarts P data η B J (cycleClock P data η B J ω) ∨
    (Separates data (trajectory P data η ω ((P.count : ℕ) * cycleClock P data η B J ω)).point ∧
      ∀ r, ω ∉ cycleStarts P data η B J r) := by
  induction J with
  | zero => left; simp [cycleClock_zero, cycleStarts]
  | succ J ih =>
    rcases ih with ha | ⟨hs, hn⟩
    · let r := cycleClock P data η B J ω
      obtain ⟨k, hk⟩ := hf r
      have ht := cycle_hit_from_exit P data η B J r k ω ha hk
      have hd := cycleDuration_on_exit P data η B J r k ω ha hk
      have hc : cycleClock P data η B (J + 1) ω = r + k + B := by
        rw [cycleClock_succ, hd]
        dsimp [r]
        omega
      rw [hc]
      by_cases hs : Separates data (trajectory P data η ω ((P.count : ℕ) * (r + k + B))).point
      · exact Or.inr ⟨hs, cycle_next_absent_of_separating_hit P data η B J (r+k) ω ht hs⟩
      · left
        rw [cycleStarts_succ_shift]
        exact ⟨ht, hs⟩
    · obtain ⟨hd, hn'⟩ := cycle_absent_propagates P data η B J ω hn
      rw [cycleClock_succ, hd, Nat.add_zero]
      exact Or.inr ⟨hs, hn'⟩
lemma exit_duration_flux (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (B : ℕ) (S : ℕ → Set P.noise.Ω)
    (hS : ∀ r, HistoryEvent P r (S r))
    (hQ : Summable (fun r => ∫ ω, (S r).indicator (batchPotential P data η r) ω
      ∂(P.noise.law : Measure P.noise.Ω)))
    (hm : Summable (fun r => (P.noise.law : Measure P.noise.Ω).real (S r))) :
    Summable (fun z : ℕ × ℕ => ((z.2 + B : ℕ) : ℝ) *
      (P.noise.law : Measure P.noise.Ω).real (S z.1 ∩ exitEvent P data η z.1 z.2)) ∧
    (∑' z : ℕ × ℕ, ((z.2 + B : ℕ) : ℝ) *
      (P.noise.law : Measure P.noise.Ω).real (S z.1 ∩ exitEvent P data η z.1 z.2)) ≤
    (∑' r, ∫ ω, (S r).indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω)) /
      (6 * P.noiseScale ^ 2 * (P.dimension + 1)) +
      B * (∑' r, (P.noise.law : Measure P.noise.Ω).real (S r)) := by
  let f := fun r k : ℕ => ((k+B : ℕ) : ℝ) *
    (P.noise.law : Measure P.noise.Ω).real (S r ∩ exitEvent P data η r k)
  let g := fun r => (∫ ω, (S r).indicator (batchPotential P data η r) ω
    ∂(P.noise.law : Measure P.noise.Ω)) / (6 * P.noiseScale ^ 2 * (P.dimension + 1)) +
    B * (P.noise.law : Measure P.noise.Ω).real (S r)
  have hr (r : ℕ) : Summable (f r) ∧ (∑' k, f r k) ≤ g r := by
    have hms := weighted_exit_mass_total P data η h hη hsmall hk hR hσ r (S r)
      (historyEvent_measurable P r (hS r) h.measurable)
    have hts : Summable (fun k : ℕ => (k : ℝ) *
        (P.noise.law : Measure P.noise.Ω).real (S r ∩ exitEvent P data η r k)) ∧
        (∑' k : ℕ, (k : ℝ) * (P.noise.law : Measure P.noise.Ω).real (S r ∩ exitEvent P data η r k)) ≤
        (∫ ω, (S r).indicator (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω)) /
          (6 * P.noiseScale ^ 2 * (P.dimension + 1)) := by
      rcases hS r with ⟨A, hA, he⟩
      rw [he]
      exact weighted_exit_time_summable P data η h hη hsmall hk hR hσ r A hA
    have he (k : ℕ) : f r k = (k : ℝ) * (P.noise.law : Measure P.noise.Ω).real
        (S r ∩ exitEvent P data η r k) + B * (P.noise.law : Measure P.noise.Ω).real
        (S r ∩ exitEvent P data η r k) := by dsimp [f]; push_cast; ring
    constructor
    · have hs := hts.1.add (hms.1.mul_left (B : ℝ))
      apply hs.congr
      intro k
      exact (he k).symm
    simp_rw [he]
    rw [Summable.tsum_add hts.1 (hms.1.mul_left (B : ℝ)), tsum_mul_left, hms.2]
    exact add_le_add hts.2 le_rfl
  have hn (r k : ℕ) : 0 ≤ f r k := by dsimp [f]; positivity
  have hg : Summable g := (hQ.div_const _).add (hm.mul_left (B : ℝ))
  have hs : Summable (fun r => ∑' k, f r k) :=
    Summable.of_nonneg_of_le (fun r => tsum_nonneg (hn r)) (fun r => (hr r).2) hg
  have hp : Summable (fun z : ℕ × ℕ => f z.1 z.2) :=
    (summable_prod_of_nonneg (fun z => hn z.1 z.2)).2 ⟨fun r => (hr r).1, hs⟩
  refine ⟨hp, ?_⟩
  change (∑' z : ℕ × ℕ, f z.1 z.2) ≤ _
  rw [hp.tsum_prod]
  have hi := Summable.tsum_le_tsum (fun r => (hr r).2) hs hg
  dsimp [g] at hi
  rw [Summable.tsum_add (hQ.div_const _) (hm.mul_left (B : ℝ)), tsum_div_const, tsum_mul_left] at hi
  exact hi
lemma cycleDuration_integrable_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (B j : ℕ)
    (hQ : Summable (fun r => ∫ ω, (cycleStarts P data η B j r).indicator
      (batchPotential P data η r) ω ∂(P.noise.law : Measure P.noise.Ω))) :
    Integrable (fun ω => (cycleDuration P data η B j ω : ℝ)) (P.noise.law : Measure P.noise.Ω) ∧
    (∫ ω, (cycleDuration P data η B j ω : ℝ) ∂(P.noise.law : Measure P.noise.Ω)) ≤
    (∑' r, ∫ ω, (cycleStarts P data η B j r).indicator (batchPotential P data η r) ω
      ∂(P.noise.law : Measure P.noise.Ω)) / (6 * P.noiseScale ^ 2 * (P.dimension + 1)) +
      B * (∑' r, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B j r)) := by
  let f := fun z : ℕ × ℕ => ((z.2 + B : ℕ) : ℝ) *
    (P.noise.law : Measure P.noise.Ω).real
      (cycleStarts P data η B j z.1 ∩ exitEvent P data η z.1 z.2)
  have hf := exit_duration_flux P data η h hη hsmall hk hR hσ B _
    (historyEvent_cycleStarts P data η B j) hQ (cycleStarts_mass_summable P data η B j h.measurable)
  have hs : Summable (fun l => f (Nat.unpair l)) := (Nat.pairEquiv.symm.summable_iff (f := f)).mpr hf.1
  have he (l : ℕ) : (∫ ω, (cyclePiece P data η B j l).indicator
      (fun _ => (((Nat.unpair l).2 + B : ℕ) : ℝ)) ω ∂(P.noise.law : Measure P.noise.Ω)) =
      f (Nat.unpair l) := by
    rw [integral_indicator (measurableSet_cyclePiece P data η B j l h.measurable), setIntegral_const]
    simp [f, cyclePiece, smul_eq_mul, mul_comm]
  have hi := integrable_disjoint_partition (P.noise.law : Measure P.noise.Ω)
    (cyclePiece P data η B j) (fun ω => (cycleDuration P data η B j ω : ℝ))
    (fun l _ => (((Nat.unpair l).2 + B : ℕ) : ℝ))
    (fun l => measurableSet_cyclePiece P data η B j l h.measurable)
    (cyclePiece_disjoint P data η B j)
    (fun l ω hω => congrArg Nat.cast (cycleDuration_on_piece P data η B j l ω hω))
    (fun ω hω => by rw [cycleDuration_off_union P data η B j ω hω]; norm_num)
    (fun _ => integrable_const _) (fun _ _ => by positivity) (by simpa only [he] using hs)
  refine ⟨hi.1, ?_⟩
  rw [hi.2]
  simp_rw [he]
  have hre := Nat.pairEquiv.symm.tsum_eq f
  change (∑' l, f (Nat.unpair l)) = _ at hre
  rw [hre]
  exact hf.2
lemma duration_cost_algebra (a s B T : ℝ) (ha : 0 ≤ a) (hs : 0 < s) (hB : 0 ≤ B) (hT : 1 ≤ T) :
    T * (4 * a + 2 * s + B * s) / (6 * s) + B ≤ T * (2 + a / s + 2 * B) := by
  have hq : 0 ≤ a / s := div_nonneg ha hs.le
  have he : T * (4 * a + 2 * s + B * s) / (6 * s) =
      T * ((2 / 3 : ℝ) * (a / s) + 1 / 3 + B / 6) := by field_simp; ring
  rw [he]
  have hle : (2 / 3 : ℝ) * (a / s) + 1 / 3 + B / 6 ≤ 1 + a / s + B := by linarith
  have hp := mul_le_mul_of_nonneg_left hle (by linarith : 0 ≤ T)
  have hb := mul_le_mul_of_nonneg_right hT hB
  nlinarith
lemma cycleDuration_geometric_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (B j : ℕ) (hB : B * (η ^ 2 * P.radius ^ 2) ≤ 3) :
    Integrable (fun ω => (cycleDuration P data η B j ω : ℝ)) (P.noise.law : Measure P.noise.Ω) ∧
    (∫ ω, (cycleDuration P data η B j ω : ℝ) ∂(P.noise.law : Measure P.noise.Ω)) ≤
      128 ^ j * (2 + ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1)) + 2 * B) := by
  have hd := cycleDuration_integrable_bound P data η h hη hsmall hk hR hσ B j
    (cycle_potential_summable P data η h hη hsmall hk hR hσ B j hB)
  refine ⟨hd.1, ?_⟩
  have hq := cycle_potential_geometric P data η h hη hsmall hk hR hσ B j hB
  have hm := cycle_mass_le_one P data η B j h.measurable
  have hdiv := div_le_div_of_nonneg_right hq
    (show 0 ≤ 6 * P.noiseScale ^ 2 * (P.dimension + 1 : ℝ) by positivity)
  have hmass := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) B)
  have hh := hd.2.trans (add_le_add hdiv hmass)
  simp only [mul_one] at hh
  apply hh.trans
  have hs : 0 < P.noiseScale ^ 2 * (P.dimension + 1 : ℝ) := by positivity
  have ha := duration_cost_algebra (‖P.start‖ ^ 2) (P.noiseScale ^ 2 * (P.dimension + 1))
    B (128 ^ j) (sq_nonneg _) hs (by positivity) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 128))
  simpa only [mul_assoc] using ha
lemma cycleClock_integrable_bound (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (hη : 0 < η) (hsmall : η * P.radius ≤ 1 / 16)
    (hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256) (hR : ∀ i, ‖data i‖ ≤ P.radius)
    (hσ : 0 < P.noiseScale) (B J : ℕ) (hB : B * (η ^ 2 * P.radius ^ 2) ≤ 3) :
    Integrable (fun ω => (cycleClock P data η B J ω : ℝ)) (P.noise.law : Measure P.noise.Ω) ∧
    (∫ ω, (cycleClock P data η B J ω : ℝ) ∂(P.noise.law : Measure P.noise.Ω)) ≤
      128 ^ J * (2 + ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1)) + 2 * B) := by
  have hn : 0 ≤ ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1 : ℝ)) := by positivity
  induction J with
  | zero =>
    simp only [cycleClock_zero, Nat.cast_one, pow_zero, one_mul]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, probReal_univ, one_smul]
    nlinarith [Nat.cast_nonneg (α := ℝ) B]
  | succ J ih =>
    have hd := cycleDuration_geometric_bound P data η h hη hsmall hk hR hσ B J hB
    have he : (fun ω => (cycleClock P data η B (J + 1) ω : ℝ)) =
        (fun ω => (cycleClock P data η B J ω : ℝ) + (cycleDuration P data η B J ω : ℝ)) := by
      funext ω
      rw [cycleClock_succ, Nat.cast_add]
    rw [he]
    refine ⟨ih.1.add hd.1, ?_⟩
    rw [integral_add ih.1 hd.1, pow_succ]
    have hp : 0 ≤ (128 : ℝ) ^ J *
        (2 + ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1)) + 2 * B) := by positivity
    nlinarith [ih.2, hd.2]
lemma natural_clock_tail_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℕ) (hX : Integrable (fun ω => (X ω : ℝ)) μ) (N : ℕ) (hN : 0 < N) :
    μ.real {ω | N < X ω} ≤ (∫ ω, (X ω : ℝ) ∂μ) / N := by
  have hsub : {ω | N < X ω} ⊆ {ω | (N : ℝ) ≤ (X ω : ℝ)} := by
    intro ω hω
    exact_mod_cast (Nat.le_of_lt hω)
  have hm := measureReal_mono (μ := μ) hsub
  have hi := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => Nat.cast_nonneg (α := ℝ) (X ω)) hX (N : ℝ)
  apply (le_div_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) N)]
open ProbabilityTheory
open LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronProbability
open LongTails.Proofs.NoisyBatchQuadraticPerceptronExecution
lemma batch_separates_mono (P : Public) (data : Data P) (η : ℝ) (ω : P.noise.Ω)
    (t N : ℕ) (ht : t ≤ N)
    (hs : Separates data (trajectory P data η ω ((P.count : ℕ) * t)).point) :
    Separates data (trajectory P data η ω ((P.count : ℕ) * N)).point := by
  rcases eq_or_lt_of_le ht with rfl | hlt
  · exact hs
  · have hle := Nat.mul_le_mul_left (P.count : ℕ) (Nat.succ_le_of_lt hlt)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
    obtain ⟨hf, hp⟩ := frozen_after_separating_batch P data η ω t hs
    rw [hj, frozen_trajectory P data η ω _ j hf, hp]
    exact hs
lemma batch_failure_clock_inclusion (P : Public) (data : Data P) (η : ℝ) (B J N : ℕ)
    (hf : ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω), ∀ r, ∃ k, ω ∈ exitEvent P data η r k) :
    ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω),
      ¬Separates data (trajectory P data η ω ((P.count : ℕ) * N)).point →
      ω ∈ (⋃ r, cycleStarts P data η B J r) ∪ {ω | N < cycleClock P data η B J ω} := by
  filter_upwards [hf] with ω hω
  intro hbad
  by_cases ha : ω ∈ ⋃ r, cycleStarts P data η B J r
  · exact Or.inl ha
  · apply Or.inr
    by_contra hc
    have hcn : cycleClock P data η B J ω ≤ N := Nat.le_of_not_gt hc
    rcases cycleClock_path_invariant P data η B J ω hω with hs | ⟨hs, _⟩
    · exact ha (Set.mem_iUnion.mpr ⟨_, hs⟩)
    · exact hbad (batch_separates_mono P data η ω _ N hcn hs)
lemma batch_failure_clock_bound (P : Public) (data : Data P) (η : ℝ) (B J N : ℕ)
    (hm : ∀ k, Measurable (P.noise.sample k))
    (hf : ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω), ∀ r, ∃ k, ω ∈ exitEvent P data η r k)
    (hi : Integrable (fun ω => (cycleClock P data η B J ω : ℝ)) (P.noise.law : Measure P.noise.Ω))
    (hN : 0 < N) :
    (P.noise.law : Measure P.noise.Ω).real
      {ω | ¬Separates data (trajectory P data η ω ((P.count : ℕ) * N)).point} ≤
    (∑' r, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B J r)) +
      (∫ ω, (cycleClock P data η B J ω : ℝ) ∂(P.noise.law : Measure P.noise.Ω)) / N := by
  have hinc := batch_failure_clock_inclusion P data η B J N hf
  have hμ := ENNReal.toReal_mono (measure_ne_top (P.noise.law : Measure P.noise.Ω) _)
    (measure_mono_ae hinc)
  change (P.noise.law : Measure P.noise.Ω).real _ ≤
    (P.noise.law : Measure P.noise.Ω).real
      ((⋃ r, cycleStarts P data η B J r) ∪ {ω | N < cycleClock P data η B J ω}) at hμ
  have hu := measureReal_union_le (μ := (P.noise.law : Measure P.noise.Ω))
    (⋃ r, cycleStarts P data η B J r) {ω | N < cycleClock P data η B J ω}
  have ht := natural_clock_tail_bound (P.noise.law : Measure P.noise.Ω)
    (cycleClock P data η B J) hi N hN
  have he : (P.noise.law : Measure P.noise.Ω).real (⋃ r, cycleStarts P data η B J r) =
      ∑' r, (P.noise.law : Measure P.noise.Ω).real (cycleStarts P data η B J r) := by
    rw [measureReal_def, measure_iUnion (cycleStarts_disjoint P data η B J)
      (fun r => historyEvent_measurable P r (historyEvent_cycleStarts P data η B J r) hm),
      ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
    rfl
  rw [he] at hu
  exact hμ.trans (hu.trans (add_le_add le_rfl ht))
open LongTails.Proofs.NoisyBatchQuadraticPerceptronBudget
lemma batch_failure_quantitative (P : Public) (data : Data P) (η : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (K B J N : ℕ) (hN : 0 < N)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2) :
    (P.noise.law : Measure P.noise.Ω).real
      {ω | ¬Separates data (trajectory P data η ω ((P.count : ℕ) * N)).point} ≤
    (1 - Real.exp (-25000 * (P.dimension + 1) ^ 2 *
      (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2)) ^ J +
    128 ^ J * (2 + ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1)) + 2 * B) / N := by
  have hn : 1 ≤ (P.count : ℝ) := by exact_mod_cast P.count.property
  have hs := LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialConstants.tuned_step_bounds
    P.count P.radius P.margin η hn hδ hδR htune
  have hRp : 0 < P.radius := lt_of_lt_of_le hδ hδR
  have hk : η ^ 2 * P.radius ^ 2 ≤ 1 / 256 := by
    have hq := (sq_le_sq₀ (mul_nonneg hs.1.le hRp.le) (by norm_num : (0 : ℝ) ≤ 1 / 16)).2 hs.2.1
    nlinarith
  have ht : 8 * ((P.count : ℝ) + 1) * η * P.radius ^ 2 = P.margin := by
    have he := (eq_div_iff (by positivity : 8 * ((P.count : ℝ) + 1) * P.radius ^ 2 ≠ 0)).mp htune
    nlinarith
  have hb : B * (η ^ 2 * P.radius ^ 2) ≤ 3 := by
    rw [hB, hK]
    exact LongTails.Proofs.NoisyBatchQuadraticPerceptronMoments.trial_growth_tuning
      P.count η P.margin P.radius hs.1 hδ ht hk
  have hc := cycleClock_integrable_bound P data η h hs.1 hs.2.1 hk hR hσ B J hb
  have hf : ∀ᵐ ω ∂(P.noise.law : Measure P.noise.Ω), ∀ r, ∃ k, ω ∈ exitEvent P data η r k := by
    rw [ae_all_iff]
    intro r
    filter_upwards [hittingOffset_spec_ae P data η h hs.1 hs.2.1 hk hR hσ r] with ω hω
    exact ⟨_, hω.1⟩
  have hm := cycle_mass_geometric P data η h u K B J hσ hδ hδR hR hu hmargin htune hK hB
  exact (batch_failure_clock_bound P data η B J N h.measurable hf hc.1 hN).trans
    (add_le_add hm (div_le_div_of_nonneg_right hc.2 (Nat.cast_nonneg N)))
lemma batch_failure_confidence (P : Public) (data : Data P) (η ρ : ℝ)
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID P.noise.sample
      (stdGaussian (Weights P.dimension)) (P.noise.law : Measure P.noise.Ω))
    (u : Features P.dimension) (K B : ℕ)
    (hσ : 0 < P.noiseScale) (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius)
    (hρ : 0 < ρ) (hR : ∀ i, ‖data i‖ ≤ P.radius) (hu : ‖u‖ = 1)
    (hmargin : ∀ i, P.margin ≤ ⟪data i, u⟫)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2))
    (hK : K = ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊) (hB : B = K + 2) :
    let A := 25000 * (P.dimension + 1 : ℝ) ^ 2 * (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2
    let J := ⌈Real.exp A * Real.log (2 / ρ)⌉₊
    let N := ⌈(2 / ρ) * 128 ^ J * (2 + ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1)) + 2 * B)⌉₊
    (P.noise.law : Measure P.noise.Ω).real
      {ω | ¬Separates data (trajectory P data η ω ((P.count : ℕ) * N)).point} ≤ ρ := by
  dsimp only
  let A := 25000 * (P.dimension + 1 : ℝ) ^ 2 * (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2
  let J := ⌈Real.exp A * Real.log (2 / ρ)⌉₊
  let C := 2 + ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1 : ℝ)) + 2 * B
  let N := ⌈(2 / ρ) * 128 ^ J * C⌉₊
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hp := tuned_cycle_failure A ρ hA hρ
  have hc := tuned_clock_tail C ρ J hC hρ
  have hb := batch_failure_quantitative P data η h u K B J N hc.1 hσ hδ hδR hR hu hmargin htune hK hB
  have he : -25000 * (P.dimension + 1 : ℝ) ^ 2 *
      (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2 = -A := by dsimp [A]; ring
  rw [he] at hb
  change (P.noise.law : Measure P.noise.Ω).real _ ≤ ρ
  have hh := add_le_add hp hc.2
  exact hb.trans (by dsimp only [J, C, N] at *; linarith)
end LongTails.Proofs.NoisyBatchQuadraticPerceptronRegeneration
