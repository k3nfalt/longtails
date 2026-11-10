import LongTails.Proofs.ProximalEf21FunctionalBounds
import LongTails.Proofs.ProximalEf21EnergyComparison
import LongTails.Proofs.ProximalEf21WeightedErrors
import LongTails.Proofs.ProximalEf21ScalarCore
import LongTails.Proofs.ProximalEf21Schedule

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21StochasticContraction

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21FunctionalCalculus
open LongTails.Proofs.ProximalEf21FunctionalBounds
open LongTails.Proofs.ProximalEf21EnergyComparison
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21MomentCalculus
open LongTails.Proofs.ProximalEf21ScalarCore
open LongTails.Proofs.ProximalEf21Schedule

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [MeasurableSpace Ω]

noncomputable def workerMean {n : ℕ} (u : Fin n → E) : E :=
  (n : ℝ)⁻¹ • ∑ i, u i

noncomputable def weightedSquare {n : ℕ} (w : Fin n → ℝ) (u : Fin n → E) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, w i * ‖u i‖ ^ 2

lemma workerMean_add {n : ℕ} (u v : Fin n → E) :
    workerMean (fun i => u i + v i) = workerMean u + workerMean v := by
  simp only [workerMean, Finset.sum_add_distrib, smul_add]

lemma workerMean_sub {n : ℕ} (u v : Fin n → E) :
    workerMean (fun i => u i - v i) = workerMean u - workerMean v := by
  simp only [workerMean, Finset.sum_sub_distrib, smul_sub]

lemma workerMean_smul {n : ℕ} (a : ℝ) (u : Fin n → E) :
    workerMean (fun i => a • u i) = a • workerMean u := by
  simp only [workerMean, ← Finset.smul_sum, smul_smul]
  rw [mul_comm]

lemma workerMean_const {n : ℕ} (hn : 0 < n) (u : E) :
    workerMean (fun _ : Fin n => u) = u := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [workerMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_smul, smul_smul, inv_mul_cancel₀ hnR, one_smul]

lemma workerMean_momentum {n : ℕ} (hn : 0 < n) (α : ℝ)
    (m g ζ : Fin n → E) (b : E) :
    workerMean (fun i => (1 - α) • m i + α • (g i + b + ζ i)) =
      workerMean m + α • (workerMean g - workerMean m + b + workerMean ζ) := by
  simp only [workerMean_add, workerMean_smul, workerMean_const hn,
    sub_smul, one_smul, smul_add, smul_sub]
  abel

lemma weightedSquare_nonnegative {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (u : Fin n → E) : 0 ≤ weightedSquare w u := by
  unfold weightedSquare
  positivity

lemma weightedSquare_integrable {n : ℕ} (P : Measure Ω)
    (w : Fin n → ℝ) (u : Fin n → Ω → E)
    (hu : ∀ i, Integrable (fun ω => ‖u i ω‖ ^ 2) P) :
    Integrable (fun ω => weightedSquare w (fun i => u i ω)) P := by
  exact (integrable_finset_sum _ (fun i _ => (hu i).const_mul (w i))).const_mul _

lemma integral_weightedSquare {n : ℕ} (P : Measure Ω)
    (w : Fin n → ℝ) (u : Fin n → Ω → E)
    (hu : ∀ i, Integrable (fun ω => ‖u i ω‖ ^ 2) P) :
    (∫ ω, weightedSquare w (fun i => u i ω) ∂P) =
      (n : ℝ)⁻¹ * ∑ i, w i * (∫ ω, ‖u i ω‖ ^ 2 ∂P) := by
  unfold weightedSquare
  rw [integral_const_mul,
    integral_finset_sum _ (fun i _ => (hu i).const_mul (w i))]
  simp only [integral_const_mul]

lemma weighted_sum_le {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (u v : Fin n → ℝ) (huv : ∀ i, u i ≤ v i) :
    (n : ℝ)⁻¹ * ∑ i, w i * u i ≤ (n : ℝ)⁻¹ * ∑ i, w i * v i := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (huv i) (hw i))

lemma weighted_constant_le {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℝ) (hw : ∀ i, w i ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    (n : ℝ)⁻¹ * ∑ i, w i * a ≤ a := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  calc
    (n : ℝ)⁻¹ * ∑ i, w i * a ≤ (n : ℝ)⁻¹ * ∑ _ : Fin n, a := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
      exact Finset.sum_le_sum (fun i _ => by
        simpa using mul_le_mul_of_nonneg_right (hw i) ha)
    _ = a := by simp [hnR]

lemma workerMean_memLp {n : ℕ} (P : Measure Ω) (u : Fin n → Ω → E)
    (hu : ∀ i, MemLp (u i) 2 P) :
    MemLp (fun ω => workerMean (fun i => u i ω)) 2 P := by
  exact (memLp_finset_sum _ (fun i _ => hu i)).const_smul _

lemma workerMean_predictable {n : ℕ} (P : Measure Ω)
    (m : MeasurableSpace Ω) (u : Fin n → Ω → E)
    (hu : ∀ i, AEStronglyMeasurable[m] (u i) P) :
    AEStronglyMeasurable[m] (fun ω => workerMean (fun i => u i ω)) P := by
  exact (Finset.aestronglyMeasurable_sum _ (fun i _ => hu i)).const_smul _

lemma mean_noise_orthogonal {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ ‹MeasurableSpace Ω›)
    (ζ : Fin n → Ω → E) (hζ : ∀ i, MemLp (ζ i) 2 P)
    (hcentered : ∀ i, condExp m P (ζ i) =ᵐ[P] (fun _ => 0))
    (u : Ω → E) (hu : MemLp u 2 P)
    (hpred : AEStronglyMeasurable[m] u P) :
    (∫ ω, ⟪u ω, workerMean (fun i => ζ i ω)⟫_ℝ ∂P) = 0 := by
  have hint : ∀ i, Integrable (fun ω => ⟪u ω, ζ i ω⟫_ℝ) P :=
    fun i => integrable_inner_of_memLp_two P u (ζ i) hu (hζ i)
  have hz : ∀ i, (∫ ω, ⟪u ω, ζ i ω⟫_ℝ ∂P) = 0 :=
    fun i => predictable_inner_centered_noise P m hm u (ζ i)
      hu (hζ i) hpred (hcentered i)
  simp only [workerMean, real_inner_smul_right, inner_sum]
  rw [integral_const_mul,
    integral_finset_sum _ (fun i _ => hint i)]
  simp only [hz, Finset.sum_const_zero, mul_zero]

lemma mean_noise_second_moment {n : ℕ} (hn : 0 < n)
    (P : Measure Ω) (ζ : Fin n → Ω → E) (variance : ℝ)
    (hζ : ∀ i, MemLp (ζ i) 2 P)
    (hvar : ∀ i, (∫ ω, ‖ζ i ω‖ ^ 2 ∂P) ≤ variance) :
    (∫ ω, ‖workerMean (fun i => ζ i ω)‖ ^ 2 ∂P) ≤ variance := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsqi : ∀ i, Integrable (fun ω => ‖ζ i ω‖ ^ 2) P := fun i =>
    (memLp_two_iff_integrable_sq_norm (hζ i).aestronglyMeasurable).mp (hζ i)
  have hmean := workerMean_memLp P ζ hζ
  have hmeansq := (memLp_two_iff_integrable_sq_norm hmean.aestronglyMeasurable).mp hmean
  have hpoint : ∀ ω, ‖workerMean (fun i => ζ i ω)‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ i, ‖ζ i ω‖ ^ 2 := by
    intro ω
    have h := weighted_cauchy_schwarz_mean hn (fun _ => 1)
      (fun _ => by norm_num) (fun i => ζ i ω)
    simpa [workerMean, hnR] using h
  have hsumint := (integrable_finset_sum _ (fun i _ => hsqi i)).const_mul ((n : ℝ)⁻¹)
  calc
    (∫ ω, ‖workerMean (fun i => ζ i ω)‖ ^ 2 ∂P) ≤
        ∫ ω, (n : ℝ)⁻¹ * ∑ i, ‖ζ i ω‖ ^ 2 ∂P :=
      integral_mono hmeansq hsumint hpoint
    _ = (n : ℝ)⁻¹ * ∑ i, ∫ ω, ‖ζ i ω‖ ^ 2 ∂P := by
      rw [integral_const_mul, integral_finset_sum _ (fun i _ => hsqi i)]
    _ ≤ (n : ℝ)⁻¹ * ∑ _ : Fin n, variance := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
      exact Finset.sum_le_sum (fun i _ => hvar i)
    _ = variance := by simp [hnR]

lemma weighted_momentum_recurrence {n : ℕ} (hn : 0 < n)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (filtration : MeasurableSpace Ω) (hfiltration : filtration ≤ ‹MeasurableSpace Ω›)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (m g ζ mnext : Fin n → Ω → E) (gstar : Fin n → E) (b : E)
    {α M variance gap : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hvariance : 0 ≤ variance)
    (hm : ∀ i, MemLp (m i) 2 P) (hg : ∀ i, MemLp (g i) 2 P)
    (hζ : ∀ i, MemLp (ζ i) 2 P) (hmnext : ∀ i, MemLp (mnext i) 2 P)
    (hpm : ∀ i, AEStronglyMeasurable[filtration] (m i) P)
    (hpg : ∀ i, AEStronglyMeasurable[filtration] (g i) P)
    (hcentered : ∀ i, condExp filtration P (ζ i) =ᵐ[P] (fun _ => 0))
    (hvar : ∀ i, ∀ᵐ ω ∂P,
      condExp filtration P (fun ω' => ‖ζ i ω'‖ ^ 2) ω ≤ variance)
    (hupdate : ∀ i, ∀ᵐ ω ∂P,
      mnext i ω = (1 - α) • m i ω + α • (g i ω + b + ζ i ω))
    (hinterpolation : (n : ℝ)⁻¹ * ∑ i,
      w i * (∫ ω, ‖g i ω - gstar i‖ ^ 2 ∂P) ≤ 2 * M * gap) :
    (n : ℝ)⁻¹ * ∑ i, w i * (∫ ω, ‖mnext i ω - gstar i‖ ^ 2 ∂P) ≤
      (1 - α) * ((n : ℝ)⁻¹ * ∑ i,
        w i * (∫ ω, ‖m i ω - gstar i‖ ^ 2 ∂P)) +
      4 * α * M * gap + 2 * α * ‖b‖ ^ 2 + α ^ 2 * variance := by
  have hi (i : Fin n) :
      (∫ ω, ‖mnext i ω - gstar i‖ ^ 2 ∂P) ≤
        (1 - α) * (∫ ω, ‖m i ω - gstar i‖ ^ 2 ∂P) +
        2 * α * (∫ ω, ‖g i ω - gstar i‖ ^ 2 ∂P) +
        2 * α * ‖b‖ ^ 2 + α ^ 2 * variance := by
    let u : Ω → E := fun ω =>
      (1 - α) • m i ω + α • (g i ω + b) - gstar i
    have hu : MemLp u 2 P :=
      (((hm i).const_smul (1 - α)).add
        (((hg i).add (memLp_const b)).const_smul α)).sub (memLp_const (gstar i))
    have hpu : AEStronglyMeasurable[filtration] u P :=
      (((hpm i).const_smul (1 - α)).add
        (((hpg i).add aestronglyMeasurable_const).const_smul α)).sub
          aestronglyMeasurable_const
    have hnoise := square_integral_add_fresh_noise P filtration hfiltration
      u (ζ i) α variance hu (hζ i) hpu (hcentered i) (hvar i)
    have hid : (fun ω => ‖mnext i ω - gstar i‖ ^ 2) =ᵐ[P]
        (fun ω => ‖u ω + α • ζ i ω‖ ^ 2) := by
      filter_upwards [hupdate i] with ω hω
      rw [hω]
      congr 1
      dsimp [u]
      simp only [smul_add]
      abel
    have hmi := (memLp_two_iff_integrable_sq_norm
      ((hm i).sub (memLp_const (gstar i))).aestronglyMeasurable).mp
      ((hm i).sub (memLp_const (gstar i)))
    have hgi := (memLp_two_iff_integrable_sq_norm
      ((hg i).sub (memLp_const (gstar i))).aestronglyMeasurable).mp
      ((hg i).sub (memLp_const (gstar i)))
    have hui := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
    have hr := ((hmi.const_mul (1 - α)).add (hgi.const_mul (2 * α))).add
      (integrable_const (2 * α * ‖b‖ ^ 2))
    have hdet := integral_mono hui hr (fun ω =>
      momentum_square_bound α hα hα1 (m i ω) (g i ω) (gstar i) b)
    rw [integral_add ((hmi.const_mul _).add (hgi.const_mul _)) (integrable_const _),
      integral_add (hmi.const_mul _) (hgi.const_mul _),
      integral_const_mul, integral_const_mul] at hdet
    simp only [integral_const, probReal_univ, one_smul, smul_eq_mul] at hdet
    rw [integral_congr_ae hid]
    linarith
  have hsum := weighted_sum_le w hw _ _ hi
  have hconst := weighted_constant_le hn w hw1
    (show 0 ≤ 2 * α * ‖b‖ ^ 2 + α ^ 2 * variance by positivity)
  have hq := mul_le_mul_of_nonneg_left hinterpolation
    (show 0 ≤ 2 * α by positivity)
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have hrew (a : ℝ) (u : Fin n → ℝ) :
      (n : ℝ)⁻¹ * ∑ i, w i * (a * u i) =
      a * ((n : ℝ)⁻¹ * ∑ i, w i * u i) := by
    simp only [show ∀ i, w i * (a * u i) = a * (w i * u i) by intro i; ring,
      ← Finset.mul_sum]
    ring
  simp only [hrew] at hsum
  have hc : (n : ℝ)⁻¹ * ∑ i, w i * (2 * α * ‖b‖ ^ 2) +
      (n : ℝ)⁻¹ * ∑ i, w i * (α ^ 2 * variance) ≤
      2 * α * ‖b‖ ^ 2 + α ^ 2 * variance := by
    simpa only [mul_add, Finset.sum_add_distrib] using hconst
  nlinarith only [hsum, hq, hc]

lemma weighted_compression_recurrence {n : ℕ} (hn : 0 < n)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (filtration : MeasurableSpace Ω) (hfiltration : filtration ≤ ‹MeasurableSpace Ω›)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1)
    (m v g ζ mnext vnext : Fin n → Ω → E) (gstar : Fin n → E) (b : E)
    {α δ M variance gap : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hvariance : 0 ≤ variance)
    (hm : ∀ i, MemLp (m i) 2 P) (hv : ∀ i, MemLp (v i) 2 P)
    (hg : ∀ i, MemLp (g i) 2 P) (hζ : ∀ i, MemLp (ζ i) 2 P)
    (hpm : ∀ i, AEStronglyMeasurable[filtration] (m i) P)
    (hpv : ∀ i, AEStronglyMeasurable[filtration] (v i) P)
    (hpg : ∀ i, AEStronglyMeasurable[filtration] (g i) P)
    (hcentered : ∀ i, condExp filtration P (ζ i) =ᵐ[P] (fun _ => 0))
    (hvar : ∀ i, ∀ᵐ ω ∂P,
      condExp filtration P (fun ω' => ‖ζ i ω'‖ ^ 2) ω ≤ variance)
    (hupdate : ∀ i, ∀ᵐ ω ∂P,
      mnext i ω = (1 - α) • m i ω + α • (g i ω + b + ζ i ω))
    (hcontractive : ∀ i,
      (∫ ω, ‖vnext i ω - mnext i ω‖ ^ 2 ∂P) ≤
        (1 - δ) * (∫ ω, ‖mnext i ω - v i ω‖ ^ 2 ∂P))
    (hinterpolation : (n : ℝ)⁻¹ * ∑ i,
      w i * (∫ ω, ‖g i ω - gstar i‖ ^ 2 ∂P) ≤ 2 * M * gap) :
    (n : ℝ)⁻¹ * ∑ i, w i * (∫ ω, ‖vnext i ω - mnext i ω‖ ^ 2 ∂P) ≤
      (1 - δ / 2) * ((n : ℝ)⁻¹ * ∑ i,
        w i * (∫ ω, ‖v i ω - m i ω‖ ^ 2 ∂P)) +
      6 * α ^ 2 / δ * ((n : ℝ)⁻¹ * ∑ i,
        w i * (∫ ω, ‖m i ω - gstar i‖ ^ 2 ∂P)) +
      12 * α ^ 2 * M / δ * gap + 6 * α ^ 2 / δ * ‖b‖ ^ 2 +
      α ^ 2 * variance := by
  have hi (i : Fin n) :
      (∫ ω, ‖vnext i ω - mnext i ω‖ ^ 2 ∂P) ≤
        (1 - δ / 2) * (∫ ω, ‖v i ω - m i ω‖ ^ 2 ∂P) +
        6 * α ^ 2 / δ * (∫ ω, ‖m i ω - gstar i‖ ^ 2 ∂P) +
        6 * α ^ 2 / δ * (∫ ω, ‖g i ω - gstar i‖ ^ 2 ∂P) +
        6 * α ^ 2 / δ * ‖b‖ ^ 2 + α ^ 2 * variance := by
    let u : Ω → E := fun ω => m i ω - v i ω + α • (g i ω - m i ω + b)
    have hu : MemLp u 2 P := ((hm i).sub (hv i)).add
      ((((hg i).sub (hm i)).add (memLp_const b)).const_smul α)
    have hpu : AEStronglyMeasurable[filtration] u P := ((hpm i).sub (hpv i)).add
      ((((hpg i).sub (hpm i)).add aestronglyMeasurable_const).const_smul α)
    have hnoise := square_integral_add_fresh_noise P filtration hfiltration
      u (ζ i) α variance hu (hζ i) hpu (hcentered i) (hvar i)
    have hid : (fun ω => ‖mnext i ω - v i ω‖ ^ 2) =ᵐ[P]
        (fun ω => ‖u ω + α • ζ i ω‖ ^ 2) := by
      filter_upwards [hupdate i] with ω hω
      rw [hω]
      congr 1
      dsimp [u]
      simp only [smul_add, smul_sub, sub_smul, one_smul]
      abel
    have hmi := (memLp_two_iff_integrable_sq_norm
      ((hm i).sub (memLp_const (gstar i))).aestronglyMeasurable).mp
      ((hm i).sub (memLp_const (gstar i)))
    have hgi := (memLp_two_iff_integrable_sq_norm
      ((hg i).sub (memLp_const (gstar i))).aestronglyMeasurable).mp
      ((hg i).sub (memLp_const (gstar i)))
    have hvi := (memLp_two_iff_integrable_sq_norm
      ((hv i).sub (hm i)).aestronglyMeasurable).mp ((hv i).sub (hm i))
    have hui := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
    have hr := (hvi.const_mul (1 - δ / 2)).add
      (((hmi.add hgi).add (integrable_const ‖b‖ ^ 2)).const_mul (6 * α ^ 2 / δ))
    have hdet := integral_mono (hui.const_mul (1 - δ)) hr (fun ω =>
      compression_square_bound δ α hδ hδ1 (m i ω) (v i ω)
        (g i ω) (gstar i) b)
    rw [integral_const_mul, integral_add (hvi.const_mul _) _,
      integral_const_mul, integral_const_mul,
      integral_add (hmi.add hgi) (integrable_const _), integral_add hmi hgi] at hdet
    simp only [integral_const, probReal_univ, one_smul, smul_eq_mul] at hdet
    have hscale := mul_le_mul_of_nonneg_left hnoise (sub_nonneg.mpr hδ1)
    have hnoiseDrop : (1 - δ) * (α ^ 2 * variance) ≤ α ^ 2 * variance := by
      nlinarith [mul_nonneg (le_of_lt hδ) (mul_nonneg (sq_nonneg α) hvariance)]
    have hc := hcontractive i
    rw [integral_congr_ae hid] at hc
    nlinarith only [hc, hscale, hdet, hnoiseDrop]
  have hsum := weighted_sum_le w hw _ _ hi
  have hconst := weighted_constant_le hn w hw1
    (show 0 ≤ 6 * α ^ 2 / δ * ‖b‖ ^ 2 + α ^ 2 * variance by positivity)
  have hq := mul_le_mul_of_nonneg_left hinterpolation
    (show 0 ≤ 6 * α ^ 2 / δ by positivity)
  have hrew (a : ℝ) (u : Fin n → ℝ) :
      (n : ℝ)⁻¹ * ∑ i, w i * (a * u i) =
      a * ((n : ℝ)⁻¹ * ∑ i, w i * u i) := by
    simp only [show ∀ i, w i * (a * u i) = a * (w i * u i) by intro i; ring,
      ← Finset.mul_sum]
    ring
  simp only [mul_add, Finset.sum_add_distrib, hrew] at hsum
  have hc : (n : ℝ)⁻¹ * ∑ i, w i * (6 * α ^ 2 / δ * ‖b‖ ^ 2) +
      (n : ℝ)⁻¹ * ∑ i, w i * (α ^ 2 * variance) ≤
      6 * α ^ 2 / δ * ‖b‖ ^ 2 + α ^ 2 * variance := by
    simpa only [mul_add, Finset.sum_add_distrib] using hconst
  nlinarith only [hsum, hq, hc]

lemma integrated_functional_progress
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F ψ : E → ℝ) {μ M τ γ α variance : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hτ : 0 < τ) (hγ : 0 < γ)
    (hγτ : γ ≤ τ / 2) (hμτ : μ * τ ≤ 1 / 4096) (hα : α = μ * γ)
    (xstar gstar b : E) (x y m v z g mnext znext ζ : Ω → E)
    (W V : Ω → ℝ)
    (hW0 : ∀ᵐ ω ∂P, 0 ≤ W ω) (hV0 : ∀ᵐ ω ∂P, 0 ≤ V ω)
    (hW : Integrable W P) (hV : Integrable V P)
    (hE0 : Integrable (fun ω => functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω)) P)
    (hE1 : Integrable (fun ω => functionalEnergy F ψ μ τ xstar (y ω) (mnext ω) (znext ω)) P)
    (hgap : Integrable (fun ω => F (y ω) + ψ (y ω) - (F xstar + ψ xstar)) P)
    (hdisp : Integrable (fun ω => ‖y ω - x ω‖ ^ 2) P)
    (hrem1 : Integrable (fun ω =>
      ⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar) P)
    (hrem2 : Integrable (fun ω =>
      ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ) P)
    (hi1 : Integrable (fun ω => ⟪x ω - z ω, ζ ω⟫_ℝ) P)
    (hi2 : Integrable (fun ω => ⟪y ω - xstar, ζ ω⟫_ℝ) P)
    (hi3 : Integrable (fun ω => ⟪g ω - m ω + b, ζ ω⟫_ℝ) P)
    (hζsq : Integrable (fun ω => ‖ζ ω‖ ^ 2) P)
    (hz1 : (∫ ω, ⟪x ω - z ω, ζ ω⟫_ℝ ∂P) = 0)
    (hz2 : (∫ ω, ⟪y ω - xstar, ζ ω⟫_ℝ ∂P) = 0)
    (hz3 : (∫ ω, ⟪g ω - m ω + b, ζ ω⟫_ℝ ∂P) = 0)
    (hvariance : (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ variance)
    (hupdate : ∀ᵐ ω ∂P,
      mnext ω = m ω + α • (g ω - m ω + b + ζ ω))
    (hsmooth : ∀ᵐ ω ∂P,
      F (y ω) - F (x ω) ≤ -⟪g ω, x ω - y ω⟫_ℝ - μ / 2 * ‖y ω - x ω‖ ^ 2)
    (hsupport : ∀ᵐ ω ∂P,
      ψ (z ω) + ⟪τ⁻¹ • (x ω - z ω) - m ω, znext ω - z ω⟫_ℝ ≤ ψ (znext ω))
    (hD : ∀ᵐ ω ∂P, 0 ≤
      ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ)
    (hstrong : ∀ᵐ ω ∂P,
      F (y ω) + ⟪g ω, xstar - y ω⟫_ℝ + μ / 2 * ‖xstar - y ω‖ ^ 2 ≤ F xstar)
    (hmono : ∀ᵐ ω ∂P, 0 ≤
      ⟪γ⁻¹ • (x ω - y ω) - v ω - (τ⁻¹ • (x ω - z ω) - m ω), y ω - z ω⟫_ℝ)
    (hgrad : ∀ᵐ ω ∂P, ‖g ω - gstar‖ ^ 2 ≤
      2 * M * (F (y ω) + ψ (y ω) - (F xstar + ψ xstar)))
    (hmemory : ∀ᵐ ω ∂P, ‖m ω - gstar‖ ^ 2 ≤ 2 * W ω)
    (hcompression : ∀ᵐ ω ∂P, ‖v ω - m ω‖ ^ 2 ≤ 2 * V ω) :
    (∫ ω, functionalEnergy F ψ μ τ xstar (y ω) (mnext ω) (znext ω) ∂P) ≤
      (∫ ω, functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω) ∂P) -
      α * (1 / 8 - 15 * M * τ / 2) *
        (∫ ω, F (y ω) + ψ (y ω) - (F xstar + ψ xstar) ∂P) -
      5 / (8 * γ) * (∫ ω, ‖y ω - x ω‖ ^ 2 ∂P) -
      α / 8 * (∫ ω,
        ⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar ∂P) -
      1 / (μ * τ) * (∫ ω,
        ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ ∂P) +
      15 * α * τ / 2 * (∫ ω, W ω ∂P) + 5 * γ / (μ * τ) * (∫ ω, V ω ∂P) +
      5 * γ * ‖b‖ ^ 2 + μ * γ ^ 2 / 2 * variance := by
  let rhs : Ω → ℝ := fun ω =>
    -α * (1 / 8 - 15 * M * τ / 2) * (F (y ω) + ψ (y ω) - (F xstar + ψ xstar)) -
    5 / (8 * γ) * ‖y ω - x ω‖ ^ 2 -
    α / 8 * (⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar) -
    1 / (μ * τ) * (ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ) +
    15 * α * τ / 2 * W ω + 5 * γ / (μ * τ) * V ω + 5 * γ * ‖b‖ ^ 2 +
    γ / τ * ⟪x ω - z ω, ζ ω⟫_ℝ - α / 8 * ⟪y ω - xstar, ζ ω⟫_ℝ +
    μ * γ ^ 2 * ⟪g ω - m ω + b, ζ ω⟫_ℝ + μ * γ ^ 2 / 2 * ‖ζ ω‖ ^ 2
  have hrhs : Integrable rhs P :=
    (((((((((hgap.const_mul _).sub (hdisp.const_mul _)).sub (hrem1.const_mul _)).sub
      (hrem2.const_mul _)).add (hW.const_mul _)).add (hV.const_mul _)).add
      (integrable_const _)).add (hi1.const_mul _)).sub (hi2.const_mul _)).add
      (hi3.const_mul _) |>.add (hζsq.const_mul _)
  have hp : ∀ᵐ ω ∂P,
      functionalEnergy F ψ μ τ xstar (y ω) (mnext ω) (znext ω) -
        functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω) ≤ rhs ω := by
    filter_upwards [hupdate, hsmooth, hsupport, hD, hstrong, hmono,
      hgrad, hmemory, hcompression, hW0, hV0] with ω hu hs hsu hd hst hmo hg hm hc hw hv
    have h1 := functional_change_with_noise F ψ hμ hτ hα
      xstar (x ω) (y ω) (m ω) (mnext ω) (z ω) (znext ω) (g ω) b (ζ ω) hu hs hsu
    have h2 := pointwise_functional_progress F ψ hμ hM hτ hγ hγτ hμτ hα hw hv
      xstar (x ω) (y ω) (m ω) (v ω) (z ω) (g ω) gstar b hd hst hmo hg hm hc
    dsimp [rhs]
    linarith only [h1, h2]
  have h := integral_mono_ae (hE1.sub hE0) hrhs hp
  rw [integral_sub hE1 hE0] at h
  have heq : (∫ ω, rhs ω ∂P) =
      -α * (1 / 8 - 15 * M * τ / 2) *
        (∫ ω, F (y ω) + ψ (y ω) - (F xstar + ψ xstar) ∂P) -
      5 / (8 * γ) * (∫ ω, ‖y ω - x ω‖ ^ 2 ∂P) -
      α / 8 * (∫ ω, ⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar ∂P) -
      1 / (μ * τ) * (∫ ω, ψ (x ω) - ψ (y ω) -
        ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ ∂P) +
      15 * α * τ / 2 * (∫ ω, W ω ∂P) + 5 * γ / (μ * τ) * (∫ ω, V ω ∂P) +
      5 * γ * ‖b‖ ^ 2 + μ * γ ^ 2 / 2 * (∫ ω, ‖ζ ω‖ ^ 2 ∂P) := by
    dsimp [rhs]
    simp only [integral_add, integral_sub, integral_const_mul, integral_const,
      probReal_univ, one_smul, smul_eq_mul, hz1, hz2, hz3,
      mul_zero, add_zero, sub_zero,
      hgap, hdisp, hrem1, hrem2, hW, hV, hi1, hi2, hi3, hζsq,
      Integrable.add, Integrable.sub, Integrable.const_mul, integrable_const]
  rw [heq] at h
  have hv := mul_le_mul_of_nonneg_left hvariance
    (show 0 ≤ μ * γ ^ 2 / 2 by positivity)
  linarith

lemma integrated_upper_comparison
    (P : Measure Ω) (F ψ : E → ℝ) {μ M τ γ : ℝ}
    (hμ : 0 < μ) (hM : 0 < M) (hτ : 0 < τ) (hγ : 0 < γ)
    (hμM : μ ≤ M) (hμγ : μ * γ ≤ 1) (hμτ : μ * τ ≤ 1)
    (hsmall : μ * γ + 2 * μ * M * γ ^ 2 ≤ 3)
    (xstar gstar : E) (x y m v z g : Ω → E) (W V : Ω → ℝ)
    (hE : Integrable (fun ω => functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω)) P)
    (hgap : Integrable (fun ω => F (y ω) + ψ (y ω) - (F xstar + ψ xstar)) P)
    (hdisp : Integrable (fun ω => ‖y ω - x ω‖ ^ 2) P)
    (hrem1 : Integrable (fun ω =>
      ⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar) P)
    (hrem2 : Integrable (fun ω =>
      ψ (x ω) - ψ (y ω) - ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ) P)
    (hW : Integrable W P) (hV : Integrable V P)
    (hsupport : ∀ᵐ ω ∂P, ψ (y ω) +
      ⟪γ⁻¹ • (x ω - y ω) - v ω, z ω - y ω⟫_ℝ ≤ ψ (z ω))
    (hD : ∀ᵐ ω ∂P, 0 ≤ ψ (x ω) - ψ (y ω) -
      ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ)
    (hdistance : ∀ᵐ ω ∂P, μ / 2 * ‖y ω - xstar‖ ^ 2 ≤
      F (y ω) + ψ (y ω) - (F xstar + ψ xstar))
    (hsmooth : ∀ᵐ ω ∂P,
      F (x ω) ≤ F (y ω) + ⟪g ω, x ω - y ω⟫_ℝ + M / 2 * ‖x ω - y ω‖ ^ 2)
    (hgrad : ∀ᵐ ω ∂P, ‖g ω - gstar‖ ^ 2 ≤
      2 * M * (F (y ω) + ψ (y ω) - (F xstar + ψ xstar)))
    (hmemory : ∀ᵐ ω ∂P, ‖m ω - gstar‖ ^ 2 ≤ 2 * W ω)
    (hcompression : ∀ᵐ ω ∂P, ‖v ω - m ω‖ ^ 2 ≤ 2 * V ω) :
    (∫ ω, functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω) ∂P) ≤
      3 * (∫ ω, F (y ω) + ψ (y ω) - (F xstar + ψ xstar) ∂P) +
      5 / (μ * γ ^ 2) * (∫ ω, ‖y ω - x ω‖ ^ 2 ∂P) +
      (∫ ω, ⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar ∂P) / 8 +
      2 / (μ * τ) * (∫ ω, ψ (x ω) - ψ (y ω) -
        ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ ∂P) +
      (∫ ω, W ω ∂P) / M + 4 / μ * (∫ ω, V ω ∂P) := by
  have hr := (((((hgap.const_mul _).add (hdisp.const_mul _)).add
      (hrem1.div_const 8)).add (hrem2.const_mul _)).add
      (hW.div_const M)).add (hV.const_mul _)
  have hp : ∀ᵐ ω ∂P,
      functionalEnergy F ψ μ τ xstar (x ω) (m ω) (z ω) ≤
      3 * (F (y ω) + ψ (y ω) - (F xstar + ψ xstar)) +
      5 / (μ * γ ^ 2) * ‖y ω - x ω‖ ^ 2 +
      (⟪γ⁻¹ • (x ω - y ω) - v ω, y ω - xstar⟫_ℝ - ψ (y ω) + ψ xstar) / 8 +
      2 / (μ * τ) * (ψ (x ω) - ψ (y ω) -
        ⟪γ⁻¹ • (x ω - y ω) - v ω, x ω - y ω⟫_ℝ) + W ω / M + 4 / μ * V ω := by
    filter_upwards [hsupport, hD, hdistance, hsmooth, hgrad, hmemory,
      hcompression] with ω hs hd hdi hsm hg hm hc
    exact functional_upper_comparison F ψ hμ hM hτ hγ hμM hμγ hμτ hsmall
      xstar (x ω) (y ω) (m ω) (v ω) (z ω) (g ω) gstar hs hd hdi hsm hg hm hc
  have h := integral_mono_ae hE hr hp
  simpa only [integral_add, integral_const_mul, integral_div,
    hgap, hdisp, hrem1, hrem2, hW, hV,
    Integrable.add, Integrable.const_mul, Integrable.div_const] using h

end LongTails.Proofs.ProximalEf21StochasticContraction
