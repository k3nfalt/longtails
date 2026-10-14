import LongTails.Proofs.RenewalInitialization
import LongTails.Proofs.MarkovQuadraticSource

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.MarkovQuadratic

noncomputable section

open MarkovProduct

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private local instance : NormedSpace ℂ (Complexified E →L[ℂ] Complexified E) :=
  ContinuousLinearMap.toNormedSpace
private local instance : Module ℝ (Complexified E →L[ℂ] Complexified E) := Module.complexToReal _
private local instance : NormedSpace ℝ (Complexified E →L[ℂ] Complexified E) := NormedSpace.complexToReal
private local instance : NormedSpace ℂ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := ContinuousLinearMap.toNormedSpace
private local instance : Module ℝ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := Module.complexToReal _
private local instance : NormedSpace ℝ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := NormedSpace.complexToReal

lemma markovCovariance_refresh (η : ℝ) (H : S → E →L[ℝ] E)
    (κ Q : Kernel S S) [IsMarkovKernel Q] (π μ : ProbabilityMeasure S) (α : ℝ)
    (hdec : ∀ i j, (κ i).real {j} = (1 - α) * (Q i).real {j} + α * (π : Measure S).real {j})
    (n : ℕ) :
    markovCovariance η H κ μ n = (((1 - α : ℝ) : ℂ)) ^ n • markovCovariance η H Q μ n +
      ∑ k ∈ Finset.range n, ((α : ℂ) * (((1 - α : ℝ) : ℂ)) ^ k) •
        (markovCovariance η H Q μ (k + 1) * markovCovariance η H κ π (n - 1 - k)) := by
  have hmix : stateMix (B := Complexified E →L[ℂ] Complexified E) (fun i j => (κ i).real {j}) =
      (((1 - α : ℝ) : ℂ)) • stateMix (fun i j => (Q i).real {j}) +
        (α : ℂ) • stateConstant.comp (stateAverage (fun i => (π : Measure S).real {i})) := by
    simp_rw [hdec]
    exact stateMix_refresh _ _ _ _
  simp only [markovCovariance, hmix]
  exact transferCovariance_refresh _ _ _ _ _
    (stateMix_constant _ (fun i => (finite_probability_weights (Q i)).2)) _ _ n

lemma markovCovariance_renewal (η : ℝ) (H : S → E →L[ℝ] E)
    (κ Q : Kernel S S) [IsMarkovKernel Q] (π μ : ProbabilityMeasure S) (α : ℝ)
    (hdec : ∀ i j, (κ i).real {j} = (1 - α) * (Q i).real {j} + α * (π : Measure S).real {j})
    (n : ℕ) :
    markovCovariance η H κ μ (n + 1) = (((1 - α : ℝ) : ℂ)) ^ n • markovCovariance η H Q μ (n + 1) +
      ∑ k ∈ Finset.range n, ((α : ℂ) * (((1 - α : ℝ) : ℂ)) ^ k) •
        (markovCovariance η H Q μ (k + 1) * markovCovariance η H κ π (n - k)) := by
  apply refresh_last_term _ _ _ _ _ (by push_cast; ring)
    (markovCovariance_zero η H κ π) (markovCovariance_refresh η H κ Q π μ α hdec) n

lemma markovCovariance_stationary_source_rate (H : S → E →L[ℝ] E)
    (κ Q : Kernel S S) [IsMarkovKernel κ] [IsMarkovKernel Q] (π : ProbabilityMeasure S)
    (hstat : Q ∘ₘ (π : Measure S) = π) {L α : ℝ} (hL : 0 < L) (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : ∀ i, (H i).adjoint = H i) (hp : ∀ i x, 0 ≤ ⟪x, H i x⟫)
    (hb : ∀ i x, ⟪x, H i x⟫ ≤ L * ‖x‖ ^ 2)
    (hdec : ∀ i j, (κ i).real {j} = (1 - α) * (Q i).real {j} + α * (π : Measure S).real {j})
    (n : ℕ) (hn : 1 ≤ n) :
    ‖markovCovariance (α / (10000 * L)) H κ π n *
      (1 - geometricMean (1 - α) (markovCovariance (α / (10000 * L)) H Q π))‖ ≤
        100000000000 / (α * n) := by
  let η := α / (10000 * L)
  let Φ := markovCovariance η H Q π
  let V := markovCovariance η H κ π
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hηL : η * L = α / 10000 := by dsimp [η]; field_simp
  have hsmall : η * L ≤ 2 := by rw [hηL]; linarith
  have hΦ : ∀ k, ‖Φ k‖ ≤ 1 := norm_markovCovariance_le_one η H Q π hL hs hp hb hη hsmall
  have hV : ∀ k, ‖V k‖ ≤ 1 := norm_markovCovariance_le_one η H κ π hL hs hp hb hη hsmall
  have hd : ∀ k, ‖Φ (k + 1) - Φ k‖ ≤ α / 5000 := by
    intro k
    have hh := norm_markovCovariance_first_difference η H Q π hL hs hp hb hη hsmall k
    rw [hηL] at hh
    convert hh using 1; ring
  have hsecond : ∀ k, ‖Φ (k + 2) - 2 • Φ (k + 1) + Φ k‖ ≤ (α / 5000) ^ 2 := by
    intro k
    have hh := norm_markovCovariance_second_difference η H Q π hstat hL hs hp hb hη hsmall k
    rw [hηL] at hh
    convert hh using 1
    · congr 1
      dsimp [Φ]
      rw [two_smul]
      abel
    · ring
  have hkernel : renewalKernel Φ α (1 - α) 1 = geometricMean (1 - α) Φ := by
    simpa only [sub_sub_cancel] using renewalKernel_one Φ (1 - α)
  have hR : ∀ k : ℕ, ((k : ℝ) + 1) * ‖(1 - renewalKernel Φ α (1 - α) 1) *
      renewalKernel Φ α (1 - α) 1 ^ k‖ ≤ 5 := by
    intro k
    rw [hkernel, sub_mul, one_mul, ← pow_succ']
    have hh := geometricMarkovCovariance_ritt η (1 - α) H Q π hL hs hp hb hη
      (by linarith) (by linarith) (by rw [hηL]; linarith) k
    exact hh.trans (by norm_num)
  have hh := renewal_source_coefficient_bound Φ V hΦ hV (markovCovariance_zero η H Q π)
    hα hα1 hd hsecond hR (markovCovariance_renewal η H κ Q π π α hdec) n hn
  rw [hkernel, renewalScaling, ite_eq_right (by omega : n ≠ 0), smul_mul_assoc, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα.le] at hh
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ (mul_pos hα hnpos)).mpr
  have hh' := (le_div_iff₀ hnpos).mp hh
  dsimp [Φ, V, η] at hh'
  nlinarith

lemma markovCovariance_arbitrary_source_rate (H : S → E →L[ℝ] E)
    (κ Q : Kernel S S) [IsMarkovKernel κ] [IsMarkovKernel Q] (π μ : ProbabilityMeasure S)
    (hstat : Q ∘ₘ (π : Measure S) = π) {L α : ℝ} (hL : 0 < L) (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : ∀ i, (H i).adjoint = H i) (hp : ∀ i x, 0 ≤ ⟪x, H i x⟫)
    (hb : ∀ i x, ⟪x, H i x⟫ ≤ L * ‖x‖ ^ 2)
    (hdec : ∀ i j, (κ i).real {j} = (1 - α) * (Q i).real {j} + α * (π : Measure S).real {j})
    (n : ℕ) (hn : 1 ≤ n) :
    ‖markovCovariance (α / (10000 * L)) H κ μ n *
      (1 - geometricMean (1 - α) (markovCovariance (α / (10000 * L)) H Q π))‖ ≤
        300000000000 / (α * n) := by
  let η := α / (10000 * L)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hsmall : η * L ≤ 2 := by
    have he : η * L = α / 10000 := by dsimp [η]; field_simp
    rw [he]
    linarith
  have hΦ := norm_markovCovariance_le_one η H Q μ hL hs hp hb hη hsmall
  have hV := norm_markovCovariance_le_one η H κ π hL hs hp hb hη hsmall
  have hΨ := norm_geometricMean_le_one (by linarith : 0 ≤ 1 - α) (by linarith : 1 - α < 1)
    (markovCovariance η H Q π) (norm_markovCovariance_le_one η H Q π hL hs hp hb hη hsmall)
  have hA : ‖1 - geometricMean (1 - α) (markovCovariance η H Q π)‖ ≤ 2 := by
    have hi : ‖(1 : (Complexified E →L[ℂ] Complexified E) →L[ℂ]
      (Complexified E →L[ℂ] Complexified E))‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hh := norm_sub_le (1 : (Complexified E →L[ℂ] Complexified E) →L[ℂ]
      (Complexified E →L[ℂ] Complexified E)) (geometricMean (1 - α) (markovCovariance η H Q π))
    linarith
  have hh := renewal_arbitrary_initial_source (markovCovariance η H Q μ) (markovCovariance η H κ π)
    (markovCovariance η H κ μ) _ hΦ hV hA hα hα1 (by norm_num : (0 : ℝ) ≤ 100000000000)
    (markovCovariance_stationary_source_rate H κ Q π hstat hL hα hα1 hs hp hb hdec)
    (markovCovariance_renewal η H κ Q π μ α hdec) n hn
  exact hh.trans (by gcongr; norm_num)

end

end OracleTemplate.MarkovQuadratic
