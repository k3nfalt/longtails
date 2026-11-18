import LongTails.Proofs.PolynomialMixingValidation
import LongTails.Proofs.HeavyTailSaddleMultilevel

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.PolynomialMixingScore

open LongTails.Setups.PolynomialMixingSubgradient LongTails.Algorithms.PolynomialMixingSelection
open LongTails.Proofs.PolynomialMixingValidation

variable {q : Params} {f : Space q → ℝ} {g : Point q → ℝ → Space q} {π : Measure ℝ}
  [IsProbabilityMeasure π]

lemma adaptive_score_moment {S : Type*} [MeasurableSpace S] (π : Measure ℝ) [IsProbabilityMeasure π]
    {step : S → ℝ → S} (hs : Measurable (Function.uncurry step)) {D : S → ℝ → ℝ}
    (hD : Measurable (Function.uncurry D)) {p B : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hi : ∀ s, Integrable (D s) π) (hpi : ∀ s, Integrable (fun z => ‖D s z‖ ^ p) π)
    (hb : ∀ s, (∫ z, ‖D s z‖ ^ p ∂π) ≤ B) (s : S) (n : ℕ) :
    let F := fun ξ : ℕ → ℝ => ∑ i ∈ Finset.range n, let t := HeavyTailedProductProcess.trajectory step i s ξ
      D t (ξ i) - ∫ z, D t z ∂π
    Integrable (fun ξ => ‖F ξ‖ ^ p) (Measure.infinitePi (fun _ : ℕ => π)) ∧
      (∫ ξ, ‖F ξ‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => π)) ≤ 24 * n * B := by
  intro F
  let e := fun t z => D t z - ∫ w, D t w ∂π
  have hm : Measurable (fun t => ∫ w, D t w ∂π) := hD.stronglyMeasurable.integral_prod_right.measurable
  have he : Measurable (Function.uncurry e) := hD.sub (hm.comp measurable_fst)
  have hc (t : S) := HeavyTailSaddleMultilevel.centered_moment_le π (hi t) 0 hp hp2
    (by simpa using hpi t)
  have hns := HeavyTailedFreshProcess.noiseSum_moment π hs he hp.le hp2
    (fun t => (hi t).sub (integrable_const _))
    (fun t => by dsimp [e]; rw [integral_sub (hi t) (integrable_const _)]; simp)
    (fun t => (hc t).1) (κ := 4 * B)
    (fun t => ((hc t).2).trans (by simpa using mul_le_mul_of_nonneg_left (hb t) (by norm_num : (0 : ℝ) ≤ 4)))
    n s 0
  have heq (ξ : ℕ → ℝ) : HeavyTailedFreshProcess.noiseSum step e n s 0 ξ = F ξ := by
    simp [HeavyTailedFreshProcess.noiseSum_eq_sum, e, F]
  simp only [heq, norm_zero, Real.zero_rpow (by linarith : p ≠ 0), zero_add] at hns
  exact ⟨hns.1, hns.2.trans_eq (by ring)⟩

omit [IsProbabilityMeasure π] in
lemma inner_raw_moment (h : SubgradientOracle q f g π) (hp : 0 ≤ q.p) (hG : 0 ≤ q.G)
    (y : Point q) (v : Space q) {B : ℝ} (hv : ‖v‖ ≤ B) :
    Integrable (fun z => ‖⟪g y z, v⟫‖ ^ q.p) π ∧
      (∫ z, ‖⟪g y z, v⟫‖ ^ q.p ∂π) ≤ (q.G * B) ^ q.p := by
  have hB := (norm_nonneg v).trans hv
  have hb (z : ℝ) : ‖⟪g y z, v⟫‖ ^ q.p ≤ ‖g y z‖ ^ q.p * B ^ q.p := by
    rw [← Real.mul_rpow (norm_nonneg _) hB]
    exact Real.rpow_le_rpow (norm_nonneg _) ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg _))) hp
  have hi := (h.momentIntegrable y).mul_const (B ^ q.p)
  have hm : Measurable (fun z => ⟪g y z, v⟫) :=
    (h.measurable.comp measurable_prodMk_left).inner measurable_const
  have hi' : Integrable (fun z => ‖⟪g y z, v⟫‖ ^ q.p) π := hi.mono' (hm.norm.pow_const q.p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]; exact hb z)
  refine ⟨hi', (integral_mono hi' hi hb).trans ?_⟩
  rw [integral_mul_const, Real.mul_rpow hG hB]
  exact mul_le_mul_of_nonneg_right (h.moment y) (Real.rpow_nonneg hB _)

lemma chord_score_moment (h : SubgradientOracle q f g π) (hp : 1 < q.p)
    (hp2 : q.p ≤ 2) (hG : 0 ≤ q.G) (x : Point q) (n : ℕ) :
    let D := fun (i : ℕ) (z : ℝ) => ⟪g (chordPoint q x n i) z, x.val⟫
    let F := fun ξ : ℕ → ℝ => ∑ i ∈ Finset.range n, (D i (ξ i) - ∫ z, D i z ∂π)
    Integrable (fun ξ => ‖F ξ‖ ^ q.p) (Measure.infinitePi (fun _ : ℕ => π)) ∧
      (∫ ξ, ‖F ξ‖ ^ q.p ∂Measure.infinitePi (fun _ : ℕ => π)) ≤
        24 * n * (q.G * q.R) ^ q.p := by
  intro D F
  have hD (i : ℕ) : Measurable (D i) :=
    (h.measurable.comp measurable_prodMk_left).inner measurable_const
  have hDi (i : ℕ) : Integrable (D i) π := (h.integrable _).inner_const _
  have hx : ‖x.val‖ ≤ q.R := by simpa only [Domain, Metric.mem_closedBall, dist_zero_right] using x.property
  have hip (i : ℕ) : Integrable (fun z => ‖D i z‖ ^ q.p) π ∧
      (∫ z, ‖D i z‖ ^ q.p ∂π) ≤ (q.G * q.R) ^ q.p :=
    inner_raw_moment h (by linarith) hG _ _ hx
  let step := fun (i : ℕ) (_ : ℝ) => i + 1
  have hns := adaptive_score_moment π (step := step) (D := D)
    (by dsimp [step, Function.uncurry]; fun_prop) (measurable_from_prod_countable_right hD)
    hp hp2 hDi (fun i => (hip i).1) (fun i => (hip i).2) 0 n
  have ht (i s : ℕ) (ξ : ℕ → ℝ) : HeavyTailedProductProcess.trajectory step i s ξ = s + i := by
    induction i generalizing s ξ with
    | zero => simp [HeavyTailedProductProcess.trajectory]
    | succ i ih => simp [HeavyTailedProductProcess.trajectory, ih, step]; omega
  simpa only [ht, zero_add, F] using hns

end LongTails.Proofs.PolynomialMixingScore
