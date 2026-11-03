import LongTails.Algorithms.TailObliviousExtragradient
import LongTails.Proofs.TailObliviousNoise
import LongTails.Proofs.GapStrongGrowthIteration
import LongTails.Proofs.ClippedExtragradientIteration
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.TailObliviousStage

open LongTails.Setups.TailObliviousMonotoneRootFinding
open LongTails.Algorithms.TailObliviousExtragradient
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)

lemma strength_pos (d : Public) (hL : 0 < d.L) (k j : ℕ) : 0 < strength d k j := by
  unfold strength; positivity

lemma strength_succ (d : Public) (k j : ℕ) :
    strength d k (j + 1) = 2 * strength d k j := by
  unfold strength; rw [pow_succ]; ring

lemma strength_le (d : Public) (hL : 0 < d.L) (k j : ℕ) (hj : j ≤ k) :
    strength d k j ≤ d.L := by
  unfold strength
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
  nlinarith

lemma strength_zero (d : Public) (k : ℕ) : strength d k 0 = d.L / 2 ^ k := by
  unfold strength; simp

lemma strength_last (d : Public) (hL : 0 < d.L) (k : ℕ) : strength d k k = d.L := by
  unfold strength; field_simp

lemma strength_zero_le (d : Public) (hL : 0 < d.L) (k j : ℕ) :
    strength d k 0 ≤ strength d k j := by
  unfold strength
  have h : d.L * 2 ^ 0 ≤ d.L * 2 ^ j :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.zero_le j)) hL.le
  exact div_le_div_of_nonneg_right h (by positivity)

lemma relaxation_pos (k : ℕ) : 0 < relaxation k := by unfold relaxation; positivity

lemma relaxation_le (k : ℕ) : relaxation k ≤ 1 / 16 := by
  unfold relaxation
  have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma stepSize_mul (d : Public) (hL : 0 < d.L) (k j : ℕ) :
    stepSize d k j * strength d k j = relaxation k := by
  unfold stepSize
  field_simp [(strength_pos d hL k j).ne']

lemma stepSize_nonneg (d : Public) (hL : 0 < d.L) (k j : ℕ) : 0 ≤ stepSize d k j := by
  unfold stepSize
  exact div_nonneg (relaxation_pos k).le (strength_pos d hL k j).le

lemma stepSize_lip (d : Public) (hL : 0 < d.L) (k j : ℕ) :
    stepSize d k j * (d.L + strength d k j) ≤ 1 / 4 := by
  have ha := strength_pos d hL k j
  have hm := stepSize_mul d hL k j
  have hs : stepSize d k j = relaxation k / strength d k j := rfl
  have h1 : stepSize d k j * d.L = relaxation k * 2 ^ k / 2 ^ j := by
    rw [hs]; unfold strength; field_simp
  have h2 : relaxation k * 2 ^ k / 2 ^ j ≤ 1 / 16 := by
    unfold relaxation
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith
  have := relaxation_le k
  nlinarith

lemma decay_bound (k : ℕ) :
    (1 - relaxation k / 2) ^ innerSteps k ≤ 1 / 18 := by
  have hδ := relaxation_pos k
  have hδ1 := relaxation_le k
  have hc : 1 - relaxation k / 2 ≤ Real.exp (-(relaxation k / 2)) := by
    have he := Real.add_one_le_exp (-(relaxation k / 2))
    linarith
  have hp := pow_le_pow_left₀ (by linarith) hc (innerSteps k)
  have hn : (innerSteps k : ℝ) * (relaxation k / 2) = 3 := by
    unfold innerSteps relaxation
    push_cast
    field_simp
    ring
  have hexp : (1 - relaxation k / 2) ^ innerSteps k ≤ Real.exp (-3) := by
    calc _ ≤ Real.exp (-(relaxation k / 2)) ^ innerSteps k := hp
      _ = Real.exp ((innerSteps k : ℝ) * (-(relaxation k / 2))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (-3) := by rw [mul_neg, hn]
  have h3 : (18 : ℝ) ≤ Real.exp 3 := by
    have he := Real.exp_one_gt_d9
    have h : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    nlinarith [sq_nonneg (Real.exp 1)]
  refine hexp.trans ?_
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h3

lemma geometric_sum (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 - t) ^ i ≤ 1 / t := by
  have h : t * ∑ i ∈ Finset.range n, (1 - t) ^ i = 1 - (1 - t) ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring
  have hp : 0 ≤ (1 - t) ^ n := pow_nonneg (by linarith) _
  rw [le_div_iff₀ ht, mul_comm]
  linarith

variable {d : Public} {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma egStep_eq (g : d.E → Ω → d.E) (k j : ℕ) (b x : d.E) (ω : Fin 2 → Ω) :
    egStep d g k j b x ω =
      x - stepSize d k j • (g (x - stepSize d k j • (g x (ω 0) + strength d k j • x - b)) (ω 1) +
        strength d k j • (x - stepSize d k j • (g x (ω 0) + strength d k j • x - b)) - b) := rfl

lemma egStep_measurable (g : d.E → Ω → d.E) (hg : Measurable (Function.uncurry g)) (k j : ℕ) :
    Measurable (fun w : d.E × d.E × (Fin 2 → Ω) => egStep d g k j w.1 w.2.1 w.2.2) := by
  unfold egStep
  have h0 : Measurable (fun w : d.E × d.E × (Fin 2 → Ω) => g w.2.1 (w.2.2 0)) :=
    hg.comp (measurable_fst.comp measurable_snd |>.prodMk
      ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd)))
  have hy : Measurable (fun w : d.E × d.E × (Fin 2 → Ω) =>
      w.2.1 - stepSize d k j • (g w.2.1 (w.2.2 0) + strength d k j • w.2.1 - w.1)) := by
    fun_prop
  have h1 : Measurable (fun w : d.E × d.E × (Fin 2 → Ω) =>
      g (w.2.1 - stepSize d k j • (g w.2.1 (w.2.2 0) + strength d k j • w.2.1 - w.1)) (w.2.2 1)) :=
    hg.comp (hy.prodMk ((measurable_pi_apply 1).comp (measurable_snd.comp measurable_snd)))
  fun_prop

lemma stageRun_parameter_measurable (g : d.E → Ω → d.E)
    (hg : Measurable (Function.uncurry g)) (k j : ℕ) :
    Measurable (fun w : d.E × d.E × (Fin (innerSteps k) → Fin 2 → Ω) =>
      stageRun d g k j w.1 w.2.1 w.2.2) := by
  unfold stageRun
  apply OracleTemplate.ClippedExtragradient.measurable_iterateSamples_parameter
    (advance := fun (b z : d.E) (ω : Fin 2 → Ω) => egStep d g k j b z ω) (k := innerSteps k)
  have h := egStep_measurable g hg k j
  exact h.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))

lemma stage_moment (hL : 0 < d.L) (F : d.E → d.E) (hFm : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hFl : ∀ x y, ‖F x - F y‖ ≤ d.L * ‖x - y‖)
    (p : ProbabilityMeasure Ω) (g : d.E → Ω → d.E) (σ α : ℝ) (hσ0 : 0 ≤ σ)
    (hg : HeavyTailedOperator (p : Measure Ω) F g σ α) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (k j : ℕ) (b x u : d.E) (hu : F u + strength d k j • u - b = 0) :
    Integrable (fun ξ => strength d k j ^ α * ‖stageRun d g k j b x ξ - u‖ ^ α)
      (Measure.pi fun _ : Fin (innerSteps k) => Measure.pi fun _ : Fin 2 => (p : Measure Ω)) ∧
    (∫ ξ, strength d k j ^ α * ‖stageRun d g k j b x ξ - u‖ ^ α
      ∂Measure.pi fun _ : Fin (innerSteps k) => Measure.pi fun _ : Fin 2 => (p : Measure Ω)) ≤
      (1 / 18) * (strength d k j ^ α * ‖x - u‖ ^ α) +
        18 * σ ^ α * relaxation k ^ (α - 1) := by
  set a := strength d k j with ha_def
  set η := stepSize d k j with hη_def
  set δ := relaxation k with hδ_def
  have ha := strength_pos d hL k j
  have hηa : η * a = δ := stepSize_mul d hL k j
  have hη0 : 0 ≤ η := stepSize_nonneg d hL k j
  have hδ := relaxation_pos k
  have hδ1 := relaxation_le k
  let P2 : ProbabilityMeasure (Fin 2 → Ω) := ⟨Measure.pi fun _ => (p : Measure Ω), inferInstance⟩
  have hstep : ∀ z : d.E, Integrable (fun ω => ‖egStep d g k j b z ω - u‖ ^ α)
      (P2 : Measure (Fin 2 → Ω)) ∧
      (∫ ω, ‖egStep d g k j b z ω - u‖ ^ α ∂(P2 : Measure (Fin 2 → Ω))) ≤
        (1 - δ / 2) * ‖z - u‖ ^ α + 9 * η ^ α * σ ^ α := by
    intro z
    have h := TailObliviousNoise.eg_step_moment F d.L hFm hFl p g σ α hg hα1 hα2 a η ha.le
      hL.le hη0 (by rw [hηa]; linarith) (stepSize_lip d hL k j) b z u hu
    rw [hηa] at h
    exact h
  have hm : Measurable (fun q : d.E × (Fin 2 → Ω) => egStep d g k j b q.1 q.2) :=
    (egStep_measurable g hg.measurable k j).comp (measurable_const.prodMk measurable_id)
  have hi := OracleTemplate.GapStrongGrowth.iterateSamples_measurable_integral hm P2
    (fun z => ‖z - u‖ ^ α) (by fun_prop) (fun z => Real.rpow_nonneg (norm_nonneg _) _)
    (by linarith) hstep (innerSteps k) x
  have hdec := decay_bound k
  have hgeo := geometric_sum (δ / 2) (by positivity) (by linarith) (innerSteps k)
  refine ⟨hi.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have haα : 0 ≤ a ^ α := Real.rpow_nonneg ha.le _
  have hxu : 0 ≤ ‖x - u‖ ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have hprod : a ^ α * η ^ α = δ ^ α := by
    rw [← Real.mul_rpow ha.le hη0, mul_comm, hηa]
  have hδα : δ ^ α = δ * δ ^ (α - 1) := by
    rw [← Real.rpow_one_add' hδ.le (by linarith)]
    congr 1; ring
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (innerSteps k), (1 - δ / 2) ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (by linarith) _)
  have hpow0 : 0 ≤ (1 - δ / 2) ^ innerSteps k := pow_nonneg (by linarith) _
  calc a ^ α * (∫ ξ, ‖stageRun d g k j b x ξ - u‖ ^ α
        ∂Measure.pi fun _ : Fin (innerSteps k) => Measure.pi fun _ : Fin 2 => (p : Measure Ω))
      ≤ a ^ α * ((1 - δ / 2) ^ innerSteps k * ‖x - u‖ ^ α +
          9 * η ^ α * σ ^ α * ∑ i ∈ Finset.range (innerSteps k), (1 - δ / 2) ^ i) :=
        mul_le_mul_of_nonneg_left hi.2 haα
    _ = (1 - δ / 2) ^ innerSteps k * (a ^ α * ‖x - u‖ ^ α) +
          9 * σ ^ α * (a ^ α * η ^ α) * ∑ i ∈ Finset.range (innerSteps k), (1 - δ / 2) ^ i := by
        ring
    _ ≤ (1 / 18) * (a ^ α * ‖x - u‖ ^ α) + 9 * σ ^ α * (δ * δ ^ (α - 1)) * (1 / (δ / 2)) := by
        rw [hprod, hδα]
        have hδα0 : 0 ≤ 9 * σ ^ α * (δ * δ ^ (α - 1)) := by
          have := Real.rpow_nonneg hδ.le (α - 1)
          have := Real.rpow_nonneg hσ0 α
          positivity
        exact add_le_add (mul_le_mul_of_nonneg_right hdec (mul_nonneg haα hxu))
          (mul_le_mul_of_nonneg_left hgeo hδα0)
    _ = (1 / 18) * (a ^ α * ‖x - u‖ ^ α) + 18 * σ ^ α * δ ^ (α - 1) := by
        have hδne : δ ≠ 0 := ne_of_gt hδ
        field_simp
        ring

end LongTails.Proofs.TailObliviousStage
