import LongTails.Proofs.HeavyTailedSospOutput

open MeasureTheory

namespace LongTails.Proofs.HeavyTailedSospWorkIntegration

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open HeavyTailedProductProcess HeavyTailedSospExecution HeavyTailedSospWork

lemma activeCharge_measurable (p : Params) : Measurable (activeCharge p) := by
  have hm : Measurable (Function.uncurry (fun ph (_ : Unit) => activeCharge p ph)) := by
    apply HeavyTailedSospMeasurable.measurable_phase_uncurry p <;> exact measurable_const
  exact hm.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma activeCharge_le_one (p : Params) (ph : Phase p) : activeCharge p ph ≤ 1 := by
  cases ph <;> simp [activeCharge]

lemma unpaddedWork_measurable (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (target N : ℕ) : Measurable (unpaddedWork p c g H target N) := by
  apply Finset.measurable_sum
  intro k hk
  exact (activeCharge_measurable p).comp ((HeavyTailedSospMeasurable.measurable_phase p).comp
    ((trajectory_measurable (HeavyTailedSospMeasurable.measurable_sampleStep p c g H hg hH) k).comp
      ((measurable_const (a := initial p target)).prodMk measurable_id)))

lemma unpaddedWork_le_horizon (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω) : unpaddedWork p c g H target N ξ ≤ N := by
  have hb := Finset.sum_le_sum (s := Finset.range N)
    (f := fun k => activeCharge p (trajectory (sampleStep p c g H) k (initial p target) ξ).phase)
    (g := fun _ => 1) (fun k _ => activeCharge_le_one p _)
  simpa only [unpaddedWork, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] using hb

lemma unpaddedWork_integrable (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P] (target N : ℕ) :
    Integrable (fun ξ => (unpaddedWork p c g H target N ξ : ℝ)) P := by
  have hm := (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (unpaddedWork_measurable p c g hg H hH target N)
  apply (integrable_const (N : ℝ)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  change (unpaddedWork p c g H target N ξ : ℝ) ≤ (N : ℝ)
  exact_mod_cast unpaddedWork_le_horizon p c g H target N ξ

lemma completed_work_real_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (target N : ℕ) (ξ : ℕ → Aux p c × p.Ω)
    (hdone : (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done) :
    let V : ℝ := (trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex
    (unpaddedWork p c g H target N ξ : ℝ) ≤
      (max 1 c.resetBatch : ℕ) * (V / (max 1 c.epoch : ℕ) + 1) +
        V * (max 1 c.transportBatch : ℕ) + c.cycles * (detectorCalls c : ℝ) := by
  intro V
  rw [completed_unpaddedWork p c g H target N ξ hdone]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  have hd : (((trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex /
      max 1 c.epoch : ℕ) : ℝ) ≤ V / (max 1 c.epoch : ℕ) := Nat.cast_div_le
  dsimp only [V] at hd ⊢
  nlinarith [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (max 1 c.resetBatch) : (0 : ℝ) ≤ _)]

lemma expected_unpaddedWork_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q] (target N : ℕ)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done)
    (hV : (∫ ξ, ((trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex : ℝ)
      ∂(Measure.infinitePi fun _ : ℕ => Q)) ≤ 2 * c.cycles) :
    (∫ ξ, (unpaddedWork p c g H target N ξ : ℝ) ∂(Measure.infinitePi fun _ : ℕ => Q)) ≤
      (2 * c.cycles / (max 1 c.epoch : ℕ) + 1) * (max 1 c.resetBatch : ℕ) +
        2 * c.cycles * (max 1 c.transportBatch : ℕ) + c.cycles * (detectorCalls c : ℝ) := by
  let P := Measure.infinitePi fun _ : ℕ => Q
  let V := fun ξ => ((trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex : ℝ)
  let B : ℝ := (max 1 c.resetBatch : ℕ)
  let q : ℝ := (max 1 c.epoch : ℕ)
  let b : ℝ := (max 1 c.transportBatch : ℕ)
  let D : ℝ := detectorCalls c
  have hiV : Integrable V P := HeavyTailedSospEpochIntegration.virtualIndex_integrable p c g hg H hH Q target N
  have hi1 : Integrable (fun ξ => B * (V ξ / q + 1)) P := ((hiV.div_const q).add (integrable_const 1)).const_mul B
  have hi2 : Integrable (fun ξ => V ξ * b) P := hiV.mul_const b
  have hi3 : Integrable (fun _ : ℕ → Aux p c × p.Ω => (c.cycles : ℝ) * D) P := integrable_const _
  have hi12 : Integrable (fun ξ => B * (V ξ / q + 1) + V ξ * b) P := hi1.add hi2
  have hF : Integrable (fun ξ => B * (V ξ / q + 1) + V ξ * b + c.cycles * D) P := (hi1.add hi2).add hi3
  have hb := integral_mono (unpaddedWork_integrable p c g hg H hH P target N) hF
    (fun ξ => completed_work_real_bound p c g H target N ξ (hdone ξ))
  have he : (∫ ξ, B * (V ξ / q + 1) + V ξ * b + c.cycles * D ∂P) =
      B * ((∫ ξ, V ξ ∂P) / q + 1) + (∫ ξ, V ξ ∂P) * b + c.cycles * D := by
    rw [integral_add hi12 hi3, integral_add hi1 hi2, integral_const_mul,
      integral_add (hiV.div_const q) (integrable_const 1), integral_div, integral_mul_const]
    simp
  rw [he] at hb
  have hq : 0 < q := by dsimp [q]; positivity
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hbn : 0 ≤ b := Nat.cast_nonneg _
  have hvq := div_le_div_of_nonneg_right hV (le_of_lt hq)
  have hvB := mul_le_mul_of_nonneg_left (add_le_add hvq (show (1 : ℝ) ≤ 1 from le_rfl)) hB
  have hvb := mul_le_mul_of_nonneg_right hV hbn
  change _ ≤ (2 * c.cycles / q + 1) * B + 2 * c.cycles * b + c.cycles * D
  dsimp only [V, P] at hb hvB hvb
  nlinarith

lemma expected_virtualIndex_le_twice_cycles (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (target N : ℕ) (hT : 0 < c.cycles) (hs : 0 < c.s)
    (hMh : (max 1 c.ncSegments : ℕ) * c.h ≤ 2 * c.s)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p target) ξ).phase = .done)
    (hacc : (∫ ξ, ∑ k ∈ Finset.range N,
      (ncCharge p (trajectory (sampleStep p c g H) k (initial p target) ξ).phase : ℝ) ∂P) /
        c.cycles ≤ c.h / (5 * c.s)) :
    (∫ ξ, ((trajectory (sampleStep p c g H) N (initial p target) ξ).virtualIndex : ℝ) ∂P) ≤
      2 * c.cycles := by
  rw [HeavyTailedSospForecastIntegration.completed_virtualIndex_integral p c g hg H hH P target N hdone]
  have hTr : (0 : ℝ) < c.cycles := by exact_mod_cast hT
  have ha := (div_le_div_iff₀ hTr (by positivity : 0 < 5 * c.s)).mp hacc
  have hM : (0 : ℝ) ≤ (max 1 c.ncSegments : ℕ) := Nat.cast_nonneg _
  have haM := mul_le_mul_of_nonneg_left ha hM
  have hMT := mul_le_mul_of_nonneg_right hMh (le_of_lt hTr)
  nlinarith

lemma cap_failure_bound (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (target N C : ℕ) (hC : 0 < C) {W : ℝ} (hWC : 10 * W ≤ C)
    (hW : (∫ ξ, (unpaddedWork p c g H target N ξ : ℝ) ∂P) ≤ W) :
    P.real {ξ | C < unpaddedWork p c g H target N ξ} ≤ 1 / 10 := by
  have hi := unpaddedWork_integrable p c g hg H hH P target N
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ξ => (Nat.cast_nonneg (unpaddedWork p c g H target N ξ) : (0 : ℝ) ≤ _))) hi (C : ℝ)
  have hsub : {ξ | C < unpaddedWork p c g H target N ξ} ⊆
      {ξ | (C : ℝ) ≤ (unpaddedWork p c g H target N ξ : ℝ)} := by
    intro ξ hh
    change C < unpaddedWork p c g H target N ξ at hh
    change (C : ℝ) ≤ (unpaddedWork p c g H target N ξ : ℝ)
    exact_mod_cast Nat.le_of_lt hh
  have hp := measureReal_mono (μ := P) hsub
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hh := mul_le_mul_of_nonneg_left hp (le_of_lt hCr)
  nlinarith

lemma joint_cap_event_probability (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    {Initial : Type*} [MeasurableSpace Initial]
    (R : Measure Initial) [IsProbabilityMeasure R]
    (P : Measure (ℕ → Aux p c × p.Ω)) [IsProbabilityMeasure P]
    (target N C : ℕ) :
    (R.prod P).real {z | C < unpaddedWork p c g H target N z.2} =
      P.real {ξ | C < unpaddedWork p c g H target N ξ} := by
  have he : {z : Initial × (ℕ → Aux p c × p.Ω) | C < unpaddedWork p c g H target N z.2} =
      Set.univ ×ˢ {ξ | C < unpaddedWork p c g H target N ξ} := by
    ext z
    simp
  rw [he, measureReal_prod_prod, probReal_univ, one_mul]

lemma completed_joint_cap_failure_bound (p : Params) (c : Config)
    [NeZero (max 1 c.cycles)]
    (g : Space p → p.Ω → Space p) (hg : Measurable (Function.uncurry g))
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (hH : Measurable (Function.uncurry H))
    (Q : Measure (Aux p c × p.Ω)) [IsProbabilityMeasure Q]
    (N C : ℕ) (hT : 0 < c.cycles) (hs : 0 < c.s) (hC : 0 < C)
    (hMh : (max 1 c.ncSegments : ℕ) * c.h ≤ 2 * c.s)
    (hdone : ∀ ξ, (trajectory (sampleStep p c g H) N (initial p 0) ξ).phase = .done)
    (hacc : (∫ ξ, ∑ k ∈ Finset.range N,
      (ncCharge p (trajectory (sampleStep p c g H) k (initial p 0) ξ).phase : ℝ)
      ∂(Measure.infinitePi fun _ : ℕ => Q)) / c.cycles ≤ c.h / (5 * c.s))
    (hWC : 10 * ((2 * (c.cycles : ℝ) / (max 1 c.epoch : ℕ) + 1) * (max 1 c.resetBatch : ℕ) +
      2 * c.cycles * (max 1 c.transportBatch : ℕ) + c.cycles * (detectorCalls c : ℝ)) ≤ C) :
    ((PMF.uniformOfFintype (Fin (max 1 c.cycles))).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => Q)).real
      {z | C < unpaddedWork p c g H 0 N z.2} ≤ 1 / 10 := by
  rw [joint_cap_event_probability]
  apply cap_failure_bound p c g hg H hH _ 0 N C hC hWC
  apply expected_unpaddedWork_bound p c g hg H hH Q 0 N hdone
  exact expected_virtualIndex_le_twice_cycles p c g hg H hH _ 0 N hT hs hMh hdone hacc

end LongTails.Proofs.HeavyTailedSospWorkIntegration
