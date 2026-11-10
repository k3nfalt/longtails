import LongTails.Proofs.ParameterFreeNsgdmRunBound

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.ParameterFreeNsgdmSelection

open ParameterFreeNsgdmRun ParameterFreeNsgdmRunBound

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma selected_le {C : ℕ} (y est : Fin C → E) (grad : E → E) (sel c : Fin C)
    (hsel : ∀ c', ‖est sel‖ ≤ ‖est c'‖) :
    ‖grad (y sel)‖ ≤ ‖grad (y c)‖ + ‖est c - grad (y c)‖ + ‖est sel - grad (y sel)‖ := by
  have h1 : ‖grad (y sel)‖ ≤ ‖est sel‖ + ‖est sel - grad (y sel)‖ := by
    have := norm_sub_le (est sel) (est sel - grad (y sel))
    simpa using this
  have h2 : ‖est c‖ ≤ ‖grad (y c)‖ + ‖est c - grad (y c)‖ := by
    have := norm_add_le (grad (y c)) (est c - grad (y c))
    simpa using this
  linarith [hsel c]

lemma rpow_le_root_sum {C : ℕ} {p : ℝ} (hp : 1 ≤ p) (e : Fin C → ℝ) (he : ∀ c, 0 ≤ e c) (c : Fin C) :
    e c ≤ (∑ c', e c' ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h1 : e c ^ p ≤ ∑ c', e c' ^ p :=
    Finset.single_le_sum (fun c' _ => Real.rpow_nonneg (he c') p) (Finset.mem_univ c)
  calc e c = (e c ^ p) ^ (1 / p) := by
        rw [← Real.rpow_mul (he c), mul_one_div_cancel hp0.ne', Real.rpow_one]
    _ ≤ (∑ c', e c' ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (he c) p) h1 (by positivity)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma selected_le_root {C : ℕ} {p : ℝ} (hp : 1 ≤ p) (y est : Fin C → E) (grad : E → E)
    (sel c : Fin C) (hsel : ∀ c', ‖est sel‖ ≤ ‖est c'‖) :
    ‖grad (y sel)‖ ≤ ‖grad (y c)‖ + ‖est c - grad (y c)‖ +
      (∑ c', ‖est c' - grad (y c')‖ ^ p) ^ (1 / p) := by
  have h := selected_le y est grad sel c hsel
  have h2 := rpow_le_root_sum hp (fun c' => ‖est c' - grad (y c')‖) (fun _ => norm_nonneg _) sel
  linarith

variable {ν : Measure Ω} [IsProbabilityMeasure ν] {g : E → Ω → E} {grad : E → E} {σ p : ℝ}

noncomputable def batchMean (g : E → Ω → E) (T off : ℕ) (x : E) (ξ : ℕ → Ω) : E :=
  ((T : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range T, g x (ξ (off + i))

lemma shift_preserving (off : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun i => ξ (off + i))
      (Measure.infinitePi fun _ : ℕ => ν) (Measure.infinitePi fun _ : ℕ => ν) :=
  measurePreserving_snd.comp (OracleTemplate.StochasticGeneralized.splitStream_preserving ν off)

lemma batchMean_moment (hO : Oracle ν g grad σ p) (hp : 1 ≤ p)
    (hp2 : p ≤ 2) {T : ℕ} (hT : 0 < T) (off : ℕ) (x : E) :
    Integrable (fun ξ : ℕ → Ω => ‖batchMean g T off x ξ - grad x‖ ^ p)
      (Measure.infinitePi fun _ : ℕ => ν) ∧
    (∫ ξ, ‖batchMean g T off x ξ - grad x‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => ν)) ≤
      6 * σ ^ p / (T : ℝ) ^ (p - 1) := by
  have he_meas : Measurable (fun ω => g x ω - grad x) := by
    have h1 : Measurable (fun ω : Ω => g x ω) := by
      have := hO.measurable.comp (measurable_const.prodMk measurable_id : Measurable fun ω : Ω => (x, ω))
      exact this
    exact h1.sub measurable_const
  have hb := HeavyTailedFreshProcess.iid_batch_moment ν
    (e := fun ω => g x ω - grad x) he_meas hp hp2 ((hO.integrable x).sub (integrable_const _))
    (by rw [integral_sub (hO.integrable x) (integrable_const _), hO.unbiased, integral_const]; simp)
    (hO.moment_integrable x) (hO.moment x) T hT
  have heq : (fun ξ : ℕ → Ω => ‖batchMean g T off x ξ - grad x‖ ^ p) =
      (fun ξ : ℕ → Ω => ‖((T : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range T, (g x (ξ k) - grad x)‖ ^ p) ∘
        (fun ξ : ℕ → Ω => fun i => ξ (off + i)) := by
    funext ξ
    simp only [Function.comp_apply, batchMean]
    congr 2
    have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hT', one_smul]
  have hshift := shift_preserving (ν := ν) off
  have hae : AEStronglyMeasurable
      (fun ξ : ℕ → Ω => ‖((T : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range T, (g x (ξ k) - grad x)‖ ^ p)
      (Measure.map (fun ξ : ℕ → Ω => fun i => ξ (off + i)) (Measure.infinitePi fun _ : ℕ => ν)) := by
    rw [hshift.map_eq]; exact hb.1.aestronglyMeasurable
  have hmap := integral_map (μ := Measure.infinitePi fun _ : ℕ => ν)
    hshift.measurable.aemeasurable hae
  rw [hshift.map_eq] at hmap
  rw [heq]
  refine ⟨hshift.integrable_comp_of_integrable hb.1, le_of_eq_of_le ?_ hb.2⟩
  exact hmap.symm

end LongTails.Proofs.ParameterFreeNsgdmSelection
