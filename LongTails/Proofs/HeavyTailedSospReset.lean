import LongTails.Proofs.HeavyTailedSospExecution
import LongTails.Proofs.HeavyTailedFreshProcess

open MeasureTheory
open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSosp
open LongTails.Proofs.HeavyTailedSospExecution
open LongTails.Proofs.HeavyTailedProductProcess

namespace LongTails.Proofs.HeavyTailedSospReset

lemma resume_phase_irrelevant (p : Params) (c : Config) (s : State p)
    (ph : Phase p) (after : Resume p) :
    resume p c { s with phase := ph } after = resume p c s after := by
  cases after <;> simp only [resume, startCycle]

@[simp] lemma resume_estimate (p : Params) (c : Config) (s : State p) (after : Resume p) :
    (resume p c s after).estimate = s.estimate := by
  cases after <;> simp only [resume, startCycle]
  all_goals split_ifs <;> rfl

@[simp] lemma resume_point (p : Params) (c : Config) (s : State p) (after : Resume p) :
    (resume p c s after).point = s.point := by
  cases after <;> simp only [resume, startCycle]
  all_goals split_ifs <;> rfl

lemma resume_virtualIndex (p : Params) (c : Config) (s : State p) (after : Resume p) :
    (resume p c s after).virtualIndex = s.virtualIndex := by
  cases after <;> simp only [resume, startCycle]
  all_goals split_ifs <;> rfl

lemma reset_prefix (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (after : Resume p) (ξ : ℕ → Aux p c × p.Ω)
    (n : ℕ) (hn : n < max 1 c.resetBatch) :
    trajectory (sampleStep p c g H) n { s with phase := .reset 0 0 after } ξ =
      { s with phase := .reset n (∑ k ∈ Finset.range n, g s.point (ξ k).2) after } := by
  induction n with
  | zero => simp [trajectory]
  | succ n ih =>
    rw [trajectory_succ_last, ih (by omega)]
    simp [sampleStep, query, update, hn, Finset.sum_range_succ]

lemma reset_complete (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (after : Resume p) (ξ : ℕ → Aux p c × p.Ω) :
    trajectory (sampleStep p c g H) (max 1 c.resetBatch)
      { s with phase := .reset 0 0 after } ξ =
      resume p c { s with
        estimate := ((max 1 c.resetBatch : ℕ) : ℝ)⁻¹ •
          (∑ k ∈ Finset.range (max 1 c.resetBatch), g s.point (ξ k).2)
        phase := .reset (max 1 c.resetBatch - 1)
          (∑ k ∈ Finset.range (max 1 c.resetBatch - 1), g s.point (ξ k).2) after } after := by
  have hb : max 1 c.resetBatch - 1 + 1 = max 1 c.resetBatch := by omega
  conv_lhs => rw [← hb, trajectory_succ_last]
  rw [reset_prefix p c g H s after ξ _ (by omega)]
  simp only [sampleStep, query, update, hb, lt_self_iff_false, ↓reduceIte]
  congr 2
  rw [← Finset.sum_range_succ, hb]

lemma reset_complete_estimate (p : Params) (c : Config)
    (g : Space p → p.Ω → Space p) (H : Space p → p.Ω → Space p →L[ℝ] Space p)
    (s : State p) (after : Resume p) (ξ : ℕ → Aux p c × p.Ω) :
    (trajectory (sampleStep p c g H) (max 1 c.resetBatch)
      { s with phase := .reset 0 0 after } ξ).estimate =
      ((max 1 c.resetBatch : ℕ) : ℝ)⁻¹ •
        (∑ k ∈ Finset.range (max 1 c.resetBatch), g s.point (ξ k).2) := by
  rw [reset_complete, resume_estimate]

lemma batch_error_identity (p : Params) (n : ℕ) (hn : 0 < n)
    (v : ℕ → Space p) (μ : Space p) :
    (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, v k) - μ =
      (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (v k - μ)) := by
  rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_range]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_smul]

lemma reset_batch_moment (p : Params) (P : Measure p.Ω) [IsProbabilityMeasure P]
    (g : p.Ω → Space p) (μ : Space p) (hg : Measurable g)
    {α κ : ℝ} (hα : 1 ≤ α) (hα2 : α ≤ 2)
    (hi : Integrable (fun ω => g ω - μ) P)
    (hm : (∫ ω, g ω - μ ∂P) = 0)
    (hpi : Integrable (fun ω => ‖g ω - μ‖ ^ α) P)
    (hb : (∫ ω, ‖g ω - μ‖ ^ α ∂P) ≤ κ) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ => ‖(n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, g (ξ k)) - μ‖ ^ α)
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, ‖(n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, g (ξ k)) - μ‖ ^ α
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 6 * κ / (n : ℝ) ^ (α - 1) := by
  simp_rw [batch_error_identity p n hn]
  exact HeavyTailedFreshProcess.iid_batch_moment P (hg.sub measurable_const)
    hα hα2 hi hm hpi hb n hn

lemma reset_execution_moment (p : Params) (c : Config) (P : Measure p.Ω)
    [IsProbabilityMeasure P] (g : Space p → p.Ω → Space p)
    (H : Space p → p.Ω → Space p →L[ℝ] Space p) (s : State p) (after : Resume p)
    (μ : Space p) (hg : Measurable (g s.point))
    {α κ : ℝ} (hα : 1 ≤ α) (hα2 : α ≤ 2)
    (hi : Integrable (fun ω => g s.point ω - μ) P)
    (hm : (∫ ω, g s.point ω - μ ∂P) = 0)
    (hpi : Integrable (fun ω => ‖g s.point ω - μ‖ ^ α) P)
    (hb : (∫ ω, ‖g s.point ω - μ‖ ^ α ∂P) ≤ κ) :
    let Q := (auxLaw p c).toMeasure.prod P
    let err := fun ξ => (trajectory (sampleStep p c g H) (max 1 c.resetBatch)
      { s with phase := .reset 0 0 after } ξ).estimate - μ
    Integrable (fun ξ => ‖err ξ‖ ^ α) (Measure.infinitePi fun _ : ℕ => Q) ∧
      (∫ ξ, ‖err ξ‖ ^ α ∂Measure.infinitePi (fun _ : ℕ => Q)) ≤
        6 * κ / ((max 1 c.resetBatch : ℕ) : ℝ) ^ (α - 1) := by
  intro Q err
  have hproj : MeasurePreserving (Prod.snd : Aux p c × p.Ω → p.Ω) Q P :=
    measurePreserving_snd
  have he : Measurable (fun ω => g s.point ω - μ) := hg.sub measurable_const
  have hmean : (∫ z : Aux p c × p.Ω, g s.point z.2 - μ ∂Q) = 0 := by
    rw [← hm, ← hproj.map_eq]
    exact (integral_map hproj.measurable.aemeasurable he.aestronglyMeasurable).symm
  have hmoment : (∫ z : Aux p c × p.Ω, ‖g s.point z.2 - μ‖ ^ α ∂Q) ≤ κ := by
    have heq : (∫ z : Aux p c × p.Ω, ‖g s.point z.2 - μ‖ ^ α ∂Q) =
        (∫ ω, ‖g s.point ω - μ‖ ^ α ∂P) := by
      rw [← hproj.map_eq]
      exact (integral_map hproj.measurable.aemeasurable
        (he.norm.pow_const α).aestronglyMeasurable).symm
    exact heq.trans_le hb
  dsimp only [err]
  simp_rw [reset_complete_estimate, batch_error_identity p (max 1 c.resetBatch) (by omega)]
  exact HeavyTailedFreshProcess.iid_batch_moment Q (he.comp measurable_snd) hα hα2
    (hproj.integrable_comp_of_integrable hi) hmean
    (hproj.integrable_comp_of_integrable hpi) hmoment _ (by omega)

end LongTails.Proofs.HeavyTailedSospReset
