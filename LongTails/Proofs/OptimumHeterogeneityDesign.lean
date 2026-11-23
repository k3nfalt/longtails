import LongTails.Algorithms.OptimumHeterogeneityDesign
import Mathlib.Tactic

namespace LongTails.Proofs.OptimumHeterogeneityDesign

open Set LongTails.Setups.DistributedOptimumHeterogeneity LongTails.Algorithms.OptimumHeterogeneityDesign

variable {p : Params}

lemma uniform_design (hp : spec.valid p) :
    (fun _ : Fin p.n => ((p.n : ℝ) * p.μ)⁻¹) ∈ designs p := by
  have hn : 0 < (p.n : ℝ) := by exact_mod_cast p.n.pos
  have hμ := hp.1.2.2.1
  have hm : 0 < (p.n : ℝ) * p.μ := mul_pos hn hμ
  refine ⟨fun _ => (inv_pos.mpr hm).le, ?_, ?_⟩
  · intro a ha
    rw [← Finset.mul_sum, ← div_eq_inv_mul]
    exact (one_le_div hm).mpr ha.2
  · unfold centeredEnergy
    simp [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hn.ne', sq_nonneg]

lemma closed_designs (p : Params) : IsClosed (designs p) := by
  have h₁ : IsClosed {w : Fin p.n → ℝ | ∀ i, 0 ≤ w i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h₂ : IsClosed {w : Fin p.n → ℝ | ∀ a ∈ admissibleCurvatures p, 1 ≤ ∑ i, w i * a i} := by
    simp only [ofPred_forall]
    refine isClosed_iInter fun a => isClosed_iInter fun _ => isClosed_le continuous_const ?_
    fun_prop
  have h₃ : Continuous (centeredEnergy p) := by unfold centeredEnergy; fun_prop
  exact h₁.inter (h₂.inter (isClosed_le (continuous_const.mul h₃) continuous_const))

lemma weights_optimal (hp : spec.valid p) :
    weights p ∈ designs p ∧ IsMinOn (cost p) (designs p) (weights p) := by
  let u := fun _ : Fin p.n => ((p.n : ℝ) * p.μ)⁻¹
  let M := cost p u
  let bound := fun i : Fin p.n => Real.sqrt (M / (p.h i : ℝ))
  have hh (i) : 0 < (p.h i : ℝ) := by exact_mod_cast hp.1.1 i
  have hc : Continuous (cost p) := by unfold cost; fun_prop
  have hbox (w) (hw : w ∈ designs p) (hM : cost p w ≤ M) : w ∈ Icc 0 bound := by
    refine ⟨hw.1, fun i => ?_⟩
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ (hh i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (s := Finset.univ) (f := fun j => (p.h j : ℝ) * w j ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)).trans hM
  have hu : u ∈ designs p := uniform_design hp
  obtain ⟨v, hv, hmin⟩ := (isCompact_Icc.inter_right (closed_designs p)).exists_isMinOn
    ⟨u, hbox u hu le_rfl, hu⟩ hc.continuousOn
  apply Classical.epsilon_spec (p := fun w => w ∈ designs p ∧ IsMinOn (cost p) (designs p) w)
  refine ⟨v, hv.2, ?_⟩
  apply isMinOn_iff.mpr
  intro w hw
  by_cases h : cost p w ≤ M
  · exact hmin ⟨hbox w hw h, hw⟩
  · exact (hmin ⟨hbox u hu le_rfl, hu⟩).trans (le_of_not_ge h)

end LongTails.Proofs.OptimumHeterogeneityDesign
