import LongTails.Proofs.GradientOnlyQuasarTuning
import LongTails.Proofs.GradientOnlyQuasarExecution

open MeasureTheory Set Filter
open scoped RealInnerProductSpace

namespace OracleTemplate.GradientOnlyQuasar

open LongTails.Setups.GradientOnlyGeneralizedQuasar

lemma inaccurate_after_time {q : Params} (hv : spec.valid q) {f : q.E → ℝ} {u : q.E}
    {s : ℝ × q.E × q.E} (ht : stageStart q (stageCount q) ≤ s.1)
    (he : q.ε < f s.2.1 - f u) : 1 ≤ potential q f u s := by
  have htarget := stageWeight_target hv
  have hw := weight_after hv ht
  have hW := weight_pos hv s.1
  have henergy : energyLevel q ≤ weightedEnergy f u (weight q s.1) s.2.1 s.2.2 := by
    unfold weightedEnergy
    rw [← hw] at htarget
    have hh := mul_le_mul_of_nonneg_left he.le hW.le
    nlinarith [sq_nonneg ‖s.2.2 - u‖]
  have hratio : 1 ≤ weightedEnergy f u (weight q s.1) s.2.1 s.2.2 / energyLevel q := by
    exact (le_div_iff₀ (energyLevel_pos hv)).2 (by simpa using henergy)
  have hpow : 1 ≤ (weightedEnergy f u (weight q s.1) s.2.1 s.2.2 / energyLevel q) ^ momentOrder q :=
    one_le_pow₀ hratio
  exact (barrier_eq_one hpow).ge

lemma run_accuracy {q : Params} (hv : spec.valid q) {f : q.E → ℝ}
    (hf : ∀ y, HasGradientAt f (gradient f y) y) (hg : Continuous (gradient f))
    (hs : CompositeGeneralized.SymmetricSmooth (gradient f) q.L0 q.L1)
    {u : q.E} (hm : IsMinOn f univ u) (hR : ‖q.x0 - u‖ ≤ q.R)
    (hΔ : f q.x0 - f u ≤ q.Δ)
    (hq : ∀ y, q.γ * (f y - f u) ≤ ⟪gradient f y, y - u⟫) :
    (RelativeQuasar.samplesLaw (calls q) : Measure (Fin (calls q) → ℝ))
      {samples | q.ε < f (run q (gradient f) (calls q) (0, q.x0, q.x0) samples).2.1 - f u} ≤
      ENNReal.ofReal q.δ := by
  let V := fun samples => potential q f u (run q (gradient f) (calls q) (0, q.x0, q.x0) samples)
  have hδ := hv.2.2.2.2.2.2.2.1
  obtain ⟨hVi, hVe⟩ := run_potential_nonincrease hv hf hg hs hm hq (calls q) (0, q.x0, q.x0)
  have hb : (∫ samples, V samples ∂(RelativeQuasar.samplesLaw (calls q) : Measure _)) ≤ q.δ / 4 := by
    apply hVe.trans
    have hi := initial_potential_bound hv hm hR hΔ
    have hh := half_pow_momentOrder hv
    linarith
  have hbad : (RelativeQuasar.samplesLaw (calls q) : Measure (Fin (calls q) → ℝ))
      {samples | 1 ≤ V samples} ≤ ENNReal.ofReal (q.δ / 4) := by
    apply (hVi.measure_le_integral (Eventually.of_forall (fun samples => potential_nonneg hv hm _))
      (s := {samples | 1 ≤ V samples}) (fun _ hs => hs)).trans
    exact ENNReal.ofReal_le_ofReal hb
  have hsub : {samples | q.ε < f (run q (gradient f) (calls q) (0, q.x0, q.x0) samples).2.1 - f u} ⊆
      {samples | clockSum samples < stageStart q (stageCount q)} ∪ {samples | 1 ≤ V samples} := by
    intro samples he
    by_cases ht : clockSum samples < stageStart q (stageCount q)
    · exact Or.inl ht
    · apply Or.inr
      apply inaccurate_after_time hv _ he
      rw [run_clock]
      simpa only [zero_add] using le_of_not_gt ht
  calc
    _ ≤ (RelativeQuasar.samplesLaw (calls q) : Measure (Fin (calls q) → ℝ))
        ({samples | clockSum samples < stageStart q (stageCount q)} ∪ {samples | 1 ≤ V samples}) :=
      measure_mono hsub
    _ ≤ (RelativeQuasar.samplesLaw (calls q) : Measure (Fin (calls q) → ℝ))
        {samples | clockSum samples < stageStart q (stageCount q)} +
        (RelativeQuasar.samplesLaw (calls q) : Measure (Fin (calls q) → ℝ)) {samples | 1 ≤ V samples} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (q.δ / 8) + ENNReal.ofReal (q.δ / 4) := add_le_add (budget_clock_tail hv) hbad
    _ ≤ ENNReal.ofReal q.δ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)

end OracleTemplate.GradientOnlyQuasar
