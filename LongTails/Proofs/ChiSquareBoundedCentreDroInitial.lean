import LongTails.Proofs.ChiSquareBoundedCentreDroExecution
import LongTails.Proofs.ChiSquareObjective

open MeasureTheory
namespace OracleTemplate.ChiSquareBoundedCentreDro
open ChiSquareDro LongTails.Setups.ChiSquareConstrainedDro

lemma initial_success (q : Params) (hq : spec.valid q) (I : Instance q)
    (O : Oracle q.E (q.E × ℝ × q.E)) (ha : spec.admissible q I O) (h : min q.B (q.G*q.R) ≤ q.ε) :
    spec.successful q I
      (fun w : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (algorithm q) (fun _ => 0) w.1 w.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hρ,hG,-,-,-⟩ := hq
  obtain ⟨proj,P,_,rfl,_,_,hx0,_,_,_,hm,_,hsub,hz,hg,xs,hxs,hmin,hR⟩ := ha
  have he : (fun w : (algorithm q).Seed × ((k : ℕ) → (sampleOracle I proj P).Seed k) =>
      execute (sampleOracle I proj P) (algorithm q) (fun _ => 0) w.1 w.2) = fun _ => q.x0 := by
    funext w
    refine (execution_eq q I proj P w.2 (show usedCalls q ≤ 0 by simp [usedCalls,h])).trans ?_
    simp [plan,h,interpret]
  change Measurable _ ∧ _ ∧ _
  rw [he]
  let μ : ProbabilityMeasure ((algorithm q).Seed × ((k : ℕ) → (sampleOracle I proj P).Seed k)) :=
    ⟨((algorithm q).law : Measure _).prod ((sampleOracle I proj P).law : Measure _), inferInstance⟩
  refine ⟨measurable_const, fun _ => hx0, xs, hxs, hmin, ?_, ?_⟩
  · change Integrable (fun _ => objective I q.x0 - objective I xs) μ.toMeasure
    exact integrable_const _
  change (∫ _, objective I q.x0 - objective I xs ∂μ.toMeasure) ≤ q.ε
  simp only [integral_const, probReal_univ, one_smul]
  have hm' (x : q.E) : Measurable (I.loss x) := hm.comp (measurable_const.prodMk measurable_id)
  apply le_trans _ h
  apply le_min
  · linarith [objective_le_bound I hρ.le (hm' _) (fun ω => (hz ω _ hx0).1) (fun ω => (hz ω _ hx0).2),
      objective_nonneg I hρ.le (hm' _) (fun ω => (hz ω _ hxs).1) (fun ω => (hz ω _ hxs).2)]
  · linarith [objective_lipschitz I hρ.le hm hsub hg hz hx0 hxs, mul_le_mul_of_nonneg_left hR hG.le]

end OracleTemplate.ChiSquareBoundedCentreDro
