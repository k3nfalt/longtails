import LongTails.Algorithms.HeavyTailedPLHessian
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.PLHessianConvergence
import LongTails.Proofs.RobustPLBlocks
import LongTails.Proofs.IIDBlocks

open MeasureTheory

namespace OracleTemplate.HeavyTailedPLHessian

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma sgdSeq_eq_iterate (g : E → Ω → E) (η τ : ℝ) (x0 : E)
    (ξ : ℕ → Fin 65 → Ω) : ∀ k,
    PLHessian.sgdSeq (fun x block => flatEstimate τ (fun i => g x (block i))) η x0 ξ k =
      iterate g η τ x0 ξ k
  | 0 => rfl
  | k + 1 => by
      simp only [PLHessian.sgdSeq, iterate, MarkovQuadratic.iterate]
      rw [sgdSeq_eq_iterate g η τ x0 ξ k]
      rfl

lemma execute_method (P : ProbabilityMeasure (ℕ → Ω))
    (Q : ProbabilityMeasure (ℕ → Fin 65 → Ω)) (g : E → Ω → E)
    (η τ : ℝ) (n m K : ℕ) (x0 : E) (seed : Fin (m + 1)) (ξ : ℕ → Ω) (hK : n + m ≤ K) :
    execute (PLHessian.winOracle g P) (method η τ n m x0) (fun _ => K * 65) seed ξ =
      output g η τ x0 n m seed (fun k i => ξ (k * 65 + i.val)) := by
  let G := fun x (block : Fin 65 → Ω) => flatEstimate τ (fun i => g x (block i))
  let blocks := fun k (i : Fin 65) => ξ (k * 65 + i.val)
  have he : execute (PLHessian.winOracle g P) (method η τ n m x0) (fun _ => K * 65) seed ξ =
      execute (PLHessian.winOracle G Q) (WindowSgd.method η n m x0) (fun _ => K) seed blocks := by
    have h1 := execute_batched (by norm_num : 0 < 65) (WindowSgd.method η n m x0)
      (fun state _ => state.2.2) (fun _ replies => flatEstimate τ replies) 0 P g ξ K seed
    have h2 := StochasticGradient.execute_advance Q G (WindowSgd.method η n m x0) K seed blocks
    exact h1.trans h2.symm
  rw [he, PLHessian.execute_window G Q η n m x0 K seed blocks hK]
  exact sgdSeq_eq_iterate g η τ x0 blocks (n + seed.val)

lemma iid_output_integral [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : ProbabilityTheory.iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ => ξ k) = p)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    {f : E → ℝ} (hf : Continuous f) (u x0 : E) (η τ : ℝ) (n m : ℕ) :
    (∫⁻ ω : Fin (m + 1) × (ℕ → Ω), ENNReal.ofReal
      (f (output g η τ x0 n m ω.1 (fun k i => ω.2 (k * 65 + i.val))) - f u)
      ∂((PMF.uniformOfFintype (Fin (m + 1))).toMeasure.prod P)) =
    ∫⁻ ω : Fin (m + 1) × (ℕ → Fin 65 → Ω), ENNReal.ofReal
      (f (PLHessian.sgdSeq (fun x block => flatEstimate τ (fun i => g x (block i)))
        η x0 ω.2 (n + ω.1.val)) - f u)
      ∂((PMF.uniformOfFintype (Fin (m + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin 65 => p)) := by
  let G := fun x (block : Fin 65 → Ω) => flatEstimate τ (fun i => g x (block i))
  have hG : Measurable (Function.uncurry G) := measurable_sampledReply hg τ
  have hm : Measurable (fun ω : Fin (m + 1) × (ℕ → Fin 65 → Ω) =>
      ENNReal.ofReal (f (PLHessian.sgdSeq G η x0 ω.2 (n + ω.1.val)) - f u)) :=
    ENNReal.measurable_ofReal.comp
      ((hf.measurable.comp (PLHessian.measurable_window_out hG η n m x0)).sub_const _)
  have hb := FiniteVariance.infinite_block_law p P hind hmarg 65
  have he := ((MeasurePreserving.id
    (PMF.uniformOfFintype (Fin (m + 1))).toMeasure).prod hb).lintegral_comp hm
  simpa only [Prod.map, Function.comp_def, id_eq, G, sgdSeq_eq_iterate, output] using he

lemma measurable_output [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (η τ : ℝ) (x0 : E) (n m : ℕ) :
    Measurable (fun ω : Fin (m + 1) × (ℕ → Ω) =>
      output g η τ x0 n m ω.1 (fun k i => ω.2 (k * 65 + i.val))) := by
  have hG : Measurable (Function.uncurry (fun x (block : Fin 65 → Ω) =>
      flatEstimate τ (fun i => g x (block i)))) := measurable_sampledReply hg τ
  have hm := PLHessian.measurable_window_out hG η n m x0
  have hb : Measurable (fun ω : Fin (m + 1) × (ℕ → Ω) =>
      (ω.1, fun k (i : Fin 65) => ω.2 (k * 65 + i.val))) := by fun_prop
  have hh := hm.comp hb
  simpa only [Function.comp_def, sgdSeq_eq_iterate, output] using hh

end OracleTemplate.HeavyTailedPLHessian
