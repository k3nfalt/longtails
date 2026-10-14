import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveEntropicRun
import LongTails.Proofs.AdaptiveEntropicBudget
import LongTails.Proofs.AdaptiveEntropicGuarantee

open MeasureTheory

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma execution_epsilon_iid (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (ν : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) (ν : Measure _) (P : Measure _))
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {f : Vector q.d → ℝ} (hL : 0 < q.L) (hδ : 0 < q.δ) (hδ1 : q.δ < 1)
    (hf : ConvexOn ℝ (simplex q.d) f)
    (hgrad : ∀ x ∈ simplex q.d, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ simplex q.d, ∀ y ∈ simplex q.d,
      dualNorm (gradient f x - gradient f y) ≤ q.L * oneNorm (x - y))
    {σ ε p : ℝ} (hσ : 0 ≤ σ) (hε : 0 < ε) (hp : 1 < p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - gradient f x) ^ p) (ν : Measure _))
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - gradient f x) ^ p ∂(ν : Measure _)) ≤ σ ^ p)
    (hgi : ∀ x, Integrable (g x) (ν : Measure _))
    (hgu : ∀ x, (∫ ω, g x ω ∂(ν : Measure _)) = gradient f x)
    (N : ℕ) (xstar : simplex q.d)
    (hN : 256 * confidence q + 67108864 * Real.sqrt
      ((q.L * (Real.log (2 * (q.d : ℝ)) + confidence q) / ε) *
        (confidence q + Real.log (2 + q.L * (Real.log (2 * (q.d : ℝ)) + confidence q) / ε))) +
      4 * (Real.log (2 * (q.d : ℝ)) + confidence q) *
        (274877906944 * σ / ε) ^ (p / (p - 1)) ≤ (N : ℝ)) :
    ((Measure.dirac ()).prod (P : Measure _)) {w : Unit × (ℕ → Ω) |
      ε < f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (query : Fin 1 × simplex q.d) seed => g query.2 seed }
        (algorithm q) (fun _ => N) w.1 w.2 : simplex q.d) - f xstar} ≤ ENNReal.ofReal q.δ := by
  let T := (N - preload q) / 2
  have ht := budget_accuracy q hL hδ hδ1 hσ hε hp N hN
  have hT : 0 < T := ht.1
  have hn : preload q ≤ N := by dsimp [T] at hT; omega
  have hrate := objective_rate_tail q hg hL hδ hδ1 hf hgrad hlip hσ hp.le hp2
    hi hm hgi hgu T hT xstar
  have hPlaw : (P : Measure _) = Measure.infinitePi (fun _ : ℕ => (ν : Measure Ω)) := by
    have h := hIID.stream_law.map_eq
    change (P : Measure (ℕ → Ω)).map id = _ at h
    simpa only [Measure.map_id] using h
  have hpraw : (P : Measure _) {ξ | ε < f (macroState q g ξ T).y - f xstar} ≤ ENNReal.ofReal q.δ := by
    rw [hPlaw]
    apply le_trans (measure_mono ?_) hrate
    intro ξ hξ
    exact lt_of_le_of_lt ht.2 hξ
  have hobj : Measurable (fun ξ : ℕ → Ω => f (macroState q g ξ T).y - f xstar) :=
    ((measurable_restricted_objective hgrad).comp (measurable_macro_output q hg T)).sub_const _
  have hsnd : ProbabilityTheory.HasLaw (Prod.snd : Unit × (ℕ → Ω) → ℕ → Ω) (P : Measure _)
      ((Measure.dirac ()).prod (P : Measure _)) :=
    ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
  have he : {w : Unit × (ℕ → Ω) |
      ε < f (execute { Seed := fun _ => Ω, law := P, answer := fun _ (query : Fin 1 × simplex q.d) seed => g query.2 seed }
        (algorithm q) (fun _ => N) w.1 w.2 : simplex q.d) - f xstar} =
      {w : Unit × (ℕ → Ω) | ε < f (macroState q g w.2 T).y - f xstar} := by
    ext w
    cases w.1
    simp only [Set.mem_ofPred_eq, execute_macro_output q g P N hn]
    rfl
  rw [he, hsnd.measure_eq (measurableSet_lt measurable_const hobj)]
  exact hpraw

lemma convergence_of_call_budget (budget : Params → ℕ)
    (hbudget : ∀ p : Params, spec.valid p →
      256 * confidence p.toPublic + 67108864 * Real.sqrt
        ((p.L * (Real.log (2 * (p.d : ℝ)) + confidence p.toPublic) / p.ε) *
          (confidence p.toPublic + Real.log (2 + p.L *
            (Real.log (2 * (p.d : ℝ)) + confidence p.toPublic) / p.ε))) +
        4 * (Real.log (2 * (p.d : ℝ)) + confidence p.toPublic) *
          (274877906944 * p.σ / p.ε) ^ (p.p / (p.p - 1)) ≤ (budget p : ℝ)) :
    Convergence spec (fun p _ => budget p) := by
  apply OracleTemplate.convergence_of_call_budget (S := spec) budget
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp N hN f O ho
  rcases hp with ⟨hL, hδ, hδ1, hpp, hpp2, hσ, hε⟩
  rcases ho with ⟨g, ν, P, hIID, rfl, hf, hgrad, hlip, hmin, hg, hgi, hgu, hi, hm⟩
  rcases hmin with ⟨u, hu, hmin⟩
  have hn := (hbudget p ⟨hL, hδ, hδ1, hpp, hpp2, hσ, hε⟩).trans (Nat.cast_le.mpr hN)
  constructor
  · exact measurable_execute_output p.toPublic P g hg N
  · refine ⟨u, hu, hmin, ?_⟩
    exact execution_epsilon_iid p.toPublic ν P hIID hg hL hδ hδ1 hf hgrad hlip hσ hε
      hpp hpp2 hi hm hgi hgu N ⟨u, hu⟩ hn

end OracleTemplate.AdaptiveHeavyTailSimplex
