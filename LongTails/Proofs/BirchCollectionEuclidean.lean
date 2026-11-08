import LongTails.Proofs.BirchCollectionEuclideanTrace
import LongTails.Theorems.BirchSgd

namespace LongTails.Proofs.BirchCollectionEuclidean

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open OracleTemplate.BirchSgd (Tree gradientOracle branch_mono execute_birch birch_success main_theorem
  stepSize stepSize_facts horizon birch)
open LongTails.Setups.BirchSgd (Params spec publicInput)
open LongTails.Algorithms.BirchCollectionEuclidean (native prefixProgram prefixAlgorithm algorithm
  vertexReg trace)
open LongTails.Proofs.BirchCollectionEuclideanTrace
open LongTails.Proofs.BirchNonEuclideanExecution (interpret execute_interpret)

lemma prefix_calls (p : Params) (K : ℕ) : (prefixProgram p K).oracleCalls = p.branch K :=
  program_calls p.tree (publicInput p).gamma p.branch (p.branch K) K

lemma prefix_legal (p : Params) (hp : spec.valid p) (K : ℕ) :
    (prefixProgram p K).Legal 1 := by
  obtain ⟨hL, hσ, hε, _, hR, hT, hm, _, _⟩ := hp
  have hγ := (stepSize_facts p.L p.σ p.ε p.R hL hσ hε hR).1.le
  exact program_legal p.tree _ p.branch (p.branch K) K hT hγ
    (fun i hi => branch_mono p.tree hT p.branch hm i K hi)

lemma execute_vertex {Ω : Type} [MeasurableSpace Ω] (p : Params) (K : ℕ)
    (hT : p.tree.WellFormed) (hm : p.tree.IsMainBranch p.branch)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Point p.d)
    (i : Fin (K + 1)) (ξ : ℕ → Ω) :
    execute (gradientOracle P g) (prefixAlgorithm p K) (fun _ => p.branch K) i ξ =
      p.tree.vertex (publicInput p).gamma p.x0 g ξ (p.branch i.val) := by
  let a := prefixProgram p K
  change execute (gradientOracle P g)
    (LongTails.Setups.BirchNonEuclidean.programAlgorithm (native p) a (fun _ => 0))
    (fun _ => p.branch K) i ξ = _
  have ha : a.oracleCalls = p.branch K := prefix_calls p K
  rw [← ha]
  apply (execute_interpret (native p) a (fun _ => 0) P g ξ i).trans
  exact (trace_replay (native p) p.tree (publicInput p).gamma g ξ (p.branch K) hT).point _
    (branch_mono p.tree hT p.branch hm _ _ (Nat.lt_succ_iff.mp i.isLt))

lemma execute_eq_birch {Ω : Type} [MeasurableSpace Ω] (p : Params) (hp : spec.valid p)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Point p.d)
    (i : (algorithm p).Seed) (ξ : ℕ → Ω) :
    execute (gradientOracle P g) (algorithm p) (fun _ => OracleTemplate.BirchSgd.budget p 0) i ξ =
    execute (gradientOracle P g) (birch (publicInput p))
      (fun _ => OracleTemplate.BirchSgd.budget p 0) i ξ := by
  obtain ⟨_, _, _, _, _, hT, hm, _, _⟩ := hp
  exact (execute_vertex p _ hT hm P g i ξ).trans (execute_birch (publicInput p) hT hm P g i ξ).symm

lemma recovered_calls (p : Params) :
    (prefixProgram p (publicInput p).K).oracleCalls = OracleTemplate.BirchSgd.budget p 0 :=
  prefix_calls p _

lemma recovered_success (p : Params) (hp : spec.valid p) (I : Instance p.d)
    (O : Oracle (Point p.d) (Point p.d)) (hO : spec.admissible p I O) :
    spec.successful p I
      (fun z : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (algorithm p) (fun _ => OracleTemplate.BirchSgd.budget p 0) z.1 z.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hb := birch_success p hp I O hO
  obtain ⟨_, _, _, Ω, mΩ, μ, P, g, _, _, _, rfl⟩ := hO
  let := mΩ
  have he : (fun z : (algorithm p).Seed × (ℕ → Ω) =>
      execute (gradientOracle P g) (algorithm p) (fun _ => OracleTemplate.BirchSgd.budget p 0)
        z.1 z.2) = fun z =>
      execute (gradientOracle P g) (birch (publicInput p))
        (fun _ => OracleTemplate.BirchSgd.budget p 0) z.1 z.2 := by
    funext z
    exact execute_eq_birch p hp P g z.1 z.2
  change Measurable _ ∧ Integrable _ _ ∧ _ at hb ⊢
  erw [he]
  exact hb

lemma paper_prefix_rate {Ω : Type} [MeasurableSpace Ω] (p : Params) (hp : spec.valid p)
    (I : Instance p.d) (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d)
    (hsmooth : LongTails.Setups.BirchSgd.SmoothObjective I.f p.L)
    (hlower : LongTails.Setups.BirchSgd.LowerBounded I.f I.lower)
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
      (μ : Measure Ω) I.f g p.σ)
    (hlaw : ∀ c, (P : Measure (ℕ → Ω)).map (fun ξ => ξ c) = (μ : Measure Ω))
    (hind : LongTails.Setups.BirchSgd.SampleIndependent p.tree p.branch (publicInput p).gamma p.x0 g
      (P : Measure (ℕ → Ω))) (K : ℕ)
    (hK : 4 * (p.R + 1) * p.L * (I.f p.x0 - I.lower) / p.ε +
      8 * p.σ ^ 2 * p.L * (I.f p.x0 - I.lower) / p.ε ^ 2 ≤ K) :
    1 / (K : ℝ) * ∑ k ∈ Finset.range K,
      ∫ ξ, ‖gradient I.f
        (if hk : k < K + 1 then
          execute (gradientOracle P g) (prefixAlgorithm p K) (fun _ => p.branch K) ⟨k, hk⟩ ξ
        else p.x0)‖ ^ 2 ∂(P : Measure (ℕ → Ω)) ≤ p.ε := by
  classical
  obtain ⟨hL, hσ, hε, _, hR, hT, hm, hrepr, hdist⟩ := hp
  have ha := (main_theorem I.f p.L p.σ p.ε p.R I.lower p.x0 p.tree p.branch μ P g
    hL hσ hε hR hsmooth hlower hg hlaw hT hm hind hrepr hdist K hK).2
  convert ha using 2
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < K + 1 := (Finset.mem_range.mp hk).trans (Nat.lt_succ_self _)
  simp only [dite_eq_left hk']
  apply integral_congr_ae
  filter_upwards [] with ξ
  exact congrArg (fun v : Point p.d => ‖gradient I.f v‖ ^ 2)
    (execute_vertex p K hT hm P g ⟨k, hk'⟩ ξ)

end LongTails.Proofs.BirchCollectionEuclidean
