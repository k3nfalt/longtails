import LongTails.Proofs.CovarianceAcceleratedExecution
import LongTails.Proofs.CovarianceAcceleratedSelection
import LongTails.Proofs.MultiplicativeRobustMedoid

open MeasureTheory Convexity
open LongTails.Algorithms.CovarianceAccelerated
open LongTails.Algorithms.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedSelection

namespace LongTails.Proofs.CovarianceAcceleratedMeasurable

noncomputable local instance simplexMeasurableSpace (n : ℕ) : MeasurableSpace (StdSimplex ℝ (Fin n)) := borel _
local instance (n : ℕ) : BorelSpace (StdSimplex ℝ (Fin n)) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (StdSimplex ℝ (Fin n)) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin n)).secondCountableTopology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ} (c : Config E n)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_push {k : ℕ} :
    Measurable (fun q : (Fin (k + 1) → E) × E => push q.1 q.2) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_snd
  · exact (measurable_pi_apply j.castSucc).comp measurable_fst

lemma measurable_query : Measurable (query c) := by
  apply measurable_from_prod_countable_right
  intro N
  by_cases hN : N < c.window + 1
  · simpa only [query, hN, ite_true] using
      (measurable_const : Measurable (fun _ : E × StdSimplex ℝ (Fin n) ×
        (Fin (c.window + 1) → E) => c.x0))
  · simp only [query, hN, ite_false]
    have hm := (mean_continuous c.centers).measurable.comp
      (measurable_snd.fst : Measurable (fun r : E × StdSimplex ℝ (Fin n) ×
        (Fin (c.window + 1) → E) => r.2.1))
    unfold couple
    fun_prop

lemma measurable_advance (hβ : 0 ≤ c.β) (hγ : 0 < c.γ)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖c.centers i‖ ≤ M) :
    Measurable (Function.uncurry (advance c)) := by
  have hh : Measurable (fun q : (E × StdSimplex ℝ (Fin n) × (Fin (c.window + 1) → E)) × E =>
      OracleTemplate.MultiplicativeRobustEstimator.medoid q.1.2.2) :=
    OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp (by fun_prop)
  have hpush : Measurable (fun q : (E × StdSimplex ℝ (Fin n) × (Fin (c.window + 1) → E)) × E => push q.1.2.2 q.2) :=
    (measurable_push (E := E) (k := c.window)).comp
      (measurable_fst.snd.snd.prodMk measurable_snd)
  have hf : Measurable (fun q : ℕ × ((E × StdSimplex ℝ (Fin n) × (Fin (c.window + 1) → E)) × E) => advance c (q.1, q.2.1) q.2.2) := by
    apply measurable_from_prod_countable_right
    intro N
    by_cases hN : N < c.window + 1
    · simp only [advance, hN, ite_true]
      exact measurable_const.prodMk (measurable_fst.fst.prodMk
        (measurable_fst.snd.fst.prodMk hpush))
    · simp only [advance, hN, ite_false]
      have hp := (step_continuous c.centers c.x0 c.a (weight c.η (N - (c.window + 1)))
        c.β c.γ hβ hγ hM hz).measurable.comp
        (measurable_fst.snd.fst.prodMk (hh.prodMk measurable_snd))
      have hm := (mean_continuous c.centers).measurable.comp hp
      have hy : Measurable (fun q : (E × StdSimplex ℝ (Fin n) × (Fin (c.window + 1) → E)) × E =>
          couple (cumulative c.η (N - (c.window + 1))) (weight c.η (N - (c.window + 1))) q.1.1
            (c.x0 + c.a • mean c.centers
              (step c.centers c.x0 c.a (weight c.η (N - (c.window + 1))) c.β c.γ q.1.2.1
                (OracleTemplate.MultiplicativeRobustEstimator.medoid q.1.2.2) q.2))) := by
        unfold couple
        fun_prop
      exact measurable_const.prodMk (hy.prodMk (hp.prodMk hpush))
  exact hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

lemma measurable_trajectory {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (hβ : 0 ≤ c.β) (hγ : 0 < c.γ)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖c.centers i‖ ≤ M) (N : ℕ) :
    Measurable (fun ξ : ℕ → Ω => trajectory c g ξ N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    have hr := hg.comp (((measurable_query c).comp ih).prodMk (measurable_pi_apply N))
    exact (measurable_advance c hβ hγ hM hz).comp (ih.prodMk hr)

lemma measurable_output {Ω : Type*} [MeasurableSpace Ω] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (hβ : 0 ≤ c.β) (hγ : 0 < c.γ)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖c.centers i‖ ≤ M) (N : ℕ) :
    Measurable (fun ξ : ℕ → Ω => output c g ξ N) :=
  (measurable_trajectory c hg hβ hγ hM hz N).snd.fst

end LongTails.Proofs.CovarianceAcceleratedMeasurable
