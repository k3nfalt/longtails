import LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth
import LongTails.Proofs.MatrixGeneralizedExecution
import LongTails.Proofs.Execution
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.MatrixGeneralizedZO

open LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈Real.logb 2 (1 / q.δ)⌉₊ * (4 * ⌈510 * Real.sqrt (q.d * (q.r + 1) * q.L0 * q.R ^ 2 / q.ε) + 1300 * (q.r + 1 + q.L1 * q.R * Real.sqrt (q.d * (q.r + 1))) * Real.log (Real.exp 1 + 8 * q.Δ / q.ε)⌉₊ + 1)

lemma budget_eq (p : Params) : budget p 0 = runLength (iterations p) * numRuns p := by
  rw [runLength_eq, mul_comm]
  rfl

theorem result : Convergence LongTails.Setups.ZerothOrderMatrixGeneralizedSmooth.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hadm
  obtain ⟨hans, hc, hg, hd, H, hsym, hcoer, hup, htr, hhess, xstar, hmin, hstart, hgap⟩ := hadm
  have hv := valid_of_spec hp
  have hδ : 0 < p.δ := hp.2.2.2.2.2.2.2.1
  have hδ1 : p.δ < 1 := hp.2.2.2.2.2.2.2.2
  have hG : Geometry H := ⟨hsym, hcoer, hup⟩
  have hB : HessBound f H p.L0 p.L1 := hhess
  have I : Inst p f H xstar :=
    ⟨hv, hG, htr, hc, hg, hd, hB.mono (L1_le_Lp (p := p)), hmin, hstart, hgap⟩
  let out := fun seed : Seeds p => QueryPlan.eval f (fullPlan p seed)
  have hexec (seed : Seeds p) (ξ : (k : ℕ) → O.Seed k) :
      execute O (algorithm p) (fun _ => (budget p 0)) seed ξ = out seed := by
    erw [execute_eq_of_answer_eq O f hans, budget_eq]
    exact QueryPlan.execute_plan _ _ _ _ _ f seed
  change spec.successful p f
      (fun seed => (execute O (algorithm p) (fun _ => (budget p 0)) seed.1 seed.2))
      ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure.prod
        (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩
  simp only [hexec]
  refine ⟨(measurable_from_top : Measurable out).comp measurable_fst, xstar, hmin, ?_⟩
  have hset : {ω : Seeds p × ((k : ℕ) → O.Seed k) | p.ε < f (out ω.1) - f xstar} =
      {seed : Seeds p | p.ε < f (out seed) - f xstar} ×ˢ Set.univ := by
    ext ω; simp
  change ((PMF.uniformOfFintype (Seeds p)).toMeasure.prod
      (O.law : Measure ((k : ℕ) → O.Seed k)))
      {ω : Seeds p × ((k : ℕ) → O.Seed k) | p.ε < f (out ω.1) - f xstar} ≤ ENNReal.ofReal p.δ
  rw [hset, Measure.prod_prod, measure_univ, mul_one, uniform_measure_eq]
  apply ENNReal.ofReal_le_ofReal
  set st0 : Point p.d × Point p.d × Point p.d := (p.x0, p.x0, p.x0)
  set F := fun t : Fin (iterations p) → Fin p.d → Bool =>
    if p.ε < f (traj p f (iterations p) 0 st0 t).1 - f xstar then (1 : ℝ) else 0
  have hN := numRuns_pos p hδ hδ1
  have hpoint : ∀ seed : Seeds p,
      (if p.ε < f (out seed) - f xstar then (1 : ℝ) else 0) ≤ ∏ j, F (seed j) := by
    intro seed
    split_ifs with hfail
    · have hall : ∀ j, F (seed j) = 1 := by
        intro j
        have hle := best_of_ofFn f p.x0 hN
          (fun j => QueryPlan.eval f (runPlan p (iterations p) 0 (p.x0, p.x0) (seed j)))
          (fun j => by rw [eval_runPlan p f (iterations p) 0 st0 (seed j)]) j
        rw [← eval_fullPlan] at hle
        rw [eval_runPlan p f (iterations p) 0 st0 (seed j)] at hle
        simp only [F]
        rw [ite_eq_left]
        change p.ε < f (QueryPlan.eval f (fullPlan p seed)) - f xstar at hfail
        linarith
      rw [Finset.prod_congr rfl (fun j _ => hall j), Finset.prod_const_one]
    · exact Finset.prod_nonneg fun j _ => by simp only [F]; split_ifs <;> norm_num
  have h1 := Finset.expect_le_expect (s := Finset.univ) (fun seed _ => hpoint seed)
  have h2 : (𝔼 seed : Seeds p, ∏ j, F (seed j)) = ∏ _j : Fin (numRuns p), (𝔼 t : Fin (iterations p) → Fin p.d → Bool, F t) :=
    expect_prod_indep (ι := Fin (numRuns p)) F
  have h3 : (𝔼 t : Fin (iterations p) → Fin p.d → Bool, F t) ≤ 1 / 2 := run_fail_prob I
  have h4 : 0 ≤ (𝔼 t : Fin (iterations p) → Fin p.d → Bool, F t) :=
    Finset.expect_nonneg fun t _ => by simp only [F]; split_ifs <;> norm_num
  have h5 : ∏ _j : Fin (numRuns p), (𝔼 t : Fin (iterations p) → Fin p.d → Bool, F t) ≤ (1 / 2 : ℝ) ^ numRuns p := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ h4 h3 (numRuns p)
  have h6 : (1 / 2 : ℝ) ^ numRuns p ≤ p.δ := half_pow_le_delta hδ
  calc (𝔼 seed : Seeds p, if p.ε < f (out seed) - f xstar then (1 : ℝ) else 0)
      ≤ 𝔼 seed : Seeds p, ∏ j, F (seed j) := h1
    _ = ∏ _j : Fin (numRuns p), (𝔼 t : Fin (iterations p) → Fin p.d → Bool, F t) := h2
    _ ≤ (1 / 2 : ℝ) ^ numRuns p := h5
    _ ≤ p.δ := h6

end OracleTemplate.MatrixGeneralizedZO
