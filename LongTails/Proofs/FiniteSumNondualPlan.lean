import LongTails.Proofs.FiniteSumNondualBudget
import LongTails.Proofs.FiniteSumNondualPhase
import LongTails.Proofs.FiniteSumNondualExecution

open Set Classical
open scoped BigOperators

namespace LongTails.Proofs.FiniteSumNondualPlan

open LongTails.Setups.FiniteSumNondualSmoothConvex
open LongTails.Algorithms.FiniteSumNondual LongTails.Algorithms.FiniteSumNondualProx
open OracleTemplate.ComponentEnvelope (Program)
open OracleTemplate.FiniteSum (fullGradient)
open FiniteSumNondualDomain FiniteSumNondualBudget FiniteSumNondualProxGeometry
open FiniteSumNondualProxStep FiniteSumNondualProxExecution FiniteSumNondualProxSolver
open FiniteSumNondualProxFeasibility FiniteSumNondualSampling FiniteSumNondualOuterGeometry

lemma fallback_eval (p : Params) (g : Fin p.n × Point p → Point p) :
    (Program.eval g (fallbackPlan p)).val = step (domain p) 0 (1 / p.L) 0 0 (fullGradient g 0) := by
  simp only [fallbackPlan, Program.eval_map, snapshot_eval, id_eq]
  exact FiniteSumNondualExecution.feasiblePoint_val p _
    (step_mem (domain_nonempty p) (domain_compact p) (domain_convex p) _ _ _ _ _)

lemma fallback_gap (p : Params) (hp : spec.valid p) (f : Fin p.n → Point p → ℝ)
    (O : OracleTemplate.Oracle (Fin p.n × Feasible p) (Point p)) (ha : spec.admissible p f O)
    (u : Feasible p) :
    objective f (Program.eval (fun q => gradient (f q.1) q.2) (fallbackPlan p)).val - objective f u.val ≤
      p.L * p.R ^ 2 / 2 := by
  have hL := hp.2.2.1
  have he : (1 / p.L) * p.L ≤ 1 := by field_simp; norm_num
  have hh := exact_step_gap (domain_nonempty p) (domain_compact p) (domain_convex p)
    (objective_model p hL f O ha) (μ := 0) (by norm_num) (one_div_pos.mpr hL) he
    (0 : Point p) 0 u.val u.property
  simp only [regularized, zero_div, zero_mul, add_zero, zero_sub, norm_neg] at hh
  have hn := domain_norm p u.property
  have hs := sq_le_sq₀ (norm_nonneg u.val) p.hR |>.mpr hn
  rw [fallback_eval]
  have ht := mul_le_mul_of_nonneg_left hh hL.le
  field_simp at ht
  nlinarith [mul_le_mul_of_nonneg_left hs hL.le]

lemma solver_good (p : Params) (hp : spec.valid p) (g : Fin p.n × Point p → Point p)
    (c : Feasible p) (seed : Fin (epochCount p) → Fin (144 * p.n) → Fin p.n)
    (haccept : ‖(Program.eval g (solverPlan p c seed)).error‖ ≤ residualTolerance p) :
    Certified (domain p) (fullGradient g) (smoothing p) (residualTolerance p) c.val
      (Program.eval g (solverPlan p c seed)) := by
  obtain ⟨hw, hg, v, hv, he⟩ := solver_certificate (domain_nonempty p) (domain_compact p)
    (domain_convex p) hp.2.2.1 (smoothing_pos p hp).le g c.val (epochCount p) seed
  exact ⟨hw, hg, v, hv, he, haccept⟩

lemma solver_failure (p : Params) (hp : spec.valid p) (f : Fin p.n → Point p → ℝ)
    (O : OracleTemplate.Oracle (Fin p.n × Feasible p) (Point p)) (ha : spec.admissible p f O)
    (c : Feasible p) :
    (𝔼 seed : Fin (epochCount p) → Fin (144 * p.n) → Fin p.n,
      if ‖(Program.eval (fun q => gradient (f q.1) q.2) (solverPlan p c seed)).error‖ ≤ residualTolerance p
      then (0 : ℝ) else 1) ≤ failureRate p := by
  have hu := proximalPoint_spec (domain_nonempty p) (domain_compact p)
    (objective_continuous p f O ha) (smoothing p) c.val
  have hh := solver_failure_fraction (g := fun q : Fin p.n × Point p => gradient (f q.1) q.2) (domain_nonempty p) (domain_compact p) (domain_convex p)
    (component_model p hp.2.2.1 f O ha) p.hR c.val _ hu.1 (domain_distance p c.property hu.1)
    hu.2 (epochCount p) (tolerance_pos p hp) (residual_failure_budget p hp)
  simp only [← not_le, ite_not] at hh
  convert hh using 1
  apply Finset.expect_congr rfl
  intro seed _
  rfl

lemma plan_expected_gap (p : Params) (hp : spec.valid p) (f : Fin p.n → Point p → ℝ)
    (O : OracleTemplate.Oracle (Fin p.n × Feasible p) (Point p)) (ha : spec.admissible p f O)
    (xstar : Feasible p) (hmin : IsMinOn (objective f) (domain p) xstar.val) :
    (𝔼 seed : Seeds p, objective f (Program.eval (fun q => gradient (f q.1) q.2) (plan p seed)) -
      objective f xstar.val) ≤ p.ε := by
  change (𝔼 seed : Fin (requestCount p) → Fin (epochCount p) → Fin (144 * p.n) → Fin p.n,
    objective f (Program.eval (fun q => gradient (f q.1) q.2) (plan p seed)) - objective f xstar.val) ≤ p.ε
  let : NeZero p.d := ⟨hp.1.ne'⟩
  let g : Fin p.n × Point p → Point p := fun q => gradient (f q.1) q.2
  let base := Program.eval g (fallbackPlan p)
  have hbase : objective f base.val - objective f xstar.val ≤ p.L * p.R ^ 2 / 2 :=
    fallback_gap p hp f O ha xstar
  have hc := FiniteSumNondualPhase.phases_contract p (objective_model p hp.2.2.1 f O ha)
    (objective_continuous p f O ha) (smoothing_pos p hp) hp.2.2.2.2 hp.2.2.2.1
    (phaseSize_pos p) xstar hmin (lineFuel p) (tolerance_line p hp) (tolerance_value p hp)
    (line_precision p hp) (cube_budget p hp) (logSize p) (logSize_pos p) base
    (hbase.trans (initial_bound p hp))
  have hh := expected_loss (fun c seed => Program.eval g (solverPlan p c seed))
    (fun _ out => ‖out.error‖ ≤ residualTolerance p)
    (fun c out => Certified (domain p) (fullGradient g) (smoothing p) (residualTolerance p) c.val out)
    (fun u : Feasible p => objective f u.val - objective f xstar.val) base
    (show 0 ≤ p.ε / 2 by linarith [hp.2.2.2.2])
    (show 0 ≤ p.L * p.R ^ 2 / 2 by positivity [hp.2.2.1]) (failureRate_pos p hp).le
    hbase (solver_good p hp g) (solver_failure p hp f O ha)
    (requestCount p) _ (by simpa only [requestCount, Nat.mul_assoc] using
      (FiniteSumNondualPhase.phases_within p (smoothing p)
        (10 * phaseSize p) (lineFuel p) (logSize p) base)) hc
  rw [failure_loss p hp] at hh
  simp only [plan, Program.eval_bind, Program.eval_map]
  simp_rw [guardedPlan_eval]
  simpa only [base, g, Finset.expect_sub_distrib, Fintype.expect_const,
    show p.ε / 2 + p.ε / 2 = p.ε by ring] using hh

lemma checked_mono {Q Reply U : Type*} {pq : Q → Prop} {pu pv : U → Prop}
    {program : Program Q Reply U} (hp : Checked pq pu program) (h : ∀ u, pu u → pv u) :
    Checked pq pv program := by
  induction program with
  | done u => exact h u hp
  | ask q rest ih => exact ⟨hp.1, fun reply => ih reply (hp.2 reply)⟩

lemma checked_true {Q Reply U : Type*} (program : Program Q Reply U) :
    Checked (fun _ => True) (fun _ => True) program := by
  induction program with
  | done u => trivial
  | ask q rest ih => exact ⟨trivial, ih⟩

lemma plan_checked (p : Params) (seed : Seeds p) :
    Checked (fun q : Fin p.n × Point p => q.2 ∈ domain p) (fun x => x ∈ domain p) (plan p seed) := by
  unfold plan
  have hfb : Checked (fun q : Fin p.n × Point p => q.2 ∈ domain p)
      (fun _ : Feasible p => True) (fallbackPlan p) := by
    apply checked_map (snapshot_checked (domain p) 0 (by simp [domain, p.hR]) p.n id)
    intro _ _
    trivial
  apply checked_bind hfb
  intro base _
  apply checked_map (pu := fun _ => True)
  · apply guardedPlan_checked
    · intro c sample
      exact checked_mono (solvePlan_checked (domain_nonempty p) (domain_compact p) (domain_convex p)
        p.L (smoothing p) c.val c.property (epochCount p) sample) (fun _ _ => trivial)
    · trivial
    · exact checked_true _
  · intro u _
    exact u.property

lemma plan_cost (p : Params) (g : Fin p.n × Point p → Point p) (seed : Seeds p) :
    Program.cost g (plan p seed) ≤ 1099511627776 * p.n * rootSize p * logSize p ^ 4 := by
  have hc (c : Feasible p) (sample : Fin (epochCount p) → Fin (144 * p.n) → Fin p.n) :
      Program.cost g (solverPlan p c sample) ≤ (145 * epochCount p + 3) * p.n := by
    rw [solverPlan, solvePlan_cost]
  have hh := guardedPlan_cost (solverPlan p) (fun _ out => ‖out.error‖ ≤ residualTolerance p)
    (Program.eval g (fallbackPlan p)) g ((145 * epochCount p + 3) * p.n) hc
    (requestCount p) (phasesPlan p (smoothing p) (10 * phaseSize p) (lineFuel p) (logSize p)
      (Program.eval g (fallbackPlan p))) seed
  simp only [plan, Program.cost_bind, Program.cost_map, fallbackPlan, snapshot_cost]
  exact (Nat.add_le_add_left hh p.n).trans (total_cost_bound p)

end LongTails.Proofs.FiniteSumNondualPlan
