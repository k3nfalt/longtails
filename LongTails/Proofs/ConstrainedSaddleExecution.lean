import LongTails.Proofs.ConstrainedSaddleOuter
import LongTails.Proofs.AuxiliaryPlan

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ConstrainedSaddleExecution

open LongTails.Setups.ConstrainedMinimaxSecondOrder
open LongTails.Algorithms.ConstrainedSaddleCubic
open LongTails.Algorithms.AuxiliaryPlan
open ConstrainedSaddleInner ConstrainedSaddleTracking ConstrainedSaddleOuter ConstrainedMinimaxEnvelope

lemma eval_liftPlan {Q R U : Type} (g : Q → R) {k : ℕ}
    (plan : OracleTemplate.QueryPlan Q R U k) :
    TwoPlan.eval (fun _ => g) (liftPlan plan) = OracleTemplate.QueryPlan.eval g plan := by
  induction plan with
  | done value => rfl
  | ask q next ih => exact ih (g q)

lemma length_liftPlan {Q R U : Type} (g : Q → R) {k : ℕ}
    (plan : OracleTemplate.QueryPlan Q R U k) :
    AuxiliaryPlan.TwoPlan.length (fun _ => g) (liftPlan plan) = k := by
  induction plan with
  | done value => rfl
  | ask q next ih =>
    simp only [liftPlan, AuxiliaryPlan.TwoPlan.length, ih]
    omega

lemma length_bind {Q R U V : Type} (g : Fin 2 → Q → R) (plan : TwoPlan Q R U)
    (next : U → TwoPlan Q R V) :
    AuxiliaryPlan.TwoPlan.length g (plan.andThen next) =
      AuxiliaryPlan.TwoPlan.length g plan + AuxiliaryPlan.TwoPlan.length g (next (TwoPlan.eval g plan)) := by
  induction plan with
  | done value => simp [TwoPlan.andThen, AuxiliaryPlan.TwoPlan.length, TwoPlan.eval]
  | ask i q rest ih =>
    simp only [TwoPlan.andThen, AuxiliaryPlan.TwoPlan.length, TwoPlan.eval, ih]
    omega

lemma advance_plan {Q R U : Type} (g : Q → R) (q0 : Q) (plan : TwoPlan Q R U)
    (K call : ℕ) :
    OracleTemplate.StochasticGradient.advance
      (fun _ state => TwoPlan.advance state (g (TwoPlan.index q0 state).2)) K call plan =
      (TwoPlan.step (fun _ => g))^[K] plan := by
  induction K generalizing plan call with
  | zero => rfl
  | succ K ih =>
    rw [OracleTemplate.StochasticGradient.advance, Function.iterate_succ_apply]
    have hs : TwoPlan.advance plan (g (TwoPlan.index q0 plan).2) =
        TwoPlan.step (fun _ => g) plan := by cases plan <;> rfl
    rw [hs]
    exact ih _ _

lemma execute_method {p : Params} (O : OracleTemplate.Oracle (Space p) (spec.Reply p))
    (g : Space p → spec.Reply p)
    (hO : ∀ hist seed z, O.answer hist (0, z) seed = g z) (K : ℕ)
    (hK : AuxiliaryPlan.TwoPlan.length (fun _ => g) (fullPlan p) ≤ K)
    (ω : (k : ℕ) → O.Seed k) :
    output p O K ω = TwoPlan.eval (fun _ => g) (fullPlan p) := by
  have hreply : ∀ hist query, O.answer hist query (ω hist.length) = g query.2 := by
    intro hist query
    have hi : query.1 = 0 := Subsingleton.elim _ _
    obtain ⟨i, z⟩ := query
    simp only at hi ⊢
    rw [hi]
    exact hO hist _ z
  unfold output
  rw [OracleTemplate.StochasticGradient.execute_advance_of_answer O (method p) K () ω
    (fun _ query => g query.2) hreply]
  change TwoPlan.result p.x0
    (OracleTemplate.StochasticGradient.advance
      (fun _ state => TwoPlan.advance state (g (TwoPlan.index (WithLp.toLp 2 (p.x0, p.y0)) state).2))
      K 0 (fullPlan p)) = _
  rw [advance_plan, AuxiliaryPlan.TwoPlan.iterate_step_of_length_le _ _ _ hK]
  rfl

lemma run_outer_accuracy {p : Params} {f : Space p → ℝ} (H : Regularity p f)
    (hv : spec.valid p) (n : ℕ) (z : p.E) (state : Space p × Space p) (G : ℝ)
    (hw : TrackingInvariant f z state) (hG : 0 ≤ G)
    (hgap : ∀ u, envelope f z - envelope f u ≤ G)
    (hn : G < n * (p.ε * Real.sqrt p.ε / (96 * Real.sqrt (modelScale p)))) :
    ‖gradient (value f) (TwoPlan.eval (fun _ => jet f) (runOuter n z state))‖ ≤ p.ε := by
  induction n generalizing z state G with
  | zero => simp only [Nat.cast_zero, zero_mul] at hn; linarith
  | succ n ih =>
    let z' := OracleTemplate.QueryPlan.eval (jet f) (outerPlan z state)
    let next := OracleTemplate.QueryPlan.eval (jet f)
      (trackPlan z z' (segmentCount z z') 0 (segmentCount z z') state)
    have hnext : TrackingInvariant f z' next := tracking_complete H hv z z' state hw
    rw [runOuter, AuxiliaryPlan.TwoPlan.eval_bind, eval_liftPlan,
      AuxiliaryPlan.TwoPlan.eval_bind, eval_liftPlan]
    change ‖gradient (value f) (TwoPlan.eval (fun _ => jet f)
      (if ‖z' - z‖ ^ 2 ≤ p.ε / (4 * modelScale p) then .done next.1.fst else runOuter n z' next))‖ ≤ p.ε
    by_cases hs : ‖z' - z‖ ^ 2 ≤ p.ε / (4 * modelScale p)
    · rw [ite_eq_left hs, TwoPlan.eval]
      exact outer_small_step_accuracy H hv z state next hw hnext hs
    · rw [ite_eq_right hs]
      have hlarge : p.ε / (4 * modelScale p) ≤ ‖z' - z‖ ^ 2 := (lt_of_not_ge hs).le
      have hd := outer_large_step_decrease H hv z state hw hlarge
      change p.ε * Real.sqrt p.ε / (96 * Real.sqrt (modelScale p)) ≤ envelope f z - envelope f z' at hd
      apply ih z' next (G - (envelope f z - envelope f z')) hnext
      · linarith [hgap z']
      · intro u
        linarith [hgap u]
      · push_cast at hn
        nlinarith

lemma outer_steps_sufficient {p : Params} (hv : spec.valid p) :
    p.Δ < outerSteps p * (p.ε * Real.sqrt p.ε / (96 * Real.sqrt (modelScale p))) := by
  have hε := hv.2.2.2.2.2.1
  have hR := model_scale_positive hv
  have hd : 0 < p.ε * Real.sqrt p.ε / (96 * Real.sqrt (modelScale p)) := by positivity
  have he : p.Δ / (p.ε * Real.sqrt p.ε / (96 * Real.sqrt (modelScale p))) =
      96 * p.Δ * Real.sqrt (modelScale p) / (p.ε * Real.sqrt p.ε) := by field_simp
  apply (div_lt_iff₀ hd).mp
  rw [he]
  have hh := Nat.le_ceil (96 * p.Δ * Real.sqrt (modelScale p) / (p.ε * Real.sqrt p.ε))
  unfold outerSteps
  push_cast
  linarith

lemma full_plan_accuracy {p : Params} {f : Space p → ℝ} (H : Assumptions p f)
    (hv : spec.valid p) :
    ‖gradient (value f) (TwoPlan.eval (fun _ => jet f) (fullPlan p))‖ ≤ p.ε := by
  rw [fullPlan, AuxiliaryPlan.TwoPlan.eval_bind, eval_liftPlan,
    AuxiliaryPlan.TwoPlan.eval_bind, eval_liftPlan]
  exact run_outer_accuracy H.toRegularity hv (outerSteps p) p.x0 _ p.Δ
    (startup_invariant H hv) hv.2.2.2.1 (envelope_initial_gap H hv) (outer_steps_sufficient hv)

end LongTails.Proofs.ConstrainedSaddleExecution
