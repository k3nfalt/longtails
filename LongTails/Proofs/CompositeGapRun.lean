import LongTails.Proofs.CompositeGapAdvance
import LongTails.Proofs.CompositeGapGrowth
import LongTails.Proofs.CompositeGeneralizedRun

namespace LongTails.Proofs.CompositeGapRun

open LongTails.Setups.CompositeGapSmooth
open OracleTemplate OracleTemplate.CompositeGapAccelerated
open CompositeGapPhase CompositeGapAdvance CompositeGapTuning CompositeGapGrowth

variable {p : Params} {I : Instance p} {s center : p.E} {Δ : ℝ}

noncomputable def transition (p : Params) (I : Instance p) (Δ : ℝ) (center : p.E)
    (q : State p.E) : State p.E :=
  QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox)
    (stepPlan p Δ center q)

lemma transition_eq (q : State p.E) : transition p I Δ center q =
    if target p Δ ≤ q.A then q else
      let y := queryPoint p Δ q
      let a := weight p Δ q.A
      update p Δ q (I.grad y)
        (I.prox (q.A + a) center ((1 / (q.A + a)) • (q.v + a • I.grad y))) := by
  unfold transition stepPlan
  split_ifs <;> rfl

lemma eval_phase (n : ℕ) (q : State p.E) :
    QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox)
      (phasePlan p Δ center n q) = (transition p I Δ center)^[n] q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [phasePlan, QueryPlan.eval_bind, ih, Function.iterate_succ_apply]
    rfl

lemma initial_transition (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < Δ) :
    let a := 1 / (16 * curvature p Δ)
    let z := I.prox a center (I.grad center)
    transition p I Δ center (initial center) = ⟨a, z, z, a • I.grad center⟩ := by
  have hT := target_pos p hR hΔ
  have hM := curvature_pos p h0 h1 hR hΔ
  have ha : 0 < 1 / (16 * curvature p Δ) := by positivity
  have hy : queryPoint p Δ (initial center) = center := by
    simp [queryPoint, initial, weight, hM.ne']
  rw [transition_eq, ite_eq_right (by simpa [initial] using not_le.mpr hT), hy]
  simp [initial, weight, update, hM.ne', smul_smul]
  congr 1
  rw [show 16 * curvature p Δ * ((curvature p Δ)⁻¹ * 16⁻¹) = 1 by field_simp]
  simp

lemma invariant_transition (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < Δ) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) {q : State p.E}
    (hq : Invariant p I s center Δ q) :
    Invariant p I s center Δ (transition p I Δ center q) := by
  rw [transition_eq]
  split_ifs with ht
  · exact hq
  · exact active_invariant h h0 h1 hR hΔ hc hr hgap hq (lt_of_not_ge ht)

lemma invariant_iterate (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < Δ) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) (n : ℕ) :
    Invariant p I s center Δ ((transition p I Δ center)^[n + 1] (initial center)) := by
  induction n with
  | zero =>
    rw [show 0 + 1 = 1 by rfl, Function.iterate_one, initial_transition h0 h1 hR hΔ]
    exact initial_invariant h h0 h1 hR hΔ hc hr hgap
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact invariant_transition h h0 h1 hR hΔ hc hr hgap ih

lemma transition_mass {q : State p.E} (hq : 0 < q.A) (hcap : q.A ≤ target p Δ) :
    (transition p I Δ center q).A = min (target p Δ) (q.A / (1 - fraction p Δ)) := by
  rw [transition_eq]
  split_ifs with ht
  · have he : q.A = target p Δ := le_antisymm hcap ht
    rw [he, min_eq_left]
    apply (le_div_iff₀ (by linarith [fraction_le p Δ])).mpr
    have hT : 0 ≤ target p Δ := by linarith
    nlinarith [fraction_pos p Δ]
  · exact active_mass p hq

lemma phase_accuracy_of_growth (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < Δ) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) (n : ℕ)
    (hn : Real.log (16 * scale p Δ) ≤ n * fraction p Δ) :
    let q := QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox)
      (phasePlan p Δ center (n + 1) (initial center))
    q.x ∈ I.Q ∧ ‖q.x - s‖ ≤ p.R ∧ objective I q.x - objective I s ≤ Δ / 2 := by
  let f := fun k => ((transition p I Δ center)^[k + 1] (initial center)).A
  let a := 1 / (16 * curvature p Δ)
  have hM := curvature_pos p h0 h1 hR hΔ
  have ha : 0 < a := by dsimp [a]; positivity
  have hi (k : ℕ) := invariant_iterate h h0 h1 hR hΔ hc hr hgap k
  have hinit : f 0 = a := by
    change (transition p I Δ center (initial center)).A = a
    rw [initial_transition h0 h1 hR hΔ]
  have hstep (k : ℕ) : f (k + 1) = min (target p Δ) (f k / (1 - fraction p Δ)) := by
    dsimp only [f]
    rw [Function.iterate_succ_apply']
    exact transition_mass (hi k).positive (hi k).capped
  have hat : a ≤ target p Δ := by simpa only [← hinit] using (hi 0).capped
  have he : target p Δ / a = 16 * scale p Δ := by
    dsimp [target, a, scale]
    field_simp
  have hθ := fraction_pos p Δ
  have hθ1 : fraction p Δ < 1 := by linarith [fraction_le p Δ]
  have hcap := capped_reaches ha hat hθ.le hθ1 f hinit hstep n (by rw [he]; exact hn)
  rw [eval_phase]
  let q := (transition p I Δ center)^[n + 1] (initial center)
  have hq : Invariant p I s center Δ q := hi n
  have he' := invariant_energy h hq h.minimizer_feasible
  change q.A = target p Δ at hcap
  have hs := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hr
  rw [hcap, norm_sub_rev s center] at he'
  refine ⟨hq.feasible_x, hq.radius_x, ?_⟩
  have ht : target p Δ * Δ = p.R ^ 2 := by dsimp [target]; field_simp
  have htp := target_pos p hR hΔ
  nlinarith [sq_nonneg ‖q.z - s‖]

lemma phase_accuracy (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hεΔ : p.ε ≤ Δ)
    (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) :
    let q := QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox)
      (phasePlan p Δ center (phaseIterations p) (initial center))
    q.x ∈ I.Q ∧ ‖q.x - s‖ ≤ p.R ∧ objective I q.x - objective I s ≤ Δ / 2 := by
  obtain ⟨hN, hgrowth⟩ := phase_iterations_suffice p h0 h1 hR hε hεΔ
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [hn] at ⊢ hgrowth
  norm_num only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hgrowth
  exact phase_accuracy_of_growth h h0 h1 hR (hε.trans_le hεΔ) hc hr hgap n hgrowth

lemma stages_accuracy (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (S k : ℕ)
    (hk : k + S ≤ phases p) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ p.Δ / 2 ^ k) :
    let x := QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox)
      (phasesPlan p (phaseIterations p) S k center)
    x ∈ I.Q ∧ ‖x - s‖ ≤ p.R ∧ objective I x - objective I s ≤ p.Δ / 2 ^ (k + S) := by
  induction S generalizing k center with
  | zero => simpa [phasesPlan, QueryPlan.eval] using And.intro hc (And.intro hr hgap)
  | succ S ih =>
    have hkg : k < phases p := by omega
    have hεk := (stage_gap_gt p hΔ hε hkg).le
    have hphase := phase_accuracy h h0 h1 hR hε hεk hc hr hgap
    let q := QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox)
      (phasePlan p (p.Δ / 2 ^ k) center (phaseIterations p) (initial center))
    change q.x ∈ I.Q ∧ ‖q.x - s‖ ≤ p.R ∧ objective I q.x - objective I s ≤ (p.Δ / 2 ^ k) / 2 at hphase
    have he : (p.Δ / 2 ^ k) / 2 = p.Δ / 2 ^ (k + 1) := by rw [pow_succ, div_div]
    rw [he] at hphase
    have hh := ih (k + 1) (by omega) hphase.1 hphase.2.1 hphase.2.2
    dsimp only
    rw [phasesPlan, QueryPlan.eval_bind]
    simpa only [Nat.add_assoc, Nat.add_comm 1 S] using hh

lemma run_accuracy (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    let x := QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox)
      (phasesPlan p (phaseIterations p) (phases p) 0 p.x0)
    x ∈ I.Q ∧ objective I x - objective I s ≤ p.ε := by
  have hh := stages_accuracy h h0 h1 hR hΔ hε (phases p) 0 (by omega)
    h.initial_feasible h.distance (by simpa using h.gap)
  dsimp only at hh ⊢
  exact ⟨hh.1, hh.2.2.trans (by simpa using final_gap_le p hΔ hε)⟩

lemma execute_accuracy (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (O : Oracle (Query p) p.E)
    (hans : ∀ k query seed, O.answer k (0, query) seed =
      CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox query)
    (K : ℕ) (hK : calls p ≤ K) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) (fun _ => K) () ξ ∈ I.Q ∧
      objective I (execute O (algorithm p) (fun _ => K) () ξ) - objective I s ≤ p.ε := by
  have he := execute_eq_of_answer_eq O _ hans (algorithm p) K () ξ
  have hp := QueryPlan.execute_plan_of_le
    (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ : MeasureTheory.ProbabilityMeasure Unit)
    (.gradient p.x0 : Query p) p.x0 (calls p) K
    (fun _ : Unit => phasesPlan p (phaseIterations p) (phases p) 0 p.x0)
    (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox) () hK
  have hexec := he.trans hp
  rw [hexec]
  exact run_accuracy h h0 h1 hR hΔ hε

lemma output_accuracy (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (O : Oracle (Query p) p.E)
    (hans : ∀ k query seed, O.answer k (0, query) seed =
      CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox query)
    (ξ : (k : ℕ) → O.Seed k) :
    output p O ξ ∈ I.Q ∧ objective I (output p O ξ) - objective I s ≤ p.ε :=
  execute_accuracy h h0 h1 hR hΔ hε O hans (calls p) le_rfl ξ

end LongTails.Proofs.CompositeGapRun
