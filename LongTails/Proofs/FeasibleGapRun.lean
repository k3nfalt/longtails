import LongTails.Proofs.FeasibleGapAdvance
import LongTails.Proofs.FeasibleGapGrowth
import LongTails.Proofs.CompositeGeneralizedRun
import LongTails.Proofs.FeasibleGapExecution

namespace LongTails.Proofs.FeasibleGapRun

open LongTails.Setups.FeasibleHessianGapComposite
open OracleTemplate OracleTemplate.FeasibleGapAccelerated
open FeasibleGapPhase FeasibleGapAdvance FeasibleGapTuning FeasibleGapGrowth

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
    (hR : 0 < p.R) (hε : 0 < p.ε) (hεΔ : p.ε ≤ Δ) :
    let a := 1 / (131072 * logarithm p ^ 2 * curvature p Δ)
    let z := I.prox a center (I.grad center)
    transition p I Δ center (initial center) = ⟨a, z, z, a • I.grad center⟩ := by
  have hΔ : 0 < Δ := hε.trans_le hεΔ
  have hL := logarithm_lower p h0 h1 hε
  have hLp : 0 < logarithm p := by linarith
  let a := 1 / (131072 * logarithm p ^ 2 * curvature p Δ)
  have hT := target_pos p hR hΔ
  have hM := curvature_pos p h0 h1 hR hΔ
  have ha : 0 < a := by dsimp [a]; positivity
  have hw : weight p Δ 0 = a := by simp [weight, a]
  have hy : queryPoint p Δ (initial center) = center := by
    simp only [queryPoint, initial, hw, zero_add, zero_div, zero_smul, zero_add,
      div_self ha.ne', one_smul]
  rw [transition_eq, ite_eq_right (by simpa [initial] using not_le.mpr hT), hy]
  dsimp only
  simp only [initial, hw, zero_add]
  change update p Δ (initial center) (I.grad center)
    (I.prox a center ((1 / a) • (a • I.grad center))) = _
  rw [smul_smul, one_div_mul_cancel ha.ne', one_smul]
  simp only [update, initial, hw, zero_add, zero_div, zero_smul, zero_add,
    div_self ha.ne', one_smul]
  rfl


lemma invariant_transition (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hεΔ : p.ε ≤ Δ) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) {q : State p.E}
    (hq : Invariant p I s center Δ q) :
    Invariant p I s center Δ (transition p I Δ center q) := by
  have hΔ : 0 < Δ := hε.trans_le hεΔ
  have hL := logarithm_lower p h0 h1 hε
  have hLp : 0 < logarithm p := by linarith
  rw [transition_eq]
  split_ifs with ht
  · exact hq
  · exact active_invariant h h0 h1 hR hε hεΔ hc hr hgap hq (lt_of_not_ge ht)

lemma invariant_iterate (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hεΔ : p.ε ≤ Δ) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) (n : ℕ) :
    Invariant p I s center Δ ((transition p I Δ center)^[n + 1] (initial center)) := by
  have hΔ : 0 < Δ := hε.trans_le hεΔ
  have hL := logarithm_lower p h0 h1 hε
  have hLp : 0 < logarithm p := by linarith
  induction n with
  | zero =>
    rw [show 0 + 1 = 1 by rfl, Function.iterate_one, initial_transition h0 h1 hR hε hεΔ]
    exact initial_invariant h h0 h1 hR hε hεΔ hc hr hgap
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact invariant_transition h h0 h1 hR hε hεΔ hc hr hgap ih

lemma transition_mass {q : State p.E} (hq : 0 < q.A) (hcap : q.A ≤ target p Δ) (hL : 1 / 2 ≤ logarithm p) :
    (transition p I Δ center q).A = min (target p Δ) (q.A / (1 - fraction p Δ)) := by
  rw [transition_eq]
  split_ifs with ht
  · have he : q.A = target p Δ := le_antisymm hcap ht
    rw [he, min_eq_left]
    apply (le_div_iff₀ (by linarith [fraction_bound p hL Δ])).mpr
    have hT : 0 ≤ target p Δ := by linarith
    nlinarith [fraction_positive p (by linarith) Δ]
  · exact active_mass p hq hL

lemma phase_accuracy_of_growth (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hεΔ : p.ε ≤ Δ) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) (n : ℕ)
    (hn : Real.log (131072 * logarithm p ^ 2 * scale p Δ) ≤ n * fraction p Δ) :
    let q := QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox)
      (phasePlan p Δ center (n + 1) (initial center))
    q.x ∈ I.Q ∧ ‖q.x - s‖ ≤ p.R ∧ objective I q.x - objective I s ≤ Δ / 2 := by
  have hΔ : 0 < Δ := hε.trans_le hεΔ
  have hL := logarithm_lower p h0 h1 hε
  have hLp : 0 < logarithm p := by linarith
  let f := fun k => ((transition p I Δ center)^[k + 1] (initial center)).A
  let a := 1 / (131072 * logarithm p ^ 2 * curvature p Δ)
  have hM := curvature_pos p h0 h1 hR hΔ
  have ha : 0 < a := by dsimp [a]; positivity
  have hi (k : ℕ) := invariant_iterate h h0 h1 hR hε hεΔ hc hr hgap k
  have hinit : f 0 = a := by
    change (transition p I Δ center (initial center)).A = a
    rw [initial_transition h0 h1 hR hε hεΔ]
  have hstep (k : ℕ) : f (k + 1) = min (target p Δ) (f k / (1 - fraction p Δ)) := by
    dsimp only [f]
    rw [Function.iterate_succ_apply']
    exact transition_mass (hi k).positive (hi k).capped hL
  have hat : a ≤ target p Δ := by simpa only [← hinit] using (hi 0).capped
  have he : target p Δ / a = 131072 * logarithm p ^ 2 * scale p Δ := by
    dsimp [target, a, scale]
    field_simp
  have hθ := fraction_positive p (by linarith) Δ
  have hθ1 : fraction p Δ < 1 := by linarith [fraction_bound p hL Δ]
  have hcap := LongTails.Proofs.CompositeGapGrowth.capped_reaches ha hat hθ.le hθ1 f hinit hstep n (by rw [he]; exact hn)
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
  exact phase_accuracy_of_growth h h0 h1 hR hε hεΔ hc hr hgap n hgrowth

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


def allowedQuery (I : Instance p) : Query p → Prop
  | .gradient x => x ∈ I.Q
  | .prox _ _ _ => True

lemma initial_query (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hεΔ : p.ε ≤ Δ) :
    queryPoint p Δ (initial center) = center := by
  have hd := hε.trans_le hεΔ
  have hM := curvature_pos p h0 h1 hR hd
  have hL := logarithm_lower p h0 h1 hε
  have hLp : logarithm p ≠ 0 := by linarith
  simp [queryPoint, initial, weight, hM.ne', hLp]

lemma step_supported (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hεΔ : p.ε ≤ Δ) (hc : center ∈ I.Q)
    {q : State p.E} (hq : q = initial center ∨ Invariant p I s center Δ q) :
    FeasibleGapExecution.Supported
      (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox) (allowedQuery I)
      (stepPlan p Δ center q) := by
  have hd := hε.trans_le hεΔ
  have hL := logarithm_lower p h0 h1 hε
  rcases hq with rfl | hq
  · have hT := target_pos p hR hd
    rw [stepPlan, ite_eq_right (by simpa [initial] using not_le.mpr hT)]
    change queryPoint p Δ (initial center) ∈ I.Q ∧ True ∧ True
    rw [initial_query h0 h1 hR hε hεΔ]
    exact ⟨hc, trivial, trivial⟩
  · rw [stepPlan]
    split_ifs with ht
    · exact ⟨hq.feasible_x, hq.feasible_x, trivial⟩
    · change queryPoint p Δ q ∈ I.Q ∧ True ∧ True
      obtain ⟨ha, _, _⟩ := weight_bounds p hq.positive (lt_of_not_ge ht) hL
      have hB : 0 < q.A + weight p Δ q.A := by linarith [hq.positive]
      refine ⟨?_, trivial, trivial⟩
      apply h.convex_domain hq.feasible_x hq.feasible_z
        (div_nonneg hq.positive.le hB.le) (div_nonneg ha.le hB.le)
      field_simp

lemma phase_supported (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hεΔ : p.ε ≤ Δ)
    (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ Δ) (n : ℕ) {q : State p.E}
    (hq : q = initial center ∨ Invariant p I s center Δ q) :
    FeasibleGapExecution.Supported
      (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox) (allowedQuery I)
      (phasePlan p Δ center n q) := by
  induction n generalizing q with
  | zero => trivial
  | succ n ih =>
    apply FeasibleGapExecution.supported_bind
    · exact step_supported h h0 h1 hR hε hεΔ hc hq
    · apply ih
      right
      change Invariant p I s center Δ (transition p I Δ center q)
      rcases hq with rfl | hq
      · rw [initial_transition h0 h1 hR hε hεΔ]
        exact initial_invariant h h0 h1 hR hε hεΔ hc hr hgap
      · exact invariant_transition h h0 h1 hR hε hεΔ hc hr hgap hq

lemma stages_supported (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (S k : ℕ)
    (hk : k + S ≤ phases p) (hc : center ∈ I.Q) (hr : ‖center - s‖ ≤ p.R)
    (hgap : objective I center - objective I s ≤ p.Δ / 2 ^ k) :
    FeasibleGapExecution.Supported
      (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox) (allowedQuery I)
      (phasesPlan p (phaseIterations p) S k center) := by
  induction S generalizing k center with
  | zero => trivial
  | succ S ih =>
    have hkg : k < phases p := by omega
    have hεk := (stage_gap_gt p hΔ hε hkg).le
    apply FeasibleGapExecution.supported_bind
    · exact phase_supported h h0 h1 hR hε hεk hc hr hgap _ (Or.inl rfl)
    · have hp := phase_accuracy h h0 h1 hR hε hεk hc hr hgap
      apply ih (k + 1) (by omega) hp.1 hp.2.1
      have he : (p.Δ / 2 ^ k) / 2 = p.Δ / 2 ^ (k + 1) := by rw [pow_succ, div_div]
      simpa only [he] using hp.2.2

lemma execute_accuracy (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (O : Oracle (Query p) p.E)
    (hgrad : ∀ history seed x, x ∈ I.Q → O.answer history (0, .gradient x) seed = I.grad x)
    (hprox : ∀ history seed a z v, O.answer history (0, .prox a z v) seed = I.prox a z v)
    (K : ℕ) (hK : calls p ≤ K) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) (fun _ => K) () ξ ∈ I.Q ∧
      objective I (execute O (algorithm p) (fun _ => K) () ξ) - objective I s ≤ p.ε := by
  have hans : ∀ history q seed, allowedQuery I q → O.answer history (0, q) seed =
      CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox q := by
    intro history q seed hq
    cases q with
    | gradient x => exact hgrad history seed x hq
    | prox a z v => exact hprox history seed a z v
  have hs := stages_supported h h0 h1 hR hΔ hε (phases p) 0 (by omega)
    h.initial_feasible h.distance (by simpa using h.gap)
  have he := FeasibleGapExecution.execute_supported O
    (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox) (allowedQuery I) hans
    (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ : MeasureTheory.ProbabilityMeasure Unit)
    (.gradient p.x0 : Query p) p.x0 (calls p) K
    (fun _ : Unit => phasesPlan p (phaseIterations p) (phases p) 0 p.x0) () hs hK ξ
  change execute O (algorithm p) (fun _ => K) () ξ = _ at he
  rw [he]
  exact run_accuracy h h0 h1 hR hΔ hε

lemma output_accuracy (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (O : Oracle (Query p) p.E)
    (hgrad : ∀ history seed x, x ∈ I.Q → O.answer history (0, .gradient x) seed = I.grad x)
    (hprox : ∀ history seed a z v, O.answer history (0, .prox a z v) seed = I.prox a z v)
    (ξ : (k : ℕ) → O.Seed k) :
    output p O ξ ∈ I.Q ∧ objective I (output p O ξ) - objective I s ≤ p.ε :=
  execute_accuracy h h0 h1 hR hΔ hε O hgrad hprox (calls p) le_rfl ξ

end LongTails.Proofs.FeasibleGapRun
