import LongTails.Proofs.CompositeGapQuadraticWeightsPhase
import LongTails.Proofs.CompositeGapQuadraticWeightsBudget

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CompositeGapQuadraticWeights

open LongTails.Setups.CompositeGapSmooth
open OracleTemplate OracleTemplate.CompositeGapQuadraticWeights
open CompositeGapGeometry CompositeGapModel

variable {p : Params} {I : Instance p} {s c : p.E}

open OracleTemplate.CompositeGapAccelerated (phases)

lemma eval_transport {Q R U : Type*} {k l : ℕ} (g : Q → R) (e : k = l)
    (plan : QueryPlan Q R U k) : QueryPlan.eval g (e ▸ plan : QueryPlan Q R U l) =
      QueryPlan.eval g plan := by cases e; rfl

lemma phase_accuracy (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (k : ℕ) (hc : c ∈ I.Q) (hcs : ‖c - s‖ ≤ p.R)
    (hcg : objective I c - objective I s ≤ level p k) :
    let q := QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox)
      (phase p (curvature p (level p k)) c (iterations p k))
    q.x ∈ I.Q ∧ ‖q.x - s‖ ≤ p.R ∧ objective I q.x - objective I s ≤ level p k / 2 := by
  let d := level p k
  let M := curvature p d
  let r := Real.sqrt (d / M)
  let m := iterations p k
  let q := fun n => QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox)
    (phase p M c n)
  have hd : 0 < d := level_pos p hΔ k
  have hM : 0 < M := by dsimp [M, curvature]; positivity
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hd hM)
  have hdr : M * r ^ 2 = d := by dsimp [r]; rw [Real.sq_sqrt (by positivity)]; field_simp
  have hcoef : p.H0 + p.H1 * d ≤ M := by dsimp [M, curvature]; linarith [show 0 ≤ d / (2 * p.R ^ 2) by positivity]
  have hloc : Real.sqrt p.H1 * r ≤ 1 := by
    apply (sq_le_sq₀ (by positivity) (by norm_num)).mp
    rw [mul_pow, Real.sq_sqrt h1, one_pow]
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith only [congrArg (p.H1 * ·) hdr, hcoef, h0]
  have hi (n : ℕ) : Invariant I s c M r d n (q n) := by
    induction n with
    | zero =>
      change Invariant I s c M r d 0 ⟨c, c, 0⟩
      constructor
      · exact hc
      · exact hc
      · exact hcg
      · exact hcs
      · simp; positivity
      · simp; positivity
      · simp [mass]
      · have ht := (regularizerShift_le_gap h c).trans hcg
        simp only [Nat.cast_zero, zero_add, one_mul]
        exact ht.trans (le_add_of_nonneg_right (by positivity))
      · refine ⟨0, ?_, ?_, ?_⟩
        · intro u hu
          simp [model, mass]; positivity
        · simp [model, mass]
        · intro u hu
          simp [model, mass]
    | succ n ih =>
      dsimp only [q, phase]
      rw [eval_transport, QueryPlan.eval_bind]
      exact advance h h0 h1 hM hr hdr hcoef hloc hc hR hcs hcg n _ ih
  have hm := hi m
  obtain ⟨b, hmin, hl, hu⟩ := hm.cert
  have hmass : 0 ≤ mass M m := by dsimp [mass]; positivity
  have he := model_energy h hmass hm.fz h.minimizer_feasible hmin hl (hu s h.minimizer_feasible)
  have ht : 16 * Real.sqrt (scale p d) ≤ (m : ℝ) := Nat.le_ceil _
  have hscale : 0 ≤ scale p d := by change 0 ≤ M * p.R ^ 2 / d; positivity
  have hs := (sq_le_sq₀ (by positivity) (Nat.cast_nonneg m)).mpr ht
  rw [mul_pow, Real.sq_sqrt hscale] at hs
  change 16 ^ 2 * (M * p.R ^ 2 / d) ≤ (m : ℝ) ^ 2 at hs
  have hmd : p.R ^ 2 ≤ mass M m * d := by
    dsimp [mass]; field_simp at hs ⊢
    nlinarith only [hs, mul_nonneg (Nat.cast_nonneg (α := ℝ) m) hd.le]
  have hmp : 0 < mass M m := by
    by_contra! hh
    nlinarith only [hmd, mul_nonpos_of_nonpos_of_nonneg hh hd.le, sq_pos_of_pos hR]
  refine ⟨hm.fx, hm.radius, ?_⟩
  change objective I (q m).x - objective I s ≤ d / 2
  apply (mul_le_mul_iff_right₀ hmp).mp
  rw [norm_sub_rev s c] at he
  nlinarith only [he, hmd, (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hcs, sq_nonneg ‖(q m).z - s‖]

lemma stages_accuracy (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (k : ℕ) :
    let x := QueryPlan.eval (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox) (stages p k)
    x ∈ I.Q ∧ ‖x - s‖ ≤ p.R ∧ objective I x - objective I s ≤ level p k := by
  induction k with
  | zero => exact ⟨h.initial_feasible, h.distance, by simpa [level, stages, QueryPlan.eval] using h.gap⟩
  | succ k ih =>
    dsimp only [stages, cost]
    erw [QueryPlan.eval_bind, QueryPlan.eval_map, level_succ]
    exact phase_accuracy h h0 h1 hR hΔ k ih.1 ih.2.1 ih.2.2

lemma execute_accuracy (h : Conditions p I s) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (O : Oracle (Query p) p.E)
    (hans : ∀ k query seed, O.answer k (0, query) seed =
      CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox query)
    (K : ℕ) (hK : cost p (phases p) ≤ K) (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) (fun _ => K) () ξ ∈ I.Q ∧
      objective I (execute O (algorithm p) (fun _ => K) () ξ) - objective I s ≤ p.ε := by
  have he := execute_eq_of_answer_eq O _ hans (algorithm p) K () ξ
  have hp := QueryPlan.execute_plan_of_le
    (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ : MeasureTheory.ProbabilityMeasure Unit)
    (.gradient p.x0 : Query p) p.x0 (cost p (phases p)) K (fun _ : Unit => stages p (phases p))
    (CompositeGeneralized.answerOf (oraclePublic p) I.grad I.prox) () hK
  rw [he.trans hp]
  have ht := stages_accuracy h h0 h1 hR hΔ (phases p)
  exact ⟨ht.1, ht.2.2.trans (CompositeGapGrowth.final_gap_le p hΔ hε)⟩

end LongTails.Proofs.CompositeGapQuadraticWeights
