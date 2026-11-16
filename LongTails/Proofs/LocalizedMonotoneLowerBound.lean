import LongTails.Setups.GlobalJacobianMonotoneExpected
import LongTails.Proofs.Execution
import LongTails.Proofs.LocalizedMonotoneInstance
import LongTails.Proofs.LocalizedMonotoneParameters
import LongTails.Proofs.LocalizedMonotoneExpectation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.LocalizedMonotoneLowerBound

open LocalizedMonotoneInstance LocalizedMonotoneParameters LocalizedMonotoneConstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma derivative_translate (x0 : E) (F : E → E) (J : E → E →L[ℝ] E)
    (h : ∀ x, HasFDerivAt F (J x) x) (x : E) :
    HasFDerivAt (fun y => F (y - x0)) (J (x - x0)) x := by
  have hd := (h (x - x0)).comp x ((hasFDerivAt_id x).sub_const x0)
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using hd

noncomputable def oracle {d : ℕ} (x0 : EuclideanSpace ℝ (Fin d))
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (J : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    Oracle (EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))) where
  answer _ q _ := (F (q.2 - x0), J (q.2 - x0))

lemma execute_translated {d : ℕ} (x0 : EuclideanSpace ℝ (Fin d))
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (J : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (A : Algorithm (EuclideanSpace ℝ (Fin d))
      (EuclideanSpace ℝ (Fin d) × (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
      (EuclideanSpace ℝ (Fin d))) (N : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) :
    execute (oracle x0 F J) A (fun _ => N) seed ξ =
      A.output ((fun s => A.update s (F ((A.query s).2 - x0), J ((A.query s).2 - x0)))^[N] (A.initial seed)) := by
  rw [execute_eq_of_answer_eq (oracle x0 F J) (fun x => (F (x - x0), J (x - x0))) (by intros; rfl)]
  exact execute_iterate (fun x => (F (x - x0), J (x - x0))) A N seed

lemma instance_admissible (p : LongTails.Setups.GlobalJacobianMonotoneExpected.Params)
    (hL : 0 < p.L) (hR : 0 < p.R) (n : ℕ) (hn : 1 ≤ n)
    (π : Fin (n + 1) ↪ Fin p.d) :
    let a := width p.R n
    let c := offset p.R n
    let γ := p.L * a / 4
    let F := field a (4 * p.R) c γ π
    let J := jacobian a (4 * p.R) γ π
    LongTails.Setups.GlobalJacobianMonotoneExpected.spec.admissible p
      (fun x => F (x - p.x0)) (oracle p.x0 F J) := by
  let a := width p.R n
  let c := offset p.R n
  let γ := p.L * a / 4
  let F := field a (4 * p.R) c γ π
  let J := jacobian a (4 * p.R) γ π
  have ha : 0 < a := width_pos p.R hR n
  have hb : 0 < 4 * p.R := by positivity
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have hder (x) : HasFDerivAt (fun y => F (y - p.x0)) (J (x - p.x0)) x :=
    derivative_translate p.x0 F J (field_hasFDerivAt a (4 * p.R) c γ ha hb π) x
  refine ⟨?_, fun x => (hder x).differentiableAt, ?_, ?_, ?_⟩
  · intro history x seed
    change (F (x - p.x0), J (x - p.x0)) = _
    rw [(hder x).fderiv]
  · intro x y
    rw [(hder x).fderiv, (hder y).fderiv]
    have hh := jacobian_difference a (4 * p.R) γ ha hb hγ π (x - p.x0) (y - p.x0)
    rw [sub_sub_sub_cancel_right] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (smoothness_scale p.L p.R hL.le hR n) (norm_nonneg _))
  · intro x y
    have hh := field_monotone a (4 * p.R) c γ ha hb hγ π (x - p.x0) (y - p.x0)
    simpa only [sub_sub_sub_cancel_right] using hh
  · let z := rootPoint (height p.R n) (3 * a / 2) π
    have hz : chain a c π z = z := chain_root a (height p.R n) ha (height_ge p.R hR n) hn π
    have hzn : ‖z‖ ≤ p.R := root_norm p.R hR π
    refine ⟨p.x0 + z, ?_, ?_⟩
    · change F (p.x0 + z - p.x0) = 0
      rw [add_sub_cancel_left]
      exact field_zero_of_chain_root a (4 * p.R) c γ π z hz (by linarith)
    · simpa only [sub_add_cancel_left, norm_neg] using hzn

lemma exists_failure (p : LongTails.Setups.GlobalJacobianMonotoneExpected.Params)
    (n k : ℕ) (hL : 0 < p.L) (hR : 0 < p.R) (hn : 1 ≤ n) (hk : k ≤ n)
    (hd : 4096 * (n + 1) ^ 5 ≤ p.d)
    (hε : 2 * p.ε < p.L * p.R ^ 2 / (32 * ((n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1)))
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d) × (EuclideanSpace ℝ (Fin p.d) →L[ℝ] EuclideanSpace ℝ (Fin p.d)))
      (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (F : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d))
      (O : Oracle (EuclideanSpace ℝ (Fin p.d))
        (EuclideanSpace ℝ (Fin p.d) × (EuclideanSpace ℝ (Fin p.d) →L[ℝ] EuclideanSpace ℝ (Fin p.d)))),
      LongTails.Setups.GlobalJacobianMonotoneExpected.spec.admissible p F O ∧
        ¬ LongTails.Setups.GlobalJacobianMonotoneExpected.spec.successful p F
          (fun w : A.Seed × ((j : ℕ) → O.Seed j) => execute O A (fun _ => k) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  let a := width p.R n
  let c := offset p.R n
  let γ := p.L * a / 4
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  let query := fun s => (A.query s).2 - p.x0
  let output := fun s => A.output s - p.x0
  obtain ⟨π, hbad⟩ := LocalizedMonotoneExpectation.exists_failure_of_dimension
    p.L p.R p.ε hL hR hn hk hd hε query output A.update
    (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  let F := field a (4 * p.R) c γ π
  let J := jacobian a (4 * p.R) γ π
  refine ⟨fun x => F (x - p.x0), oracle p.x0 F J, instance_admissible p hL hR n hn π, ?_⟩
  intro hsuccess
  apply hbad
  have hout :
      (fun w : A.Seed × (ℕ → Unit) => ‖F (execute (oracle p.x0 F J) A (fun _ => k) w.1 w.2 - p.x0)‖) =
      fun w => ‖F (output ((fun s => A.update s (F (query s), J (query s)))^[k] (A.initial w.1)))‖ := by
    funext w
    rw [execute_translated p.x0 F J A k w.1 w.2]
  change Integrable (fun w : A.Seed × (ℕ → Unit) =>
    ‖F (output ((fun s => A.update s (F (query s), J (query s)))^[k] (A.initial w.1)))‖) (P : Measure _) ∧
      (∫ w : A.Seed × (ℕ → Unit),
        ‖F (output ((fun s => A.update s (F (query s), J (query s)))^[k] (A.initial w.1)))‖ ∂(P : Measure _)) ≤ p.ε
  rw [← hout]
  exact hsuccess

end LongTails.Proofs.LocalizedMonotoneLowerBound
