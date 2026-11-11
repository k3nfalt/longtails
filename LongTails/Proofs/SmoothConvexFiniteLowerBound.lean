import LongTails.Setups.SmoothAndConvexExpected
import LongTails.Proofs.Execution
import LongTails.Proofs.SmoothConvexFiniteExpectation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.SmoothConvexFiniteLowerBound

open LongTails.Setups.SmoothAndConvexExpected
open SmoothConvexFiniteWall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_translate (x0 : E) (f : E → ℝ) (g : E → E)
    (hg : ∀ x, HasGradientAt f (g x) x) (x : E) :
    HasGradientAt (fun y => f (y - x0)) (g (x - x0)) x := by
  have h := (hg (x - x0)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x0)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1 <;> simp [Function.comp_def]

omit [CompleteSpace E] in
lemma convex_translate (x0 : E) (f : E → ℝ) (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun x => f (x - x0)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ c e hc he hce
  have hshift : c • x + e • y - x0 = c • (x - x0) + e • (y - x0) := by
    have he' : e = 1 - c := by linarith
    rw [he']
    module
  simpa only [hshift, smul_eq_mul] using
    hf.2 (Set.mem_univ (x - x0)) (Set.mem_univ (y - x0)) hc he hce

noncomputable def oracle {d : ℕ} (x0 : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) :
    Oracle (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) where
  answer _ q _ := g (q.2 - x0)

lemma execute_translated {d : ℕ} (x0 : EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (A : Algorithm (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (N : ℕ) (seed : A.Seed) (ξ : ℕ → Unit) :
    execute (oracle x0 g) A (fun _ => N) seed ξ =
      A.output ((fun s => A.update s (g ((A.query s).2 - x0)))^[N] (A.initial seed)) := by
  rw [execute_eq_of_answer_eq (oracle x0 g) (fun x => g (x - x0)) (by intros; rfl)]
  exact execute_iterate (fun x => g (x - x0)) A N seed

lemma exists_failure (q : Params) (N : ℕ) (hL : 0 < q.L) (hR : 0 < q.R)
    (hd : 65536 * (N + 1) ^ 5 ≤ q.d)
    (hgap : 16384 * ((N : ℝ) + 1) ^ 2 * q.ε < q.L * q.R ^ 2)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin q.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))),
      spec.admissible q f O ∧
        ¬ spec.successful q f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  let K : ℝ := (N : ℝ) + 1
  let a := q.R / Real.sqrt K
  let δ := a / (8 * K)
  have hK : 0 < K := by dsimp [K]; positivity
  have ha : 0 < a := div_pos hR (Real.sqrt_pos.mpr hK)
  have hδ : 0 < δ := div_pos ha (by positivity)
  have hrad : K * a ^ 2 = q.R ^ 2 := by
    dsimp [a]
    rw [div_pow, Real.sq_sqrt hK.le, mul_div_cancel₀ _ hK.ne']
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  let query := fun s => (A.query s).2 - q.x0
  let output := fun s => A.output s - q.x0
  obtain ⟨π, hbad⟩ := SmoothConvexFiniteExpectation.exists_failure_of_dimension q.L q.R q.ε
    hL.le hR hd hgap query output A.update (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  let f := objective q.L q.R δ a π
  let g := field q.L q.R δ a π
  let z := FiniteSumNondualLowerComponents.hiddenPoint π a
  have hmin := objective_minimum q.L q.R δ a hL.le hR hδ.le π hrad.le
  have hadm : spec.admissible q (fun x : EuclideanSpace ℝ (Fin q.d) => f (x - q.x0)) (oracle q.x0 g) := by
    refine ⟨convex_translate q.x0 f (objective_convex q.L q.R δ a hL.le hR hδ.le π),
      ?_, ?_, q.x0 + z, ?_, ?_⟩
    · intro history seed x
      exact gradient_translate q.x0 f g (objective_gradient q.L q.R δ a hR hδ.le π) x
    · intro history seed x y
      change ‖g (x - q.x0) - g (y - q.x0)‖ ≤ _
      simpa only [sub_sub_sub_cancel_right] using
        field_lipschitz q.L q.R δ a hL.le hR hδ.le π hrad.le (x - q.x0) (y - q.x0)
    · intro x _
      change f (q.x0 + z - q.x0) ≤ f (x - q.x0)
      rw [add_sub_cancel_left]
      exact hmin.2 (Set.mem_univ (x - q.x0))
    · change ‖q.x0 - (q.x0 + z)‖ ≤ q.R
      simpa only [sub_add_cancel_left, norm_neg] using hiddenPoint_radius q.R a hR.le π hrad.le
  refine ⟨fun x : EuclideanSpace ℝ (Fin q.d) => f (x - q.x0), oracle q.x0 g, hadm, ?_⟩
  rintro ⟨xstar, hm, hi, he⟩
  change EuclideanSpace ℝ (Fin q.d) at xstar
  have hz : f (xstar - q.x0) = 0 := by
    apply le_antisymm
    · have hh := hm (Set.mem_univ (q.x0 + z))
      change f (xstar - q.x0) ≤ f (q.x0 + z - q.x0) at hh
      rw [add_sub_cancel_left] at hh
      exact hh.trans_eq hmin.1
    · exact objective_nonneg q.L q.R δ a hL.le hR π _
  have hout :
      (fun w : A.Seed × (ℕ → Unit) =>
        f (execute (oracle q.x0 g) A (fun _ => N) w.1 w.2 - q.x0) - f (xstar - q.x0)) =
      fun w => f (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1))) := by
    funext w
    rw [hz, sub_zero, execute_translated q.x0 g A N w.1 w.2]
  apply hbad
  constructor
  · change Integrable (fun w : A.Seed × (ℕ → Unit) =>
      f (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1)))) (P : Measure _)
    rw [← hout]
    exact hi
  · change (∫ w : A.Seed × (ℕ → Unit),
      f (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1))) ∂(P : Measure _)) ≤ q.ε
    rw [← hout]
    exact he

end LongTails.Proofs.SmoothConvexFiniteLowerBound
