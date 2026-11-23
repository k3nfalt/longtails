import LongTails.Proofs.GeneralizedMintyHiding
import LongTails.Proofs.Execution

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedMintyLowerBound

open LongTails.Setups.GeneralizedLipschitzMinty
open MintyChainGeometry GeneralizedMintyChain GeneralizedMintyScales GeneralizedMintyHiding

variable {p : Params} (s : Scales p) (π : Fin (2 * s.m + 1) ↪ Fin p.d)

noncomputable def instanceField (x : V p) := hard s π (x - p.x0)

noncomputable def oracle : Oracle (V p) (V p) where
  answer _ q _ := instanceField s π q.2

lemma admissible (hp : spec.valid p) : spec.admissible p (instanceField s π) (oracle s π) := by
  obtain ⟨_, h1, hR, _⟩ := hp
  have hd : LipschitzWith 1 (deficit s.r s.B π) := LipschitzWith.of_dist_le_mul (fun x y => by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
      deficit_lipschitz s.r s.B s.radius π x y)
  have hf : LipschitzWith ⟨6 * s.κ, by linarith [s.slope]⟩ (field s.κ s.r s.B π) :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact field_lipschitz s.κ s.r s.B s.slope.le s.spacing s.radius π x y)
  have hc : Continuous (hard s π) := by
    unfold hard amplified exponent
    exact ((continuous_const.min (continuous_const.mul hd.continuous)).rexp).smul hf.continuous
  refine ⟨fun _ _ _ => rfl, hc.comp (continuous_id.sub continuous_const), ?_,
    p.x0 + target s.r π, ?_, ?_, ?_⟩
  · intro x y M hseg
    have hr := amplified_regular s.slope s.spacing s.radius s.base h1 s.cap s.localScale π s.far
      (x - p.x0) (y - p.x0) M (by
        intro θ hθ
        have he : x - p.x0 + θ • ((y - p.x0) - (x - p.x0)) = (x + θ • (y - x)) - p.x0 := by
          rw [sub_sub_sub_cancel_right]; abel
        rw [he]; exact hseg _ hθ)
    rwa [sub_sub_sub_cancel_right] at hr
  · simp only [instanceField, add_sub_cancel_left, hard, amplified,
      field_target s.κ s.r s.B s.spacing.le s.radius.le π s.far, smul_zero]
  · rw [← norm_neg, neg_sub, add_sub_cancel_left]
    apply le_of_pow_le_pow_left₀ two_ne_zero hR
    rw [target_norm_sq]
    exact s.root
  · intro x
    have e : x - (p.x0 + target s.r π) = x - p.x0 - target s.r π := by abel
    rw [e]
    unfold instanceField hard amplified
    rw [real_inner_smul_left]
    exact mul_nonneg (Real.exp_pos _).le
      (field_minty s.κ s.r s.B s.slope.le s.spacing s.radius π s.far _)

lemma insufficient (hp : spec.valid p) (A : Algorithm (V p) (V p) (V p)) (N : ℕ) (hN : N ≤ s.m) :
    ∃ π : Fin (2 * s.m + 1) ↪ Fin p.d,
      let O := oracle s π
      let X := fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2
      ¬ spec.successful p (instanceField s π) X ⟨(A.law : Measure _).prod (O.law : Measure _),
        inferInstance⟩ := by
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  let q := fun v => (A.query v).2 - p.x0
  let out := fun v => A.output v - p.x0
  obtain ⟨π, hbad⟩ := failure s N q out A.update (fun w : A.Seed × (ℕ → Unit) => A.initial w.1)
    P hp.2.1 hp.2.2.2 hN
  refine ⟨π, ?_⟩
  have he (w : A.Seed × (ℕ → Unit)) :
      ‖instanceField s π (execute (oracle s π) A (fun _ => N) w.1 w.2)‖ =
        loss s N q out A.update (A.initial w.1) π := by
    exact congrArg (fun x => ‖instanceField s π x‖)
      ((execute_eq_of_answer_eq (oracle s π) (instanceField s π) (fun _ _ _ => rfl) A N w.1 w.2).trans
        (execute_iterate (instanceField s π) A N w.1))
  change ¬ (Integrable (fun w : A.Seed × (ℕ → Unit) =>
    ‖instanceField s π (execute (oracle s π) A (fun _ => N) w.1 w.2)‖) (P : Measure _) ∧
    (∫ w : A.Seed × (ℕ → Unit),
    ‖instanceField s π (execute (oracle s π) A (fun _ => N) w.1 w.2)‖ ∂(P : Measure (A.Seed × (ℕ → Unit)))) ≤ p.ε)
  simpa only [he] using hbad

end LongTails.Proofs.GeneralizedMintyLowerBound
