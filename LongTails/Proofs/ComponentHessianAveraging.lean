import LongTails.Proofs.ComponentHessianInstance
import LongTails.Proofs.FiniteSumNondualLowerBound

set_option backward.isDefEq.respectTransparency false

namespace LongTails.Proofs.ComponentHessianAveraging

open OracleTemplate MeasureTheory LongTails.Setups.ConvexFiniteSumMeanSquareHessian
open ComponentHessianInstance

variable {p : Params}

abbrev Method (p : Params) := Algorithm (Fin p.n × Point p) (Reply p) (Point p)

noncomputable def gap (I : Instance p) (A : Method p) (T : ℕ) (ω : A.Seed × (ℕ → Unit)) : ℝ :=
  objective I (execute (exactOracle I) A (fun _ => T) ω.1 ω.2) - objective I I.xstar

lemma extract {U V : Type*} [Fintype U] [Fintype V] (I : U → V → Instance p) (A : Method p)
    (b : Fin 1 → ℕ) (hu : 0 < Fintype.card U) (hv : 0 < Fintype.card V)
    (hI : ∀ u v, spec.admissible p (I u v) (exactOracle (I u v))) {C : ℝ} (hC : 32 * p.ε < C)
    (hpoint : ∀ ω, C * Fintype.card U * Fintype.card V ≤ 32 * ∑ u, ∑ v, gap (I u v) A (b 0) ω) :
    ∃ (J : Instance p) (O : Oracle (Fin p.n × Point p) (Reply p)), spec.admissible p J O ∧
      ¬ spec.successful p J (fun s : A.Seed × ((k : ℕ) → O.Seed k) => execute O A b s.1 s.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  have hb : (fun _ : Fin 1 => b 0) = b := funext (fun i => congrArg b (Subsingleton.elim 0 i))
  by_contra hn
  push Not at hn
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  have hs (u v) : Integrable (gap (I u v) A (b 0)) (P : Measure _) ∧
      (∫ ω, gap (I u v) A (b 0) ω ∂(P : Measure _)) ≤ p.ε := by
    have h := (hn (I u v) (exactOracle (I u v)) (hI u v)).2
    rw [← hb] at h
    exact h
  have hl := FiniteSumNondualLowerBound.finite_integral_lower P
    (fun ω u v => gap (I u v) A (b 0) ω) _ (fun u v => (hs u v).1) hpoint
  have hub : (∑ u, ∑ v, ∫ ω, gap (I u v) A (b 0) ω ∂(P : Measure _)) ≤
      ∑ _ : U, ∑ _ : V, p.ε :=
    Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => (hs u v).2))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hub
  have hh := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hC
    (show (0 : ℝ) < Fintype.card U by exact_mod_cast hu))
    (show (0 : ℝ) < Fintype.card V by exact_mod_cast hv)
  linarith only [hl, hh, mul_le_mul_of_nonneg_left hub (by norm_num : (0 : ℝ) ≤ 32)]

end LongTails.Proofs.ComponentHessianAveraging
