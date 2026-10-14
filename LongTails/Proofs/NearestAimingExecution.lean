import LongTails.Setups.LocalStrongAiming
import LongTails.Proofs.Execution
import Mathlib.Tactic

namespace OracleTemplate.NearestAiming

open LongTails.Setups.LocalStrongAiming

noncomputable def certifiedNesterov (p : Public) : CertifiedAlgorithm p :=
  ⟨nesterov p.L p.μ p.x0, by
    refine ⟨Prod.fst, Prod.snd, ?_, ?_, ?_, ?_⟩
    · intro seed
      exact ⟨rfl, rfl⟩
    · intro state
      rfl
    · intro state reply
      rfl
    · intro state
      rfl⟩

lemma execute_nesterov (p : Public) (f : p.E → ℝ) (oracle : Oracle p.E p.E)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (horacle : ∀ k seed x, HasGradientAt f (oracle.answer k (0, x) seed) x)
    (K : ℕ) (seed : (certifiedNesterov p).val.Seed)
    (oracleSeed : (k : ℕ) → oracle.Seed k) :
    execute oracle (certifiedNesterov p).val (fun _ => K) seed oracleSeed =
      nesterovOutput (gradient f) p.L p.μ p.x0 K := by
  rw [execute_eq_of_answer_eq oracle (gradient f)
    (fun k x seed => (horacle k seed x).unique (hg x))]
  erw [execute_iterate]
  rfl

end OracleTemplate.NearestAiming
