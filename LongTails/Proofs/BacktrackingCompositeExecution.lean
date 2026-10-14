import LongTails.Proofs.BacktrackingCompositeRun
import LongTails.Proofs.Execution

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.CompositeParameterFree

open LongTails.Setups.CompositeGeneralizedParameterFree

open CompositeGeneralized

def answerOf (p : Public) (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E) :
    Query p → p.E
  | .gradient x => grad x
  | .prox a z v => prox a z v

noncomputable def embed (p : Public) (s : TState p.E) (gy q : p.E) : BtState p.E :=
  ⟨s.A, s.x, s.z, s.h, 0, gy, q⟩

lemma three_calls (p : Public) (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E)
    (s : TState p.E) (gy q : p.E) :
    let A := backtrackingComposite p
    let T := fun st => A.update st (answerOf p grad prox ((A.query st).2))
    T^[3] (embed p s gy q) =
      embed p (trial grad prox s) (grad (trialY s)) (trialP grad prox s) := by
  intro A T
  have h1 : T (embed p s gy q) = ⟨s.A, s.x, s.z, s.h, 1, grad (trialY s), q⟩ := by
    simp +decide only [T, A, backtrackingComposite, embed, answerOf, trialY, trialA, ↓reduceIte]
  have h2 : T ⟨s.A, s.x, s.z, s.h, 1, grad (trialY s), q⟩ =
      ⟨s.A, s.x, s.z, s.h, 2, grad (trialY s), trialP grad prox s⟩ := by
    simp +decide only [T, A, backtrackingComposite, answerOf, trialP, trialY, trialA, ↓reduceIte]
  have h3 : T ⟨s.A, s.x, s.z, s.h, 2, grad (trialY s), trialP grad prox s⟩ =
      embed p (trial grad prox s) (grad (trialY s)) (trialP grad prox s) := by
    by_cases hacc : Accepts grad prox s
    · rw [trial_accept hacc]
      simp +decide only [T, A, backtrackingComposite, answerOf, embed, trialX, trialY, trialA,
        trialP, ↓reduceIte]
      rw [ite_eq_left (by exact hacc)]
    · rw [trial_reject hacc]
      simp +decide only [T, A, backtrackingComposite, answerOf, embed, trialY, trialA,
        trialP, ↓reduceIte]
      rw [ite_eq_right (by exact hacc)]
  erw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_one, h1, h2,
    h3]

lemma execute_backtracking (p : Public) (grad : p.E → p.E) (prox : ℝ → p.E → p.E → p.E)
    (n : ℕ) :
    execute { answer := fun _ (_, q) _ => answerOf p grad prox q } (backtrackingComposite p) (fun _ => (3 * n)) =
      (run grad prox p.x0 p.h0 n).x := by
  erw [execute_iterate]
  let A := backtrackingComposite p
  let T := fun st => A.update st (answerOf p grad prox ((A.query st).2))
  have hi : ∀ n, ∃ gy q, T^[3 * n] (A.initial ()) = embed p (run grad prox p.x0 p.h0 n) gy q := by
    intro n
    induction n with
    | zero => exact ⟨0, p.x0, rfl⟩
    | succ n ih =>
      obtain ⟨gy, q, h⟩ := ih
      refine ⟨grad (trialY (run grad prox p.x0 p.h0 n)),
        trialP grad prox (run grad prox p.x0 p.h0 n), ?_⟩
      rw [show 3 * (n + 1) = 3 + 3 * n by ring, Function.iterate_add_apply, h]
      exact three_calls p grad prox _ gy q
  obtain ⟨gy, q, h⟩ := hi n
  change A.output (T^[3 * n] (A.initial ())) = _
  rw [h]
  rfl

end OracleTemplate.CompositeParameterFree
