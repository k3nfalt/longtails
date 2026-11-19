import LongTails.Algorithms.LocalizedClippedSubgradient
import LongTails.Proofs.TerminalClippingProbability

set_option backward.isDefEq.respectTransparency false

open MeasureTheory OracleTemplate OracleTemplate.ContinuizedSimilarQuasar
open LongTails.Setups.TerminalClippingConvex
open LongTails.Algorithms.LocalizedClippedSubgradient

namespace LongTails.Proofs.LocalizedClippedSubgradient

variable {Ω : Type} [MeasurableSpace Ω]

noncomputable def next (p : Public) (g : Vector p.d → Ω → Vector p.d) (proj : Vector p.d → Vector p.d)
    (x : Vector p.d) (ω : Ω) : Vector p.d := proj (proposal p x (g x ω))

noncomputable def transition (p : Public) (g : Vector p.d → Ω → Vector p.d) (proj : Vector p.d → Vector p.d)
    (s : Vector p.d × Vector p.d) (ω : Ω) : Vector p.d × Vector p.d :=
  (next p g proj s.1 ω, s.2 + s.1)

lemma next_measurable (p : Public) {g : Vector p.d → Ω → Vector p.d}
    {proj : Vector p.d → Vector p.d} (hg : Measurable (Function.uncurry g))
    (hp : Measurable proj) : Measurable (Function.uncurry (next p g proj)) := by
  change Measurable (fun w : Vector p.d × Ω => proj (p.x0 + clip p.R
    (w.1 - step p • clip (threshold p) (g w.1 w.2) - p.x0)))
  apply hp.comp
  apply measurable_const.add
  apply (measurable_clip p.R).comp
  apply Measurable.sub_const
  apply measurable_fst.sub
  exact ((measurable_clip (threshold p)).comp hg).const_smul (step p)

lemma transition_measurable (p : Public) {g : Vector p.d → Ω → Vector p.d}
    {proj : Vector p.d → Vector p.d} (hg : Measurable (Function.uncurry g))
    (hp : Measurable proj) : Measurable (Function.uncurry (transition p g proj)) :=
  ((next_measurable p hg hp).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk
    (measurable_fst.snd.add measurable_fst.fst)

lemma advance_pairs (p : Public) (g : Vector p.d → Ω → Vector p.d)
    (proj : Vector p.d → Vector p.d) (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω)
    (n k : ℕ) (x total : Vector p.d) :
    StochasticGradient.advance
      (fun j s => (algorithm p).update s
        ((TerminalClipping.sampleOracle p g proj P).answer [] ((algorithm p).query s) (ξ j)))
      (2 * n) k (.ready x total) =
      let s := iterateSamples (transition p g proj) n (x, total) (fun i => ξ (k + 2 * i.val))
      State.ready s.1 s.2 := by
  induction n generalizing k x total with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    change StochasticGradient.advance _ (2 * n) (k + 1 + 1)
      (State.ready (p := p) (next p g proj x (ξ k)) (total + x)) = _
    rw [ih]
    simp only [iterateSamples, transition, Fin.val_zero, mul_zero, Nat.add_zero, Fin.val_succ]
    congr 2 <;> congr 1 <;> funext i <;> congr 1 <;> omega

lemma execute_output (p : Public) (g : Vector p.d → Ω → Vector p.d)
    (proj : Vector p.d → Vector p.d) (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) :
    execute (TerminalClipping.sampleOracle p g proj P) (algorithm p)
      (fun _ => 2 * iterations p) () ξ =
      let s := iterateSamples (transition p g proj) (iterations p) (p.x0, 0)
        (fun i => ξ (2 * i.val))
      output p (.ready s.1 s.2) := by
  erw [StochasticGradient.execute_advance_of_answer _ _ _ _ _
    (fun k query => (TerminalClipping.sampleOracle p g proj P).answer [] query (ξ k))
    (fun _ _ => rfl)]
  have h := advance_pairs p g proj P ξ (iterations p) 0 p.x0 0
  simpa only [algorithm, Nat.zero_add] using congrArg (output p) h

end LongTails.Proofs.LocalizedClippedSubgradient
