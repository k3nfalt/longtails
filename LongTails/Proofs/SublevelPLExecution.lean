import LongTails.Proofs.SublevelPLProcess
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.IIDBlocks

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.SublevelRobustGradient

open RobustGradient

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma advance_plainStep (L : ℝ) {n : ℕ} (G : E → (Fin n → Ω) → E) (ζ : ℕ → Fin n → Ω) :
    ∀ (K call : ℕ) (x : E),
      StochasticGradient.advance (fun call x => x - (1 / L) • G x (ζ call)) K call x =
        iterFrom L G ζ call x K
  | 0, _, _ => rfl
  | K + 1, call, x => by
    rw [StochasticGradient.advance, advance_plainStep L G ζ K (call + 1), iterFrom_shift]

noncomputable def blocks (n : ℕ) (ξ : ℕ → Ω) : ℕ → Fin n → Ω := fun k i => ξ (k * n + i.val)

noncomputable def blockMap (L τ α σ Δ ε : ℝ) (g : E → Ω → E) :
    E → (Fin (subbatches L τ α Δ ε * subsize L τ α σ Δ ε) → Ω) → E :=
  fun x block => estimate (subbatches_pos L τ α Δ ε) (radius L τ α ε) g x block

lemma execute_method (P : ProbabilityMeasure (ℕ → Ω)) (g : E → Ω → E)
    (L τ α σ Δ ε : ℝ) (x0 : E) (K : ℕ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (method L τ α σ Δ ε x0)
      (fun _ => K * (subbatches L τ α Δ ε * subsize L τ α σ Δ ε)) () ξ =
      iter L (blockMap L τ α σ Δ ε g) x0
        (blocks (subbatches L τ α Δ ε * subsize L τ α σ Δ ε) ξ) K := by
  have h := execute_batched (Ω := Ω)
    (Nat.mul_pos (subbatches_pos L τ α Δ ε) (subsize_pos L τ α σ Δ ε))
    (plainStep (1 / L) x0) (fun x _ => x)
    (fun _ r => aggregate (m := subbatches L τ α Δ ε) (b := subsize L τ α σ Δ ε)
      (subbatches_pos L τ α Δ ε) (radius L τ α ε) r) (0 : E) P g ξ K ()
  refine h.trans ?_
  show StochasticGradient.advance (fun call x => x - (1 / L) • blockMap L τ α σ Δ ε g x
    (blocks (subbatches L τ α Δ ε * subsize L τ α σ Δ ε) ξ call)) K 0 x0 = _
  exact advance_plainStep L (blockMap L τ α σ Δ ε g)
    (blocks (subbatches L τ α Δ ε * subsize L τ α σ Δ ε) ξ) K 0 x0

lemma measurable_blockMap (L τ α σ Δ ε : ℝ) {g : E → Ω → E}
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (blockMap L τ α σ Δ ε g)) :=
  measurable_estimate (subbatches_pos L τ α Δ ε) (radius L τ α ε) hg

lemma blocks_preserving (p : Measure Ω) [IsProbabilityMeasure p]
    (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ => ξ k) = p) (n : ℕ) :
    MeasurePreserving (blocks (Ω := Ω) n) P
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p) :=
  FiniteVariance.infinite_block_law p P hind hmarg n

end OracleTemplate.SublevelRobustGradient
