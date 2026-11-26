import LongTails.Algorithms.TerminalClippingSingleLog
import LongTails.Proofs.TerminalClippingExecution

set_option backward.isDefEq.respectTransparency false

open MeasureTheory LongTails.Setups.TerminalClippingConvex

namespace OracleTemplate.TerminalClippingSingleLog

lemma algorithm_allowed (q : Public) : spec.allowedAlgorithm q (algorithm q) := by
  let η : State q → ℝ
    | .sample t _ => slope q (horizon q) * (horizon q - t : ℕ)
    | .project .. => 0
  let C : State q → ℝ
    | .sample t _ => if t < horizon q then level q (horizon q) else 0
    | .project .. => 0
  refine ⟨η, C, ?_, fun _ => ⟨rfl, rfl⟩, ?_⟩
  · intro s
    cases s with
    | project => exact ⟨le_rfl, le_rfl⟩
    | sample t x =>
      dsimp [η, C, slope, level, momentScale]
      constructor
      · positivity
      · split <;> positivity
  · intro s
    cases s with
    | project => exact fun _ => ⟨rfl, rfl⟩
    | sample => exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def path (g : E → Ω → E) (proj : E → E) (k C : ℝ) (T : ℕ)
    (x : E) (ξ : ℕ → Ω) : ℕ → E
  | 0 => x
  | t+1 =>
    let y := path g proj k C T x ξ t
    proj (y - (k * (T - t : ℕ)) • clip C (g y (ξ t)))

lemma path_mem {X : Set E} (g : E → Ω → E) {proj : E → E} (hp : ∀ w, proj w ∈ X)
    (k C : ℝ) (T : ℕ) {x : E} (hx : x ∈ X) (ξ : ℕ → Ω) :
    ∀ t, path g proj k C T x ξ t ∈ X
  | 0 => hx
  | _+1 => hp _

lemma path_measurable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    {proj : E → E} (hp : Measurable proj) (k C : ℝ) (T : ℕ) (n : ℕ) :
    Measurable (fun s : E × (ℕ → Ω) => path g proj k C T s.1 s.2 n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    exact hp.comp (ih.sub (measurable_const.smul ((measurable_clip C).comp
      (hg.comp (ih.prodMk ((measurable_pi_apply n).comp measurable_snd))))))

lemma execute_path {Ω : Type} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (proj : Vector q.d → Vector q.d)
    (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) (n : ℕ) (hn : n ≤ horizon q) :
    execute (TerminalClipping.sampleOracle q g proj P) (algorithm q) (fun _ => 2*n) () ξ =
      path g proj (slope q (horizon q)) (level q (horizon q)) (horizon q) q.x0
        (fun i => ξ (2*i)) n := by
  let y := path g proj (slope q (horizon q)) (level q (horizon q)) (horizon q) q.x0
    (fun i => ξ (2*i))
  let step : ℕ → State q → State q := fun (k : ℕ) (s : State q) => (algorithm q).update s
    ((TerminalClipping.sampleOracle q g proj P).answer [] ((algorithm q).query s) (ξ k))
  have h (l t : ℕ) (ht : t+l ≤ horizon q) :
      StochasticGradient.advance step (2*l) (2*t) (.sample t (y t)) =
        .sample (t+l) (y (t+l)) := by
    induction l generalizing t with
    | zero => simp [StochasticGradient.advance]
    | succ l ih =>
      rw [show 2*(l+1) = (2*l+1)+1 by omega, StochasticGradient.advance, StochasticGradient.advance]
      rw [show 2*t+1+1 = 2*(t+1) by omega]
      have hstep : step (2*t+1) (step (2*t) (.sample t (y t))) = .sample (t+1) (y (t+1)) := by
        simp [step, algorithm, TerminalClipping.sampleOracle, show t < horizon q by omega, y, path,
          clipReply, clip]
      rw [hstep, ih (t+1) (by omega), show t+1+l = t+(l+1) by omega]
  erw [StochasticGradient.execute_advance_of_answer _ _ _ _ _
    (fun k query => (TerminalClipping.sampleOracle q g proj P).answer [] query (ξ k)) (fun _ _ => rfl)]
  change (algorithm q).output (StochasticGradient.advance step (2*n) (2*0) (.sample 0 (y 0))) = y n
  rw [h n 0 (by omega), Nat.zero_add]
  rfl

end OracleTemplate.TerminalClippingSingleLog
