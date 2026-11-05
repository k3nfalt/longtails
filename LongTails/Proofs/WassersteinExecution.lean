import LongTails.Algorithms.WassersteinAcceleratedProximal
import LongTails.Proofs.WassersteinOracleGeometry
import LongTails.Proofs.ExecutionHistory

open MeasureTheory OracleTemplate
open LongTails.Setups.WassersteinSmoothComposite
open LongTails.Algorithms.WassersteinAcceleratedProximal

namespace LongTails.Proofs.WassersteinExecution

noncomputable def run (p : Public) (R : ℕ → Query p.d → Reply p.d) : ℕ → State p.d
  | 0 => ⟨.forward, p.initial, p.initial, p.initial, 0⟩
  | n + 1 => update (run p R n) (R n (query p.L (run p R n)))

lemma execute_eq_run (p : Public) (O : Oracle (Query p.d) (Reply p.d))
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) (K : ℕ) :
    execute O (algorithm p) (fun _ => K) seed ξ =
      (run p (fun n q => executeAnswerAt O (algorithm p) seed ξ n (0, q)) K).current := by
  let R := fun n q => executeAnswerAt O (algorithm p) seed ξ n (0, q)
  have hr : ∀ n, (executeIndexedState O (algorithm p) seed ξ n).1 = run p R n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [run, ← ih]
      rfl
  unfold execute
  rw [executeWithTrace_eq_executeIndexedState]
  exact congrArg State.current (hr K)

lemma response_correct {p : Params} {I : Instance p.toPublic}
    {O : Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O)
    (seed : (algorithm p.toPublic).Seed) (ξ : (k : ℕ) → O.Seed k) (n : ℕ) (q : Query p.d) :
    CorrectReply p.toPublic I q (executeAnswerAt O (algorithm p.toPublic) seed ξ n (0, q)) :=
  h.replies _ _ q

lemma forward_pair {p : Params} {I : Instance p.toPublic}
    {O : Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O)
    (hL : 0 < p.L) (ξ : (k : ℕ) → O.Seed k)
    (R : ℕ → Query p.d → Reply p.d)
    (hR : ∀ n q, CorrectReply p.toPublic I q (R n q)) (n : ℕ)
    (hs : (run p.toPublic R n).phase = .forward) :
    ∃ b u : Distribution p.d,
      run p.toPublic R (n + 2) =
        { run p.toPublic R n with phase := .transport, previous := (run p.toPublic R n).current, current := u, probe := b, steps := (run p.toPublic R n).steps + 1 } ∧
      u ∈ I.Q ∧ ∀ v ∈ I.Q,
        (1 / p.L) * (objective I u - objective I v) ≤
          squaredDistance (run p.toPublic R n).probe v - squaredDistance u v -
            (1 / 2 : ℝ) * squaredDistance (run p.toPublic R n).probe u := by
  obtain ⟨b, hb, hf⟩ := hR n (.forward (1 / (2 * p.L)) (run p.toPublic R n).probe)
  have hn : run p.toPublic R (n + 1) =
      { run p.toPublic R n with phase := .proximal, probe := b } := by
    rw [run]
    simp only [query, hs, hb, update]
  obtain ⟨u, hu, huQ, hp⟩ := hR (n + 1) (.proximal (1 / (2 * p.L)) b) (by positivity)
  refine ⟨b, u, ?_, huQ, ?_⟩
  · rw [show n + 2 = (n + 1) + 1 by omega, run, hn]
    simp only [query, hu, update]
  · intro v hv
    exact WassersteinOracleGeometry.split_evi h hL ξ _ b u v huQ hv hf hp

lemma transport_step {p : Params} {I : Instance p.toPublic}
    (R : ℕ → Query p.d → Reply p.d)
    (hR : ∀ n q, CorrectReply p.toPublic I q (R n q)) (n : ℕ)
    (hs : (run p.toPublic R n).phase = .transport)
    (hx : (run p.toPublic R n).current ∈ I.Q) :
    ∃ T : OptimalTransport (run p.toPublic R n).current (run p.toPublic R n).previous,
      run p.toPublic R (n + 1) =
        { run p.toPublic R n with phase := .forward, probe := extrapolate T.toTransport ((((run p.toPublic R n).steps : ℝ) - 1) / (((run p.toPublic R n).steps : ℝ) + 2)) } := by
  obtain ⟨T, hT⟩ := hR n (.transport (run p.toPublic R n).current
    (run p.toPublic R n).previous) hx
  refine ⟨T, ?_⟩
  rw [run]
  simp only [query, hs, hT, update]

lemma triple_step {p : Params} {I : Instance p.toPublic}
    {O : Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O)
    (hL : 0 < p.L) (ξ : (k : ℕ) → O.Seed k)
    (R : ℕ → Query p.d → Reply p.d)
    (hR : ∀ n q, CorrectReply p.toPublic I q (R n q)) (n : ℕ)
    (hs : (run p.toPublic R n).phase = .transport)
    (hx : (run p.toPublic R n).current ∈ I.Q) :
    ∃ (T : OptimalTransport (run p.toPublic R n).current (run p.toPublic R n).previous)
      (b u : Distribution p.d),
      run p.toPublic R (n + 3) =
        { run p.toPublic R n with phase := .transport, previous := (run p.toPublic R n).current, current := u, probe := b, steps := (run p.toPublic R n).steps + 1 } ∧
      u ∈ I.Q ∧ ∀ v ∈ I.Q,
        let y := extrapolate T.toTransport
          ((((run p.toPublic R n).steps : ℝ) - 1) / (((run p.toPublic R n).steps : ℝ) + 2))
        (1 / p.L) * (objective I u - objective I v) ≤
          squaredDistance y v - squaredDistance u v - (1 / 2 : ℝ) * squaredDistance y u := by
  obtain ⟨T, hT⟩ := transport_step R hR n hs hx
  have hf : (run p.toPublic R (n + 1)).phase = .forward := by rw [hT]
  obtain ⟨b, u, he, hu, hv⟩ := forward_pair h hL ξ R hR (n + 1) hf
  refine ⟨T, b, u, ?_, hu, ?_⟩
  · rw [hT] at he
    simpa only [Nat.add_assoc] using he
  · intro v hvQ
    have he := hv v hvQ
    rw [hT] at he
    exact he

end LongTails.Proofs.WassersteinExecution
