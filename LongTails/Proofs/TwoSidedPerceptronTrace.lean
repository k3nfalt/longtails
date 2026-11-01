import LongTails.Proofs.TwoSidedPerceptronCounting

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSidedPerceptronTrace

open TwoSidedPerceptronDynamics TwoSidedPerceptronTrajectory TwoSidedPerceptronCounting

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Trace (c : Control) (b : ι → ℝ) (p r : ι → E) where
  length : ℕ
  states : ℕ → State E
  events : ℕ → ι
  valid : Trajectory c b p r states events length

namespace Trace

variable {c : Control} {b : ι → ℝ} {p r : ι → E}

def endpoint (t : Trace c b p r) : State E := t.states t.length

noncomputable def empty [Inhabited ι] (c : Control) (b : ι → ℝ) (p r : ι → E) : Trace c b p r where
  length := 0
  states _ := c.start
  events _ := default
  valid := ⟨rfl, by omega, by omega⟩

lemma empty_endpoint [Inhabited ι] : (empty c b p r).endpoint = (c.start : State E) := rfl

noncomputable def append (t : Trace c b p r) (j : ι)
    (hj : margin (b j) c.δ (p j) (r j) t.endpoint ≤ 0) : Trace c b p r where
  length := t.length + 1
  states := Function.update t.states (t.length + 1) (step (b j) c.δ (p j) (r j) t.endpoint)
  events := Function.update t.events t.length j
  valid := {
    initial := by
      rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ t.length + 1)]
      exact t.valid.initial
    update := by
      intro k hk
      by_cases hk0 : k < t.length
      · rw [Function.update_of_ne (by omega : k + 1 ≠ t.length + 1),
          Function.update_of_ne (by omega : k ≠ t.length),
          Function.update_of_ne (by omega : k ≠ t.length + 1)]
        exact t.valid.update k hk0
      · have he : k = t.length := by omega
        subst k
        simp [endpoint]
    mistake := by
      intro k hk
      by_cases hk0 : k < t.length
      · rw [Function.update_of_ne (by omega : k ≠ t.length),
          Function.update_of_ne (by omega : k ≠ t.length + 1)]
        exact t.valid.mistake k hk0
      · have he : k = t.length := by omega
        subst k
        simpa [Function.update_of_ne (by omega : t.length ≠ t.length + 1), endpoint] using hj }

lemma append_endpoint (t : Trace c b p r) (j : ι)
    (hj : margin (b j) c.δ (p j) (r j) t.endpoint ≤ 0) :
    (t.append j hj).endpoint = step (b j) c.δ (p j) (r j) t.endpoint := by
  simp [endpoint, append]

lemma length_lt {w : E} (t : Trace c b p r) (G : Geometry c b p r w) {K m : ℕ}
    (hR : Regime c K) (hm0 : 0 < m)
    (hdecay : (1 - c.clo ^ 2 / 8) ^ m * (2 * c.a₀) ≤ c.threshold (2 * m))
    (hK : 2 * m + c.bound m < K) : t.length < K := by
  by_contra h
  replace h := not_lt.mp h
  have tr : Trajectory c b p r t.states t.events K := {
    initial := t.valid.initial
    update := fun k hk => t.valid.update k (by omega)
    mistake := fun k hk => t.valid.mistake k (by omega) }
  have := mistakes_le hR G tr hm0 hdecay
  linarith

end Trace

end LongTails.Proofs.TwoSidedPerceptronTrace
