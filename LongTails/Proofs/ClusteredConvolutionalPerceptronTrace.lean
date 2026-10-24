import LongTails.Proofs.ClusteredConvolutionalPerceptronBounds

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClusteredConvolutionalPerceptronTrace

open ManySampleConvolutionalPerceptronDynamics (State)
open ClusteredConvolutionalPerceptronDynamics
open ClusteredConvolutionalPerceptronBounds

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Trace (c : Control) (b : ι → ℝ) (p r : ι → E) where
  length : ℕ
  states : ℕ → State E
  times : ℕ → ℝ
  events : ℕ → ι
  valid : Trajectory c b p r states times events length

namespace Trace

variable {c : Control} {b : ι → ℝ} {p r : ι → E}

def endpoint (t : Trace c b p r) : State E := t.states t.length

def empty [Inhabited ι] (c : Control) (b : ι → ℝ) (p r : ι → E) : Trace c b p r where
  length := 0
  states _ := ⟨c.C, 0, 1, 0⟩
  times _ := 0
  events _ := default
  valid := ⟨rfl, rfl, by omega, by omega, by omega⟩

noncomputable def append (t : Trace c b p r) (j : ι)
    (hj : b j * t.endpoint.a * t.endpoint.q +
      c.δ * (t.endpoint.a * ⟪p j, t.endpoint.z⟫ + t.endpoint.t * ⟪r j, t.endpoint.z⟫) ≤ 0) :
    Trace c b p r where
  length := t.length + 1
  states := Function.update t.states (t.length + 1) (step (b j) c.δ (p j) (r j) t.endpoint)
  times := Function.update t.times (t.length + 1) (t.times t.length + t.endpoint.t)
  events := Function.update t.events t.length j
  valid := {
    initial := by
      rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ t.length + 1)]
      exact t.valid.initial
    time_zero := by
      rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ t.length + 1)]
      exact t.valid.time_zero
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
    time_update := by
      intro k hk
      by_cases hk0 : k < t.length
      · rw [Function.update_of_ne (by omega : k + 1 ≠ t.length + 1),
          Function.update_of_ne (by omega : k ≠ t.length + 1),
          Function.update_of_ne (by omega : k ≠ t.length + 1)]
        exact t.valid.time_update k hk0
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
    (hj : b j * t.endpoint.a * t.endpoint.q +
      c.δ * (t.endpoint.a * ⟪p j, t.endpoint.z⟫ + t.endpoint.t * ⟪r j, t.endpoint.z⟫) ≤ 0) :
    (t.append j hj).endpoint = step (b j) c.δ (p j) (r j) t.endpoint := by
  simp [endpoint, append]

lemma length_bound (t : Trace c b p r) (G : Geometry c b p r)
    (hδ1 : c.δ ≤ 1) (hinit : 8 * c.C ^ 2 ≤ c.h)
    (hnoise : (12 * (c.C + c.e) / c.ρ ^ 2) ^ 2 * c.L ≤ c.h) :
    t.length ≤ ⌈8 / c.ρ ^ 2 * Real.log (1 / c.δ)⌉₊ + 2 := by
  let K := ⌈8 / c.ρ ^ 2 * Real.log (1 / c.δ)⌉₊ + 2
  change t.length ≤ K
  by_contra h
  have hK : K < t.length := by omega
  have tr : Trajectory c b p r t.states t.times t.events K := {
    initial := t.valid.initial
    time_zero := t.valid.time_zero
    update := fun k hk => t.valid.update k (by omega)
    time_update := fun k hk => t.valid.time_update k (by omega)
    mistake := fun k hk => t.valid.mistake k (by omega) }
  have hs := terminal_separates G tr rfl hδ1 hinit hnoise (t.events K)
  have hm := t.valid.mistake K hK
  linarith

end Trace

end LongTails.Proofs.ClusteredConvolutionalPerceptronTrace
