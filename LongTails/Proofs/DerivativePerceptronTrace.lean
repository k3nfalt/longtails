import LongTails.Proofs.DerivativePerceptronConvergence

open scoped RealInnerProductSpace

namespace LongTails.Proofs.DerivativePerceptronTrace

open ManySampleConvolutionalPerceptronDynamics (State)
open ClusteredConvolutionalPerceptronDynamics (step)

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Trace (δ : ℝ) (b : ι → ℝ) (p r : ι → E) where
  length : ℕ
  states : ℕ → State E
  events : ℕ → ι
  initial : states 0 = ⟨1, 0, 1, 0⟩
  update : ∀ k < length, states (k + 1) = step (b (events k)) δ (p (events k)) (r (events k)) (states k)
  mistake : ∀ k < length, b (events k) * (states k).a * (states k).q +
    δ * ((states k).a * ⟪p (events k), (states k).z⟫ + (states k).t * ⟪r (events k), (states k).z⟫) ≤ 0

namespace Trace

variable {δ : ℝ} {b : ι → ℝ} {p r : ι → E}

def endpoint (t : Trace δ b p r) : State E := t.states t.length

def empty [Inhabited ι] (δ : ℝ) (b : ι → ℝ) (p r : ι → E) : Trace δ b p r where
  length := 0
  states _ := ⟨1, 0, 1, 0⟩
  events _ := default
  initial := rfl
  update := by omega
  mistake := by omega

noncomputable def append (t : Trace δ b p r) (j : ι)
    (hj : b j * t.endpoint.a * t.endpoint.q +
      δ * (t.endpoint.a * ⟪p j, t.endpoint.z⟫ + t.endpoint.t * ⟪r j, t.endpoint.z⟫) ≤ 0) :
    Trace δ b p r where
  length := t.length + 1
  states := Function.update t.states (t.length + 1) (step (b j) δ (p j) (r j) t.endpoint)
  events := Function.update t.events t.length j
  initial := by
      rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ t.length + 1)]
      exact t.initial
  update := by
      intro k hk
      by_cases hk0 : k < t.length
      · rw [Function.update_of_ne (by omega : k + 1 ≠ t.length + 1),
          Function.update_of_ne (by omega : k ≠ t.length),
          Function.update_of_ne (by omega : k ≠ t.length + 1)]
        exact t.update k hk0
      · have he : k = t.length := by omega
        subst k
        simp [endpoint]
  mistake := by
      intro k hk
      by_cases hk0 : k < t.length
      · rw [Function.update_of_ne (by omega : k ≠ t.length),
          Function.update_of_ne (by omega : k ≠ t.length + 1)]
        exact t.mistake k hk0
      · have he : k = t.length := by omega
        subst k
        simpa [Function.update_of_ne (by omega : t.length ≠ t.length + 1), endpoint] using hj

lemma append_endpoint (t : Trace δ b p r) (j : ι)
    (hj : b j * t.endpoint.a * t.endpoint.q +
      δ * (t.endpoint.a * ⟪p j, t.endpoint.z⟫ + t.endpoint.t * ⟪r j, t.endpoint.z⟫) ≤ 0) :
    (t.append j hj).endpoint = step (b j) δ (p j) (r j) t.endpoint := by
  simp [endpoint, append]

lemma length_bound (tuning : DerivativePerceptronParameters.Tuning)
    (tr : Trace tuning.residualScale b p r) (w : E) (hw : ‖w‖ = 1)
    (hp : ∀ i, ‖p i‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1)
    (hsep : ∀ i, tuning.κ ≤ ⟪r i, w⟫)
    (hb : ∀ i, tuning.backgroundScale ≤ |b i|)
    (hbu : ∀ i, |b i| ≤ tuning.stepScale) : tr.length < tuning.iterations := by
  by_contra hn
  have hK : tuning.iterations ≤ tr.length := by omega
  exact DerivativePerceptronConvergence.tuned_mistake_horizon_impossible tuning
    tr.states (fun k => b (tr.events k)) (fun k => p (tr.events k)) (fun k => r (tr.events k))
    w hw tr.initial (fun k hk => tr.update k (by omega))
    (fun k _ => hp (tr.events k)) (fun k _ => hr (tr.events k))
    (fun k _ => hsep (tr.events k)) (fun k _ => hb (tr.events k))
    (fun k _ => hbu (tr.events k)) (fun k hk => tr.mistake k (by omega))

end Trace

end LongTails.Proofs.DerivativePerceptronTrace
