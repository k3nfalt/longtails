import LongTails.Proofs.ManySampleConvolutionalPerceptronCounting

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronTrace

open ManySampleConvolutionalPerceptronDynamics
open ManySampleConvolutionalPerceptronTrajectory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

structure Trace (g : Gains E n) where
  length : ℕ
  states : ℕ → State E
  events : ℕ → Option (Fin n)
  initial : states 0 = ⟨1, 0, 1, 0⟩
  step : ∀ j, j < length → states (j + 1) = next g (events j) (states j)
  permitted : ∀ j, j < length → Permitted g (events j) (states j)

namespace Trace

variable {g : Gains E n}

def endpoint (t : Trace g) : State E := t.states t.length

def negatives (t : Trace g) : ℕ := negativeCount t.events t.length

def empty (g : Gains E n) : Trace g where
  length := 0
  states _ := ⟨1, 0, 1, 0⟩
  events _ := none
  initial := rfl
  step j hj := by omega
  permitted j hj := by omega

noncomputable def append (t : Trace g) (e : Option (Fin n)) (he : Permitted g e t.endpoint) : Trace g where
  length := t.length + 1
  states := Function.update t.states (t.length + 1) (next g e t.endpoint)
  events := Function.update t.events t.length e
  initial := by
    rw [Function.update_of_ne (by omega : (0 : ℕ) ≠ t.length + 1)]
    exact t.initial
  step j hj := by
    by_cases hj0 : j < t.length
    · rw [Function.update_of_ne (by omega : j + 1 ≠ t.length + 1),
        Function.update_of_ne (by omega : j ≠ t.length),
        Function.update_of_ne (by omega : j ≠ t.length + 1)]
      exact t.step j hj0
    · have hj' : j = t.length := by omega
      subst j
      simp [endpoint]
  permitted j hj := by
    by_cases hj0 : j < t.length
    · rw [Function.update_of_ne (by omega : j ≠ t.length),
        Function.update_of_ne (by omega : j ≠ t.length + 1)]
      exact t.permitted j hj0
    · have hj' : j = t.length := by omega
      subst j
      simpa [Function.update_of_ne (by omega : t.length ≠ t.length + 1), endpoint] using he

lemma append_endpoint (t : Trace g) (e : Option (Fin n)) (he : Permitted g e t.endpoint) :
    (t.append e he).endpoint = next g e t.endpoint := by simp [endpoint, append]

lemma count_congr {e f : ℕ → Option (Fin n)} {K : ℕ} (h : ∀ j, j < K → e j = f j) :
    negativeCount e K = negativeCount f K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [negativeCount, ih (fun j hj => h j (by omega)), h K (by omega)]

lemma append_negatives (t : Trace g) (e : Option (Fin n)) (he : Permitted g e t.endpoint) :
    (t.append e he).negatives = t.negatives + if e.isSome then 1 else 0 := by
  have hc : negativeCount (Function.update t.events t.length e) t.length =
      negativeCount t.events t.length := by
    apply count_congr
    intro j hj
    exact Function.update_of_ne (by omega) _ _
  simp only [negatives, append, negativeCount, Function.update_self, hc]

end Trace

end LongTails.Proofs.ManySampleConvolutionalPerceptronTrace
