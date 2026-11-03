import LongTails.Algorithms.ComponentEnvelope
import LongTails.Algorithms.Svrg

namespace LongTails.Algorithms.FiniteSumNondualProx

open OracleTemplate.ComponentEnvelope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def step (C : Set E) (μ η : ℝ) (c x v : E) : E :=
  OracleTemplate.SaddlePoint.project C ((1 / (1 + η * μ)) • (x - η • v + (η * μ) • c))

noncomputable def residual (η : ℝ) (x w gx gw : E) : E :=
  gw - gx + (1 / η) • (x - w)

noncomputable def snapshot {Q : Type*} (x : Q) {n : ℕ} :
    (m : ℕ) → (Fin m → Fin n) → Program (Fin n × Q) E (Fin m → E)
  | 0, _ => .done Fin.elim0
  | m + 1, indices => .ask (indices 0, x) fun first =>
      (snapshot x m (fun j => indices j.succ)).map (Fin.cons first)

noncomputable def innerRun {n : ℕ} (oracle : Fin n × E → E) (C : Set E)
    (μ η : ℝ) (c z : E) : E → List (Fin n) → E × List E
  | x, [] => (x, [])
  | x, i :: tail =>
    let w := step C μ η c x (OracleTemplate.FiniteSum.estimator oracle z x i)
    let rest := innerRun oracle C μ η c z w tail
    (rest.1, w :: rest.2)

noncomputable def epoch {n : ℕ} (oracle : Fin n × E → E) (C : Set E)
    (μ η : ℝ) (c z : E) (seed : List (Fin n)) : E :=
  (seed.length : ℝ)⁻¹ • (innerRun oracle C μ η c z z seed).2.sum

noncomputable def epochRun {n m : ℕ} (oracle : Fin n × E → E) (C : Set E)
    (μ η : ℝ) (c : E) : (s : ℕ) → E → (Fin s → Fin m → Fin n) → E
  | 0, z, _ => z
  | s + 1, z, seed => epochRun oracle C μ η c s
      (epoch oracle C μ η c z (List.ofFn (seed 0))) (fun j => seed j.succ)

structure Certificate (E : Type*) where
  point : E
  gradient : E
  error : E

noncomputable def cacheMean {n : ℕ} (cache : Fin n → E) : E :=
  (n : ℝ)⁻¹ • ∑ i, cache i

noncomputable def innerPlan {n : ℕ} (C : Set E) (μ η : ℝ) (c : E)
    (cache : Fin n → E) : E → List (Fin n) → Program (Fin n × E) E (E × List E)
  | x, [] => .done (x, [])
  | x, i :: tail => .ask (i, x) fun reply =>
    let w := step C μ η c x (reply - cache i + cacheMean cache)
    (innerPlan C μ η c cache w tail).map (fun rest => (rest.1, w :: rest.2))

noncomputable def epochPlan {n : ℕ} (C : Set E) (μ η : ℝ) (c z : E)
    (seed : List (Fin n)) : Program (Fin n × E) E E :=
  (snapshot z n id).bind fun cache =>
    (innerPlan C μ η c cache z seed).map fun rest => (seed.length : ℝ)⁻¹ • rest.2.sum

noncomputable def epochsPlan {n m : ℕ} (C : Set E) (μ η : ℝ) (c : E) :
    (s : ℕ) → E → (Fin s → Fin m → Fin n) → Program (Fin n × E) E E
  | 0, z, _ => .done z
  | s + 1, z, seed => (epochPlan C μ η c z (List.ofFn (seed 0))).bind fun next =>
      epochsPlan C μ η c s next (fun j => seed j.succ)

noncomputable def solvePlan {n : ℕ} (C : Set E) (L μ : ℝ) (c : E) (s : ℕ)
    (seed : Fin s → Fin (144 * n) → Fin n) : Program (Fin n × E) E (Certificate E) :=
  (snapshot c n id).bind fun initialCache =>
    let initial := step C μ (1 / L) c c (cacheMean initialCache)
    (epochsPlan C μ (1 / (12 * L)) c s initial seed).bind fun x =>
      (snapshot x n id).bind fun currentCache =>
        let gx := cacheMean currentCache
        let w := step C μ (1 / L) c x gx
        (snapshot w n id).map fun finalCache =>
          let gw := cacheMean finalCache
          ⟨w, gw, residual (1 / L) x w gx gw⟩

def mapQueries {Q Q' Reply U : Type*} (transform : Q → Q') :
    Program Q Reply U → Program Q' Reply U
  | .done u => .done u
  | .ask q next => .ask (transform q) (fun reply => mapQueries transform (next reply))

end LongTails.Algorithms.FiniteSumNondualProx
