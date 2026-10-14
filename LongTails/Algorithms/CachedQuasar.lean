import LongTails.Algorithms.Svrg

noncomputable section

namespace OracleTemplate.SimilarQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def query (θ : ℝ) (s : E × E) : E :=
  (1 / (1 + θ)) • (s.1 + θ • s.2)

def update (γ θ μ : ℝ) (s : E × E) (g : E) : E × E :=
  let y := query θ s
  (y - (θ ^ 2 / μ) • g,
    (1 - γ * θ) • s.2 + (γ * θ) • y - (θ / μ) • g)

def innerRun {n : ℕ} [NeZero n] (g : Fin n × E → E) (γ θ μ : ℝ) (snapshot : E) :
    ℕ → (E × E) → E × E
  | 0, s => s
  | k + 1, s => innerRun g γ θ μ snapshot k
      (update γ θ μ s (FiniteSum.estimator g snapshot (query θ s) 0))

def epoch {n : ℕ} [NeZero n] (g : Fin n × E → E) (γ θ μ : ℝ) (m : ℕ)
    (s : E × E) : E × E := innerRun g γ θ μ s.1 m s

def run {n : ℕ} [NeZero n] (g : Fin n × E → E) (γ θ μ : ℝ) (m : ℕ) :
    ℕ → (E × E) → E × E
  | 0, s => s
  | k + 1, s => run g γ θ μ m k (epoch g γ θ μ m s)

end OracleTemplate.SimilarQuasar
