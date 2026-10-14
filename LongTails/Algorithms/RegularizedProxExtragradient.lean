import LongTails.Algorithms.QueryPlan
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OracleTemplate.StochasticCohypomonotone

open QueryPlan

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure RegCfg where
  γ : ℝ
  α : ℝ
  S : ℕ
  lam : ℕ → ℝ
  Lam : ℕ → ℝ
  T : ℕ → ℕ
  b : ℕ → ℕ
  bf : ℕ

def batchSum (x : E) : (b : ℕ) → QueryPlan (E ⊕ (ℝ × E)) E E b
  | 0 => .done 0
  | b + 1 => .ask (.inl x) (fun r => (batchSum x b).map (r + ·))

def resolventQuery (γ : ℝ) (y : E) : QueryPlan (E ⊕ (ℝ × E)) E E 1 :=
  .ask (.inr (γ, y)) .done

noncomputable def egStep (γ α Λ : ℝ) (b : ℕ) (c x : E) :
    QueryPlan (E ⊕ (ℝ × E)) E E (b + 1 + b) :=
  (batchSum x b).bind fun s1 =>
    (resolventQuery γ (x - γ • ((1 / (b : ℝ)) • s1 + Λ • (x - c)))).bind fun xb =>
      (batchSum xb b).map fun s2 =>
        x - (α * γ) • (γ⁻¹ • (x - xb) - ((1 / (b : ℝ)) • s1 + Λ • (x - c)) +
          ((1 / (b : ℝ)) • s2 + Λ • (xb - c)))

def repeatPlan {c : ℕ} (step : E → QueryPlan (E ⊕ (ℝ × E)) E E c) :
    (n : ℕ) → E → QueryPlan (E ⊕ (ℝ × E)) E E (c * n)
  | 0, x => .done x
  | n + 1, x => (step x).bind fun y => repeatPlan step n y

def stageLen (cfg : RegCfg) (s : ℕ) : ℕ := (cfg.b s + 1 + cfg.b s) * cfg.T s

noncomputable def stagePlan (cfg : RegCfg) (s : ℕ) (st : E × E) :
    QueryPlan (E ⊕ (ℝ × E)) E (E × E) (stageLen cfg s) :=
  (repeatPlan (egStep cfg.γ cfg.α (cfg.Lam s) (cfg.b s) ((cfg.Lam s)⁻¹ • (st.2 + cfg.lam s • st.1)))
    (cfg.T s) st.1).map fun y => (y, st.2 + cfg.lam s • st.1)

def stagesLen (cfg : RegCfg) : ℕ → ℕ
  | 0 => 0
  | n + 1 => stageLen cfg n + stagesLen cfg n

noncomputable def stagesPlan (cfg : RegCfg) :
    (n : ℕ) → E × E → QueryPlan (E ⊕ (ℝ × E)) E (E × E) (stagesLen cfg n)
  | 0, st => .done st
  | n + 1, st => (stagesPlan cfg n st).bind (stagePlan cfg n)

noncomputable def finalPlan (cfg : RegCfg) (st : E × E) :
    QueryPlan (E ⊕ (ℝ × E)) E (E × E) (1 + cfg.bf) :=
  (batchSum st.1 cfg.bf).bind fun s =>
    (resolventQuery cfg.γ (st.1 - cfg.γ • ((1 / (cfg.bf : ℝ)) • s +
      cfg.Lam cfg.S • (st.1 - (cfg.Lam cfg.S)⁻¹ • st.2)))).map fun xb =>
        (xb, cfg.γ⁻¹ • ((st.1 - cfg.γ • ((1 / (cfg.bf : ℝ)) • s +
          cfg.Lam cfg.S • (st.1 - (cfg.Lam cfg.S)⁻¹ • st.2))) - xb))

def planLen (cfg : RegCfg) : ℕ := 1 + cfg.bf + stagesLen cfg (cfg.S + 1)

noncomputable def regularizedPlan (cfg : RegCfg) (x0 : E) :
    QueryPlan (E ⊕ (ℝ × E)) E (E × E) (planLen cfg) :=
  (stagesPlan cfg (cfg.S + 1) (x0, 0)).bind (finalPlan cfg)

noncomputable def regularizedProxExtragradient (cfg : RegCfg) (x0 : E) :
    Algorithm (E ⊕ (ℝ × E)) E (E × E) :=
  QueryPlan.algorithm (S := Unit) ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
    (.inl x0) (x0, 0) (planLen cfg) (fun _ => regularizedPlan cfg x0)

end OracleTemplate.StochasticCohypomonotone
