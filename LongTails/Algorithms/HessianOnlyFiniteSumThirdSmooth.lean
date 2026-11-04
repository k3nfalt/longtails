import LongTails.Setups.FiniteSumThirdSmoothConvex
import LongTails.Algorithms.AcceleratedQuarticNewton
import Mathlib.Probability.Distributions.Uniform

namespace LongTails.Algorithms.HessianOnlyFiniteSumThirdSmooth

open LongTails.Setups.FiniteSumThirdSmoothConvex
open LongTails.Algorithms.QuarticProximalTrial
open OracleTemplate

noncomputable def scale (p : Params) : ℝ := 2 + p.n + p.G * p.R / p.ε + p.H * p.R ^ 2 / p.ε + p.L * p.R ^ 4 / p.ε

noncomputable def padding (p : Params) : ℝ := p.L + p.ε / p.R ^ 4

noncomputable def regularization (p : Params) : ℝ := padding p / p.n

noncomputable def iterations (p : Params) : ℕ := ⌈64 * (1 + ((p.L * p.R ^ 4 / p.ε + 1) / p.n) ^ (1 / 5 : ℝ))⌉₊

noncomputable def Seeds (p : Params) : Type :=
  Fin (iterations p) → Fin (64 * logarithm (scale p)) → StageSeed p.n (24 * logarithm (scale p))

noncomputable instance (p : Params) : Fintype (Seeds p) := by unfold Seeds; infer_instance
instance (p : Params) : Nonempty (Seeds p) := by unfold Seeds; infer_instance
instance (p : Params) : MeasurableSpace (Seeds p) := ⊤
instance (p : Params) : MeasurableSingletonClass (Seeds p) := ⟨fun _ => trivial⟩

noncomputable def calls (p : Params) : ℕ := trialCost p.n (scale p) * iterations p

noncomputable def plan (p : Params) (seed : Seeds p) :
    QueryPlan (Fin p.n × p.E) (p.E × (p.E →L[ℝ] p.E)) p.E (calls p) :=
  (AcceleratedQuarticNewton.run p.ε p.R (scale p) (padding p + 6 * regularization p)
    (regularization p) p.x0 (iterations p) seed .initial).map (AcceleratedQuarticNewton.output p.x0)

noncomputable def algorithm (p : Params) : Algorithm (Fin p.n × p.E) (p.E × (p.E →L[ℝ] p.E)) p.E :=
  QueryPlan.algorithm ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure, inferInstance⟩ (0, p.x0) p.x0 (calls p) (plan p)

end LongTails.Algorithms.HessianOnlyFiniteSumThirdSmooth
