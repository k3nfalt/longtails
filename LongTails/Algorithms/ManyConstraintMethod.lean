import LongTails.Setups.ManyConstraintStochasticConvex
import LongTails.Algorithms.ManyConstraintVR
import LongTails.Proofs.ManyConstraintTuning

open MeasureTheory

namespace LongTails.Algorithms.ManyConstraintMethod

open LongTails.Setups.ManyConstraintStochasticConvex LongTails.Algorithms.ManyConstraintPlan
  LongTails.Algorithms.ManyConstraintVR LongTails.Proofs.ManyConstraintTuning

noncomputable def penaltyKatyusha (q : Params) [NeZero q.m] :
    OracleTemplate.Algorithm (q.E × Option (Fin q.m)) q.E q.E 2 :=
  Plan2.algorithm
    ⟨(PMF.uniformOfFintype ((Fin (LongTails.Proofs.ManyConstraintTuning.ST q.m q.κ q.σ q.ε q.L q.R) →
      Fin (2 * q.m) → Fin q.m) × (Fin (QT q.κ q.R q.δ) → Fin q.m))).toMeasure, inferInstance⟩
    (q.x0, none) q.x0 _ _
    (fullPlan (knobs q.m q.κ q.σ q.ε q.L q.R q.x0) (LongTails.Proofs.ManyConstraintTuning.ST q.m q.κ q.σ q.ε q.L q.R)
      (QT q.κ q.R q.δ))

noncomputable def trivialMethod (q : Params) :
    OracleTemplate.Algorithm (q.E × Option (Fin q.m)) q.E q.E 2 :=
  Plan2.algorithm ⟨Measure.dirac (), inferInstance⟩ (q.x0, none) q.x0 0 0
    (fun _ => Plan2.done q.x0)

noncomputable def method (q : Params) :
    OracleTemplate.Algorithm (q.E × Option (Fin q.m)) q.E q.E 2 :=
  if h : 0 < q.R ∧ 0 < q.m then
    haveI : NeZero q.m := ⟨h.2.ne'⟩
    penaltyKatyusha q
  else trivialMethod q

end LongTails.Algorithms.ManyConstraintMethod
