import LongTails.Includes
import LongTails.Setups.SmoothAndConvex
import LongTails.Setups.SmoothAndConvexUnknownL
import LongTails.Setups.GeneralizedSmoothAndConvex
import LongTails.Setups.GeneralizedSmoothParameterFree
import LongTails.Setups.SharpRelativeErrorSmoothConvex
import LongTails.Setups.RecursiveRelativeErrorSmoothConvex
import LongTails.Setups.ConstantStepReshuffledSmoothConvex
import LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex
import LongTails.Setups.DiagonalSmoothStronglyConvex
import LongTails.Setups.DiagonalSmoothStronglyConvexBlackBox
import LongTails.Setups.StochasticPowerSmoothFixedPoint

open OracleTemplate MeasureTheory

namespace LongTails.Tests.SetupIncludes

open LongTails.Setups

universe u

lemma unknownL_includes_knownL :
    Includes SmoothAndConvexUnknownL.spec.{u} SmoothAndConvex.spec.{u} := by
  let pub : SmoothAndConvex.Public → SmoothAndConvexUnknownL.Public :=
    fun p => { E := p.E, x0 := p.x0 }
  let params : SmoothAndConvex.Params → SmoothAndConvexUnknownL.Params :=
    fun p => { pub p.toPublic with L := p.L, R := p.R, ε := p.ε }
  exact ⟨{
    numOracles_eq := rfl
    mapParams := params
    mapPublic := pub
    instance_eq := fun _ => rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    public_eq := fun _ => rfl
    valid := fun _ h => h
    admissible := fun _ _ _ _ h => h
    successful := fun _ _ _ _ _ _ _ _ _ h => h
    allowedAlgorithm := fun _ _ _ => trivial }⟩

lemma parameterFree_includes_generalizedSmooth :
    Includes GeneralizedSmoothParameterFree.spec.{u} GeneralizedSmoothAndConvex.spec.{u} := by
  let pub : GeneralizedSmoothAndConvex.Public → GeneralizedSmoothParameterFree.Public :=
    fun p => { E := p.E, x0 := p.x0, h0 := 1 }
  let params : GeneralizedSmoothAndConvex.Params → GeneralizedSmoothParameterFree.Params :=
    fun p => { pub p.toPublic with L0 := p.L0, L1 := p.L1, R := p.R, Δ := p.Δ, ε := p.ε }
  exact ⟨{
    numOracles_eq := rfl
    mapParams := params
    mapPublic := pub
    instance_eq := fun _ => rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    public_eq := fun _ => rfl
    valid := fun _ h => ⟨by norm_num [params, pub], h⟩
    admissible := fun _ _ _ _ h => h
    successful := fun _ _ _ _ _ _ _ _ _ h => h
    allowedAlgorithm := fun _ _ _ => trivial }⟩

lemma relativeError_includes_sharp :
    Includes RelativeErrorSmoothConvex.spec.{u} SharpRelativeErrorSmoothConvex.spec.{u} := by
  exact ⟨{
    numOracles_eq := rfl
    mapParams := id
    mapPublic := id
    instance_eq := fun _ => rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    public_eq := fun _ => rfl
    valid := fun _ h => h.1
    admissible := fun _ _ _ _ h => h
    successful := fun _ _ _ _ _ _ _ _ _ h => h
    allowedAlgorithm := fun _ _ _ => trivial }⟩

lemma relativeError_includes_recursive :
    Includes RelativeErrorSmoothConvex.spec.{u} RecursiveRelativeErrorSmoothConvex.spec.{u} := by
  exact ⟨{
    numOracles_eq := rfl
    mapParams := id
    mapPublic := id
    instance_eq := fun _ => rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    public_eq := fun _ => rfl
    valid := fun _ h => h.1
    admissible := fun _ _ _ _ h => h
    successful := fun _ _ _ _ _ _ _ _ _ h => h
    allowedAlgorithm := fun _ _ _ => trivial }⟩

lemma constantStep_includes_reshuffled :
    Includes ConstantStepReshuffledSmoothConvex.spec.{u} ReshuffledSmoothConvex.spec.{u} := by
  refine ⟨{
    numOracles_eq := rfl
    mapParams := id
    mapPublic := id
    instance_eq := fun _ => rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    public_eq := fun _ => rfl
    valid := fun _ h => h
    admissible := fun _ _ _ _ h => h
    successful := fun _ _ _ _ _ _ _ _ _ h => h
    allowedAlgorithm := ?_ }⟩
  intro p A h
  obtain ⟨K, η, _, hA⟩ := h
  exact ⟨K, fun _ => η, hA⟩

lemma finiteVariance_includes_lightTail :
    Includes FiniteVarianceGeneralizedSmoothAndConvex.spec.{u}
      StochasticGeneralizedSmoothAndConvex.spec.{u} := by
  refine ⟨{
    numOracles_eq := rfl
    mapParams := id
    mapPublic := id
    instance_eq := fun _ => rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    public_eq := fun _ => rfl
    valid := fun _ h => h
    admissible := ?_
    successful := fun _ _ _ _ _ _ _ _ _ h => h
    allowedAlgorithm := fun _ _ _ => trivial }⟩
  intro q _ f O h
  obtain ⟨g, p, P, hiid, hO, hc, hg, hd, hl, hmin, hnoise⟩ := h
  exact ⟨g, p, P, hiid, hO, hc, hg, hd, hl, hmin, hnoise.toIsStochasticGradient⟩

lemma diagonalBlackBox_includes_knownValue :
    Includes DiagonalSmoothStronglyConvexBlackBox.spec DiagonalSmoothStronglyConvex.spec := by
  let pub : DiagonalSmoothStronglyConvex.Public → DiagonalSmoothStronglyConvexBlackBox.Public :=
    fun p => { d := p.d, x0 := p.x0 }
  let params : DiagonalSmoothStronglyConvex.Params → DiagonalSmoothStronglyConvexBlackBox.Params :=
    fun p => { pub p.toPublic with w := p.w, μ := p.μ, Δ := p.Δ, ε := p.ε }
  refine ⟨{
    numOracles_eq := rfl
    mapParams := params
    mapPublic := pub
    instance_eq := fun _ => rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    public_eq := fun _ => rfl
    valid := fun _ h => h
    admissible := ?_
    successful := ?_
    allowedAlgorithm := fun _ _ _ => trivial }⟩
  · intro q _ f O h
    obtain ⟨hg, hO, hu, hl, ⟨xstar, hmin, hvalue⟩, hgap⟩ := h
    refine ⟨hg, hO, hu, hl, xstar, hmin, ?_⟩
    change f q.x0 - f xstar ≤ q.Δ
    simpa only [hvalue] using hgap
  · intro q _ f O had Ω _ output P hs
    obtain ⟨xstar, hmin, hacc⟩ := hs
    obtain ⟨z, hz, hvalue⟩ := had.2.2.2.2.1
    have heq : f xstar = f z := le_antisymm (hmin (Set.mem_univ z)) (hz (Set.mem_univ xstar))
    exact ⟨xstar, hmin, heq.trans hvalue, hacc⟩

lemma powerSmooth_includes_twoSmooth :
    Includes StochasticPowerSmoothFixedPoint.spec.{u} StochasticFixedPointSmoothBanach.spec.{u} := by
  let params : StochasticFixedPointSmoothBanach.Params → StochasticPowerSmoothFixedPoint.Params :=
    fun p => { p with K := p.K + 1, exponent := 2 }
  refine ⟨{
    numOracles_eq := rfl
    mapParams := params
    mapPublic := params
    instance_eq := fun _ => rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    public_eq := fun _ => rfl
    valid := ?_
    admissible := ?_
    successful := fun _ _ _ _ _ _ _ _ _ h => h
    allowedAlgorithm := fun _ _ _ => trivial }⟩
  · intro p hp
    exact ⟨by norm_num [params], by norm_num [params], by dsimp [params]; linarith [hp.1], hp.2⟩
  · intro q _ M O h
    obtain ⟨P, hiid, hO, ⟨j, hj⟩, hne, hstar, hmeas, hmean, hnoise⟩ := h
    refine ⟨P, hiid, hO, ⟨j, ?_⟩, hne, hstar, hmeas, hmean, ?_⟩
    · intro x y
      change ‖x + y‖ ^ (2 : ℝ) ≤ ‖x‖ ^ (2 : ℝ) + 2 * j x y + (q.K + 1) * ‖y‖ ^ (2 : ℝ)
      simp only [Real.rpow_two]
      have hh := hj x y
      nlinarith [sq_nonneg ‖y‖]
    · simpa [params, Real.rpow_two] using hnoise

end LongTails.Tests.SetupIncludes
