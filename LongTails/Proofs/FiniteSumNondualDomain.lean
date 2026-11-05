import LongTails.Setups.FiniteSumNondualSmoothConvex
import LongTails.Proofs.KnownValueNondualGeometry
import LongTails.Proofs.ComponentEnvelopeCoupling

open Set
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.FiniteSumNondualDomain

open LongTails.Setups.FiniteSumNondualSmoothConvex
open RecursiveEnvelopeGeometry

private noncomputable def geometryParams (p : Params) :
    LongTails.Setups.KnownValueNondualGeneralizedConvex.Public :=
  ⟨p.d, p.L, 0, p.R, p.ε, 0, 0⟩

lemma domain_nonempty (p : Params) : (domain p).Nonempty := by
  refine ⟨0, ?_⟩
  simpa [domain] using p.hR

lemma domain_compact (p : Params) : IsCompact (domain p) :=
  KnownValueNondualGeometry.initialBody_compact (geometryParams p)

lemma domain_convex (p : Params) : Convex ℝ (domain p) :=
  KnownValueNondualGeometry.initialBody_convex (geometryParams p)

lemma domain_norm (p : Params) {x : Point p} (hx : x ∈ domain p) : ‖x‖ ≤ p.R :=
  KnownValueNondualGeometry.initialBody_norm (geometryParams p) hx

lemma domain_distance (p : Params) {x y : Point p} (hx : x ∈ domain p) (hy : y ∈ domain p) :
    ‖x - y‖ ≤ 2 * p.R := by
  have h := norm_sub_le x y
  linarith [domain_norm p hx, domain_norm p hy]

lemma component_model (p : Params) (hL : 0 < p.L) (f : Fin p.n → Point p → ℝ)
    (O : OracleTemplate.Oracle (Fin p.n × Feasible p) (Point p)) (ha : spec.admissible p f O)
    (i : Fin p.n) : Model p.L (f i) (gradient (f i)) := by
  refine ⟨hL, ?_, OracleTemplate.Gradient.smooth_upper_bound (ha.2.1 i) (ha.2.2.1 i)⟩
  intro x y
  have h := OracleTemplate.Gradient.convex_support (ha.1 i) (ha.2.1 i) x y
  linarith

lemma objective_model (p : Params) (hL : 0 < p.L) (f : Fin p.n → Point p → ℝ)
    (O : OracleTemplate.Oracle (Fin p.n × Feasible p) (Point p)) (ha : spec.admissible p f O) :
    Model p.L (objective f) (OracleTemplate.FiniteSum.fullGradient
      (fun q : Fin p.n × Point p => gradient (f q.1) q.2)) :=
  OracleTemplate.ComponentEnvelope.finiteSum_model (component_model p hL f O ha)

lemma objective_continuous (p : Params) (f : Fin p.n → Point p → ℝ)
    (O : OracleTemplate.Oracle (Fin p.n × Feasible p) (Point p)) (ha : spec.admissible p f O) :
    Continuous (objective f) := by
  unfold objective LongTails.Setups.FiniteSumSmoothAndConvex.objective
  apply continuous_const.mul
  exact continuous_finsetSum _ (fun i _ => continuous_iff_continuousAt.mpr
    (fun x => (ha.2.1 i x).continuousAt))

lemma exists_minimizer (p : Params) (f : Fin p.n → Point p → ℝ)
    (O : OracleTemplate.Oracle (Fin p.n × Feasible p) (Point p)) (ha : spec.admissible p f O) :
    ∃ xstar : Feasible p, IsMinOn (objective f) (domain p) xstar.val := by
  obtain ⟨x, hx, hm⟩ := (domain_compact p).exists_isMinOn (domain_nonempty p)
    (objective_continuous p f O ha).continuousOn
  exact ⟨⟨x, hx⟩, hm⟩

end LongTails.Proofs.FiniteSumNondualDomain
