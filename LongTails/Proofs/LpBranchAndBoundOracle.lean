import LongTails.Setups.BoundedMixedIntegerLinear
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace

namespace OracleTemplate.BoundedMixedIntegerLinear

open LongTails.Setups.BoundedMixedIntegerLinear Matrix

lemma continuous_objective (P : Params) : Continuous (objective P) := by
  unfold objective
  simp only [dotProduct]
  fun_prop

lemma isClosed_relaxationFeasible (P : Params) (β : Box P) :
    IsClosed {x : Point P | RelaxationFeasible P β x} := by
  have hrow : ∀ i, Continuous fun x : Point P => (P.A *ᵥ x.1 + P.G *ᵥ x.2) i := by
    intro i
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
    fun_prop
  have hbox : ∀ γ : Box P, IsClosed {x : Point P | InBox P γ x.1} := by
    intro γ
    simp only [InBox, Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun j =>
      (isClosed_le continuous_const ((continuous_apply j).comp continuous_fst)).inter
        (isClosed_le ((continuous_apply j).comp continuous_fst) continuous_const)
  have hrows : IsClosed {x : Point P | RowFeasible P x} := by
    simp only [RowFeasible, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (hrow i) continuous_const
  exact hrows.inter ((hbox _).inter (hbox β))

lemma exists_relaxationOracle (P : Params)
    (hb : Bornology.IsBounded {x : Point P | RelaxationFeasible P (P.lo, P.hi) x}) :
    ∃ O : Oracle (Box P) (Option (Point P)), IsRelaxationOracle P O := by
  classical
  have hmin : ∀ β : Box P, (∃ x, RelaxationFeasible P β x) →
      ∃ x, RelaxationFeasible P β x ∧
        ∀ x', RelaxationFeasible P β x' → objective P x ≤ objective P x' := by
    intro β ⟨x0, hx0⟩
    have hc : IsCompact {x : Point P | RelaxationFeasible P β x} :=
      Metric.isCompact_of_isClosed_isBounded (isClosed_relaxationFeasible P β)
        (hb.subset fun x hx => ⟨hx.1, hx.2.1, hx.2.1⟩)
    obtain ⟨x, hx, hxmin⟩ :=
      hc.exists_isMinOn ⟨x0, hx0⟩ (continuous_objective P).continuousOn
    exact ⟨x, hx, fun x' hx' => hxmin hx'⟩
  refine ⟨{ answer := fun _ query _ =>
    if h : ∃ x, RelaxationFeasible P query.2 x ∧
      ∀ x', RelaxationFeasible P query.2 x' → objective P x ≤ objective P x'
    then some h.choose else none }, fun _ query _ => ?_⟩
  by_cases h : ∃ x, RelaxationFeasible P query.2 x ∧
      ∀ x', RelaxationFeasible P query.2 x' → objective P x ≤ objective P x'
  · simp only [dite_eq_left h]
    exact h.choose_spec
  · simp only [dite_eq_right h]
    intro x hx
    exact h (hmin _ ⟨x, hx⟩)

end OracleTemplate.BoundedMixedIntegerLinear
