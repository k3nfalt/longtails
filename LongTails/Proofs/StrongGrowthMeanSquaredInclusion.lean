import LongTails.Setups.EuclideanStrongGrowthMeanSquared
import LongTails.Includes
import LongTails.Theorems.ProximalStormStrongGrowth

namespace LongTails.Proofs.StrongGrowthMeanSquaredInclusion

open OracleTemplate LongTails.Setups

noncomputable def inclusion :
    Inclusion StrongGrowthMeanSquaredSmoothConvex.spec EuclideanStrongGrowthMeanSquared.spec where
  numOracles_eq := rfl
  mapParams q := q.toBase
  mapPublic q := q.toBase
  instance_eq _ := rfl
  query_eq _ := rfl
  reply_eq _ := rfl
  output_eq _ := rfl
  public_eq _ := rfl
  valid _ hq := ⟨hq.1, hq.2.1, hq.2.2.1.le, hq.2.2.2.1⟩
  admissible _ _ _ _ h := h
  successful _ _ _ _ _ _ _ _ _ h := h
  allowedAlgorithm _ _ _ := trivial

lemma transfer (B : EuclideanStrongGrowthMeanSquared.Params → ℕ)
    (hB : ∀ q, EuclideanStrongGrowthMeanSquared.spec.valid q →
      ProximalStorm.budget q.toBase = fun _ => B q) :
    Convergence EuclideanStrongGrowthMeanSquared.spec (fun q _ => B q) := by
  obtain ⟨make, correct, _⟩ := ProximalStorm.result
  refine ⟨fun q => make q.toBase, ?_, fun _ _ => trivial⟩
  intro q hq f O h
  have hr := correct q.toBase (inclusion.valid q hq) f O (inclusion.admissible q hq f O h)
  rw [hB q hq] at hr
  exact hr

end LongTails.Proofs.StrongGrowthMeanSquaredInclusion
