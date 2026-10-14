import LongTails.Setups.InterpolatedFiniteSum
import LongTails.Proofs.Execution
import LongTails.Proofs.CyclicGradientRun

namespace OracleTemplate.CyclicInterpolation

open LongTails.Setups.InterpolatedFiniteSum

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => q.m * ⌈(q.m : ℝ) ^ 3 * q.L * q.R ^ 2 / q.ε⌉₊

theorem result : Convergence LongTails.Setups.InterpolatedFiniteSum.spec budget := by
  apply convergence_of_block_budget (S := spec) (fun q => ⌈(q.m : ℝ) ^ 3 * q.L * q.R ^ 2 / q.ε⌉₊) (fun p => p.m)
  refine ⟨fun p => cyclicGradient p.m p.L p.x0, ?_, fun _ _ => rfl⟩
  rintro q ⟨hL, _, hε⟩
  intro N hN
  rintro f oracle ⟨hc, hg, hlip, xstar, hmin, hdist⟩
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g : Fin q.m × q.E → q.E := fun z => oracle.answer 0 (0, z) seed0
  have hanswer : ∀ k z seed, oracle.answer k (0, z) seed = g z :=
    fun k z seed => (hg k seed z.1 z.2).unique (hg 0 seed0 z.1 z.2)
  have hyp : Hyp q.m f g q.L xstar :=
    ⟨hL, hc, fun i x => hg 0 seed0 i x, fun i x y => hlip 0 seed0 i x y, hmin⟩
  have hexec (seed : (cyclicGradient q.m q.L q.x0).Seed × ((k : ℕ) → oracle.Seed k)) :
      execute oracle (cyclicGradient q.m q.L q.x0) (fun _ => (q.m * N)) seed.1 seed.2 =
        iter q.m g q.L q.x0 (q.m * N) := by
    rw [execute_eq_of_answer_eq oracle g hanswer]
    exact execute_cyclic q.m g q.L q.x0 (q.m * N)
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  · intro seed
    change (q.m : ℝ)⁻¹ * ∑ i, (f i (execute oracle (cyclicGradient q.m q.L q.x0) (fun _ => (q.m * N))
      seed.1 seed.2) - f i xstar) ≤ q.ε
    rw [hexec]
    exact hyp.accuracy q.x0 hdist hε _ ((Nat.le_ceil _).trans (Nat.cast_le.mpr hN))

end OracleTemplate.CyclicInterpolation
