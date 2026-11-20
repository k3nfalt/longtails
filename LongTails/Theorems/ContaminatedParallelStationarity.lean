import LongTails.Setups.DistributedContaminatedSmoothNonconvex
import LongTails.Proofs.ContaminatedParallelAccuracy

namespace LongTails.Theorems.ContaminatedParallelStationarity

open DistributedTemplate MeasureTheory
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent (algorithm)
open LongTails.Proofs.ContaminatedParallelFailures (Data)

noncomputable def budget (p : Params) : Time :=
  let K := 1 + ⌈2^19 * p.L * p.Δ / p.ε^2⌉₊
  let q := 4 + ⌈Real.log (1 / p.failure)⌉₊
  2^34 * (K + q * min K q : ℕ) * (Finset.univ.sup p.h + (2^18 * (∑ i, (p.h i : ℝ) * p.σ i^2) / ((p.n : ℝ)^2 * p.ε^2)).toNNReal) + 512 * (K : Time) * (((1 + Nat.log2 p.n : ℕ) : Time) * Finset.univ.sup p.h + p.l + p.b * (64 + ((p.d + p.n - 1) / p.n) * (8 + Nat.log2 ((p.n : ℕ) * (p.d + 1))) : ℕ))

theorem result : DistributedTemplate.TimedConvergence LongTails.Setups.DistributedContaminatedSmoothNonconvex.spec budget := by
  refine ⟨fun p => algorithm p (budget p),?_⟩
  intro p hp
  refine ⟨trivial,?_⟩
  intro f O had
  obtain ⟨hf,hs,hgap,g,μ,ν,P,rfl,hw,hl⟩ := had
  let D : Data p := ⟨f,g,μ,ν,P,hp,hf,hs,hgap,hw,fun i => (hl i).1,fun i => (hl i).2⟩
  let O := Setups.BandwidthHeterogeneousSmoothNonconvex.system (network p) g P
  let A := algorithm p (budget p)
  refine ⟨Filter.Eventually.of_forall (fun z => Proofs.ContaminatedParallelExecution.finite p g P _ z.1 z.2),?_⟩
  have he (z : A.Seed × O.Seed) : execute O A (budget p) z.1 z.2 = Proofs.ContaminatedParallelAccuracy.out D z := by
    rw [Proofs.ContaminatedParallelSchedule.execute_output p g P (budget p) z.1 z.2
      (Proofs.ContaminatedParallelBudget.sufficient p hp.1 z.1)]
    let ls := Algorithms.ContaminatedParallelDescent.operations p z.1
    have h := (Proofs.ContaminatedParallelHistory.agrees p g z.2 ls ls.length le_rfl).1
    rw [List.take_length] at h
    exact congrArg (Algorithms.ContaminatedParallelDescent.output p) h.symm
  change Measurable (fun z : A.Seed × O.Seed => execute O A (budget p) z.1 z.2) ∧
    (law O A : Measure (A.Seed × O.Seed)) {z | p.ε < ‖D.G (execute O A (budget p) z.1 z.2)‖} ≤ ENNReal.ofReal p.failure
  simp only [he]
  exact ⟨Proofs.ContaminatedParallelAccuracy.measurable_out D,Proofs.ContaminatedParallelAccuracy.prob D⟩

end LongTails.Theorems.ContaminatedParallelStationarity
