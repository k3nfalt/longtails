import LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
import LongTails.Proofs.LeonAccuracy
import LongTails.Proofs.LeonTiming
import LongTails.Proofs.LeonConfiguredSchedule

namespace LongTails.Theorems.FiniteBitLeon

open MeasureTheory DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonProtocol (algorithm)

noncomputable def budget (p : Params) : Time := 8 * (1 + ⌈2^19 * p.L * p.Δ / p.ε^2⌉₊ : ℕ) * (Finset.univ.sup p.h + (∑ i, p.h i) * (2^18 * p.σ^2 / ((p.n : ℝ)^2 * p.ε^2)).toNNReal + 2 * (p.l + p.b * (64 + ((p.d + p.n - 1) / p.n) * (8 + Nat.log2 ((p.n : ℕ) * (p.d + 1))) : ℕ)))

theorem result : DistributedTemplate.TimedConvergence LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.spec budget := by
  refine ⟨fun p => algorithm p (budget p), ?_⟩
  intro p hp
  obtain ⟨hh,hL,_,_,hε⟩ := hp
  refine ⟨trivial, ?_⟩
  intro f O had
  obtain ⟨hf,hlip,⟨a,ha,hgap⟩,g,μ,P,rfl,hw,hlocal⟩ := had
  refine ⟨Filter.Eventually.of_forall (fun z => Proofs.LeonTermination.finite g P _ z.1 z.2), ?_⟩
  have h := Proofs.LeonAccuracy.accuracy p hh hε hL P μ f g hw (fun i => (hlocal i).1)
    (fun i => (hlocal i).2) hf hlip a ha hgap (budget p)
  have he := Proofs.LeonConfiguredSchedule.execute_output p hh g P
  let ls := LongTails.Algorithms.LeonCalendar.levels (LongTails.Algorithms.LeonTuning.height p)
  have hfun : (fun z : (algorithm p (budget p)).Seed × (system p g P).Seed =>
      execute (system p g P) (algorithm p (budget p)) (budget p) z.1 z.2) =
      fun z => LongTails.Algorithms.LeonTrajectory.output p
        (LongTails.Algorithms.LeonTrajectory.trajectory p g z.2 ls ls.length) z.1.1 z.1.2 :=
    funext (fun z => he z.2 (budget p) z.1 (Proofs.LeonClosedBudget.sufficient p))
  exact (congrArg (fun X => spec.successful p f X (law (system p g P) (algorithm p (budget p)))) hfun).mpr h

end LongTails.Theorems.FiniteBitLeon
