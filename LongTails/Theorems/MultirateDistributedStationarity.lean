import LongTails.Setups.DistributedComponentSmoothNonconvex
import LongTails.Proofs.MultirateAccuracy
import LongTails.Proofs.MultirateBudget
import LongTails.Proofs.MultirateCertificate

namespace LongTails.Theorems.MultirateDistributedStationarity

open DistributedTemplate MeasureTheory
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex (objective system)
open LongTails.Algorithms.MultirateSchedule (algorithm output)

noncomputable def budget (p : Params) : Time :=
  let δ := p.ε / 512
  let q := p.Δ / δ ^ 2
  let R := 1 + ⌈2 * q * (∑ i, p.L i) / p.n⌉₊
  let C := p.l + p.b * (64 + p.d * (11 + Nat.log2 ((p.n : ℕ) * (p.d + 1)) + Nat.log2 R) : ℕ)
  let I := ((Finset.univ.sup p.h : Time) : ℝ) + (∑ i, p.σ i ^ 2 * (p.h i : ℝ)) / (p.n * δ) ^ 2
  (32 * (I +
    (R : ℝ) * (C : ℝ) + q * ((∑ i, p.L i * (p.h i : ℝ)) / p.n +
      (∑ i, p.σ i * √(p.L i * (p.h i : ℝ))) ^ 2 / ((p.n : ℝ) ^ 3 * δ ^ 2))) : ℝ).toNNReal

theorem result : DistributedTemplate.TimedConvergence LongTails.Setups.DistributedComponentSmoothNonconvex.spec budget := by
  refine ⟨fun p => algorithm p (budget p), ?_⟩
  intro p hp
  change Params at p
  obtain ⟨hh,hL,hΔ,hσ,hε⟩ := hp
  refine ⟨trivial,?_⟩
  intro f O had
  obtain ⟨hf,hl,⟨lower,hlo,hgap⟩,g,μ,P,rfl,hw,hlocal⟩ := had
  refine ⟨Filter.Eventually.of_forall (Proofs.MultirateTermination.finite g P (budget p)),?_⟩
  set T := budget p
  let A := algorithm p T
  let O := system (network p) g P
  change spec.successful p f (fun z : A.Seed × O.Seed => execute O A T z.1 z.2) (law O A)
  by_cases hz : smoothness p = 0
  · have hzero := Proofs.MultirateAccuracy.zero_curvature (Proofs.MultirateAccuracy.objective_diff hf)
      (Proofs.MultirateStaleness.gradient_lipschitz hf hl) hz hΔ lower hlo hgap
    have he (z : A.Seed × O.Seed) : execute O A T z.1 z.2 = p.x0 :=
      Proofs.MultirateCertificate.execute_zero g z.2 P T z.1 hz
    apply (congrArg (fun X => spec.successful p f X (law O A)) (funext he)).mpr
    refine ⟨measurable_const,integrable_const _,?_⟩
    change (∫ _ : A.Seed × O.Seed, ‖gradient (objective (network p) f) p.x0‖^2 ∂(law O A : Measure _)) ≤ p.ε^2
    change gradient (objective (network p) f) p.x0 = 0 at hzero
    simp [hzero,sq_nonneg]
  · have hpos : 0 < smoothness p := lt_of_le_of_ne
      (div_nonneg (Finset.sum_nonneg (fun i _ => hL i)) (by positivity)) (Ne.symm hz)
    have hT : Proofs.MultirateCalendar.stamp p (Algorithms.MultirateSchedule.K p) ≤ T :=
      Proofs.MultirateBudget.sufficient hh hL hΔ hσ hε hpos
    have hfun : (fun z : A.Seed × O.Seed => execute O A T z.1 z.2) = fun z =>
        output p (Proofs.MultirateTrajectory.modelAt g z.2 (Algorithms.MultirateSchedule.K p)) z.1 :=
      funext fun z => Proofs.MultirateCertificate.execute_positive g z.2 P T hT z.1 hpos
        (Proofs.MultirateService.tick_pos hh hL hpos)
    apply (congrArg (fun X => spec.successful p f X (law O A)) hfun).mpr
    exact Proofs.MultirateAccuracy.successful P μ hw (fun i => (hlocal i).1) (fun i => (hlocal i).2)
      hh hσ hε hpos hL hf hl lower hlo hgap T

end LongTails.Theorems.MultirateDistributedStationarity
