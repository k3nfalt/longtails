import LongTails.Setups.MultirateSmoothNonconvex
import LongTails.Proofs.MultirateExecution
import LongTails.Proofs.MultirateAccuracy
import LongTails.Proofs.MultirateBudget

open MeasureTheory DistributedTemplate

namespace LongTails.Theorems.MultirateDistributedStationarity

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateProtocol LongTails.Algorithms.MultirateTrajectory
open LongTails.Algorithms.MultirateCalendar
open LongTails.Proofs.MultirateExecution

noncomputable def budget (p : Params) : Time :=
  let δ := p.ε / 1024
  let τ := p.Δ / ((p.n : ℝ) * δ^2)
  let K := 1 + ⌈τ * ∑ i, p.L i⌉₊
  let c := p.l + p.b * (clockBits + p.d * (4 + Nat.size ((p.n : ℕ) * (p.d + 1)) + K.size) : ℕ)
  (4 * K + 2 : ℕ) * c + 6 * Finset.univ.sup p.h +
    Real.toNNReal (10 * (∑ i, (p.h i : ℝ) * p.σ i^2) / ((p.n : ℝ) * δ)^2 +
      2 * τ * ((∑ i, p.L i * p.h i) + 2 * (∑ i, p.σ i * Real.sqrt (p.L i * p.h i))^2 / ((p.n : ℝ) * δ)^2))

theorem result : DistributedTemplate.TimedConvergence LongTails.Setups.MultirateSmoothNonconvex.spec budget := by
  refine ⟨fun p => algorithm p (budget p), ?_⟩
  intro p hp
  change Params at p
  obtain ⟨hh,hL,hΔ,hσ,hε⟩ := hp
  refine ⟨trivial, ?_⟩
  intro f O hO
  change Functions p at f
  obtain ⟨hf,hl,⟨a,ha,hgap⟩,g,μ,P,rfl,hw,hs⟩ := hO
  let S := Setups.DistributedAggregateSmoothNonconvex.system (aggregate p) g P
  let A := algorithm p (budget p)
  have hb : Proofs.MultirateReservations.finishTime p ≤ budget p := Proofs.MultirateBudget.finish_bound hh hL hΔ hσ hε
  have hr (ab : Fin (steps p) × Fin (steps p)) (s : Samples p) (T : Time) (ht : T ≤ budget p) :=
    terminates (g := g) (P := P) hh hL hb T ht ab s
  refine ⟨Filter.Eventually.of_forall (fun z T ht => ?_), ?_⟩
  · obtain ⟨k,hk,_⟩ := hr z.1 z.2 T ht
    exact ⟨k,hk⟩
  · have he (z : (Fin (steps p) × Fin (steps p)) × Samples p) :
        execute S A (budget p) z.1 z.2 = output p (trajectory p g z.2 (steps p)) z.1.1 z.1.2 := by
      obtain ⟨k,hk,ho⟩ := hr z.1 z.2 (budget p) le_rfl
      exact (Proofs.DistributedExecution.execute_eq_terminal S A (budget p) z k hk).trans (ho rfl)
    have hsucc := Proofs.MultirateAccuracy.accuracy hh hL hΔ hσ hε P μ hw (fun i => (hs i).1)
      g f (fun i => (hs i).2) hf hl a ha hgap (budget p)
    exact (funext he).symm ▸ hsucc

end LongTails.Theorems.MultirateDistributedStationarity
