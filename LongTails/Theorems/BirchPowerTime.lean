import LongTails.Setups.BirchPowerTime
import LongTails.Proofs.BirchResourcePublic

namespace LongTails.Theorems.BirchPowerTime

open Finset OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchPowerTime
open LongTails.Algorithms.BirchCollections (algorithm)
open LongTails.Algorithms.BirchResourceNative
open LongTails.Proofs.BirchResourcePublic

noncomputable def budget : (let S := LongTails.Setups.BirchPowerTime.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ =>
  (1 + ⌈240 * p.geometry.L * p.geometry.Δ / (1 / 8 * p.geometry.ε)⌉₊) * sInf (chargeOptions p)

lemma budget_le (p : Params) (hp : Valid p) :
    budget p 0 ≤ rounds p * (block p + p.packetLimit) := by
  let l := powerPlan p hp
  change rounds p * sInf (chargeOptions p) ≤ _
  rw [← l.charge]
  exact Nat.mul_le_mul_left _ l.cap

noncomputable def controller (p : Params) :
    Algorithm (Point p.geometry.d) (Point p.geometry.d) (Point p.geometry.d × ℝ) := by
  classical
  exact if hp : Valid p then
    let l := powerPlan p hp
    clocked (algorithm (compiledParams p.geometry l.layout l.positive)) (rounds p * window p)
  else clocked (algorithm (tuned p.geometry)) 0

theorem result : Convergence spec budget := by
  classical
  refine ⟨controller, ?_, ?_⟩
  · intro p hp I O hI
    let l := powerPlan p hp
    have hc : controller p = clocked (algorithm (compiledParams p.geometry l.layout l.positive))
        (rounds p * window p) := by
      unfold controller
      exact dite_eq_left hp
    have hb : budget p = fun _ => rounds p * (∑ i, l.layout.paid i) := by
      funext _
      change rounds p * sInf (chargeOptions p) = _
      rw [l.charge]
    have h := clocked_success p.geometry l.layout l.positive l.valid hp.1
      (rounds p * window p) I O hI
    rw [hb]
    have hgen (A : Algorithm (Point p.geometry.d) (Point p.geometry.d) (Point p.geometry.d × ℝ))
        (he : A = clocked (algorithm (compiledParams p.geometry l.layout l.positive))
          (rounds p * window p)) :
        spec.successful p I (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
          execute O A (fun _ => rounds p * (∑ i, l.layout.paid i)) z.1 z.2)
          ⟨((A.law : Measure _).prod (O.law : Measure _)), inferInstance⟩ := by
      subst A
      exact h
    exact hgen (controller p) hc
  · intro p hp
    let l := powerPlan p hp
    refine ⟨l.packets, LongTails.Proofs.BirchPowerTime.scheduled p.hardware, l.order,
      l.layout, l.positive, l.legal, l.window, fun i =>
        ⟨(l.valid.count i).1, (l.valid.count i).2, l.work i⟩,
      l.valid.quota, l.cap, l.parent, ?_⟩
    unfold controller
    exact dite_eq_left hp

end LongTails.Theorems.BirchPowerTime
