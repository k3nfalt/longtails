import LongTails.Setups.SphericalRandomUtility
import LongTails.Proofs.SphericalPreferenceEnvelope
import LongTails.Proofs.SphericalPreferenceExecution

open MeasureTheory Metric Set

namespace LongTails.Theorems.SphericalPreferenceDescent

open OracleTemplate LongTails.Setups.SphericalRandomUtility LongTails.Algorithms.SphericalPreferenceDescent
open LongTails.Proofs.SphericalPreferenceEnvelope LongTails.Proofs.SphericalPreferenceExecution

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(p.d : ℝ) * (672 * p.B * p.R / p.ε) ^ 2⌉₊

theorem result : Convergence LongTails.Setups.SphericalRandomUtility.spec budget := by
  refine ⟨fun p => method p (budget p 0), ?_, fun _ _ => trivial⟩
  rintro p ⟨hd,hR,hB,he,_⟩ f O ⟨hc,hm,μ,P,hs,hq,hi,rfl⟩
  let n := budget p 0
  have : NeZero p.d := ⟨by omega⟩
  obtain ⟨hn,hrate⟩ := enough_calls p hd hB hR he (n := n) (Nat.le_ceil _)
  obtain ⟨ht,F,hL,hF,hcF,o,hmin⟩ := objective_extension p f μ hs hd hR hB.le hq hc
  obtain ⟨hlm,hli,herr⟩ := expected_output p hn hd hR hB μ hs ht f F hF hL hcF o hmin hm
  have hp := prefix_law p n μ P hi
  let O : Oracle (Feasible p × Feasible p) Bool :=
    { Seed := fun _ => Point p.d, law := P, answer := fun _ (_,q) z => comparePair f q z }
  let Z := (ℕ → Draw p.d) × (ℕ → Point p.d)
  have hout (q : Z) : f (execute O (method p n) (fun _ => n) q.1 q.2).val-f o.val =
      F (returned p n f F o (fun i => (q.1 i,q.2 i))).val-F o.val := by
    rw [show execute O (method p n) (fun _ => n) q.1 q.2 = _ from execute_eq p n f F o P q.1 q.2,
      hF (returned p n f F o _).property,hF o.property]
  refine ⟨o, ?_, ?_, ?_⟩
  · intro y hy
    change f o.val ≤ f y
    rw [hF o.property,hF hy]
    exact hmin hy
  · change Integrable (fun q : Z => f (execute O (method p n) (fun _ => n) q.1 q.2).val-f o.val) _
    simp_rw [hout]
    exact (hp.integrable_comp hlm.aestronglyMeasurable).mpr hli
  · change (∫ q : Z, f (execute O (method p n) (fun _ => n) q.1 q.2).val - f o.val ∂_) ≤ _
    simp_rw [hout]
    exact (hp.hasLaw.integral_comp hlm.aestronglyMeasurable).trans_le (herr.trans hrate)

end LongTails.Theorems.SphericalPreferenceDescent
