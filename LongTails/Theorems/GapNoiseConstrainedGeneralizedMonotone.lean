import LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone
import LongTails.Proofs.GapNoisePublic
import LongTails.Proofs.GapNoiseBudget
import LongTails.Proofs.Execution

namespace OracleTemplate.GapNoiseConstrainedGeneralizedMonotone

open LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone
open LongTails.Algorithms.GapNoisePastExtragradient
open LongTails.Proofs.GapNoiseBudget LongTails.Proofs.GapNoisePublic

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 350 * ((q.L0 + q.L1 * q.G + q.v) * q.R * (1 + q.L1 * q.R) ^ 2 / q.ε + (1 + q.L1 * q.R) ^ 4 + q.σ ^ 2 * (1 + q.L1 * q.R) / q.ε ^ 2) * (1 + Real.log ((2 + (q.L0 + q.L1 * q.G) * q.R * (1 + q.L1 * q.R) ^ 2 / q.ε + (1 + q.L1 * q.R) ^ 4) / q.δ)) ^ 5⌉₊

theorem result : Convergence LongTails.Setups.GapNoiseConstrainedGeneralizedMonotone.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun q => budget q 0)
  refine ⟨fun q => algorithm { L0 := q.L0, L1 := q.L1, R := 2 * q.R, G := q.G, σ := q.σ, ε := q.ε, δ := q.δ, v := q.v } q.x0, ?_, fun _ _ => trivial⟩
  rintro q ⟨h0, h1, hR, hG, hσ, hv, hε, hδ, hδ1⟩
  rintro I O ⟨g, p, P, proj, hIID, rfl, hproj, hX, hx0, hc, hm, hlip,
    ⟨xstar, hstar, hvi, hd, hGs, hg⟩⟩
  let t : Tuning := { L0 := q.L0, L1 := q.L1, R := 2 * q.R, G := q.G, σ := q.σ, ε := q.ε, δ := q.δ, v := q.v }
  have htR : 0 < t.R := by dsimp [t]; positivity
  have hP : ConstrainedMonotone.Proj I.X proj :=
    ⟨fun z => (hproj z).1, fun z => (hproj z).2⟩
  have hF : GeneralizedMonotone.Hyp I.F t.L0 t.L1 := ⟨h0, h1, hc, hm, hlip⟩
  have hb : t.L1 ≤ effectiveCurvature t := by
    have hn : 0 ≤ t.L0 / (t.G + t.L0 * t.R) := by
      change 0 ≤ q.L0 / (q.G + q.L0 * (2 * q.R))
      positivity
    unfold effectiveCurvature
    linarith
  have hFb := LongTails.Proofs.GapNoiseTuning.enlarge_generalized_parameter hF hb
  have hn : ConstrainedMonotone.Normal I.X xstar (-I.F xstar) := by
    intro w hw
    simpa only [inner_neg_left, neg_nonpos] using hvi w hw
  have hd' : ‖q.x0 - xstar‖ ≤ t.R / 2 := by dsimp [t]; linarith
  have hK : runCalls t 0 (stages t) ≤ budget q 0 := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact (runCalls_radius_upper t q.R rfl h0 h1 hR hG hε hv hδ hδ1).trans (Nat.le_ceil _)
  exact execution_success hP hX t hFb h1 htR hε hv hδ hx0 hstar hn hGs hd' p P hIID hg
    (budget q 0) hK

end OracleTemplate.GapNoiseConstrainedGeneralizedMonotone
