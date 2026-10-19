import LongTails.Setups.QuantileSymmetricRemainderConvex
import LongTails.Proofs.CharacteristicConvergence
import LongTails.Proofs.CharacteristicTuning
import LongTails.Proofs.QuantileMinimax

open MeasureTheory

namespace LongTails.Theorems.QuantileRemainderMinimaxConvex

open OracleTemplate
open LongTails.Setups.QuantileSymmetricRemainderConvex
open LongTails.Algorithms.CharacteristicGradient
open LongTails.Proofs.CharacteristicConvergence
open LongTails.Proofs.CharacteristicTuning

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => (1 + ⌈4 * Real.sqrt (q.L * q.R ^ 2 / q.ε) + 32768 * (Real.sqrt q.d * q.R * (2 * q.L * q.R + q.r) / q.ε + 8 * q.d * q.M * q.R ^ 2 / q.ε ^ 2) ^ 2⌉₊) * (1 + ⌈Real.log (1 + 512 * (Real.sqrt q.d * q.R * (2 * q.L * q.R + q.r) / q.ε + 8 * q.d * q.M * q.R ^ 2 / q.ε ^ 2)) / Real.log 2⌉₊)

theorem result : Convergence LongTails.Setups.QuantileSymmetricRemainderConvex.spec budget := by
  refine ⟨tunedAlgorithm, ?_, fun _ _ => trivial⟩
  intro q hv f O hO
  obtain ⟨g, p, P, hs, rfl, hc, hg, hlip, ⟨u, hm, hu⟩, hG, hnoise⟩ := hO
  have hK : 0 < batchCount q := by unfold batchCount; omega
  have hH := scale_pos q hv
  have hD := curvature_bounds q hv
  have hN := (iteration_bounds q).1
  have hu' : ‖u - q.x0‖ ≤ q.R := by simpa only [norm_sub_rev] using hu
  have hb := output_expected (K := batchCount q) (N := iterationCount q) hv.2.1 hD.1 hD.2 hv.2.2.1.le
    (one_div_pos.mpr hH) hv.2.2.2.1.le hv.2.2.2.2.1 (frequency_quantile q hv)
    hc hg hlip hG q.x0 u hm hu' hnoise hN
  have ha := stream_expected (K := batchCount q) (N := iterationCount q) p P hs g hG (curvature q) q.R (1 / scale q) q.x0 u f q.ε
    ⟨hb.1, hb.2.trans (tuned_rate q hv)⟩
  let F := fun s : Unit × (ℕ → q.Ω) => execute
      { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (algorithm hK (curvature q) q.R (1 / scale q) q.x0)
      (fun _ => iterationCount q * batchCount q) s.1 s.2
  change Measurable F ∧ ∃ v, IsMinOn f Set.univ v ∧
    Integrable (fun s => f (F s) - f v) ((Measure.dirac () : Measure Unit).prod (P : Measure _)) ∧
    (∫ s, f (F s) - f v ∂((Measure.dirac () : Measure Unit).prod (P : Measure _))) ≤ q.ε
  have he (s : Unit × (ℕ → q.Ω)) : execute
      { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (algorithm hK (curvature q) q.R (1 / scale q) q.x0)
      (fun _ => iterationCount q * batchCount q) s.1 s.2 =
      output (K := batchCount q) g (curvature q) q.R (1 / scale q) q.x0 (iterationCount q)
        (fun n j => s.2 (n.val * batchCount q + j.val)) := by
    rcases s with ⟨⟨⟩, ξ⟩
    exact execute_output hK P g (curvature q) q.R (1 / scale q) q.x0 (iterationCount q) ξ
  dsimp only [F]
  simp only [he]
  exact ⟨ha.1, u, hm, ha.2.1, ha.2.2⟩

end LongTails.Theorems.QuantileRemainderMinimaxConvex
