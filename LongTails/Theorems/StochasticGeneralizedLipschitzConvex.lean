import LongTails.Setups.StochasticGeneralizedLipschitzConvex
import LongTails.Proofs.GeneralizedLipschitzComposition
import LongTails.Proofs.GeneralizedLipschitzComplexity
open MeasureTheory OracleTemplate
namespace LongTails.Theorems.StochasticGeneralizedLipschitzConvex
open LongTails.Setups.StochasticGeneralizedLipschitzConvex
open LongTails.Algorithms.GeneralizedLipschitzPilot
open LongTails.Algorithms.GeneralizedLipschitzConvex
open LongTails.Proofs.GeneralizedLipschitzComplexity
open LongTails.Proofs.GeneralizedLipschitzPilot
open LongTails.Proofs.GeneralizedLipschitzBurnin
open LongTails.Proofs.GeneralizedLipschitzComposition
noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 66 * ((1 + q.R * q.G1) ^ 3 + (1 + q.R * q.G1) ^ 2 * (q.R * q.G0 / q.ε) + (q.R * q.G0 / q.ε) ^ 2) * (1 + Real.log (2 + q.R * q.G1 + q.R * q.G0 / q.ε)) ^ 3⌉₊
theorem result : Convergence LongTails.Setups.StochasticGeneralizedLipschitzConvex.spec budget := by
  refine ⟨fun q => tunedAlgorithm q.x0 q.R q.G0 q.G1 q.ε, ?_, fun _ _ => trivial⟩
  rintro q ⟨hR, hG0, hG1, hε⟩ f O ⟨g, p, P, hIID, rfl, _hconv, hf, xs, hmin, hdist, ho⟩
  let G := max q.G1 (1 / q.R)
  let T := ⌈204800 * (q.R * G) ^ 2⌉₊
  let δ : ℝ := 1 / (100 * T)
  let c := tuning (q.R * G) δ
  let D := 2 * q.R
  let e := q.ε / 20
  let τ := ⌈(96 * D * G) ^ 2⌉₊
  let α := min (1 / (16 * τ * (D * G))) (min ((e / (24 * D * q.G0)) ^ 2) (e / (1536 * τ * D * q.G0)))
  let K := ⌈(2 / α) * Real.log (max 2 (1024 * D * q.G0 / e))⌉₊
  let N := budget q 0
  have hκ : 1 ≤ q.R * G := by rw [normalized_parameters hR]; exact le_max_left _ _
  have hG : 0 < G := lt_of_lt_of_le (one_div_pos.mpr hR) (le_max_right _ _)
  have htime := burnin_horizon_bound hκ
  have hδ : 0 < δ := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using htime.2.1
  have hcost : T * c.calls + K ≤ N := execution_cost hR hG0 hG1 hε
  have hstar : ‖xs - q.x0‖ ≤ q.R := by simpa only [norm_sub_rev] using hdist
  have hglobal : ∀ x, f xs ≤ f x := fun x => hmin (Set.mem_univ x)
  have hc := combined_confidence (p : Measure q.Ω) P hIID hf.measurable ho hR hG0 hG1 hG
    (le_max_left _ _) hκ hglobal q.x0 hstar hε hδ T htime.1 N hcost
  let O : Oracle q.E q.E := { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
  let out := output c (tuning_calls_pos (q.R * G) δ) q.x0 q.R G q.G0 (q.R * G) α T K N O
  have hm : Measurable out := hc.1
  have hp : (P : Measure _) {ξ | q.ε < f (out ξ) - f xs} ≤ ENNReal.ofReal (1 / 10 : ℝ) := by
    apply hc.2.trans
    have ht : 2048 * (q.R * G) ^ 2 / T + T * δ ≤ (1 / 50 : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using htime.2.2
    calc
      _ ≤ ENNReal.ofReal (1 / 50 : ℝ) + ENNReal.ofReal (1 / 20 : ℝ) := add_le_add (ENNReal.ofReal_le_ofReal ht) le_rfl
      _ ≤ ENNReal.ofReal (1 / 10 : ℝ) := by
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 50) (by norm_num : (0 : ℝ) ≤ 1 / 20)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
  change Measurable (fun seed : Unit × (ℕ → q.Ω) => execute O (tunedAlgorithm q.x0 q.R q.G0 q.G1 q.ε) (fun _ => N) seed.1 seed.2) ∧
    ∃ xstar, IsMinOn f Set.univ xstar ∧
      ((Measure.dirac ()).prod (P : Measure _)) {seed : Unit × (ℕ → q.Ω) | q.ε < f (execute O (tunedAlgorithm q.x0 q.R q.G0 q.G1 q.ε) (fun _ => N) seed.1 seed.2) - f xstar} ≤ ENNReal.ofReal (1 / 10 : ℝ)
  have he (seed : Unit × (ℕ → q.Ω)) : execute O (tunedAlgorithm q.x0 q.R q.G0 q.G1 q.ε) (fun _ => N) seed.1 seed.2 = out seed.2 := by
    rcases seed with ⟨⟨⟩, ξ⟩
    rfl
  simp_rw [he]
  refine ⟨hm.comp measurable_snd, xs, hmin, ?_⟩
  have hs : MeasurableSet {ξ | q.ε < f (out ξ) - f xs} := measurableSet_lt measurable_const ((hf.measurable.comp hm).sub measurable_const)
  have hmp := measurePreserving_snd (μ := Measure.dirac ()) (ν := (P : Measure (ℕ → q.Ω)))
  rw [← hmp.measure_preimage hs.nullMeasurableSet] at hp
  exact hp
end LongTails.Theorems.StochasticGeneralizedLipschitzConvex
