import LongTails.Proofs.ScentExecution

namespace OracleTemplate.Scent

open MeasureTheory Real
open LongTails.Setups.CompositionalEntropicRisk
open OracleTemplate.SampledConvex (extend measurable_extend extend_agree map_prefix_pair integral_prefix)

section PrefixSplit

variable {Ξ Y : Type*} [MeasurableSpace Ξ] [MeasurableSpace Y]

lemma prefix_split_bounded (p : Measure Ξ) [IsProbabilityMeasure p] (k : ℕ)
    (X : (Fin k → Ξ) → Y) (hX : Measurable X) (Φ : Y → Ξ → ℝ)
    (hΦ : Measurable (Function.uncurry Φ)) (C : ℝ)
    (hsec : ∀ y, Integrable (Φ y) p) (hbound : ∀ y, (∫ ω, |Φ y ω| ∂p) ≤ C) :
    Integrable (fun ξ : ℕ → Ξ => Φ (X (fun i : Fin k => ξ i)) (ξ k))
      (Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  set pre : (ℕ → Ξ) → (Fin k → Ξ) := fun ξ i => ξ i
  have hpre : Measurable pre := by fun_prop
  set Q := P.map pre
  have hpair : Measurable (fun ξ : ℕ → Ξ => (pre ξ, ξ k)) := by fun_prop
  let H : (Fin k → Ξ) × Ξ → ℝ := fun z => Φ (X z.1) z.2
  have hH : Measurable H := hΦ.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have hmap := map_prefix_pair p k
  have hHi : Integrable H (Q.prod p) := by
    rw [integrable_prod_iff hH.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun u => hsec (X u), ?_⟩
    refine Integrable.of_bound ?_ C ?_
    · exact (hH.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        simpa only [Real.norm_eq_abs] using hbound (X u)
  rw [show (fun ξ : ℕ → Ξ => Φ (X (fun i : Fin k => ξ i)) (ξ k)) = fun ξ => H (pre ξ, ξ k) from rfl]
  have := (integrable_map_measure hH.aestronglyMeasurable hpair.aemeasurable).mp (by rw [hmap]; exact hHi)
  exact this

end PrefixSplit

end OracleTemplate.Scent
