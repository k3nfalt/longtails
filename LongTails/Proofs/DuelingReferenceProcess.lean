import LongTails.Proofs.HeavyTailedTapeExecution

open MeasureTheory LongTails.Proofs.HeavyTailedProductProcess

namespace LongTails.Proofs.DuelingReferenceProcess

lemma integral_trajectory_le {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (step : S → Ω → S)
    (hm : Measurable (Function.uncurry step)) (clock : S → ℕ)
    (ht : ∀ s ω, clock (step s ω) = clock s + 1)
    (energy : S → ℝ) (he : Measurable energy)
    (bound : ℕ → ℝ) (hb : ∀ s, |energy s| ≤ bound (clock s))
    (hd : ∀ s, (∫ ω, energy (step s ω) ∂P) ≤ energy s)
    (n : ℕ) (s : S) :
    (∫ ξ, energy (trajectory step n s ξ) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ energy s := by
  let Q := Measure.infinitePi fun _ : ℕ => P
  have htime (N : ℕ) (a : S) (ξ : ℕ → Ω) : clock (trajectory step N a ξ) = clock a + N := by
    induction N generalizing a ξ with
    | zero => simp [trajectory]
    | succ N ih => rw [trajectory, ih, ht]; omega
  induction n generalizing s with
  | zero => simp [trajectory]
  | succ n ih =>
    let F := fun z : Ω × (ℕ → Ω) => energy (trajectory step n (step s z.1) z.2)
    have hstep : Measurable (step s) := hm.of_uncurry_left
    have hF : Measurable F := he.comp ((trajectory_measurable hm n).comp
      ((hstep.comp measurable_fst).prodMk measurable_snd))
    have hi : Integrable F (P.prod Q) := Integrable.of_bound hF.aestronglyMeasurable
      (bound (clock s+1+n)) (Filter.Eventually.of_forall fun z => by
        simpa only [F,Real.norm_eq_abs,htime,ht] using hb (trajectory step n (step s z.1) z.2))
    have hsplit := head_tail_preserving P
    have heq := integral_map (μ := Q) hsplit.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hsplit.map_eq] at heq
    change (∫ ξ, F (ξ 0,fun k => ξ (k+1)) ∂Q) ≤ energy s
    rw [← heq,integral_prod _ hi]
    apply le_trans _ (hd s)
    apply integral_mono hi.integral_prod_left _ (fun z => ih (step s z))
    exact Integrable.of_bound (he.comp hstep).aestronglyMeasurable (bound (clock s+1))
      (Filter.Eventually.of_forall fun z => by simpa [ht] using hb (step s z))

end LongTails.Proofs.DuelingReferenceProcess
