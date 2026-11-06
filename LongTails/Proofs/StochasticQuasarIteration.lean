import LongTails.Algorithms.StochasticQuasarAcceleration
import LongTails.Proofs.StochasticEnvelopeFreshness

open MeasureTheory
open scoped ENNReal

namespace OracleTemplate.StochasticQuasar

variable {S U Ω : Type*} [MeasurableSpace S] [MeasurableSpace U] [MeasurableSpace Ω]

lemma seeded_stream_run_measurable {calls : S → ℕ} {advance : U → S → (ℕ → Ω) → U}
    (hc : Measurable calls) (ha : Measurable (fun w : U × (S × (ℕ → Ω)) => advance w.1 w.2.1 w.2.2))
    (k : ℕ) : Measurable (fun w : U × ((Fin k → S) × (ℕ → Ω)) =>
      seededStreamRun calls advance k w.1 w.2.1 w.2.2) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
      have hhead : Measurable (fun w : U × ((Fin (k + 1) → S) × (ℕ → Ω)) => w.2.1 0) :=
        (measurable_pi_apply 0).comp measurable_snd.fst
      have hnext := ha.comp (measurable_fst.prodMk (hhead.prodMk measurable_snd.snd))
      have hseeds : Measurable (fun w : U × ((Fin (k + 1) → S) × (ℕ → Ω)) =>
          fun i : Fin k => w.2.1 i.succ) := by fun_prop
      have htail : Measurable (fun w : U × ((Fin (k + 1) → S) × (ℕ → Ω)) =>
          fun j => w.2.2 (calls (w.2.1 0) + j)) :=
        (LongTails.Proofs.StochasticEnvelopeFreshness.measurable_seed_shift (hc.comp hhead)).comp
          (measurable_id.prodMk measurable_snd.snd)
      exact ih.comp (hnext.prodMk (hseeds.prodMk htail))

lemma lintegral_seed_cons {P : Measure S} [IsProbabilityMeasure P] (k : ℕ)
    {F : (Fin (k + 1) → S) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ seeds, F seeds ∂Measure.pi (fun _ : Fin (k + 1) => P)) =
      ∫⁻ a, ∫⁻ seeds, F (Fin.cons a seeds) ∂Measure.pi (fun _ : Fin k => P) ∂P := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => P) 0).symm
  rw [← hp.lintegral_comp hF]
  have he := lintegral_prod (μ := P) (ν := Measure.pi (fun _ : Fin k => P)) (F ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => S) 0).symm)
    (hF.comp hp.measurable).aemeasurable
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, Function.comp_apply, cast_eq] using he

lemma reassociated_lintegral_ofReal {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μa : Measure A} {μb : Measure B} {μc : Measure C}
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μb] [IsProbabilityMeasure μc]
    {F : A × (B × C) → ℝ} (hF : Measurable F) (hb : ∀ w, 0 ≤ F w ∧ F w ≤ 1) :
    (∫⁻ seed : A × B, ∫⁻ ξ, ENNReal.ofReal (F (seed.1, seed.2, ξ)) ∂μc ∂μa.prod μb) =
      ENNReal.ofReal (∫ w, F w ∂μa.prod (μb.prod μc)) := by
  have hi : Integrable F (μa.prod (μb.prod μc)) := by
    apply Integrable.of_bound hF.aestronglyMeasurable 1
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hb w).1]
    exact (hb w).2
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun w => (hb w).1)]
  have hp := measurePreserving_prodAssoc μa μb μc
  have he := hp.lintegral_comp (ENNReal.measurable_ofReal.comp hF)
  have hm : Measurable (fun w : (A × B) × C => ENNReal.ofReal (F (w.1.1, w.1.2, w.2))) :=
    (ENNReal.measurable_ofReal.comp hF).comp hp.measurable
  exact (lintegral_prod _ hm.aemeasurable).symm.trans he

lemma seeded_stream_run_lintegral {P : Measure S} [IsProbabilityMeasure P]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {calls : S → ℕ} {advance : U → S → (ℕ → Ω) → U}
    (hc : Measurable calls) (ha : Measurable (fun w : U × (S × (ℕ → Ω)) => advance w.1 w.2.1 w.2.2))
    (hdep : ∀ u a ξ ζ, (∀ j, j < calls a → ξ j = ζ j) → advance u a ξ = advance u a ζ)
    {V : U → ℝ≥0∞} (hV : Measurable V) {good : U → Prop}
    (hkeep : ∀ u, good u → ∀ a ξ, good (advance u a ξ))
    (hstep : ∀ u, good u → (∫⁻ a, ∫⁻ ξ, V (advance u a ξ)
      ∂Measure.infinitePi (fun _ : ℕ => μ) ∂P) ≤ V u) (k : ℕ) (u : U) (hu : good u) :
    (∫⁻ seeds : Fin k → S, ∫⁻ ξ, V (seededStreamRun calls advance k u seeds ξ)
      ∂Measure.infinitePi (fun _ : ℕ => μ) ∂Measure.pi (fun _ : Fin k => P)) ≤ V u := by
  let ν := Measure.infinitePi fun _ : ℕ => μ
  induction k generalizing u with
  | zero => simp [seededStreamRun]
  | succ k ih =>
      have hrun := seeded_stream_run_measurable hc ha k
      have houter : Measurable (fun seeds : Fin (k + 1) → S =>
          ∫⁻ ξ, V (seededStreamRun calls advance (k + 1) u seeds ξ) ∂ν) :=
        (hV.comp ((seeded_stream_run_measurable hc ha (k + 1)).comp
          (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))).lintegral_prod_right'
      rw [lintegral_seed_cons k houter]
      simp only [seededStreamRun, Fin.cons_zero, Fin.cons_succ]
      apply le_trans ?_ (hstep u hu)
      apply lintegral_mono
      intro a
      let X := fun ξ => advance u a ξ
      let F := fun w : U × (ℕ → Ω) =>
        ∫⁻ seeds : Fin k → S, V (seededStreamRun calls advance k w.1 seeds w.2)
          ∂Measure.pi (fun _ : Fin k => P)
      have hX : Measurable X := ha.comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      have ht : Measurable (fun ξ : ℕ → Ω => fun j => ξ (calls a + j)) := by fun_prop
      have hFm : Measurable (fun w : (U × (ℕ → Ω)) × (Fin k → S) =>
          V (seededStreamRun calls advance k w.1.1 w.2 w.1.2)) :=
        hV.comp (hrun.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd)))
      have hF : Measurable F := hFm.lintegral_prod_right'
      have hswap : Measurable (fun w : (Fin k → S) × (ℕ → Ω) =>
          V (seededStreamRun calls advance k (X w.2) w.1 (fun j => w.2 (calls a + j)))) :=
        hV.comp (hrun.comp ((hX.comp measurable_snd).prodMk
          (measurable_fst.prodMk (ht.comp measurable_snd))))
      calc
        _ = ∫⁻ ξ, F (X ξ, fun j => ξ (calls a + j)) ∂ν :=
          lintegral_lintegral_swap hswap.aemeasurable
        _ = ∫⁻ ξ, ∫⁻ ζ, F (X ξ, ζ) ∂ν ∂ν :=
          LongTails.Proofs.StochasticEnvelopeFreshness.prefix_tail_lintegral μ (calls a) X hX
            (hdep u a) F hF
        _ ≤ ∫⁻ ξ, V (X ξ) ∂ν := by
          apply lintegral_mono
          intro ξ
          have hh : Measurable (fun w : (ℕ → Ω) × (Fin k → S) =>
              V (seededStreamRun calls advance k (X ξ) w.2 w.1)) :=
            hV.comp (hrun.comp (measurable_const.prodMk (measurable_snd.prodMk measurable_fst)))
          calc
            _ = ∫⁻ seeds : Fin k → S, ∫⁻ ζ,
                V (seededStreamRun calls advance k (X ξ) seeds ζ) ∂ν
                ∂Measure.pi (fun _ : Fin k => P) := lintegral_lintegral_swap hh.aemeasurable
            _ ≤ V (X ξ) := ih (X ξ) (hkeep u hu a ξ)

end OracleTemplate.StochasticQuasar
