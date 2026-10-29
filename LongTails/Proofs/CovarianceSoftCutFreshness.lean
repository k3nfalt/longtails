import LongTails.Proofs.AdaptiveIID

open MeasureTheory

namespace LongTails.Proofs.CovarianceSoftCutFreshness

open OracleTemplate.StochasticGeneralized

lemma accumulated_nonneg {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (increment : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (hinc : ∀ n s b, 0 ≤ increment n s b) (k : ℕ) (s : S) (ξ : ℕ → Ω) :
    0 ≤ accumulated cost next increment k s ξ := by
  induction k generalizing s ξ with
  | zero => simp [accumulated]
  | succ k ih => exact add_nonneg (hinc _ _ _) (ih _ _)

lemma accumulated_integrable_mean {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] {cost : S → ℕ}
    {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {increment : (n : ℕ) → S → (Fin n → Ω) → ℝ} {c : ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hi : ∀ n, Measurable (Function.uncurry (increment n)))
    (hinc : ∀ n s b, 0 ≤ increment n s b)
    (hint : ∀ s, Integrable (increment (cost s) s) (Measure.pi fun _ : Fin (cost s) => p))
    (hbound : ∀ s, (∫ b, increment (cost s) s b
      ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ c) (k : ℕ) (s : S) :
    Integrable (accumulated cost next increment k s) (Measure.infinitePi fun _ : ℕ => p) ∧
    (∫ ξ, accumulated cost next increment k s ξ ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ k*c := by
  induction k generalizing s with
  | zero => simp [accumulated]
  | succ k ih =>
    let m := cost s
    let F : (Fin m → Ω) × (ℕ → Ω) → ℝ := fun z =>
      increment m s z.1 + accumulated cost next increment k (next m s z.1) z.2
    have hnext : Measurable (fun b : Fin m → Ω => next m s b) :=
      (hn m).comp measurable_prodMk_left
    have hincm : Measurable (fun b : Fin m → Ω => increment m s b) :=
      (hi m).comp measurable_prodMk_left
    have hF : Measurable F := (hincm.comp measurable_fst).add
      ((accumulated_measurable hc hn hi k).comp
        ((hnext.comp measurable_fst).prodMk measurable_snd))
    have hFnon (z) : 0 ≤ F z := add_nonneg (hinc _ _ _)
      (accumulated_nonneg cost next increment hinc _ _ _)
    have hsection (b : Fin m → Ω) : Integrable (fun ξ => F (b, ξ))
        (Measure.infinitePi fun _ : ℕ => p) := by
      change Integrable (fun ξ => increment m s b + accumulated cost next increment k (next m s b) ξ) _
      exact (integrable_const _).add (ih (next m s b)).1
    have hcond (b : Fin m → Ω) :
        (∫ ξ, F (b, ξ) ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ increment m s b+k*c := by
      change (∫ ξ, increment m s b+accumulated cost next increment k (next m s b) ξ
        ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ _
      rw [integral_add (integrable_const _) (ih _).1]
      simpa using add_le_add_left (ih (next m s b)).2 (increment m s b)
    have hFi : Integrable F ((Measure.pi fun _ : Fin m => p).prod
        (Measure.infinitePi fun _ : ℕ => p)) := by
      apply (integrable_prod_iff hF.aestronglyMeasurable).2
      refine ⟨Filter.Eventually.of_forall hsection, ?_⟩
      apply ((hint s).add (integrable_const (k*c))).mono_nonneg
        hF.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun b => integral_nonneg (fun ξ => norm_nonneg _)))
      apply Filter.Eventually.of_forall
      intro b
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hFnon _), Pi.add_apply] using hcond b
    have hprod : (∫ z, F z ∂(Measure.pi fun _ : Fin m => p).prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ (k+1)*c := by
      rw [integral_prod _ hFi]
      have h := integral_mono hFi.integral_prod_left ((hint s).add (integrable_const (k*c))) hcond
      simp only [Pi.add_apply] at h
      rw [integral_add (hint s) (integrable_const _)] at h
      simp only [integral_const, probReal_univ, one_smul] at h
      have hb := hbound s
      dsimp only [m] at h
      linarith
    have hsplit := splitStream_preserving p m
    have he : accumulated cost next increment (k+1) s = F ∘ splitStream m := rfl
    rw [he]
    refine ⟨hsplit.integrable_comp_of_integrable hFi, ?_⟩
    simp only [Function.comp_apply]
    rw [hsplit.integral_comp' F]
    simpa only [Nat.cast_add, Nat.cast_one] using hprod

lemma accumulated_mean_iid {S Ω Ξ : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [MeasurableSpace Ξ] (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure Ξ)
    (ξ : ℕ → Ξ → Ω)
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {cost : S → ℕ} {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {increment : (n : ℕ) → S → (Fin n → Ω) → ℝ} {c : ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hi : ∀ n, Measurable (Function.uncurry (increment n)))
    (hinc : ∀ n s b, 0 ≤ increment n s b)
    (hint : ∀ s, Integrable (increment (cost s) s) (Measure.pi fun _ : Fin (cost s) => p))
    (hbound : ∀ s, (∫ b, increment (cost s) s b
      ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ c) (k : ℕ) (s : S) :
    Integrable (fun ω => accumulated cost next increment k s (fun i => ξ i ω)) P ∧
    (∫ ω, accumulated cost next increment k s (fun i => ξ i ω) ∂P) ≤ k*c := by
  have h := accumulated_integrable_mean p hc hn hi hinc hint hbound k s
  refine ⟨h_samples.stream_law.integrable_comp_of_integrable h.1, ?_⟩
  have he : (∫ ω, accumulated cost next increment k s (fun i => ξ i ω) ∂P) =
      ∫ z, accumulated cost next increment k s z ∂Measure.infinitePi (fun _ : ℕ => p) := by
    rw [← h_samples.stream_law.map_eq]
    exact (integral_map h_samples.stream_law.measurable.aemeasurable
      (((accumulated_measurable hc hn hi k).comp measurable_prodMk_left).aestronglyMeasurable)).symm
  rw [he]
  exact h.2

end LongTails.Proofs.CovarianceSoftCutFreshness
