import LongTails.Proofs.AdaptiveIID

open MeasureTheory

namespace OracleTemplate.RobustGradient

open StochasticGeneralized
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma accumulated_unit_bounds {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (increment : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (hinc : ∀ n s b, 0 ≤ increment n s b ∧ increment n s b ≤ 1)
    (k : ℕ) (s : S) (ξ : ℕ → Ω) :
    0 ≤ accumulated cost next increment k s ξ ∧
      accumulated cost next increment k s ξ ≤ k := by
  induction k generalizing s ξ with
  | zero => simp [accumulated]
  | succ k ih =>
    rw [accumulated]
    have h := hinc (cost s) s (fun i => ξ i)
    have ht := ih (next (cost s) s (fun i => ξ i)) (fun i => ξ (cost s+i))
    push_cast
    constructor <;> linarith

lemma accumulated_mean_control {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] {cost : S → ℕ}
    {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {increment : (n : ℕ) → S → (Fin n → Ω) → ℝ} {c : ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hi : ∀ n, Measurable (Function.uncurry (increment n)))
    (hinc : ∀ n s b, 0 ≤ increment n s b ∧ increment n s b ≤ 1)
    (hbound : ∀ s, (∫ b, increment (cost s) s b
      ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ c) (k : ℕ) (s : S) :
    Integrable (accumulated cost next increment k s) (Measure.infinitePi fun _ : ℕ => p) ∧
    (∫ ξ, accumulated cost next increment k s ξ ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ k*c := by
  have hint (j : ℕ) (s : S) : Integrable (accumulated cost next increment j s)
      (Measure.infinitePi fun _ : ℕ => p) := by
    apply Integrable.of_bound
      (((accumulated_measurable hc hn hi j).comp measurable_prodMk_left).aestronglyMeasurable) j
    exact Filter.Eventually.of_forall (fun ξ => by
      change ‖accumulated cost next increment j s ξ‖ ≤ (j : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (accumulated_unit_bounds cost next increment hinc j s ξ).1]
      exact (accumulated_unit_bounds cost next increment hinc j s ξ).2)
  refine ⟨hint k s, ?_⟩
  induction k generalizing s with
  | zero => simp [accumulated]
  | succ k ih =>
    let m := cost s
    let F : (Fin m → Ω) × (ℕ → Ω) → ℝ := fun z =>
      increment m s z.1+accumulated cost next increment k (next m s z.1) z.2
    have hnext : Measurable (fun b : Fin m → Ω => next m s b) :=
      (hn m).comp measurable_prodMk_left
    have hincm : Measurable (fun b : Fin m → Ω => increment m s b) :=
      (hi m).comp measurable_prodMk_left
    have hF : Measurable F := (hincm.comp measurable_fst).add
      ((accumulated_measurable hc hn hi k).comp
        ((hnext.comp measurable_fst).prodMk measurable_snd))
    have hFi : Integrable F ((Measure.pi fun _ : Fin m => p).prod
        (Measure.infinitePi fun _ : ℕ => p)) := by
      apply Integrable.of_bound hF.aestronglyMeasurable (k+1)
      exact Filter.Eventually.of_forall (fun z => by
        have hi' := hinc m s z.1
        have ht := accumulated_unit_bounds cost next increment hinc k (next m s z.1) z.2
        rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ F z by dsimp [F]; linarith)]
        dsimp [F]
        linarith)
    have hi' : Integrable (fun b : Fin m → Ω => increment m s b)
        (Measure.pi fun _ : Fin m => p) := by
      apply Integrable.of_bound hincm.aestronglyMeasurable 1
      exact Filter.Eventually.of_forall (fun b => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hinc m s b).1]
        exact (hinc m s b).2)
    have hcond (b : Fin m → Ω) :
        (∫ ξ, F (b, ξ) ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ increment m s b+k*c := by
      change (∫ ξ, increment m s b+accumulated cost next increment k (next m s b) ξ
        ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ _
      rw [integral_add (integrable_const _) (hint k _)]
      simpa using add_le_add_left (ih (next m s b)) (increment m s b)
    have hprod : (∫ z, F z ∂(Measure.pi fun _ : Fin m => p).prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ (k+1)*c := by
      rw [integral_prod _ hFi]
      have h := integral_mono hFi.integral_prod_left (hi'.add (integrable_const (k*c))) hcond
      simp only [Pi.add_apply] at h
      rw [integral_add hi' (integrable_const _)] at h
      simp only [integral_const, probReal_univ, one_smul] at h
      have hb := hbound s
      dsimp only [m] at h
      linarith
    have hsplit := splitStream_preserving p m
    have he : accumulated cost next increment (k+1) s = F ∘ splitStream m := rfl
    rw [he]
    simp only [Function.comp_apply]
    rw [hsplit.integral_comp' F]
    simpa only [Nat.cast_add, Nat.cast_one] using hprod

lemma accumulated_failure_probability {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] {cost : S → ℕ}
    {next : (n : ℕ) → S → (Fin n → Ω) → S}
    {increment : (n : ℕ) → S → (Fin n → Ω) → ℝ} {c : ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hi : ∀ n, Measurable (Function.uncurry (increment n)))
    (hinc : ∀ n s b, 0 ≤ increment n s b ∧ increment n s b ≤ 1)
    (hbound : ∀ s, (∫ b, increment (cost s) s b
      ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ c) (k : ℕ) (s : S) :
    (Measure.infinitePi fun _ : ℕ => p)
      {ξ | 1 ≤ accumulated cost next increment k s ξ} ≤ ENNReal.ofReal (k*c) := by
  have h := accumulated_mean_control p hc hn hi hinc hbound k s
  exact (h.1.measure_le_integral (Filter.Eventually.of_forall
    (fun ξ => (accumulated_unit_bounds cost next increment hinc k s ξ).1))
      (fun _ hξ => hξ)).trans (ENNReal.ofReal_le_ofReal h.2)

lemma adaptive_pair_bad_mean {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set Ω} {B : Set (Ω × Ξ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {c : ℝ} (hfirst : P.real A ≤ c)
    (hsecond : ∀ ω, Q.real {ξ | (ω, ξ) ∈ B} ≤ c) :
    (∫ w : Ω × Ξ, (Prod.fst ⁻¹' A ∪ B).indicator (fun _ => (1 : ℝ)) w ∂P.prod Q) ≤ 2*c := by
  classical
  let D : Set (Ω × Ξ) := Prod.fst ⁻¹' A ∪ B
  have hD : MeasurableSet D := (hA.preimage measurable_fst).union hB
  change (∫ w, D.indicator 1 w ∂P.prod Q) ≤ 2*c
  rw [integral_indicator_one hD]
  have hfst : (P.prod Q).real (Prod.fst ⁻¹' A) = P.real A := by
    unfold Measure.real
    rw [measurePreserving_fst.measure_preimage hA.nullMeasurableSet]
  have hBi : Integrable (B.indicator (1 : Ω × Ξ → ℝ)) (P.prod Q) :=
    (integrable_const 1).indicator hB
  have hBmean : (P.prod Q).real B ≤ c := by
    rw [← integral_indicator_one hB, integral_prod _ hBi]
    have hc := integral_mono hBi.integral_prod_left (integrable_const c) (fun ω => by
      change (∫ ξ, (if (ω, ξ) ∈ B then (1 : ℝ) else 0) ∂Q) ≤ c
      have hs : MeasurableSet {ξ | (ω, ξ) ∈ B} := hB.preimage measurable_prodMk_left
      change (∫ ξ, ({ξ | (ω, ξ) ∈ B}).indicator 1 ξ ∂Q) ≤ c
      rw [integral_indicator_one hs]
      exact hsecond ω)
    simpa using hc
  have hu := measureReal_union_le (μ := P.prod Q) (Prod.fst ⁻¹' A) B
  change (P.prod Q).real D ≤ 2*c
  dsimp [D]
  rw [hfst] at hu
  linarith

end OracleTemplate.RobustGradient
