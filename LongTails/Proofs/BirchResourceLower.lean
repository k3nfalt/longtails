import LongTails.Proofs.BirchResourceWindow

namespace LongTails.Proofs.BirchResourceLower

open Finset MeasureTheory Set

lemma fast_probability_from_rate (p R t Φ : ℝ) (hp : 0 < p) (hR : 0 ≤ R)
    (hΦ : t = Φ / 9) (h : Φ ≤ t + (1 / p) / R) :
    p * (t * R) ≤ 1 / 8 := by
  rcases hR.eq_or_lt with hr | hr
  · simp [← hr]
  have h' := (le_div_iff₀ hr).mp (show Φ - t ≤ (1 / p) / R by linarith)
  have h'' := mul_le_mul_of_nonneg_left h' hp.le
  have he : p * (1 / p) = 1 := by field_simp
  rw [he] at h''
  rw [show Φ - t = 8 * t by linarith] at h''
  linarith only [h'']

lemma reveal_probability {Ω J : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : Finset J) (reveal : J → Set Ω)
    (fast : Set Ω) {p R t Φ : ℝ} (hp : 0 < p) (hR : 0 ≤ R)
    (hΦ : t = Φ / 9) (h : Φ ≤ t + (1 / p) / R)
    (hcap : (s.card : ℝ) ≤ t * R)
    (hprob : ∀ j ∈ s, P.real (reveal j) ≤ p)
    (hcover : fast ⊆ ⋃ j ∈ s, reveal j) :
    P.real fast ≤ 1 / 8 := by
  have hμ := (measure_mono (μ := P) hcover).trans (measure_biUnion_finset_le s reveal)
  have hfinite : (∑ j ∈ s, P (reveal j)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun j _ => measure_ne_top P (reveal j))
  have hreal := ENNReal.toReal_mono hfinite hμ
  rw [ENNReal.toReal_sum (fun j _ => measure_ne_top P (reveal j))] at hreal
  have hsum : (∑ j ∈ s, P.real (reveal j)) ≤ (s.card : ℝ) * p := by
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hprob
  calc
    _ ≤ (s.card : ℝ) * p := hreal.trans hsum
    _ ≤ (t * R) * p := mul_le_mul_of_nonneg_right hcap hp.le
    _ ≤ _ := by rw [mul_comm]; exact fast_probability_from_rate p R t Φ hp hR hΦ h

lemma predictable_reveal {Ω J : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : Finset J)
    (eligible coin : J → Set Ω) (fast : Set Ω)
    (he : ∀ j ∈ s, MeasurableSet (eligible j)) (hc : ∀ j ∈ s, MeasurableSet (coin j))
    (hf : MeasurableSet fast) {p R t Φ : ℝ} (hp : 0 < p) (hR : 0 ≤ R)
    (hΦ : t = Φ / 9) (h : Φ ≤ t + (1 / p) / R)
    (hjoint : ∀ j ∈ s, P.real (eligible j ∩ coin j) = p * P.real (eligible j))
    (hcount : ∀ ω, (∑ j ∈ s, (eligible j).indicator (fun _ => (1 : ℝ)) ω) ≤ t * R)
    (hcover : fast ⊆ ⋃ j ∈ s, eligible j ∩ coin j) :
    P.real fast ≤ 1 / 8 := by
  classical
  let count := fun j => (eligible j).indicator (fun _ : Ω => (1 : ℝ))
  let visible := fun j => (eligible j ∩ coin j).indicator (fun _ : Ω => (1 : ℝ))
  have hcover' (ω : Ω) : fast.indicator (fun _ => (1 : ℝ)) ω ≤ ∑ j ∈ s, visible j ω := by
    by_cases hw : ω ∈ fast
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hw)
      obtain ⟨hj', hvis⟩ := mem_iUnion.mp hj
      rw [indicator_of_mem hw]
      have hv : visible j ω = 1 := indicator_of_mem hvis _
      rw [← hv]
      exact single_le_sum (f := fun j => visible j ω)
        (fun j _ => indicator_nonneg (fun _ _ => zero_le_one) _) hj'
    · rw [indicator_of_notMem hw]
      exact sum_nonneg (fun j _ => indicator_nonneg (fun _ _ => zero_le_one) _)
  have hcountI (j : J) (hj : j ∈ s) : Integrable (count j) P :=
    (integrable_const _).indicator (he j hj)
  have hvisI (j : J) (hj : j ∈ s) : Integrable (visible j) P :=
    (integrable_const _).indicator ((he j hj).inter (hc j hj))
  have hu := integral_mono ((integrable_const (1 : ℝ)).indicator hf)
    (integrable_finsetSum _ hvisI) hcover'
  have hb := integral_mono (integrable_finsetSum _ hcountI) (integrable_const _) hcount
  rw [integral_indicator_const _ hf, smul_eq_mul, mul_one, integral_finsetSum _ hvisI] at hu
  rw [integral_finsetSum _ hcountI, integral_const, probReal_univ, one_smul] at hb
  have ha (j : J) (hj : j ∈ s) : (∫ ω, visible j ω ∂P) = p * (∫ ω, count j ω ∂P) := by
    rw [show visible j = (eligible j ∩ coin j).indicator (fun _ => (1 : ℝ)) from rfl,
      show count j = (eligible j).indicator (fun _ => (1 : ℝ)) from rfl,
      integral_indicator_const _ ((he j hj).inter (hc j hj)), integral_indicator_const _ (he j hj),
      smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    exact hjoint j hj
  calc
    _ ≤ ∑ j ∈ s, ∫ ω, visible j ω ∂P := hu
    _ = p * ∑ j ∈ s, ∫ ω, count j ω ∂P := by
      rw [mul_sum]
      exact sum_congr rfl ha
    _ ≤ p * (t * R) := mul_le_mul_of_nonneg_left hb hp.le
    _ ≤ _ := fast_probability_from_rate p R t Φ hp hR hΦ h

lemma many_fast_small {D : ℕ} (time work : Fin D → ℝ) {ℓ u : ℝ}
    (hℓ : 0 < ℓ) (hu : 0 < u) (ht : ∀ i, 0 ≤ time i) (hw : ∀ i, 0 ≤ work i)
    (hT : (∑ i, time i) ≤ D * ℓ / 4) (hW : (∑ i, work i) ≤ D * u / 4) :
    (D : ℝ) / 2 ≤ ∑ i, if time i ≤ ℓ ∧ work i ≤ u then (1 : ℝ) else 0 := by
  have h (i : Fin D) :
      1 ≤ (if time i ≤ ℓ ∧ work i ≤ u then (1 : ℝ) else 0) + time i / ℓ + work i / u := by
    split
    · linarith [div_nonneg (ht i) hℓ.le, div_nonneg (hw i) hu.le]
    · rename_i hbad
      push Not at hbad
      by_cases he : time i ≤ ℓ
      · have ha : 1 ≤ work i / u := (le_div_iff₀ hu).2 (by simpa using (hbad he).le)
        linarith [div_nonneg (ht i) hℓ.le]
      · have ha : 1 ≤ time i / ℓ := (le_div_iff₀ hℓ).2 (by simpa using (le_of_not_ge he))
        linarith [div_nonneg (hw i) hu.le]
  have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin D))) => h i)
  simp only [sum_const, card_fin, nsmul_eq_mul, mul_one, sum_add_distrib, ← sum_div] at hh
  have hT' : (∑ i, time i) / ℓ ≤ D / 4 := (div_le_iff₀ hℓ).2 (by linarith only [hT])
  have hW' : (∑ i, work i) / u ≤ D / 4 := (div_le_iff₀ hu).2 (by linarith only [hW])
  linarith only [hh, hT', hW']

lemma rare_many {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {D : ℕ} (hD : 0 < D) (fast : Fin D → Set Ω) (success : Set Ω)
    (hf : ∀ i, MeasurableSet (fast i)) (hs : MeasurableSet success)
    (hprob : ∀ i, P.real (fast i) ≤ 1 / 8)
    (hcount : ∀ ω ∈ success, (D : ℝ) / 2 ≤ ∑ i, (fast i).indicator (fun _ => (1 : ℝ)) ω) :
    P.real success ≤ 1 / 4 := by
  let f := fun i => (fast i).indicator (fun _ : Ω => (1 : ℝ))
  let g := success.indicator (fun _ : Ω => (D : ℝ) / 2)
  have hi (i : Fin D) : Integrable (f i) P := (integrable_const _).indicator (hf i)
  have hg : Integrable g P := (integrable_const _).indicator hs
  have hle (ω : Ω) : g ω ≤ ∑ i, f i ω := by
    by_cases h : ω ∈ success
    · rw [show g ω = (D : ℝ) / 2 from indicator_of_mem h _]
      exact hcount ω h
    · rw [show g ω = 0 from indicator_of_notMem h _]
      exact sum_nonneg (fun i _ => indicator_nonneg (fun _ _ => zero_le_one) _)
  have hh := integral_mono hg (integrable_finsetSum _ (fun i _ => hi i)) hle
  rw [integral_finsetSum _ (fun i _ => hi i)] at hh
  have hfint (i : Fin D) : (∫ ω, f i ω ∂P) = P.real (fast i) := by
    rw [show f i = (fast i).indicator (fun _ => (1 : ℝ)) from rfl,
      integral_indicator_const _ (hf i), smul_eq_mul, mul_one]
  rw [show g = success.indicator (fun _ => (D : ℝ) / 2) from rfl,
    integral_indicator_const _ hs, smul_eq_mul] at hh
  simp only [hfint] at hh
  have hsum : (∑ i, P.real (fast i)) ≤ (D : ℝ) / 8 := by
    simpa [nsmul_eq_mul, div_eq_mul_inv] using
      (sum_le_sum (s := (univ : Finset (Fin D))) (fun i _ => hprob i))
  apply le_of_mul_le_mul_right _ (show 0 < (D : ℝ) / 2 by positivity)
  linarith only [hh, hsum]

lemma short_run_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {D : ℕ} (hD : 0 < D) (time work : Fin D → Ω → ℝ) {ℓ u : ℝ}
    (hℓ : 0 < ℓ) (hu : 0 < u)
    (ht : ∀ i, Measurable (time i)) (hw : ∀ i, Measurable (work i))
    (ht₀ : ∀ i ω, 0 ≤ time i ω) (hw₀ : ∀ i ω, 0 ≤ work i ω)
    (success : Set Ω) (hs : MeasurableSet success)
    (hprob : ∀ i, P.real {ω | time i ω ≤ ℓ ∧ work i ω ≤ u} ≤ 1 / 8)
    (hT : ∀ ω ∈ success, (∑ i, time i ω) ≤ D * ℓ / 4)
    (hW : ∀ ω ∈ success, (∑ i, work i ω) ≤ D * u / 4) :
    P.real success ≤ 1 / 4 := by
  classical
  apply rare_many P hD (fun i => {ω | time i ω ≤ ℓ ∧ work i ω ≤ u}) success
    (fun i => (measurableSet_le (ht i) measurable_const).inter
      (measurableSet_le (hw i) measurable_const)) hs hprob
  intro ω hω
  simp only [indicator_apply, mem_ofPred_eq]
  exact many_fast_small (fun i => time i ω) (fun i => work i ω) hℓ hu
    (fun i => ht₀ i ω) (fun i => hw₀ i ω) (hT ω hω) (hW ω hω)

end LongTails.Proofs.BirchResourceLower
