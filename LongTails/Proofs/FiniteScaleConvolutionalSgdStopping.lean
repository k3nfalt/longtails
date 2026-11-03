import LongTails.Proofs.FiniteScaleConvolutionalSgdProcess

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FiniteScaleConvolutionalSgdStopping

open ManySampleConvolutionalPerceptronDynamics (State)
open FiniteScaleConvolutionalSgdDynamics
open FiniteScaleConvolutionalSgdProcess

lemma trajectory_congr {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples samples' : ℕ → ι)
    (k : ℕ) (h : ∀ j < k, samples j = samples' j) :
    trajectory K δ c p r start samples k = trajectory K δ c p r start samples' k := by
  rw [trajectory_factor, trajectory_factor]
  congr 1
  funext j
  exact h j j.isLt

lemma trajectory_shift {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples : ℕ → ι) (j k : ℕ) :
    trajectory K δ c p r start samples (j + k) =
      trajectory K δ c p r (trajectory K δ c p r start samples j) (fun n => samples (j + n)) k := by
  induction k with
  | zero => simp only [Nat.add_zero, trajectory]
  | succ k ih =>
    change next K (c (samples (j + k))) δ (p (samples (j + k))) (r (samples (j + k)))
      (trajectory K δ c p r start samples (j + k)) = _
    rw [ih]
    rfl

section Events

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples : ℕ → ι)

def EnteredBy (k : ℕ) : Prop :=
  ∃ j ≤ k, meanPotential (trajectory K δ c p r start samples j) ≤ F

def NoSeparation (k : ℕ) : Prop :=
  ∀ j ≤ k, ¬SeparatesState δ c p r (trajectory K δ c p r start samples j)

def Active (T₀ k : ℕ) : Prop :=
  EnteredBy K δ F c p r start samples (min k T₀) ∧ NoSeparation K δ c p r start samples k

noncomputable def activity (T₀ k : ℕ) : ℝ := by
  classical
  exact if Active K δ F c p r start samples T₀ k then 1 else 0

lemma activity_nonneg (T₀ k : ℕ) : 0 ≤ activity K δ F c p r start samples T₀ k := by
  unfold activity
  split_ifs <;> norm_num

lemma activity_le_one (T₀ k : ℕ) : activity K δ F c p r start samples T₀ k ≤ 1 := by
  unfold activity
  split_ifs <;> norm_num

lemma activity_congr (samples' : ℕ → ι) (T₀ k : ℕ)
    (h : ∀ j < k, samples j = samples' j) :
    activity K δ F c p r start samples T₀ k = activity K δ F c p r start samples' T₀ k := by
  have hs (j : ℕ) (hj : j ≤ k) := trajectory_congr K δ c p r start samples samples' j
    (fun l hl => h l (Nat.lt_of_lt_of_le hl hj))
  have he : EnteredBy K δ F c p r start samples (min k T₀) ↔
      EnteredBy K δ F c p r start samples' (min k T₀) := by
    constructor <;> rintro ⟨j, hj, hentry⟩
    · exact ⟨j, hj, by rwa [← hs j (hj.trans (min_le_left _ _))]⟩
    · exact ⟨j, hj, by rwa [hs j (hj.trans (min_le_left _ _))]⟩
  have hn : NoSeparation K δ c p r start samples k ↔ NoSeparation K δ c p r start samples' k := by
    constructor <;> intro hno j hj
    · rw [← hs j hj]
      exact hno j hj
    · rw [hs j hj]
      exact hno j hj
  have heq : Active K δ F c p r start samples T₀ k = Active K δ F c p r start samples' T₀ k :=
    propext (and_congr he hn)
  unfold activity
  rw [heq]

end Events

lemma sum_sampleWeight_lower {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (x : State E)
    (hK : 0 < K) (hno : ¬SeparatesState δ c p r x) :
    1 / 2 ≤ ∑ i, sampleWeight K (c i) δ (p i) (r i) x := by
  obtain ⟨i, hi⟩ : ∃ i, score (c i) δ (p i) (r i) x ≤ 0 := by
    simpa only [SeparatesState, not_forall, not_lt] using hno
  have hw := SoftQuadraticDynamics.weight_ge_half
    (mul_nonpos_of_nonneg_of_nonpos hK.le hi)
  have hh : sampleWeight K (c i) δ (p i) (r i) x ≤ ∑ j, sampleWeight K (c j) δ (p j) (r j) x :=
    Finset.single_le_sum (fun j _ => (sampleWeight_bounds K (c j) δ (p j) (r j) x).1.le)
      (Finset.mem_univ i)
  exact hw.trans hh

noncomputable def historyStream {ι : Type*} [Nonempty ι] {k : ℕ} (z : Fin k → ι) : ℕ → ι :=
  fun j => if hj : j < k then z ⟨j, hj⟩ else Classical.choice ‹Nonempty ι›

lemma historyStream_apply {ι : Type*} [Nonempty ι] {k : ℕ} (z : Fin k → ι) (j : Fin k) :
    historyStream z j = z j := by
  simp only [historyStream, dite_eq_left j.isLt, Fin.eta]

lemma historyStream_state {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nonempty ι] (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (k : ℕ) (z : Fin k → ι) :
    trajectory K δ c p r start (historyStream z) k = pastState K δ c p r start k z := by
  rw [trajectory_factor]
  simp only [historyStream_apply]

noncomputable def pastActivity {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nonempty ι] (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (T₀ k : ℕ) (z : Fin k → ι) : ℝ := activity K δ F c p r start (historyStream z) T₀ k

lemma activity_factor {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Nonempty ι] (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (samples : ℕ → ι) (T₀ k : ℕ) :
    activity K δ F c p r start samples T₀ k =
      pastActivity K δ F c p r start T₀ k (fun j : Fin k => samples j) := by
  apply activity_congr
  intro j hj
  simp only [historyStream, dite_eq_left hj]

lemma active_weight_row {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] [Nonempty ι] (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (T₀ k : ℕ) (z : Fin k → ι) (hK : 0 < K) :
    pastActivity K δ F c p r start T₀ k z / 2 ≤
      ∑ i, pastActivity K δ F c p r start T₀ k z *
        sampleWeight K (c i) δ (p i) (r i) (pastState K δ c p r start k z) := by
  classical
  by_cases h : Active K δ F c p r start (historyStream z) T₀ k
  · have hno := h.2 k le_rfl
    rw [historyStream_state] at hno
    have hh := sum_sampleWeight_lower K δ c p r (pastState K δ c p r start k z) hK hno
    simpa only [pastActivity, activity, ite_eq_left h, one_mul] using hh
  · simp only [pastActivity, activity, ite_eq_right h, zero_div, zero_mul, Finset.sum_const_zero,
      le_refl]

noncomputable def weightAt {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples : ℕ → ι) (k : ℕ) : ℝ :=
  sampleWeight K (c (samples k)) δ (p (samples k)) (r (samples k))
    (trajectory K δ c p r start samples k)

lemma active_mass_of_entry_mass {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ F B : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples : ℕ → ι)
    (T₀ T : ℕ) (hT : T₀ ≤ T) (hB : 0 ≤ B)
    (hpost : ∀ j ≤ T₀, meanPotential (trajectory K δ c p r start samples j) ≤ F →
      (∑ k ∈ Finset.range (T - j), weightAt K δ c p r start samples (j + k)) ≤ B) :
    (∑ k ∈ Finset.range T, activity K δ F c p r start samples T₀ k *
      weightAt K δ c p r start samples k) ≤ B := by
  classical
  by_cases hentry : EnteredBy K δ F c p r start samples T₀
  · have hex : ∃ j, j ≤ T₀ ∧ meanPotential (trajectory K δ c p r start samples j) ≤ F := hentry
    let J := Nat.find hex
    have hJ : J ≤ T₀ ∧ meanPotential (trajectory K δ c p r start samples J) ≤ F := Nat.find_spec hex
    have hJT : J ≤ T := hJ.1.trans hT
    have hmin (k : ℕ) (hk : Active K δ F c p r start samples T₀ k) : J ≤ k := by
      obtain ⟨j, hj, he⟩ := hk.1
      have hh : J ≤ j := Nat.find_min' hex ⟨hj.trans (min_le_right _ _), he⟩
      exact hh.trans (hj.trans (min_le_left _ _))
    have hzero (k : ℕ) (hk : k < J) : activity K δ F c p r start samples T₀ k = 0 := by
      unfold activity
      apply ite_eq_right
      intro ha
      exact (Nat.not_le_of_lt hk) (hmin k ha)
    have hprefix : (∑ k ∈ Finset.range J, activity K δ F c p r start samples T₀ k *
        weightAt K δ c p r start samples k) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [hzero k (Finset.mem_range.mp hk), zero_mul]
    calc
      _ = (∑ k ∈ Finset.range J, activity K δ F c p r start samples T₀ k *
          weightAt K δ c p r start samples k) +
          ∑ k ∈ Finset.range (T - J), activity K δ F c p r start samples T₀ (J + k) *
            weightAt K δ c p r start samples (J + k) := by
        rw [← Finset.sum_range_add, Nat.add_sub_of_le hJT]
      _ ≤ ∑ k ∈ Finset.range (T - J), weightAt K δ c p r start samples (J + k) := by
        rw [hprefix, zero_add]
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_of_le_one_left (sampleWeight_bounds _ _ _ _ _ _).1.le
          (activity_le_one K δ F c p r start samples T₀ (J + k))
      _ ≤ B := hpost J hJ.1 hJ.2
  · have hzero (k : ℕ) : activity K δ F c p r start samples T₀ k = 0 := by
      unfold activity
      apply ite_eq_right
      intro ha
      obtain ⟨j, hj, he⟩ := ha.1
      exact hentry ⟨j, hj.trans (min_le_right _ _), he⟩
    simp only [hzero, zero_mul, Finset.sum_const_zero]
    exact hB

lemma post_entry_mass {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ κ b A H H₀ F ζ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (samples : ℕ → ι) (v : E) (T j : ℕ)
    (hK : 0 < K) (hKζ : 1 / K ≤ ζ) (hδ : 0 < δ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1 / 4)
    (hb : 0 ≤ b) (hbκ : b ≤ κ / 1000) (hA : 0 ≤ A) (hAκ : A ≤ κ / 1000)
    (hH₀ : 0 ≤ H₀) (hH₀H : H₀ ≤ H / 10) (hH : 1000 ≤ κ * H)
    (hFsmall : F ≤ A ^ 2 / 4) (hFscale : 2 * F ≤ δ * H ^ 2 / 100)
    (hmean : 30 * δ * H * (T : ℝ) ≤ A ^ 2 / 4)
    (htime : δ * H * (T : ℝ) ≤ 1 / 4) (hdH : δ * H ≤ κ / 1000)
    (hζ : 0 ≤ ζ) (hζH : ζ ≤ δ * H) (hthermal : (T : ℝ) * ζ ≤ δ)
    (hWj : meanPotential (trajectory K δ c p r start samples j) ≤ F)
    (hzj : ‖(trajectory K δ c p r start samples j).z‖ ≤ H₀)
    (htj : 3 / 4 ≤ (trajectory K δ c p r start samples j).t ∧
      (trajectory K δ c p r start samples j).t ≤ 7 / 4)
    (hv : ‖v‖ ≤ 1) (hc : ∀ i, |c i| ≤ b)
    (hp : ∀ i, ‖p i‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1) (hsep : ∀ i, κ ≤ ⟪v, r i⟫) :
    (∑ k ∈ Finset.range (T - j), weightAt K δ c p r start samples (j + k)) ≤ 6 * H / κ := by
  let y := trajectory K δ c p r (trajectory K δ c p r start samples j) (fun n => samples (j + n))
  let w : ℕ → ℝ := fun k => sampleWeight K (c (samples (j + k))) δ
    (p (samples (j + k))) (r (samples (j + k))) (y k)
  have hh := FiniteScaleConvolutionalSgdTrajectory.late_path_bounds y
    (fun k => c (samples (j + k))) w (fun k => p (samples (j + k))) (fun k => r (samples (j + k)))
    v δ κ b A H H₀ F ζ T hδ hκ hκ₁ hb hbκ hA hAκ hH₀ hH₀H hH hFsmall hFscale
    hmean htime hdH hζ hζH hthermal hWj hzj htj hv (fun _ _ => rfl)
    (fun k _ => ⟨(sampleWeight_bounds _ _ _ _ _ _).1.le, (sampleWeight_bounds _ _ _ _ _ _).2⟩)
    (fun k _ => hc (samples (j + k))) (fun k _ => hp (samples (j + k)))
    (fun k _ => hr (samples (j + k))) (fun k _ => hsep (samples (j + k)))
    (fun k _ => (sampleWeight_gate _ _ _ _ _ _ hK).trans hKζ)
  have hm := (hh (T - j) (Nat.sub_le T j)).2.2.2
  have he (k : ℕ) : weightAt K δ c p r start samples (j + k) = w k := by
    dsimp only [weightAt, w, y]
    rw [trajectory_shift]
  simpa only [he] using hm

open MeasureTheory
open FiniteScaleConvolutionalSgdProbability

lemma integral_activity_le_weight {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      (PMF.uniformOfFintype ι).toMeasure P)
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (T₀ k : ℕ) (hK : 0 < K) :
    (∫ ω, activity K δ F c p r start (fun j => ξ j ω) T₀ k ∂P) / (2 * Fintype.card ι) ≤
      ∫ ω, activity K δ F c p r start (fun j => ξ j ω) T₀ k *
        weightAt K δ c p r start (fun j => ξ j ω) k ∂P := by
  let H : (Fin k → ι) × ι → ℝ := fun z => pastActivity K δ F c p r start T₀ k z.1 *
    sampleWeight K (c z.2) δ (p z.2) (r z.2) (pastState K δ c p r start k z.1)
  let G : (Fin k → ι) → ℝ := fun z => pastActivity K δ F c p r start T₀ k z /
    (2 * Fintype.card ι)
  have hm : Measurable (fun ω (j : Fin k) => ξ j ω) := Measurable.of_eval (fun j => hξ.measurable j)
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hrow (z : Fin k → ι) : G z ≤ (∑ i, H (z, i)) / Fintype.card ι := by
    have hh := div_le_div_of_nonneg_right (active_weight_row K δ F c p r start T₀ k z hK) hN.le
    simpa only [div_div, G, H] using hh
  have hi := integral_mono (integrable_finite_comp P _ hm G)
    (integrable_finite_comp P _ hm (fun z => (∑ i, H (z, i)) / Fintype.card ι))
    (fun ω => hrow (fun j : Fin k => ξ j ω))
  rw [← integral_prefix_next P ξ hξ k H] at hi
  dsimp only [G, H] at hi
  simp only [integral_div] at hi
  simp only [activity_factor, weightAt, trajectory_factor]
  exact hi

lemma integrable_activity {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι) (hξ : ∀ j, Measurable (ξ j))
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (T₀ k : ℕ) :
    Integrable (fun ω => activity K δ F c p r start (fun j => ξ j ω) T₀ k) P := by
  simp only [activity_factor]
  exact integrable_finite_comp P (fun ω (j : Fin k) => ξ j ω)
    (Measurable.of_eval (fun j : Fin k => hξ j))
    (pastActivity K δ F c p r start T₀ k)

lemma integrable_weighted_activity {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι) (hξ : ∀ j, Measurable (ξ j))
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (T₀ k : ℕ) :
    Integrable (fun ω => activity K δ F c p r start (fun j => ξ j ω) T₀ k *
      weightAt K δ c p r start (fun j => ξ j ω) k) P := by
  simp only [activity_factor, weightAt, trajectory_factor]
  exact integrable_finite_comp P (fun ω => ((fun j : Fin k => ξ j ω), ξ k ω))
    ((Measurable.of_eval (fun j : Fin k => hξ j)).prodMk (hξ k))
    (fun z => pastActivity K δ F c p r start T₀ k z.1 *
      sampleWeight K (c z.2) δ (p z.2) (r z.2) (pastState K δ c p r start k z.1))

lemma integral_active_count_bound {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      (PMF.uniformOfFintype ι).toMeasure P)
    (K δ F B : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (T₀ T : ℕ) (hK : 0 < K)
    (hbound : ∀ ω, (∑ k ∈ Finset.range T, activity K δ F c p r start (fun j => ξ j ω) T₀ k *
      weightAt K δ c p r start (fun j => ξ j ω) k) ≤ B) :
    (∫ ω, ∑ k ∈ Finset.range T, activity K δ F c p r start (fun j => ξ j ω) T₀ k ∂P) ≤
      2 * (Fintype.card ι : ℝ) * B := by
  have hiA (k : ℕ) := integrable_activity P ξ hξ.measurable K δ F c p r start T₀ k
  have hiW (k : ℕ) := integrable_weighted_activity P ξ hξ.measurable K δ F c p r start T₀ k
  have hs := Finset.sum_le_sum (s := Finset.range T) (fun k _ =>
    integral_activity_le_weight P ξ hξ K δ F c p r start T₀ k hK)
  rw [← Finset.sum_div] at hs
  have hm := integral_mono (integrable_finsetSum (Finset.range T) (fun k _ => hiW k))
    (integrable_const B) hbound
  rw [integral_finsetSum _ (fun k _ => hiW k)] at hm
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
  rw [integral_finsetSum _ (fun k _ => hiA k)]
  have hN : (0 : ℝ) < 2 * Fintype.card ι := by positivity
  have hh := (div_le_iff₀ hN).mp (hs.trans hm)
  simpa only [mul_comm] using hh

lemma failure_active_count {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples : ℕ → ι)
    (T₀ T : ℕ) (hT : T₀ ≤ T) (hentry : EnteredBy K δ F c p r start samples T₀)
    (hno : NoSeparation K δ c p r start samples T) :
    ((T - T₀ : ℕ) : ℝ) ≤ ∑ k ∈ Finset.range T, activity K δ F c p r start samples T₀ k := by
  have hone (k : ℕ) (hk₀ : T₀ ≤ k) (hkT : k ≤ T) :
      activity K δ F c p r start samples T₀ k = 1 := by
    unfold activity
    apply ite_eq_left
    constructor
    · simpa only [min_eq_right hk₀] using hentry
    · intro j hj
      exact hno j (hj.trans hkT)
  have htail : (∑ k ∈ Finset.range (T - T₀), activity K δ F c p r start samples T₀ (T₀ + k)) =
      ((T - T₀ : ℕ) : ℝ) := by
    calc
      _ = ∑ _k ∈ Finset.range (T - T₀), (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn := Finset.mem_range.mp hk
        exact hone (T₀ + k) (by omega) (by omega)
      _ = _ := by simp
  have hsplit : (∑ k ∈ Finset.range T, activity K δ F c p r start samples T₀ k) =
      (∑ k ∈ Finset.range T₀, activity K δ F c p r start samples T₀ k) +
      ∑ k ∈ Finset.range (T - T₀), activity K δ F c p r start samples T₀ (T₀ + k) := by
    rw [← Finset.sum_range_add, Nat.add_sub_of_le hT]
  rw [hsplit, htail]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun k _ => activity_nonneg K δ F c p r start samples T₀ k))

lemma late_failure_bound {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      (PMF.uniformOfFintype ι).toMeasure P)
    (K δ F B : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (T₀ T : ℕ)
    (hK : 0 < K) (hT : T₀ < T)
    (hbound : ∀ ω, (∑ k ∈ Finset.range T, activity K δ F c p r start (fun j => ξ j ω) T₀ k *
      weightAt K δ c p r start (fun j => ξ j ω) k) ≤ B) :
    P {ω | EnteredBy K δ F c p r start (fun j => ξ j ω) T₀ ∧
      NoSeparation K δ c p r start (fun j => ξ j ω) T} ≤
      ENNReal.ofReal (2 * (Fintype.card ι : ℝ) * B / (T - T₀ : ℕ)) := by
  let C : Ω → ℝ := fun ω => ∑ k ∈ Finset.range T, activity K δ F c p r start (fun j => ξ j ω) T₀ k
  have hi : Integrable C P := integrable_finsetSum (Finset.range T) (fun k _ =>
    integrable_activity P ξ hξ.measurable K δ F c p r start T₀ k)
  have hn : ∀ ω, 0 ≤ C ω := fun ω => Finset.sum_nonneg (fun k _ =>
    activity_nonneg K δ F c p r start (fun j => ξ j ω) T₀ k)
  have hden : (0 : ℝ) < (T - T₀ : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hT
  have hmean := integral_active_count_bound P ξ hξ K δ F B c p r start T₀ T hK hbound
  have hmark := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hn) hi ((T - T₀ : ℕ) : ℝ)
  have hsub : {ω | EnteredBy K δ F c p r start (fun j => ξ j ω) T₀ ∧
        NoSeparation K δ c p r start (fun j => ξ j ω) T} ⊆ {ω | ((T - T₀ : ℕ) : ℝ) ≤ C ω} := by
    intro ω hω
    exact failure_active_count K δ F c p r start (fun j => ξ j ω) T₀ T hT.le hω.1 hω.2
  have hmono := measureReal_mono (μ := P) hsub (measure_ne_top _ _)
  have hreal : P.real {ω | EnteredBy K δ F c p r start (fun j => ξ j ω) T₀ ∧
        NoSeparation K δ c p r start (fun j => ξ j ω) T} ≤
      2 * (Fintype.card ι : ℝ) * B / (T - T₀ : ℕ) := by
    apply (le_div_iff₀ hden).2
    have hh := mul_le_mul_of_nonneg_left hmono hden.le
    change (∫ ω, C ω ∂P) ≤ 2 * (Fintype.card ι : ℝ) * B at hmean
    nlinarith
  rw [← ofReal_measureReal (measure_ne_top P _)]
  exact ENNReal.ofReal_le_ofReal hreal

lemma failure_split {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K δ F : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E) (samples : ℕ → ι)
    (T₀ T : ℕ) (hT : T₀ ≤ T) (hno : NoSeparation K δ c p r start samples T) :
    alivePast K δ F c p r start T₀ (fun j : Fin T₀ => samples j) ∨
      (EnteredBy K δ F c p r start samples T₀ ∧ NoSeparation K δ c p r start samples T) := by
  classical
  by_cases he : EnteredBy K δ F c p r start samples T₀
  · exact Or.inr ⟨he, hno⟩
  · apply Or.inl
    apply (alivePast_trajectory_iff K δ F c p r start samples T₀).2
    intro j hj
    exact ⟨lt_of_not_ge (fun h => he ⟨j, hj, h⟩), hno j (hj.trans hT)⟩

lemma one_run_failure {E Ω ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ι)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ
      (PMF.uniformOfFintype ι).toMeasure P)
    (K δ κ b A H H₀ F ρ ζ : ℝ) (c : ι → ℝ) (p r : ι → E) (start : State E)
    (v : E) (T₀ T : ℕ) (hT : T₀ < T)
    (hK : 0 < K) (hKζ : 1 / K ≤ ζ) (hδ : 0 < δ) (hκ : 0 < κ) (hκ₁ : κ ≤ 1 / 4)
    (hρ : 0 ≤ ρ) (hF : 0 < F) (hb : 0 ≤ b) (hbκ : b ≤ κ / 1000)
    (hA : 0 ≤ A) (hAκ : A ≤ κ / 1000)
    (hH₀def : H₀ = 4 * (T₀ : ℝ) + 1) (hearly : δ * H₀ * (T₀ : ℝ) ≤ 1 / 100)
    (hdH₀ : δ * H₀ ≤ 1) (hζH₀ : ζ ≤ δ * H₀)
    (hfloor : 1000 * (Fintype.card ι : ℝ) * (δ * H₀) ≤ ρ ^ 2 * F)
    (hH₀H : H₀ ≤ H / 10) (hH : 1000 ≤ κ * H)
    (hFsmall : F ≤ A ^ 2 / 4) (hFscale : 2 * F ≤ δ * H ^ 2 / 100)
    (hmean : 30 * δ * H * (T : ℝ) ≤ A ^ 2 / 4)
    (htime : δ * H * (T : ℝ) ≤ 1 / 4) (hdH : δ * H ≤ κ / 1000)
    (hζ : 0 ≤ ζ) (hζH : ζ ≤ δ * H) (hthermal : (T : ℝ) * ζ ≤ δ)
    (hW₀ : meanPotential start ≤ 3) (hz₀ : ‖start.z‖ ≤ 1)
    (ht₀ : 1 ≤ start.t ∧ start.t ≤ 3 / 2)
    (hv : ‖v‖ ≤ 1) (hcl : ∀ i, ρ ≤ |c i|) (hcu : ∀ i, |c i| ≤ b)
    (hp : ∀ i, ‖p i‖ ≤ 1) (hr : ∀ i, ‖r i‖ ≤ 1) (hsep : ∀ i, κ ≤ ⟪v, r i⟫)
    (hdecay : (1 - ρ ^ 2 / (24 * Fintype.card ι)) ^ T₀ * 3 / F ≤ 1 / 8)
    (hbudget : 2 * (Fintype.card ι : ℝ) * (6 * H / κ) / (T - T₀ : ℕ) ≤ 1 / 8) :
    P {ω | NoSeparation K δ c p r start (fun j => ξ j ω) T} ≤ ENNReal.ofReal (1 / 4) := by
  have hH₀ : 0 ≤ H₀ := by rw [hH₀def]; positivity
  have hHpos : 0 < H := by nlinarith
  have hc₁ (i : ι) : |c i| ≤ 1 / 4 := by linarith [hcu i]
  have henergy := killed_integral_bound P ξ hξ K δ F ρ H₀ ζ c p r start T₀
    hK hδ.le hρ hζ hKζ hζH₀ hH₀def hearly hdH₀ hW₀ ht₀ hz₀ hcl hc₁ hp hr hfloor
  have hearlyProb : P {ω | alivePast K δ F c p r start T₀ (fun j : Fin T₀ => ξ j ω)} ≤
      ENNReal.ofReal (1 / 8) := by
    apply (killed_event_bound P ξ hξ.measurable K δ F c p r start T₀ hF).trans
    apply ENNReal.ofReal_le_ofReal
    exact (div_le_div_of_nonneg_right henergy hF.le).trans hdecay
  have hmass (ω : Ω) : (∑ k ∈ Finset.range T,
      activity K δ F c p r start (fun j => ξ j ω) T₀ k *
        weightAt K δ c p r start (fun j => ξ j ω) k) ≤ 6 * H / κ := by
    apply active_mass_of_entry_mass K δ F (6 * H / κ) c p r start (fun j => ξ j ω) T₀ T hT.le
      (by positivity)
    intro j hj hentry
    have hs : meanPotential (trajectory K δ c p r start (fun l => ξ l ω) j) ≤ 4 ∧
        (3 / 4 ≤ (trajectory K δ c p r start (fun l => ξ l ω) j).t ∧
          (trajectory K δ c p r start (fun l => ξ l ω) j).t ≤ 7 / 4) ∧
        ‖(trajectory K δ c p r start (fun l => ξ l ω) j).z‖ ≤ H₀ := by
      simpa only [trajectory_factor] using early_past_bounds K δ H₀ ζ c p r start T₀
        hK hδ.le hζ hKζ hζH₀ hH₀def hearly hdH₀ hW₀ ht₀ hz₀ hc₁ hp hr j hj
        (fun l : Fin j => ξ l ω)
    exact post_entry_mass K δ κ b A H H₀ F ζ c p r start (fun l => ξ l ω) v T j
      hK hKζ hδ hκ hκ₁ hb hbκ hA hAκ hH₀ hH₀H hH hFsmall hFscale hmean htime
      hdH hζ hζH hthermal hentry hs.2.2 hs.2.1 hv hcu hp hr hsep
  have hlateProb : P {ω | EnteredBy K δ F c p r start (fun j => ξ j ω) T₀ ∧
      NoSeparation K δ c p r start (fun j => ξ j ω) T} ≤ ENNReal.ofReal (1 / 8) := by
    exact (late_failure_bound P ξ hξ K δ F (6 * H / κ) c p r start T₀ T hK hT hmass).trans
      (ENNReal.ofReal_le_ofReal hbudget)
  have hsub : {ω | NoSeparation K δ c p r start (fun j => ξ j ω) T} ⊆
      {ω | alivePast K δ F c p r start T₀ (fun j : Fin T₀ => ξ j ω)} ∪
      {ω | EnteredBy K δ F c p r start (fun j => ξ j ω) T₀ ∧
        NoSeparation K δ c p r start (fun j => ξ j ω) T} := by
    intro ω hω
    exact failure_split K δ F c p r start (fun j => ξ j ω) T₀ T hT.le hω
  calc
    _ ≤ P ({ω | alivePast K δ F c p r start T₀ (fun j : Fin T₀ => ξ j ω)} ∪
        {ω | EnteredBy K δ F c p r start (fun j => ξ j ω) T₀ ∧
          NoSeparation K δ c p r start (fun j => ξ j ω) T}) := measure_mono hsub
    _ ≤ P {ω | alivePast K δ F c p r start T₀ (fun j : Fin T₀ => ξ j ω)} +
        P {ω | EnteredBy K δ F c p r start (fun j => ξ j ω) T₀ ∧
          NoSeparation K δ c p r start (fun j => ξ j ω) T} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) := add_le_add hearlyProb hlateProb
    _ = _ := by
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      congr 1
      norm_num

end LongTails.Proofs.FiniteScaleConvolutionalSgdStopping
