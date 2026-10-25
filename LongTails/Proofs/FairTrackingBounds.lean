import LongTails.Proofs.NormalizedStormMoments
import LongTails.Proofs.FairTracker

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory

lemma mod_succ_of_ne_zero {t q : ℕ} (hq : 0 < q) (h : (t + 1) % q ≠ 0) :
    (t + 1) % q = t % q + 1 := by
  have hq1 : 1 < q := by
    by_contra hh
    have he : q = 1 := by omega
    exact h (by rw [he, Nat.mod_one])
  have he : (t + 1) % q = (t % q + 1) % q := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hq1]
  have ht := Nat.mod_lt t hq
  have hh : t % q + 1 < q := by
    by_contra hn
    have heq : t % q + 1 = q := by omega
    rw [he, heq, Nat.mod_self] at h
    exact h rfl
  rw [he, Nat.mod_eq_of_lt hh]

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace Ω]

lemma biasDrift_bound (cfg : Config) (hq : 0 < cfg.q) (p : Measure (Fin cfg.m → Ω))
    (g : E → Ω → E) (F : E → E) (x0 : E) (ξ : ℕ → Fin cfg.m → Ω)
    {β0 β1 : ℝ} {T : ℕ}
    (hlocal : ∀ t < T, ‖localBias cfg p g F t
      (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1‖ ≤
        if cfg.isRefresh t then β0 else β1) :
    ∀ t, t < T → ‖biasDrift cfg p g F x0 ξ (t + 1)‖ ≤ β0 + (t % cfg.q : ℕ) * β1
  | 0, ht => by
      have hh := hlocal 0 ht
      simpa only [biasDrift, Config.isRefresh, Nat.zero_mod, beq_self_eq_true, Bool.true_eq,
        ite_true, add_zero, Nat.cast_zero, zero_mul] using hh
  | t + 1, ht => by
      have hi := biasDrift_bound cfg hq p g F x0 ξ hlocal t (by omega)
      have hh := hlocal (t + 1) ht
      rw [biasDrift]
      by_cases h : cfg.isRefresh (t + 1) = true
      · simp only [h, ite_true] at hh ⊢
        have hm : (t + 1) % cfg.q = 0 := by simpa only [Config.isRefresh, beq_iff_eq] using h
        simpa only [add_zero, hm, Nat.cast_zero, zero_mul] using hh
      · simp only [h, Bool.false_eq_true, ite_false] at hh ⊢
        have hm : (t + 1) % cfg.q ≠ 0 := by simpa only [Config.isRefresh, beq_iff_eq] using h
        rw [mod_succ_of_ne_zero hq hm, Nat.cast_add, Nat.cast_one]
        exact (norm_add_le _ _).trans (by linarith)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

lemma centeredTracker_step_moment (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B) (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E)
    (hb : ∀ t, 0 < cfg.batch t) (t : ℕ)
    (hi : Integrable (fun ξ => ‖centeredTracker cfg p g x0 ξ t‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p)) {V : ℝ}
    (hV : ∀ ξ, observationVariance cfg p g t (trajectory cfg g x0 ξ t).1
      (trajectory cfg g x0 ξ t).2.1 ≤ V) :
    Integrable (fun ξ => ‖centeredTracker cfg p g x0 ξ (t + 1)‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) ∧
    (∫ ξ, ‖centeredTracker cfg p g x0 ξ (t + 1)‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) ≤
      (if cfg.isRefresh t then 0 else
        ∫ ξ, ‖centeredTracker cfg p g x0 ξ t‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) + V / cfg.batch t := by
  let S := fun ξ => ((trajectory cfg g x0 ξ t).1, (trajectory cfg g x0 ξ t).2.1)
  have hT := measurable_trajectory cfg hm hR hg x0 t
  have hS : Measurable S := hT.fst.prodMk hT.snd.fst
  have hdep : ∀ ξ ξ', (∀ i, i < cfg.blockOffset t → ξ i = ξ' i) → S ξ = S ξ' := by
    intro ξ ξ' h
    simp only [S, trajectory_congr cfg g x0 t h]
  let U := fun ξ => if cfg.isRefresh t then (0 : E) else centeredTracker cfg p g x0 ξ t
  have hU : Measurable U := by
    dsimp [U]
    split_ifs
    · exact measurable_const
    · exact measurable_centeredTracker cfg hm hR p hg x0 hb t
  have hUd : ∀ ξ ξ', (∀ i, i < cfg.blockOffset t → ξ i = ξ' i) → U ξ = U ξ' := by
    intro ξ ξ' h
    simp only [U, centeredTracker_congr cfg p g x0 hb t h]
  have hUi : Integrable (fun ξ => ‖U ξ‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) := by
    dsimp [U]
    split_ifs
    · simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0)] using integrable_const (μ := Measure.infinitePi fun _ : ℕ => p) (0 : ℝ)
    · exact hi
  have he := centered_batch_step cfg hm hR hG hB p hg t (hb t) S hS hdep U hU hUd hUi hV
  by_cases h : cfg.isRefresh t = true
  · simpa only [U, S, centeredTracker, centeredBatch, h, ite_true, norm_zero, zero_pow (by decide : 2 ≠ 0),
      integral_zero, zero_add, add_zero] using he
  · simpa only [U, S, centeredTracker, centeredBatch, h, Bool.false_eq_true, ite_false, add_comm] using he

lemma centeredTracker_moments (cfg : Config) (hq : 0 < cfg.q) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B) (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E)
    (hb : ∀ t, 0 < cfg.batch t) {V0 V1 : ℝ} {T : ℕ}
    (hV : ∀ t < T, ∀ ξ, observationVariance cfg p g t (trajectory cfg g x0 ξ t).1
      (trajectory cfg g x0 ξ t).2.1 ≤ if cfg.isRefresh t then V0 else V1) :
    ∀ t, t < T →
      Integrable (fun ξ => ‖centeredTracker cfg p g x0 ξ (t + 1)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p) ∧
      (∫ ξ, ‖centeredTracker cfg p g x0 ξ (t + 1)‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p)) ≤
        V0 / cfg.b0 + (t % cfg.q : ℕ) * (V1 / cfg.b)
  | 0, ht => by
      have hi : Integrable (fun ξ => ‖centeredTracker cfg p g x0 ξ 0‖ ^ 2)
          (Measure.infinitePi fun _ : ℕ => p) := by simp [centeredTracker]
      have he := centeredTracker_step_moment cfg hm hR hG hB p hg x0 hb 0 hi (hV 0 ht)
      simpa only [Config.batch, Config.isRefresh, Nat.zero_mod, beq_self_eq_true, Bool.true_eq,
        ite_true, Nat.cast_zero, zero_mul, zero_add, add_zero] using he
  | t + 1, ht => by
      have hi := centeredTracker_moments cfg hq hm hR hG hB p hg x0 hb hV t (by omega)
      have he := centeredTracker_step_moment cfg hm hR hG hB p hg x0 hb (t + 1) hi.1 (hV (t + 1) ht)
      refine ⟨he.1, ?_⟩
      by_cases h : cfg.isRefresh (t + 1) = true
      · have hm' : (t + 1) % cfg.q = 0 := by simpa only [Config.isRefresh, beq_iff_eq] using h
        simpa only [Config.batch, h, ite_true, hm', Nat.cast_zero, zero_mul, zero_add, add_zero] using he.2
      · have hm' : (t + 1) % cfg.q ≠ 0 := by simpa only [Config.isRefresh, beq_iff_eq] using h
        simp only [Config.batch, h, Bool.false_eq_true, ite_false] at he
        rw [mod_succ_of_ne_zero hq hm', Nat.cast_add, Nat.cast_one]
        linarith [hi.2, he.2]

lemma tracker_expected_error (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} {F : E → E} (hg : Measurable (Function.uncurry g)) (hF : Measurable F)
    (x0 : E) (hb : ∀ t, 0 < cfg.batch t) (t : ℕ) {M β : ℝ}
    (hMi : Integrable (fun ξ => ‖centeredTracker cfg p g x0 ξ (t + 1)‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p))
    (hM : (∫ ξ, ‖centeredTracker cfg p g x0 ξ (t + 1)‖ ^ 2
      ∂(Measure.infinitePi fun _ : ℕ => p)) ≤ M)
    (hβ : ∀ ξ, ‖biasDrift cfg p g F x0 ξ (t + 1)‖ ≤ β) :
    Integrable (fun ξ => ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖)
      (Measure.infinitePi fun _ : ℕ => p) ∧
    (∫ ξ, ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖
      ∂(Measure.infinitePi fun _ : ℕ => p)) ≤ Real.sqrt M + β := by
  let P := Measure.infinitePi fun _ : ℕ => p
  have hcm := measurable_centeredTracker cfg hm hR p hg x0 hb (t + 1)
  have hdm := measurable_biasDrift cfg hm hR p hg hF x0 (t + 1)
  have hci : Integrable (fun ξ => centeredTracker cfg p g x0 ξ (t + 1)) P :=
    ((TwoSidedPL.memLp_two_iff_sq hcm.aestronglyMeasurable).mpr hMi).integrable (by norm_num)
  have hdi : Integrable (fun ξ => biasDrift cfg p g F x0 ξ (t + 1)) P :=
    Integrable.of_bound hdm.aestronglyMeasurable β (Filter.Eventually.of_forall hβ)
  have hsum := (hci.add hdi).norm
  simp_rw [direction_error_decomposition cfg p g F x0 _ hb t]
  refine ⟨hsum, ?_⟩
  have hc := (NormalizedStorm.integral_norm_le_sqrt hcm.aestronglyMeasurable hMi).trans
    (Real.sqrt_le_sqrt hM)
  have hd := integral_mono hdi.norm (integrable_const β) hβ
  simp only [integral_const, probReal_univ, one_smul] at hd
  have he := integral_mono hsum (hci.norm.add hdi.norm) (fun ξ => norm_add_le _ _)
  simp only [Pi.add_apply] at he
  rw [integral_add hci.norm hdi.norm] at he
  exact he.trans (add_le_add hc hd)

lemma expected_error_uniform_bound (cfg : Config) (hq : 0 < cfg.q) (hm : 0 < cfg.m)
    (hR : 0 < cfg.R) (hG : 0 ≤ cfg.G) (hB : 0 ≤ cfg.B)
    (p : Measure (Fin cfg.m → Ω)) [IsProbabilityMeasure p]
    {g : E → Ω → E} {F : E → E} (hg : Measurable (Function.uncurry g)) (hF : Measurable F)
    (x0 : E) (hb : ∀ t, 0 < cfg.batch t) {V0 V1 β0 β1 : ℝ} (hV1 : 0 ≤ V1) (hβ1 : 0 ≤ β1)
    (hV : ∀ t < cfg.T, ∀ ξ, observationVariance cfg p g t
      (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1 ≤
        if cfg.isRefresh t then V0 else V1)
    (hβ : ∀ t < cfg.T, ∀ ξ, ‖localBias cfg p g F t
      (trajectory cfg g x0 ξ t).1 (trajectory cfg g x0 ξ t).2.1‖ ≤
        if cfg.isRefresh t then β0 else β1) {t : ℕ} (ht : t < cfg.T) :
    Integrable (fun ξ => ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖)
      (Measure.infinitePi fun _ : ℕ => p) ∧
    (∫ ξ, ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖
      ∂(Measure.infinitePi fun _ : ℕ => p)) ≤
      Real.sqrt (V0 / cfg.b0 + ((cfg.q - 1 : ℕ) : ℝ) * (V1 / cfg.b)) +
        (β0 + ((cfg.q - 1 : ℕ) : ℝ) * β1) := by
  have hv := centeredTracker_moments cfg hq hm hR hG hB p hg x0 hb hV t ht
  have hmod : (t % cfg.q : ℕ) ≤ cfg.q - 1 := by have := Nat.mod_lt t hq; omega
  apply tracker_expected_error cfg hm hR p hg hF x0 hb t hv.1
  · exact hv.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (by exact_mod_cast hmod) (div_nonneg hV1 (Nat.cast_nonneg _))))
  · intro ξ
    exact (biasDrift_bound cfg hq p g F x0 ξ (fun j hj => hβ j hj ξ) t ht).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hmod) hβ1))

end OracleTemplate.FairVarianceReduction
