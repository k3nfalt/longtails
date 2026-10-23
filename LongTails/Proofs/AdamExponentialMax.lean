import LongTails.Proofs.AdamHeavyTailedProcess
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Exponential

open MeasureTheory

namespace LongTails.Proofs.AdamExponentialMax

noncomputable def potential (x m : ℝ) : ℝ := Real.sqrt m + x / Real.sqrt m

lemma potential_lower {x m : ℝ} (hx : 0 ≤ x) :
    Real.sqrt m ≤ potential x m := by
  exact le_add_of_nonneg_right (div_nonneg hx (Real.sqrt_nonneg m))

lemma potential_step {x m y : ℝ} (hm : 0 < m) :
    potential y (max m y) ≤ potential x m + (y - x) / Real.sqrt m := by
  have hr : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  by_cases h : y ≤ m
  · rw [max_eq_left h]
    dsimp [potential]
    ring_nf
    exact le_rfl
  · have hmy : m ≤ y := le_of_lt (lt_of_not_ge h)
    have hy : 0 < y := lt_of_lt_of_le hm hmy
    have hry : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
    rw [max_eq_right hmy]
    dsimp [potential]
    have he : y / Real.sqrt y = Real.sqrt y := by
      apply (div_eq_iff hry.ne').2
      nlinarith [Real.sq_sqrt hy.le]
    rw [he]
    have hh : 2 * Real.sqrt y ≤ (m + y) / Real.sqrt m := (le_div_iff₀ hr).2 (by
      nlinarith [sq_nonneg (Real.sqrt y - Real.sqrt m), Real.sq_sqrt hm.le,
        Real.sq_sqrt hy.le])
    have he' : Real.sqrt m + x / Real.sqrt m + (y - x) / Real.sqrt m =
        (m + y) / Real.sqrt m := by
      field_simp
      nlinarith [Real.sq_sqrt hm.le]
    rw [he']
    linarith

lemma exp_centered_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {U : Ω → ℝ} (hU : Measurable U)
    (hi : Integrable U P) (h2 : Integrable (fun ω => (U ω) ^ 2) P)
    {θ v : ℝ} (hmean : (∫ ω, U ω ∂P) = 0)
    (hvariance : (∫ ω, (U ω) ^ 2 ∂P) ≤ v)
    (hbound : ∀ ω, |θ * U ω| ≤ 1) :
    Integrable (fun ω => Real.exp (θ * U ω - θ ^ 2 * v)) P ∧
      (∫ ω, Real.exp (θ * U ω - θ ^ 2 * v) ∂P) ≤ 1 := by
  have hp (ω) : Real.exp (θ * U ω) ≤ 1 + θ * U ω + θ ^ 2 * (U ω) ^ 2 := by
    have hh := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le (hbound ω))).2
    nlinarith only [hh]
  have hr : Integrable (fun ω => 1 + θ * U ω + θ ^ 2 * (U ω) ^ 2) P :=
    ((integrable_const 1).add (hi.const_mul θ)).add (h2.const_mul (θ ^ 2))
  have he : Integrable (fun ω => Real.exp (θ * U ω)) P := hr.mono'
    (Real.measurable_exp.comp (hU.const_mul θ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hp ω)
  have hmeanexp : (∫ ω, Real.exp (θ * U ω) ∂P) ≤ 1 + θ ^ 2 * v := by
    have hh := integral_mono he hr hp
    have hlin : Integrable (fun ω => 1 + θ * U ω) P :=
      (integrable_const 1).add (hi.const_mul θ)
    rw [integral_add hlin (h2.const_mul (θ ^ 2)),
      integral_add (integrable_const 1) (hi.const_mul θ)] at hh
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul, hmean, mul_zero,
      add_zero] at hh
    have hv := mul_le_mul_of_nonneg_left hvariance (sq_nonneg θ)
    linarith
  have hexp : 1 + θ ^ 2 * v ≤ Real.exp (θ ^ 2 * v) := by
    linarith [Real.add_one_le_exp (θ ^ 2 * v)]
  have hi' : Integrable (fun ω => Real.exp (θ * U ω - θ ^ 2 * v)) P := by
    simpa only [Real.exp_sub, div_eq_mul_inv] using he.mul_const ((Real.exp (θ ^ 2 * v))⁻¹)
  refine ⟨hi', ?_⟩
  simp only [Real.exp_sub, integral_div]
  exact (div_le_one (Real.exp_pos _)).2 (hmeanexp.trans hexp)

noncomputable def runningMax {Ω : Type*} (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 1
  | n + 1, ω => max (runningMax X n ω) (X (n + 1) ω)

lemma runningMax_ge_one {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    1 ≤ runningMax X n ω := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma measurable_runningMax {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (n : ℕ) : Measurable (runningMax X n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.max (hX (n + 1))

lemma maximal_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hX0 : ∀ ω, X 0 ω = 1)
    (hXpos : ∀ n ω, 0 ≤ X n ω) (n : ℕ)
    (hpotential : ∀ k ≤ n, Integrable (fun ω => potential (X k ω) (runningMax X k ω)) P)
    (hincrement : ∀ k < n, Integrable (fun ω =>
      (X (k + 1) ω - X k ω) / Real.sqrt (runningMax X k ω)) P)
    (hdrift : ∀ k < n, (∫ ω, (X (k + 1) ω - X k ω) /
      Real.sqrt (runningMax X k ω) ∂P) ≤ 0) :
    Integrable (fun ω => Real.sqrt (runningMax X n ω)) P ∧
      (∫ ω, Real.sqrt (runningMax X n ω) ∂P) ≤ 2 := by
  have hbound (k : ℕ) (hk : k ≤ n) : (∫ ω, potential (X k ω) (runningMax X k ω) ∂P) ≤ 2 := by
    induction k with
    | zero => norm_num [runningMax, potential, hX0]
    | succ k ih =>
        have hk' : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
        have hi := ih (Nat.le_of_lt hk')
        have hh := integral_mono (hpotential (k + 1) hk)
          ((hpotential k (Nat.le_of_lt hk')).add (hincrement k hk'))
          (fun ω => potential_step (x := X k ω) (y := X (k + 1) ω)
            (lt_of_lt_of_le zero_lt_one (runningMax_ge_one X k ω)))
        simp only [Pi.add_apply] at hh
        rw [integral_add (hpotential k (Nat.le_of_lt hk')) (hincrement k hk')] at hh
        linarith [hdrift k hk']
  have hint : Integrable (fun ω => Real.sqrt (runningMax X n ω)) P :=
    (hpotential n le_rfl).mono'
      (Real.continuous_sqrt.measurable.comp (measurable_runningMax hX n)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact potential_lower (hXpos n ω))
  exact ⟨hint, (integral_mono hint (hpotential n le_rfl) (fun ω => potential_lower (hXpos n ω))).trans
    (hbound n le_rfl)⟩

lemma potential_expected_step {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : Measurable Y) (hYi : Integrable Y P)
    (hYpos : ∀ ω, 0 ≤ Y ω) {x m : ℝ} (hm : 0 < m)
    (hmean : (∫ ω, Y ω ∂P) ≤ x) :
    Integrable (fun ω => potential (Y ω) (max m (Y ω))) P ∧
      (∫ ω, potential (Y ω) (max m (Y ω)) ∂P) ≤ potential x m := by
  have hbound (ω) : potential (Y ω) (max m (Y ω)) ≤
      Real.sqrt m + Y ω / Real.sqrt m := by
    have hh := potential_step (x := x) (y := Y ω) hm
    dsimp [potential] at hh ⊢
    rw [sub_div] at hh
    linarith
  have hnonneg (ω) : 0 ≤ potential (Y ω) (max m (Y ω)) :=
    (Real.sqrt_nonneg _).trans (potential_lower (hYpos ω))
  have hint : Integrable (fun ω => Real.sqrt m + Y ω / Real.sqrt m) P :=
    (integrable_const _).add (hYi.div_const _)
  have hmeas : Measurable (fun ω => potential (Y ω) (max m (Y ω))) := by
    dsimp [potential]
    fun_prop
  have hi := hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)]
    exact hbound ω)
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hint hbound
  rw [integral_add (integrable_const _) (hYi.div_const _)] at hh
  simp only [integral_const, probReal_univ, one_smul, integral_div] at hh
  have hd := div_le_div_of_nonneg_right hmean (Real.sqrt_nonneg m)
  exact hh.trans (by change Real.sqrt m + _ ≤ Real.sqrt m + _; linarith)

lemma predictable_multiplier_drift {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (next : S → Ω → S)
    (s : S) (ω0 : Ω) (n : ℕ) (U : S → Ω → ℝ) (A : S → ℝ)
    (hi : Integrable (fun ξ => A (AdamHeavyTailedProcess.stateAt next s ξ n) *
      (Real.exp (U (AdamHeavyTailedProcess.stateAt next s ξ n) (ξ n)) - 1))
      (Measure.infinitePi (fun _ : ℕ => P)))
    (hA : ∀ b : Fin n → Ω, 0 ≤ A (AdamHeavyTailedProcess.prefixState next s ω0 n b))
    (hUi : ∀ b : Fin n → Ω, Integrable (fun ω =>
      Real.exp (U (AdamHeavyTailedProcess.prefixState next s ω0 n b) ω)) P)
    (hUe : ∀ b : Fin n → Ω, (∫ ω,
      Real.exp (U (AdamHeavyTailedProcess.prefixState next s ω0 n b) ω) ∂P) ≤ 1) :
    (∫ ξ, A (AdamHeavyTailedProcess.stateAt next s ξ n) *
      (Real.exp (U (AdamHeavyTailedProcess.stateAt next s ξ n) (ξ n)) - 1)
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 0 := by
  have hh := AdamHeavyTailedProcess.stateAt_sample_integral_le P next s ω0 n
    (fun s ω => A s * (Real.exp (U s ω) - 1)) (fun _ => 0) hi (integrable_const 0)
    (fun b => ((hUi b).sub (integrable_const 1)).const_mul _) (fun b => by
      rw [integral_const_mul, integral_sub (hUi b) (integrable_const 1)]
      simp only [integral_const, probReal_univ, one_smul]
      exact mul_nonpos_of_nonneg_of_nonpos (hA b) (sub_nonpos.2 (hUe b)))
  simpa only [integral_zero] using hh

end LongTails.Proofs.AdamExponentialMax
