import LongTails.Proofs.RobustEnergyConcentration
import LongTails.Proofs.StoppedVectorConcentration
import LongTails.Proofs.TerminalClippingEnergy
import LongTails.Proofs.HeavyTailedMomentBounds

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineTransportConcentration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma energy_increment_abs (s y : E) {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hs : ‖s‖ ≤ a) (hy : ‖y‖ ≤ C) :
    |2 * ⟪s, y⟫ + ‖y‖ ^ 2| ≤ 2 * a * C + C ^ 2 := by
  have hi := abs_real_inner_le_norm s y
  have hm := mul_le_mul hs hy (norm_nonneg y) ha
  have hsq := sq_le_sq₀ (norm_nonneg y) hC |>.mpr hy
  have ht := abs_add_le (2 * ⟪s, y⟫) (‖y‖ ^ 2)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (sq_nonneg ‖y‖)] at ht
  nlinarith

lemma energy_increment_sq (s y : E) {a C : ℝ}
    (ha : 0 ≤ a) (hC : 0 ≤ C) (hs : ‖s‖ ≤ a) (hy : ‖y‖ ≤ C) :
    (2 * ⟪s, y⟫ + ‖y‖ ^ 2) ^ 2 ≤ (8 * a ^ 2 + 2 * C ^ 2) * ‖y‖ ^ 2 := by
  have hi := (abs_real_inner_le_norm s y).trans
    (mul_le_mul_of_nonneg_right hs (norm_nonneg y))
  have hi2 := sq_le_sq₀ (abs_nonneg ⟪s, y⟫) (mul_nonneg ha (norm_nonneg y)) |>.mpr hi
  rw [sq_abs, mul_pow] at hi2
  have hy2 := sq_le_sq₀ (norm_nonneg y) hC |>.mpr hy
  have hy4 := mul_le_mul_of_nonneg_right hy2 (sq_nonneg ‖y‖)
  nlinarith [sq_nonneg (2 * ⟪s, y⟫ - ‖y‖ ^ 2)]

lemma energy_exponent_tuning {a C V θ ell : ℝ}
    (hC : 0 ≤ C) (hV : 0 ≤ V) (hθ : 0 ≤ θ) (hell : 1 ≤ ell)
    (hCa : C ≤ a) (hscale : θ * a ^ 2 = 2 * ell)
    (hincrement : θ * a * C ≤ 1 / 32) (hvariance : θ * V ≤ 1 / 128) :
    θ * (2 * a * C + C ^ 2) ≤ 1 ∧
      (θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * V - θ * a ^ 2 ≤ -ell := by
  have hCsmall := mul_le_mul_of_nonneg_left hCa (mul_nonneg hθ hC)
  have hCsq := pow_le_pow_left₀ hC hCa 2
  have hD := mul_le_mul_of_nonneg_left hCsq (show 0 ≤ 2 * θ ^ 2 * V by positivity)
  have hQ := mul_le_mul_of_nonneg_left hvariance (show 0 ≤ 10 * (θ * a ^ 2) by positivity)
  constructor
  · nlinarith
  · nlinarith

section Integral

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma energy_increment_mgf {Y : Ω → E} (hY : Measurable Y) (hYi : Integrable Y P)
    (hY2i : Integrable (fun ω => ‖Y ω‖ ^ 2) P)
    {a C v θ : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hθ : 0 ≤ θ) (s : E)
    (hs : ‖s‖ ≤ a) (hbound : ∀ ω, ‖Y ω‖ ≤ C)
    (hzero : (∫ ω, Y ω ∂P) = 0)
    (hsecond : (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ v)
    (hsmall : θ * (2 * a * C + C ^ 2) ≤ 1) :
    Integrable (fun ω => Real.exp (θ * (2 * ⟪s, Y ω⟫ + ‖Y ω‖ ^ 2))) P ∧
      (∫ ω, Real.exp (θ * (2 * ⟪s, Y ω⟫ + ‖Y ω‖ ^ 2)) ∂P) ≤
        Real.exp ((θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * v) := by
  let Z := fun ω => θ * (2 * ⟪s, Y ω⟫ + ‖Y ω‖ ^ 2)
  have hZ : Measurable Z := by dsimp [Z]; fun_prop
  have hZb (ω : Ω) : |Z ω| ≤ 1 := by
    dsimp [Z]
    rw [abs_mul, abs_of_nonneg hθ]
    exact (mul_le_mul_of_nonneg_left (energy_increment_abs s (Y ω) ha hC hs (hbound ω)) hθ).trans hsmall
  have hmean : (∫ ω, Z ω ∂P) ≤ θ * v := by
    dsimp [Z]
    rw [integral_const_mul, integral_add ((Integrable.const_inner (𝕜 := ℝ) s hYi).const_mul (2 : ℝ)) hY2i,
      integral_const_mul, integral_inner hYi s, hzero]
    simpa using mul_le_mul_of_nonneg_left hsecond hθ
  have hp (ω : Ω) : Z ω ^ 2 ≤
      (θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * ‖Y ω‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left
      (energy_increment_sq s (Y ω) ha hC hs (hbound ω)) (sq_nonneg θ)
    simpa only [Z, mul_pow, mul_assoc] using hh
  have hZ2i : Integrable (fun ω => Z ω ^ 2) P :=
    (hY2i.const_mul (θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2))).mono'
      (hZ.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Z ω))] using hp ω))
  have hvariance : (∫ ω, Z ω ^ 2 ∂P) ≤
      θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2) * v := by
    calc
      _ ≤ ∫ ω, (θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * ‖Y ω‖ ^ 2 ∂P :=
        integral_mono hZ2i (hY2i.const_mul _) hp
      _ = (θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * ∫ ω, ‖Y ω‖ ^ 2 ∂P := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hsecond (by positivity)
  have hh := OracleTemplate.RobustGradient.bounded_increment_mgf hZ hZb hmean hvariance
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  congr 1
  ring

variable [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma raw_moment_from_centered {X : Ω → E} (hXi : Integrable X P)
    {q : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hqi : Integrable (fun ω => ‖X ω - ∫ z, X z ∂P‖ ^ q) P) :
    Integrable (fun ω => ‖X ω‖ ^ q) P ∧
      (∫ ω, ‖X ω‖ ^ q ∂P) ≤ ‖∫ z, X z ∂P‖ ^ q +
        6 * ∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ q ∂P := by
  have he := hXi.sub (integrable_const (∫ z, X z ∂P))
  have hzero : (∫ ω, (X ω - ∫ z, X z ∂P) ∂P) = 0 := by
    rw [integral_sub hXi (integrable_const _)]
    simp
  have hi := HeavyTailedMomentBounds.integrable_norm_add_rpow (∫ z, X z ∂P)
    (by linarith : 0 < q) he.aestronglyMeasurable hqi
  have hb := HeavyTailedMomentBounds.integral_norm_add_rpow_le hq hq2 he hqi hzero
    (w := ∫ z, X z ∂P)
  simpa only [Pi.sub_apply, add_sub_cancel_left, add_sub_cancel, add_comm] using And.intro hi hb

omit [CompleteSpace E] in
lemma raw_clipping_bias {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P)
    {q C σ : ℝ} (hq : 1 ≤ q) (hC : 0 < C)
    (hqi : Integrable (fun ω => ‖X ω‖ ^ q) P)
    (hqb : (∫ ω, ‖X ω‖ ^ q ∂P) ≤ σ ^ q) :
    ‖(∫ ω, OracleTemplate.clip C (X ω) ∂P) - ∫ ω, X ω ∂P‖ ≤
      σ ^ q / (C / 2) ^ (q - 1) := by
  have hci := OracleTemplate.integrable_clip (P := P) hX hC.le
  have hb := norm_integral_le_of_norm_le (hqi.div_const ((C / 2) ^ (q - 1)))
    (f := fun ω => OracleTemplate.clip C (X ω) - X ω)
    (Filter.Eventually.of_forall (fun ω => by
      rw [norm_sub_rev]
      simpa only [sub_zero] using OracleTemplate.clip_residual_le_moment hC hq
        (u := (0 : E)) (by simpa using (show (0 : ℝ) ≤ C / 2 by positivity)) (X ω)))
  rw [integral_sub hci hXi, integral_div] at hb
  exact hb.trans (div_le_div_of_nonneg_right hqb (Real.rpow_nonneg (by positivity) _))

lemma centered_clipping_moments {X : Ω → E} (hX : Measurable X)
    {q C σ : ℝ} (hq : 0 ≤ q) (hq2 : q ≤ 2) (hC : 0 ≤ C)
    (hqi : Integrable (fun ω => ‖X ω‖ ^ q) P)
    (hqb : (∫ ω, ‖X ω‖ ^ q ∂P) ≤ σ ^ q) :
    let Y := fun ω => OracleTemplate.clip C (X ω) - ∫ z, OracleTemplate.clip C (X z) ∂P
    Integrable Y P ∧ Integrable (fun ω => ‖Y ω‖ ^ 2) P ∧
      (∫ ω, Y ω ∂P) = 0 ∧ (∀ ω, ‖Y ω‖ ≤ 2 * C) ∧
      (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ (2 * C) ^ (2 - q) * σ ^ q := by
  let W := fun ω => OracleTemplate.clip C (X ω)
  have hWi : Integrable W P := OracleTemplate.integrable_clip hX hC
  have hW2i : Integrable (fun ω => ‖W ω‖ ^ 2) P := by
    apply Integrable.of_bound (((OracleTemplate.measurable_clip C).comp hX).norm.pow_const 2).aestronglyMeasurable (C ^ 2)
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (OracleTemplate.norm_clip_le hC (X ω)) 2)
  have hcenter := OracleTemplate.TerminalClipping.centered_second_moment hWi hW2i
  have hmean : ‖∫ ω, W ω ∂P‖ ≤ C := by
    have hh := norm_integral_le_of_norm_le (integrable_const C : Integrable (fun _ : Ω => C) P)
      (Filter.Eventually.of_forall (fun ω => OracleTemplate.norm_clip_le hC (X ω)))
    simpa only [integral_const, probReal_univ, one_smul] using hh
  refine ⟨hWi.sub (integrable_const _), hcenter.1, ?_, ?_, ?_⟩
  · rw [integral_sub hWi (integrable_const _)]
    simp [W]
  · intro ω
    exact (norm_sub_le _ _).trans (by linarith [OracleTemplate.norm_clip_le hC (X ω)])
  · apply hcenter.2.trans
    simpa only [sub_zero] using OracleTemplate.clipped_second_moment_bound hX hC hq hq2
      (u := (0 : E)) (by simpa using hC) (by simpa only [sub_zero] using hqi)
      (by simpa only [sub_zero] using hqb)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P]
    [SecondCountableTopology E] in
lemma scaled_centered_moments {Y : Ω → E} {b C V : ℝ} (hb : 0 < b)
    (hi : Integrable Y P) (h2i : Integrable (fun ω => ‖Y ω‖ ^ 2) P)
    (hz : (∫ ω, Y ω ∂P) = 0) (hn : ∀ ω, ‖Y ω‖ ≤ C)
    (h2b : (∫ ω, ‖Y ω‖ ^ 2 ∂P) ≤ V) :
    Integrable (fun ω => b⁻¹ • Y ω) P ∧
      Integrable (fun ω => ‖b⁻¹ • Y ω‖ ^ 2) P ∧
      (∫ ω, b⁻¹ • Y ω ∂P) = 0 ∧ (∀ ω, ‖b⁻¹ • Y ω‖ ≤ C / b) ∧
      (∫ ω, ‖b⁻¹ • Y ω‖ ^ 2 ∂P) ≤ V / b ^ 2 := by
  have hinv : 0 ≤ b⁻¹ := inv_nonneg.mpr hb.le
  have heq (ω : Ω) : ‖b⁻¹ • Y ω‖ ^ 2 = (b⁻¹) ^ 2 * ‖Y ω‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv, mul_pow]
  refine ⟨hi.smul b⁻¹, ?_, ?_, ?_, ?_⟩
  · simpa only [heq] using h2i.const_mul ((b⁻¹) ^ 2)
  · rw [integral_smul, hz, smul_zero]
  · intro ω
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left (hn ω) hinv
  · simp_rw [heq]
    rw [integral_const_mul]
    simpa only [div_eq_mul_inv, inv_pow, mul_comm] using
      mul_le_mul_of_nonneg_left h2b (sq_nonneg b⁻¹)

end Integral

section Process

open StoppedVectorConcentration

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]

lemma iid_stopped_energy_bound {ξ : ℕ → Ω → Z}
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    {Y : (n : ℕ) → (Fin n → Z) × Z → E} (hY : ∀ n, Measurable (Y n))
    (hYi : ∀ n a, Integrable (fun z => Y n (a, z)) p)
    (hY2i : ∀ n a, Integrable (fun z => ‖Y n (a, z)‖ ^ 2) p)
    {a C v θ : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hv : 0 ≤ v) (hθ : 0 ≤ θ)
    (hbound : ∀ n h z, ‖Y n (h, z)‖ ≤ C)
    (hzero : ∀ n h, (∫ z, Y n (h, z) ∂p) = 0)
    (hsecond : ∀ n h, (∫ z, ‖Y n (h, z)‖ ^ 2 ∂p) ≤ v)
    (hsmall : θ * (2 * a * C + C ^ 2) ≤ 1) (n : ℕ) :
    Integrable (fun ω => Real.exp (θ * ‖historyStoppedSum Y a n (fun i => ξ i ω)‖ ^ 2)) P ∧
      (∫ ω, Real.exp (θ * ‖historyStoppedSum Y a n (fun i => ξ i ω)‖ ^ 2) ∂P) ≤
        Real.exp ((n : ℝ) * ((θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * v)) := by
  let S := fun n (h : Fin n → Z) => θ * ‖historyStoppedSum Y a n h‖ ^ 2
  let I := fun n (w : (Fin n → Z) × Z) =>
    if ‖historyStoppedSum Y a n w.1‖ ≤ a then
      θ * (2 * ⟪historyStoppedSum Y a n w.1, Y n w⟫ + ‖Y n w‖ ^ 2) else 0
  have hS : ∀ n, Measurable (S n) := fun n =>
    ((history_stopped_sum_measurable hY a n).norm.pow_const 2).const_mul θ
  have hI : ∀ n, Measurable (I n) := by
    intro n
    have hh : Measurable (fun w : (Fin n → Z) × Z => historyStoppedSum Y a n w.1) :=
      (history_stopped_sum_measurable hY a n).comp measurable_fst
    have hm : Measurable (fun w : (Fin n → Z) × Z =>
        θ * (2 * ⟪historyStoppedSum Y a n w.1, Y n w⟫ + ‖Y n w‖ ^ 2)) := by
      fun_prop
    exact hm.ite (measurableSet_le hh.norm measurable_const) measurable_const
  have hinit : ∀ ω, S 0 (fun i => ξ i ω) = 0 := by
    intro ω
    simp [S, historyStoppedSum]
  have hstep : ∀ k ω, S (k + 1) (fun i => ξ i ω) =
      S k (fun i => ξ i ω) + I k ((fun i => ξ i ω), ξ k ω) := by
    intro k ω
    simp only [S, I, history_stopped_sum_eq]
    rw [stoppedSum]
    split_ifs <;> (try rw [norm_add_sq_real]) <;> ring
  have hmgf (k : ℕ) (h : Fin k → Z) :
      Integrable (fun z => Real.exp (I k (h, z))) p ∧
      (∫ z, Real.exp (I k (h, z)) ∂p) ≤
        Real.exp ((θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * v) := by
    by_cases hs : ‖historyStoppedSum Y a k h‖ ≤ a
    · simpa only [I, hs, ite_true, Function.comp_apply] using
        energy_increment_mgf ((hY k).comp measurable_prodMk_left) (hYi k h) (hY2i k h)
          ha hC hθ (historyStoppedSum Y a k h) hs (hbound k h) (hzero k h)
          (hsecond k h) hsmall
    · simp only [I, hs, ite_false, Real.exp_zero]
      refine ⟨integrable_const 1, ?_⟩
      simp only [integral_const, probReal_univ, one_smul]
      exact Real.one_le_exp (by positivity)
  exact AdaptiveOracleConcentration.iid_exponential_recursion hξ hind hlaw hS hI hinit hstep
    (fun k h => (hmgf k h).1) (fun k h => (hmgf k h).2) n

def historyActiveCount (A : (n : ℕ) → (Fin n → Z) → Bool) :
    (n : ℕ) → (Fin n → Z) → ℕ
  | 0, _ => 0
  | n + 1, h => historyActiveCount A n (Fin.init h) + if A n (Fin.init h) then 1 else 0

lemma historyActiveCount_measurable (A : (n : ℕ) → (Fin n → Z) → Bool)
    (hA : ∀ n, Measurable (A n)) (n : ℕ) : Measurable (historyActiveCount A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hinit : Measurable (Fin.init : (Fin (n + 1) → Z) → Fin n → Z) :=
      measurable_pi_iff.mpr (fun i => measurable_pi_apply i.castSucc)
    exact (ih.comp hinit).add (Measurable.ite
      (measurableSet_eq_fun ((hA n).comp hinit) measurable_const) measurable_const measurable_const)

omit [MeasurableSpace Z] in
lemma historyActiveCount_eq (A : (n : ℕ) → (Fin n → Z) → Bool) (ξ : ℕ → Z) (n : ℕ) :
    historyActiveCount A n (fun i => ξ i) =
      ∑ k ∈ Finset.range n, if A k (fun i => ξ i) then 1 else 0 := by
  induction n with
  | zero => simp [historyActiveCount]
  | succ n ih =>
    simp only [historyActiveCount, Fin.init_def, Fin.val_castSucc, Finset.sum_range_succ]
    rw [ih]
    rfl

lemma iid_compensated_energy_bound {ξ : ℕ → Ω → Z}
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    {Y : (n : ℕ) → (Fin n → Z) × Z → E} (hY : ∀ n, Measurable (Y n))
    (hYi : ∀ n a, Integrable (fun z => Y n (a, z)) p)
    (hY2i : ∀ n a, Integrable (fun z => ‖Y n (a, z)‖ ^ 2) p)
    (A : (n : ℕ) → (Fin n → Z) → Bool) (hA : ∀ n, Measurable (A n))
    (hinactive : ∀ n h, A n h = false → ∀ z, Y n (h, z) = 0)
    {a C v θ B : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hv : 0 ≤ v) (hθ : 0 ≤ θ)
    (hbound : ∀ n h z, ‖Y n (h, z)‖ ≤ C)
    (hzero : ∀ n h, (∫ z, Y n (h, z) ∂p) = 0)
    (hsecond : ∀ n h, (∫ z, ‖Y n (h, z)‖ ^ 2 ∂p) ≤ v)
    (hsmall : θ * (2 * a * C + C ^ 2) ≤ 1)
    (D : (n : ℕ) → (Fin n → Z) → ℝ) (hD : ∀ n, Measurable (D n))
    (hDzero : ∀ ω, D 0 (fun i => ξ i ω) = 0)
    (hDstep : ∀ k ω, D (k + 1) (fun i => ξ i ω) = D k (fun i => ξ i ω) +
      if A k (fun i => ξ i ω) then (θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * v else 0)
    (n : ℕ) (hDB : ∀ ω, D n (fun i => ξ i ω) ≤ B) :
    Integrable (fun ω => Real.exp (θ * ‖historyStoppedSum Y a n (fun i => ξ i ω)‖ ^ 2)) P ∧
      (∫ ω, Real.exp (θ * ‖historyStoppedSum Y a n (fun i => ξ i ω)‖ ^ 2) ∂P) ≤ Real.exp B := by
  let rate := (θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * v
  have hrate : 0 ≤ rate := by dsimp [rate]; positivity
  let S := fun n (h : Fin n → Z) => θ * ‖historyStoppedSum Y a n h‖ ^ 2 - D n h
  let I := fun n (w : (Fin n → Z) × Z) =>
    (if ‖historyStoppedSum Y a n w.1‖ ≤ a then
      θ * (2 * ⟪historyStoppedSum Y a n w.1, Y n w⟫ + ‖Y n w‖ ^ 2) else 0) -
      if A n w.1 then rate else 0
  have hS : ∀ k, Measurable (S k) := fun k =>
    (((history_stopped_sum_measurable hY a k).norm.pow_const 2).const_mul θ).sub (hD k)
  have hI : ∀ k, Measurable (I k) := by
    intro k
    have hh : Measurable (fun w : (Fin k → Z) × Z => historyStoppedSum Y a k w.1) :=
      (history_stopped_sum_measurable hY a k).comp measurable_fst
    have hm : Measurable (fun w : (Fin k → Z) × Z =>
        θ * (2 * ⟪historyStoppedSum Y a k w.1, Y k w⟫ + ‖Y k w‖ ^ 2)) := by fun_prop
    exact (hm.ite (measurableSet_le hh.norm measurable_const) measurable_const).sub
      (measurable_const.ite (measurableSet_eq_fun ((hA k).comp measurable_fst) measurable_const)
        measurable_const)
  have hinit : ∀ ω, S 0 (fun i => ξ i ω) = 0 := by
    intro ω
    simp [S, historyStoppedSum, hDzero]
  have hstep : ∀ k ω, S (k + 1) (fun i => ξ i ω) =
      S k (fun i => ξ i ω) + I k ((fun i => ξ i ω), ξ k ω) := by
    intro k ω
    simp only [S, I, hDstep, history_stopped_sum_eq]
    rw [stoppedSum]
    split_ifs <;> (try rw [norm_add_sq_real]) <;> (try dsimp [rate]) <;> ring
  have hmgf (k : ℕ) (h : Fin k → Z) :
      Integrable (fun z => Real.exp (I k (h, z))) p ∧
        (∫ z, Real.exp (I k (h, z)) ∂p) ≤ Real.exp 0 := by
    by_cases hact : A k h = true
    · by_cases hs : ‖historyStoppedSum Y a k h‖ ≤ a
      · have hh := energy_increment_mgf ((hY k).comp measurable_prodMk_left)
          (hYi k h) (hY2i k h) ha hC hθ (historyStoppedSum Y a k h) hs
          (hbound k h) (hzero k h) (hsecond k h) hsmall
        simp only [I, hs, ite_true, hact, Real.exp_sub]
        refine ⟨hh.1.div_const _, ?_⟩
        rw [integral_div, Real.exp_zero]
        exact (div_le_one (Real.exp_pos rate)).mpr hh.2
      · simp only [I, hs, ite_false, hact, ite_true, zero_sub]
        refine ⟨integrable_const _, ?_⟩
        simp only [integral_const, probReal_univ, one_smul]
        exact Real.exp_le_exp.mpr (by linarith)
    · have hf : A k h = false := Bool.eq_false_iff.mpr hact
      have hz := hinactive k h hf
      simp only [I, hf, Bool.false_eq_true, ite_false, hz, inner_zero_right, norm_zero,
        zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero, ite_self, sub_zero]
      exact ⟨integrable_const _, le_rfl.trans_eq (by simp)⟩
  have hr := AdaptiveOracleConcentration.iid_exponential_recursion hξ hind hlaw hS hI hinit hstep
    (fun k h => (hmgf k h).1) (fun k h => (hmgf k h).2) n
  have hmeas : Measurable (fun ω => Real.exp (θ * ‖historyStoppedSum Y a n (fun i => ξ i ω)‖ ^ 2)) :=
    ((((history_stopped_sum_measurable hY a n).comp
      (measurable_pi_iff.mpr (fun i => hξ i))).norm.pow_const 2).const_mul θ).exp
  have hdom := hr.1.const_mul (Real.exp B)
  have hpoint (ω : Ω) : Real.exp (θ * ‖historyStoppedSum Y a n (fun i => ξ i ω)‖ ^ 2) ≤
      Real.exp B * Real.exp (S n (fun i => ξ i ω)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [S]
    linarith [hDB ω]
  have hi : Integrable (fun ω => Real.exp (θ * ‖historyStoppedSum Y a n (fun i => ξ i ω)‖ ^ 2)) P :=
    hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hpoint ω))
  refine ⟨hi, (integral_mono hi hdom hpoint).trans ?_⟩
  rw [integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left hr.2 (Real.exp_pos B).le
  simpa using hb

lemma iid_active_count_energy_bound {ξ : ℕ → Ω → Z}
    (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    {Y : (n : ℕ) → (Fin n → Z) × Z → E} (hY : ∀ n, Measurable (Y n))
    (hYi : ∀ n a, Integrable (fun z => Y n (a, z)) p)
    (hY2i : ∀ n a, Integrable (fun z => ‖Y n (a, z)‖ ^ 2) p)
    (A : (n : ℕ) → (Fin n → Z) → Bool) (hA : ∀ n, Measurable (A n))
    (hinactive : ∀ n h, A n h = false → ∀ z, Y n (h, z) = 0)
    {a C v θ : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hv : 0 ≤ v) (hθ : 0 ≤ θ)
    (hbound : ∀ n h z, ‖Y n (h, z)‖ ≤ C)
    (hzero : ∀ n h, (∫ z, Y n (h, z) ∂p) = 0)
    (hsecond : ∀ n h, (∫ z, ‖Y n (h, z)‖ ^ 2 ∂p) ≤ v)
    (hsmall : θ * (2 * a * C + C ^ 2) ≤ 1)
    (N n : ℕ) (hcount : ∀ ω, historyActiveCount A n (fun i => ξ i ω) ≤ N) :
    Integrable (fun ω => Real.exp (θ * ‖historyStoppedSum Y a n (fun i => ξ i ω)‖ ^ 2)) P ∧
      (∫ ω, Real.exp (θ * ‖historyStoppedSum Y a n (fun i => ξ i ω)‖ ^ 2) ∂P) ≤
        Real.exp ((N : ℝ) * ((θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * v)) := by
  let rate := (θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * v
  have hrate : 0 ≤ rate := by dsimp [rate]; positivity
  let D := fun k (h : Fin k → Z) => (historyActiveCount A k h : ℝ) * rate
  have hD : ∀ k, Measurable (D k) := by
    intro k
    exact ((measurable_of_countable (fun j : ℕ => (j : ℝ))).comp
      (historyActiveCount_measurable A hA k)).mul_const rate
  have hzeroD : ∀ ω, D 0 (fun i => ξ i ω) = 0 := by
    intro ω
    simp [D, historyActiveCount]
  have hstepD : ∀ k ω, D (k + 1) (fun i => ξ i ω) = D k (fun i => ξ i ω) +
      if A k (fun i => ξ i ω) then (θ + θ ^ 2 * (8 * a ^ 2 + 2 * C ^ 2)) * v else 0 := by
    intro k ω
    change ((historyActiveCount A k (fun i => ξ i ω) +
      if A k (fun i => ξ i ω) then 1 else 0 : ℕ) : ℝ) * rate =
        (historyActiveCount A k (fun i => ξ i ω) : ℝ) * rate +
          if A k (fun i => ξ i ω) then rate else 0
    by_cases ha : A k (fun i => ξ i ω) = true
    · simp only [ha, ite_true, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    · simp [ha]
  exact iid_compensated_energy_bound hξ hind hlaw hY hYi hY2i A hA hinactive ha hC hv hθ
    hbound hzero hsecond hsmall D hD hzeroD hstepD n (fun ω =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount ω) hrate)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] in
lemma maximal_sum_tail {Y : Ω → ℕ → E} {a θ V : ℝ} (ha : 0 ≤ a)
    (hθ : 0 ≤ θ) (n : ℕ)
    (hi : Integrable (fun ω => Real.exp (θ * ‖stoppedSum (Y ω) a n‖ ^ 2)) P)
    (hb : (∫ ω, Real.exp (θ * ‖stoppedSum (Y ω) a n‖ ^ 2) ∂P) ≤ Real.exp V) :
    P.real {ω | ∃ k ≤ n, a < ‖∑ i ∈ Finset.range k, Y ω i‖} ≤
      Real.exp (V - θ * a ^ 2) := by
  have hsubset : {ω | ∃ k ≤ n, a < ‖∑ i ∈ Finset.range k, Y ω i‖} ⊆
      {ω | a ^ 2 ≤ ‖stoppedSum (Y ω) a n‖ ^ 2} := by
    rintro ω ⟨k, hk, hlarge⟩
    have he : a < ‖stoppedSum (Y ω) a n‖ := by
      by_contra hn
      have hp := stopped_sum_prefix_bound (le_of_not_gt hn) hk
      have heq := stopped_sum_eq_unstopped hp
      rw [heq] at hp
      exact (not_le.mpr hlarge) hp
    exact pow_le_pow_left₀ ha he.le 2
  exact (measureReal_mono hsubset).trans (exponential_tail_of_bound hθ hi hb (a ^ 2))

end Process

lemma expected_from_failure_and_second {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    {e η M δ : ℝ} (he : 0 ≤ e) (hη : 0 < η)
    (hsecond : (∫ ω, X ω ^ 2 ∂P) ≤ M)
    (hfailure : P.real {ω | e < X ω} ≤ δ) :
    Integrable X P ∧ (∫ ω, X ω ∂P) ≤ e + η * M + δ / (4 * η) := by
  classical
  let A := {ω | e < X ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hX
  let B := A.indicator (fun _ : Ω => (4 * η)⁻¹)
  have hBi : Integrable B P := (integrable_const _).indicator hA
  let W := fun ω => e + η * X ω ^ 2 + B ω
  have hWi : Integrable W P := ((integrable_const e).add (hX2.const_mul η)).add hBi
  have hpoint (ω : Ω) : X ω ≤ W ω := by
    by_cases hb : ω ∈ A
    · have hid : (4 * η) * (4 * η)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
      dsimp [W, B]
      rw [Set.indicator_of_mem hb]
      have hs := sq_nonneg (2 * η * X ω - 1)
      have hn := mul_nonneg he hη.le
      nlinarith
    · have hx : X ω ≤ e := le_of_not_gt hb
      dsimp [W, B]
      rw [Set.indicator_of_notMem hb]
      nlinarith [sq_nonneg (X ω)]
  have hXi : Integrable X P := hWi.mono' hX.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
      exact hpoint ω))
  have hB : (∫ ω, B ω ∂P) ≤ δ / (4 * η) := by
    dsimp [B]
    rw [integral_indicator hA]
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
    change P.real A * (4 * η)⁻¹ ≤ δ / (4 * η)
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hfailure (by positivity)
  refine ⟨hXi, (integral_mono hXi hWi hpoint).trans ?_⟩
  change (∫ ω, (e + η * X ω ^ 2) + B ω ∂P) ≤ _
  have hbase : Integrable (fun ω => e + η * X ω ^ 2) P :=
    (integrable_const e).add (hX2.const_mul η)
  rw [integral_add hbase hBi, integral_add (integrable_const e) (hX2.const_mul η), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  have hs := mul_le_mul_of_nonneg_left hsecond hη.le
  linarith

end LongTails.Proofs.AffineTransportConcentration
