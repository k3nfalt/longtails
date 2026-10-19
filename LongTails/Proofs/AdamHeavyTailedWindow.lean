import LongTails.Proofs.AdamHeavyTailedCancellation

open MeasureTheory

namespace LongTails.Proofs.AdamHeavyTailedWindow

noncomputable def embedding {ι : Type*} (w : ℝ) (a z : ι → ℝ) :
    EuclideanSpace ℝ (Option ι) :=
  WithLp.toLp 2 fun i => i.elim (Real.sqrt w) (fun j => Real.sqrt (a j) * z j)

lemma embedding_norm_sq {ι : Type*} [Fintype ι] {w : ℝ} (hw : 0 ≤ w)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ‖embedding w a z‖ ^ 2 = w + ∑ i, a i * (z i) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [embedding, Fintype.sum_option, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt, hw, ha]

lemma embedding_norm {ι : Type*} [Fintype ι] {w : ℝ} (hw : 0 ≤ w)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ‖embedding w a z‖ = Real.sqrt (w + ∑ i, a i * (z i) ^ 2) := by
  rw [← embedding_norm_sq hw a z ha, Real.sqrt_sq (norm_nonneg _)]

lemma embedding_update {ι : Type*} [DecidableEq ι]
    (w : ℝ) (a z : ι → ℝ) (j : ι) (e : ℝ) :
    embedding w a (Function.update z j (z j + e)) =
      embedding w a z + e • PiLp.single 2 (some j) (Real.sqrt (a j)) := by
  ext i
  cases i with
  | none => simp [embedding]
  | some i =>
    by_cases hi : i = j
    · subst i
      simp [embedding]
      ring
    · simp [embedding, hi]

lemma embedding_denominator {ι : Type*} [Fintype ι] (w : ℝ)
    (a z : ι → ℝ) (τ : ℝ) : Real.sqrt w + τ ≤ ‖embedding w a z‖ + τ := by
  have hb := PiLp.norm_apply_le (embedding w a z) none
  have hh : Real.sqrt w ≤ ‖embedding w a z‖ := by
    simpa [embedding, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg w)] using hb
  exact add_le_add hh le_rfl

noncomputable def response {ι : Type*} [Fintype ι] (w : ℝ) (a : ι → ℝ)
    (τ : ℝ) (i : ι) (z : ι → ℝ) : ℝ :=
  z i / (Real.sqrt (w + ∑ k, a k * (z k) ^ 2) + τ)

lemma embedding_response {ι : Type*} [Fintype ι] {w : ℝ} (hw : 0 ≤ w)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (τ : ℝ) (i : ι) :
    (embedding w a z) (some i) / (‖embedding w a z‖ + τ) =
      Real.sqrt (a i) * response w a τ i z := by
  rw [embedding_norm hw a z ha]
  change (Real.sqrt (a i) * z i) / _ = _
  dsimp [response]
  ring

lemma response_coordinate_taylor {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w τ p : ℝ} (hw : 0 ≤ w) (hτ : 0 < τ)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i j : ι) (hai : 0 < a i)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ∃ c : ℝ, |c| ≤ (2 * Real.sqrt (a j) / τ) / Real.sqrt (a i) ∧ ∀ e : ℝ,
      |response w a τ i (Function.update z j (z j + e)) - response w a τ i z - c * e| ≤
        ((4 * (Real.sqrt (a j) / (Real.sqrt w + τ)) ^ p) / Real.sqrt (a i)) * |e| ^ p := by
  have hA : 0 < Real.sqrt w + τ := by positivity
  have hAv (e : ℝ) : Real.sqrt w + τ ≤
      ‖embedding w a z + e • PiLp.single 2 (some j) (Real.sqrt (a j))‖ + τ := by
    rw [← embedding_update]
    exact embedding_denominator w a _ τ
  obtain ⟨c, hc, ht⟩ := AdamHeavyTailedNormalizer.coordinate_normalizer_taylor
    (embedding w a z) (some i) (some j) hτ hA (embedding_denominator w a z τ) hAv hp hp2
  have hi : 0 < Real.sqrt (a i) := Real.sqrt_pos.mpr hai
  refine ⟨c / Real.sqrt (a i), ?_, ?_⟩
  · rw [abs_div, abs_of_pos hi]
    exact div_le_div_of_nonneg_right (by simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using hc) hi.le
  · intro e
    have hb := ht e
    rw [← embedding_update, embedding_response hw a _ ha τ i,
      embedding_response hw a z ha τ i] at hb
    rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hb
    have hid : response w a τ i (Function.update z j (z j + e)) - response w a τ i z -
        (c / Real.sqrt (a i)) * e =
        (Real.sqrt (a i) * response w a τ i (Function.update z j (z j + e)) -
          Real.sqrt (a i) * response w a τ i z - c * e) / Real.sqrt (a i) := by
      field_simp
    rw [hid, abs_div, abs_of_pos hi]
    calc
      _ ≤ ((4 * (Real.sqrt (a j) / (Real.sqrt w + τ)) ^ p) * |e| ^ p) / Real.sqrt (a i) :=
        div_le_div_of_nonneg_right hb hi.le
      _ = _ := by ring

lemma response_bound {ι : Type*} [Fintype ι] {w τ : ℝ} (hw : 0 ≤ w)
    (hτ : 0 < τ) (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) (hai : 0 < a i) :
    |response w a τ i z| ≤ 1 / Real.sqrt (a i) := by
  have hi : 0 < Real.sqrt (a i) := Real.sqrt_pos.mpr hai
  have hd : 0 < Real.sqrt (w + ∑ k, a k * (z k) ^ 2) + τ := by positivity
  have hb := PiLp.norm_apply_le (embedding w a z) (some i)
  have hn : Real.sqrt (a i) * |z i| ≤ Real.sqrt (w + ∑ k, a k * (z k) ^ 2) := by
    rw [embedding_norm hw a z ha] at hb
    simpa [embedding, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hb
  unfold response
  rw [abs_div, abs_of_pos hd]
  apply (div_le_div_iff₀ hd hi).2
  nlinarith

lemma response_own_coordinate_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w τ : ℝ} (hw : 0 ≤ w) (hτ : 0 < τ)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) (hai : 0 < a i) (e : ℝ) :
    |response w a τ i (Function.update z i (z i + e)) - response w a τ i z| ≤
      2 * |e| / (Real.sqrt w + τ) := by
  let x := embedding w a z
  let x' := embedding w a (Function.update z i (z i + e))
  have hi : 0 < Real.sqrt (a i) := Real.sqrt_pos.mpr hai
  have hdist : ‖x' - x‖ = Real.sqrt (a i) * |e| := by
    dsimp [x', x]
    rw [embedding_update, add_sub_cancel_left, norm_smul, PiLp.norm_single]
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    ring
  have hn : |x (some i)| ≤ ‖x‖ + τ := by
    have hh := PiLp.norm_apply_le x (some i)
    rw [Real.norm_eq_abs] at hh
    linarith
  have hdn : |x' (some i) - x (some i)| ≤ Real.sqrt (a i) * |e| := by
    simpa only [hdist, PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x' - x) (some i)
  have hdd : |(‖x'‖ + τ) - (‖x‖ + τ)| ≤ Real.sqrt (a i) * |e| := by
    simpa only [add_sub_add_right_eq_sub, hdist] using abs_norm_sub_norm_le x' x
  have hh := AdamHeavyTailedNormalizer.normalized_difference_le
    (by positivity : 0 < Real.sqrt w + τ) (by positivity : 0 ≤ Real.sqrt (a i) * |e|)
    (embedding_denominator w a z τ) (embedding_denominator w a _ τ) hn hdn hdd
  change |x' (some i) / (‖x'‖ + τ) - x (some i) / (‖x‖ + τ)| ≤ _ at hh
  dsimp [x', x] at hh
  rw [embedding_response hw a _ ha τ i, embedding_response hw a z ha τ i,
    ← mul_sub, abs_mul, abs_of_pos hi] at hh
  apply (mul_le_mul_iff_right₀ hi).mp
  convert hh using 1
  ring

lemma response_own_coordinate_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    {w τ p : ℝ} (hw : 0 ≤ w) (hτ : 0 < τ)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) (hai : 0 < a i)
    (hp : 0 ≤ p) (hp2 : p ≤ 2) (e : ℝ) :
    (response w a τ i (Function.update z i (z i + e))) ^ 2 ≤
      2 * (response w a τ i z) ^ 2 +
        (8 / a i) * (Real.sqrt (a i) * |e| / (Real.sqrt w + τ)) ^ p := by
  have hi : 0 < Real.sqrt (a i) := Real.sqrt_pos.mpr hai
  have hA : 0 < Real.sqrt w + τ := by positivity
  have hd := response_own_coordinate_difference hw hτ a z ha i hai e
  have hd' : |response w a τ i (Function.update z i (z i + e)) - response w a τ i z| ≤
      (2 / Real.sqrt (a i)) * (Real.sqrt (a i) * |e| / (Real.sqrt w + τ)) := by
    convert hd using 1
    field_simp
  have hb := response_bound hw hτ a z ha i hai
  have hb' := response_bound hw hτ a (Function.update z i (z i + e)) ha i hai
  have hcap : |response w a τ i (Function.update z i (z i + e)) - response w a τ i z| ≤
      2 / Real.sqrt (a i) := by
    have ht := abs_sub_le (response w a τ i (Function.update z i (z i + e))) 0 (response w a τ i z)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    calc
      _ ≤ _ := ht.trans (add_le_add hb' hb)
      _ = _ := by ring
  have hs := AdamHeavyTailedAlgebra.bounded_square_interpolation
    (by positivity : 0 ≤ Real.sqrt (a i) * |e| / (Real.sqrt w + τ))
    hp hp2 hd' hcap
  have heq : 2 * (2 / Real.sqrt (a i)) ^ 2 = 8 / a i := by
    rw [div_pow, Real.sq_sqrt (ha i)]
    ring
  have ht := sq_nonneg (response w a τ i (Function.update z i (z i + e)) - 2 * response w a τ i z)
  nlinarith [congrArg (fun c : ℝ => c * (Real.sqrt (a i) * |e| / (Real.sqrt w + τ)) ^ p) heq]

lemma integrable_response_coordinate {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {w τ : ℝ} (hw : 0 ≤ w) (hτ : 0 < τ)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i j : ι) (hai : 0 < a i)
    {X : Ω → ℝ} (hX : Integrable X P) :
    Integrable (fun ω => response w a τ i (Function.update z j (z j + X ω))) P := by
  have hc : Continuous (fun e : ℝ => response w a τ i (Function.update z j (z j + e))) := by
    unfold response
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro e
    exact ne_of_gt (by positivity)
  have hφ : Integrable (fun ω => response w a τ i (Function.update z j (z j + X ω))) P := by
    apply Integrable.of_bound (hc.comp_aestronglyMeasurable hX.aestronglyMeasurable) (1 / Real.sqrt (a i))
    exact Filter.Eventually.of_forall fun ω => by
      change ‖response w a τ i (Function.update z j (z j + X ω))‖ ≤ _
      rw [Real.norm_eq_abs]
      exact response_bound hw hτ a _ ha i hai
  exact hφ

lemma integrable_response_square {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {w τ : ℝ} (hw : 0 ≤ w) (hτ : 0 < τ)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i j : ι) (hai : 0 < a i)
    {X : Ω → ℝ} (hX : Integrable X P) :
    Integrable (fun ω => (response w a τ i (Function.update z j (z j + X ω))) ^ 2) P := by
  have hφ := integrable_response_coordinate hw hτ a z ha i j hai hX
  apply Integrable.of_bound (hφ.aestronglyMeasurable.pow 2) ((1 / Real.sqrt (a i)) ^ 2)
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := response_bound hw hτ a (Function.update z j (z j + X ω)) ha i hai
    change (response w a τ i (Function.update z j (z j + X ω))) ^ 2 ≤ _
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2

lemma response_own_coordinate_energy {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {w τ p : ℝ} (hw : 0 ≤ w) (hτ : 0 < τ)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) (hai : 0 < a i)
    (hp : 0 ≤ p) (hp2 : p ≤ 2) {X : Ω → ℝ} (hX : Integrable X P)
    (hm : Integrable (fun ω => |X ω| ^ p) P) :
    (∫ ω, (response w a τ i (Function.update z i (z i + X ω))) ^ 2 ∂P) ≤
      2 * (response w a τ i z) ^ 2 +
        ((8 / a i) * (Real.sqrt (a i) / (Real.sqrt w + τ)) ^ p) * (∫ ω, |X ω| ^ p ∂P) := by
  have hφ := integrable_response_square hw hτ a z ha i i hai hX
  let C := (8 / a i) * (Real.sqrt (a i) / (Real.sqrt w + τ)) ^ p
  have hh : (∫ ω, (response w a τ i (Function.update z i (z i + X ω))) ^ 2 ∂P) ≤
      ∫ ω, 2 * (response w a τ i z) ^ 2 + C * |X ω| ^ p ∂P := by
    apply integral_mono hφ ((integrable_const _).add (hm.const_mul C))
    intro ω
    have ht := response_own_coordinate_square hw hτ a z ha i hai hp hp2 (X ω)
    have heq : Real.sqrt (a i) * |X ω| / (Real.sqrt w + τ) =
        (Real.sqrt (a i) / (Real.sqrt w + τ)) * |X ω| := by ring
    rw [heq, Real.mul_rpow (by positivity) (abs_nonneg _)] at ht
    dsimp [C]
    nlinarith
  simpa only [integral_add (integrable_const _) (hm.const_mul C), integral_const,
    probReal_univ, one_smul, integral_const_mul] using hh

lemma response_coordinate_bias {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {w τ p : ℝ} (hw : 0 ≤ w) (hτ : 0 < τ)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i j : ι) (hai : 0 < a i)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) {X : Ω → ℝ} (hX : Integrable X P)
    (hmean : ∫ ω, X ω ∂P = 0) (hm : Integrable (fun ω => |X ω| ^ p) P) :
    |(∫ ω, response w a τ i (Function.update z j (z j + X ω)) ∂P) - response w a τ i z| ≤
      ((4 * (Real.sqrt (a j) / (Real.sqrt w + τ)) ^ p) / Real.sqrt (a i)) *
        ∫ ω, |X ω| ^ p ∂P := by
  have hφ := integrable_response_coordinate hw hτ a z ha i j hai hX
  obtain ⟨c, _, hrem⟩ := response_coordinate_taylor hw hτ a z ha i j hai hp hp2
  have hb := AdamHeavyTailedCancellation.centered_remainder_bias
    (φ := fun e => response w a τ i (Function.update z j (z j + e)))
    (a := c) hX hmean hφ hm (fun e => by simpa using hrem e)
  simpa using hb

lemma joint_coordinate_bias {ι κ Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {τ p W M : ℝ} (w μ : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (hτ : 0 < τ)
    (a : ι → ℝ) (z : κ → ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i j : ι) (hai : 0 < a i)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) {X : κ → Ω → ℝ}
    (hX : ∀ k, Integrable (X k) P) (hmean : ∀ k, ∫ ω, X k ω ∂P = 0)
    (hm : ∀ k, Integrable (fun ω => |X k ω| ^ p) P)
    (hW : 0 ≤ W)
    (hcoef : ∀ k, |μ k| * ((4 * (Real.sqrt (a j) / (Real.sqrt (w k) + τ)) ^ p) /
      Real.sqrt (a i)) ≤ W)
    (hmass : (∑ k, ∫ ω, |X k ω| ^ p ∂P) ≤ M) :
    |(∫ ω, ∑ k, μ k * response (w k) a τ i (Function.update (z k) j (z k j + X k ω)) ∂P) -
      ∑ k, μ k * response (w k) a τ i (z k)| ≤ W * M := by
  classical
  let C : κ → ℝ := fun k =>
    (4 * (Real.sqrt (a j) / (Real.sqrt (w k) + τ)) ^ p) / Real.sqrt (a i)
  let D : κ → ℝ := fun k =>
    (∫ ω, response (w k) a τ i (Function.update (z k) j (z k j + X k ω)) ∂P) -
      response (w k) a τ i (z k)
  have hb (k : κ) : |D k| ≤ C k * ∫ ω, |X k ω| ^ p ∂P :=
    response_coordinate_bias (hw k) hτ a (z k) ha i j hai hp hp2 (hX k) (hmean k) (hm k)
  rw [integral_finsetSum Finset.univ (fun k _ =>
    (integrable_response_coordinate (hw k) hτ a (z k) ha i j hai (hX k)).const_mul (μ k))]
  simp_rw [integral_const_mul]
  rw [← Finset.sum_sub_distrib]
  change |∑ k, (μ k * _ - μ k * _)| ≤ _
  have he : (∑ k, (μ k * (∫ ω, response (w k) a τ i
      (Function.update (z k) j (z k j + X k ω)) ∂P) - μ k * response (w k) a τ i (z k))) =
      ∑ k, μ k * D k := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp [D]
    ring
  rw [he]
  calc
    _ ≤ ∑ k, |μ k * D k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |μ k| * |D k| := by simp only [abs_mul]
    _ ≤ ∑ k, |μ k| * (C k * ∫ ω, |X k ω| ^ p ∂P) :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hb k) (abs_nonneg _)
    _ ≤ ∑ k, W * ∫ ω, |X k ω| ^ p ∂P := by
      apply Finset.sum_le_sum
      intro k _
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hcoef k) (integral_nonneg fun _ => by positivity)
    _ = W * ∑ k, ∫ ω, |X k ω| ^ p ∂P := (Finset.mul_sum _ _ _).symm
    _ ≤ W * M := mul_le_mul_of_nonneg_left hmass hW

lemma scalar_response_energy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {w ρ τ p μ : ℝ}
    (hw : 0 ≤ w) (hρ : 0 < ρ) (hτ : 0 < τ) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    {X : Ω → ℝ} (hX : Integrable X P) (hm : Integrable (fun ω => |X ω| ^ p) P) :
    (∫ ω, ((μ + X ω) / (Real.sqrt (w + ρ * (μ + X ω) ^ 2) + τ)) ^ 2 ∂P) ≤
      2 * (μ ^ 2 / (Real.sqrt (w + ρ * μ ^ 2) + τ)) / τ +
        ((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * (∫ ω, |X ω| ^ p ∂P) := by
  have hh := response_own_coordinate_energy hw hτ (fun _ : Unit => ρ) (fun _ : Unit => μ)
    (fun _ => hρ.le) () hρ hp hp2 hX hm
  simp [response] at hh
  have hd : 0 < Real.sqrt (w + ρ * μ ^ 2) + τ := by positivity
  have hτd : τ ≤ Real.sqrt (w + ρ * μ ^ 2) + τ := le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hb : (μ / (Real.sqrt (w + ρ * μ ^ 2) + τ)) ^ 2 ≤
      (μ ^ 2 / (Real.sqrt (w + ρ * μ ^ 2) + τ)) / τ := by
    rw [div_pow, div_div]
    apply div_le_div_of_nonneg_left (sq_nonneg μ) (mul_pos hd hτ)
    nlinarith
  have hc : (Real.sqrt ρ / (Real.sqrt w + τ)) ^ p ≤ (Real.sqrt ρ / τ) ^ p := by
    apply Real.rpow_le_rpow (by positivity) _ hp
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hτ (le_add_of_nonneg_left (Real.sqrt_nonneg _))
  have hm0 : 0 ≤ ∫ ω, |X ω| ^ p ∂P := integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 8 / ρ)) hm0
  calc
    _ ≤ _ := hh
    _ ≤ 2 * ((μ ^ 2 / (Real.sqrt (w + ρ * μ ^ 2) + τ)) / τ) +
        ((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * (∫ ω, |X ω| ^ p ∂P) :=
      add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num)) he
    _ = _ := by ring

lemma embedding_difference_norm_sq {ι : Type*} [Fintype ι]
    (w : ℝ) (a z y : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ‖embedding w a z - embedding w a y‖ ^ 2 = ∑ i, a i * (z i - y i) ^ 2 := by
  have he : embedding w a z - embedding w a y = embedding 0 a (fun i => z i - y i) := by
    ext i
    cases i with
    | none => simp [embedding]
    | some i =>
      change Real.sqrt (a i) * z i - Real.sqrt (a i) * y i = Real.sqrt (a i) * (z i - y i)
      ring
  rw [he, embedding_norm_sq (by norm_num) a _ ha, zero_add]

lemma denominator_difference_sq {ι : Type*} [Fintype ι]
    {w : ℝ} (hw : 0 ≤ w) (a z y : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (Real.sqrt (w + ∑ i, a i * (z i) ^ 2) - Real.sqrt (w + ∑ i, a i * (y i) ^ 2)) ^ 2 ≤
      ∑ i, a i * (z i - y i) ^ 2 := by
  rw [← embedding_norm hw a z ha, ← embedding_norm hw a y ha]
  have hh := pow_le_pow_left₀ (abs_nonneg _) (abs_norm_sub_norm_le (embedding w a z) (embedding w a y)) 2
  simpa only [sq_abs, embedding_difference_norm_sq w a z y ha] using hh

lemma denominator_vector_difference_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j)
    (g h : ι → EuclideanSpace ℝ κ) :
    (∑ k, (Real.sqrt (w k + ∑ j, a j * (g j k) ^ 2) -
      Real.sqrt (w k + ∑ j, a j * (h j k) ^ 2)) ^ 2) ≤
      ∑ j, a j * ‖g j - h j‖ ^ 2 := by
  calc
    _ ≤ ∑ k, ∑ j, a j * (g j k - h j k) ^ 2 :=
      Finset.sum_le_sum fun k _ => denominator_difference_sq (hw k) a (fun j => g j k) (fun j => h j k) ha
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
      simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]

lemma joint_response_energy {κ Ω : Type*} [Fintype κ] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (w μ : κ → ℝ)
    {ρ τ p M : ℝ} (hw : ∀ k, 0 ≤ w k) (hρ : 0 < ρ) (hτ : 0 < τ)
    (hp : 0 ≤ p) (hp2 : p ≤ 2) (X : κ → Ω → ℝ)
    (hX : ∀ k, Integrable (X k) P) (hm : ∀ k, Integrable (fun ω => |X k ω| ^ p) P)
    (hmass : (∑ k, ∫ ω, |X k ω| ^ p ∂P) ≤ M) :
    (∫ ω, ∑ k, ((μ k + X k ω) / (Real.sqrt (w k + ρ * (μ k + X k ω) ^ 2) + τ)) ^ 2 ∂P) ≤
      (2 / τ) * (∑ k, (μ k) ^ 2 / (Real.sqrt (w k + ρ * (μ k) ^ 2) + τ)) +
        ((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * M := by
  have hi (k : κ) : Integrable (fun ω =>
      ((μ k + X k ω) / (Real.sqrt (w k + ρ * (μ k + X k ω) ^ 2) + τ)) ^ 2) P := by
    simpa [response] using
      integrable_response_square (hw k) hτ (fun _ : Unit => ρ) (fun _ : Unit => μ k)
        (fun _ => hρ.le) () () hρ (hX k)
  rw [integral_finsetSum _ (fun k _ => hi k)]
  calc
    _ ≤ ∑ k, (2 * ((μ k) ^ 2 / (Real.sqrt (w k + ρ * (μ k) ^ 2) + τ)) / τ +
        ((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * (∫ ω, |X k ω| ^ p ∂P)) :=
      Finset.sum_le_sum fun k _ => scalar_response_energy (hw k) hρ hτ hp hp2 (hX k) (hm k)
    _ = (2 / τ) * (∑ k, (μ k) ^ 2 / (Real.sqrt (w k + ρ * (μ k) ^ 2) + τ)) +
        ((8 / ρ) * (Real.sqrt ρ / τ) ^ p) * (∑ k, ∫ ω, |X k ω| ^ p ∂P) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hmass (by positivity))

lemma denominator_coordinate_lower {ι : Type*} [Fintype ι] {w : ℝ} (hw : 0 ≤ w)
    (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) :
    Real.sqrt (a i) * |z i| ≤ Real.sqrt (w + ∑ k, a k * (z k) ^ 2) := by
  have hh := PiLp.norm_apply_le (embedding w a z) (some i)
  rw [embedding_norm hw a z ha] at hh
  simpa [embedding, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using hh

lemma denominator_two_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w τ : ℝ) (a z : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i j : ι) (hij : i ≠ j) :
    Real.sqrt (w + a i * (z i) ^ 2 + a j * (z j) ^ 2) + τ ≤
      Real.sqrt (w + ∑ k, a k * (z k) ^ 2) + τ := by
  apply add_le_add _ le_rfl
  apply Real.sqrt_le_sqrt
  have hh : (∑ k ∈ ({i, j} : Finset ι), a k * (z k) ^ 2) ≤ ∑ k, a k * (z k) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => mul_nonneg (ha k) (sq_nonneg _))
  simp only [Finset.sum_pair hij] at hh
  linarith


lemma norm_power_le_coordinate_sum {ι : Type*} [Fintype ι]
    (z : EuclideanSpace ℝ ι) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ‖z‖ ^ p ≤ ∑ i, |z i| ^ p := by
  have hh := AdamHeavyTailedAlgebra.weighted_rms_power Finset.univ (fun _ : ι => (1 : ℝ))
    (fun i => z i) (fun _ => by norm_num) hp hp2
  simp only [one_mul, Real.one_rpow] at hh
  have he : (∑ i, (z i) ^ 2) = ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
  simpa only [he, Real.sqrt_sq (norm_nonneg z)] using hh


end LongTails.Proofs.AdamHeavyTailedWindow
