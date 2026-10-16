import LongTails.Proofs.WeakGradientConvolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

open MeasureTheory Set

namespace LongTails.Proofs.ScalarMomentConcentration

lemma centered_even_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Integrable X P) (k : ℕ)
    (hi : Integrable (fun ξ => |X ξ| ^ (2 * (k + 1))) P) :
    Integrable (fun ξ => |X ξ - ∫ z, X z ∂P| ^ (2 * (k + 1))) P ∧
      (∫ ξ, |X ξ - ∫ z, X z ∂P| ^ (2 * (k + 1)) ∂P) ≤
        2 ^ (2 * (k + 1)) * ∫ ξ, |X ξ| ^ (2 * (k + 1)) ∂P := by
  let n := 2 * (k + 1)
  have hn : Even n := ⟨k + 1, by dsimp [n]; omega⟩
  have hn0 : 0 < n := by dsimp [n]; omega
  change Integrable (fun ξ => |X ξ| ^ n) P at hi
  have hXi : Integrable (fun ξ => X ξ ^ n) P := by simpa only [hn.pow_abs] using hi
  have hmean : (∫ ξ, X ξ ∂P) ^ n ≤ ∫ ξ, X ξ ^ n ∂P := by
    exact hn.convexOn_pow.map_integral_le (continuous_id.pow n).continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => mem_univ _)) hX hXi
  let m := ∫ ξ, X ξ ∂P
  have hb (ξ : Ω) : (X ξ - m) ^ n ≤ 2 ^ (n - 1) * (X ξ ^ n + m ^ n) := by
    simpa only [sub_eq_add_neg, hn.neg_pow] using (hn.add_pow_le (a := X ξ) (b := -m))
  have hI : Integrable (fun ξ => (X ξ - m) ^ n) P := by
    apply ((hXi.add (integrable_const (m ^ n))).const_mul (2 ^ (n - 1))).mono'
      ((hX.aestronglyMeasurable.sub aestronglyMeasurable_const).pow n)
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (hn.pow_nonneg _)]
    exact hb ξ
  have hbound := integral_mono hI
    ((hXi.add (integrable_const (m ^ n))).const_mul (2 ^ (n - 1))) hb
  simp only [Pi.add_apply, integral_const_mul, integral_add hXi (integrable_const (m ^ n))] at hbound
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hbound
  have hpow : (2 : ℝ) ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn0]
  have hfinal : (∫ ξ, (X ξ - m) ^ n ∂P) ≤ 2 ^ n * ∫ ξ, X ξ ^ n ∂P := by
    have hh := mul_le_mul_of_nonneg_left hmean (by positivity : 0 ≤ (2 : ℝ) ^ (n - 1))
    change (2 : ℝ) ^ (n - 1) * m ^ n ≤ _ at hh
    rw [← hpow]
    nlinarith only [hbound, hh]
  change Integrable (fun ξ => |X ξ - m| ^ n) P ∧
    (∫ ξ, |X ξ - m| ^ n ∂P) ≤ 2 ^ n * ∫ ξ, |X ξ| ^ n ∂P
  simpa only [hn.pow_abs] using And.intro hI hfinal

lemma bounded_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → ℝ} {M : ℝ}
    (hX : Measurable X) (hM : ∀ ξ, |X ξ| ≤ M) (θ : ℝ) :
    Integrable (fun ξ => Real.exp (θ * X ξ)) P := by
  apply Integrable.of_bound ((measurable_const.mul hX).exp).aestronglyMeasurable (Real.exp (|θ| * M))
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    θ * X ξ ≤ |θ * X ξ| := le_abs_self _
    _ = |θ| * |X ξ| := abs_mul _ _
    _ ≤ |θ| * M := mul_le_mul_of_nonneg_left (hM ξ) (abs_nonneg θ)

lemma probability_integral_square {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Integrable X P) (hX2 : Integrable (fun ξ => X ξ ^ 2) P) :
    (∫ ξ, X ξ ∂P) ^ 2 ≤ ∫ ξ, X ξ ^ 2 ∂P := by
  exact (show Even 2 by decide).convexOn_pow.map_integral_le
    (continuous_id.pow 2).continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _)) hX hX2

lemma centered_exp_le_cosh {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {M : ℝ}
    (hX : Measurable X) (hM : ∀ ξ, |X ξ| ≤ M) (θ : ℝ) :
    Integrable (fun ξ => Real.exp (θ * (X ξ - ∫ z, X z ∂P))) P ∧
    Integrable (fun ξ => Real.cosh (2 * θ * X ξ)) P ∧
      (∫ ξ, Real.exp (θ * (X ξ - ∫ z, X z ∂P)) ∂P) ≤
        ∫ ξ, Real.cosh (2 * θ * X ξ) ∂P := by
  have hXi : Integrable X P := Integrable.of_bound hX.aestronglyMeasurable M
    (Filter.Eventually.of_forall (fun ξ => by simpa only [Real.norm_eq_abs] using hM ξ))
  have hp := bounded_exp_integrable (P := P) hX hM θ
  have hn := bounded_exp_integrable (P := P) hX hM (-θ)
  have hp2 := bounded_exp_integrable (P := P) hX hM (2 * θ)
  have hn2 := bounded_exp_integrable (P := P) hX hM (2 * (-θ))
  have he2 (a : ℝ) : (fun ξ => Real.exp (a * X ξ) ^ 2) =
      fun ξ => Real.exp ((2 * a) * X ξ) := by
    funext ξ
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hps := probability_integral_square hp (by rw [he2]; exact hp2)
  have hns := probability_integral_square hn (by rw [he2]; exact hn2)
  rw [he2] at hps hns
  have hmean : Real.exp (-θ * ∫ ξ, X ξ ∂P) ≤ ∫ ξ, Real.exp (-θ * X ξ) ∂P := by
    have hh := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => mem_univ _)) (hXi.const_mul (-θ)) hn
    simpa only [integral_const_mul, Function.comp_def] using hh
  have hec : (fun ξ => Real.exp (θ * (X ξ - ∫ z, X z ∂P))) =
      fun ξ => Real.exp (-θ * ∫ z, X z ∂P) * Real.exp (θ * X ξ) := by
    funext ξ
    rw [← Real.exp_add]
    congr 1
    ring
  have heh : (fun ξ => Real.cosh (2 * θ * X ξ)) =
      fun ξ => (Real.exp ((2 * θ) * X ξ) + Real.exp ((2 * (-θ)) * X ξ)) / 2 := by
    funext ξ
    simp only [Real.cosh_eq, mul_neg, neg_mul]
  have hci : Integrable (fun ξ => Real.cosh (2 * θ * X ξ)) P := by
    rw [heh]
    exact (hp2.add hn2).div_const 2
  refine ⟨?_, hci, ?_⟩
  · rw [hec]
    exact hp.const_mul _
  · rw [hec, heh, integral_const_mul, integral_div, integral_add hp2 hn2]
    have ha : 0 ≤ ∫ ξ, Real.exp (θ * X ξ) ∂P := integral_nonneg (fun _ => (Real.exp_pos _).le)
    have hm := mul_le_mul_of_nonneg_right hmean ha
    nlinarith [sq_nonneg ((∫ ξ, Real.exp (θ * X ξ) ∂P) - (∫ ξ, Real.exp (-θ * X ξ) ∂P))]

lemma finite_geometric_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, r ^ i) ≤ 1 / (1 - r) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - r)).mpr
  rw [geom_sum_mul_neg]
  linarith [pow_nonneg hr0 n]

lemma cosh_bound_of_even_coefficients {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {C r : ℝ}
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hi : ∀ n : ℕ, Integrable (fun ξ => X ξ ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ)) P)
    (hb : ∀ n : ℕ, (∫ ξ, X ξ ^ (2 * (n + 1)) / ((2 * (n + 1)).factorial : ℝ) ∂P) ≤ C * r ^ n) :
    Integrable (fun ξ => Real.cosh (X ξ)) P ∧
      (∫ ξ, Real.cosh (X ξ) ∂P) ≤ 1 + C / (1 - r) := by
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  let T := fun n : ℕ => fun ξ => X ξ ^ (2 * n) / ((2 * n).factorial : ℝ)
  let F := fun n : ℕ => fun ξ => ∑ i ∈ Finset.range n, T i ξ
  have hT (n : ℕ) : Integrable (T n) P := by
    cases n with
    | zero => simp [T]
    | succ n => exact hi n
  have hF (n : ℕ) : Integrable (F n) P := integrable_finsetSum _ (fun i _ => hT i)
  have hnon (n : ℕ) : ∀ᵐ ξ ∂P, 0 ≤ F n ξ := Filter.Eventually.of_forall (fun ξ => by
    apply Finset.sum_nonneg
    intro i _
    dsimp [T]
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact (even_two_mul i).pow_nonneg _)
  have hbound (n : ℕ) : (∫ ξ, F n ξ ∂P) ≤ 1 + C / (1 - r) := by
    cases n with
    | zero => simp only [F, Finset.range_zero, Finset.sum_empty, integral_zero]; positivity
    | succ n =>
      have he : (∫ ξ, F (n + 1) ξ ∂P) = 1 + ∑ i ∈ Finset.range n, ∫ ξ, T (i + 1) ξ ∂P := by
        rw [show F (n + 1) = fun ξ => ∑ i ∈ Finset.range (n + 1), T i ξ from rfl,
          integral_finsetSum _ (fun i _ => hT i), Finset.sum_range_succ']
        simp [T, add_comm]
      rw [he]
      have hs : (∑ i ∈ Finset.range n, ∫ ξ, T (i + 1) ξ ∂P) ≤ C * ∑ i ∈ Finset.range n, r ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => hb i)
      have hg := mul_le_mul_of_nonneg_left (finite_geometric_bound hr0 hr1 n) hC
      have hh : C * (1 / (1 - r)) = C / (1 - r) := by ring
      rw [hh] at hg
      linarith
  have ht : ∀ᵐ ξ ∂P, Filter.Tendsto (fun n => F n ξ) Filter.atTop (nhds (Real.cosh (X ξ))) :=
    Filter.Eventually.of_forall (fun ξ => (Real.hasSum_cosh (X ξ)).tendsto_sum_nat)
  exact WeakGradientConvolution.nonnegative_limit_integral_bound (by positivity)
    hF hnon hbound ht

lemma cosh_coefficient_bound {A B s θ : ℝ} (hB : 0 ≤ B) (k : ℕ)
    (hA : A ≤ 12 * 8 ^ (k + 1) * ((k + 1).factorial : ℝ) * B * s ^ (2 * k)) :
    (2 * θ) ^ (2 * (k + 1)) * A / ((2 * (k + 1)).factorial : ℝ) ≤
      192 * B * θ ^ 2 * (16 * θ ^ 2 * s ^ 2) ^ k := by
  have hf : (2 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) ≤ ((2 * (k + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.two_pow_mul_factorial_le_factorial_two_mul (k + 1)
  have hpos : (0 : ℝ) < ((2 * (k + 1)).factorial : ℝ) := by positivity
  apply (div_le_iff₀ hpos).mpr
  calc
    (2 * θ) ^ (2 * (k + 1)) * A ≤
        (2 * θ) ^ (2 * (k + 1)) * (12 * 8 ^ (k + 1) * ((k + 1).factorial : ℝ) * B * s ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left hA ((even_two_mul (k + 1)).pow_nonneg _)
    _ = (192 * B * θ ^ 2 * (16 * θ ^ 2 * s ^ 2) ^ k) *
        (2 ^ (k + 1) * ((k + 1).factorial : ℝ)) := by
      have he : (2 : ℝ) ^ (2 * k) * 8 ^ k = 2 ^ k * 16 ^ k := by
        rw [pow_mul, ← mul_pow, ← mul_pow]
        norm_num
      linear_combination (384 * θ ^ 2 * θ ^ (2 * k) * ((k + 1).factorial : ℝ) * B * s ^ (2 * k)) * he
    _ ≤ (192 * B * θ ^ 2 * (16 * θ ^ 2 * s ^ 2) ^ k) * ((2 * (k + 1)).factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hf (by positivity)

lemma bounded_centered_mgf_of_even_moments {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {M B s θ : ℝ}
    (hX : Measurable X) (hM : ∀ ξ, |X ξ| ≤ M) (hB : 0 ≤ B)
    (hr : 16 * θ ^ 2 * s ^ 2 < 1)
    (hm : ∀ k : ℕ, Integrable (fun ξ => |X ξ| ^ (2 * (k + 1))) P ∧
      (∫ ξ, |X ξ| ^ (2 * (k + 1)) ∂P) ≤
        12 * 8 ^ (k + 1) * ((k + 1).factorial : ℝ) * B * s ^ (2 * k)) :
    Integrable (fun ξ => Real.exp (θ * (X ξ - ∫ z, X z ∂P))) P ∧
      (∫ ξ, Real.exp (θ * (X ξ - ∫ z, X z ∂P)) ∂P) ≤
        Real.exp (192 * B * θ ^ 2 / (1 - 16 * θ ^ 2 * s ^ 2)) := by
  have he (k : ℕ) :
      (fun ξ => (2 * θ * X ξ) ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ)) =
      fun ξ => ((2 * θ) ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ)) *
        |X ξ| ^ (2 * (k + 1)) := by
    funext ξ
    rw [mul_pow, pow_abs_two_mul]
    ring
  have hi (k : ℕ) : Integrable (fun ξ =>
      (2 * θ * X ξ) ^ (2 * (k + 1)) / ((2 * (k + 1)).factorial : ℝ)) P := by
    rw [he]
    exact (hm k).1.const_mul _
  have hb (k : ℕ) : (∫ ξ, (2 * θ * X ξ) ^ (2 * (k + 1)) /
      ((2 * (k + 1)).factorial : ℝ) ∂P) ≤ (192 * B * θ ^ 2) * (16 * θ ^ 2 * s ^ 2) ^ k := by
    rw [he, integral_const_mul]
    have hh := cosh_coefficient_bound (θ := θ) hB k (hm k).2
    convert hh using 1; ring
  have hc := cosh_bound_of_even_coefficients (show 0 ≤ 192 * B * θ ^ 2 by positivity)
    (show 0 ≤ 16 * θ ^ 2 * s ^ 2 by positivity) hr hi hb
  have hg := centered_exp_le_cosh (P := P) hX hM θ
  refine ⟨hg.1, hg.2.2.trans (hc.2.trans ?_)⟩
  nlinarith only [Real.add_one_le_exp (192 * B * θ ^ 2 / (1 - 16 * θ ^ 2 * s ^ 2))]

lemma bounded_centered_mgf_bernstein {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {M B s θ : ℝ}
    (hX : Measurable X) (hM : ∀ ξ, |X ξ| ≤ M) (hB : 0 ≤ B)
    (hs : 0 ≤ s) (hsmall : 256 * |θ| * s < 1)
    (hm : ∀ k : ℕ, Integrable (fun ξ => |X ξ| ^ (2 * (k + 1))) P ∧
      (∫ ξ, |X ξ| ^ (2 * (k + 1)) ∂P) ≤
        12 * 8 ^ (k + 1) * ((k + 1).factorial : ℝ) * B * s ^ (2 * k)) :
    Integrable (fun ξ => Real.exp (θ * (X ξ - ∫ z, X z ∂P))) P ∧
      (∫ ξ, Real.exp (θ * (X ξ - ∫ z, X z ∂P)) ∂P) ≤
        Real.exp (131072 * B * θ ^ 2 / (1 - 256 * |θ| * s)) := by
  have hq : 0 ≤ |θ| * s := mul_nonneg (abs_nonneg _) hs
  have he : (|θ| * s) ^ 2 = θ ^ 2 * s ^ 2 := by rw [mul_pow, sq_abs]
  have hd : 0 < 1 - 256 * |θ| * s := by linarith
  have hc : 1 - 256 * |θ| * s ≤ 1 - 16 * θ ^ 2 * s ^ 2 := by
    nlinarith [sq_nonneg (|θ| * s)]
  have hr : 16 * θ ^ 2 * s ^ 2 < 1 := by linarith
  have h := bounded_centered_mgf_of_even_moments hX hM hB hr hm
  refine ⟨h.1, h.2.trans (Real.exp_le_exp.mpr ?_)⟩
  calc
    192 * B * θ ^ 2 / (1 - 16 * θ ^ 2 * s ^ 2) ≤
        192 * B * θ ^ 2 / (1 - 256 * |θ| * s) :=
      div_le_div_of_nonneg_left (by positivity) hd hc
    _ ≤ 131072 * B * θ ^ 2 / (1 - 256 * |θ| * s) := by
      apply div_le_div_of_nonneg_right _ hd.le
      nlinarith [mul_nonneg hB (sq_nonneg θ)]

end LongTails.Proofs.ScalarMomentConcentration
