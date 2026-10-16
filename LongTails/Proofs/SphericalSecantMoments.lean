import LongTails.Proofs.SphereOddMoments
import LongTails.Proofs.WeightedSphericalMoments
import LongTails.Proofs.WeakGradientConvolution
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory Set Metric
open scoped RealInnerProductSpace Topology

namespace LongTails.Proofs.SphericalSecantMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma secant_odd (f : E → ℝ) (x : E) (γ : ℝ) (u : E) :
    (f (x + γ • (-u)) - f (x - γ • (-u))) / (2 * γ) =
      -((f (x + γ • u) - f (x - γ • u)) / (2 * γ)) := by
  simp only [smul_neg, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

lemma secant_gradient {f : E → ℝ} {g : E → E}
    (hg : ∀ z, HasGradientAt f (g z) z) (x : E) {γ : ℝ} (hγ : γ ≠ 0) (u : E) :
    HasGradientAt (fun v => (f (x + γ • v) - f (x - γ • v)) / (2 * γ))
      ((1 / 2 : ℝ) • (g (x + γ • u) + g (x - γ • u))) u := by
  have hp := OracleTemplate.ZerothOrder.affine_scaled_gradient hg x γ u
  have hn := OracleTemplate.ZerothOrder.affine_scaled_gradient hg x (-γ) u
  have h := (hp.hasFDerivAt.sub hn.hasFDerivAt).const_smul ((2 * γ)⁻¹)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · funext v
    simp only [neg_smul, ← sub_eq_add_neg, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  · ext v
    simp [neg_smul, sub_eq_add_neg]
    field_simp [hγ]

omit [CompleteSpace E] in
lemma average_norm_square_le (a b : E) :
    ‖(1 / 2 : ℝ) • (a + b)‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
    mul_pow, norm_add_sq_real]
  have h := sq_nonneg ‖a - b‖
  rw [norm_sub_sq_real] at h
  nlinarith

omit [CompleteSpace E] in
lemma average_second_moment_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a b : Ω → E} {B : ℝ} (ha : AEStronglyMeasurable a P)
    (hb : AEStronglyMeasurable b P)
    (hai : Integrable (fun ξ => ‖a ξ‖ ^ 2) P)
    (hbi : Integrable (fun ξ => ‖b ξ‖ ^ 2) P)
    (haB : (∫ ξ, ‖a ξ‖ ^ 2 ∂P) ≤ B) (hbB : (∫ ξ, ‖b ξ‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ξ => ‖(1 / 2 : ℝ) • (a ξ + b ξ)‖ ^ 2) P ∧
      (∫ ξ, ‖(1 / 2 : ℝ) • (a ξ + b ξ)‖ ^ 2 ∂P) ≤ B := by
  have hdom : Integrable (fun ξ => (‖a ξ‖ ^ 2 + ‖b ξ‖ ^ 2) / 2) P :=
    (hai.add hbi).div_const 2
  have hi : Integrable (fun ξ => ‖(1 / 2 : ℝ) • (a ξ + b ξ)‖ ^ 2) P := by
    apply hdom.mono' (((ha.add hb).const_smul (1 / 2 : ℝ)).norm.pow 2)
    filter_upwards [] with ξ
    simpa only [Pi.pow_apply, Pi.smul_apply, Pi.add_apply, Real.norm_eq_abs, abs_sq] using average_norm_square_le (a ξ) (b ξ)
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hdom (fun ξ => average_norm_square_le (a ξ) (b ξ))
  rw [integral_div, integral_add hai hbi] at h
  linarith

section Spherical

open OracleTemplate.ZerothOrder LongTails.Proofs.WeakGradientConvolution

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "S" => sphere (0 : H) 1
local notation "Q" => (sphereLaw H : Measure S)

lemma stochastic_odd_sphere_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {a : H → Ω → ℝ} {g : H → Ω → H}
    (ha : Measurable (fun z : S × Ω => a z.1 z.2))
    (hg : Measurable (fun z : S × Ω => g z.1 z.2))
    (hs : ∀ᵐ ξ ∂P, Continuous (fun x => g x ξ) ∧
      (∀ x, HasGradientAt (fun y => a y ξ) (g x ξ) x) ∧
      (∀ x, a (-x) ξ = -a x ξ))
    {B : ℝ} (hi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖g u ξ‖ ^ 2) P)
    (hb : ∀ᵐ u : S ∂Q, (∫ ξ, ‖g u ξ‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) :
    Integrable (fun z : S × Ω => a z.1 z.2 ^ 2) ((Q).prod P) ∧
      (∫ z : S × Ω, a z.1 z.2 ^ 2 ∂(Q).prod P) ≤ Real.pi ^ 2 / (4 * ((d : ℝ) - 1)) * B := by
  have hd : 1 < d := by
    have hcard : 1 < Fintype.card (Fin d) := Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩
    simpa using hcard
  have hdR : 0 < (d : ℝ) - 1 := by
    have h : (1 : ℝ) < d := by exact_mod_cast hd
    linarith
  let C := Real.pi ^ 2 / (4 * ((d : ℝ) - 1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hG := nonnegative_fiber_integral_bound (hg.norm.pow_const 2).stronglyMeasurable
    (fun z => sq_nonneg _) hi (integrable_const B) hb
  have hGb : (∫ z : S × Ω, ‖g z.1 z.2‖ ^ 2 ∂(Q).prod P) ≤ B := by
    simpa using hG.2
  have hAi : ∀ᵐ ξ ∂P, Integrable (fun u : S => a u ξ ^ 2) Q := by
    filter_upwards [hs] with ξ hξ
    have hc : Continuous (fun x => a x ξ) := continuous_iff_continuousAt.mpr
      (fun x => (hξ.2.1 x).hasFDerivAt.continuousAt)
    exact ((hc.comp continuous_subtype_val).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAb : ∀ᵐ ξ ∂P, (∫ u : S, a u ξ ^ 2 ∂Q) ≤ C * (∫ u : S, ‖g u ξ‖ ^ 2 ∂Q) := by
    filter_upwards [hs] with ξ hξ
    have h := SphereOddMoments.odd_sphere_second_moment hξ.1 hξ.2.1 hξ.2.2 i j hij
    have hh : (∫ u : S, a u ξ ^ 2 ∂Q) ≤
        (Real.pi ^ 2 / 4 * (∫ u : S, ‖g u ξ‖ ^ 2 ∂Q)) / ((d : ℝ) - 1) :=
      (le_div_iff₀ hdR).mpr (by nlinarith only [h])
    convert hh using 1
    dsimp [C]
    field_simp
  have hA := nonnegative_fiber_integral_bound ((ha.pow_const 2).stronglyMeasurable.comp_measurable
      measurable_swap) (fun z => sq_nonneg (a z.2 z.1)) hAi
      (hG.1.integral_prod_right.const_mul C) hAb
  refine ⟨integrable_swap_iff.mp hA.1, ?_⟩
  have he : (∫ z : Ω × S, a z.2 z.1 ^ 2 ∂P.prod Q) =
      ∫ z : S × Ω, a z.1 z.2 ^ 2 ∂(Q).prod P :=
        integral_prod_swap (μ := Q) (ν := P) (fun z : S × Ω => a z.1 z.2 ^ 2)
  have hAA := hA.2
  change (∫ z : Ω × S, a z.2 z.1 ^ 2 ∂P.prod Q) ≤
    ∫ ξ, C * (∫ u : S, ‖g u ξ‖ ^ 2 ∂Q) ∂P at hAA
  rw [he, integral_const_mul, ← integral_prod_symm _ hG.1] at hAA
  exact hAA.trans (mul_le_mul_of_nonneg_left hGb hC)

lemma sphere_weighted_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : S × Ω → ℝ} (hf : Integrable f ((Q).prod P)) (i : Fin d) (k : ℕ) :
    Integrable (fun z : S × Ω => f z * (z.1 : H) i ^ k) ((Q).prod P) := by
  apply hf.mul_bdd (((sphere_coordinate_measurable i).comp measurable_fst).pow_const k).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_pow]
  simpa only [one_pow, Function.comp_def] using pow_le_pow_left₀ (abs_nonneg _) (sphere_coordinate_abs z.1 i) k

lemma weighted_gradient_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {g : H → Ω → H}
    (hg : Measurable (fun z : S × Ω => g z.1 z.2)) {B : ℝ}
    (hi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖g u ξ‖ ^ 2) P)
    (hb : ∀ᵐ u : S ∂Q, (∫ ξ, ‖g u ξ‖ ^ 2 ∂P) ≤ B) (i : Fin d) (k : ℕ) :
    Integrable (fun z : S × Ω => (z.1 : H) i ^ (2 * k) * ‖g z.1 z.2‖ ^ 2) ((Q).prod P) ∧
      (∫ z : S × Ω, (z.1 : H) i ^ (2 * k) * ‖g z.1 z.2‖ ^ 2 ∂(Q).prod P) ≤
        B * (∫ u : S, (u : H) i ^ (2 * k) ∂Q) := by
  have hw (u : S) : 0 ≤ (u : H) i ^ (2 * k) := by
    rw [mul_comm 2 k, pow_mul]
    exact sq_nonneg _
  have hm : Measurable (fun z : S × Ω => (z.1 : H) i ^ (2 * k) * ‖g z.1 z.2‖ ^ 2) :=
    (((sphere_coordinate_measurable i).comp measurable_fst).pow_const _).mul (hg.norm.pow_const 2)
  have hfi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => (u : H) i ^ (2 * k) * ‖g u ξ‖ ^ 2) P := by
    filter_upwards [hi] with u hu
    exact hu.const_mul _
  have hfb : ∀ᵐ u : S ∂Q, (∫ ξ, (u : H) i ^ (2 * k) * ‖g u ξ‖ ^ 2 ∂P) ≤
      B * (u : H) i ^ (2 * k) := by
    filter_upwards [hb] with u hu
    rw [integral_const_mul, mul_comm B]
    exact mul_le_mul_of_nonneg_left hu (hw u)
  have h := nonnegative_fiber_integral_bound hm.stronglyMeasurable
    (fun z => mul_nonneg (hw z.1) (sq_nonneg _)) hfi
    ((sphere_coordinate_power_integrable i (2 * k)).const_mul B) hfb
  simpa only [integral_const_mul] using h

lemma stochastic_weighted_square_recurrence {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {a : H → Ω → ℝ} {g : H → Ω → H}
    (hg : Measurable (fun z : S × Ω => g z.1 z.2))
    (hA : Integrable (fun z : S × Ω => a z.1 z.2 ^ 2) ((Q).prod P))
    (hs : ∀ᵐ ξ ∂P, Continuous (fun x => g x ξ) ∧
      (∀ x, HasGradientAt (fun y => a y ξ) (g x ξ) x))
    {B : ℝ} (hi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖g u ξ‖ ^ 2) P)
    (hb : ∀ᵐ u : S ∂Q, (∫ ξ, ‖g u ξ‖ ^ 2 ∂P) ≤ B)
    (i : Fin d) (k : ℕ) :
    ((d : ℝ) + 2 * k) ^ 2 *
        (∫ z : S × Ω, a z.1 z.2 ^ 2 * (z.1 : H) i ^ (2 * k + 2) ∂(Q).prod P) ≤
      2 * ((d : ℝ) + 2 * k) * (2 * (k : ℝ) + 1) *
        (∫ z : S × Ω, a z.1 z.2 ^ 2 * (z.1 : H) i ^ (2 * k) ∂(Q).prod P) +
      4 * B * (∫ u : S, (u : H) i ^ (2 * k) ∂Q) := by
  let T := fun z : S × Ω => (z.1 : H) i ^ (2 * k) *
    ((g z.1 z.2) i - (z.1 : H) i * ⟪g z.1 z.2, (z.1 : H)⟫) ^ 2
  have hw (u : S) : 0 ≤ (u : H) i ^ (2 * k) := by
    rw [mul_comm 2 k, pow_mul]
    exact sq_nonneg _
  have hG := weighted_gradient_moment hg hi hb i k
  have hTm : Measurable T := by
    have hu : Measurable (fun z : S × Ω => (z.1 : H)) :=
      continuous_subtype_val.measurable.comp measurable_fst
    have hc : Measurable (fun z : S × Ω => (z.1 : H) i) :=
      (sphere_coordinate_measurable i).comp measurable_fst
    have hgc := (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg
    exact (hc.pow_const (2 * k)).mul ((hgc.sub (hc.mul (continuous_inner.measurable.comp (hg.prodMk hu)))).pow_const 2)
  have hTbound (z : S × Ω) : T z ≤ (z.1 : H) i ^ (2 * k) * ‖g z.1 z.2‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (WeightedSphericalMoments.tangent_coordinate_square_le
      z.1 (g z.1 z.2) i) (hw z.1)
  have hTi : Integrable T ((Q).prod P) := by
    apply hG.1.mono' hTm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw z.1) (sq_nonneg _))]
    exact hTbound z
  have hTb : (∫ z, T z ∂(Q).prod P) ≤ B * (∫ u : S, (u : H) i ^ (2 * k) ∂Q) :=
    (integral_mono hTi hG.1 hTbound).trans hG.2
  have h0 := sphere_weighted_integrable hA i (2 * k)
  have h1 := sphere_weighted_integrable hA i (2 * k + 2)
  have hr : ∀ᵐ ξ ∂P,
      ((d : ℝ) + 2 * k) ^ 2 * (∫ u : S, a u ξ ^ 2 * (u : H) i ^ (2 * k + 2) ∂Q) ≤
      2 * ((d : ℝ) + 2 * k) * (2 * (k : ℝ) + 1) *
        (∫ u : S, a u ξ ^ 2 * (u : H) i ^ (2 * k) ∂Q) + 4 * (∫ u : S, T (u, ξ) ∂Q) := by
    filter_upwards [hs] with ξ hξ
    have hc : Continuous (fun x => a x ξ) := continuous_iff_continuousAt.mpr
      (fun x => (hξ.2 x).hasFDerivAt.continuousAt)
    exact WeightedSphericalMoments.sphere_weighted_square_recurrence hc hξ.1 hξ.2 i k
  have h := integral_mono_ae (h1.integral_prod_right.const_mul (((d : ℝ) + 2 * k) ^ 2))
    ((h0.integral_prod_right.const_mul (2 * ((d : ℝ) + 2 * k) * (2 * (k : ℝ) + 1))).add
      (hTi.integral_prod_right.const_mul 4)) hr
  simp only [Pi.add_apply] at h
  rw [integral_add (h0.integral_prod_right.const_mul _) (hTi.integral_prod_right.const_mul 4),
    integral_const_mul, integral_const_mul, integral_const_mul,
    ← integral_prod_symm _ h1, ← integral_prod_symm _ h0, ← integral_prod_symm _ hTi] at h
  nlinarith only [h, hTb]

lemma stochastic_weighted_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {a : H → Ω → ℝ} {g : H → Ω → H}
    (ha : Measurable (fun z : S × Ω => a z.1 z.2))
    (hg : Measurable (fun z : S × Ω => g z.1 z.2))
    (hs : ∀ᵐ ξ ∂P, Continuous (fun x => g x ξ) ∧
      (∀ x, HasGradientAt (fun y => a y ξ) (g x ξ) x) ∧
      (∀ x, a (-x) ξ = -a x ξ))
    {B : ℝ} (hB : 0 ≤ B)
    (hi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖g u ξ‖ ^ 2) P)
    (hb : ∀ᵐ u : S ∂Q, (∫ ξ, ‖g u ξ‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (k : ℕ) :
    Integrable (fun z : S × Ω => a z.1 z.2 ^ 2 * (z.1 : H) i ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) *
        (∫ z : S × Ω, a z.1 z.2 ^ 2 * (z.1 : H) i ^ (2 * k) ∂(Q).prod P) ≤
          5 * 8 ^ k * (k.factorial : ℝ) * B := by
  have hA := stochastic_odd_sphere_second_moment ha hg hs hi hb i j hij
  refine ⟨sphere_weighted_integrable hA.1 i (2 * k), ?_⟩
  have hd : 1 < d := by
    simpa using (Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩ : 1 < Fintype.card (Fin d))
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hp : Real.pi ^ 2 ≤ 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hc : (d : ℝ) * (Real.pi ^ 2 / (4 * ((d : ℝ) - 1))) ≤ 5 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < 4 * ((d : ℝ) - 1))).mpr
    nlinarith [mul_le_mul_of_nonneg_right hp hd0.le]
  let X := fun n => ∫ z : S × Ω, a z.1 z.2 ^ 2 * (z.1 : H) i ^ (2 * n) ∂(Q).prod P
  let m := fun n => ∫ u : S, (u : H) i ^ (2 * n) ∂Q
  have hw (u : S) (n : ℕ) : 0 ≤ (u : H) i ^ (2 * n) := by
    rw [mul_comm 2 n, pow_mul]
    exact sq_nonneg _
  have hX (n : ℕ) : 0 ≤ X n := integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (hw z.1 n))
  have hm (n : ℕ) : 0 ≤ m n := integral_nonneg (fun u => hw u n)
  have h0 : (d : ℝ) * X 0 ≤ 5 * B := by
    have h1 := mul_le_mul_of_nonneg_left hA.2 hd0.le
    have h2 := mul_le_mul_of_nonneg_right hc hB
    simpa [X, mul_assoc] using h1.trans (by simpa [mul_assoc] using h2)
  have hr (n : ℕ) : (d : ℝ) ^ 2 * X (n + 1) ≤
      2 * (d : ℝ) * (2 * (n : ℝ) + 1) * X n + 4 * B * m n := by
    have hsn : ∀ᵐ ξ ∂P, Continuous (fun x => g x ξ) ∧
        ∀ x, HasGradientAt (fun y => a y ξ) (g x ξ) x := hs.mono (fun _ h => ⟨h.1, h.2.1⟩)
    have h := stochastic_weighted_square_recurrence hg hA.1 hsn hi hb i n
    have hn : 2 * (n + 1) = 2 * n + 2 := by omega
    have he : ((d : ℝ) + 2 * n) ^ 2 * X (n + 1) ≤
        2 * ((d : ℝ) + 2 * n) * (2 * (n : ℝ) + 1) * X n + 4 * (B * m n) := by
      simpa only [X, m, hn, mul_assoc] using h
    have hh := WeightedSphericalMoments.relax_weighted_recurrence hd0
      (show (d : ℝ) ≤ d + 2 * n by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity) (hX n) (mul_nonneg hB (hm n)) he
    simpa only [mul_assoc] using hh
  exact WeightedSphericalMoments.weighted_sequence_moment_bound hd0.le hB h0
    (fun n => WeightedSphericalMoments.sphere_even_moment_bound i n) hr k

lemma weighted_moment_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a : ℕ → S × Ω → ℝ} {b : S × Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (i : Fin d) (k : ℕ)
    (hi : ∀ n, Integrable (fun z : S × Ω => a n z ^ 2 * (z.1 : H) i ^ (2 * k)) ((Q).prod P))
    (hb : ∀ n, (d : ℝ) ^ (k + 1) *
      (∫ z : S × Ω, a n z ^ 2 * (z.1 : H) i ^ (2 * k) ∂(Q).prod P) ≤ B)
    (ht : ∀ᵐ z ∂(Q).prod P, Filter.Tendsto (fun n => a n z) Filter.atTop (𝓝 (b z))) :
    Integrable (fun z : S × Ω => b z ^ 2 * (z.1 : H) i ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) *
        (∫ z : S × Ω, b z ^ 2 * (z.1 : H) i ^ (2 * k) ∂(Q).prod P) ≤ B := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hd : 0 < (d : ℝ) ^ (k + 1) := pow_pos hd0 _
  have hn : ∀ n, 0 ≤ᵐ[(Q).prod P] (fun z : S × Ω => a n z ^ 2 * (z.1 : H) i ^ (2 * k)) := by
    intro n
    filter_upwards [] with z
    apply mul_nonneg (sq_nonneg _)
    rw [mul_comm 2 k, pow_mul]
    exact sq_nonneg _
  have hc : ∀ᵐ z ∂(Q).prod P,
      Filter.Tendsto (fun n => a n z ^ 2 * (z.1 : H) i ^ (2 * k)) Filter.atTop
        (𝓝 (b z ^ 2 * (z.1 : H) i ^ (2 * k))) := by
    filter_upwards [ht] with z hz
    exact (hz.pow 2).mul_const _
  have h := nonnegative_limit_integral_bound (div_nonneg hB hd.le) hi hn
    (fun n => (le_div_iff₀ hd).mpr (by nlinarith only [hb n])) hc
  refine ⟨h.1, ?_⟩
  have hh := (le_div_iff₀ hd).mp h.2
  nlinarith only [hh]

lemma smooth_secant_fields {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : H × Ω → ℝ} {G : H × Ω → H}
    (hF : Measurable F) (hG : Measurable G)
    (hs : ∀ᵐ ξ ∂P, Continuous (fun y => G (y, ξ)) ∧
      ∀ y, HasGradientAt (fun z => F (z, ξ)) (G (y, ξ)) y)
    (x : H) {γ B : ℝ} (hγ : γ ≠ 0)
    (hi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖G (x + γ • (u : H), ξ)‖ ^ 2) P ∧
      Integrable (fun ξ => ‖G (x - γ • (u : H), ξ)‖ ^ 2) P)
    (hb : ∀ᵐ u : S ∂Q, (∫ ξ, ‖G (x + γ • (u : H), ξ)‖ ^ 2 ∂P) ≤ B ∧
      (∫ ξ, ‖G (x - γ • (u : H), ξ)‖ ^ 2 ∂P) ≤ B) :
    let a := fun u : H => fun ξ => (F (x + γ • u, ξ) - F (x - γ • u, ξ)) / (2 * γ)
    let g := fun u : H => fun ξ => (1 / 2 : ℝ) • (G (x + γ • u, ξ) + G (x - γ • u, ξ))
    Measurable (fun z : S × Ω => a z.1 z.2) ∧ Measurable (fun z : S × Ω => g z.1 z.2) ∧
      (∀ᵐ ξ ∂P, Continuous (fun u => g u ξ) ∧
        (∀ u, HasGradientAt (fun v => a v ξ) (g u ξ) u) ∧ (∀ u, a (-u) ξ = -a u ξ)) ∧
      (∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖g u ξ‖ ^ 2) P) ∧
      (∀ᵐ u : S ∂Q, (∫ ξ, ‖g u ξ‖ ^ 2 ∂P) ≤ B) := by
  let a := fun u : H => fun ξ => (F (x + γ • u, ξ) - F (x - γ • u, ξ)) / (2 * γ)
  let g := fun u : H => fun ξ => (1 / 2 : ℝ) • (G (x + γ • u, ξ) + G (x - γ • u, ξ))
  have hup : Measurable (fun z : S × Ω => (x + γ • (z.1 : H), z.2)) := by fun_prop
  have hum : Measurable (fun z : S × Ω => (x - γ • (z.1 : H), z.2)) := by fun_prop
  have ha : Measurable (fun z : S × Ω => a z.1 z.2) :=
    ((hF.comp hup).sub (hF.comp hum)).div_const _
  have hg : Measurable (fun z : S × Ω => g z.1 z.2) :=
    ((hG.comp hup).add (hG.comp hum)).const_smul (1 / 2 : ℝ)
  have hsg : ∀ᵐ ξ ∂P, Continuous (fun u => g u ξ) ∧
      (∀ u, HasGradientAt (fun v => a v ξ) (g u ξ) u) ∧
      (∀ u, a (-u) ξ = -a u ξ) := by
    filter_upwards [hs] with ξ hξ
    refine ⟨?_, ?_, ?_⟩
    · dsimp [g]
      have hp : Continuous (fun u : H => x + γ • u) := by fun_prop
      have hm : Continuous (fun u : H => x - γ • u) := by fun_prop
      exact ((hξ.1.comp hp).add (hξ.1.comp hm)).const_smul (1 / 2 : ℝ)
    · exact fun u => secant_gradient hξ.2 x hγ u
    · exact fun u => secant_odd (fun z => F (z, ξ)) x γ u
  have hm : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖g u ξ‖ ^ 2) P ∧
      (∫ ξ, ‖g u ξ‖ ^ 2 ∂P) ≤ B := by
    filter_upwards [hi, hb] with u hu hv
    exact average_second_moment_bound
      (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable hu.1 hu.2 hv.1 hv.2
  exact ⟨ha, hg, hsg, hm.mono (fun _ h => h.1), hm.mono (fun _ h => h.2)⟩

lemma smooth_secant_weighted_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : H × Ω → ℝ} {G : H × Ω → H}
    (hF : Measurable F) (hG : Measurable G)
    (hs : ∀ᵐ ξ ∂P, Continuous (fun y => G (y, ξ)) ∧
      ∀ y, HasGradientAt (fun z => F (z, ξ)) (G (y, ξ)) y)
    (x : H) {γ B : ℝ} (hγ : γ ≠ 0) (hB : 0 ≤ B)
    (hi : ∀ᵐ u : S ∂Q, Integrable (fun ξ => ‖G (x + γ • (u : H), ξ)‖ ^ 2) P ∧
      Integrable (fun ξ => ‖G (x - γ • (u : H), ξ)‖ ^ 2) P)
    (hb : ∀ᵐ u : S ∂Q, (∫ ξ, ‖G (x + γ • (u : H), ξ)‖ ^ 2 ∂P) ≤ B ∧
      (∫ ξ, ‖G (x - γ • (u : H), ξ)‖ ^ 2 ∂P) ≤ B)
    (i j : Fin d) (hij : i ≠ j) (k : ℕ) :
    Integrable (fun z : S × Ω =>
      ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
        (z.1 : H) i ^ (2 * k)) ((Q).prod P) ∧
      (d : ℝ) ^ (k + 1) * (∫ z : S × Ω,
        ((F (x + γ • (z.1 : H), z.2) - F (x - γ • (z.1 : H), z.2)) / (2 * γ)) ^ 2 *
          (z.1 : H) i ^ (2 * k) ∂(Q).prod P) ≤ 5 * 8 ^ k * (k.factorial : ℝ) * B := by
  have h := smooth_secant_fields hF hG hs x hγ hi hb
  exact stochastic_weighted_moment_bound h.1 h.2.1 h.2.2.1 hB h.2.2.2.1 h.2.2.2.2 i j hij k

end Spherical

end LongTails.Proofs.SphericalSecantMoments
