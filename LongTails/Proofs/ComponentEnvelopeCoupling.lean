import LongTails.Proofs.ComponentEnvelopeProx
import LongTails.Proofs.ExtragradientStep
import LongTails.Proofs.AcceleratedVariance
open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators
namespace OracleTemplate.ComponentEnvelope
open LongTails.Proofs.RecursiveEnvelopeGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma projection_nonexpansive {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) (x y : E) :
    ‖SaddlePoint.project C x - SaddlePoint.project C y‖ ≤ ‖x - y‖ := by
  let p := SaddlePoint.project C x
  let q := SaddlePoint.project C y
  have hp := SaddlePoint.project_spec hne hco hcv x
  have hq := SaddlePoint.project_spec hne hco hcv y
  have h1 := hp.2 q hq.1
  have h2 := hq.2 p hp.1
  change ⟪x - p, q - p⟫ ≤ 0 at h1
  change ⟪y - q, p - q⟫ ≤ 0 at h2
  rw [show q - p = -(p - q) by module, inner_neg_right] at h1
  have hid : ⟪x - y, p - q⟫ - ‖p - q‖ ^ 2 =
      ⟪x - p, p - q⟫ - ⟪y - q, p - q⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left]
    ring
  have hsq : ‖p - q‖ ^ 2 ≤ ‖x - y‖ * ‖p - q‖ := by
    nlinarith [real_inner_le_norm (x - y) (p - q)]
  change ‖p - q‖ ≤ ‖x - y‖
  nlinarith [norm_nonneg (p - q), norm_nonneg (x - y)]

lemma projected_quadratic_minimum {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {μ : ℝ} (hμ : 0 < μ) (x v t : E) (ht : t ∈ C) :
    let y := SaddlePoint.project C (x - (1 / (6 * μ)) • v)
    ⟪v, x - t⟫ - 3 * μ * ‖x - t‖ ^ 2 ≤
      ⟪v, x - y⟫ - 3 * μ * ‖x - y‖ ^ 2 := by
  dsimp only
  let y := SaddlePoint.project C (x - (1 / (6 * μ)) • v)
  have hp := SaddlePoint.project_inequality hne hco hcv (1 / (6 * μ)) x v t ht
  change 2 * (1 / (6 * μ)) * ⟪v, y - t⟫ ≤
    ‖x - t‖ ^ 2 - ‖y - t‖ ^ 2 - ‖x - y‖ ^ 2 at hp
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 3 * μ by positivity)
  have hid : 3 * μ * (2 * (1 / (6 * μ)) * ⟪v, y - t⟫) = ⟪v, y - t⟫ := by field_simp; ring
  rw [hid] at hm
  have hi : ⟪v, x - t⟫ - ⟪v, x - y⟫ = ⟪v, y - t⟫ := by
    simp only [inner_sub_right]
    ring
  change ⟪v, x - t⟫ - 3 * μ * ‖x - t‖ ^ 2 ≤ ⟪v, x - y⟫ - 3 * μ * ‖x - y‖ ^ 2
  nlinarith [mul_nonneg hμ.le (sq_nonneg ‖y - t‖)]

lemma model_projected_progress {f : E → ℝ} {g : E → E} {μ : ℝ}
    (hm : Model μ f g) (x y v : E) :
    f y ≤ f x - (⟪v, x - y⟫ - 3 * μ * ‖x - y‖ ^ 2) +
      ‖v - g x‖ ^ 2 / (4 * μ) := by
  have hu := hm.upper x y
  rw [norm_sub_rev y x] at hu
  have hi : ⟪g x, y - x⟫ = -⟪v, x - y⟫ + ⟪v - g x, x - y⟫ := by
    rw [show y - x = -(x - y) by module, inner_neg_right, inner_sub_left]
    ring
  rw [hi] at hu
  have hc := real_inner_le_norm (v - g x) (x - y)
  have hμ := hm.pos
  have hs := sq_nonneg (‖v - g x‖ - 2 * μ * ‖x - y‖)
  have hdiv : 4 * μ * (‖v - g x‖ ^ 2 / (4 * μ)) = ‖v - g x‖ ^ 2 := by field_simp
  have h1 := mul_le_mul_of_nonneg_left hu (show 0 ≤ 4 * μ by positivity)
  have h2 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4 * μ by positivity)
  have h3 : 0 ≤ μ ^ 2 * ‖x - y‖ ^ 2 := by positivity
  nlinarith


lemma projected_mirror_coupling {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {μ τ : ℝ} (hμ : 0 < μ) (hτ : 0 < τ)
    (x z v u : E) (hu : u ∈ C)
    (ht : x + τ • (SaddlePoint.project C (z - (1 / (6 * μ * τ)) • v) - z) ∈ C) :
    let y := SaddlePoint.project C (x - (1 / (6 * μ)) • v)
    let zn := SaddlePoint.project C (z - (1 / (6 * μ * τ)) • v)
    τ * ⟪v, z - u⟫ ≤ ⟪v, x - y⟫ - 3 * μ * ‖x - y‖ ^ 2 +
      3 * μ * τ ^ 2 * (‖z - u‖ ^ 2 - ‖zn - u‖ ^ 2) := by
  dsimp only
  let y := SaddlePoint.project C (x - (1 / (6 * μ)) • v)
  let zn := SaddlePoint.project C (z - (1 / (6 * μ * τ)) • v)
  let t := x + τ • (zn - z)
  have hp := projected_quadratic_minimum hne hco hcv hμ x v t ht
  have hid : x - t = τ • (z - zn) := by dsimp [t]; module
  rw [hid, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, mul_pow] at hp
  have hm := SaddlePoint.project_inequality hne hco hcv (1 / (6 * μ * τ)) z v u hu
  have hscaled := mul_le_mul_of_nonneg_left hm (show 0 ≤ 3 * μ * τ ^ 2 by positivity)
  change 3 * μ * τ ^ 2 * (2 * (1 / (6 * μ * τ)) * ⟪v, zn - u⟫) ≤
    3 * μ * τ ^ 2 * (‖z - u‖ ^ 2 - ‖zn - u‖ ^ 2 - ‖z - zn‖ ^ 2) at hscaled
  have hs : 3 * μ * τ ^ 2 * (2 * (1 / (6 * μ * τ)) * ⟪v, zn - u⟫) =
      τ * ⟪v, zn - u⟫ := by field_simp; ring
  rw [hs] at hscaled
  have hi : ⟪v, z - u⟫ = ⟪v, z - zn⟫ + ⟪v, zn - u⟫ := by
    simp only [inner_sub_right]
    ring
  change τ * ⟪v, z - u⟫ ≤ ⟪v, x - y⟫ - 3 * μ * ‖x - y‖ ^ 2 +
    3 * μ * τ ^ 2 * (‖z - u‖ ^ 2 - ‖zn - u‖ ^ 2)
  change τ * ⟪v, z - zn⟫ - 3 * μ * (τ ^ 2 * ‖z - zn‖ ^ 2) ≤
    ⟪v, x - y⟫ - 3 * μ * ‖x - y‖ ^ 2 at hp
  nlinarith


lemma model_query_mixing {f : E → ℝ} {g : E → E} {μ τ : ℝ}
    (hm : Model μ f g) (hτ : 0 ≤ τ) (hτu : τ ≤ 1 / 2)
    (y z w u : E) :
    let x := τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y
    f x - f u ≤ (1 / 2 - τ) * (f y - f u) + (1 / 2 : ℝ) * (f w - f u) +
      τ * ⟪g x, z - u⟫ - (1 / 2 : ℝ) * (f w - f x - ⟪g x, w - x⟫) := by
  dsimp only
  let x := τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y
  have hu := mul_le_mul_of_nonneg_left (hm.lower x u) hτ
  have hy := mul_le_mul_of_nonneg_left (hm.lower x y) (show 0 ≤ 1 / 2 - τ by linarith)
  have hid : τ • (z - u) + (1 / 2 : ℝ) • (w - x) + (1 / 2 - τ) • (y - x) =
      τ • (x - u) := by
    dsimp [x]
    module
  have hi := congrArg (fun v => ⟪g x, v⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hiu : ⟪g x, u - x⟫ = -⟪g x, x - u⟫ := by
    rw [show u - x = -(x - u) by module, inner_neg_right]
  rw [hiu] at hu
  change f x - f u ≤ _
  nlinarith


lemma query_mixture_mem {C : Set E} (hcv : Convex ℝ C) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτu : τ ≤ 1 / 2) {y z w : E}
    (hy : y ∈ C) (hz : z ∈ C) (hw : w ∈ C) :
    τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y ∈ C := by
  have hm := hcv hz hy (show 0 ≤ 2 * τ by positivity)
    (show 0 ≤ 1 - 2 * τ by linarith) (show 2 * τ + (1 - 2 * τ) = 1 by ring)
  have hh := hcv hm hw (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  convert hh using 1
  module

lemma projected_accelerated_pointwise {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {f : E → ℝ} {g : E → E} {μ τ : ℝ}
    (hm : Model μ f g) (hτ : 0 < τ) (hτu : τ ≤ 1 / 2)
    (y z w u v : E) (hy : y ∈ C) (hw : w ∈ C) (hu : u ∈ C) :
    let x := τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y
    let yn := SaddlePoint.project C (x - (1 / (6 * μ)) • v)
    let zn := SaddlePoint.project C (z - (1 / (6 * μ * τ)) • v)
    f yn - f u + 3 * μ * τ ^ 2 * ‖zn - u‖ ^ 2 ≤
      (1 / 2 - τ) * (f y - f u) + (1 / 2 : ℝ) * (f w - f u) +
      3 * μ * τ ^ 2 * ‖z - u‖ ^ 2 + ‖v - g x‖ ^ 2 / (4 * μ) -
      τ * ⟪v - g x, z - u⟫ - (1 / 2 : ℝ) * (f w - f x - ⟪g x, w - x⟫) := by
  dsimp only
  let x := τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y
  let yn := SaddlePoint.project C (x - (1 / (6 * μ)) • v)
  let zn := SaddlePoint.project C (z - (1 / (6 * μ * τ)) • v)
  have hzn : zn ∈ C := (SaddlePoint.project_spec hne hco hcv _).1
  have ht : x + τ • (zn - z) ∈ C := by
    have hh := query_mixture_mem hcv hτ.le hτu hy hzn hw
    convert hh using 1
    dsimp [x]
    module
  have hprogress := model_projected_progress hm x yn v
  have hmirror := projected_mirror_coupling hne hco hcv hm.pos hτ x z v u hu ht
  have hmix := model_query_mixing hm hτ.le hτu y z w u
  change f x - f u ≤ _ at hmix
  change τ * ⟪v, z - u⟫ ≤ ⟪v, x - yn⟫ - 3 * μ * ‖x - yn‖ ^ 2 +
    3 * μ * τ ^ 2 * (‖z - u‖ ^ 2 - ‖zn - u‖ ^ 2) at hmirror
  change f yn - f u + 3 * μ * τ ^ 2 * ‖zn - u‖ ^ 2 ≤ _
  simp only [inner_sub_left]
  nlinarith

open OracleTemplate.FiniteSum
open LongTails.Setups.FiniteSumSmoothAndConvex
variable {n : ℕ} [NeZero n]

lemma finiteSum_model {f : Fin n → E → ℝ} {g : Fin n × E → E} {μ : ℝ}
    (hm : ∀ i, Model μ (f i) (fun x => g (i, x))) :
    Model μ (objective f) (fullGradient g) := by
  refine ⟨(hm 0).pos, ?_, ?_⟩
  · intro x y
    have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ => (hm i).lower x y)
    simpa only [Finset.expect_add_distrib, expect_inner_left, ← objective_eq_expect,
      fullGradient] using h
  · intro x y
    have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ => (hm i).upper x y)
    simpa only [Finset.expect_add_distrib, expect_inner_left, ← objective_eq_expect,
      Fintype.expect_const, fullGradient] using h

lemma model_estimator_variance {f : Fin n → E → ℝ} {g : Fin n × E → E} {μ : ℝ}
    (hm : ∀ i, Model μ (f i) (fun x => g (i, x))) (w x : E) :
    (𝔼 i, ‖estimator g w x i - fullGradient g x‖ ^ 2) ≤
      2 * μ * (objective f w - objective f x - ⟪fullGradient g x, w - x⟫) := by
  let v := fun i => g (i, x) - g (i, w)
  have hv : ∀ i, estimator g w x i - fullGradient g x =
      v i - (n : ℝ)⁻¹ • ∑ j, v j := by
    intro i
    simp only [v, Finset.sum_sub_distrib, smul_sub, estimator, fullGradient]
    module
  simp only [hv]
  apply (centered_second_moment v).trans
  have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ => (hm i).bregman w x)
  simpa only [v, norm_sub_rev (g (_, w)), ← Finset.mul_expect,
    Finset.expect_sub_distrib, expect_inner_left, ← objective_eq_expect, fullGradient] using h

lemma projected_accelerated_average {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {f : Fin n → E → ℝ} {g : Fin n × E → E} {μ τ : ℝ}
    (hm : ∀ i, Model μ (f i) (fun x => g (i, x))) (hτ : 0 < τ) (hτu : τ ≤ 1 / 2)
    (y z w u : E) (hy : y ∈ C) (hw : w ∈ C) (hu : u ∈ C) :
    let x := τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y
    let yn := fun i => SaddlePoint.project C (x - (1 / (6 * μ)) • estimator g w x i)
    let zn := fun i => SaddlePoint.project C (z - (1 / (6 * μ * τ)) • estimator g w x i)
    (𝔼 i, (objective f (yn i) - objective f u + 3 * μ * τ ^ 2 * ‖zn i - u‖ ^ 2)) ≤
      (1 / 2 - τ) * (objective f y - objective f u) +
      (1 / 2 : ℝ) * (objective f w - objective f u) + 3 * μ * τ ^ 2 * ‖z - u‖ ^ 2 := by
  dsimp only
  let x := τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y
  let e := estimator g w x
  let v := fullGradient g x
  have hp (i : Fin n) := projected_accelerated_pointwise hne hco hcv
    (finiteSum_model hm) hτ hτu y z w u (e i) hy hw hu
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun i _ => hp i)
  have hmean : (n : ℝ)⁻¹ • ∑ i, (e i - v) = 0 := by
    simp only [Finset.sum_sub_distrib, smul_sub]
    rw [show (n : ℝ)⁻¹ • ∑ i, e i = v from estimator_unbiased g w x]
    simp [v, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, NeZero.ne n]
  change (𝔼 i, (objective f (SaddlePoint.project C (x - (1 / (6 * μ)) • e i)) - objective f u +
    3 * μ * τ ^ 2 * ‖SaddlePoint.project C (z - (1 / (6 * μ * τ)) • e i) - u‖ ^ 2)) ≤
    (𝔼 i, ((1 / 2 - τ) * (objective f y - objective f u) +
      (1 / 2 : ℝ) * (objective f w - objective f u) + 3 * μ * τ ^ 2 * ‖z - u‖ ^ 2 +
      ‖e i - v‖ ^ 2 / (4 * μ) - τ * ⟪e i - v, z - u⟫ -
      (1 / 2 : ℝ) * (objective f w - objective f x - ⟪v, w - x⟫))) at hav
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    ← Finset.expect_div, Fintype.expect_const, expect_inner_left, hmean,
    inner_zero_left, mul_zero, sub_zero] at hav
  have hvar := model_estimator_variance hm w x
  have hμ := (hm 0).pos
  have hv := div_le_div_of_nonneg_right hvar (show 0 ≤ 4 * μ by positivity)
  have hid : (2 * μ * (objective f w - objective f x - ⟪v, w - x⟫)) / (4 * μ) =
      (1 / 2 : ℝ) * (objective f w - objective f x - ⟪v, w - x⟫) := by field_simp; ring
  change (𝔼 i, ‖e i - v‖ ^ 2) / (4 * μ) ≤ _ at hv
  rw [hid] at hv
  change (𝔼 i, (objective f (SaddlePoint.project C (x - (1 / (6 * μ)) • e i)) - objective f u +
    3 * μ * τ ^ 2 * ‖SaddlePoint.project C (z - (1 / (6 * μ * τ)) • e i) - u‖ ^ 2)) ≤ _
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    Fintype.expect_const]
  linarith



omit [InnerProductSpace ℝ E] in
lemma squared_distance_perturbation {a b u : E} {R : ℝ}
    (ha : ‖a - u‖ ≤ 2 * R) (hb : ‖b - u‖ ≤ 2 * R) :
    ‖a - u‖ ^ 2 - ‖b - u‖ ^ 2 ≤ 4 * R * ‖a - b‖ := by
  have hn := norm_sub_norm_le (a - u) (b - u)
  rw [show (a - u) - (b - u) = a - b by module] at hn
  have hm := mul_le_mul_of_nonneg_right hn
    (show 0 ≤ ‖a - u‖ + ‖b - u‖ by positivity)
  have hu := mul_le_mul_of_nonneg_right (show ‖a - u‖ + ‖b - u‖ ≤ 4 * R by linarith)
    (norm_nonneg (a - b))
  nlinarith

lemma projected_gradient_perturbation {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {η : ℝ} (hη : 0 ≤ η) (x v w : E) :
    ‖SaddlePoint.project C (x - η • v) - SaddlePoint.project C (x - η • w)‖ ≤
      η * ‖v - w‖ := by
  have hh := projection_nonexpansive hne hco hcv (x - η • v) (x - η • w)
  have he : (x - η • v) - (x - η • w) = -η • (v - w) := by module
  simpa only [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη] using hh

lemma projected_accelerated_perturbation {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {f : E → ℝ} {g : E → E} {μ τ R ζ : ℝ}
    (hm : Model μ f g) (hτ : 0 < τ) (hτu : τ ≤ 1 / 2)
    (hR : 0 ≤ R) (hζ : 0 ≤ ζ) (x z u v w : E) (hgu : g u = 0)
    (hrad : ∀ a ∈ C, ‖a - u‖ ≤ 2 * R) (herr : ‖v - w‖ ≤ 3 * ζ) :
    let Y := fun a => SaddlePoint.project C (x - (1 / (6 * μ)) • a)
    let Z := fun a => SaddlePoint.project C (z - (1 / (6 * μ * τ)) • a)
    f (Y v) + 3 * μ * τ ^ 2 * ‖Z v - u‖ ^ 2 ≤
      f (Y w) + 3 * μ * τ ^ 2 * ‖Z w - u‖ ^ 2 + 4 * R * ζ := by
  dsimp only
  let Y := fun a => SaddlePoint.project C (x - (1 / (6 * μ)) • a)
  let Z := fun a => SaddlePoint.project C (z - (1 / (6 * μ * τ)) • a)
  have hμ := hm.pos
  have hym : ∀ a, Y a ∈ C := fun a => (SaddlePoint.project_spec hne hco hcv _).1
  have hzm : ∀ a, Z a ∈ C := fun a => (SaddlePoint.project_spec hne hco hcv _).1
  have hy := projected_gradient_perturbation hne hco hcv
    (by positivity : 0 ≤ 1 / (6 * μ)) x v w
  have hz := projected_gradient_perturbation hne hco hcv
    (by positivity : 0 ≤ 1 / (6 * μ * τ)) z v w
  have hy' : ‖Y v - Y w‖ ≤ ζ / (2 * μ) := by
    calc
      _ ≤ (1 / (6 * μ)) * (3 * ζ) := hy.trans (mul_le_mul_of_nonneg_left herr (by positivity))
      _ = _ := by field_simp; ring
  have hz' : ‖Z v - Z w‖ ≤ ζ / (2 * μ * τ) := by
    calc
      _ ≤ (1 / (6 * μ * τ)) * (3 * ζ) := hz.trans (mul_le_mul_of_nonneg_left herr (by positivity))
      _ = _ := by field_simp; ring
  have hgrad : ‖g (Y v)‖ ≤ 2 * μ * R := by
    have hl := hm.lipschitz (Y v) u
    rw [hgu, sub_zero] at hl
    have hb := mul_le_mul_of_nonneg_left (hrad (Y v) (hym v)) hμ.le
    nlinarith
  have hf := hm.lower (Y v) (Y w)
  have hi := real_inner_le_norm (g (Y v)) (Y v - Y w)
  rw [show Y w - Y v = -(Y v - Y w) by module, inner_neg_right] at hf
  have hprod := mul_le_mul hgrad hy' (norm_nonneg _) (by positivity : 0 ≤ 2 * μ * R)
  have hprodid : (2 * μ * R) * (ζ / (2 * μ)) = R * ζ := by field_simp
  rw [hprodid] at hprod
  have hfd : f (Y v) - f (Y w) ≤ R * ζ := by linarith
  have hs := squared_distance_perturbation (hrad (Z v) (hzm v)) (hrad (Z w) (hzm w))
  have hsd := hs.trans (mul_le_mul_of_nonneg_left hz' (by positivity : 0 ≤ 4 * R))
  have hsweight := mul_le_mul_of_nonneg_left hsd (show 0 ≤ 3 * μ * τ ^ 2 by positivity)
  have hsid : 3 * μ * τ ^ 2 * (4 * R * (ζ / (2 * μ * τ))) = 6 * R * τ * ζ := by field_simp; ring
  rw [hsid] at hsweight
  have ht := mul_le_mul_of_nonneg_right hτu (mul_nonneg hR hζ)
  change f (Y v) + 3 * μ * τ ^ 2 * ‖Z v - u‖ ^ 2 ≤
    f (Y w) + 3 * μ * τ ^ 2 * ‖Z w - u‖ ^ 2 + 4 * R * ζ
  nlinarith

lemma projected_accelerated_inexact {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {f : Fin n → E → ℝ} {g : Fin n × E → E} {μ τ R ζ : ℝ}
    (hm : ∀ i, Model μ (f i) (fun x => g (i, x))) (hτ : 0 < τ) (hτu : τ ≤ 1 / 2)
    (hR : 0 ≤ R) (hζ : 0 ≤ ζ) (y z w u : E) (v : Fin n → E)
    (hy : y ∈ C) (hw : w ∈ C) (hu : u ∈ C) (hgu : fullGradient g u = 0)
    (hrad : ∀ a ∈ C, ‖a - u‖ ≤ 2 * R)
    (herr : ∀ i, ‖v i - estimator g w (τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y) i‖ ≤ 3 * ζ) :
    let x := τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y
    let yn := fun i => SaddlePoint.project C (x - (1 / (6 * μ)) • v i)
    let zn := fun i => SaddlePoint.project C (z - (1 / (6 * μ * τ)) • v i)
    (𝔼 i, (objective f (yn i) - objective f u + 3 * μ * τ ^ 2 * ‖zn i - u‖ ^ 2)) ≤
      (1 / 2 - τ) * (objective f y - objective f u) +
      (1 / 2 : ℝ) * (objective f w - objective f u) +
      3 * μ * τ ^ 2 * ‖z - u‖ ^ 2 + 4 * R * ζ := by
  dsimp only
  let x := τ • z + (1 / 2 : ℝ) • w + (1 / 2 - τ) • y
  let Y := fun a => SaddlePoint.project C (x - (1 / (6 * μ)) • a)
  let Z := fun a => SaddlePoint.project C (z - (1 / (6 * μ * τ)) • a)
  have hp (i : Fin n) := projected_accelerated_perturbation hne hco hcv
    (finiteSum_model hm) hτ hτu hR hζ x z u (v i) (estimator g w x i) hgu hrad (herr i)
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun i _ => hp i)
  have hexact := projected_accelerated_average hne hco hcv hm hτ hτu y z w u hy hw hu
  change (𝔼 i, (objective f (Y (v i)) + 3 * μ * τ ^ 2 * ‖Z (v i) - u‖ ^ 2)) ≤
    (𝔼 i, (objective f (Y (estimator g w x i)) +
      3 * μ * τ ^ 2 * ‖Z (estimator g w x i) - u‖ ^ 2 + 4 * R * ζ)) at hav
  change (𝔼 i, (objective f (Y (estimator g w x i)) - objective f u +
      3 * μ * τ ^ 2 * ‖Z (estimator g w x i) - u‖ ^ 2)) ≤ _ at hexact
  change (𝔼 i, (objective f (Y (v i)) - objective f u +
      3 * μ * τ ^ 2 * ‖Z (v i) - u‖ ^ 2)) ≤ _
  simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib,
    ← Finset.mul_expect, Fintype.expect_const] at hav hexact ⊢
  linarith



lemma finite_average_norm (e : Fin n → E) {ζ : ℝ} (he : ∀ i, ‖e i‖ ≤ ζ) :
    ‖(n : ℝ)⁻¹ • ∑ i, e i‖ ≤ ζ := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  have hs := (norm_sum_le Finset.univ e).trans (Finset.sum_le_sum (fun i _ => he i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hh := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] using hh

lemma cached_estimator_error (G : Fin n × E → E) (cache : Fin n → E)
    (w x query : E) (i : Fin n) {ζ : ℝ}
    (hcache : ∀ j, ‖cache j - G (j, w)‖ ≤ ζ) (hquery : ‖query - G (i, x)‖ ≤ ζ) :
    ‖query - cache i + (n : ℝ)⁻¹ • ∑ j, cache j - estimator G w x i‖ ≤ 3 * ζ := by
  have hmean := finite_average_norm (fun j => cache j - G (j, w)) hcache
  have hid : query - cache i + (n : ℝ)⁻¹ • ∑ j, cache j - estimator G w x i =
      (query - G (i, x)) - (cache i - G (i, w)) + (n : ℝ)⁻¹ • ∑ j, (cache j - G (j, w)) := by
    simp only [estimator, fullGradient, Finset.sum_sub_distrib, smul_sub]
    module
  rw [hid]
  have h1 := norm_add_le ((query - G (i, x)) - (cache i - G (i, w)))
    ((n : ℝ)⁻¹ • ∑ j, (cache j - G (j, w)))
  have h2 := norm_sub_le (query - G (i, x)) (cache i - G (i, w))
  linarith [hcache i]


end OracleTemplate.ComponentEnvelope
