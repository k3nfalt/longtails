import LongTails.Proofs.NearZeroSumModel
import LongTails.Proofs.PLMinimaxInitialization
import LongTails.Proofs.NearZeroSumInner
import LongTails.Algorithms.HeavyTailSaddleEstimator
import LongTails.Proofs.ScalarSearchBudget
import LongTails.Proofs.HeavyTailSaddleGeometry
open scoped BigOperators RealInnerProductSpace
open LongTails.Proofs.RecursiveEnvelopeGeometry
namespace LongTails.Proofs.HeavyTailSaddleRecovery
lemma weighted_center_telescope {E : Type*} [AddCommGroup E] [Module ℝ E]
    (weight : ℕ → ℝ) (point : ℕ → E) (K : ℕ) :
    ∑ i ∈ Finset.range K, weight i • (point K - point i) =
      ∑ j ∈ Finset.range K, (∑ i ∈ Finset.range (j + 1), weight i) • (point (j + 1) - point j) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hsplit : ∑ i ∈ Finset.range K, weight i • (point (K + 1) - point i) =
        (∑ i ∈ Finset.range K, weight i • (point K - point i)) +
          (∑ i ∈ Finset.range K, weight i) • (point (K + 1) - point K) := by
      rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      module
    rw [hsplit, ih, Finset.sum_range_succ, add_smul]
    abel

lemma dyadic_weight_sum (μ : ℝ) (K : ℕ) :
    ∑ i ∈ Finset.range K, (2 : ℝ) ^ i * μ = ((2 : ℝ) ^ K - 1) * μ := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma dyadic_gradient_telescope {E : Type*} [AddCommGroup E] [Module ℝ E]
    (base : E → E) (μ : ℝ) (point : ℕ → E) (K : ℕ) :
    base (point K) =
      (base (point K) + ∑ i ∈ Finset.range K, ((2 : ℝ) ^ i * μ) • (point K - point i)) -
        ∑ j ∈ Finset.range K, (((2 : ℝ) ^ (j + 1) - 1) * μ) • (point (j + 1) - point j) := by
  rw [weighted_center_telescope]
  simp_rw [dyadic_weight_sum]
  abel
lemma regularized_stage_transfer {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {m e e' : ℝ} (hm : 0 ≤ m) (v u w z : E)
    (hmin : ∀ x, f u ≤ f x) (hv : f v - f u ≤ e)
    (hsc : ∀ x, m * ‖x - w‖ ^ 2 ≤
      RecursiveEnvelopeGeometry.regularized f m v x - RecursiveEnvelopeGeometry.regularized f m v w)
    (hz : RecursiveEnvelopeGeometry.regularized f m v z -
      RecursiveEnvelopeGeometry.regularized f m v w ≤ e') :
    RecursiveEnvelopeGeometry.regularized f m v v - RecursiveEnvelopeGeometry.regularized f m v w ≤ e ∧
      m * ‖z - v‖ ^ 2 ≤ 2 * (e + e') := by
  have he : RecursiveEnvelopeGeometry.regularized f m v v -
      RecursiveEnvelopeGeometry.regularized f m v w ≤ e := by
    dsimp [RecursiveEnvelopeGeometry.regularized]
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero]
    have hn := mul_nonneg hm (sq_nonneg ‖w - v‖)
    linarith [hmin w]
  have hvd := (hsc v).trans he
  have hzd := (hsc z).trans hz
  have hdist := AuxiliaryInner.norm_add_sq_le (z - w) (w - v)
  rw [show (z - w) + (w - v) = z - v by abel, norm_sub_rev w v] at hdist
  have hh := mul_le_mul_of_nonneg_left hdist hm
  exact ⟨he, by nlinarith only [hh, hvd, hzd]⟩

lemma recursive_warm_reference {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] {m e : ℝ} (hm : 0 ≤ m) (he : 0 ≤ e)
    (ref : E) (v w : F) (U : F → E) (hU : ∀ x y, ‖U x - U y‖ ≤ ‖x - y‖)
    (href : m * ‖ref - U v‖ ^ 2 ≤ e / 128) (hv : m * ‖v - w‖ ^ 2 ≤ e) :
    (2 * m) * ‖ref - U w‖ ^ 2 ≤ 8 * e := by
  have hs := pow_le_pow_left₀ (norm_nonneg _) (hU v w) 2
  have hscale := mul_le_mul_of_nonneg_left hs hm
  have hdist := AuxiliaryInner.norm_add_sq_le (ref - U v) (U v - U w)
  rw [show (ref - U v) + (U v - U w) = ref - U w by abel] at hdist
  have hh := mul_le_mul_of_nonneg_left hdist hm
  nlinarith only [href, hv, hscale, hh, he]
lemma dyadic_residual_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) (base : E → E) (point : ℕ → E) (K : ℕ)
    (hstep : ∀ j < K, ((2 : ℝ) ^ j * μ) ^ 2 * ‖point (j + 1) - point j‖ ^ 2 ≤ 3 * t ^ 2)
    (hlast : ‖base (point K) + ∑ i ∈ Finset.range K, ((2 : ℝ) ^ i * μ) • (point K - point i)‖ ≤ 2 * t) :
    ‖base (point K)‖ ≤ (4 * K + 2) * t := by
  have hterm (j : ℕ) (hj : j < K) :
      ‖(((2 : ℝ) ^ (j + 1) - 1) * μ) • (point (j + 1) - point j)‖ ≤ 4 * t := by
    have hw : 0 < (2 : ℝ) ^ j * μ := by positivity
    have hc0 : 0 ≤ ((2 : ℝ) ^ (j + 1) - 1) * μ :=
      mul_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num))) hμ.le
    have hc : ((2 : ℝ) ^ (j + 1) - 1) * μ ≤ 2 * ((2 : ℝ) ^ j * μ) := by
      rw [pow_succ]
      nlinarith only [hμ]
    have hd : ((2 : ℝ) ^ j * μ) * ‖point (j + 1) - point j‖ ≤ 2 * t := by
      apply (sq_le_sq₀ (mul_nonneg hw.le (norm_nonneg _)) (by positivity)).mp
      rw [mul_pow]
      nlinarith only [hstep j hj, sq_nonneg t]
    rw [norm_smul, Real.norm_of_nonneg hc0]
    have hh := mul_le_mul_of_nonneg_right hc (norm_nonneg (point (j + 1) - point j))
    nlinarith only [hh, hd]
  have hsum : ‖∑ j ∈ Finset.range K, (((2 : ℝ) ^ (j + 1) - 1) * μ) • (point (j + 1) - point j)‖ ≤ K * (4 * t) := by
    calc
      _ ≤ ∑ j ∈ Finset.range K, ‖(((2 : ℝ) ^ (j + 1) - 1) * μ) • (point (j + 1) - point j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range K, (4 * t) := Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
      _ = _ := by simp
  have hh := norm_sub_le
    (base (point K) + ∑ i ∈ Finset.range K, ((2 : ℝ) ^ i * μ) • (point K - point i))
    (∑ j ∈ Finset.range K, (((2 : ℝ) ^ (j + 1) - 1) * μ) • (point (j + 1) - point j))
  rw [← dyadic_gradient_telescope] at hh
  nlinarith only [hh, hlast, hsum]
lemma recursive_gap_certificate {α μ L m D t J gx gy gap : ℝ}
    (hα : 0 < α) (hμ : 0 < μ) (hm : 0 < m) (hLm : L ≤ m)
    (hμα : μ ≤ 4 * α) (hD : 0 ≤ D) (ht : 0 ≤ t) (hJ : 1 ≤ J)
    (hmd : m ^ 2 * D ^ 2 ≤ t ^ 2 / 128) (hx0 : 0 ≤ gx) (hy0 : 0 ≤ gy)
    (hx : gx ≤ L * D) (hy : gy ≤ 4 * J * t + L * D)
    (hgap : gap ≤ gx ^ 2 / (2 * α) + gy ^ 2 / (2 * μ)) :
    gap ≤ 15 * J ^ 2 * t ^ 2 / μ := by
  have hmt : m * D ≤ t := by
    apply (sq_le_sq₀ (mul_nonneg hm.le hD) ht).mp
    rw [mul_pow]
    nlinarith only [hmd, sq_nonneg t]
  have hlt : L * D ≤ t := (mul_le_mul_of_nonneg_right hLm hD).trans hmt
  have hx2 : gx ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hx0 (hx.trans hlt) 2
  have hy' : gy ≤ 5 * J * t := by nlinarith only [hy, hlt, mul_nonneg (sub_nonneg.mpr hJ) ht]
  have hy2 : gy ^ 2 ≤ 25 * J ^ 2 * t ^ 2 := by
    have hh := pow_le_pow_left₀ hy0 hy' 2
    nlinarith only [hh]
  have hfirst : gx ^ 2 / (2 * α) ≤ 2 * t ^ 2 / μ := by
    calc
      _ ≤ t ^ 2 / (2 * α) := div_le_div_of_nonneg_right hx2 (by positivity)
      _ ≤ _ := (div_le_div_iff₀ (by positivity) hμ).mpr
        (by nlinarith only [mul_le_mul_of_nonneg_right hμα (sq_nonneg t)])
  have hsecond : gy ^ 2 / (2 * μ) ≤ 25 * J ^ 2 * t ^ 2 / (2 * μ) :=
    div_le_div_of_nonneg_right hy2 (by positivity)
  have hJ2 : 1 ≤ J ^ 2 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hJ2 (sq_nonneg t)
  have hsum : 2 * t ^ 2 / μ + 25 * J ^ 2 * t ^ 2 / (2 * μ) ≤ 15 * J ^ 2 * t ^ 2 / μ := by
    apply (le_div_iff₀ hμ).mpr
    field_simp
    nlinarith only [hscale]
  exact hgap.trans ((add_le_add hfirst hsecond).trans hsum)
lemma terminal_reference_scale {m B t D : ℝ} (hm : 0 < m) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hentry : B ≤ 2 * t ^ 2 / m)
    (hd : D ≤ Real.sqrt (B / m) / 16) : m ^ 2 * D ^ 2 ≤ t ^ 2 / 128 := by
  have hsq := pow_le_pow_left₀ hD hd 2
  rw [div_pow, Real.sq_sqrt (div_nonneg hB hm.le)] at hsq
  have h1 := (le_div_iff₀ (by positivity : 0 < (16 : ℝ) ^ 2)).mp hsq
  have h2 := (le_div_iff₀ hm).mp h1
  have h3 := (le_div_iff₀ hm).mp hentry
  have hh := mul_le_mul_of_nonneg_right h2 hm.le
  nlinarith only [hh, h3]

lemma recursive_gap_tuning {μ ζ J : ℝ} (hμ : 0 < μ) (hζ : 0 < ζ) (hJ : 1 ≤ J) :
    15 * J ^ 2 * (Real.sqrt (μ * ζ) / (1000 * J)) ^ 2 / μ ≤ ζ / 100 := by
  have hJ0 : 0 < J := by linarith
  rw [div_pow, Real.sq_sqrt (mul_pos hμ hζ).le]
  have heq : 15 * J ^ 2 * (μ * ζ / (1000 * J) ^ 2) / μ = 15 * ζ / 1000000 := by
    field_simp
    ring
  rw [heq]
  linarith

open LongTails.Algorithms.HeavyTailSaddleEstimator
lemma refinement_envelope_pos {B : ℝ} (hB : 0 < B) (j : ℕ) :
    0 < refinementEnvelope B j := by unfold refinementEnvelope; positivity
lemma refinement_envelope_succ (B : ℝ) (j : ℕ) :
    refinementEnvelope B (j + 1) = refinementEnvelope B j / 2 := by
  simp only [refinementEnvelope, pow_succ, div_mul_eq_div_div]
lemma refinement_steps_tuning {B target : ℝ} (ht : 0 < target) :
    0 < refinementSteps B target ∧
    refinementEnvelope B (refinementSteps B target - 1) ≤ target ∧
    refinementEnvelope B (refinementSteps B target) ≤ target / 2 := by
  let k := ⌈Real.logb 2 (max 1 (B / target))⌉₊
  have hk : refinementSteps B target = k + 1 := by unfold refinementSteps k; omega
  have hh := OracleTemplate.ScalarHeavyTailEstimator.dyadic_ceil_lower (B / target)
  change B / target ≤ (2 : ℝ) ^ k at hh
  have hb : B ≤ target * (2 : ℝ) ^ k := by
    have he := (div_le_iff₀ ht).mp hh
    simpa only [mul_comm] using he
  have hg : refinementEnvelope B k ≤ target := (div_le_iff₀ (by positivity)).mpr hb
  refine ⟨by omega, ?_, ?_⟩
  · simpa only [hk, Nat.add_sub_cancel] using hg
  · rw [hk, refinement_envelope_succ]
    exact div_le_div_of_nonneg_right hg (by norm_num)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma regularized_strong_lower {q : E → ℝ} {g : E → E} {m lam : ℝ}
    (hsc : ∀ x y, q x + ⟪g x,y-x⟫ + m/2 * ‖y-x‖^2 ≤ q y) (c x y : E) :
    regularized q lam c x + ⟪g x + lam • (x-c), y-x⟫ + (m+lam)/2 * ‖y-x‖^2 ≤
      regularized q lam c y := by
  unfold regularized
  rw [squared_shift x y c, inner_add_left, real_inner_smul_left]
  linarith [hsc x y]

lemma regularized_field_lipschitz {g : E → E} {H lam : ℝ} (hlam : 0 ≤ lam)
    (hl : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖) (c x y : E) :
    ‖(g x + lam • (x-c)) - (g y + lam • (y-c))‖ ≤ (H+lam)*‖x-y‖ := by
  have he : (g x + lam • (x-c)) - (g y + lam • (y-c)) = (g x-g y)+lam • (x-y) := by module
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hlam, add_mul]
  exact add_le_add (hl x y) le_rfl

lemma regularized_hasGradient [CompleteSpace E] {q : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt q (g x) x) (lam : ℝ) (c x : E) :
    HasGradientAt (regularized q lam c) (g x + lam • (x-c)) x := by
  unfold regularized
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hg x).hasFDerivAt.add
    (((hasStrictFDerivAt_norm_sq (x-c)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const c)).const_mul (lam/2)) using 1
  all_goals
    first
    | rfl
    | (ext v; simp; ring)
lemma strongly_convex_zero [CompleteSpace E] {q : E → ℝ} {g : E → E} {m H : ℝ}
    (hm : 0 < m) (hmH : m ≤ H) (hl : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖)
    (hsc : ∀ x y, q x + ⟪g x,y-x⟫ + m/2 * ‖y-x‖^2 ≤ q y) :
    ∃ u, g u = 0 ∧ ∀ x, q u ≤ q x := by
  have hneg : ∀ x y, -q y ≤ -q x + ⟪-g x,y-x⟫ - m/2 * ‖y-x‖^2 := by
    intro x y
    rw [inner_neg_left]
    linarith [hsc x y]
  obtain ⟨u, hu, hmin⟩ := HeavyTailSaddleGeometry.dual_attainment hm hmH
    (fun x y => by rw [neg_sub_neg, norm_sub_rev]; exact hl x y) hneg
  exact ⟨u, neg_eq_zero.mp hu, fun x => neg_le_neg_iff.mp (hmin x)⟩

lemma finite_regularized_hasGradient [CompleteSpace E] {q : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt q (g x) x) (weight : ℕ → ℝ) (center : ℕ → E) (K : ℕ) (x : E) :
    HasGradientAt (fun v => q v + ∑ j ∈ Finset.range K, weight j / 2 * ‖v-center j‖^2)
      (g x + ∑ j ∈ Finset.range K, weight j • (x-center j)) x := by
  induction K generalizing x with
  | zero => simpa using hg x
  | succ K ih =>
    have hh := regularized_hasGradient ih (weight K) (center K) x
    unfold regularized at hh
    simpa only [Finset.sum_range_succ, add_assoc] using hh

lemma finite_regularized_strong_lower {q : E → ℝ} {g : E → E} {m : ℝ}
    (hsc : ∀ x y, q x + ⟪g x,y-x⟫ + m/2 * ‖y-x‖^2 ≤ q y)
    (weight : ℕ → ℝ) (center : ℕ → E) (K : ℕ) (x y : E) :
    (q x + ∑ j ∈ Finset.range K, weight j/2 * ‖x-center j‖^2) +
      ⟪g x + ∑ j ∈ Finset.range K, weight j • (x-center j),y-x⟫ +
      (m + ∑ j ∈ Finset.range K, weight j)/2 * ‖y-x‖^2 ≤
      q y + ∑ j ∈ Finset.range K, weight j/2 * ‖y-center j‖^2 := by
  induction K generalizing x y with
  | zero => simpa using hsc x y
  | succ K ih =>
    simpa only [Finset.sum_range_succ, regularized, add_assoc] using
      regularized_strong_lower ih (lam := weight K) (center K) x y

lemma finite_regularized_field_lipschitz {g : E → E} {H : ℝ}
    (hl : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖)
    (weight : ℕ → ℝ) (hw : ∀ j, 0 ≤ weight j) (center : ℕ → E) (K : ℕ) (x y : E) :
    ‖(g x + ∑ j ∈ Finset.range K, weight j • (x-center j)) -
      (g y + ∑ j ∈ Finset.range K, weight j • (y-center j))‖ ≤
      (H + ∑ j ∈ Finset.range K, weight j)*‖x-y‖ := by
  induction K generalizing x y with
  | zero => simpa using hl x y
  | succ K ih =>
    simpa only [Finset.sum_range_succ, add_assoc] using
      regularized_field_lipschitz (hw K) ih (center K) x y


lemma affine_regularized_hasGradient [CompleteSpace E] {q : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt q (g x) x) (lam : ℝ) (b x : E) :
    HasGradientAt (fun v => q v + lam/2 * ‖v‖^2 - ⟪b,v⟫) (g x + lam • x - b) x := by
  have hh := regularized_hasGradient hg lam (0 : E) x
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hh.hasFDerivAt.sub (innerSL ℝ b).hasFDerivAt using 1
  · ext v
    simp [regularized]
  · ext v
    simp [InnerProductSpace.toDual_apply_apply]

lemma affine_regularized_strong_lower {q : E → ℝ} {g : E → E} {m lam : ℝ}
    (hsc : ∀ x y, q x + ⟪g x,y-x⟫ + m/2 * ‖y-x‖^2 ≤ q y) (b x y : E) :
    (q x + lam/2 * ‖x‖^2 - ⟪b,x⟫) + ⟪g x+lam • x-b,y-x⟫ +
      (m+lam)/2 * ‖y-x‖^2 ≤ q y + lam/2 * ‖y‖^2 - ⟪b,y⟫ := by
  have hh := regularized_strong_lower hsc (lam := lam) (0 : E) x y
  simp only [regularized, sub_zero] at hh
  rw [inner_sub_left, inner_sub_right b]
  linarith only [hh]

lemma affine_regularized_field_lipschitz {g : E → E} {H lam : ℝ} (hlam : 0 ≤ lam)
    (hl : ∀ x y, ‖g x-g y‖ ≤ H*‖x-y‖) (b x y : E) :
    ‖(g x+lam • x-b) - (g y+lam • y-b)‖ ≤ (H+lam)*‖x-y‖ := by
  simpa only [sub_zero, sub_sub_sub_cancel_right] using
    regularized_field_lipschitz hlam hl (0 : E) x y

lemma regularized_field_sum (weight : ℕ → ℝ) (center : ℕ → E) (K : ℕ) (x : E) :
    (∑ j ∈ Finset.range K, weight j • (x-center j)) =
      (∑ j ∈ Finset.range K, weight j) • x - ∑ j ∈ Finset.range K, weight j • center j := by
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]

open OracleTemplate.PLMinimax
lemma proximal_regularized_dual_geometry {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ lam : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y + ⟪gy x y,y'-y⟫ - μ/2 * ‖y'-y‖^2)
    (hlam : 0 ≤ lam) (c : E) (b : F) :
    let q := fun y => -dual f L c y + lam/2 * ‖y‖^2 - ⟪b,y⟫
    let g := fun y => -gy (innerPrimal f L c y) y + lam • y - b
    (∀ y, HasGradientAt q (g y) y) ∧
    (∀ x y, q x + ⟪g x,y-x⟫ + (μ+lam)/2 * ‖y-x‖^2 ≤ q y) ∧
    (∀ x y, ‖g x-g y‖ ≤ (2*L+lam)*‖x-y‖) ∧
    ∃ u, g u = 0 ∧ ∀ y, q u ≤ q y := by
  intro q g
  have hbaseg (y : F) : HasGradientAt (fun y => -dual f L c y)
      (-gy (innerPrimal f L c y) y) y :=
    OracleTemplate.TwoSidedPL.hasGradientAt_neg' (H.dual_hasGradient c y)
  have hbasel (x y : F) : ‖-gy (innerPrimal f L c x) x - -gy (innerPrimal f L c y) y‖ ≤
      2*L*‖x-y‖ := by
    rw [neg_sub_neg, norm_sub_rev]
    exact H.dual_gradient_lipschitz c x y
  have hbasesc (x y : F) : -dual f L c x + ⟪-gy (innerPrimal f L c x) x,y-x⟫ +
      μ/2 * ‖y-x‖^2 ≤ -dual f L c y := by
    rw [inner_neg_left]
    linarith only [HeavyTailSaddleGeometry.proximal_dual_strong_concave H hsc c x y]
  have hqg : ∀ y, HasGradientAt q (g y) y := affine_regularized_hasGradient hbaseg lam b
  have hqsc : ∀ x y, q x + ⟪g x,y-x⟫ + (μ+lam)/2 * ‖y-x‖^2 ≤ q y :=
    affine_regularized_strong_lower hbasesc b
  have hql : ∀ x y, ‖g x-g y‖ ≤ (2*L+lam)*‖x-y‖ :=
    affine_regularized_field_lipschitz hlam hbasel b
  exact ⟨hqg, hqsc, hql, strongly_convex_zero (by linarith [H.hμ])
    (by linarith [H.hμL, H.hL]) hql hqsc⟩

lemma stationary_map_lipschitz {A E : Type*} [NormedAddCommGroup A]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {G : A → E → E} {m C : ℝ} (hm : 0 < m) (hC : 0 ≤ C)
    (hs : ∀ a x y, m * ‖x-y‖^2 ≤ ⟪G a x-G a y,x-y⟫)
    (hp : ∀ a b x, ‖G a x-G b x‖ ≤ C*‖a-b‖)
    (root : A → E) (hz : ∀ a, G a (root a) = 0) :
    LipschitzWith (Real.toNNReal (C/m)) root := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hd := OracleTemplate.NearZeroSum.strong_residual_distance (C := Set.univ)
    (A := G a) (ρ := m) (fun x _ y _ => hs a x y)
    (u := root b) (s := root a) (n := (0 : E)) (Set.mem_univ _) (Set.mem_univ _)
    (by intro w hw; simp)
    (by rw [hz]; intro w hw; simp)
  have hb := hp a b (root b)
  rw [hz, sub_zero] at hb
  simp only [add_zero, norm_sub_rev (root b) (root a)] at hd
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (div_nonneg hC hm.le)]
  have hh := hd.trans hb
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hm).mpr
  nlinarith only [hh]

section ParameterGeometry
open MeasureTheory
variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
omit [FiniteDimensional ℝ F] in
lemma inner_primal_center_lipschitz (H : Hyp f gx gy L μ) (y : F) (c d : E) :
    ‖innerPrimal f L c y-innerPrimal f L d y‖ ≤ 2*‖c-d‖ := by
  let G := fun c x => gx x y + (2*L) • (x-c)
  have hs (a x z : E) : L * ‖x-z‖^2 ≤ ⟪G a x-G a z,x-z⟫ := by
    apply (HeavyTailSaddleGeometry.proximal_primal_bounds H.hL.le a x z ?_).1
    simpa only [sub_self, norm_zero, add_zero] using H.lipx x z y y
  have hp (a b x : E) : ‖G a x-G b x‖ ≤ (2*L)*‖a-b‖ := by
    have he : G a x-G b x = (2*L) • (b-a) := by dsimp [G]; module
    rw [he, norm_smul, Real.norm_of_nonneg (by linarith [H.hL] : 0 ≤ 2*L), norm_sub_rev]
  have hh := stationary_map_lipschitz H.hL (show 0 ≤ 2*L by linarith [H.hL]) hs hp
    (fun c => innerPrimal f L c y) (fun c => H.innerPrimal_stationary c y)
  have he : (2*L)/L = 2 := by field_simp [H.hL.ne']
  rw [he] at hh
  simpa using hh.norm_sub_le c d

omit [FiniteDimensional ℝ F] in
lemma inner_primal_joint_lipschitz (H : Hyp f gx gy L μ) :
    LipschitzWith 3 (fun z : E × F => innerPrimal f L z.1 z.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have h1 := inner_primal_center_lipschitz H a.2 a.1 b.1
  have h2 := H.innerPrimal_lipschitz b.1 a.2 b.2
  have ht := norm_add_le (innerPrimal f L a.1 a.2-innerPrimal f L b.1 a.2)
    (innerPrimal f L b.1 a.2-innerPrimal f L b.1 b.2)
  rw [sub_add_sub_cancel] at ht
  have hf := norm_fst_le (a-b)
  have hs := norm_snd_le (a-b)
  simp only [Prod.fst_sub, Prod.snd_sub] at hf hs
  rw [dist_eq_norm, dist_eq_norm]
  norm_num
  linarith
omit [FiniteDimensional ℝ F] in
lemma objective_joint_measurable [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] (H : Hyp f gx gy L μ) :
    Measurable (Function.uncurry f) := by
  apply measurable_uncurry_of_continuous_of_measurable
  · intro y
    exact continuous_iff_continuousAt.mpr (fun x => (H.hgx x y).differentiableAt.continuousAt)
  · intro x
    exact (continuous_iff_continuousAt.mpr
      (fun y => (H.hgy x y).differentiableAt.continuousAt)).measurable

lemma proximal_regularized_value_measurable [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F] (H : Hyp f gx gy L μ) (lam : ℝ) :
    Measurable (fun z : (E × F) × F =>
      -dual f L z.1.1 z.2 + lam/2 * ‖z.2‖^2 - ⟪z.1.2,z.2⟫) := by
  have hU := (inner_primal_joint_lipschitz H).continuous.measurable
  have hu : Measurable (fun z : (E × F) × F => innerPrimal f L z.1.1 z.2) :=
    hU.comp (measurable_fst.fst.prodMk measurable_snd)
  have hf := (objective_joint_measurable H).comp (hu.prodMk measurable_snd)
  change Measurable (fun z : (E × F) × F => f (innerPrimal f L z.1.1 z.2) z.2) at hf
  change Measurable (fun z : (E × F) × F =>
    -(f (innerPrimal f L z.1.1 z.2) z.2 + L * ‖innerPrimal f L z.1.1 z.2-z.1.1‖^2) +
      lam/2 * ‖z.2‖^2 - ⟪z.1.2,z.2⟫)
  have hn : Measurable (fun z : (E × F) × F => L * ‖innerPrimal f L z.1.1 z.2-z.1.1‖^2) := by fun_prop
  have hq : Measurable (fun z : (E × F) × F => lam/2 * ‖z.2‖^2) := by fun_prop
  have hb : Measurable (fun z : (E × F) × F => ⟪z.1.2,z.2⟫) := by fun_prop
  exact ((hf.add hn).neg.add hq).sub hb

omit [FiniteDimensional ℝ F] in
lemma proximal_regularized_stationary_map (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y + ⟪gy x y,y'-y⟫ - μ/2 * ‖y'-y‖^2)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    let q := fun (z : E × F) y => -dual f L z.1 y + lam/2 * ‖y‖^2 - ⟪z.2,y⟫
    let G := fun (z : E × F) y => -gy (innerPrimal f L z.1 y) y + lam • y-z.2
    ∃ root : E × F → F, (∀ z, G z (root z) = 0) ∧
      (∀ z y, q z (root z) ≤ q z y) ∧
      LipschitzWith (Real.toNNReal ((2*L+1)/(μ+lam))) root := by
  intro q G
  have hex (z : E × F) : ∃ u, G z u = 0 ∧ ∀ y, q z u ≤ q z y :=
    (proximal_regularized_dual_geometry H hsc hlam z.1 z.2).2.2.2
  choose root hz hmin using hex
  refine ⟨root, hz, hmin, ?_⟩
  have hL := H.hL
  apply stationary_map_lipschitz (by linarith [H.hμ]) (by linarith) ?_ ?_ root hz
  · intro a x y
    have hqs := (proximal_regularized_dual_geometry H hsc hlam a.1 a.2).2.1
    have hn : ∀ u v, -q a v ≤ -q a u + ⟪-G a u,v-u⟫ - (μ+lam)/2 * ‖v-u‖^2 := by
      intro u v
      rw [inner_neg_left]
      have hh := hqs u v
      change q a u + ⟪G a u,v-u⟫ + (μ+lam)/2 * ‖v-u‖^2 ≤ q a v at hh
      linarith only [hh]
    simpa only [neg_neg] using HeavyTailSaddleGeometry.dual_antimonotone hn x y
  · intro a b x
    have he : G a x-G b x =
        (gy (innerPrimal f L b.1 x) x-gy (innerPrimal f L a.1 x) x)+(b.2-a.2) := by
      dsimp [G]
      abel
    have hl := H.lipy (innerPrimal f L b.1 x) (innerPrimal f L a.1 x) x x
    simp only [sub_self, norm_zero, add_zero] at hl
    have hu := inner_primal_center_lipschitz H x b.1 a.1
    rw [norm_sub_rev b.1 a.1] at hu
    rw [he]
    calc
      _ ≤ ‖gy (innerPrimal f L b.1 x) x-gy (innerPrimal f L a.1 x) x‖ + ‖b.2-a.2‖ := norm_add_le _ _
      _ ≤ L * (2*‖a.1-b.1‖) + ‖a.2-b.2‖ :=
        add_le_add (hl.trans (mul_le_mul_of_nonneg_left hu hL.le)) (by rw [norm_sub_rev])
      _ ≤ L * (2*‖a-b‖) + ‖a-b‖ := by
        gcongr
        · exact norm_fst_le (a-b)
        · exact norm_snd_le (a-b)
      _ = (2*L+1)*‖a-b‖ := by ring


end ParameterGeometry

lemma refinement_last_envelope_lower {B target : ℝ} (ht : 0 < target) (hBt : target ≤ B) :
    target/2 ≤ refinementEnvelope B (refinementSteps B target-1) := by
  let k := ⌈Real.logb 2 (max 1 (B/target))⌉₊
  have hk : refinementSteps B target-1 = k := by unfold refinementSteps k; omega
  have hr : 1 ≤ B/target := (le_div_iff₀ ht).mpr (by simpa using hBt)
  have hh := OracleTemplate.ScalarHeavyTailEstimator.dyadic_ceil_upper (B/target)
  change (2 : ℝ)^k ≤ 2*max 1 (B/target) at hh
  rw [max_eq_right hr] at hh
  rw [hk]
  change target/2 ≤ B/(2 : ℝ)^k
  apply (le_div_iff₀ (by positivity)).mpr
  have hs := mul_le_mul_of_nonneg_left hh (show 0 ≤ target/2 by positivity)
  have he : target/2*(2*(B/target)) = B := by field_simp
  exact hs.trans_eq he

lemma refinement_floored_envelope {B target : ℝ} (ht : 0 < target) :
    0 < max B target ∧ B ≤ max B target ∧
    target/2 ≤ refinementEnvelope (max B target) (refinementSteps (max B target) target-1) ∧
    refinementEnvelope (max B target) (refinementSteps (max B target) target-1) ≤ target := by
  exact ⟨lt_of_lt_of_le ht (le_max_right _ _), le_max_left _ _,
    refinement_last_envelope_lower ht (le_max_right _ _), (refinement_steps_tuning ht).2.1⟩

lemma four_halving_envelopes (e : ℝ) :
    refinementEnvelope (8*e) 4 = e/2 ∧ refinementEnvelope (8*e) 3 = e := by
  norm_num [refinementEnvelope]
  ring

lemma proximal_correction_measurable {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (L lam : ℝ) :
    Measurable (fun w : (E × F) × (E × F) => proximalCorrection L lam w.1.1 w.1.2 w.2) := by
  unfold proximalCorrection
  fun_prop
lemma proximal_correction_dual {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (L lam : ℝ) (center : E) (shift : F)
    (z reply : E × F) :
    -(reply+proximalCorrection L lam center shift z).2 = -reply.2 + lam • z.2-shift := by
  simp only [proximalCorrection, Prod.snd_add]
  abel

lemma recovery_mass_pos {μ : ℝ} (hμ : 0 < μ) (j : ℕ) : 0 < recoveryMass μ j := by
  unfold recoveryMass
  positivity
lemma recovery_mass_succ (μ : ℝ) (j : ℕ) : recoveryMass μ (j+1) = 2*recoveryMass μ j := by
  unfold recoveryMass
  rw [pow_succ]
  ring
lemma recovery_target_succ (L μ ζ : ℝ) (j : ℕ) :
    recoveryTarget L μ ζ (j+1) = recoveryTarget L μ ζ j/2 := by
  unfold recoveryTarget
  rw [recovery_mass_succ]
  ring
lemma recovery_target_pos {L μ ζ : ℝ} (hμ : 0 < μ) (hζ : 0 < ζ) (j : ℕ) :
    0 < recoveryTarget L μ ζ j := by
  have hJ : 0 < recoveryStages L μ := by unfold recoveryStages; omega
  unfold recoveryTarget recoveryScale
  exact div_pos (sq_pos_of_pos (div_pos (Real.sqrt_pos.2 (mul_pos hμ hζ)) (by positivity)))
    (recovery_mass_pos hμ j)
lemma recovery_terminal_mass {L μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 15*L) :
    15*L ≤ recoveryMass μ (recoveryStages L μ-1) ∧
    recoveryMass μ (recoveryStages L μ-1) ≤ 30*L := by
  have hratio : 1 ≤ 15*L/μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  have hlo := OracleTemplate.ScalarHeavyTailEstimator.dyadic_ceil_lower (15*L/μ)
  have hhi := OracleTemplate.ScalarHeavyTailEstimator.dyadic_ceil_upper (15*L/μ)
  rw [max_eq_right hratio] at hhi
  have hj : recoveryStages L μ-1 = ⌈Real.logb 2 (max 1 (15*L/μ))⌉₊ := by unfold recoveryStages; omega
  unfold recoveryMass
  rw [hj]
  constructor
  · exact (div_le_iff₀ hμ).mp hlo
  · have hh := mul_le_mul_of_nonneg_right hhi hμ.le
    have he : 2*(15*L/μ)*μ = 30*L := by field_simp; ring
    simpa only [max_eq_right hratio] using hh.trans_eq he
lemma recovery_warm_envelopes (L μ ζ initialBound : ℝ) (j : ℕ) :
    recoveryHalvings L μ ζ initialBound (j+1) = 4 ∧
    refinementEnvelope (recoveryEnvelope L μ ζ initialBound (j+1)) 4 = recoveryTarget L μ ζ (j+1) ∧
    refinementEnvelope (recoveryEnvelope L μ ζ initialBound (j+1)) 3 = 2*recoveryTarget L μ ζ (j+1) := by
  simp only [recoveryHalvings, recoveryEnvelope, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ite_false, Nat.add_sub_cancel, recovery_target_succ]
  have hh := four_halving_envelopes (recoveryTarget L μ ζ j)
  exact ⟨trivial, hh.1, by rw [hh.2]; ring⟩

lemma affine_regularized_increment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : E → ℝ) (m μ : ℝ) (b v x : E) :
    q x + (2*m-μ)/2*‖x‖^2-⟪b+m • v,x⟫ =
      regularized (fun y => q y+(m-μ)/2*‖y‖^2-⟪b,y⟫) m v x - m/2*‖v‖^2 := by
  unfold regularized
  rw [inner_add_left, real_inner_smul_left]
  have hn : ‖x-v‖^2 = ‖x‖^2+‖v‖^2-2*⟪v,x⟫ := by
    rw [norm_sub_sq_real, real_inner_comm x v]
    ring
  rw [hn]
  ring
lemma affine_gradient_increment {E : Type*} [AddCommGroup E] [Module ℝ E]
    (g : E → E) (m μ : ℝ) (b v x : E) :
    g x+(2*m-μ) • x-(b+m • v) = (g x+(m-μ) • x-b)+m • (x-v) := by
  module

lemma proximal_corrected_fields {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ) (lam : ℝ) (center : E) (shift : F) :
    let field := fun v x => gx x v + (2*L) • (x-center)
    let dualField := fun v x => -gy x v + lam • v-shift
    (∀ v x y, (3*L)/4*‖x-y‖^2 ≤ ⟪field v x-field v y,x-y⟫) ∧
    (∀ v x y, ‖field v x-field v y‖ ≤ (3*L)*‖x-y‖) ∧
    (∀ v x y, ‖dualField v x-dualField v y‖ ≤ (3*L)*‖x-y‖) ∧
    (∀ v, field v (innerPrimal f L center v) = 0) := by
  intro field dualField
  refine ⟨?_, fun v x y => H.primalGradient_lipschitz center x y v, ?_, H.innerPrimal_stationary center⟩
  · intro v x y
    have hh := H.primalGradient_monotone center x y v
    change _ ≤ ⟪gx x v+(2*L) • (x-center)-(gx y v+(2*L) • (y-center)),x-y⟫
    nlinarith [mul_nonneg H.hL.le (sq_nonneg ‖x-y‖)]
  · intro v x y
    have he : dualField v x-dualField v y = -(gy x v-gy y v) := by dsimp [dualField]; abel
    rw [he, norm_neg]
    have hh := H.lipy x y v v
    simp only [sub_self, norm_zero, add_zero] at hh
    exact hh.trans (by nlinarith [mul_nonneg H.hL.le (norm_nonneg (x-y))])

lemma correction_update_identity {E : Type*} [AddCommGroup E] [Module ℝ E]
    (m μ : ℝ) (b v : E) :
    (2*m-μ) • v-(b+m • v) = (m-μ) • v-b := by module
lemma correction_displacement_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m lam t A : ℝ} (hm : 0 < m) (hlam : 0 ≤ lam) (hlam2 : lam ≤ 2*m)
    (ht : 0 ≤ t) (b v w : E)
    (hold : ‖lam • v-b‖ ≤ A) (hstep : m^2*‖w-v‖^2 ≤ 3*t^2) :
    ‖lam • w-b‖ ≤ A+4*t := by
  have hd : m*‖w-v‖ ≤ 2*t := by
    apply (sq_le_sq₀ (mul_nonneg hm.le (norm_nonneg _)) (by positivity)).mp
    rw [mul_pow]
    nlinarith only [hstep,sq_nonneg t]
  have he : lam • w-b = (lam • v-b)+lam • (w-v) := by module
  rw [he]
  have hh := norm_add_le (lam • v-b) (lam • (w-v))
  rw [norm_smul,Real.norm_of_nonneg hlam] at hh
  have hs := mul_le_mul_of_nonneg_right hlam2 (norm_nonneg (w-v))
  linarith only [hh,hold,hs,hd]

lemma warm_displacement_from_gaps {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q : E → ℝ} {m t : ℝ} (hm : 0 < m) (u v w : E)
    (hsc : ∀ x, m*‖x-u‖^2 ≤ q x-q u)
    (hstart : q v-q u ≤ t^2/m) (hout : q w-q u ≤ t^2/(2*m)) :
    m^2*‖w-v‖^2 ≤ 3*t^2 := by
  have hv := (hsc v).trans hstart
  have hw := (hsc w).trans hout
  have hv' := (le_div_iff₀ hm).mp hv
  have hw' := (le_div_iff₀ (show 0 < 2*m by positivity)).mp hw
  have hd := AuxiliaryInner.norm_add_sq_le (w-u) (u-v)
  rw [show (w-u)+(u-v)=w-v by abel,norm_sub_rev u v] at hd
  have hh := mul_le_mul_of_nonneg_left hd (sq_nonneg m)
  nlinarith only [hv',hw',hh]

lemma recursive_warm_initialization {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
    {q : F → ℝ} {m e : ℝ} (hm : 0 ≤ m) (he : 0 ≤ e)
    (ref : E) (v u w : F) (U : F → E) (hU : ∀ x y, ‖U x-U y‖ ≤ ‖x-y‖)
    (hmin : ∀ x, q u ≤ q x) (hgap : q v-q u ≤ e)
    (hsc : ∀ x, m*‖x-w‖^2 ≤ regularized q m v x-regularized q m v w)
    (href : m*‖ref-U v‖^2 ≤ e/128) :
    regularized q m v v-regularized q m v w ≤ e ∧
    regularized q m v v-regularized q m v w+m*‖v-w‖^2 ≤ 2*e ∧
    (2*m)*‖ref-U w‖^2 ≤ 8*e := by
  have hg : regularized q m v v-regularized q m v w ≤ e := by
    simp only [regularized, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, add_zero]
    have hn := mul_nonneg hm (sq_nonneg ‖w-v‖)
    linarith [hmin w]
  have hd := (hsc v).trans hg
  exact ⟨hg, by linarith, recursive_warm_reference hm he ref v w U hU href hd⟩

lemma cold_weighted_distance {L μ Δ G a d : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (hd : 0 ≤ d)
    (hprimal : L*a^2 ≤ Δ) (hdual : μ*d ≤ G+L*a) :
    μ*d^2 ≤ 2*G^2/μ+2*(L/μ)*Δ := by
  have hs := pow_le_pow_left₀ (mul_nonneg hμ.le hd) hdual 2
  have hp := mul_le_mul_of_nonneg_left hprimal (show 0 ≤ 2*L by positivity)
  have he : 2*G^2/μ+2*(L/μ)*Δ = (2*G^2+2*L*Δ)/μ := by ring
  rw [he,le_div_iff₀ hμ]
  nlinarith only [hs,hp,sq_nonneg (G-L*a)]
lemma cold_reset_envelope {κ X D : ℝ} (hκ : 1 ≤ κ) (hX : 0 ≤ X) (hD : D ≤ 2*κ*X) :
    (κ+1/2)*D ≤ 3*κ^2*X := by
  have hh := mul_le_mul_of_nonneg_left hD (show 0 ≤ κ+1/2 by linarith)
  have hk : κ ≤ κ^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hk hX
  nlinarith only [hh,hm]

lemma proximal_initial_primal_distance {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ Δ : ℝ}
    (H : Hyp f gx gy L μ) (x0 : E)
    (hgap : ∀ x y, ∃ y', f x0 y-f x y' ≤ Δ) (v : F)
    (hv : ∀ y, f (primal f L x0) y ≤ f (primal f L x0) v)
    (hu : innerPrimal f L x0 v = primal f L x0) :
    L*‖primal f L x0-x0‖^2 ≤ Δ := by
  have hm := weakProx_min H.hL
    (continuous_iff_continuousAt.mpr (fun x => (H.hgx x v).differentiableAt.continuousAt))
    (H.slice_weak v) x0 (Set.mem_univ x0)
  change f (innerPrimal f L x0 v) v+L*‖innerPrimal f L x0 v-x0‖^2 ≤ f x0 v+L*‖x0-x0‖^2 at hm
  rw [hu] at hm
  simp only [sub_self,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero,add_zero] at hm
  obtain ⟨y,hy⟩ := hgap (primal f L x0) v
  linarith [hv y]

lemma proximal_initial_dual_distance {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ G : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (x0 p : E) (y0 v : F) (hv : gy p v = 0) (hG : ‖gy x0 y0‖ ≤ G) :
    μ*‖y0-v‖ ≤ G+L*‖p-x0‖ := by
  have hd := OracleTemplate.NearZeroSum.strong_residual_distance (C := Set.univ)
    (A := fun y => -gy p y) (ρ := μ)
    (fun x _ y _ => HeavyTailSaddleGeometry.dual_antimonotone (hsc p) x y)
    (u := y0) (s := v) (n := (0:F)) (Set.mem_univ _) (Set.mem_univ _)
    (by intro w hw; simp)
    (by rw [hv]; intro w hw; simp)
  simp only [add_zero,norm_neg] at hd
  have hl := H.lipy p x0 y0 y0
  simp only [sub_self,norm_zero,add_zero] at hl
  have hh := norm_le_norm_sub_add (gy p y0) (gy x0 y0)
  linarith

lemma proximal_initial_energy {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ Δ G : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (x0 : E) (y0 : F) (hgap : ∀ x y, ∃ y', f x0 y-f x y' ≤ Δ)
    (hG : ‖gy x0 y0‖ ≤ G) :
    ∃ v, gy (innerPrimal f L x0 v) v = 0 ∧
      μ*‖x0-innerPrimal f L x0 v‖^2 ≤ 3*(L/μ)^2*(Δ+G^2/μ) ∧
      -dual f L x0 y0-(-dual f L x0 v)+μ/2*‖y0-v‖^2 ≤ 3*(L/μ)^2*(Δ+G^2/μ) := by
  obtain ⟨v,hmax,hU,_⟩ := H.saddle_exists x0
  have hz := H.max_gradient_zero hmax
  have hzu : gy (innerPrimal f L x0 v) v = 0 := by rw [hU]; exact hz
  have hx := proximal_initial_primal_distance H x0 hgap v hmax hU
  have hd := proximal_initial_dual_distance H hsc x0 (primal f L x0) y0 v hz hG
  have hD := cold_weighted_distance H.hμ H.hL.le (norm_nonneg (y0-v)) hx hd
  let κ := L/μ
  let X := Δ+G^2/μ
  have hk : 1 ≤ κ := (le_div_iff₀ H.hμ).mpr (by simpa using H.hμL)
  have hΔ : 0 ≤ Δ := (mul_nonneg H.hL.le (sq_nonneg _)).trans hx
  have hs : 0 ≤ G^2/μ := div_nonneg (sq_nonneg G) H.hμ.le
  have hX : 0 ≤ X := add_nonneg hΔ hs
  have hD' : μ*‖y0-v‖^2 ≤ 2*κ*X := by
    have hh := mul_nonneg (sub_nonneg.mpr hk) hs
    have he : 2*κ*X = (2*G^2/μ+2*κ*Δ)+2*((κ-1)*(G^2/μ)) := by dsimp [X]; ring
    rw [he]
    exact hD.trans (le_add_of_nonneg_right (mul_nonneg (by norm_num) hh))
  have hr := cold_reset_envelope hk hX hD'
  have he : (L+μ/2)*‖y0-v‖^2 = (κ+1/2)*(μ*‖y0-v‖^2) := by
    dsimp [κ]
    field_simp [ne_of_gt H.hμ]
  have hqg (y : F) : HasGradientAt (fun y => -dual f L x0 y)
      (-gy (innerPrimal f L x0 y) y) y := OracleTemplate.TwoSidedPL.hasGradientAt_neg' (H.dual_hasGradient x0 y)
  have hql (y y' : F) : ‖-gy (innerPrimal f L x0 y) y - -gy (innerPrimal f L x0 y') y'‖ ≤ 2*L*‖y-y'‖ := by
    rw [neg_sub_neg,norm_sub_rev]
    exact H.dual_gradient_lipschitz x0 y y'
  have hupper := OracleTemplate.Gradient.smooth_upper_bound hqg hql v y0
  rw [hzu,neg_zero,inner_zero_left] at hupper
  have hR : Δ ≤ 3*κ^2*X := by
    have hm := mul_nonneg (show 0 ≤ 3*κ^2-1 by nlinarith) hX
    have hdx : Δ ≤ X := le_add_of_nonneg_right hs
    nlinarith only [hm,hdx]
  refine ⟨v,hzu,?_,?_⟩
  · rw [hU,norm_sub_rev x0]
    exact ((mul_le_mul_of_nonneg_right H.hμL (sq_nonneg _)).trans hx).trans hR
  · rw [← he] at hr
    change _ ≤ 3*κ^2*X
    linarith

lemma proximal_saddle_shift {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (c c' x x' : E) (y y' : F)
    (hx : gx x y+(2*L) • (x-c) = 0) (hy : gy x y = 0)
    (hx' : gx x' y'+(2*L) • (x'-c') = 0) (hy' : gy x' y' = 0) :
    L*‖x-x'‖^2+μ*‖y-y'‖^2 ≤ 4*L*‖c-c'‖^2 := by
  let q := fun u v => LongTails.Setups.WeaklyConvexHeavyTailed.proxObj (fun z => f z v) L c u
  have hpx (u u' : E) (v : F) : q u v+⟪gx u v+(2*L) • (u-c),u'-u⟫+L/2*‖u'-u‖^2 ≤ q u' v :=
    proxObj_lower (H.slice_weak v) c u u'
  have hpy (u : E) (v v' : F) : q u v' ≤ q u v+⟪gy u v,v'-v⟫-μ/2*‖v'-v‖^2 := by
    dsimp [q,LongTails.Setups.WeaklyConvexHeavyTailed.proxObj]
    linarith only [hsc u v v']
  have hh := OracleTemplate.NearZeroSum.saddle_monotonicity_of_support
    (hpx x x' y) (hpx x' x y') (hpy x y y') (hpy x' y' y)
  have he : gx x' y'+(2*L) • (x'-c) = (2*L) • (c'-c) := by
    calc
      _ = (gx x' y'+(2*L) • (x'-c'))+(2*L) • (c'-c) := by module
      _ = _ := by rw [hx',zero_add]
  rw [hx,he,hy,hy',sub_self,inner_zero_left,sub_zero,zero_sub] at hh
  have hn : -((2*L) • (c'-c)) = (2*L) • (c-c') := by module
  rw [hn,real_inner_smul_left] at hh
  exact HeavyTailSaddleGeometry.saddle_shift_energy H.hL.le H.hμ.le (x-x') (c-c') (y-y') hh

open LongTails.Setups.StochasticTwoSidedPL LongTails.Setups.WeaklyConvexHeavyTailed

lemma proximal_joint_gap_bound {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ) (c x : E) (y : F) :
    proxObj (maxValue f) L c x-dual f L c y ≤
      ‖gx x y+(2*L) • (x-c)‖^2/(2*L)+‖gy x y‖^2/(2*μ) := by
  have hx := proxObj_gap_bound H.hL (H.slice_weak y) c x (innerPrimal f L c y)
  obtain ⟨v,hv⟩ := H.attain x
  have hp := H.ply x y v
  have hy : maxValue f x-f x y ≤ ‖gy x y‖^2/(2*μ) := by
    rw [H.max_value_eq hv,le_div_iff₀ (by linarith [H.hμ])]
    linarith
  change f x y+L*‖x-c‖^2-dual f L c y ≤ _ at hx
  change maxValue f x+L*‖x-c‖^2-dual f L c y ≤ _
  linarith
lemma proximal_joint_gap_energy {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ ζ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (c x u : E) (y v : F)
    (hu : gx u v+(2*L) • (u-c) = 0) (hv : gy u v = 0)
    (hgap : proxObj (maxValue f) L c x-dual f L c y ≤ ζ) :
    L*‖x-u‖^2+μ*‖y-v‖^2 ≤ 2*ζ := by
  have hx := proxObj_lower (H.slice_weak v) c u x
  rw [hu,inner_zero_left,add_zero] at hx
  have hy := hsc u v y
  rw [hv,inner_zero_left,add_zero] at hy
  have hmin := weakProx_min H.hL
    (continuous_iff_continuousAt.mpr (fun z => (H.hgx z y).differentiableAt.continuousAt))
    (H.slice_weak y) c (Set.mem_univ u)
  change dual f L c y ≤ f u y+L*‖u-c‖^2 at hmin
  have hmax := H.le_max_value x v
  dsimp only [proxObj] at hx hgap
  linarith

lemma proximal_energy_from_weighted {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ W : ℝ}
    (H : Hyp f gx gy L μ) (c ref : E) (start u : F)
    (hu : gy (innerPrimal f L c u) u = 0)
    (hw : L*‖ref-innerPrimal f L c u‖^2+μ*‖start-u‖^2 ≤ W) :
    μ*‖ref-innerPrimal f L c u‖^2 ≤ (L/μ+1/2)*W ∧
    -dual f L c start-(-dual f L c u)+μ/2*‖start-u‖^2 ≤ (L/μ+1/2)*W := by
  have hx := mul_nonneg H.hL.le (sq_nonneg ‖ref-innerPrimal f L c u‖)
  have hy := mul_nonneg H.hμ.le (sq_nonneg ‖start-u‖)
  have hW : 0 ≤ W := (add_nonneg hx hy).trans hw
  have hk : 1 ≤ L/μ := (le_div_iff₀ H.hμ).mpr (by simpa using H.hμL)
  have hqg (y : F) : HasGradientAt (fun y => -dual f L c y)
      (-gy (innerPrimal f L c y) y) y := OracleTemplate.TwoSidedPL.hasGradientAt_neg' (H.dual_hasGradient c y)
  have hql (y y' : F) : ‖-gy (innerPrimal f L c y) y - -gy (innerPrimal f L c y') y'‖ ≤ 2*L*‖y-y'‖ := by
    rw [neg_sub_neg,norm_sub_rev]
    exact H.dual_gradient_lipschitz c y y'
  have hupper := OracleTemplate.Gradient.smooth_upper_bound hqg hql u start
  rw [hu,neg_zero,inner_zero_left] at hupper
  constructor
  · have hl := mul_le_mul_of_nonneg_right H.hμL (sq_nonneg ‖ref-innerPrimal f L c u‖)
    have hm := mul_nonneg (show 0 ≤ L/μ+1/2-1 by linarith) hW
    nlinarith only [hl,hw,hy,hm]
  · have hd : μ*‖start-u‖^2 ≤ W := by linarith only [hw,hx]
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ L/μ+1/2 by linarith)
    have he : (L/μ+1/2)*(μ*‖start-u‖^2) = (L+μ/2)*‖start-u‖^2 := by
      field_simp [ne_of_gt H.hμ]
    rw [he] at hh
    linarith

lemma proximal_warm_energy {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ ζ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (c c' ref : E) (start : F)
    (hgap : proxObj (maxValue f) L c ref-dual f L c start ≤ ζ) :
    ∃ v, gy (innerPrimal f L c' v) v = 0 ∧
      μ*‖ref-innerPrimal f L c' v‖^2 ≤ (L/μ+1/2)*(4*ζ+8*L*‖c-c'‖^2) ∧
      -dual f L c' start-(-dual f L c' v)+μ/2*‖start-v‖^2 ≤ (L/μ+1/2)*(4*ζ+8*L*‖c-c'‖^2) := by
  obtain ⟨v,hv,hU,_⟩ := H.saddle_exists c
  obtain ⟨v',hv',hU',_⟩ := H.saddle_exists c'
  have hy := H.max_gradient_zero hv
  have hy' := H.max_gradient_zero hv'
  have hx : gx (primal f L c) v+(2*L) • (primal f L c-c) = 0 := by
    rw [← hU]
    exact H.innerPrimal_stationary c v
  have hx' : gx (primal f L c') v'+(2*L) • (primal f L c'-c') = 0 := by
    rw [← hU']
    exact H.innerPrimal_stationary c' v'
  have hold := proximal_joint_gap_energy H hsc c ref (primal f L c) start v hx hy hgap
  have hshift := proximal_saddle_shift H hsc c c' (primal f L c) (primal f L c') v v' hx hy hx' hy'
  have hw := HeavyTailSaddleGeometry.warm_start_energy H.hL.le H.hμ.le
    ref (primal f L c) (primal f L c') start v v' hold hshift
  have hzero : gy (innerPrimal f L c' v') v' = 0 := by rw [hU']; exact hy'
  refine ⟨v',hzero,?_⟩
  apply proximal_energy_from_weighted H c' ref start v' hzero
  simpa only [hU'] using hw
lemma warm_public_envelope {κ ζ L Δ d : ℝ} (hκ : 1 ≤ κ) (hζ : 0 ≤ ζ) (hΔ : 0 ≤ Δ)
    (T : ℕ) (hmove : L*d^2 ≤ Δ+T*ζ) :
    (κ+1/2)*(4*ζ+8*L*d^2) ≤ 12*κ*(Δ+(T+1)*ζ) := by
  have hN : 0 ≤ Δ+(T+1)*ζ := by positivity
  have hW : 4*ζ+8*L*d^2 ≤ 8*(Δ+(T+1)*ζ) := by nlinarith only [hmove,hζ]
  have h1 := mul_le_mul_of_nonneg_left hW (show 0 ≤ κ+1/2 by linarith)
  have h2 := mul_le_mul_of_nonneg_right (show κ+1/2 ≤ 3*κ/2 by linarith) (mul_nonneg (by norm_num : (0:ℝ)≤8) hN)
  have he : (3*κ/2)*(8*(Δ+(T+1)*ζ)) = 12*κ*(Δ+(T+1)*ζ) := by ring
  exact h1.trans (h2.trans_eq he)

lemma proximal_fine_initial_energy {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ ζ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2)
    (hζ : 0 ≤ ζ) (c ref : E) (start : F)
    (hgap : proxObj (maxValue f) L c ref-dual f L c start ≤ ζ) :
    ∃ v, gy (innerPrimal f L c v) v = 0 ∧
      μ*‖ref-innerPrimal f L c v‖^2 ≤ 3*(L/μ)*ζ ∧
      -dual f L c start-(-dual f L c v)+μ/2*‖start-v‖^2 ≤ 3*(L/μ)*ζ := by
  obtain ⟨v,hv,hU,_⟩ := H.saddle_exists c
  have hy := H.max_gradient_zero hv
  have hx : gx (primal f L c) v+(2*L) • (primal f L c-c) = 0 := by
    rw [← hU]
    exact H.innerPrimal_stationary c v
  have hw := proximal_joint_gap_energy H hsc c ref (primal f L c) start v hx hy hgap
  have hzero : gy (innerPrimal f L c v) v = 0 := by rw [hU]; exact hy
  have hh := proximal_energy_from_weighted H c ref start v hzero (by simpa only [hU] using hw)
  have hk : 1 ≤ L/μ := (le_div_iff₀ H.hμ).mpr (by simpa using H.hμL)
  have he : (L/μ+1/2)*(2*ζ) ≤ 3*(L/μ)*ζ := by
    have hn := mul_nonneg (sub_nonneg.mpr hk) hζ
    nlinarith only [hn]
  exact ⟨v,hzero,hh.1.trans he,hh.2.trans he⟩

lemma recovery_mass_ge {μ : ℝ} (hμ : 0 ≤ μ) (j : ℕ) : μ ≤ recoveryMass μ j := by
  have hh := mul_le_mul_of_nonneg_right (one_le_pow₀ (show (1:ℝ)≤2 by norm_num) (n := j)) hμ
  simpa only [one_mul,recoveryMass] using hh
lemma recovery_refinement_envelopes {L μ ζ : ℝ} (hμ : 0 < μ) (hζ : 0 < ζ)
    (initialBound : ℝ) (j : ℕ) :
    let B := recoveryEnvelope L μ ζ initialBound j
    let K := recoveryHalvings L μ ζ initialBound j
    let e := recoveryTarget L μ ζ j
    0 < B ∧ 0 < K ∧ refinementEnvelope B K ≤ e ∧
      e/2 ≤ refinementEnvelope B (K-1) ∧ refinementEnvelope B (K-1) ≤ 2*e := by
  intro B K e
  cases j with
  | zero =>
    have he := recovery_target_pos (L := L) hμ hζ 0
    have hh := refinement_floored_envelope (B := initialBound) he
    have ht := refinement_steps_tuning (B := max initialBound (recoveryTarget L μ ζ 0)) he
    change 0 < max initialBound (recoveryTarget L μ ζ 0) ∧ _
    refine ⟨hh.1,?_,?_,?_,?_⟩
    · simpa only [K,recoveryHalvings,recoveryEnvelope,ite_true] using ht.1
    · change refinementEnvelope (max initialBound (recoveryTarget L μ ζ 0))
        (refinementSteps (max initialBound (recoveryTarget L μ ζ 0)) (recoveryTarget L μ ζ 0)) ≤ recoveryTarget L μ ζ 0
      exact ht.2.2.trans (by linarith)
    · simpa only [B,K,e,recoveryHalvings,recoveryEnvelope,ite_true] using hh.2.2.1
    · have hb := hh.2.2.2
      change refinementEnvelope (max initialBound (recoveryTarget L μ ζ 0))
        (refinementSteps (max initialBound (recoveryTarget L μ ζ 0)) (recoveryTarget L μ ζ 0)-1) ≤ 2*recoveryTarget L μ ζ 0
      exact hb.trans (by linarith)
  | succ j =>
    have he := recovery_target_pos (L := L) hμ hζ (j+1)
    have hh := recovery_warm_envelopes L μ ζ initialBound j
    have hB : 0 < B := by
      change 0 < recoveryEnvelope L μ ζ initialBound (j+1)
      simp only [recoveryEnvelope,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel]
      exact mul_pos (by norm_num) (recovery_target_pos (L := L) hμ hζ j)
    have hK : K=4 := hh.1
    refine ⟨hB,by omega,?_,?_,?_⟩
    · change refinementEnvelope (recoveryEnvelope L μ ζ initialBound (j+1)) K ≤ recoveryTarget L μ ζ (j+1)
      rw [hK,hh.2.1]
    · change recoveryTarget L μ ζ (j+1)/2 ≤ refinementEnvelope (recoveryEnvelope L μ ζ initialBound (j+1)) (K-1)
      rw [hK]
      norm_num only at *
      rw [hh.2.2]
      linarith
    · change refinementEnvelope (recoveryEnvelope L μ ζ initialBound (j+1)) (K-1) ≤ 2*recoveryTarget L μ ζ (j+1)
      rw [hK]
      norm_num only
      exact hh.2.2.le

lemma affine_warm_initialization {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (base : F → ℝ) {m μ e : ℝ} (hm : 0 ≤ m) (he : 0 ≤ e)
    (b : F) (ref : E) (v u w : F) (U : F → E) (hU : ∀ x y, ‖U x-U y‖ ≤ ‖x-y‖) :
    let q := fun x => base x+(m-μ)/2*‖x‖^2-⟪b,x⟫
    let qnext := fun x => base x+(2*m-μ)/2*‖x‖^2-⟪b+m • v,x⟫
    (∀ x, q u ≤ q x) → q v-q u ≤ e →
    (∀ x, m*‖x-w‖^2 ≤ qnext x-qnext w) → m*‖ref-U v‖^2 ≤ e/128 →
    qnext v-qnext w ≤ e ∧ qnext v-qnext w+m*‖v-w‖^2 ≤ 2*e ∧
      (2*m)*‖ref-U w‖^2 ≤ 8*e := by
  intro q qnext hmin hgap hsc href
  have hrel (x : F) : qnext x = regularized q m v x-m/2*‖v‖^2 :=
    affine_regularized_increment base m μ b v x
  have hsc' (x : F) : m*‖x-w‖^2 ≤ regularized q m v x-regularized q m v w := by
    have hh := hsc x
    rw [hrel x,hrel w] at hh
    linarith only [hh]
  have hh := recursive_warm_initialization hm he ref v u w U hU hmin hgap hsc' href
  refine ⟨?_,?_,hh.2.2⟩
  · rw [hrel v,hrel w]
    linarith only [hh.1]
  · rw [hrel v,hrel w]
    linarith only [hh.2.1]

noncomputable def recoveryShiftedObjective {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (base : F → ℝ) (μ : ℝ) (j : ℕ) (b v : F) : ℝ :=
  base v+(recoveryMass μ j-μ)/2*‖v‖^2-⟪b,v⟫
noncomputable def recoveryShiftedGradient {F : Type*} [AddCommGroup F] [Module ℝ F]
    (base : F → F) (μ : ℝ) (j : ℕ) (b v : F) : F :=
  base v+(recoveryMass μ j-μ) • v-b
noncomputable def recoveryGood {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (base : F → ℝ) (U : F → E) (root : ℕ → F → F) (L μ ζ initialBound : ℝ) (j : ℕ) :
    Set ((E × F) × F) :=
  {s | recoveryMass μ j*‖s.1.1-U (root j s.2)‖^2 ≤ recoveryEnvelope L μ ζ initialBound j ∧
    recoveryShiftedObjective base μ j s.2 s.1.2-recoveryShiftedObjective base μ j s.2 (root j s.2)+
      recoveryMass μ j/2*‖s.1.2-root j s.2‖^2 ≤ recoveryEnvelope L μ ζ initialBound j ∧
    (0 < j → recoveryShiftedObjective base μ j s.2 s.1.2-recoveryShiftedObjective base μ j s.2 (root j s.2) ≤
      recoveryTarget L μ ζ (j-1)) ∧
    ‖(recoveryMass μ j-μ) • s.1.2-s.2‖ ≤ 4*(j-1:ℕ)*recoveryScale L μ ζ}
noncomputable def recoveryCertificate {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (base : F → F) (U : F → E) (L μ ζ : ℝ) (j : ℕ) : Set ((E × F) × F) :=
  {s | (recoveryMass μ j)^2*‖s.1.1-U s.1.2‖^2 ≤ (recoveryScale L μ ζ)^2/128 ∧
    ‖recoveryShiftedGradient base μ (j+1) s.2 s.1.2‖^2 ≤
      2*recoverySmoothness L μ j*recoveryTarget L μ ζ j}
lemma recovery_shifted_objective_measurable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {base : F → ℝ} (hb : Measurable base) (μ : ℝ) (j : ℕ) :
    Measurable (Function.uncurry (recoveryShiftedObjective base μ j)) := by
  unfold recoveryShiftedObjective
  fun_prop
lemma recovery_good_measurable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {base : F → ℝ} {U : F → E} {root : ℕ → F → F}
    (hb : Measurable base) (hU : Measurable U) (hr : ∀ j, Measurable (root j))
    (L μ ζ initialBound : ℝ) (j : ℕ) : MeasurableSet (recoveryGood base U root L μ ζ initialBound j) := by
  have hq := recovery_shifted_objective_measurable hb μ j
  have hgap : Measurable (fun s : (E × F) × F =>
      recoveryShiftedObjective base μ j s.2 s.1.2-recoveryShiftedObjective base μ j s.2 (root j s.2)) :=
    (hq.comp (measurable_snd.prodMk measurable_fst.snd)).sub
      (hq.comp (measurable_snd.prodMk ((hr j).comp measurable_snd)))
  have h1 := measurableSet_le
    (show Measurable (fun s : (E × F) × F => recoveryMass μ j*‖s.1.1-U (root j s.2)‖^2) by fun_prop)
    (measurable_const (a := recoveryEnvelope L μ ζ initialBound j))
  have h2 := measurableSet_le
    (hgap.add (show Measurable (fun s : (E × F) × F => recoveryMass μ j/2*‖s.1.2-root j s.2‖^2) by fun_prop))
    (measurable_const (a := recoveryEnvelope L μ ζ initialBound j))
  have h3 : MeasurableSet {s : (E × F) × F | 0 < j →
      recoveryShiftedObjective base μ j s.2 s.1.2-recoveryShiftedObjective base μ j s.2 (root j s.2) ≤ recoveryTarget L μ ζ (j-1)} := by
    by_cases hj : 0 < j
    · simpa only [hj,true_implies] using measurableSet_le hgap (measurable_const (a := recoveryTarget L μ ζ (j-1)))
    · simp only [hj,false_implies,Set.ofPred_true]
      exact MeasurableSet.univ
  have h4 := measurableSet_le
    (show Measurable (fun s : (E × F) × F => ‖(recoveryMass μ j-μ) • s.1.2-s.2‖) by fun_prop)
    (measurable_const (a := 4*(j-1:ℕ)*recoveryScale L μ ζ))
  exact h1.inter (h2.inter (h3.inter h4))
lemma recovery_certificate_measurable {E F : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {base : F → F} {U : F → E} (hb : Measurable base) (hU : Measurable U)
    (L μ ζ : ℝ) (j : ℕ) : MeasurableSet (recoveryCertificate base U L μ ζ j) := by
  have h1 := measurableSet_le
    (show Measurable (fun s : (E × F) × F => (recoveryMass μ j)^2*‖s.1.1-U s.1.2‖^2) by fun_prop)
    (measurable_const (a := (recoveryScale L μ ζ)^2/128))
  have h2 := measurableSet_le
    (show Measurable (fun s : (E × F) × F => ‖recoveryShiftedGradient base μ (j+1) s.2 s.1.2‖^2) by
      unfold recoveryShiftedGradient
      fun_prop)
    (measurable_const (a := 2*recoverySmoothness L μ j*recoveryTarget L μ ζ j))
  exact h1.inter h2

lemma recovery_terminal_residual {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (objective : F → ℝ) (gradient : F → F) (U : F → E) (root : ℕ → F → F)
    {L μ ζ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 15*L) (hζ : 0 < ζ)
    (initialBound : ℝ) (state : (E × F) × F)
    (hgood : state ∈ recoveryGood objective U root L μ ζ initialBound (recoveryStages L μ))
    (hcert : state ∈ recoveryCertificate gradient U L μ ζ (recoveryStages L μ-1)) :
    ‖gradient state.1.2‖ ≤ 4*recoveryStages L μ*recoveryScale L μ ζ ∧
    (recoveryMass μ (recoveryStages L μ-1))^2*‖state.1.1-U state.1.2‖^2 ≤ (recoveryScale L μ ζ)^2/128 := by
  let J := recoveryStages L μ
  let K := J-1
  let m := recoveryMass μ K
  let t := recoveryScale L μ ζ
  have hJ : 0 < J := by dsimp [J,recoveryStages]; omega
  have hK : K+1=J := by dsimp [K]; omega
  have hm : 0 < m := recovery_mass_pos hμ K
  have ht : 0 ≤ t := by dsimp [t,recoveryScale]; positivity
  have he : 0 ≤ recoveryTarget L μ ζ K := (recovery_target_pos hμ hζ K).le
  have hmass := (recovery_terminal_mass hμ hμL).1
  have hH : recoverySmoothness L μ K ≤ 2*m := by
    dsimp [recoverySmoothness,m,K,J] at *
    linarith
  have hscale : 2*(2*m)*recoveryTarget L μ ζ K = 4*t^2 := by
    dsimp [recoveryTarget,t,m]
    field_simp [ne_of_gt (recovery_mass_pos hμ K)]
    ring
  have hg2 := hcert.2
  change ‖recoveryShiftedGradient gradient μ (K+1) state.2 state.1.2‖^2 ≤
    2*recoverySmoothness L μ K*recoveryTarget L μ ζ K at hg2
  rw [hK] at hg2
  have hmul := mul_le_mul_of_nonneg_right hH he
  have hnorm : ‖recoveryShiftedGradient gradient μ J state.2 state.1.2‖ ≤ 2*t := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith only [hg2,hmul,hscale]
  have hcor := hgood.2.2.2
  change ‖(recoveryMass μ J-μ) • state.1.2-state.2‖ ≤ 4*K*t at hcor
  have heq : gradient state.1.2 = recoveryShiftedGradient gradient μ J state.2 state.1.2-
      ((recoveryMass μ J-μ) • state.1.2-state.2) := by unfold recoveryShiftedGradient; module
  have hnormbase := norm_sub_le (recoveryShiftedGradient gradient μ J state.2 state.1.2)
    ((recoveryMass μ J-μ) • state.1.2-state.2)
  rw [← heq] at hnormbase
  have hcast : (K:ℝ)+1=J := by exact_mod_cast hK
  refine ⟨?_,hcert.1⟩
  change ‖gradient state.1.2‖ ≤ 4*J*t
  nlinarith only [hnormbase,hnorm,hcor,hcast,ht]

lemma recovery_terminal_joint_gap {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ ζ : ℝ}
    (H : Hyp f gx gy L μ) (hζ : 0 < ζ) (center : E)
    (root : ℕ → F → F) (initialBound : ℝ) (state : (E × F) × F) :
    let U := innerPrimal f L center
    state ∈ recoveryGood (fun v => -dual f L center v) U root L μ ζ initialBound (recoveryStages L μ) →
    state ∈ recoveryCertificate (fun v => -gy (U v) v) U L μ ζ (recoveryStages L μ-1) →
    proxObj (maxValue f) L center state.1.1-dual f L center state.1.2 ≤ ζ/100 := by
  intro U hgood hcert
  let J := recoveryStages L μ
  let K := J-1
  let m := recoveryMass μ K
  let t := recoveryScale L μ ζ
  let D := ‖state.1.1-U state.1.2‖
  have hJ : (1:ℝ) ≤ J := by
    have hh : 1 ≤ J := by dsimp [J,recoveryStages]; omega
    exact_mod_cast hh
  have ht : 0 ≤ t := by dsimp [t,recoveryScale]; positivity
  have hm : 0 < m := recovery_mass_pos H.hμ K
  have hthreshold : μ ≤ 15*L := by linarith [H.hμL,H.hL]
  have hmass := (recovery_terminal_mass H.hμ hthreshold).1
  have hLm : 3*L ≤ m := by dsimp [m,K,J]; linarith [H.hL]
  have hres := recovery_terminal_residual (fun v => -dual f L center v) (fun v => -gy (U v) v) U root
    H.hμ hthreshold hζ initialBound state hgood hcert
  have hbase : ‖gy (U state.1.2) state.1.2‖ ≤ 4*J*t := by simpa only [norm_neg] using hres.1
  have hx : ‖gx state.1.1 state.1.2+(2*L) • (state.1.1-center)‖ ≤ (3*L)*D := by
    have hh := H.primalGradient_lipschitz center state.1.1 (U state.1.2) state.1.2
    have hz := H.innerPrimal_stationary center state.1.2
    change gx (U state.1.2) state.1.2+(2*L) • (U state.1.2-center) = 0 at hz
    simpa only [hz,sub_zero] using hh
  have hy : ‖gy state.1.1 state.1.2‖ ≤ 4*J*t+(3*L)*D := by
    have hl := H.lipy state.1.1 (U state.1.2) state.1.2 state.1.2
    simp only [sub_self,norm_zero,add_zero] at hl
    have hh := norm_le_norm_sub_add (gy state.1.1 state.1.2) (gy (U state.1.2) state.1.2)
    have hn : 0 ≤ L*D := mul_nonneg H.hL.le (norm_nonneg _)
    change ‖gy state.1.1 state.1.2-gy (U state.1.2) state.1.2‖ ≤ L*D at hl
    linarith
  have hh := recursive_gap_certificate (α := L) (μ := μ) (L := 3*L) (m := m) (D := D) (t := t) (J := (J:ℝ))
    H.hL H.hμ hm hLm (by linarith [H.hμL,H.hL]) (norm_nonneg _) ht hJ hres.2
    (norm_nonneg _) (norm_nonneg _) hx hy (proximal_joint_gap_bound H center state.1.1 state.1.2)
  exact hh.trans (recursive_gap_tuning H.hμ hζ hJ)

lemma recovery_correction_step {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (base : F → ℝ) (U : F → E) (root : ℕ → F → F)
    {L μ ζ : ℝ} (hμ : 0 < μ) (hζ : 0 < ζ) (initialBound : ℝ) (j : ℕ)
    (state : (E × F) × F) (v : F)
    (hgood : state ∈ recoveryGood base U root L μ ζ initialBound j)
    (hsc : ∀ x, recoveryMass μ j/2*‖x-root j state.2‖^2 ≤
      recoveryShiftedObjective base μ j state.2 x-recoveryShiftedObjective base μ j state.2 (root j state.2))
    (hgap : recoveryShiftedObjective base μ j state.2 v-recoveryShiftedObjective base μ j state.2 (root j state.2) ≤
      recoveryTarget L μ ζ j) :
    ‖(recoveryMass μ (j+1)-μ) • v-(state.2+recoveryMass μ j • v)‖ ≤ 4*j*recoveryScale L μ ζ := by
  have he : (recoveryMass μ (j+1)-μ) • v-(state.2+recoveryMass μ j • v) =
      (recoveryMass μ j-μ) • v-state.2 := by
    rw [recovery_mass_succ]
    exact correction_update_identity (recoveryMass μ j) μ state.2 v
  rw [he]
  have ht : 0 ≤ recoveryScale L μ ζ := by unfold recoveryScale; positivity
  cases j with
  | zero =>
    have hh := hgood.2.2.2
    simpa only [recoveryMass,pow_zero,one_mul,sub_self,zero_smul,zero_sub,Nat.cast_zero,mul_zero,zero_mul,Nat.sub_zero,Nat.zero_sub] using hh
  | succ j =>
    have hm := recovery_mass_pos hμ j
    have hstart := hgood.2.2.1 (Nat.zero_lt_succ j)
    have hsc' (x : F) : recoveryMass μ j*‖x-root (j+1) state.2‖^2 ≤
        recoveryShiftedObjective base μ (j+1) state.2 x-recoveryShiftedObjective base μ (j+1) state.2 (root (j+1) state.2) := by
      have hh := hsc x
      rw [recovery_mass_succ] at hh
      convert hh using 1; ring
    have hd := warm_displacement_from_gaps hm (root (j+1) state.2) state.1.2 v hsc'
      (by simpa only [Nat.add_sub_cancel,recoveryTarget] using hstart)
      (by simpa only [recoveryTarget,recovery_mass_succ] using hgap)
    have hlow : 0 ≤ recoveryMass μ (j+1)-μ := sub_nonneg.mpr (recovery_mass_ge hμ.le (j+1))
    have hhi : recoveryMass μ (j+1)-μ ≤ 2*recoveryMass μ j := by rw [recovery_mass_succ]; linarith
    have hh := correction_displacement_bound hm hlow hhi ht state.2 state.1.2 v hgood.2.2.2 hd
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at hh ⊢
    nlinarith only [hh]

lemma recovery_root_maps {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2) (center : E) :
    let U := innerPrimal f L center
    let base := fun v => -dual f L center v
    let gradient := fun v => -gy (U v) v
    ∃ root : ℕ → F → F,
      (∀ j b, recoveryShiftedGradient gradient μ j b (root j b) = 0) ∧
      (∀ j, Measurable (root j)) ∧
      (∀ j b v, recoveryShiftedObjective base μ j b (root j b) ≤ recoveryShiftedObjective base μ j b v) := by
  intro U base gradient
  have hex (j : ℕ) := proximal_regularized_stationary_map H hsc
    (sub_nonneg.mpr (recovery_mass_ge H.hμ.le j))
  choose r hz hmin hlip using hex
  refine ⟨fun j b => r j (center,b),fun j b => hz j (center,b),?_,fun j b v => hmin j (center,b) v⟩
  intro j
  exact ((hlip j).continuous.comp (continuous_const.prodMk continuous_id)).measurable
lemma recovery_stage_geometry {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μ : ℝ}
    (H : Hyp f gx gy L μ)
    (hsc : ∀ x y y', f x y' ≤ f x y+⟪gy x y,y'-y⟫-μ/2*‖y'-y‖^2) (center : E) (j : ℕ) (b : F) :
    let U := innerPrimal f L center
    let q := recoveryShiftedObjective (fun v => -dual f L center v) μ j b
    let g := recoveryShiftedGradient (fun v => -gy (U v) v) μ j b
    (∀ v, HasGradientAt q (g v) v) ∧
    (∀ v w, q v+⟪g v,w-v⟫+recoveryMass μ j/2*‖w-v‖^2 ≤ q w) ∧
    (∀ v w, ‖g v-g w‖ ≤ recoverySmoothness L μ j*‖v-w‖) := by
  intro U q g
  have hh := proximal_regularized_dual_geometry H hsc (sub_nonneg.mpr (recovery_mass_ge H.hμ.le j)) center b
  have he : μ+(recoveryMass μ j-μ)=recoveryMass μ j := by ring
  refine ⟨hh.1,?_,?_⟩
  · have hs := hh.2.1
    dsimp only at hs
    rw [he] at hs
    exact hs
  · intro v w
    have hl := hh.2.2.1 v w
    exact hl.trans (mul_le_mul_of_nonneg_right
      (by unfold recoverySmoothness; linarith [H.hL]) (norm_nonneg _))

lemma recovery_stage_preserves {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (base : F → ℝ) (gradient : F → F) (U : F → E) (root : ℕ → F → F)
    {L μ ζ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 15*L) (hζ : 0 < ζ)
    (hU : ∀ x y, ‖U x-U y‖ ≤ ‖x-y‖)
    (initialBound : ℝ) (j : ℕ) (state : (E × F) × F) (out : E × F)
    (hgood : state ∈ recoveryGood base U root L μ ζ initialBound j) :
    let m := recoveryMass μ j
    let B := recoveryEnvelope L μ ζ initialBound j
    let K := recoveryHalvings L μ ζ initialBound j
    let bnext := state.2+m • out.2
    let q := recoveryShiftedObjective base μ j state.2
    let qnext := recoveryShiftedObjective base μ (j+1) bnext
    (∀ x, HasGradientAt q (recoveryShiftedGradient gradient μ j state.2 x) x) →
    (∀ x y, ‖recoveryShiftedGradient gradient μ j state.2 x-recoveryShiftedGradient gradient μ j state.2 y‖ ≤
      recoverySmoothness L μ j*‖x-y‖) →
    (∀ x, m/2*‖x-root j state.2‖^2 ≤ q x-q (root j state.2)) →
    (∀ x, m*‖x-root (j+1) bnext‖^2 ≤ qnext x-qnext (root (j+1) bnext)) →
    q out.2-q (root j state.2)+m/2*‖out.2-root j state.2‖^2 ≤ refinementEnvelope B K →
    ‖out.1-U out.2‖ ≤ Real.sqrt (refinementEnvelope B (K-1)/m)/16 →
    (out,bnext) ∈ recoveryGood base U root L μ ζ initialBound (j+1) ∧
    (out,bnext) ∈ recoveryCertificate gradient U L μ ζ j := by
  intro m B K bnext q qnext hqg hql hcur hnext henergy hdirect
  let e := recoveryTarget L μ ζ j
  have hm : 0 < m := recovery_mass_pos hμ j
  have he : 0 < e := recovery_target_pos hμ hζ j
  have henv := recovery_refinement_envelopes (L := L) hμ hζ initialBound j
  have hgap : q out.2-q (root j state.2) ≤ e := by
    have hn := mul_nonneg (show 0 ≤ m/2 by positivity) (sq_nonneg ‖out.2-root j state.2‖)
    have hh := henv.2.2.1
    change refinementEnvelope B K ≤ e at hh
    linarith only [henergy,hn,hh]
  have hmin (x : F) : q (root j state.2) ≤ q x := by
    have hh := hcur x
    have hn := mul_nonneg (show 0 ≤ m/2 by positivity) (sq_nonneg ‖x-root j state.2‖)
    linarith only [hh,hn]
  have hentry : refinementEnvelope B (K-1) ≤ 2*(recoveryScale L μ ζ)^2/m := by
    have hh := henv.2.2.2.2
    change refinementEnvelope B (K-1) ≤ 2*e at hh
    simpa only [e,recoveryTarget,mul_div_assoc] using hh
  have hd2 := terminal_reference_scale hm
    (refinement_envelope_pos henv.1 (K-1)).le (norm_nonneg _) hentry hdirect
  have href : m*‖out.1-U out.2‖^2 ≤ e/128 := by
    have heq : e/128 = ((recoveryScale L μ ζ)^2/128)/m := by dsimp [e,recoveryTarget,m]; ring
    rw [heq,le_div_iff₀ hm]
    nlinarith only [hd2]
  have hnext' (x : F) : m*‖x-root (j+1) bnext‖^2 ≤
      (base x+(2*m-μ)/2*‖x‖^2-⟪state.2+m • out.2,x⟫)-
      (base (root (j+1) bnext)+(2*m-μ)/2*‖root (j+1) bnext‖^2-⟪state.2+m • out.2,root (j+1) bnext⟫) := by
    simpa only [qnext,recoveryShiftedObjective,recovery_mass_succ,bnext] using hnext x
  have hw := affine_warm_initialization base hm.le he.le state.2 out.1 out.2 (root j state.2)
    (root (j+1) bnext) U hU hmin hgap hnext' href
  have hnewgap : qnext out.2-qnext (root (j+1) bnext) ≤ e := by
    simpa only [qnext,recoveryShiftedObjective,recovery_mass_succ,bnext] using hw.1
  have hnewreset : qnext out.2-qnext (root (j+1) bnext)+m*‖out.2-root (j+1) bnext‖^2 ≤ 2*e := by
    simpa only [qnext,recoveryShiftedObjective,recovery_mass_succ,bnext] using hw.2.1
  have hcor := recovery_correction_step base U root hμ hζ initialBound j state out.2 hgood hcur hgap
  have hnewB : recoveryEnvelope L μ ζ initialBound (j+1)=8*e := by
    simp only [recoveryEnvelope,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,Nat.add_sub_cancel]
    rfl
  have hmnext : recoveryMass μ (j+1)=2*m := recovery_mass_succ μ j
  have hmhalf : recoveryMass μ (j+1)/2=m := by rw [hmnext]; ring
  have hH : 0 < recoverySmoothness L μ j := by
    change 0 < 15*L+m-μ
    linarith
  have hg2 := OracleTemplate.ComponentEnvelope.smooth_gradient_gap hH hqg hql hmin out.2
  have hgBound := hg2.trans (mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2*recoverySmoothness L μ j by positivity))
  have hgEqual : recoveryShiftedGradient gradient μ (j+1) bnext out.2 =
      recoveryShiftedGradient gradient μ j state.2 out.2 := by
    unfold recoveryShiftedGradient
    rw [hmnext]
    dsimp [bnext]
    module
  constructor
  · change recoveryMass μ (j+1)*‖out.1-U (root (j+1) bnext)‖^2 ≤ _ ∧
      qnext out.2-qnext (root (j+1) bnext)+recoveryMass μ (j+1)/2*‖out.2-root (j+1) bnext‖^2 ≤ _ ∧ _ ∧ _
    rw [hnewB,hmhalf,hmnext]
    refine ⟨hw.2.2,?_,?_,?_⟩
    · linarith only [hnewreset,he]
    · intro hj
      simpa only [Nat.add_sub_cancel] using hnewgap
    · simpa only [Nat.add_sub_cancel,recovery_mass_succ] using hcor
  · change _ ∧ ‖recoveryShiftedGradient gradient μ (j+1) bnext out.2‖^2 ≤ _
    exact ⟨hd2,by rw [hgEqual]; exact hgBound⟩

lemma strongly_convex_stationary_unique {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {q : F → ℝ} {g : F → F} {m : ℝ} (hm : 0 < m)
    (hsc : ∀ x y, q x+⟪g x,y-x⟫+m/2*‖y-x‖^2 ≤ q y)
    {x y : F} (hx : g x=0) (hy : g y=0) : x=y := by
  have h1 := hsc x y
  have h2 := hsc y x
  rw [hx,inner_zero_left,add_zero,norm_sub_rev y x] at h1
  rw [hy,inner_zero_left,add_zero] at h2
  have hh : m*‖x-y‖^2 ≤ 0 := by linarith only [h1,h2]
  have hd : ‖x-y‖^2 ≤ 0 := by
    have hh' : ‖x-y‖^2 ≤ 0/m := (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hh)
    simpa only [zero_div] using hh'
  have hz : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)
lemma recovery_initial_good {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (base : F → ℝ) (U : F → E) (root : ℕ → F → F)
    (L μ ζ initialBound : ℝ) (initial : E × F) (u : F) (hr : root 0 0=u)
    (href : μ*‖initial.1-U u‖^2 ≤ initialBound)
    (hstart : base initial.2-base u+μ/2*‖initial.2-u‖^2 ≤ initialBound) :
    (initial,0) ∈ recoveryGood base U root L μ ζ initialBound 0 := by
  have h1 := href.trans (le_max_left initialBound (recoveryTarget L μ ζ 0))
  have h2 := hstart.trans (le_max_left initialBound (recoveryTarget L μ ζ 0))
  simpa [recoveryGood,recoveryShiftedObjective,recoveryMass,recoveryEnvelope,hr] using And.intro h1 h2

end LongTails.Proofs.HeavyTailSaddleRecovery
