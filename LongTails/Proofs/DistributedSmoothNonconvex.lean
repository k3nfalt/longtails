import LongTails.Setups.DistributedSmoothNonconvex
import LongTails.Proofs.GdConvex
import LongTails.Proofs.Clipping
import LongTails.Proofs.DistributedQuantization

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.DistributedSmoothNonconvex

open LongTails.Setups.DistributedSmoothNonconvex

variable {p : Params} {f : Point p → ℝ}

lemma initial_gradient_bound
    (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x)
    (hgap : f p.x0 - lower ≤ p.Δ) :
    ‖gradient f p.x0‖ ^ 2 ≤ 2 * p.L * p.Δ := by
  have hd := OracleTemplate.Gradient.descent hL hg hlip p.x0
  have hb := hlower (p.x0 - (1 / p.L) • gradient f p.x0)
  have h : ‖gradient f p.x0‖ ^ 2 / (2 * p.L) ≤ p.Δ := by linarith
  have hden : 0 < 2 * p.L := by positivity
  nlinarith [(div_le_iff₀ hden).mp h]

lemma inexact_descent
    (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (x g : Point p) :
    f (x - (1 / p.L) • g) ≤ f x - ‖gradient f x‖ ^ 2 / (2 * p.L) +
      ‖g - gradient f x‖ ^ 2 / (2 * p.L) := by
  have h := OracleTemplate.Gradient.smooth_upper_bound hg hlip x (x - (1 / p.L) • g)
  have he : x - (1 / p.L) • g - x = -(1 / p.L) • g := by module
  rw [he] at h
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (one_div_pos.mpr hL)] at h
  convert h using 1
  rw [norm_sub_sq_real, real_inner_comm g (gradient f x)]
  field_simp [ne_of_gt hL]
  ring

lemma trajectory_gradient_bound
    (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x)
    (hgap : f p.x0 - lower ≤ p.Δ)
    (x g : ℕ → Point p) (hstart : x 0 = p.x0)
    (hstep : ∀ k, x (k + 1) = x k - (1 / p.L) • g k) (K : ℕ) :
    (∑ k ∈ Finset.range K, ‖gradient f (x k)‖ ^ 2) ≤ 2 * p.L * p.Δ +
      ∑ k ∈ Finset.range K, ‖g k - gradient f (x k)‖ ^ 2 := by
  have henergy : ∀ m, f (x m) +
      (∑ k ∈ Finset.range m, ‖gradient f (x k)‖ ^ 2) / (2 * p.L) ≤
      f p.x0 + (∑ k ∈ Finset.range m, ‖g k - gradient f (x k)‖ ^ 2) / (2 * p.L) := by
    intro m
    induction m with
    | zero => simp [hstart]
    | succ m ih =>
        have hd := inexact_descent hL hg hlip (x m) (g m)
        rw [← hstep m] at hd
        rw [Finset.sum_range_succ, Finset.sum_range_succ, add_div, add_div]
        linarith
  have hden : 0 < 2 * p.L := by positivity
  have hbound :
      ((∑ k ∈ Finset.range K, ‖gradient f (x k)‖ ^ 2) -
        ∑ k ∈ Finset.range K, ‖g k - gradient f (x k)‖ ^ 2) / (2 * p.L) ≤ p.Δ := by
    rw [sub_div]
    linarith [henergy K, hlower (x K)]
  nlinarith [(div_le_iff₀ hden).mp hbound]

lemma decoded_gradient_bound
    (hL : 0 ≤ p.L)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (x decoded : Point p) :
    ‖gradient f decoded‖ ^ 2 ≤ 2 * ‖gradient f x‖ ^ 2 +
      2 * p.L ^ 2 * ‖decoded - x‖ ^ 2 := by
  have htriangle : ‖gradient f decoded‖ ≤
      ‖gradient f x‖ + p.L * ‖decoded - x‖ := by
    calc
      ‖gradient f decoded‖ ≤ ‖gradient f decoded - gradient f x‖ +
          ‖gradient f x‖ := by
        simpa using norm_add_le (gradient f decoded - gradient f x) (gradient f x)
      _ ≤ ‖gradient f x‖ + p.L * ‖decoded - x‖ := by
        linarith [hlip decoded x]
  have hn : 0 ≤ p.L * ‖decoded - x‖ := mul_nonneg hL (norm_nonneg _)
  nlinarith [sq_nonneg (‖gradient f x‖ - p.L * ‖decoded - x‖),
    sq_nonneg (‖gradient f x‖ + p.L * ‖decoded - x‖ - ‖gradient f decoded‖),
    mul_nonneg (sub_nonneg.mpr htriangle)
      (add_nonneg (norm_nonneg (gradient f decoded))
        (add_nonneg (norm_nonneg (gradient f x)) hn))]

lemma trajectory_step_energy
    (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x)
    (hgap : f p.x0 - lower ≤ p.Δ)
    (x g : ℕ → Point p) (hstart : x 0 = p.x0)
    (hstep : ∀ k, x (k + 1) = x k - (1 / p.L) • g k) (K : ℕ) :
    (∑ k ∈ Finset.range K, ‖g k‖ ^ 2) ≤ 4 * p.L * p.Δ +
      4 * ∑ k ∈ Finset.range K, ‖g k - gradient f (x k)‖ ^ 2 := by
  have hpoint (k : ℕ) : ‖g k‖ ^ 2 ≤
      2 * ‖gradient f (x k)‖ ^ 2 + 2 * ‖g k - gradient f (x k)‖ ^ 2 := by
    have hsq := sq_nonneg ‖g k - (2 : ℝ) • gradient f (x k)‖
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right] at hsq
    norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hsq
    rw [norm_sub_sq_real]
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.range K) (fun k _ => hpoint k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hgradient := trajectory_gradient_bound hL hg hlip lower hlower hgap x g hstart hstep K
  linarith

lemma expected_trajectory_gradient_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x)
    (hgap : f p.x0 - lower ≤ p.Δ)
    (x g : Ω → ℕ → Point p) (hstart : ∀ ω, x ω 0 = p.x0)
    (hstep : ∀ ω k, x ω (k + 1) = x ω k - (1 / p.L) • g ω k)
    (K : ℕ)
    (hx : ∀ k < K, Integrable (fun ω => ‖gradient f (x ω k)‖ ^ 2) P)
    (he : ∀ k < K, Integrable (fun ω => ‖g ω k - gradient f (x ω k)‖ ^ 2) P) :
    (∑ k ∈ Finset.range K, ∫ ω, ‖gradient f (x ω k)‖ ^ 2 ∂P) ≤
      2 * p.L * p.Δ + ∑ k ∈ Finset.range K, ∫ ω, ‖g ω k - gradient f (x ω k)‖ ^ 2 ∂P := by
  have hxi : Integrable (fun ω => ∑ k ∈ Finset.range K, ‖gradient f (x ω k)‖ ^ 2) P :=
    integrable_finsetSum _ (fun k hk => hx k (Finset.mem_range.mp hk))
  have hei : Integrable (fun ω => ∑ k ∈ Finset.range K,
      ‖g ω k - gradient f (x ω k)‖ ^ 2) P :=
    integrable_finsetSum _ (fun k hk => he k (Finset.mem_range.mp hk))
  have hbound := integral_mono hxi ((integrable_const (2 * p.L * p.Δ)).add hei)
    (fun ω => trajectory_gradient_bound hL hg hlip lower hlower hgap
      (x ω) (g ω) (hstart ω) (hstep ω) K)
  simp only [Pi.add_apply] at hbound
  rw [integral_add (integrable_const _) hei, integral_const] at hbound
  simp only [probReal_univ, one_smul] at hbound
  rw [integral_finsetSum _ (fun k hk => hx k (Finset.mem_range.mp hk)),
    integral_finsetSum _ (fun k hk => he k (Finset.mem_range.mp hk))] at hbound
  exact hbound

lemma expected_trajectory_gradient_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x)
    (hgap : f p.x0 - lower ≤ p.Δ)
    (x g : Ω → ℕ → Point p) (hstart : ∀ ω, x ω 0 = p.x0)
    (hstep : ∀ ω k, x ω (k + 1) = x ω k - (1 / p.L) • g ω k)
    (K : ℕ) (V : ℝ)
    (hx : ∀ k < K, Integrable (fun ω => ‖gradient f (x ω k)‖ ^ 2) P)
    (he : ∀ k < K, Integrable (fun ω => ‖g ω k - gradient f (x ω k)‖ ^ 2) P)
    (herr : ∀ k < K, ∫ ω, ‖g ω k - gradient f (x ω k)‖ ^ 2 ∂P ≤ V) :
    (∑ k ∈ Finset.range K, ∫ ω, ‖gradient f (x ω k)‖ ^ 2 ∂P) ≤
      2 * p.L * p.Δ + K * V := by
  have hbound := expected_trajectory_gradient_error P hL hg hlip lower hlower hgap
    x g hstart hstep K hx he
  have hsum := Finset.sum_le_sum (s := Finset.range K)
    (fun k hk => herr k (Finset.mem_range.mp hk))
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  linarith

lemma trajectory_displacement (hL : 0 < p.L)
    (x g : ℕ → Point p) (hstart : x 0 = p.x0)
    (hstep : ∀ k, x (k + 1) = x k - (1 / p.L) • g k) (K : ℕ) :
    ‖x K - p.x0‖ ^ 2 ≤ (1 / p.L) ^ 2 * K *
      ∑ k ∈ Finset.range K, ‖g k‖ ^ 2 := by
  have hpath : ∀ m, x m - p.x0 = ∑ k ∈ Finset.range m, -(1 / p.L) • g k := by
    intro m
    induction m with
    | zero => simp [hstart]
    | succ m ih =>
        rw [hstep, Finset.sum_range_succ, ← ih]
        module
  have hnorm : ‖x K - p.x0‖ ≤ (1 / p.L) * ∑ k ∈ Finset.range K, ‖g k‖ := by
    rw [hpath]
    calc
      _ ≤ ∑ k ∈ Finset.range K, ‖-(1 / p.L) • g k‖ := norm_sum_le _ _
      _ = _ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_neg,
          abs_of_pos (one_div_pos.mpr hL), Finset.mul_sum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range K)
    (fun _ => (1 : ℝ)) (fun k => ‖g k‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one] at hcs
  have hsq := mul_self_le_mul_self (norm_nonneg _) hnorm
  have hscaled := mul_le_mul_of_nonneg_left hcs (sq_nonneg (1 / p.L))
  nlinarith

lemma expected_displacement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (x g : Ω → ℕ → Point p) (hstart : ∀ ω, x ω 0 = p.x0)
    (hstep : ∀ ω k, x ω (k + 1) = x ω k - (1 / p.L) • g ω k)
    (K k : ℕ) (hk : k ≤ K) (hx : Measurable (fun ω => x ω k))
    (he : ∀ j < K, Integrable (fun ω => ‖g ω j - gradient f (x ω j)‖ ^ 2) P) :
    Integrable (fun ω => ‖x ω k - p.x0‖ ^ 2) P ∧
      (∫ ω, ‖x ω k - p.x0‖ ^ 2 ∂P) ≤ (1 / p.L) ^ 2 * K *
        (4 * p.L * p.Δ + 4 * ∑ j ∈ Finset.range K, ∫ ω, ‖g ω j - gradient f (x ω j)‖ ^ 2 ∂P) := by
  have hpoint (ω : Ω) : ‖x ω k - p.x0‖ ^ 2 ≤ (1 / p.L) ^ 2 * K *
      (4 * p.L * p.Δ + 4 * ∑ j ∈ Finset.range K, ‖g ω j - gradient f (x ω j)‖ ^ 2) := by
    have hd := trajectory_displacement hL (x ω) (g ω) (hstart ω) (hstep ω) k
    have henergy := trajectory_step_energy hL hg hlip lower hlower hgap
      (x ω) (g ω) (hstart ω) (hstep ω) K
    have hprefix : (∑ j ∈ Finset.range k, ‖g ω j‖ ^ 2) ≤
        ∑ j ∈ Finset.range K, ‖g ω j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) (fun _ _ _ => sq_nonneg _)
    have hscale : (1 / p.L) ^ 2 * k ≤ (1 / p.L) ^ 2 * K :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hk) (sq_nonneg _)
    have hproduct := mul_le_mul hscale hprefix (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    exact hd.trans (hproduct.trans (mul_le_mul_of_nonneg_left henergy (by positivity)))
  have hsum : Integrable (fun ω => ∑ j ∈ Finset.range K,
      ‖g ω j - gradient f (x ω j)‖ ^ 2) P :=
    integrable_finsetSum _ (fun j hj => he j (Finset.mem_range.mp hj))
  have hbound := ((integrable_const (4 * p.L * p.Δ)).add (hsum.const_mul 4)).const_mul
    ((1 / p.L) ^ 2 * K)
  simp only [Pi.add_apply] at hbound
  have hI : Integrable (fun ω => ‖x ω k - p.x0‖ ^ 2) P :=
    hbound.mono' ((hx.sub_const p.x0).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, abs_sq] using hpoint ω)
  refine ⟨hI, (integral_mono hI hbound hpoint).trans_eq ?_⟩
  rw [integral_const_mul, integral_add (integrable_const _) (hsum.const_mul 4),
    integral_const, integral_const_mul,
    integral_finsetSum _ (fun j hj => he j (Finset.mem_range.mp hj))]
  simp

lemma self_consistent_error (K : ℕ) (e d : ℕ → ℝ) (a c A B : ℝ)
    (hc : 0 ≤ c) (he : ∀ k < K, 0 ≤ e k)
    (hd : ∀ k < K, d k ≤ A + B * ∑ j ∈ Finset.range K, e j)
    (herr : ∀ k < K, e k ≤ a + c * d k)
    (hsmall : 2 * K * c * B ≤ 1) :
    (∑ k ∈ Finset.range K, e k) ≤ 2 * K * (a + c * A) := by
  have hpoint (k : ℕ) (hk : k ∈ Finset.range K) :
      e k ≤ a + c * (A + B * ∑ j ∈ Finset.range K, e j) :=
    (herr k (Finset.mem_range.mp hk)).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (hd k (Finset.mem_range.mp hk)) hc) a)
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hnonneg : 0 ≤ ∑ k ∈ Finset.range K, e k :=
    Finset.sum_nonneg (fun k hk => he k (Finset.mem_range.mp hk))
  have hscaled := mul_le_mul_of_nonneg_right hsmall hnonneg
  nlinarith

lemma expected_gradient_feedback {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (x g : Ω → ℕ → Point p) (hstart : ∀ ω, x ω 0 = p.x0)
    (hstep : ∀ ω k, x ω (k + 1) = x ω k - (1 / p.L) • g ω k)
    (K : ℕ) (a c : ℝ) (hc : 0 ≤ c)
    (hxm : ∀ k < K, Measurable (fun ω => x ω k))
    (hx : ∀ k < K, Integrable (fun ω => ‖gradient f (x ω k)‖ ^ 2) P)
    (he : ∀ k < K, Integrable (fun ω => ‖g ω k - gradient f (x ω k)‖ ^ 2) P)
    (herr : ∀ k < K, (∫ ω, ‖g ω k - gradient f (x ω k)‖ ^ 2 ∂P) ≤
      a + c * ∫ ω, ‖x ω k - p.x0‖ ^ 2 ∂P)
    (hsmall : 8 * (K : ℝ) ^ 2 * c ≤ p.L ^ 2)
    (hbase : a + 4 * c * K * p.Δ / p.L ≤ p.ε / 4)
    (hbudget : 4 * p.L * p.Δ ≤ K * p.ε) :
    (∑ k ∈ Finset.range K, ∫ ω, ‖gradient f (x ω k)‖ ^ 2 ∂P) ≤ K * p.ε := by
  let e := fun k => ∫ ω, ‖g ω k - gradient f (x ω k)‖ ^ 2 ∂P
  let d := fun k => ∫ ω, ‖x ω k - p.x0‖ ^ 2 ∂P
  let A := (1 / p.L) ^ 2 * K * (4 * p.L * p.Δ)
  let B := (1 / p.L) ^ 2 * K * 4
  have hd (k : ℕ) (hk : k < K) : d k ≤ A + B * ∑ j ∈ Finset.range K, e j := by
    have h := (expected_displacement P hL hg hlip lower hlower hgap x g hstart hstep
      K k hk.le (hxm k hk) he).2
    dsimp [d, A, B, e]
    convert h using 1
    ring
  have hsmall' : 2 * K * c * B ≤ 1 := by
    dsimp [B]
    have heq : 2 * K * c * ((1 / p.L) ^ 2 * K * 4) =
        (8 * (K : ℝ) ^ 2 * c) / p.L ^ 2 := by ring
    rw [heq]
    exact (div_le_one (sq_pos_of_pos hL)).mpr hsmall
  have hsum := self_consistent_error K e d a c A B hc
    (fun k _ => integral_nonneg (fun _ => sq_nonneg _)) hd herr hsmall'
  have hbase' : a + c * A ≤ p.ε / 4 := by
    have heq : c * A = 4 * c * K * p.Δ / p.L := by
      dsimp [A]
      field_simp [ne_of_gt hL]
    rwa [heq]
  have herror : (∑ k ∈ Finset.range K, e k) ≤ K * p.ε / 2 := by
    have h := mul_le_mul_of_nonneg_left hbase' (by positivity : (0 : ℝ) ≤ 2 * K)
    linarith
  have hgrad := expected_trajectory_gradient_error P hL hg hlip lower hlower hgap
    x g hstart hstep K hx he
  change (∑ k ∈ Finset.range K, ∫ ω, ‖gradient f (x ω k)‖ ^ 2 ∂P) ≤
    2 * p.L * p.Δ + ∑ k ∈ Finset.range K, e k at hgrad
  linarith

lemma norm_add_square (a b : Point p) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := mul_self_le_mul_self (norm_nonneg (a + b)) (norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

end LongTails.Proofs.DistributedSmoothNonconvex
