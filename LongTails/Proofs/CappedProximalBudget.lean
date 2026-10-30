import LongTails.Proofs.CappedProximalParameters
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.CappedProximalBudget

open LongTails.Setups.CappedHessianSimilarConvex
open LongTails.Algorithms.CappedProximal
open CappedProximalParameters

lemma outer_length_upper {p : Params} (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    (outerLength p : ℝ) ≤ 9 * Real.sqrt (outerRegularization p / p.μ) := by
  have hr : p.μ ≤ outerRegularization p := by
    exact le_add_of_nonneg_right (div_nonneg hd (Real.sqrt_nonneg _))
  have hratio : 1 ≤ outerRegularization p / p.μ := (le_div_iff₀ hm).2 (by simpa using hr)
  have hs : 1 ≤ Real.sqrt (outerRegularization p / p.μ) := Real.one_le_sqrt.mpr hratio
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 8 * Real.sqrt (outerRegularization p / p.μ) by positivity)
  change (⌈8 * Real.sqrt (outerRegularization p / p.μ)⌉₊ : ℝ) ≤ _
  linarith

lemma epoch_length_upper {p : Params} (hs : 0 < p.s) (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    (epochLength p : ℝ) ≤ 2 + 64 * Real.sqrt (p.δ * (1 + Real.sqrt p.m / p.s) / subproblemConvexity p) +
      2 ^ 20 * p.δ ^ 2 / (p.s * subproblemConvexity p ^ 2) := by
  have hq := subproblem_convexity_pos hm hd
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 1 + 64 * Real.sqrt
    (p.δ * (1 + Real.sqrt p.m / p.s) / subproblemConvexity p) +
      2 ^ 20 * p.δ ^ 2 / (p.s * subproblemConvexity p ^ 2) by positivity)
  change (⌈_⌉₊ : ℝ) ≤ _
  linarith

lemma sqrt_affine_bound {m d : ℝ} (hm : 1 ≤ m) (hd : 0 ≤ d) :
    Real.sqrt (2 + d / Real.sqrt m) ≤ 2 + Real.sqrt d / Real.sqrt (Real.sqrt m) := by
  have hm0 : 0 < m := by linarith
  have ht : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hb : 0 < Real.sqrt (Real.sqrt m) := Real.sqrt_pos.mpr ht
  have hb2 := Real.sq_sqrt ht.le
  have hd2 := Real.sq_sqrt hd
  have hr : 0 ≤ 2 + d / Real.sqrt m := by positivity
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · have he : (Real.sqrt d / Real.sqrt (Real.sqrt m)) ^ 2 = d / Real.sqrt m := by
      rw [div_pow, hd2, hb2]
    nlinarith [sq_nonneg (Real.sqrt d / Real.sqrt (Real.sqrt m)),
      div_nonneg (Real.sqrt_nonneg d) hb.le]

lemma sqrt_cohort_bound {m s d : ℝ} (hm : 1 ≤ m) (hs : 0 < s) (hsm : s ≤ m) (hd : 0 ≤ d) :
    Real.sqrt (d * (1 + Real.sqrt m / s)) ≤
      (1 + Real.sqrt (m * Real.sqrt m) / s) * Real.sqrt d := by
  have hm0 : 0 < m := by linarith
  have ht : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hb : 0 ≤ Real.sqrt (m * Real.sqrt m) := Real.sqrt_nonneg _
  have hb2 := Real.sq_sqrt (mul_nonneg hm0.le ht.le)
  have hd2 := Real.sq_sqrt hd
  have hms : s * Real.sqrt m ≤ m * Real.sqrt m := mul_le_mul_of_nonneg_right hsm ht.le
  have hbfrac : Real.sqrt m / s ≤ (Real.sqrt (m * Real.sqrt m) / s) ^ 2 := by
    rw [div_pow, hb2]
    apply (div_le_div_iff₀ hs (sq_pos_of_pos hs)).2
    nlinarith [mul_le_mul_of_nonneg_right hms hs.le]
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · rw [mul_pow, hd2]
    nlinarith [mul_le_mul_of_nonneg_right hbfrac hd,
      mul_nonneg (div_nonneg hb hs.le) hd]

lemma noise_ratio_bound {t Q d : ℝ} (ht : 0 ≤ t) (hQ : 0 < Q) (hd : 0 ≤ d)
    (hdQ : d ≤ Q * t) :
    d ^ 2 / (Q * Real.sqrt Q) ≤ t * Real.sqrt t * Real.sqrt d := by
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have h1 : d / Q ≤ t := (div_le_iff₀ hQ).2 (by simpa only [mul_comm] using hdQ)
  have h2 : Real.sqrt d / Real.sqrt Q ≤ Real.sqrt t := by
    apply (div_le_iff₀ hsQ).2
    have hh := Real.sqrt_le_sqrt hdQ
    rw [Real.sqrt_mul hQ.le] at hh
    simpa only [mul_comm] using hh
  have hp := mul_le_mul h1 h2 (div_nonneg (Real.sqrt_nonneg d) hsQ.le) ht
  have hp' := mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg d)
  have hid : d / Q * (Real.sqrt d / Real.sqrt Q) * Real.sqrt d = d ^ 2 / (Q * Real.sqrt Q) := by
    field_simp
    nlinarith only [Real.sq_sqrt hd]
  rwa [hid] at hp'

lemma restart_count_upper {p : Params} (hD : 0 ≤ p.Δ) (he : 0 < p.ε) :
    (restartCount p : ℝ) ≤ 2 * (1 + Real.log (2 + p.Δ / p.ε)) := by
  have hz : 1 ≤ 2 + p.Δ / p.ε := by linarith [div_nonneg hD he.le]
  have hlog := Real.log_nonneg hz
  have h8 : 1 ≤ Real.log (8 : ℝ) := by
    apply (Real.le_log_iff_exp_le (by norm_num)).2
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  have hc := Nat.ceil_lt_add_one (div_nonneg hlog (by linarith : 0 ≤ Real.log (8 : ℝ)))
  have hdiv : Real.log (2 + p.Δ / p.ε) / Real.log 8 ≤ Real.log (2 + p.Δ / p.ε) :=
    div_le_self hlog h8
  change ((1 + ⌈Real.log (2 + p.Δ / p.ε) / Real.log 8⌉₊ : ℕ) : ℝ) ≤ _
  push_cast
  linarith

lemma dimension_root_identity {m : ℝ} (hm : 0 ≤ m) :
    Real.sqrt (m * Real.sqrt m) = Real.sqrt m * Real.sqrt (Real.sqrt m) := by
  rw [Real.sqrt_mul hm]

lemma snapshot_factor_bound {m s d : ℝ} (hm : 1 ≤ m) (hs : 0 < s) (hd : 0 ≤ d) :
    m / s * Real.sqrt (2 + d / Real.sqrt m) ≤
      2 * (m / s) + Real.sqrt (m * Real.sqrt m) / s * Real.sqrt d := by
  have hm0 : 0 < m := by linarith
  have ht : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hb : 0 < Real.sqrt (Real.sqrt m) := Real.sqrt_pos.mpr ht
  have hp := mul_le_mul_of_nonneg_left (sqrt_affine_bound hm hd) (div_nonneg hm0.le hs.le)
  have hid : m / s * (2 + Real.sqrt d / Real.sqrt (Real.sqrt m)) =
      2 * (m / s) + Real.sqrt (m * Real.sqrt m) / s * Real.sqrt d := by
    rw [dimension_root_identity hm0.le]
    have hi : Real.sqrt (Real.sqrt m) ^ 2 * Real.sqrt m = m := by
      rw [Real.sq_sqrt ht.le]
      simpa only [pow_two] using Real.sq_sqrt hm0.le
    field_simp
    nlinarith only [congrArg (fun x : ℝ => Real.sqrt d * x) hi]
  rwa [hid] at hp

lemma normalized_noise_bound {m d : ℝ} (hm : 1 ≤ m) (hd : 0 ≤ d) :
    d ^ 2 / ((2 + d / Real.sqrt m) * Real.sqrt (2 + d / Real.sqrt m)) ≤
      Real.sqrt (m * Real.sqrt m) * Real.sqrt d := by
  have hm0 : 0 < m := by linarith
  have ht : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hQ : 0 < 2 + d / Real.sqrt m := by positivity
  have hdQ : d ≤ (2 + d / Real.sqrt m) * Real.sqrt m := by
    rw [add_mul, div_mul_cancel₀ _ ht.ne']
    linarith
  simpa only [dimension_root_identity hm0.le] using noise_ratio_bound ht.le hQ hd hdQ

lemma normalized_cost_bound {m s d K h T : ℝ} (hm : 1 ≤ m) (hs : 0 < s)
    (hsm : s ≤ m) (hd : 0 ≤ d) (hT0 : 0 ≤ T) (hh0 : 0 ≤ h)
    (hK : K ≤ 9 * Real.sqrt (2 + d / Real.sqrt m)) (hh : h ≤ 2 * (m / s))
    (hT : T ≤ 2 + 64 * Real.sqrt (d * (1 + Real.sqrt m / s) / (2 + d / Real.sqrt m)) +
      2 ^ 20 * d ^ 2 / (s * (2 + d / Real.sqrt m) ^ 2)) :
    K * (h + 3 * T) ≤ 2 ^ 25 *
      (1 + m / s + (1 + Real.sqrt (m * Real.sqrt m) / s) * Real.sqrt d) := by
  let Q := 2 + d / Real.sqrt m
  let A := d * (1 + Real.sqrt m / s)
  have hm0 : 0 < m := by linarith
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hr : 1 ≤ m / s := (le_div_iff₀ hs).2 (by simpa using hsm)
  have hbase : h + 6 ≤ 8 * (m / s) := by linarith
  have hc := mul_le_mul hK (add_le_add le_rfl (mul_le_mul_of_nonneg_left hT (by norm_num : (0 : ℝ) ≤ 3)))
    (by positivity : 0 ≤ h + 3 * T) (by positivity : 0 ≤ 9 * Real.sqrt Q)
  have hc' := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 9 * Real.sqrt Q by positivity)
  have hroot : Real.sqrt Q * Real.sqrt (A / Q) = Real.sqrt A := by
    rw [Real.sqrt_div hA]
    field_simp
  have hnoise : Real.sqrt Q * (d ^ 2 / Q ^ 2) = d ^ 2 / (Q * Real.sqrt Q) := by
    field_simp
    nlinarith only [Real.sq_sqrt hQ.le]
  have hmid : K * (h + 3 * T) ≤ 72 * (m / s * Real.sqrt Q) +
      1728 * Real.sqrt A + (27 * 2 ^ 20 / s) * (d ^ 2 / (Q * Real.sqrt Q)) := by
    dsimp only [Q, A] at hroot hnoise ⊢
    dsimp only [Q] at hc'
    have he : 9 * Real.sqrt (2 + d / Real.sqrt m) *
        (h + 3 * (2 + 64 * Real.sqrt (d * (1 + Real.sqrt m / s) / (2 + d / Real.sqrt m)) +
          2 ^ 20 * d ^ 2 / (s * (2 + d / Real.sqrt m) ^ 2))) =
        9 * Real.sqrt (2 + d / Real.sqrt m) * (h + 6) +
          1728 * Real.sqrt (2 + d / Real.sqrt m) *
            Real.sqrt (d * (1 + Real.sqrt m / s) / (2 + d / Real.sqrt m)) +
          (27 * 2 ^ 20 / s) * (Real.sqrt (2 + d / Real.sqrt m) *
            (d ^ 2 / (2 + d / Real.sqrt m) ^ 2)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he, mul_assoc (1728 : ℝ), hroot, hnoise] at hc
    nlinarith only [hc, hc']
  have h1 := snapshot_factor_bound hm hs hd
  have h2 := sqrt_cohort_bound hm hs hsm hd
  have h3 := mul_le_mul_of_nonneg_left (normalized_noise_bound hm hd)
    (show 0 ≤ 27 * 2 ^ 20 / s by positivity)
  dsimp only [Q, A] at hmid
  have hr0 : 0 ≤ m / s := by positivity
  have hf0 : 0 ≤ Real.sqrt (m * Real.sqrt m) / s * Real.sqrt d := by positivity
  have he3 : (27 * 2 ^ 20 / s) * (Real.sqrt (m * Real.sqrt m) * Real.sqrt d) =
      (27 * 2 ^ 20) * (Real.sqrt (m * Real.sqrt m) / s * Real.sqrt d) := by ring
  rw [he3] at h3
  nlinarith only [hmid, h1, h2, h3, hr0, hf0, Real.sqrt_nonneg d]

lemma snapshot_length_upper {p : Params} (hs : 0 < p.s) (hsm : p.s ≤ p.m) :
    (snapshotLength p : ℝ) ≤ 2 * ((p.m : ℝ) / p.s) := by
  have hsR : 0 < (p.s : ℝ) := by exact_mod_cast hs
  have hsmR : (p.s : ℝ) ≤ p.m := by exact_mod_cast hsm
  have hn : p.m + p.s - 1 ≤ p.m + p.s := Nat.sub_le _ _
  have hc : ((p.m + p.s - 1 : ℕ) : ℝ) ≤ (p.m : ℝ) + p.s := by exact_mod_cast hn
  have hb : ((p.m + p.s - 1 : ℕ) : ℝ) / p.s ≤ ((p.m : ℝ) + p.s) / p.s :=
    div_le_div_of_nonneg_right hc hsR.le
  have hd : ((p.m : ℝ) + p.s) / p.s ≤ 2 * ((p.m : ℝ) / p.s) := by
    apply (div_le_iff₀ hsR).2
    field_simp
    linarith
  exact (Nat.cast_div_le (m := p.m + p.s - 1) (n := p.s)).trans (hb.trans hd)

lemma normalized_parameters {p : Params} (hm : 0 < p.μ) :
    outerRegularization p / p.μ = 1 + (p.δ / p.μ) / Real.sqrt p.m ∧
    subproblemConvexity p / p.μ = 2 + (p.δ / p.μ) / Real.sqrt p.m := by
  dsimp [outerRegularization, subproblemConvexity]
  constructor <;> field_simp
  ring

lemma epoch_round_cost_upper {p : Params} (hs : 0 < p.s) (hsm : p.s ≤ p.m)
    (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    (outerLength p : ℝ) * ((snapshotLength p : ℝ) + 3 * epochLength p) ≤
      2 ^ 25 * (1 + (p.m : ℝ) / p.s +
        (1 + Real.sqrt ((p.m : ℝ) * Real.sqrt p.m) / p.s) * Real.sqrt (p.δ / p.μ)) := by
  have hmR : 1 ≤ (p.m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p.m)
  have hsR : 0 < (p.s : ℝ) := by exact_mod_cast hs
  have hsmR : (p.s : ℝ) ≤ p.m := by exact_mod_cast hsm
  have hdR : 0 ≤ p.δ / p.μ := div_nonneg hd hm.le
  have hq := subproblem_convexity_pos hm hd
  have hn := normalized_parameters hm
  have hK : (outerLength p : ℝ) ≤ 9 * Real.sqrt (2 + (p.δ / p.μ) / Real.sqrt p.m) := by
    apply (outer_length_upper hm hd).trans
    rw [hn.1]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num)
  have he1 : p.δ * (1 + Real.sqrt p.m / p.s) / subproblemConvexity p =
      (p.δ / p.μ) * (1 + Real.sqrt p.m / p.s) / (2 + (p.δ / p.μ) / Real.sqrt p.m) := by
    rw [← hn.2]
    field_simp
  have he2 : p.δ ^ 2 / (p.s * subproblemConvexity p ^ 2) =
      (p.δ / p.μ) ^ 2 / (p.s * (2 + (p.δ / p.μ) / Real.sqrt p.m) ^ 2) := by
    rw [← hn.2]
    field_simp
  have hT := epoch_length_upper hs hm hd
  rw [he1] at hT
  have he2' := congrArg (fun x : ℝ => 2 ^ 20 * x) he2
  simp only [← mul_div_assoc] at he2'
  rw [he2'] at hT
  exact normalized_cost_bound hmR hsR hsmR hdR (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hK (snapshot_length_upper hs hsm) hT

lemma log_count_upper {Y : ℝ} (hY : 1 ≤ Y) :
    ((1 + ⌈Real.log Y / Real.log 8⌉₊ : ℕ) : ℝ) ≤ 2 + Real.log Y := by
  have hlog := Real.log_nonneg hY
  have h8 : 1 ≤ Real.log (8 : ℝ) := by
    apply (Real.le_log_iff_exp_le (by norm_num)).2
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  have hc := Nat.ceil_lt_add_one (div_nonneg hlog (by linarith : 0 ≤ Real.log (8 : ℝ)))
  have hdiv := div_le_self hlog h8
  push_cast
  linarith

lemma logarithmic_solve_bound {X ratio K : ℝ} (hX : 1 ≤ X) (hr1 : 1 ≤ ratio)
    (hr2 : ratio ≤ 2) (hK1 : 1 ≤ K) (hK : K ≤ 9 * Real.sqrt X) :
    ((1 + ⌈Real.log (2 ^ 20 * ratio * K ^ 4) / Real.log 8⌉₊ : ℕ) : ℝ) ≤
      64 * (1 + Real.log X) := by
  have hX0 : 0 < X := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hr0 : 0 ≤ ratio := by linarith
  have hK4 : 1 ≤ K ^ 4 := one_le_pow₀ hK1
  have hY : 1 ≤ 2 ^ 20 * ratio * K ^ 4 := by nlinarith
  have hp := pow_le_pow_left₀ hK0 hK 4
  have hs4 : (Real.sqrt X) ^ 4 = X ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hX0.le]
  rw [mul_pow, hs4] at hp
  have hrp := mul_le_mul_of_nonneg_right hr2 (pow_nonneg hK0 4)
  have hYupper : 2 ^ 20 * ratio * K ^ 4 ≤ (2 : ℝ) ^ 34 * X ^ 2 := by
    nlinarith [sq_nonneg X]
  have hlog := Real.log_le_log (by linarith : 0 < 2 ^ 20 * ratio * K ^ 4) hYupper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ^ 34 ≠ 0) (pow_ne_zero _ hX0.ne'),
    Real.log_pow, Real.log_pow] at hlog
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogX := Real.log_nonneg hX
  have hc := log_count_upper hY
  norm_num at hlog
  linarith

lemma solve_length_upper {p : Params} (hm : 0 < p.μ) (hd : 0 ≤ p.δ) :
    (solveLength p : ℝ) ≤ 64 * (1 + Real.log (2 + (p.m : ℝ) + p.δ / p.μ)) := by
  have hr := outer_regularization_pos hm hd
  have hq := subproblem_convexity_pos hm hd
  have hmR : 1 ≤ (p.m : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p.m)
  have hroot : 1 ≤ Real.sqrt p.m := Real.one_le_sqrt.mpr hmR
  have hdR : 0 ≤ p.δ / p.μ := div_nonneg hd hm.le
  have hX : 1 ≤ 2 + (p.m : ℝ) + p.δ / p.μ := by linarith
  have hmr : p.μ ≤ outerRegularization p :=
    le_add_of_nonneg_right (div_nonneg hd (Real.sqrt_nonneg _))
  have hr1 : 1 ≤ subproblemConvexity p / outerRegularization p := by
    apply (le_div_iff₀ hr).2
    dsimp [subproblemConvexity]
    linarith
  have hr2 : subproblemConvexity p / outerRegularization p ≤ 2 := by
    apply (div_le_iff₀ hr).2
    dsimp [subproblemConvexity]
    linarith
  have hK1 : 1 ≤ (outerLength p : ℝ) := by exact_mod_cast Nat.succ_le_of_lt (outer_length_pos hm hd)
  have hratio : outerRegularization p / p.μ ≤ 2 + (p.m : ℝ) + p.δ / p.μ := by
    rw [(normalized_parameters hm).1]
    have hh := div_le_self hdR hroot
    linarith
  have hK := (outer_length_upper hm hd).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hratio) (by norm_num : (0 : ℝ) ≤ 9))
  have hb := logarithmic_solve_bound hX hr1 hr2 hK1 hK
  have hid : 2 ^ 20 * (subproblemConvexity p / outerRegularization p) * (outerLength p : ℝ) ^ 4 =
      2 ^ 20 * subproblemConvexity p * (outerLength p : ℝ) ^ 4 / outerRegularization p := by ring
  simpa only [solveLength, hid] using hb

lemma total_cost_upper {p : Params} (hs : 0 < p.s) (hsm : p.s ≤ p.m)
    (hm : 0 < p.μ) (hd : 0 ≤ p.δ) (hD : 0 ≤ p.Δ) (he : 0 < p.ε) :
    restartCount p * outerLength p * solveLength p * (snapshotLength p + 3 * epochLength p) ≤
      ⌈2 ^ 40 * (1 + (p.m : ℝ) / p.s + (1 + Real.sqrt ((p.m : ℝ) * Real.sqrt p.m) / p.s) * Real.sqrt (p.δ / p.μ)) * (1 + Real.log (2 + (p.m : ℝ) + p.δ / p.μ)) * (1 + Real.log (2 + p.Δ / p.ε))⌉₊ := by
  let W := 1 + (p.m : ℝ) / p.s +
    (1 + Real.sqrt ((p.m : ℝ) * Real.sqrt p.m) / p.s) * Real.sqrt (p.δ / p.μ)
  let X := 1 + Real.log (2 + (p.m : ℝ) + p.δ / p.μ)
  let Z := 1 + Real.log (2 + p.Δ / p.ε)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hX : 0 ≤ X := by
    have hh : 1 ≤ 2 + (p.m : ℝ) + p.δ / p.μ := by
      linarith [show (0 : ℝ) ≤ p.m from Nat.cast_nonneg _, div_nonneg hd hm.le]
    dsimp [X]
    linarith [Real.log_nonneg hh]
  have hZ : 0 ≤ Z := by
    have hh : 1 ≤ 2 + p.Δ / p.ε := by linarith [div_nonneg hD he.le]
    dsimp [Z]
    linarith [Real.log_nonneg hh]
  have h1 := epoch_round_cost_upper hs hsm hm hd
  have h2 := solve_length_upper hm hd
  have h3 := restart_count_upper hD he
  have hp := mul_le_mul h3 h2 (Nat.cast_nonneg _) (show 0 ≤ 2 * Z by positivity)
  have hp' := mul_le_mul hp h1
    (show 0 ≤ (outerLength p : ℝ) * ((snapshotLength p : ℝ) + 3 * epochLength p) by positivity)
    (show 0 ≤ (2 * Z) * (64 * X) by positivity)
  have hid : ((restartCount p : ℝ) * solveLength p) *
      ((outerLength p : ℝ) * ((snapshotLength p : ℝ) + 3 * epochLength p)) =
      ((restartCount p * outerLength p * solveLength p * (snapshotLength p + 3 * epochLength p) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hid] at hp'
  have hu : (2 * Z * (64 * X)) * (2 ^ 25 * W) ≤ 2 ^ 40 * W * X * Z := by
    have hh := mul_nonneg (mul_nonneg hW hX) hZ
    nlinarith only [hh]
  have ht := hp'.trans hu
  have hfinal : restartCount p * outerLength p * solveLength p * (snapshotLength p + 3 * epochLength p) ≤
      ⌈2 ^ 40 * W * X * Z⌉₊ := by
    exact_mod_cast ht.trans (Nat.le_ceil (2 ^ 40 * W * X * Z))
  exact hfinal

end LongTails.Proofs.CappedProximalBudget
