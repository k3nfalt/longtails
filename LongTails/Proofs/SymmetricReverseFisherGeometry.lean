import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open MeasureTheory

namespace LongTails.Proofs.SymmetricReverseFisherGeometry

lemma weighted_zero_nonneg {μ : Measure ℝ} (w h : ℝ → ℝ) (c : ℝ)
    (hw : Integrable w μ) (hwh : Integrable (fun x => w x * h x) μ)
    (hzero : ∫ x, w x ∂μ = 0)
    (hsign : ∀ᵐ x ∂μ, 0 ≤ w x * (h x - c)) :
    0 ≤ ∫ x, w x * h x ∂μ := by
  have he : (∫ x, w x * (h x - c) ∂μ) = ∫ x, w x * h x ∂μ := by
    simp_rw [mul_sub]
    rw [integral_sub hwh (hw.mul_const c), integral_mul_const, hzero, zero_mul, sub_zero]
  rw [← he]
  exact integral_nonneg_of_ae hsign

lemma weighted_single_crossing {μ : Measure ℝ} (w h : ℝ → ℝ) (b : ℝ)
    (hw : Integrable w μ) (hwh : Integrable (fun x => w x * h x) μ)
    (hzero : ∫ x, w x ∂μ = 0)
    (hleft : ∀ x, x ≤ b → 0 ≤ w x)
    (hright : ∀ x, b ≤ x → w x ≤ 0)
    (hmono : Antitone h) :
    0 ≤ ∫ x, w x * h x ∂μ := by
  have hp (x : ℝ) : 0 ≤ w x * (h x - h b) := by
    rcases le_total x b with hx | hx
    · exact mul_nonneg (hleft x hx) (sub_nonneg.mpr (hmono hx))
    · exact mul_nonneg_of_nonpos_of_nonpos (hright x hx)
        (sub_nonpos.mpr (hmono hx))
  exact weighted_zero_nonneg w h (h b) hw hwh hzero (ae_of_all _ hp)

lemma aligned_contraction (u a κ L η D : ℝ)
    (hκ : 0 ≤ κ) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (hquot : ∃ t ∈ Set.Icc κ L, D = t * (u - a)) :
    |u - η * D - a| ≤ (1 - η * κ) * |u - a| := by
  obtain ⟨t, ⟨htκ, htL⟩, rfl⟩ := hquot
  have ht : 0 ≤ t := hκ.trans htκ
  have hηt : η * t ≤ 1 := (mul_le_mul_of_nonneg_left htL hη).trans hηL
  have he : u - η * (t * (u - a)) - a = (1 - η * t) * (u - a) := by ring
  rw [he, abs_mul, abs_of_nonneg (sub_nonneg.mpr hηt)]
  exact mul_le_mul_of_nonneg_right
    (sub_le_sub_left (mul_le_mul_of_nonneg_left htκ hη) 1) (abs_nonneg _)

lemma angular_ratio_contraction (q l η m b : ℝ)
    (hq : 0 ≤ q) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hη : 0 < η) (hm : 0 < m) (hb : m ≤ b) :
    l * q / (l + η * b) ≤ q / (1 + η * m) := by
  have hb' : 0 < b := hm.trans_le hb
  have hden : 0 < l + η * b := by positivity
  have hden' : 0 < 1 + η * m := by positivity
  apply (div_le_div_iff₀ hden hden').mpr
  have hprod : l * m ≤ b := (mul_le_of_le_one_left (le_of_lt hm) hl1).trans hb
  have hh := mul_le_mul_of_nonneg_left hprod (le_of_lt hη)
  have hh' := mul_le_mul_of_nonneg_left hh hq
  nlinarith

lemma capped_growth (u : ℕ → ℝ) {g ell : ℝ} (hg : 1 ≤ g) (hell : 0 ≤ ell)
    (hu : ∀ k, min (g * u k) ell ≤ u (k + 1)) (k : ℕ) :
    min (g ^ k * u 0) ell ≤ u k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := mul_le_mul_of_nonneg_left ih (show 0 ≤ g by linarith)
    have he : min (g ^ (k + 1) * u 0) ell = min (g * min (g ^ k * u 0) ell) ell := by
      rw [mul_min_of_nonneg _ _ (show 0 ≤ g by linarith), min_assoc]
      have hge : ell ≤ g * ell := by nlinarith
      rw [min_eq_right hge]
      congr 1
      rw [pow_succ]
      ring
    rw [he]
    exact (min_le_min_right ell h).trans (hu k)
lemma capped_decay (u : ℕ → ℝ) {d ell : ℝ} (hd : 0 ≤ d) (hd1 : d ≤ 1) (hell : 0 ≤ ell)
    (hu : ∀ k, u (k + 1) ≤ max (d * u k) ell) (k : ℕ) :
    u k ≤ max (d ^ k * u 0) ell := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := mul_le_mul_of_nonneg_left ih hd
    have he : max (d * max (d ^ k * u 0) ell) ell = max (d ^ (k + 1) * u 0) ell := by
      rw [mul_max_of_nonneg _ _ hd, max_assoc]
      have hde : d * ell ≤ ell := by nlinarith
      rw [max_eq_right hde]
      congr 1
      rw [pow_succ]
      ring
    exact (hu k).trans ((max_le_max_right ell h).trans_eq he)
lemma geometric_recurrence (u : ℕ → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hu : ∀ k, u (k + 1) ≤ b * u k) (k : ℕ) : u k ≤ b ^ k * u 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      u (k + 1) ≤ b * u k := hu k
      _ ≤ b * (b ^ k * u 0) := mul_le_mul_of_nonneg_left ih hb
      _ = b ^ (k + 1) * u 0 := by rw [pow_succ]; ring
lemma perturbed_geometric_recurrence (u : ℕ → ℝ) {A b F : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hgap : b < A) (hF : 0 ≤ F)
    (hu : ∀ k, u (k + 1) ≤ A * u k + F * b ^ k) (k : ℕ) :
    u k ≤ A ^ k * (u 0 + F / (A - b)) := by
  have hden : 0 < A - b := sub_pos.mpr hgap
  have hD : 0 ≤ F / (A - b) := div_nonneg hF hden.le
  have hcancel : F / (A - b) * (A - b) = F := div_mul_cancel₀ _ hden.ne'
  have hs (j : ℕ) :
      (u (j + 1) + F / (A - b) * b ^ (j + 1)) ≤
      A * (u j + F / (A - b) * b ^ j) := by
    have hh := hu j
    rw [pow_succ]
    nlinarith [congrArg (fun t : ℝ => t * b ^ j) hcancel]
  have ht := geometric_recurrence (fun j => u j + F / (A - b) * b ^ j) hA hs k
  simp only [pow_zero, mul_one] at ht
  exact (le_add_of_nonneg_right (mul_nonneg hD (pow_nonneg hb k))).trans ht

lemma one_sub_pow_le_exp {t : ℝ} (_ht : 0 ≤ t) (ht1 : t ≤ 1) (k : ℕ) :
    (1 - t) ^ k ≤ Real.exp (-t * k) := by
  have he : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  calc
    _ ≤ (Real.exp (-t)) ^ k := pow_le_pow_left₀ (sub_nonneg.mpr ht1) he k
    _ = Real.exp (-t * k) := by rw [← Real.exp_nat_mul]; congr 1; ring
lemma power_small_of_log {t ε : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hε : 0 < ε) {k : ℕ} (hk : Real.log (4 / ε) / t ≤ k) :
    (1 - t) ^ k ≤ ε / 4 := by
  have hlog : Real.log (4 / ε) ≤ t * k := (div_le_iff₀ ht).mp hk |>.trans_eq (mul_comm _ _)
  calc
    _ ≤ Real.exp (-t * k) := one_sub_pow_le_exp ht.le ht1 k
    _ ≤ Real.exp (-Real.log (4 / ε)) := Real.exp_le_exp.mpr (by linarith)
    _ = ε / 4 := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp

end LongTails.Proofs.SymmetricReverseFisherGeometry
