import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Semifield

namespace OracleTemplate.FixedBatchConfidence

lemma batch_wedge {η θ a c x y : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a ^ 2 + c ^ 2 = 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy : y ≤ 0) (hr : 0 ≤ a * x + c * y) :
    let x' := x - η * θ * a * (a * x + c * y)
    let y' := y - η * ((1 - θ) * y + θ * c * (a * x + c * y))
    0 ≤ x' ∧ x' ≤ x ∧ y' ≤ 0 ∧ 0 ≤ a * x' + c * y' ∧
      x - x' ≤ η * θ * a ^ 2 := by
  dsimp
  have hcys : c * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hy
  have har : a * x + c * y ≤ a * x := by linarith
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
  have het0 : 0 ≤ η * θ := mul_nonneg hη0 hθ0
  have het1 : η * θ ≤ 1 := by nlinarith
  have hm0 : 0 ≤ η * θ * a := mul_nonneg het0 ha
  have hsub0 : 0 ≤ η * θ * a * (a * x + c * y) := mul_nonneg hm0 hr
  have hsub : η * θ * a * (a * x + c * y) ≤ η * θ * a * (a * x) :=
    mul_le_mul_of_nonneg_left har hm0
  have hm2 : η * θ * a ^ 2 ≤ 1 := by nlinarith [sq_nonneg a]
  have hxx : η * θ * a ^ 2 * x ≤ x := by nlinarith
  have hstep : 0 ≤ x - η * θ * a * (a * x + c * y) := by nlinarith
  have hcoef : 0 ≤ 1 - η * (1 - θ * a ^ 2) := by
    have : 0 ≤ η * θ * a ^ 2 := mul_nonneg het0 (sq_nonneg a)
    nlinarith
  have hyy : (1 - η * (1 - θ * a ^ 2)) * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoef hy
  have hkick : 0 ≤ η * θ * a * c * x := by positivity
  have hyr : y - η * ((1 - θ) * y + θ * c * (a * x + c * y)) =
      (1 - η * (1 - θ * a ^ 2)) * y - η * θ * a * c * x := by
    nlinarith [congrArg (fun z : ℝ => η * θ * y * z) hac]
  have hr1 : 0 ≤ (1 - η * θ) * (a * x + c * y) :=
    mul_nonneg (by linarith) hr
  have hr2 : 0 ≤ -(η * (1 - θ) * c * y) := by
    have : η * (1 - θ) * c * y ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hy
    linarith
  have hre : a * (x - η * θ * a * (a * x + c * y)) +
      c * (y - η * ((1 - θ) * y + θ * c * (a * x + c * y))) =
      (1 - η * θ) * (a * x + c * y) - η * (1 - θ) * c * y := by
    nlinarith [congrArg (fun z : ℝ => η * θ * (a * x + c * y) * z) hac]
  refine ⟨hstep, by linarith, ?_, ?_, ?_⟩
  · rw [hyr]
    linarith
  · rw [hre]
    linarith
  · have hbound : η * θ * a ^ 2 * x ≤ η * θ * a ^ 2 :=
      mul_le_of_le_one_right (by positivity) hx1
    nlinarith

lemma rare_batch_kick {η b a c x y : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hb : 1 ≤ b)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hy : y ≤ 0) (hx : 3 / 4 ≤ x) :
    (1 - η * (1 - a ^ 2 / b)) * y - η * a * c * x / b ≤
      -(3 * η * a * c / (4 * b)) := by
  have hb0 : 0 < b := by linarith
  have hcoeff : 0 ≤ 1 - η * (1 - a ^ 2 / b) := by
    have : 0 ≤ η * (a ^ 2 / b) := by positivity
    nlinarith
  have hfirst := mul_nonpos_of_nonneg_of_nonpos hcoeff hy
  have hprod := mul_le_mul_of_nonneg_left hx (show 0 ≤ η * a * c / b by positivity)
  calc
    _ ≤ 0 - η * a * c * x / b := sub_le_sub_right hfirst _
    _ = -(η * a * c / b * x) := by ring
    _ ≤ -(η * a * c / b * (3 / 4)) := neg_le_neg hprod
    _ = _ := by ring

lemma batch_path_wedge {η a c : ℝ} (x y θ : ℕ → ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hac : a ^ 2 + c ^ 2 = 1) (hθ : ∀ k, 0 ≤ θ k ∧ θ k ≤ 1)
    (hx : x 0 = 1) (hy : y 0 = 0)
    (hxs : ∀ k, x (k + 1) = x k - η * θ k * a * (a * x k + c * y k))
    (hys : ∀ k, y (k + 1) = y k -
      η * ((1 - θ k) * y k + θ k * c * (a * x k + c * y k))) (k : ℕ) :
    0 ≤ x k ∧ x k ≤ 1 ∧ y k ≤ 0 ∧ 0 ≤ a * x k + c * y k ∧
      1 - x k ≤ η * a ^ 2 * ∑ j ∈ Finset.range k, θ j := by
  induction k with
  | zero => simpa [hx, hy] using ha
  | succ k ih =>
    obtain ⟨hx0, hx1, hy0, hr, hdrop⟩ := ih
    have hs := batch_wedge hη0 hη1 (hθ k).1 (hθ k).2 ha hc hac hx0 hx1 hy0 hr
    dsimp at hs
    rw [← hxs k, ← hys k] at hs
    refine ⟨hs.1, hs.2.1.trans hx1, hs.2.2.1, hs.2.2.2.1, ?_⟩
    rw [Finset.sum_range_succ]
    nlinarith [hs.2.2.2.2]

lemma common_tail {η a c : ℝ} (x y θ : ℕ → ℝ)
    (hys : ∀ k, y (k + 1) = y k -
      η * ((1 - θ k) * y k + θ k * c * (a * x k + c * y k)))
    (k n : ℕ) (hzero : ∀ j < n, θ (k + j) = 0) :
    y (k + n) = (1 - η) ^ n * y k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show k + (n + 1) = (k + n) + 1 by omega, hys, hzero n (by omega)]
    rw [ih (fun j hj => hzero j (by omega)), pow_succ]
    ring

lemma batch_prefix_lower {η a : ℝ} {x θ : ℕ → ℝ} {k : ℕ}
    (hdrop : 1 - x k ≤ η * a ^ 2 * ∑ j ∈ Finset.range k, θ j)
    (hcount : η * a ^ 2 * ∑ j ∈ Finset.range k, θ j ≤ 1 / 4) :
    3 / 4 ≤ x k := by linarith

lemma kick_persists {t a c y z r : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hy : y ≤ -(3 * t * a * c / 4)) (hr : 1 / 4 ≤ r)
    (hz : z = r * y) : z ≤ -(3 * t * a * c / 16) := by
  have hv : 0 ≤ 3 * t * a * c / 4 := by positivity
  have hr0 : 0 ≤ r := by linarith
  have h1 := mul_le_mul_of_nonneg_left hy hr0
  have h2 := mul_le_mul_of_nonneg_right hr hv
  rw [hz]
  nlinarith

lemma rare_risk_lower {t a c x y p : ℝ}
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hc : 0 ≤ c) (hc2 : 1 / 2 ≤ c ^ 2)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 8)
    (hy : y ≤ -(3 * t * a * c / 16)) :
    t ^ 2 * a ^ 2 / 256 ≤ ((1 - p) * y ^ 2 + p * (a * x + c * y) ^ 2) / 2 := by
  have hv : 0 ≤ 3 * t * a * c / 16 := by positivity
  have hsq : (3 * t * a * c / 16) ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ -y - 3 * t * a * c / 16 by linarith)
      (show 0 ≤ -y + 3 * t * a * c / 16 by linarith)]
  have hcurv := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ t ^ 2 * a ^ 2 by positivity)
  have hprob := mul_le_mul_of_nonneg_right hp1 (sq_nonneg y)
  have hrare : 0 ≤ p * (a * x + c * y) ^ 2 := by positivity
  nlinarith [sq_nonneg (t * a)]

lemma scalar_bias_lower {η ell : ℝ} {K : ℕ} (hK : 0 < K)
    (hη : 0 ≤ η) (hell : 0 ≤ ell) (hprod : (K : ℝ) * η * ell ≤ 1 / 2) :
    ell / 8 ≤ ell * (1 - η * ell) ^ (2 * K) / 2 := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hr0 : 0 ≤ η * ell := mul_nonneg hη hell
  have hr1 : η * ell ≤ 1 / 2 := by nlinarith
  have hp := one_add_mul_le_pow (a := -(η * ell)) (by linarith : -2 ≤ -(η * ell)) K
  have hhalf : 1 / 2 ≤ (1 - η * ell) ^ K := by
    change 1 + (K : ℝ) * -(η * ell) ≤ (1 - η * ell) ^ K at hp
    nlinarith
  have hsq : 1 / 4 ≤ ((1 - η * ell) ^ K) ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsq hell
  rw [Nat.mul_comm 2 K, pow_mul]
  nlinarith

lemma rare_kick_from_count {η a c b : ℝ} (x y θ : ℕ → ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hac : a ^ 2 + c ^ 2 = 1) (hb : 1 ≤ b)
    (hθ : ∀ k, 0 ≤ θ k ∧ θ k ≤ 1) (hx : x 0 = 1) (hy : y 0 = 0)
    (hxs : ∀ k, x (k + 1) = x k - η * θ k * a * (a * x k + c * y k))
    (hys : ∀ k, y (k + 1) = y k -
      η * ((1 - θ k) * y k + θ k * c * (a * x k + c * y k)))
    (k : ℕ) (hrare : θ k = 1 / b)
    (hcount : η * a ^ 2 * ∑ j ∈ Finset.range k, θ j ≤ 1 / 4) :
    y (k + 1) ≤ -(3 * η * a * c / (4 * b)) := by
  have hp := batch_path_wedge x y θ hη0 hη1 ha hc hac hθ hx hy hxs hys k
  have hxb := batch_prefix_lower hp.2.2.2.2 hcount
  have hh := rare_batch_kick hη0 hη1 hb ha hc hp.2.2.1 hxb
  have he : y (k + 1) =
      (1 - η * (1 - a ^ 2 / b)) * y k - η * a * c * x k / b := by
    rw [hys, hrare]
    field_simp
    nlinarith [congrArg (fun z : ℝ => η * y k * z) hac]
  rw [he]
  exact hh

lemma rare_window_path_risk {η a c b p : ℝ} (x y θ : ℕ → ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hac : a ^ 2 + c ^ 2 = 1) (hc2 : 1 / 2 ≤ c ^ 2) (hb : 1 ≤ b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 8)
    (hθ : ∀ k, 0 ≤ θ k ∧ θ k ≤ 1) (hx : x 0 = 1) (hy : y 0 = 0)
    (hxs : ∀ k, x (k + 1) = x k - η * θ k * a * (a * x k + c * y k))
    (hys : ∀ k, y (k + 1) = y k -
      η * ((1 - θ k) * y k + θ k * c * (a * x k + c * y k)))
    (k n : ℕ) (hrare : θ k = 1 / b)
    (hcount : η * a ^ 2 * ∑ j ∈ Finset.range k, θ j ≤ 1 / 4)
    (hzero : ∀ j < n, θ (k + 1 + j) = 0) (hpow : 1 / 4 ≤ (1 - η) ^ n) :
    (η / b) ^ 2 * a ^ 2 / 256 ≤
      ((1 - p) * y (k + 1 + n) ^ 2 +
        p * (a * x (k + 1 + n) + c * y (k + 1 + n)) ^ 2) / 2 := by
  have hkick := rare_kick_from_count x y θ hη0 hη1 ha hc hac hb hθ hx hy hxs hys k hrare hcount
  have htail := common_tail x y θ hys (k + 1) n hzero
  have ht : 0 ≤ η / b := div_nonneg hη0 (by linarith)
  have hk : y (k + 1) ≤ -(3 * (η / b) * a * c / 4) := by
    convert hkick using 1; ring
  exact rare_risk_lower ht ha hc hc2 hp0 hp1 (kick_persists ht ha hc hk hpow htail)

lemma recovery_window {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    let m := ⌈1 / (2 * η)⌉₊
    0 < m ∧ 1 / 2 ≤ η * (m : ℝ) ∧ η * (m : ℝ) ≤ 1 ∧
      1 / 2 < (1 - η) ^ (m - 1) := by
  let m := ⌈1 / (2 * η)⌉₊
  have hr0 : 0 < 1 / (2 * η) := by positivity
  have hm0 : 0 < m := Nat.ceil_pos.mpr hr0
  have hr : (1 / 2 : ℝ) ≤ 1 / (2 * η) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * η)).mpr
    nlinarith
  have hlo := mul_le_mul_of_nonneg_left (Nat.le_ceil (1 / (2 * η))) hη0.le
  have hceil : (⌈1 / (2 * η)⌉₊ : ℝ) ≤ 2 * (1 / (2 * η)) :=
    Nat.ceil_le_two_mul (by simpa only [one_div] using hr)
  have hhi := mul_le_mul_of_nonneg_left hceil hη0.le
  have hid : η * (1 / (2 * η)) = 1 / 2 := by field_simp [ne_of_gt hη0]
  have hml : 1 / 2 ≤ η * (m : ℝ) := by simpa only [hid] using hlo
  have hmu : η * (m : ℝ) ≤ 1 := by dsimp [m]; nlinarith
  have hstrict := mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one hr0.le) hη0
  have hp : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
  have hpm : η * ((m - 1 : ℕ) : ℝ) < 1 / 2 := by
    rw [hp]
    dsimp [m] at *
    nlinarith
  have hb := one_add_mul_le_pow (a := -η) (by linarith : -2 ≤ -η) (m - 1)
  refine ⟨hm0, hml, hmu, ?_⟩
  convert lt_of_lt_of_le (by nlinarith : (1 / 2 : ℝ) < 1 + ((m - 1 : ℕ) : ℝ) * -η) hb using 1

lemma recovery_window_prefix {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    {n : ℕ} (hn : n ≤ ⌈1 / (2 * η)⌉₊ - 1) :
    1 / 2 < (1 - η) ^ n := by
  have h := (recovery_window hη0 hη1).2.2.2
  exact h.trans_le (pow_le_pow_of_le_one (by linarith) (by linarith) hn)

lemma one_rare_lower {m : ℕ} {p δ : ℝ}
    (hp : 0 ≤ p) (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 64)
    (hlo : 4 * δ ≤ (m : ℝ) * p) (hhi : (m : ℝ) * p ≤ 8 * δ) :
    7 / 2 * δ ≤ (m : ℝ) * p * (1 - p) ^ (m - 1) := by
  have hmp0 : 0 ≤ (m : ℝ) * p := by positivity
  have hm : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
  have hpp := mul_le_mul_of_nonneg_right hm hp
  by_cases hz : m = 0
  · subst m
    simp only [Nat.cast_zero, zero_mul] at hlo ⊢
    linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
  have hp1 : p ≤ 1 := by nlinarith
  have hb := one_add_mul_le_pow (a := -p) (by linarith : -2 ≤ -p) (m - 1)
  have hpow : (7 / 8 : ℝ) ≤ (1 - p) ^ (m - 1) := by
    have he : (1 + -p) ^ (m - 1) = (1 - p) ^ (m - 1) := by rfl
    rw [he] at hb
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hpow hmp0
  nlinarith

end OracleTemplate.FixedBatchConfidence
