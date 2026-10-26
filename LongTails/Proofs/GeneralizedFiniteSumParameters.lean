import LongTails.Algorithms.LocalFiniteSumAcceleration
import LongTails.Proofs.RelativeGeneralizedGrowth

namespace OracleTemplate.GeneralizedFiniteSum

lemma increment_controls {A L q n M : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hq : 0 ≤ q) (hn : 1 ≤ n) (hM : M ≤ 3 * L + 204 * q ^ 2 / A) :
    let a := min (A / (1024 * (1 + q))) (Real.sqrt (n * A / (1048576 * L)))
    0 < a ∧ a ≤ A / (1024 * (1 + q)) ∧
      a ^ 2 ≤ n * A / (1048576 * L) ∧
      a * q ≤ A / 1024 ∧ a ^ 2 * M ≤ (207 / 1048576) * n * A := by
  let a := min (A / (1024 * (1 + q))) (Real.sqrt (n * A / (1048576 * L)))
  have hn0 : 0 < n := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : a ≤ A / (1024 * (1 + q)) := min_le_left _ _
  have hroot : a ≤ Real.sqrt (n * A / (1048576 * L)) := min_le_right _ _
  have hsq : a ^ 2 ≤ n * A / (1048576 * L) := by
    have hr := Real.sq_sqrt (show 0 ≤ n * A / (1048576 * L) by positivity)
    nlinarith [Real.sqrt_nonneg (n * A / (1048576 * L))]
  have hcap : a * (1024 * (1 + q)) ≤ A :=
    (le_div_iff₀ (by positivity)).mp hc
  have haq : a * q ≤ A / 1024 := by nlinarith
  have haqsq : a ^ 2 * q ^ 2 ≤ A ^ 2 / 1048576 := by
    have hh := mul_self_le_mul_self (mul_nonneg ha.le hq) haq
    nlinarith only [hh]
  have hbase : a ^ 2 * (1048576 * L) ≤ n * A :=
    (le_div_iff₀ (by positivity)).mp hsq
  have hbound := mul_le_mul_of_nonneg_left hM (sq_nonneg a)
  have hden : A * (a ^ 2 * M) ≤ 3 * L * a ^ 2 * A + 204 * a ^ 2 * q ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hbound hA.le
    field_simp at hh
    nlinarith only [hh]
  have hlast : a ^ 2 * M ≤ (207 / 1048576) * n * A := by
    have hb := mul_le_mul_of_nonneg_right hbase hA.le
    have hnA := mul_le_mul_of_nonneg_right hn (sq_nonneg A)
    apply (mul_le_mul_iff_right₀ hA).mp
    nlinarith only [hden, hb, haqsq, hnA]
  exact ⟨ha, hc, hsq, haq, hlast⟩

lemma increment_dominates {A L Q n : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hQ : 0 < Q) (hn : 0 < n) :
    A / (4096 * (Q + Real.sqrt ((L / n) * A))) ≤
      min (A / (1024 * Q)) (Real.sqrt (n * A / (1048576 * L))) := by
  let s := Real.sqrt ((L / n) * A)
  let t := Real.sqrt (n * A / (1048576 * L))
  let b := A / (4096 * (Q + s))
  have hs : 0 < s := by dsimp [s]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have he : b * (4096 * (Q + s)) = A := by dsimp [b]; field_simp
  have hprod : t * s = A / 1024 := by
    dsimp [s, t]
    rw [← Real.sqrt_mul (by positivity : 0 ≤ n * A / (1048576 * L))]
    have hid : n * A / (1048576 * L) * (L / n * A) = A ^ 2 / 1048576 := by field_simp
    rw [hid, Real.sqrt_div (sq_nonneg A), Real.sqrt_sq hA.le]
    norm_num
  apply le_min
  · apply (le_div_iff₀ (by positivity)).mpr
    change b * (1024 * Q) ≤ A
    nlinarith [mul_pos hb hs]
  · change b ≤ t
    apply (mul_le_mul_iff_right₀ hs).mp
    nlinarith [mul_pos hb hQ]

lemma increment_potential_growth {A L Q n : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hQ : 1 ≤ Q) (hn : 0 < n) :
    let a := min (A / (1024 * Q)) (Real.sqrt (n * A / (1048576 * L)))
    let s := Real.sqrt ((L / n) * A)
    let t := Real.sqrt ((L / n) * (A + a))
    1 / 12288 ≤ (t + 2 * Q * Real.log t) - (s + 2 * Q * Real.log s) := by
  let b := A / (4096 * (Q + Real.sqrt ((L / n) * A)))
  let a := min (A / (1024 * Q)) (Real.sqrt (n * A / (1048576 * L)))
  have hQ0 : 0 < Q := by linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b ≤ a := increment_dominates hA hL hQ0 hn
  have hL' : 0 < L / n := div_pos hL hn
  have hmono : Real.sqrt ((L / n) * (A + b)) ≤ Real.sqrt ((L / n) * (A + a)) := by
    apply Real.sqrt_le_sqrt
    gcongr
  have hlog := Real.log_le_log (by positivity : 0 < Real.sqrt ((L / n) * (A + b))) hmono
  have hscale := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * Q by positivity)
  have hh := RelativeGeneralized.weight_growth hA hQ hL'
  change 1 / 12288 ≤ _
  change 1 / 12288 ≤ (Real.sqrt ((L / n) * (A + b)) + 2 * Q * Real.log (Real.sqrt ((L / n) * (A + b)))) -
    (Real.sqrt ((L / n) * A) + 2 * Q * Real.log (Real.sqrt ((L / n) * A))) at hh
  linarith only [hh, hmono, hscale]

open LongTails.Setups.GeneralizedSmoothFiniteSum

lemma epochIncrement_pos (p : Params) (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1)
    (hG : 0 ≤ p.G) (hR : 0 ≤ p.R) {A : ℝ} (hA : 0 < A) :
    0 < epochIncrement p A := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  unfold epochIncrement
  positivity

lemma epochWeight_pos (p : Params) (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1)
    (hG : 0 ≤ p.G) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (k : ℕ) :
    0 < epochWeight p k := by
  induction k with
  | zero => dsimp [epochWeight]; positivity
  | succ k ih =>
    exact add_pos ih (epochIncrement_pos p h0 h1 hG hR.le ih)

lemma epochWeight_mono (p : Params) (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1)
    (hG : 0 ≤ p.G) (hR : 0 < p.R) (hΔ : 0 < p.Δ) : Monotone (epochWeight p) := by
  apply monotone_nat_of_le_succ
  intro k
  have ha := epochIncrement_pos p h0 h1 hG hR.le (epochWeight_pos p h0 h1 hG hR hΔ k)
  change epochWeight p k ≤ epochWeight p k + epochIncrement p (epochWeight p k)
  linarith

lemma epoch_potential_growth (p : Params) (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1)
    (hG : 0 ≤ p.G) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (N : ℕ) :
    let L := (p.L0 + p.L1 * p.G) / p.n
    let Q := 1 + p.L1 * p.R
    let r := fun k => Real.sqrt (L * epochWeight p k)
    (N : ℝ) / 12288 ≤ (r N + 2 * Q * Real.log (r N)) -
      (r 0 + 2 * Q * Real.log (r 0)) := by
  let L := (p.L0 + p.L1 * p.G) / p.n
  let Q := 1 + p.L1 * p.R
  let r := fun k => Real.sqrt (L * epochWeight p k)
  have hQ : 1 ≤ Q := by dsimp [Q]; nlinarith [mul_nonneg h1 hR.le]
  have hL : 0 < p.L0 + p.L1 * p.G := by positivity
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hi (k : ℕ) : 1 / 12288 ≤
      (r (k + 1) + 2 * Q * Real.log (r (k + 1))) - (r k + 2 * Q * Real.log (r k)) := by
    have hh := increment_potential_growth (epochWeight_pos p h0 h1 hG hR hΔ k) hL hQ hn
    simpa only [r, L, Q, epochWeight, epochIncrement] using hh
  change (N : ℝ) / 12288 ≤ _
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := hi N
    push_cast
    linarith

lemma log_ratio_bound {H : ℝ} (hH : 0 < H) : Real.log (12 * H) ≤ 3 * Real.log (2 + H) := by
  have hp : 12 * H ≤ (2 + H) ^ 3 := by nlinarith [sq_nonneg H, mul_nonneg (sq_nonneg H) hH.le]
  have hh := Real.log_le_log (by positivity : 0 < 12 * H) hp
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

lemma epochCount_sufficient (p : Params) (h0 : 0 < p.L0) (h1 : 0 ≤ p.L1)
    (hG : 0 ≤ p.G) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    12 * p.R ^ 2 / p.ε ≤ epochWeight p (epochCount p) := by
  let N := epochCount p
  let L := (p.L0 + p.L1 * p.G) / p.n
  let Q := 1 + p.L1 * p.R
  let X := (p.L0 + p.L1 * p.G) * p.R ^ 2 / ((p.n : ℝ) * p.ε)
  let ell := Real.log (2 + p.Δ / p.ε)
  let r := fun k => Real.sqrt (L * epochWeight p k)
  have hn : (0 : ℝ) < p.n := by exact_mod_cast NeZero.pos p.n
  have hL : 0 < L := by dsimp [L]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hell : 0 < ell := Real.log_pos (by have := div_pos hΔ hε; linarith)
  have hA (k : ℕ) := epochWeight_pos p h0 h1 hG hR hΔ k
  have hr (k : ℕ) : 0 < r k := by dsimp [r]; exact Real.sqrt_pos.mpr (mul_pos hL (hA k))
  have hrsq (k : ℕ) : r k ^ 2 = L * epochWeight p k := Real.sq_sqrt (mul_pos hL (hA k)).le
  have hgrowth := epoch_potential_growth p h0 h1 hG hR hΔ N
  change (N : ℝ) / 12288 ≤ (r N + 2 * Q * Real.log (r N)) -
    (r 0 + 2 * Q * Real.log (r 0)) at hgrowth
  have hN : 65536 * Q * ell + 65536 * Real.sqrt X ≤ N := by
    exact Nat.le_ceil _
  by_contra hbad
  have hbad' : epochWeight p N < 12 * p.R ^ 2 / p.ε := lt_of_not_ge hbad
  have hrN : r N ≤ 4 * Real.sqrt X := by
    have hh := mul_le_mul_of_nonneg_left hbad'.le hL.le
    have he : L * (12 * p.R ^ 2 / p.ε) = 12 * X := by dsimp [L, X]; ring
    rw [he, ← hrsq N] at hh
    nlinarith [Real.sq_sqrt hX.le, Real.sqrt_nonneg X, (hr N).le]
  have hlogs (k : ℕ) : 2 * Real.log (r k) = Real.log L + Real.log (epochWeight p k) := by
    have hh := congrArg Real.log (hrsq k)
    simpa only [Real.log_pow, Nat.cast_ofNat, Real.log_mul hL.ne' (hA k).ne'] using hh
  have hratio : epochWeight p N / epochWeight p 0 ≤ 12 * (p.Δ / p.ε) := by
    have hh := div_le_div_of_nonneg_right hbad'.le (hA 0).le
    have he : (12 * p.R ^ 2 / p.ε) / epochWeight p 0 = 12 * (p.Δ / p.ε) := by
      simp only [epochWeight]
      field_simp
    rwa [he] at hh
  have hlogratio := Real.log_le_log (div_pos (hA N) (hA 0)) hratio
  rw [Real.log_div (hA N).ne' (hA 0).ne'] at hlogratio
  have hlog : 2 * (Real.log (r N) - Real.log (r 0)) ≤ 3 * ell := by
    have hh := log_ratio_bound (div_pos hΔ hε)
    dsimp [ell]
    linarith only [hlogratio, hh, hlogs N, hlogs 0]
  have hscaled := mul_le_mul_of_nonneg_left hlog hQ.le
  have hQell : 0 < Q * ell := mul_pos hQ hell
  nlinarith only [hgrowth, hN, hrN, hscaled, hQell, (hr 0).le, Real.sqrt_nonneg X]

lemma trialCount_failure (p : Params) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    p.Δ * (1 / 4 : ℝ) ^ trialCount p ≤ p.ε / 2 := by
  have hX : 0 < 2 * max 1 (p.Δ / p.ε) := by positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hc : Real.log (2 * max 1 (p.Δ / p.ε)) / Real.log 4 ≤ (trialCount p : ℝ) := Nat.le_ceil _
  have hp : 2 * max 1 (p.Δ / p.ε) ≤ (4 : ℝ) ^ trialCount p := by
    apply (Real.log_le_log_iff hX (by positivity)).mp
    rw [Real.log_pow]
    exact (div_le_iff₀ hlog4).mp hc
  have hi := one_div_le_one_div_of_le hX hp
  have hi' : (1 / 4 : ℝ) ^ trialCount p ≤ 1 / (2 * max 1 (p.Δ / p.ε)) := by
    simpa only [one_div, inv_pow] using hi
  have hh := mul_le_mul_of_nonneg_left hi' hΔ.le
  apply hh.trans
  rw [mul_one_div]
  apply (div_le_iff₀ hX).mpr
  have hm := mul_le_mul_of_nonneg_left (le_max_right 1 (p.Δ / p.ε)) hε.le
  have he : p.ε * (p.Δ / p.ε) = p.Δ := by field_simp
  rw [he] at hm
  nlinarith only [hm]

end OracleTemplate.GeneralizedFiniteSum
