import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.CubicNewtonPLRecursion

structure Trace (u ρ : ℕ → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ u k
  step_nonneg : ∀ k, 0 ≤ ρ k
  quartic : ∀ k, u (k + 1) ≤ ρ k ^ 4
  cubic : ∀ k, u (k + 1) + ρ k ^ 3 ≤ u k

variable {u ρ : ℕ → ℝ}

lemma Trace.antitone (h : Trace u ρ) : Antitone u :=
  antitone_nat_of_succ_le (fun k => by
    have h1 := h.cubic k
    have h2 := pow_nonneg (h.step_nonneg k) 3
    linarith)

lemma phase_poly {s : ℝ} (hs : 1 / 2 ≤ s) : (s + 1 / 16) ^ 4 ≤ s ^ 4 + s ^ 3 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg s),
    mul_nonneg (sub_nonneg.mpr hs) (show (0 : ℝ) ≤ s by linarith), sq_nonneg s]

lemma phase_step {a b r T : ℝ} (hr : 0 ≤ r) (hq : b ≤ r ^ 4) (hc : b + r ^ 3 ≤ a)
    (ha : a ≤ T ^ 4) (hT : 9 / 16 ≤ T) : b ≤ (T - 1 / 16) ^ 4 := by
  by_contra hcon
  push Not at hcon
  have hs : (1 : ℝ) / 2 ≤ T - 1 / 16 := by linarith
  have hrs : T - 1 / 16 < r := by
    by_contra hle
    push Not at hle
    have h := pow_le_pow_left₀ hr hle 4
    linarith
  have h3 : (T - 1 / 16) ^ 3 < r ^ 3 := pow_lt_pow_left₀ hrs (by linarith) (by norm_num)
  have hp := phase_poly hs
  have he : T - 1 / 16 + 1 / 16 = T := by ring
  rw [he] at hp
  linarith

noncomputable def envelope (T0 : ℝ) (k : ℕ) : ℝ := max (T0 - k / 16) (1 / 2)

lemma envelope_succ (T0 : ℝ) (k : ℕ) :
    max (envelope T0 k) (9 / 16) - 1 / 16 ≤ envelope T0 (k + 1) := by
  unfold envelope
  push_cast
  rcases le_total (max (T0 - (k : ℝ) / 16) (1 / 2)) (9 / 16) with h1 | h1
  · rw [max_eq_right h1]
    have he : (9 : ℝ) / 16 - 1 / 16 = 1 / 2 := by norm_num
    rw [he]
    exact le_max_right _ _
  · rw [max_eq_left h1]
    have h2 : max (T0 - (k : ℝ) / 16) (1 / 2) = T0 - (k : ℝ) / 16 := by
      apply max_eq_left
      by_contra hlt
      push Not at hlt
      rw [max_eq_right hlt.le] at h1
      norm_num at h1
    rw [h2]
    have he : T0 - (k : ℝ) / 16 - 1 / 16 = T0 - ((k : ℝ) + 1) / 16 := by ring
    rw [he]
    exact le_max_left _ _

lemma phase_one (h : Trace u ρ) {T0 : ℝ} (h0 : u 0 ≤ T0 ^ 4) (hT0 : 0 ≤ T0) (k : ℕ) :
    u k ≤ envelope T0 k ^ 4 := by
  induction k with
  | zero =>
    have hle : T0 ≤ envelope T0 0 := by
      unfold envelope
      simp
    exact h0.trans (pow_le_pow_left₀ hT0 hle 4)
  | succ k ih =>
    have hE : (1 : ℝ) / 2 ≤ envelope T0 k := le_max_right _ _
    have hT : (9 : ℝ) / 16 ≤ max (envelope T0 k) (9 / 16) := le_max_right _ _
    have hu : u k ≤ (max (envelope T0 k) (9 / 16)) ^ 4 :=
      ih.trans (pow_le_pow_left₀ (by linarith) (le_max_left _ _) 4)
    have hstep := phase_step (h.step_nonneg k) (h.quartic k) (h.cubic k) hu hT
    have hnn : 0 ≤ max (envelope T0 k) (9 / 16) - 1 / 16 := by linarith
    exact hstep.trans (pow_le_pow_left₀ hnn (envelope_succ T0 k) 4)

lemma phase_one_end (h : Trace u ρ) {T0 : ℝ} (h0 : u 0 ≤ T0 ^ 4) (hT0 : 0 ≤ T0) {k : ℕ}
    (hk : 16 * T0 ≤ k) : u k ≤ 1 / 16 := by
  have h1 := phase_one h h0 hT0 k
  have he : envelope T0 k = 1 / 2 := by
    unfold envelope
    apply max_eq_right
    linarith
  rw [he] at h1
  norm_num at h1
  linarith

lemma cube_step {a b r c : ℝ} (hr : 0 ≤ r) (hc0 : 0 ≤ c) (hb : 0 ≤ b) (hq : b ≤ r ^ 4)
    (hc : b + r ^ 3 ≤ a) (ha : a ≤ c ^ 3) : b ≤ c ^ 4 := by
  have h3 : r ^ 3 ≤ c ^ 3 := by linarith
  have hrc : r ≤ c := (pow_le_pow_iff_left₀ hr hc0 (by norm_num)).mp h3
  exact hq.trans (pow_le_pow_left₀ hr hrc 4)

lemma triple_step (h : Trace u ρ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {k : ℕ}
    (hk : u k ≤ c ^ 27) : u (k + 3) ≤ (c ^ 2) ^ 27 := by
  have e1 : c ^ 27 = (c ^ 9) ^ 3 := by ring
  have e2 : (c ^ 9) ^ 4 = (c ^ 12) ^ 3 := by ring
  have e3 : (c ^ 12) ^ 4 = (c ^ 16) ^ 3 := by ring
  have e4 : (c ^ 16) ^ 4 = c ^ 64 := by ring
  have e5 : (c ^ 2) ^ 27 = c ^ 54 := by ring
  have h1 : u (k + 1) ≤ (c ^ 9) ^ 4 :=
    cube_step (h.step_nonneg k) (pow_nonneg hc0 9) (h.nonneg _) (h.quartic k) (h.cubic k)
      (hk.trans_eq e1)
  have h2 : u (k + 2) ≤ (c ^ 12) ^ 4 :=
    cube_step (h.step_nonneg (k + 1)) (pow_nonneg hc0 12) (h.nonneg _) (h.quartic (k + 1))
      (h.cubic (k + 1)) (h1.trans_eq e2)
  have h3 : u (k + 3) ≤ (c ^ 16) ^ 4 :=
    cube_step (h.step_nonneg (k + 2)) (pow_nonneg hc0 16) (h.nonneg _) (h.quartic (k + 2))
      (h.cubic (k + 2)) (h2.trans_eq e3)
  rw [e5]
  exact (h3.trans_eq e4).trans (pow_le_pow_of_le_one hc0 hc1 (by norm_num))

lemma phase_two (h : Trace u ρ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {k : ℕ}
    (hk : u k ≤ c ^ 27) (j : ℕ) : u (k + 3 * j) ≤ (c ^ 27) ^ (2 ^ j) := by
  have hgen : ∀ j : ℕ, u (k + 3 * j) ≤ (c ^ (2 ^ j)) ^ 27 := by
    intro j
    induction j with
    | zero => simpa using hk
    | succ j ih =>
      have hc' : c ^ 2 ^ j ≤ 1 := pow_le_one₀ hc0 hc1
      have ht := triple_step h (pow_nonneg hc0 (2 ^ j)) hc' ih
      have e : k + 3 * (j + 1) = k + 3 * j + 3 := by ring
      have e2 : (c ^ 2 ^ j) ^ 2 = c ^ 2 ^ (j + 1) := by rw [← pow_mul, pow_succ]
      rw [e, ← e2]
      exact ht
  have hj := hgen j
  have e : (c ^ 2 ^ j) ^ 27 = (c ^ 27) ^ 2 ^ j := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [e] at hj
  exact hj

lemma small_base : ((91 : ℝ) / 100) ^ 27 ≤ Real.exp (-1) := by
  have he := Real.exp_one_lt_d9
  have hpos := Real.exp_pos 1
  have h3 : (1 : ℝ) / 3 ≤ (Real.exp 1)⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hpos (by linarith)
  rw [Real.exp_neg]
  have hn : ((91 : ℝ) / 100) ^ 27 ≤ 1 / 3 := by norm_num
  exact hn.trans h3

theorem trace_bound (h : Trace u ρ) {T0 : ℝ} (hT0 : 0 ≤ T0) (h0 : u 0 ≤ T0 ^ 4) (j K : ℕ)
    (hK : 16 * T0 + 1 + 3 * (j : ℝ) ≤ K) : u K ≤ Real.exp (-(2 : ℝ) ^ j) := by
  have hk1 : 16 * T0 ≤ (⌈16 * T0⌉₊ : ℝ) := Nat.le_ceil _
  have hk1' : (⌈16 * T0⌉₊ : ℝ) < 16 * T0 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hle : ⌈16 * T0⌉₊ + 3 * j ≤ K := by
    have hc : ((⌈16 * T0⌉₊ + 3 * j : ℕ) : ℝ) ≤ K := by
      push_cast
      linarith
    exact_mod_cast hc
  have h1 := phase_one_end h h0 hT0 hk1
  have hc : (1 : ℝ) / 16 ≤ ((91 : ℝ) / 100) ^ 27 := by norm_num
  have h2 := phase_two h (c := 91 / 100) (by norm_num) (by norm_num) (h1.trans hc) j
  have h3 := h.antitone hle
  calc
    u K ≤ u (⌈16 * T0⌉₊ + 3 * j) := h3
    _ ≤ (((91 : ℝ) / 100) ^ 27) ^ (2 ^ j) := h2
    _ ≤ (Real.exp (-1)) ^ (2 ^ j) := pow_le_pow_left₀ (by positivity) small_base _
    _ = Real.exp (-(2 : ℝ) ^ j) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

end LongTails.Proofs.CubicNewtonPLRecursion
