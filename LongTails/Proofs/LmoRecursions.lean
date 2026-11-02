import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic

namespace OracleTemplate.NormBallLMO

lemma geometric_recursion {u : ℕ → ℝ} {β η : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hη : 0 ≤ η)
    (h : ∀ k, u (k + 1) ≤ (1 - β) * u k + η) : ∀ k, u k ≤ η / β + (1 - β) ^ k * u 0 := by
  intro k
  induction k with
  | zero =>
      have : 0 ≤ η / β := div_nonneg hη hβ.le
      simp only [pow_zero, one_mul]
      linarith
  | succ k ih =>
      have h1 : 0 ≤ 1 - β := by linarith
      have e : (1 - β) * (η / β) + η = η / β := by field_simp; ring
      calc u (k + 1) ≤ (1 - β) * u k + η := h k
        _ ≤ (1 - β) * (η / β + (1 - β) ^ k * u 0) + η := by gcongr
        _ = η / β + (1 - β) ^ (k + 1) * u 0 := by rw [mul_add, pow_succ]; linarith [e]

lemma vanishing_step {s t c : ℝ} (hs : 2 ≤ s) (ht : 0 ≤ t) (hts : t ^ 2 = s ^ 2 - 1) (hc : 0 ≤ c) :
    (1 - 1 / (2 * s)) * (4 * c / t) + c / s ^ 2 ≤ 4 * c / s := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · rw [← h] at hts; nlinarith
  have hA : 0 ≤ t * (4 * s - 1) := by nlinarith
  have hB : 0 ≤ 2 * s * (2 * s - 1) := by nlinarith
  have hsq : (2 * s * (2 * s - 1)) ^ 2 ≤ (t * (4 * s - 1)) ^ 2 := by
    have e : (t * (4 * s - 1)) ^ 2 = (s ^ 2 - 1) * (4 * s - 1) ^ 2 := by rw [mul_pow, hts]
    rw [e]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ s - 2) (by nlinarith : (0 : ℝ) ≤ 8 * s ^ 2 - 3 * s + 2)]
  have hkey : 2 * s * (2 * s - 1) ≤ t * (4 * s - 1) := by
    by_contra hlt
    push Not at hlt
    nlinarith [mul_self_lt_mul_self hA hlt]
  have e : (1 - 1 / (2 * s)) * (4 * c / t) + c / s ^ 2 = c * (4 * s ^ 2 - 2 * s + t) / (s ^ 2 * t) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) hs0]
  have : c * (4 * s ^ 2 - 2 * s + t) * s ≤ 4 * c * (s ^ 2 * t) := by
    have h2 : 4 * s ^ 2 - 2 * s + t ≤ 4 * s * t := by nlinarith
    have := mul_le_mul_of_nonneg_left h2 hc
    nlinarith
  linarith

lemma vanishing_recursion {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hu : ∀ k, 0 ≤ u k) (h0 : u 0 ≤ c)
    (h : ∀ k : ℕ, u (k + 1) ≤ (1 - 1 / (2 * Real.sqrt ((k : ℝ) + 2))) * u k + c / ((k : ℝ) + 2)) :
    ∀ k : ℕ, u k ≤ 4 * c / Real.sqrt ((k : ℝ) + 1) := by
  have hcoef : ∀ k : ℕ, 0 ≤ 1 - 1 / (2 * Real.sqrt ((k : ℝ) + 2)) ∧
      1 - 1 / (2 * Real.sqrt ((k : ℝ) + 2)) ≤ 1 := by
    intro k
    have hs : 1 ≤ Real.sqrt ((k : ℝ) + 2) := by
      have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (k : ℝ) + 2 by
        linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
      rwa [Real.sqrt_one] at this
    constructor
    · rw [sub_nonneg, div_le_one (by linarith : (0 : ℝ) < 2 * Real.sqrt ((k : ℝ) + 2))]
      linarith
    · have : 0 ≤ 1 / (2 * Real.sqrt ((k : ℝ) + 2)) := by positivity
      linarith
  have h1 : u 1 ≤ 3 / 2 * c := by
    have := h 0
    have hc0 := hcoef 0
    simp only [Nat.cast_zero, zero_add] at this hc0
    nlinarith [hu 0]
  have h2 : u 2 ≤ 11 / 6 * c := by
    have := h 1
    have hc1 := hcoef 1
    have hcu := mul_le_of_le_one_left (hu 1) hc1.2
    have e : c / (((1 : ℕ) : ℝ) + 2) = c / 3 := by norm_num
    rw [e] at this
    linarith
  have hbig : ∀ k : ℕ, u (k + 2) ≤ 4 * c / Real.sqrt ((k : ℝ) + 3) := by
    intro k
    induction k with
    | zero =>
        have hs : Real.sqrt 3 ≤ 24 / 11 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hs0 : 0 < Real.sqrt 3 := by positivity
        norm_num
        rw [le_div_iff₀ hs0]
        nlinarith
    | succ k ih =>
        set s := Real.sqrt (((k + 1 : ℕ) : ℝ) + 3)
        set t := Real.sqrt ((k : ℝ) + 3)
        have hs2 : s ^ 2 = (k : ℝ) + 4 := by
          rw [Real.sq_sqrt (by positivity)]; push_cast; ring
        have ht2 : t ^ 2 = (k : ℝ) + 3 := Real.sq_sqrt (by positivity)
        have hs : 2 ≤ s := by
          rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]]
          exact Real.sqrt_le_sqrt (by push_cast; linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
        have hrec := h (k + 2)
        have hk : ((k + 2 : ℕ) : ℝ) + 2 = (((k + 1 : ℕ) : ℝ) + 3) := by push_cast; ring
        rw [hk] at hrec
        have hc' := hcoef (k + 2)
        rw [hk] at hc'
        have step := vanishing_step (t := t) hs (Real.sqrt_nonneg _) (by rw [hs2, ht2]; ring) hc
        have hsq : (((k + 1 : ℕ) : ℝ) + 3) = s ^ 2 := by rw [hs2]; push_cast; ring
        calc u (k + 1 + 2) = u (k + 2 + 1) := by ring_nf
          _ ≤ (1 - 1 / (2 * s)) * u (k + 2) + c / (((k + 1 : ℕ) : ℝ) + 3) := hrec
          _ ≤ (1 - 1 / (2 * s)) * (4 * c / t) + c / s ^ 2 := by
              rw [hsq]
              gcongr
              exact hc'.1
          _ ≤ 4 * c / s := step
  intro k
  rcases k with _ | _ | k
  · simp only [Nat.cast_zero, zero_add, Real.sqrt_one, div_one]; linarith
  · have hs : Real.sqrt 2 ≤ 8 / 3 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hs0 : 0 < Real.sqrt 2 := by positivity
    norm_num
    rw [le_div_iff₀ hs0]
    nlinarith
  · have := hbig k
    have e : ((k + 1 + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 3 := by push_cast; ring
    rw [e]; exact this

lemma sqrt_add3_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sq_sqrt hc
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b),
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c),
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)]

lemma geom_sum_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∑ k ∈ Finset.range n, q ^ k ≤ 1 / (1 - q) := by
  rw [geom_sum_eq hq1.ne n]
  have e : (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) := by
    rw [← neg_sub (q ^ n) 1, ← neg_sub q 1, neg_div_neg_eq]
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hq0 n]) (by linarith)

lemma inv_one_sub_sqrt_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    1 / (1 - Real.sqrt (1 - α / 2)) ≤ 4 / α := by
  set q := Real.sqrt (1 - α / 2)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 1 - α / 2 := Real.sq_sqrt (by linarith)
  have hq1 : q < 1 := by nlinarith
  rw [div_le_div_iff₀ (by linarith) hα]
  nlinarith

lemma quarter_step (i : ℕ) :
    1 / ((i : ℝ) + 1) ^ (1 / 4 : ℝ) ≤
      4 / 3 * (((i : ℝ) + 1) ^ (3 / 4 : ℝ) - (i : ℝ) ^ (3 / 4 : ℝ)) := by
  set a : ℝ := (i : ℝ) + 1
  have ha : 0 < a := by positivity
  have hb : 0 ≤ (i : ℝ) := i.cast_nonneg
  have hamgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := 3 / 4) (w₂ := 1 / 4) (p₁ := (i : ℝ))
    (p₂ := a) (by norm_num) (by norm_num) hb ha.le (by norm_num)
  have hq : 0 < a ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ha _
  have hsplit : a ^ (3 / 4 : ℝ) * a ^ (1 / 4 : ℝ) = a := by
    rw [← Real.rpow_add ha]; norm_num
  rw [div_le_iff₀ hq]
  have e : 4 / 3 * (a ^ (3 / 4 : ℝ) - (i : ℝ) ^ (3 / 4 : ℝ)) * a ^ (1 / 4 : ℝ) =
      4 / 3 * (a - (i : ℝ) ^ (3 / 4 : ℝ) * a ^ (1 / 4 : ℝ)) := by
    rw [show 4 / 3 * (a ^ (3 / 4 : ℝ) - (i : ℝ) ^ (3 / 4 : ℝ)) * a ^ (1 / 4 : ℝ) =
      4 / 3 * (a ^ (3 / 4 : ℝ) * a ^ (1 / 4 : ℝ)) - 4 / 3 * ((i : ℝ) ^ (3 / 4 : ℝ) * a ^ (1 / 4 : ℝ))
      by ring, hsplit]
    ring
  rw [e]
  have hai : a - (i : ℝ) = 1 := by simp [a]
  nlinarith

lemma sum_quarter_le (n : ℕ) :
    ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 1) ^ (1 / 4 : ℝ) ≤ 4 / 3 * (n : ℝ) ^ (3 / 4 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have := quarter_step n
      push_cast
      linarith

lemma vanishing_recursion_lt {u : ℕ → ℝ} {c : ℝ} {n : ℕ} (hc : 0 ≤ c) (hu : ∀ k, 0 ≤ u k)
    (h0 : u 0 ≤ c)
    (h : ∀ k : ℕ, k + 1 < n →
      u (k + 1) ≤ (1 - 1 / (2 * Real.sqrt ((k : ℝ) + 2))) * u k + c / ((k : ℝ) + 2)) :
    ∀ k : ℕ, k < n → u k ≤ 4 * c / Real.sqrt ((k : ℝ) + 1) := by
  set v : ℕ → ℝ := fun k => if k < n then u k else 0
  have hv : ∀ k, 0 ≤ v k := fun k => by simp only [v]; split_ifs <;> simp [hu]
  have hv0 : v 0 ≤ c := by simp only [v]; split_ifs <;> linarith
  have hcoef : ∀ k : ℕ, 0 ≤ 1 - 1 / (2 * Real.sqrt ((k : ℝ) + 2)) := by
    intro k
    have hs : 1 ≤ Real.sqrt ((k : ℝ) + 2) := by
      have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ (k : ℝ) + 2 by
        linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])
      rwa [Real.sqrt_one] at this
    rw [sub_nonneg, div_le_one (by linarith : (0 : ℝ) < 2 * Real.sqrt ((k : ℝ) + 2))]
    linarith
  have hrec : ∀ k : ℕ,
      v (k + 1) ≤ (1 - 1 / (2 * Real.sqrt ((k : ℝ) + 2))) * v k + c / ((k : ℝ) + 2) := by
    intro k
    by_cases hk : k + 1 < n
    · have hk' : k < n := by omega
      simp only [v, hk, hk', ite_true]
      exact h k hk
    · simp only [v, hk, ite_false]
      have := mul_nonneg (hcoef k) (hv k)
      have : 0 ≤ c / ((k : ℝ) + 2) := by positivity
      linarith
  intro k hk
  have := vanishing_recursion hc hv hv0 hrec k
  simpa [v, hk] using this

lemma quarter_powers (T : ℕ) :
    1 ≤ ((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) ∧
      ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) = (((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) ^ 3 ∧
      ((T + 1 : ℕ) : ℝ) = (((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) ^ 4 ∧
      Real.sqrt ((T + 1 : ℕ) : ℝ) = (((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
  set x : ℝ := ((T + 1 : ℕ) : ℝ)
  have hx : 1 ≤ x := by simp [x]
  have hx0 : 0 ≤ x := by linarith
  have hp : ∀ k : ℕ, (x ^ (1 / 4 : ℝ)) ^ k = x ^ ((1 / 4 : ℝ) * k) := fun k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
  refine ⟨Real.one_le_rpow hx (by norm_num), ?_, ?_, ?_⟩
  · rw [hp]; norm_num
  · rw [hp]; norm_num
  · rw [hp, Real.sqrt_eq_rpow]; norm_num

lemma horizon_sqrt_le {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    M / Real.sqrt ((⌈(M / ε) ^ 2⌉₊ : ℝ) + 1) ≤ ε := by
  have hT : (M / ε) ^ 2 ≤ (⌈(M / ε) ^ 2⌉₊ : ℝ) + 1 := (Nat.le_ceil _).trans (by linarith)
  have hs : M / ε ≤ Real.sqrt ((⌈(M / ε) ^ 2⌉₊ : ℝ) + 1) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; exact hT
  have hs0 : 0 < Real.sqrt ((⌈(M / ε) ^ 2⌉₊ : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_iff₀ hs0]
  rw [div_le_iff₀ hε] at hs
  linarith

lemma horizon_quarter_le {M ε : ℝ} (hε : 0 < ε) :
    M / ((⌈(M / ε) ^ 4⌉₊ + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ ε := by
  obtain ⟨hv1, -, hn, -⟩ := quarter_powers ⌈(M / ε) ^ 4⌉₊
  set v := ((⌈(M / ε) ^ 4⌉₊ + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)
  have hv0 : 0 < v := by linarith
  have hT : (M / ε) ^ 4 ≤ v ^ 4 := by
    rw [← hn]; push_cast; exact (Nat.le_ceil _).trans (by linarith)
  have hs : M / ε ≤ v := by
    by_contra h
    push Not at h
    have := pow_lt_pow_left₀ h hv0.le (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  rw [div_le_iff₀ hv0]
  rw [div_le_iff₀ hε] at hs
  linarith

lemma quarter_split {A B : ℝ} (hB : 0 ≤ B) (T : ℕ) :
    A / ((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) + B / ((T + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤
      (A + B) / ((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨hv1, hw, -, -⟩ := quarter_powers T
  rw [hw, add_div]
  set v := ((T + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)
  have hv0 : 0 < v := by linarith
  have : B / v ^ 3 ≤ B / v := by
    apply div_le_div_of_nonneg_left hB hv0
    have hv2 : 1 ≤ v ^ 2 := by nlinarith
    nlinarith
  linarith

end OracleTemplate.NormBallLMO
