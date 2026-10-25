import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open Finset

namespace LongTails.Proofs.BFGSInequalities

lemma sum_inv_ge {k : ℕ} (hk : 0 < k) (ζ Q : ℕ → ℝ) (hζ : ∀ i < k, 0 < ζ i)
    (hQ : ∀ i < k, 0 < Q i) (hprod : ∏ i ∈ range k, ζ i ≤ Real.exp k) :
    (k : ℝ) ^ 2 / (Real.exp 1 * ∑ i ∈ range k, Q i) ≤ ∑ i ∈ range k, 1 / (ζ i * Q i) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set r : ℕ → ℝ := fun i => 1 / Real.sqrt (ζ i)
  have hr : ∀ i ∈ range k, 0 < r i := fun i hi =>
    one_div_pos.mpr (Real.sqrt_pos.mpr (hζ i (mem_range.mp hi)))
  have hr2 : ∀ i ∈ range k, r i ^ 2 / Q i = 1 / (ζ i * Q i) := by
    intro i hi
    simp only [r, div_pow, one_pow, Real.sq_sqrt (hζ i (mem_range.mp hi)).le]
    rw [div_div]
  have hQs : 0 < ∑ i ∈ range k, Q i :=
    sum_pos (fun i hi => hQ i (mem_range.mp hi)) (nonempty_range_iff.mpr hk.ne')
  have titu := sq_sum_div_le_sum_sq_div (range k) r (g := Q) (fun i hi => hQ i (mem_range.mp hi))
  rw [sum_congr rfl hr2] at titu
  have hP : 0 < ∏ i ∈ range k, ζ i := prod_pos fun i hi => hζ i (mem_range.mp hi)
  have amgm := Real.geom_mean_le_arith_mean_weighted (range k) (fun _ => 1 / (k : ℝ)) r
    (fun _ _ => by positivity) (by simp [hkR.ne']) (fun i hi => (hr i hi).le)
  rw [Real.finsetProd_rpow _ _ (fun i hi => (hr i hi).le), ← mul_sum] at amgm
  have hprodr : ∏ i ∈ range k, r i = 1 / Real.sqrt (∏ i ∈ range k, ζ i) := by
    simp only [r]
    rw [prod_div_distrib, prod_const_one,
      Real.sqrt_prod _ (fun i hi => (hζ i (mem_range.mp hi)).le)]
  have hlow : Real.exp (-(1 / 2)) ≤ (∏ i ∈ range k, r i) ^ (1 / (k : ℝ)) := by
    rw [hprodr]
    have h1 : Real.sqrt (∏ i ∈ range k, ζ i) ≤ Real.exp ((k : ℝ) / 2) := by
      rw [show Real.exp ((k : ℝ) / 2) = Real.sqrt (Real.exp k) by
        rw [← Real.exp_half]]
      exact Real.sqrt_le_sqrt hprod
    have h2 : Real.exp (-((k : ℝ) / 2)) ≤ 1 / Real.sqrt (∏ i ∈ range k, ζ i) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr hP) h1
    have h3 := Real.rpow_le_rpow (Real.exp_pos _).le h2 (by positivity : (0 : ℝ) ≤ 1 / k)
    rw [← Real.exp_mul] at h3
    have e : -((k : ℝ) / 2) * (1 / k) = -(1 / 2) := by
      field_simp
    rwa [e] at h3
  have hsum : (k : ℝ) * Real.exp (-(1 / 2)) ≤ ∑ i ∈ range k, r i := by
    have := hlow.trans amgm
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hkR] at this
    linarith
  have hsq : (k : ℝ) ^ 2 * Real.exp (-1) ≤ (∑ i ∈ range k, r i) ^ 2 := by
    have h0 : 0 ≤ (k : ℝ) * Real.exp (-(1 / 2)) := by positivity
    have := pow_le_pow_left₀ h0 hsum 2
    rw [mul_pow, ← Real.exp_nat_mul] at this
    convert this using 2
    norm_num
  have hfin : (k : ℝ) ^ 2 / (Real.exp 1 * ∑ i ∈ range k, Q i) ≤
      (∑ i ∈ range k, r i) ^ 2 / ∑ i ∈ range k, Q i := by
    rw [div_le_div_iff₀ (by positivity) hQs]
    have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    have h1 := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ Real.exp 1 * ∑ i ∈ range k, Q i)
    calc (k : ℝ) ^ 2 * ∑ i ∈ range k, Q i
        = (k : ℝ) ^ 2 * Real.exp (-1) * (Real.exp 1 * ∑ i ∈ range k, Q i) := by
          rw [show (k : ℝ) ^ 2 * Real.exp (-1) * (Real.exp 1 * ∑ i ∈ range k, Q i)
            = (k : ℝ) ^ 2 * (Real.exp (-1) * Real.exp 1) * ∑ i ∈ range k, Q i by ring, he, mul_one]
      _ ≤ (∑ i ∈ range k, r i) ^ 2 * (Real.exp 1 * ∑ i ∈ range k, Q i) := h1
  linarith

lemma harmonic_le (k : ℕ) : ∑ i ∈ range k, 1 / ((i : ℝ) + 1) ≤ 2 * Real.sqrt k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hs1 : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hsk : Real.sqrt k ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hprod : (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k) * (Real.sqrt ((k : ℝ) + 1) + Real.sqrt k)
        = 1 := by
      have a := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
      have b := Real.sq_sqrt hk0
      nlinarith
    have hsq1 : Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
      have a := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
      nlinarith [Real.sqrt_nonneg ((k : ℝ) + 1)]
    have step : 1 / ((k : ℝ) + 1) ≤ 2 * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.sqrt_nonneg (k : ℝ)]
    push_cast
    linarith

lemma pseries_le (k : ℕ) :
    ∑ i ∈ range k, 1 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1)) ≤ 3 := by
  suffices h : ∀ k : ℕ, 1 ≤ k →
      ∑ i ∈ range k, 1 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1)) ≤ 3 - 2 / Real.sqrt k by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp
    · have := h k hpos
      have : 0 ≤ 2 / Real.sqrt k := by positivity
      linarith
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      norm_num
    · rw [sum_range_succ]
      have := ih hpos
      have hkR : (0 : ℝ) < k := by exact_mod_cast hpos
      have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
      have hs1 : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hle : Real.sqrt k ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      have a := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
      have b := Real.sq_sqrt hkR.le
      have step : 1 / (((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)) ≤
          2 / Real.sqrt k - 2 / Real.sqrt ((k : ℝ) + 1) := by
        rw [div_sub_div _ _ hsk.ne' hs1.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        have hd : 0 ≤ Real.sqrt ((k : ℝ) + 1) - Real.sqrt k := by linarith
        have hprod : (Real.sqrt ((k : ℝ) + 1) - Real.sqrt k) *
            (Real.sqrt ((k : ℝ) + 1) + Real.sqrt k) = 1 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hle hd, mul_pos hsk hs1, mul_pos hs1 hs1]
      push_cast
      linarith

lemma bootstrap {D : ℕ → ℝ} {M κ γ : ℝ} (hM : 0 ≤ M) (hκ : 1 ≤ κ) (hγ0 : 0 < γ)
    (hγ : γ ≤ 1 / 4) (hmono : ∀ i, D (i + 1) ≤ D i) (hDinit : D 0 ≤ M / 2)
    (hrec : ∀ k : ℕ, 1 ≤ k →
      D k ≤ Real.exp 1 * (M + 2 * κ * ∑ i ∈ range k, D (i + 1)) / (γ * (k : ℝ) ^ 2)) :
    ∀ k : ℕ, 1 ≤ k → D k ≤ 1200 * κ ^ 3 * M / (γ ^ 3 * (k : ℝ) ^ 2) := by
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  set e := Real.exp 1
  have hanti : ∀ i, D i ≤ D 0 := by
    intro i
    induction i with
    | zero => exact le_rfl
    | succ i ih => exact (hmono i).trans ih
  set a1 := e * (1 + κ) * M / γ
  have st1 : ∀ k : ℕ, 1 ≤ k → D k ≤ a1 / k := by
    intro k hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hS : ∑ i ∈ range k, D (i + 1) ≤ k * (M / 2) := by
      have := sum_le_sum fun i (_ : i ∈ range k) => (hanti (i + 1)).trans hDinit
      simpa using this
    refine (hrec k hk).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have ha : a1 * (γ * (k : ℝ) ^ 2) = e * (1 + κ) * M * (k : ℝ) ^ 2 := by
      simp only [a1]
      field_simp
    rw [ha]
    have : e * (M + 2 * κ * ∑ i ∈ range k, D (i + 1)) ≤ e * (M + κ * k * M) := by
      apply mul_le_mul_of_nonneg_left _ he0.le
      nlinarith
    have h2 := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ k)
    have h3 : e * (M + κ * k * M) * k ≤ e * (1 + κ) * M * (k : ℝ) ^ 2 := by
      have : e * M * k ≤ e * M * (k * k) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg he0.le hM)
        nlinarith
      nlinarith
    linarith
  set a2 := e * (M + 4 * κ * a1) / γ
  have ha1 : 0 ≤ a1 := by positivity
  have st2 : ∀ k : ℕ, 1 ≤ k → D k ≤ a2 / ((k : ℝ) * Real.sqrt k) := by
    intro k hk
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hsk : 1 ≤ Real.sqrt k := by rw [Real.one_le_sqrt]; exact hkR
    have hsq : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (by positivity)
    have hS : ∑ i ∈ range k, D (i + 1) ≤ 2 * a1 * Real.sqrt k := by
      have h1 : ∑ i ∈ range k, D (i + 1) ≤ ∑ i ∈ range k, a1 * (1 / ((i : ℝ) + 1)) := by
        apply sum_le_sum
        intro i _
        have := st1 (i + 1) (by omega)
        push_cast at this
        rw [mul_one_div]
        exact this
      rw [← mul_sum] at h1
      have h2 := mul_le_mul_of_nonneg_left (harmonic_le k) ha1
      linarith
    refine (hrec k hk).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simp only [a2]
    have hk2 : (k : ℝ) ^ 2 = k * k := by ring
    have hA : e * (M + 2 * κ * ∑ i ∈ range k, D (i + 1)) ≤ e * (M + 4 * κ * a1 * Real.sqrt k) := by
      apply mul_le_mul_of_nonneg_left _ he0.le
      nlinarith
    have hB : e * (M + 4 * κ * a1 * Real.sqrt k) * ((k : ℝ) * Real.sqrt k) ≤
        e * (M + 4 * κ * a1) * ((k : ℝ) ^ 2) := by
      rw [hk2]
      have hM' : M * ((k : ℝ) * Real.sqrt k) ≤ M * (k * k) := by
        apply mul_le_mul_of_nonneg_left _ hM
        nlinarith
      have hK : 4 * κ * a1 * Real.sqrt k * ((k : ℝ) * Real.sqrt k) = 4 * κ * a1 * (k * k) := by
        have : Real.sqrt k * ((k : ℝ) * Real.sqrt k) = k * k := by nlinarith
        calc 4 * κ * a1 * Real.sqrt k * ((k : ℝ) * Real.sqrt k)
            = 4 * κ * a1 * (Real.sqrt k * ((k : ℝ) * Real.sqrt k)) := by ring
          _ = 4 * κ * a1 * (k * k) := by rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hM' he0.le]
    have hpos : 0 ≤ (k : ℝ) * Real.sqrt k := by positivity
    calc e * (M + 2 * κ * ∑ i ∈ range k, D (i + 1)) * ((k : ℝ) * Real.sqrt k)
        ≤ e * (M + 4 * κ * a1 * Real.sqrt k) * ((k : ℝ) * Real.sqrt k) :=
          mul_le_mul_of_nonneg_right hA hpos
      _ ≤ e * (M + 4 * κ * a1) * ((k : ℝ) ^ 2) := hB
      _ = e * (M + 4 * κ * a1) / γ * (γ * (k : ℝ) ^ 2) := by field_simp
  have ha2 : 0 ≤ a2 := by positivity
  have st3 : ∀ k : ℕ, 1 ≤ k → D k ≤ e * (M + 6 * κ * a2) / (γ * (k : ℝ) ^ 2) := by
    intro k hk
    have hS : ∑ i ∈ range k, D (i + 1) ≤ 3 * a2 := by
      have h1 : ∑ i ∈ range k, D (i + 1) ≤
          ∑ i ∈ range k, a2 * (1 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1))) := by
        apply sum_le_sum
        intro i _
        have := st2 (i + 1) (by omega)
        push_cast at this
        rw [mul_one_div]
        exact this
      rw [← mul_sum] at h1
      have h2 := mul_le_mul_of_nonneg_left (pseries_le k) ha2
      linarith
    refine (hrec k hk).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ he0.le
    nlinarith
  intro k hk
  refine (st3 k hk).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simp only [a2, a1]
  have hγ3 : 0 < γ ^ 3 := by positivity
  have hk2 : 0 < (k : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    positivity
  have key : e * (M + 6 * κ * (e * (M + 4 * κ * (e * (1 + κ) * M / γ)) / γ)) * γ ^ 2 ≤
      1200 * κ ^ 3 * M := by
    have expand : e * (M + 6 * κ * (e * (M + 4 * κ * (e * (1 + κ) * M / γ)) / γ)) * γ ^ 2 =
        e * γ ^ 2 * M + 6 * e ^ 2 * κ * γ * M + 24 * e ^ 3 * κ ^ 2 * (1 + κ) * M := by
      field_simp
      ring
    rw [expand]
    have he2 : e ^ 2 ≤ 7.39 := by nlinarith
    have he3 : e ^ 3 ≤ 20.1 := by nlinarith
    have hκ2 : κ ^ 2 ≤ κ ^ 3 := by nlinarith
    have hκ1 : κ ≤ κ ^ 3 := by nlinarith
    have hκ0 : 1 ≤ κ ^ 3 := by nlinarith
    have hγ2 : γ ^ 2 ≤ 1 / 16 := by nlinarith
    have t1 : e * γ ^ 2 * M ≤ 1 * κ ^ 3 * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      have : e * γ ^ 2 ≤ 2.72 * (1 / 16) :=
        mul_le_mul (by linarith) hγ2 (by positivity) (by norm_num)
      linarith
    have t2 : 6 * e ^ 2 * κ * γ * M ≤ 12 * κ ^ 3 * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      have h1 : e ^ 2 * γ ≤ 7.39 * (1 / 4) :=
        mul_le_mul he2 hγ (by positivity) (by norm_num)
      have h2 : 6 * e ^ 2 * κ * γ = 6 * (e ^ 2 * γ) * κ := by ring
      rw [h2]
      have h3 : 6 * (e ^ 2 * γ) * κ ≤ 6 * (7.39 * (1 / 4)) * κ := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        linarith
      linarith
    have t3 : 24 * e ^ 3 * κ ^ 2 * (1 + κ) * M ≤ 966 * κ ^ 3 * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      have h1 : κ ^ 2 * (1 + κ) ≤ 2 * κ ^ 3 := by nlinarith
      have h2 : 24 * e ^ 3 * κ ^ 2 * (1 + κ) = 24 * e ^ 3 * (κ ^ 2 * (1 + κ)) := by ring
      rw [h2]
      have h3 : 24 * e ^ 3 * (κ ^ 2 * (1 + κ)) ≤ 24 * 20.1 * (2 * κ ^ 3) :=
        mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
      linarith
    have hκM : 0 ≤ κ ^ 3 * M := mul_nonneg (by positivity) hM
    linarith
  have := mul_le_mul_of_nonneg_right key hk2.le
  nlinarith [this]

end LongTails.Proofs.BFGSInequalities
