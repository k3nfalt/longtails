import LongTails.Proofs.CovarianceSoftCutTuning
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutBudget

lemma scale_estimates (D z : ℝ) (hD : 1 ≤ D) (hz : 1 ≤ z) :
    let Q := 1+Real.log (16*D*(1+z))
    4 ≤ Q ∧ Real.log D ≤ Q-4 ∧ Real.log z ≤ Q-3 ∧
      Real.log (16*z) ≤ Q-1 ∧ Real.log Q ≤ Q/2 := by
  let Q := 1+Real.log (16*D*(1+z))
  have hDpos : 0 < D := by linarith
  have hzpos : 0 < z := by linarith
  have hbase : 0 < 16*(1+z) := by positivity
  have hlogtwo : (1/2 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have hlog32 : (3 : ℝ) ≤ Real.log 32 := by
    have he : Real.log (32 : ℝ) = 5*Real.log 2 := by
      have hp := Real.log_pow (2 : ℝ) 5
      norm_num at hp
      exact hp
    rw [he]
    linarith [Real.log_two_gt_d9]
  have hbaseLog : 3 ≤ Real.log (16*(1+z)) :=
    hlog32.trans (Real.log_le_log (by norm_num) (by linarith))
  have hsplit : Q = 1+Real.log D+Real.log (16*(1+z)) := by
    dsimp [Q]
    have he : 16*D*(1+z) = D*(16*(1+z)) := by ring
    rw [he, Real.log_mul hDpos.ne' hbase.ne']
    ring
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hQ : 4 ≤ Q := by linarith
  have hDz : Real.log D ≤ Q-4 := by linarith
  have hlog16 : (2 : ℝ) ≤ Real.log 16 := by
    have he : Real.log (16 : ℝ) = 4*Real.log 2 := by
      have hp := Real.log_pow (2 : ℝ) 4
      norm_num at hp
      exact hp
    rw [he]
    linarith
  have hsmall : Real.log (16*z) ≤ Q-1 := by
    dsimp [Q]
    have he : 1+Real.log (16*D*(1+z))-1 = Real.log (16*D*(1+z)) := by ring
    rw [he]
    apply Real.log_le_log (by positivity)
    nlinarith
  have hzlog : Real.log z ≤ Q-3 := by
    rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hzpos.ne'] at hsmall
    linarith
  have hQlog : Real.log Q ≤ Q/2 := by
    have hhalf : 0 < Q/2 := by linarith
    have hb := Real.log_le_sub_one_of_pos hhalf
    have he : Real.log Q = Real.log (Q/2)+Real.log 2 := by
      rw [← Real.log_mul hhalf.ne' (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      ring
    linarith
  exact ⟨hQ, hDz, hzlog, hsmall, hQlog⟩

lemma log48_le_four : Real.log 48 ≤ 4 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 48)).mpr
  calc
    (48 : ℝ) ≤ (8/3 : ℝ)^4 := by norm_num
    _ ≤ (Real.exp 1)^4 := by gcongr; linarith [Real.exp_one_gt_d9]
    _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num

lemma log2880_le_nine : Real.log 2880 ≤ 9 := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2880)).mpr
  calc
    (2880 : ℝ) ≤ (5/2 : ℝ)^9 := by norm_num
    _ ≤ (Real.exp 1)^9 := by gcongr; linarith [Real.exp_one_gt_d9]
    _ = Real.exp 9 := by rw [← Real.exp_nat_mul]; norm_num

lemma tree_height_bound (D Q : ℝ) (hD : 0 < D) (hQ : 4 ≤ Q)
    (hlogD : Real.log D ≤ Q-4) (hlogQ : Real.log Q ≤ Q/2)
    (H : ℕ) (hT : (2 : ℝ)^H ≤ 48*D*Q) : (H : ℝ) ≤ 4*Q := by
  have hQpos : 0 < Q := by linarith
  have hp := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) H) hT
  rw [Real.log_pow, Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 48) hD).ne' hQpos.ne',
    Real.log_mul (by norm_num : (48 : ℝ) ≠ 0) hD.ne'] at hp
  have htwo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hh := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg H : (0 : ℝ) ≤ H)
  linarith [log48_le_four]

lemma bisection_count_bound (z Q : ℝ) (hz : 1 ≤ z) (hQ : 4 ≤ Q)
    (hlogz : Real.log z ≤ Q-3) (hlogQ : Real.log Q ≤ Q/2)
    (H : ℕ) (hH : 0 < H) (hHbound : (H : ℝ) ≤ 4*Q) :
    (⌈Real.log (8*z*(H : ℝ))/Real.log 2⌉₊ : ℝ) ≤ 5*Q := by
  have hzpos : 0 < z := by linarith
  have hQpos : 0 < Q := by linarith
  have hHone : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hx : 1 ≤ 8*z*(H : ℝ) := by nlinarith
  have hlog : 0 ≤ Real.log (8*z*(H : ℝ)) := Real.log_nonneg hx
  have hlog32 : Real.log (32 : ℝ) ≤ 4 := by
    have he : Real.log (32 : ℝ) = 5*Real.log 2 := by
      have hp := Real.log_pow (2 : ℝ) 5
      norm_num at hp
      exact hp
    rw [he]
    linarith [Real.log_two_lt_d9]
  have hup : Real.log (8*z*(H : ℝ)) ≤ 3*Q/2+1 := by
    have hm : 8*z*(H : ℝ) ≤ 32*z*Q := by nlinarith
    have hh := Real.log_le_log (by positivity : 0 < 8*z*(H : ℝ)) hm
    rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 32) hzpos).ne' hQpos.ne',
      Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hzpos.ne'] at hh
    linarith
  have htwo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hden : 0 < Real.log 2 := by linarith
  have hdiv : Real.log (8*z*(H : ℝ))/Real.log 2 ≤ 2*Real.log (8*z*(H : ℝ)) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hc := Nat.ceil_lt_add_one (div_nonneg hlog hden.le)
  linarith

lemma mom_count_bound (D Q : ℝ) (hD : 1 ≤ D) (hQ : 4 ≤ Q)
    (hlogD : Real.log D ≤ Q-4) (hlogQ : Real.log Q ≤ Q/2)
    (C : ℕ) (hC : (C : ℝ) ≤ 240*D*Q^2) :
    ((2*⌈4*Real.log (12*(max 1 C : ℕ))⌉₊+1 : ℕ) : ℝ) ≤ 32*Q := by
  have hDpos : 0 < D := by linarith
  have hQpos : 0 < Q := by linarith
  have hM : (1 : ℝ) ≤ (max 1 C : ℕ) := by exact_mod_cast (le_max_left 1 C)
  have hMbound : ((max 1 C : ℕ) : ℝ) ≤ 240*D*Q^2 := by
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le _ hC
    nlinarith [sq_nonneg Q, mul_le_mul_of_nonneg_right hD (sq_nonneg Q)]
  have hlog : Real.log (12*(max 1 C : ℕ)) ≤ 2*Q+5 := by
    have hm : 12*((max 1 C : ℕ) : ℝ) ≤ 2880*D*Q^2 := by linarith
    have hh := Real.log_le_log (by positivity : 0 < 12*((max 1 C : ℕ) : ℝ)) hm
    rw [Real.log_mul (mul_pos (by norm_num : (0 : ℝ) < 2880) hDpos).ne'
      (sq_pos_of_pos hQpos).ne', Real.log_mul (by norm_num : (2880 : ℝ) ≠ 0) hDpos.ne',
      Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [log2880_le_nine]
  have hnon : 0 ≤ 4*Real.log (12*(max 1 C : ℕ)) := by
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    linarith
  have hc := Nat.ceil_lt_add_one hnon
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  linarith

lemma aggregate_cost_bound (D V Q : ℝ) (hD : 0 < D) (hV : 0 ≤ V) (hQ : 1 ≤ Q)
    (T b C n m : ℕ)
    (hT : (T : ℝ) ≤ 48*D*Q) (hb : (b : ℝ) ≤ 1+4096*V/D)
    (hC : (C : ℝ) ≤ 240*D*Q^2) (hn : (n : ℝ) ≤ 1+73728*V*Q^2/D)
    (hm : (m : ℝ) ≤ 32*Q) :
    ((T*b+C*n*m : ℕ) : ℝ) ≤ 2^30*(D+V)*Q^5 := by
  have hQpos : 0 < Q := by linarith
  have hgen : (T : ℝ)*b ≤ (48*D*Q)*(1+4096*V/D) :=
    mul_le_mul hT hb (Nat.cast_nonneg b) (by positivity)
  have hsel : (C : ℝ)*n*m ≤ (240*D*Q^2)*(1+73728*V*Q^2/D)*(32*Q) := by
    apply mul_le_mul _ hm (Nat.cast_nonneg m) (by positivity)
    exact mul_le_mul hC hn (Nat.cast_nonneg n) (by positivity)
  have hexpand : (48*D*Q)*(1+4096*V/D)+(240*D*Q^2)*(1+73728*V*Q^2/D)*(32*Q) =
      48*D*Q+196608*V*Q+7680*D*Q^3+566231040*V*Q^5 := by
    field_simp
    ring
  have htotal : ((T*b+C*n*m : ℕ) : ℝ) ≤
      48*D*Q+196608*V*Q+7680*D*Q^3+566231040*V*Q^5 := by
    push_cast
    rw [← hexpand]
    linarith
  have hQ15 : Q ≤ Q^5 := by simpa using (pow_le_pow_right₀ hQ (by decide : 1 ≤ 5))
  have hQ35 : Q^3 ≤ Q^5 := pow_le_pow_right₀ hQ (by decide : 3 ≤ 5)
  have hD15 := mul_le_mul_of_nonneg_left hQ15 hD.le
  have hV15 := mul_le_mul_of_nonneg_left hQ15 hV
  have hD35 := mul_le_mul_of_nonneg_left hQ35 hD.le
  have hD5 : 0 ≤ D*Q^5 := by positivity
  have hV5 : 0 ≤ V*Q^5 := by positivity
  norm_num
  nlinarith

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Algorithms.CovarianceSoftCutMethod
open LongTails.Proofs.CovarianceSoftCutTuning

lemma tuned_work_cost_bound (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hR : 0 < q.R)
    (hε : 0 < q.ε) (hsmall : q.ε < q.L*q.R) :
    (workCost (tunedConfig q) : ℝ) ≤
      2^30*((q.d : ℝ)+q.σ^2*q.R^2/q.ε^2)*(1+Real.log (16*(q.d : ℝ)*(1+q.L*q.R/q.ε)))^5 := by
  let c := tunedConfig q
  let D : ℝ := q.d
  let z := q.L*q.R/q.ε
  let V := q.σ^2*q.R^2/q.ε^2
  let Q := 1+Real.log (16*D*(1+z))
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast hd
  have hDpos : 0 < D := by linarith
  have hz : 1 ≤ z := (le_div_iff₀ hε).mpr (by linarith)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨hQ, hlogD, hlogz, hlog16, hlogQ⟩ := scale_estimates D z hD hz
  change 4 ≤ Q at hQ
  change Real.log (16*z) ≤ Q-1 at hlog16
  have hQpos : 0 < Q := by linarith
  have hheight := tuned_height q hε hsmall
  have hH : 0 < c.H := hheight.1
  have hHpos : (0 : ℝ) < c.H := by exact_mod_cast hH
  have hT : ((2^c.H : ℕ) : ℝ) ≤ 48*D*Q := by
    have he : 16*q.L*q.R/q.ε = 16*z := by dsimp [z]; ring
    rw [he] at hheight
    have hm := mul_le_mul_of_nonneg_left hlog16 hDpos.le
    have hh : 1+D*Real.log (16*z) ≤ D*Q := by nlinarith
    exact hheight.2.2.trans (by change 48*(1+D*Real.log (16*z)) ≤ 48*D*Q; nlinarith)
  have hHbound : (c.H : ℝ) ≤ 4*Q :=
    tree_height_bound D Q hDpos hQ hlogD hlogQ c.H (by simpa using hT)
  have hK : (c.K : ℝ) ≤ 5*Q := by
    have he : 4*q.L*q.R/(q.ε/(2*(c.H : ℝ))) = 8*z*(c.H : ℝ) := by
      dsimp [z]
      field_simp
      ring
    change (⌈Real.log (4*q.L*q.R/(q.ε/(2*(c.H : ℝ))))/Real.log 2⌉₊ : ℝ) ≤ 5*Q
    rw [he]
    exact bisection_count_bound z Q hz hQ hlogz hlogQ c.H hH hHbound
  have hC : (selectionBlocks c.K c.H : ℝ) ≤ 240*D*Q^2 := by
    have hn : selectionBlocks c.K c.H ≤ 2^c.H*c.K :=
      Nat.mul_le_mul_right c.K (Nat.sub_le _ _)
    have hm := mul_le_mul hT hK (Nat.cast_nonneg c.K) (by positivity : 0 ≤ 48*D*Q)
    have hn' : (selectionBlocks c.K c.H : ℝ) ≤ ((2^c.H : ℕ) : ℝ)*(c.K : ℝ) := by exact_mod_cast hn
    nlinarith
  have hm : (c.m : ℝ) ≤ 32*Q := mom_count_bound D Q hD hQ hlogD hlogQ (selectionBlocks c.K c.H) hC
  have hb : (c.b : ℝ) ≤ 1+4096*V/D := by
    have he : 4096*q.σ^2*q.R^2/((q.d : ℝ)*q.ε^2) = 4096*V/D := by dsimp [V, D]; ring
    change ((max 1 ⌈4096*q.σ^2*q.R^2/((q.d : ℝ)*q.ε^2)⌉₊ : ℕ) : ℝ) ≤ _
    rw [he]
    have hh := max_ceil_upper (4096*V/D) (by positivity)
    linarith
  have ha : c.a = q.ε/(24*q.R*(c.H : ℝ)) := by
    change (q.ε/(2*(c.H : ℝ)))/(12*q.R) = _
    ring
  have he : 8*q.σ^2/(D*c.a^2) = 4608*V*(c.H : ℝ)^2/D := by
    rw [ha]
    dsimp [V]
    field_simp
    ring
  have hn : (c.n : ℝ) ≤ 1+73728*V*Q^2/D := by
    have hc := max_ceil_upper (8*q.σ^2/(D*c.a^2)) (by positivity)
    change (c.n : ℝ) ≤ 8*q.σ^2/(D*c.a^2)+1 at hc
    rw [he] at hc
    have hsq : (c.H : ℝ)^2 ≤ 16*Q^2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4608*V/D)
    simp only [div_eq_mul_inv] at hc hmul ⊢
    nlinarith
  have htotal := aggregate_cost_bound D V Q hDpos hV (by linarith) (2^c.H) c.b
    (selectionBlocks c.K c.H) c.n c.m hT hb hC hn hm
  simpa only [workCost, generatorCost, selectionCost, Nat.mul_assoc] using htotal

lemma tuned_work_le_public_budget (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hR : 0 < q.R)
    (hε : 0 < q.ε) (hsmall : q.ε < q.L*q.R) :
    workCost (tunedConfig q) ≤
      ⌈2^32*((q.d : ℝ)+q.σ^2*q.R^2/q.ε^2)*(1+Real.log (16*(q.d : ℝ)*(1+q.L*q.R/q.ε)))^5⌉₊ := by
  have hD : (1 : ℝ) ≤ q.d := by exact_mod_cast hd
  have hz : 1 ≤ q.L*q.R/q.ε := (le_div_iff₀ hε).mpr (by linarith)
  have hQ := (scale_estimates (q.d : ℝ) (q.L*q.R/q.ε) hD hz).1
  have hnon : 0 ≤ ((q.d : ℝ)+q.σ^2*q.R^2/q.ε^2)*
      (1+Real.log (16*(q.d : ℝ)*(1+q.L*q.R/q.ε)))^5 := by
    apply mul_nonneg (by positivity)
    apply pow_nonneg
    linarith
  have hconst := mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ)^30 ≤ 2^32) hnon
  have hcost := tuned_work_cost_bound q hd hL hR hε hsmall
  have hcost' : (workCost (tunedConfig q) : ℝ) ≤
      2^32*((q.d : ℝ)+q.σ^2*q.R^2/q.ε^2)*(1+Real.log (16*(q.d : ℝ)*(1+q.L*q.R/q.ε)))^5 := by
    nlinarith
  exact_mod_cast hcost'.trans (Nat.le_ceil _)

end LongTails.Proofs.CovarianceSoftCutBudget
