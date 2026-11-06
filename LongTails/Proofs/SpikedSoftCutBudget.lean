import LongTails.Proofs.SpikedSoftCutTuning
import LongTails.Proofs.SpikedSoftCutMethodExecution

namespace LongTails.Proofs.SpikedSoftCutBudget

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCutMethod
open SpikedSoftCutMethodExecution
open SpikedSoftCutTuning

lemma remainingCost_real_le (c : Config) (B : ℝ) (hB : ∀ k, (epochCost c k : ℝ) ≤ B)
    (remaining k : ℕ) : (remainingCost c k remaining : ℝ) ≤ remaining*B := by
  induction remaining generalizing k with
  | zero => simp [remainingCost]
  | succ remaining ih =>
    simp only [remainingCost, Nat.cast_add, Nat.cast_succ]
    have hh := ih (k+1)
    have hk := hB k
    nlinarith

lemma tuned_remainingCost_bound (q : Params) (hG : 0 < q.G) (hR : 0 < q.R)
    (hε : 0 < q.ε) (hrest : 0 ≤ q.vRest) (hTop : 0 ≤ q.vTop) :
    (remainingCost (tunedConfig q) 0 (tunedConfig q).K : ℝ) ≤
      ((tunedConfig q).K : ℝ) *
        (((tunedConfig q).T : ℝ)*(2+2^31*q.vRest*q.R^2*logScale q/q.ε^2) +
          1+8192*((tunedConfig q).K : ℝ)*q.vTop*q.R^2/q.ε^2) := by
  apply remainingCost_real_le
  intro k
  have hb := tuned_batch_count_bound q hG hR hε hrest
  have hN := tuned_scalar_count_bound q hTop k
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (tunedConfig q).T : (0 : ℝ) ≤ (tunedConfig q).T)
  simp only [epochCost, Nat.cast_add, Nat.cast_mul]
  nlinarith

lemma proxy_dimension_charge (m top rest A : ℝ) (horder : rest ≤ top) (hA : 0 ≤ A) :
    (m+1)*rest*A ≤ (top+m*rest)*A := by
  have hh := mul_le_mul_of_nonneg_right horder hA
  nlinarith

lemma polynomial_cost_bound (K T d Q S a b : ℝ)
    (hK : 0 ≤ K) (hT : 0 ≤ T) (hQ : 1 ≤ Q)
    (hS : 1 ≤ S) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hKb : K ≤ 64*Q) (hTb : T ≤ 8192*d*Q^2)
    (hdS : d ≤ S) (haS : a ≤ S) (hdbS : d*b ≤ S) :
    K*(T*(2+2^31*b*Q)+1+8192*K*a) ≤ 2^51*S*Q^5 := by
  have hQ0 : 0 ≤ Q := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hp1 : Q ≤ Q^5 := by simpa using pow_le_pow_right₀ hQ (show 1 ≤ 5 by omega)
  have hp2 : Q^2 ≤ Q^5 := pow_le_pow_right₀ hQ (by omega)
  have hp3 : Q^3 ≤ Q^5 := pow_le_pow_right₀ hQ (by omega)
  have hp4 : Q^4 ≤ Q^5 := pow_le_pow_right₀ hQ (by omega)
  have hKT : K*T ≤ 524288*d*Q^3 := by
    have hh := mul_le_mul hKb hTb hT (show 0 ≤ 64*Q by positivity)
    nlinarith
  have hfirst : 2*K*T ≤ 1048576*S*Q^5 := by
    have hh := mul_le_mul hdS hp3 (by positivity : 0 ≤ Q^3) hS0
    nlinarith
  have hnoise : 2^31*K*T*b*Q ≤ 2^50*S*Q^5 := by
    have hh := mul_le_mul_of_nonneg_right hKT (show 0 ≤ 2^31*b*Q by positivity)
    have hc := mul_le_mul hdbS hp4 (by positivity : 0 ≤ Q^4) hS0
    nlinarith
  have hthird : K ≤ 64*S*Q^5 := by
    have hh := mul_le_mul hS hp1 hQ0 hS0
    nlinarith
  have hlast : 8192*K^2*a ≤ 33554432*S*Q^5 := by
    have hk2 : K^2 ≤ 4096*Q^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hk2 ha
    have hc := mul_le_mul haS hp2 (by positivity : 0 ≤ Q^2) hS0
    nlinarith
  have hp : 0 ≤ S*Q^5 := by positivity
  nlinarith

lemma tuned_budget_suffices (q : Params) (hG : 0 < q.G) (hR : 0 < q.R)
    (hε : 0 < q.ε) (hrest : 0 ≤ q.vRest) (horder : q.vRest ≤ q.vTop) :
    remainingCost (tunedConfig q) 0 (tunedConfig q).K ≤
      ⌈2^51*((q.m+1 : ℝ)+(q.vTop+q.m*q.vRest)*q.R^2/q.ε^2)*(logScale q)^5⌉₊ := by
  let K : ℝ := (tunedConfig q).K
  let T : ℝ := (tunedConfig q).T
  let Q := logScale q
  let d : ℝ := q.m+1
  let A := q.R^2/q.ε^2
  let a := q.vTop*A
  let b := q.vRest*A
  let S := d+(q.vTop+q.m*q.vRest)*A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have htop : 0 ≤ q.vTop := hrest.trans horder
  have ha : 0 ≤ a := mul_nonneg htop hA
  have hb : 0 ≤ b := mul_nonneg hrest hA
  have hd : 1 ≤ d := by dsimp [d]; linarith [show (0 : ℝ) ≤ q.m from Nat.cast_nonneg q.m]
  have hS : d ≤ S := by
    have hh : 0 ≤ (q.vTop+q.m*q.vRest)*A := by positivity
    dsimp [S]
    linarith
  have haS : a ≤ S := by
    have hh : 0 ≤ (q.m : ℝ)*q.vRest*A := by positivity
    dsimp [a, S]
    nlinarith
  have hbS : d*b ≤ S := by
    have hh := proxy_dimension_charge (q.m : ℝ) q.vTop q.vRest A horder hA
    dsimp [d, b, S]
    nlinarith
  have hQ : 1 ≤ Q := logScale_ge_one q hG hR hε
  have hKb : K ≤ 64*Q := by
    have hh := (tuned_epoch_count_bounds q hG hR hε).2
    change K ≤ 33*Q at hh
    linarith
  have hTb : T ≤ 8192*d*Q^2 := by
    have hh := (tuned_inner_count_bounds q hG hR hε).2
    change T ≤ 4097*d*Q^2 at hh
    have hp : 0 ≤ d*Q^2 := by positivity
    nlinarith
  have hc := polynomial_cost_bound K T d Q S a b (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hQ (hd.trans hS) ha hb hKb hTb hS haS hbS
  have hr := tuned_remainingCost_bound q hG hR hε hrest htop
  have he : ((tunedConfig q).K : ℝ) *
      (((tunedConfig q).T : ℝ)*(2+2^31*q.vRest*q.R^2*logScale q/q.ε^2)+
        1+8192*((tunedConfig q).K : ℝ)*q.vTop*q.R^2/q.ε^2) =
      K*(T*(2+2^31*b*Q)+1+8192*K*a) := by dsimp [K,T,b,Q,a,A]; ring
  rw [he] at hr
  have hbound := hr.trans hc
  have hout : 2^51*S*Q^5 =
      2^51*((q.m+1 : ℝ)+(q.vTop+q.m*q.vRest)*q.R^2/q.ε^2)*(logScale q)^5 := by
    dsimp [S,d,A,Q]
    ring
  rw [hout] at hbound
  exact_mod_cast hbound.trans (Nat.le_ceil _)

end LongTails.Proofs.SpikedSoftCutBudget
