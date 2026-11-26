import LongTails.Setups.MarkovSmoothNonconvex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace LongTails.Proofs.MarkovNonconvexBurnInBatches

open Setups.MarkovSmoothNonconvex

noncomputable def blocks (p : Params) : ℕ := ⌈8*(p.L*p.Δ/p.ε^2)⌉₊
noncomputable def discard (p : Params) : ℕ := ⌈p.τ*Real.log 16⌉₊
noncomputable def keep (p : Params) : ℕ := ⌈1024*p.τ*(p.σ^2/p.ε^2)⌉₊

lemma ratios (p : Params) (hp : spec.valid p) :
    1 ≤ p.L*p.Δ/p.ε^2 ∧ 1 ≤ p.σ^2/p.ε^2 := by
  have he := hp.2.1
  have hσ := hp.2.2.2.1
  have hT := hp.2.2.2.2.1
  constructor <;> apply (le_div_iff₀ (sq_pos_of_pos he)).2
  · nlinarith [sq_pos_of_pos he]
  · nlinarith [mul_nonneg (show 0 ≤ p.σ-p.ε by linarith) (show 0 ≤ p.σ+p.ε by linarith)]

lemma counts_pos (p : Params) (hp : spec.valid p) : 0 < blocks p ∧ 0 < keep p := by
  obtain ⟨hT,hV⟩ := ratios p hp
  have ht := hp.2.2.1
  constructor <;> apply Nat.ceil_pos.mpr <;> positivity

lemma keep_size (p : Params) (hp : spec.valid p) : 1024*p.τ*p.σ^2 ≤ keep p*p.ε^2 := by
  apply (div_le_iff₀ (sq_pos_of_pos hp.2.1)).mp
  rw [show 1024*p.τ*p.σ^2 / p.ε^2 = 1024*p.τ*(p.σ^2/p.ε^2) by ring]
  exact Nat.le_ceil _

lemma discard_decay (p : Params) (hp : spec.valid p) : 2*Real.exp (-(discard p:ℝ)/p.τ) ≤ 1/8 := by
  have ht : 0 < p.τ := by linarith [hp.2.2.1]
  have e := Nat.le_ceil (p.τ * Real.log 16)
  have a : -(discard p:ℝ)/p.τ ≤ -Real.log 16 := by
    apply (div_le_iff₀ ht).2; unfold discard; linarith
  have h := Real.exp_le_exp.mpr a
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<16)] at h
  linarith

lemma budget_bound (p : Params) (hp : spec.valid p) :
    ((blocks p * (discard p + keep p) : ℕ) : ℝ) ≤ 9261*p.τ*p.L*p.Δ*p.σ^2/p.ε^4 := by
  let T := p.L*p.Δ/p.ε^2
  let V := p.σ^2/p.ε^2
  have ⟨hT,hV⟩ := ratios p hp
  change 1 ≤ T at hT
  change 1 ≤ V at hV
  have ht := hp.2.2.1
  have tv : p.τ ≤ p.τ*V := by nlinarith [mul_nonneg (by linarith : 0 ≤ p.τ) (sub_nonneg.mpr hV)]
  have log16 : Real.log 16 ≤ 3 := by
    rw [show (16:ℝ)=2^4 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hK : (blocks p:ℝ) ≤ 9*T := by
    change (⌈8*T⌉₊:ℝ) ≤ _
    linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ 8*T)]
  have hb : (discard p:ℝ) ≤ 4*p.τ := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ p.τ*Real.log 16 by positivity)
    unfold discard
    linarith [mul_le_mul_of_nonneg_left log16 (show 0 ≤ p.τ by linarith)]
  have hn : (keep p:ℝ) ≤ 1025*(p.τ*V) := by
    change (⌈1024*p.τ*V⌉₊:ℝ) ≤ _
    linarith [Nat.ceil_lt_add_one (by positivity : 0 ≤ 1024*p.τ*V)]
  push_cast
  calc
    _ ≤ (9*T)*(1029*(p.τ*V)) := mul_le_mul hK (by linarith) (by positivity) (by positivity)
    _ = _ := by dsimp [T,V]; ring

end LongTails.Proofs.MarkovNonconvexBurnInBatches
