import LongTails.Proofs.MultirateCalendar

namespace LongTails.Proofs.MultirateBudget

open DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Algorithms
open MultirateSchedule MultirateService MultirateBatchAllocation MultirateBatches MultirateCalendar

variable {p : Params}

noncomputable def ratio (p : Params) : ℝ := p.Δ / δ p ^ 2
noncomputable def rounds (p : Params) : ℕ := 1 + ⌈2 * ratio p * (∑ i, p.L i) / p.n⌉₊
noncomputable def varianceTime (p : Params) : ℝ := (∑ i, p.σ i ^ 2 * p.h i) / (p.n * δ p) ^ 2
noncomputable def curvatureTime (p : Params) : ℝ := (∑ i, p.L i * p.h i) / p.n
noncomputable def mixedTime (p : Params) : ℝ :=
  (∑ i, p.σ i * √(p.L i * p.h i)) ^ 2 / ((p.n : ℝ)^3 * δ p ^ 2)

lemma noise_sum : ∑ i, noise p i ^ 2 = varianceTime p := by
  simp only [noise,div_pow,mul_pow,Real.sq_sqrt (NNReal.coe_nonneg _),← Finset.sum_div,varianceTime]

lemma product_sum_sq (hL : ∀ i, 0 ≤ p.L i) :
    (∑ i, noise p i * weight p i) ^ 2 = mixedTime p := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have he (i) : noise p i * weight p i = p.σ i * √(p.L i * p.h i) / (p.n * δ p * √(p.n : ℝ)) := by
    rw [noise,weight,Real.sqrt_div (hL i),Real.sqrt_mul (hL i)]
    ring
  simp only [he, ← Finset.sum_div,div_pow,mul_pow,Real.sq_sqrt hn.le,mixedTime]
  ring

lemma startup (hh : ∀ i, 0 < p.h i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) :
    ↑(Finset.univ.sup (service p)) ≤ (Finset.univ.sup p.h : Time) + 2*varianceTime p + (transmission p : ℝ) := by
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (service p)
  rw [hj]
  have ha := noise_nonneg hσ hε
  have hb (i) : 0 ≤ weight p i := Real.sqrt_nonneg _
  have hi := count_upper (fun i => (show (0 : ℝ) < p.h i from hh i)) ha hb j
  have hd := duration_le ha hb j
  rw [noise_sum] at hd
  have hmax : (p.h j : ℝ) ≤ ↑(Finset.univ.sup p.h) := by exact_mod_cast Finset.le_sup (f := p.h) (Finset.mem_univ j)
  change (batch p j : ℝ) * p.h j ≤ _ at hi
  change (batch p j : ℝ) * p.h j + (transmission p : ℝ) ≤ _
  linarith

lemma weighted_batch (hh : ∀ i, 0 < p.h i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε)
    (hL : ∀ i, 0 ≤ p.L i) :
    (∑ i, p.L i / p.n * ((batch p i : ℝ) * p.h i)) ≤ curvatureTime p + 2*mixedTime p := by
  have ha := noise_nonneg hσ hε
  have hb (i) : 0 ≤ weight p i := Real.sqrt_nonneg _
  have hw (i) : weight p i ^ 2 = p.L i / p.n := Real.sq_sqrt (div_nonneg (hL i) (by positivity))
  have he (i) := mul_le_mul_of_nonneg_left
    (count_upper (fun j => (show (0 : ℝ) < p.h j from hh j)) ha hb i) (sq_nonneg (weight p i))
  calc
    _ ≤ ∑ i, (p.L i * p.h i / p.n + 2 * (∑ j, noise p j * weight p j) * (noise p i * weight p i)) := by
      apply Finset.sum_le_sum
      intro i _
      have ht := weighted_duration_le ha hb i
      have hb' := he i
      rw [hw] at ht hb'
      change p.L i / p.n * ((batch p i : ℝ) * p.h i) ≤ _ at hb'
      rw [mul_add] at hb'
      convert hb'.trans (add_le_add_right ht _) using 1
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,← product_sum_sq hL]
      unfold curvatureTime
      ring

lemma tick_budget (hh : ∀ i, 0 < p.h i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε)
    (hL : ∀ i, 0 ≤ p.L i) (hpos : 0 < smoothness p) :
    smoothness p * (tick p : ℝ) ≤ curvatureTime p + 2*mixedTime p + smoothness p * (transmission p : ℝ) := by
  have hx := (eq_div_iff (sum_L_pos hpos).ne').mp (tick_eq hL)
  have hr : (∑ i, p.L i * (service p i : ℝ)) / p.n =
      (∑ i, p.L i / p.n * ((batch p i : ℝ) * p.h i)) + smoothness p * transmission p := by
    unfold smoothness
    simp only [service,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast,mul_add,Finset.sum_add_distrib,
      ← Finset.sum_mul,add_div]
    rw [Finset.sum_div]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · ring
  have ht : smoothness p * tick p = (∑ i, p.L i * (service p i : ℝ)) / p.n := by
    rw [← hx,smoothness]; ring
  rw [ht,hr]
  exact add_le_add_left (weighted_batch hh hσ hε hL) _

lemma tick_le_sup (hL : ∀ i, 0 ≤ p.L i) (hpos : 0 < smoothness p) :
    (tick p : ℝ) ≤ (Finset.univ.sup (service p) : Time) := by
  rw [tick_eq hL,div_le_iff₀ (sum_L_pos hpos),mul_comm,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hL i)
  exact_mod_cast Finset.le_sup (f := service p) (Finset.mem_univ i)

lemma iterations_bound : K p ≤ 4 * rounds p := by
  have ht := LeonBatchTuning.iterations_upper (network p)
  convert ht using 1
  unfold rounds ratio
  congr 3
  change 2 * (p.Δ / δ p ^ 2) * (∑ i, p.L i) / p.n = 2 * ((∑ i, p.L i) / p.n) * p.Δ / δ p ^ 2
  ring

lemma bits_bound : width p ≤ 11 + Nat.log2 ((p.n : ℕ) * (p.d+1)) + Nat.log2 (rounds p) := by
  have hr : rounds p ≠ 0 := by unfold rounds; omega
  have h := (Nat.le_log2 (show 4 * rounds p ≠ 0 by omega)).mpr
    ((Nat.log2_self_le (K_pos p).ne').trans (iterations_bound (p := p)))
  have he : K p = 2 ^ (2 * LeonTuning.height (network p)) := by
    change 4 ^ _ = _
    rw [pow_mul]; norm_num
  rw [he,Nat.log2_two_pow,show 4 * rounds p = 2*(2*rounds p) by omega,
    Nat.log2_two_mul (by omega),Nat.log2_two_mul hr] at h
  change 7 + Nat.log2 ((p.n : ℕ) * (p.d+1)) + 2 * (LeonTuning.height (network p) + 1) ≤ _
  omega


lemma sufficient (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) (hΔ : 0 ≤ p.Δ)
    (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) (hpos : 0 < smoothness p) :
    let C : Time := p.l + p.b * (64 + p.d * (11 + Nat.log2 ((p.n : ℕ)*(p.d+1)) + Nat.log2 (rounds p)) : ℕ)
    stamp p (K p) ≤ (32 * ((Finset.univ.sup p.h : Time) + varianceTime p +
      (rounds p : ℝ) * (C : ℝ) + ratio p * (curvatureTime p + mixedTime p)) : ℝ).toNNReal := by
  intro C
  let S := Finset.univ.sup (service p)
  let L := smoothness p
  let q := ratio p
  have hq : 0 ≤ q := div_nonneg hΔ (sq_nonneg _)
  have hl : 0 ≤ L := hpos.le
  have hR : 1 ≤ rounds p := by unfold rounds; omega
  have hR' : (1 : ℝ) ≤ rounds p := by exact_mod_cast hR
  have hf : 2 * q * L = 2 * ratio p * (∑ i, p.L i) / p.n := by dsimp [q,L,smoothness]; ring
  have hRlo : 2 * q * L ≤ (rounds p : ℝ) := by
    unfold rounds
    rw [hf,Nat.cast_add,Nat.cast_one]
    linarith [Nat.le_ceil (2 * ratio p * (∑ i, p.L i) / p.n)]
  have hKup : (K p : ℝ) ≤ 8 + 8 * q * L := by
    have h₁ : (K p : ℝ) ≤ 4 * (rounds p : ℝ) := by exact_mod_cast iterations_bound (p := p)
    have hc := (Nat.ceil_lt_add_one (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hq) hl)).le
    unfold rounds at h₁
    rw [← hf,Nat.cast_add,Nat.cast_one] at h₁
    linarith
  have hC : transmission p ≤ C := by
    unfold transmission C
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ zero_le
    exact_mod_cast (by have := Nat.mul_le_mul_left p.d (bits_bound (p := p)); unfold clockBits; omega :
      p.d * width p + clockBits ≤ 64 + p.d * (11 + Nat.log2 ((p.n : ℕ)*(p.d+1)) + Nat.log2 (rounds p)))
  have hC' : (transmission p : ℝ) ≤ C := hC
  have hS := startup hh hσ hε
  have hA : 0 ≤ varianceTime p := by rw [← noise_sum]; exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hM : 0 ≤ mixedTime p := by unfold mixedTime; positivity
  have hB : 0 ≤ curvatureTime p := div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hL i) (p.h i).coe_nonneg)) (by positivity)
  have h₁ := mul_le_mul_of_nonneg_right hKup (tick p).coe_nonneg
  have h₂ := mul_le_mul_of_nonneg_left (tick_budget hh hσ hε hL hpos) hq
  have h₃ := tick_le_sup hL hpos
  have h₄ := mul_le_mul_of_nonneg_left hC' (mul_nonneg hq hl)
  have h₅ := mul_le_mul_of_nonneg_right hRlo C.coe_nonneg
  have h₆ := mul_le_mul_of_nonneg_right hR' C.coe_nonneg
  change (S : ℝ) + (K p : ℝ) * (tick p : ℝ) ≤ (Real.toNNReal _ : ℝ)
  apply le_trans _ (Real.le_coe_toNNReal _)
  change (S : ℝ) + (K p : ℝ) * (tick p : ℝ) ≤ 32 * ((Finset.univ.sup p.h : Time) + varianceTime p +
    (rounds p : ℝ) * (C : ℝ) + q * (curvatureTime p + mixedTime p))
  change (S : ℝ) ≤ _ at hS
  change (tick p : ℝ) ≤ (S : ℝ) at h₃
  change q * (L * (tick p : ℝ)) ≤ q * (curvatureTime p + 2*mixedTime p + L * (transmission p : ℝ)) at h₂
  nlinarith only [h₁,h₂,h₃,h₄,h₅,h₆,hS,hC',hA,(Finset.univ.sup p.h : Time).coe_nonneg,
    mul_nonneg hq hB,mul_nonneg hq hM,mul_nonneg (le_trans zero_le_one hR') C.coe_nonneg]

end LongTails.Proofs.MultirateBudget
