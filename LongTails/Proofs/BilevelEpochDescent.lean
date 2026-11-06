import LongTails.Proofs.BilevelEpochVector
import LongTails.Proofs.GdConvex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.BilevelEpochDescent

open Finset
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma step_energy_algebra (d g e : E) {β η L σ : ℝ}
    (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hη : 0 < η) (hL : 0 ≤ L)
    (hηL : η * L ≤ 1 / 4) (he : ‖e‖ ≤ σ) :
    8 * η * (β * ⟪g, d⟫ - η * ⟪g, g + e⟫ +
      L * β ^ 2 / 2 * ‖d‖ ^ 2 + L * η ^ 2 / 2 * ‖g + e‖ ^ 2) ≤
      5 * ‖d‖ ^ 2 - 4 * ‖β • d - η • (g + e)‖ ^ 2 -
      2 * η ^ 2 * ‖g‖ ^ 2 + 8 * η * σ * ‖d‖ + 6 * η ^ 2 * σ ^ 2 := by
  have hσ : 0 ≤ σ := (norm_nonneg e).trans he
  have hβsq : β ^ 2 ≤ 1 := by nlinarith
  have hid : ‖β • d - η • (g + e)‖ ^ 2 =
      β ^ 2 * ‖d‖ ^ 2 - 2 * η * β * (⟪g, d⟫ + ⟪e, d⟫) + η ^ 2 * ‖g + e‖ ^ 2 := by
    rw [norm_sub_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right, inner_add_right]
    rw [real_inner_comm d g, real_inner_comm d e]
    ring
  have hge : ‖g + e‖ ^ 2 = ‖g‖ ^ 2 + 2 * ⟪g, e⟫ + ‖e‖ ^ 2 := norm_add_sq_real _ _
  have hcross : ⟪g, g + e⟫ = ‖g‖ ^ 2 + ⟪g, e⟫ := by rw [inner_add_right, real_inner_self_eq_norm_sq]
  have hv : ‖g + e‖ ^ 2 ≤ 2 * ‖g‖ ^ 2 + 2 * ‖e‖ ^ 2 := by
    have hn := norm_add_le g e
    have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖g‖ - ‖e‖)]
  have he2 : ‖e‖ ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) he 2
  have hed : -β * ⟪e, d⟫ ≤ σ * ‖d‖ := by
    have hh := (abs_le.mp (abs_real_inner_le_norm e d)).1
    have hh' := mul_le_mul_of_nonneg_left hh hβ
    have hn : β * ‖e‖ ≤ σ := by nlinarith [norm_nonneg e]
    have hn' := mul_le_mul_of_nonneg_right hn (norm_nonneg d)
    nlinarith only [hh', hn']
  have ha : (1 + L * η) * β ^ 2 ≤ 5 / 4 := by
    have hh := mul_le_mul_of_nonneg_left hβsq (show 0 ≤ 1 + L * η by positivity)
    nlinarith only [hh, hηL]
  have ha' := mul_le_mul_of_nonneg_right ha (sq_nonneg ‖d‖)
  have hv' := mul_le_mul_of_nonneg_left hv (show 0 ≤ η ^ 2 / 4 by positivity)
  have hLv := mul_le_mul_of_nonneg_right hηL (show 0 ≤ η ^ 2 * ‖g + e‖ ^ 2 by positivity)
  have he' := mul_le_mul_of_nonneg_left he2 (show 0 ≤ 3 * η ^ 2 / 2 by positivity)
  have hed' := mul_le_mul_of_nonneg_left hed (show 0 ≤ 2 * η by positivity)
  rw [hcross]
  nlinarith only [hid, hge, ha', hv', hLv, he', hed']

lemma smooth_step_energy [CompleteSpace E] {f : E → ℝ} {g : E → E}
    (hf : ∀ x, HasGradientAt f (g x) x) {L η θ σ : ℝ}
    (hLip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hL : 0 ≤ L) (hη : 0 < η) (hηL : η * L ≤ 1 / 4)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (x d v : E)
    (herr : ‖v - g (x + (1 - θ) • d)‖ ≤ σ) :
    8 * η * (f (x + (1 - θ) • d - η • v) - f x) ≤
      5 * ‖d‖ ^ 2 - 4 * ‖(1 - θ) • d - η • v‖ ^ 2 -
      2 * η ^ 2 * ‖g (x + (1 - θ) • d)‖ ^ 2 +
      8 * η * σ * ‖d‖ + 6 * η ^ 2 * σ ^ 2 := by
  let β := 1 - θ
  let w := x + β • d
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hβ1 : β ≤ 1 := by dsimp [β]; linarith
  have hnLip : ∀ a b, ‖-g a - -g b‖ ≤ L * ‖a - b‖ := by
    intro a b
    simpa only [neg_sub_neg, norm_sub_rev] using hLip b a
  have hneg : ∀ z, HasGradientAt (fun y => -f y) (-g z) z := by
    intro z
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]
    exact (hf z).hasFDerivAt.neg
  have hr := OracleTemplate.Gradient.smooth_upper_bound hneg hnLip w x
  have hminus : x - w = -β • d := by dsimp [w]; module
  rw [hminus] at hr
  simp only [inner_neg_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] at hr
  have hu := OracleTemplate.Gradient.smooth_upper_bound hf hLip w (w - η • v)
  rw [sub_sub_cancel_left] at hu
  simp only [inner_neg_right, real_inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hu
  have hbound : f (w - η • v) - f x ≤ β * ⟪g w, d⟫ - η * ⟪g w, v⟫ +
      L * β ^ 2 / 2 * ‖d‖ ^ 2 + L * η ^ 2 / 2 * ‖v‖ ^ 2 := by
    nlinarith only [hr, hu]
  have henergy := step_energy_algebra d (g w) (v - g w) hβ hβ1 hη hL hηL herr
  have he : g w + (v - g w) = v := by abel
  rw [he] at henergy
  exact (mul_le_mul_of_nonneg_left hbound (show 0 ≤ 8 * η by positivity)).trans henergy

omit [InnerProductSpace ℝ E] in
lemma prefix_movement_sums (D : ℕ → E) (r : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hm : (r : ℝ) * (∑ k ∈ range r, ‖D (k + 1)‖ ^ 2) ≤ B ^ 2) :
    (∑ k ∈ range r, ‖D (k + 1)‖ ^ 2) ≤ B ^ 2 ∧
      (∑ k ∈ range r, ‖D (k + 1)‖) ≤ B := by
  have hs : (∑ k ∈ range r, ‖D (k + 1)‖) ^ 2 ≤
      (r : ℝ) * ∑ k ∈ range r, ‖D (k + 1)‖ ^ 2 := by
    simpa using sum_mul_sq_le_sq_mul_sq (range r) (fun _ => (1 : ℝ)) (fun k => ‖D (k + 1)‖)
  constructor
  · by_cases hr : r = 0
    · simp [hr, sq_nonneg]
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hr
    have hh := mul_le_mul_of_nonneg_right hrR (show 0 ≤ ∑ k ∈ range r, ‖D (k + 1)‖ ^ 2 from sum_nonneg fun _ _ => sq_nonneg _)
    nlinarith only [hh, hm]
  · nlinarith [sum_nonneg (s := range r) (fun k _ => norm_nonneg (D (k + 1)))]

omit [InnerProductSpace ℝ E] in
lemma large_gradient_epoch (F : ℕ → ℝ) (D G : ℕ → E) (r : ℕ) {η σ B : ℝ}
    (hη : 0 < η) (hσ : 0 ≤ σ) (hB : 0 ≤ B) (hD0 : D 0 = 0)
    (hmove : (r : ℝ) * (∑ k ∈ range r, ‖D (k + 1)‖ ^ 2) ≤ B ^ 2)
    (hlarge : B ≤ η * ‖G r‖)
    (hstep : ∀ k, k < r + 1 → 8 * η * (F (k + 1) - F k) ≤
      5 * ‖D k‖ ^ 2 - 4 * ‖D (k + 1)‖ ^ 2 - 2 * η ^ 2 * ‖G k‖ ^ 2 +
        8 * η * σ * ‖D k‖ + 6 * η ^ 2 * σ ^ 2) :
    8 * η * (F (r + 1) - F 0) ≤ -B ^ 2 + 8 * η * σ * B +
      6 * η ^ 2 * σ ^ 2 * (r + 1) := by
  have hs := sum_le_sum (s := range (r + 1)) (fun k hk => hstep k (mem_range.mp hk))
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul] at hs
  have hF : (∑ k ∈ range (r + 1), F (k + 1)) - (∑ k ∈ range (r + 1), F k) = F (r + 1) - F 0 := by
    rw [← sum_sub_distrib, sum_range_sub]
  rw [hF] at hs
  have hsq : (∑ k ∈ range (r + 1), ‖D k‖ ^ 2) = ∑ k ∈ range r, ‖D (k + 1)‖ ^ 2 := by
    rw [sum_range_succ']
    simp [hD0]
  have hnorm : (∑ k ∈ range (r + 1), ‖D k‖) = ∑ k ∈ range r, ‖D (k + 1)‖ := by
    rw [sum_range_succ']
    simp [hD0]
  rw [hsq, hnorm, sum_range_succ] at hs
  have hm := prefix_movement_sums D r hB hmove
  have hG : ‖G r‖ ^ 2 ≤ ∑ k ∈ range (r + 1), ‖G k‖ ^ 2 :=
    single_le_sum (f := fun k => ‖G k‖ ^ 2) (a := r) (fun _ _ => sq_nonneg _) (mem_range.mpr (Nat.lt_succ_self r))
  have hG' := mul_le_mul_of_nonneg_left hG (show 0 ≤ 2 * η ^ 2 by positivity)
  have hlarge' := pow_le_pow_left₀ hB hlarge 2
  have hnorm' := mul_le_mul_of_nonneg_left hm.2 (show 0 ≤ 8 * η * σ by positivity)
  push_cast at hs ⊢
  nlinarith only [hs, hm.1, hG', hlarge', hnorm', sq_nonneg ‖D (r + 1)‖]

lemma small_gradient_endpoint (z v g : E) {η B σ : ℝ} (hη : 0 ≤ η)
    (hz : ‖z‖ ≤ 2 * B) (hg : η * ‖g‖ ≤ B) (he : ‖v - g‖ ≤ σ) :
    ‖z - η • v‖ ≤ 3 * B + η * σ := by
  have hv : ‖v‖ ≤ ‖g‖ + σ := by
    have hh := norm_add_le g (v - g)
    have hv : g + (v - g) = v := by abel
    rw [hv] at hh
    linarith
  have hh := norm_sub_le z (η • v)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hh
  have hv' := mul_le_mul_of_nonneg_left hv hη
  nlinarith only [hh, hv', hz, hg]

lemma small_exit_algebra {η K m B ρ e σ d S : ℝ}
    (hη : 0 < η) (hK : 0 < K) (hm : 0 ≤ m) (hmK : m ≤ K)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hd : 0 ≤ d)
    (hS : 0 ≤ S) (hexit : B ^ 2 ≤ m * S)
    (hdecrease : 32 * η * K ^ 2 * d ≤ B ^ 2)
    (hnoise : 32 * η * K ^ 2 * e ^ 2 ≤ d)
    (herror : σ + 2 * ρ * B ^ 2 ≤ 3 * e)
    (hend : η * σ ≤ B / 2) (hdrop : ρ * B ^ 3 = d) :
    -(3 / (8 * η * K)) * S + 2 * η * K * m * (σ + 2 * ρ * B ^ 2) ^ 2 +
      ρ * (3 * B + η * σ) ^ 3 / 6 ≤ -d := by
  have hKS : B ^ 2 ≤ K * S := hexit.trans (mul_le_mul_of_nonneg_right hmK hS)
  have hpre : 32 * η * K * d ≤ S := by
    apply (mul_le_mul_iff_right₀ hK).mp
    nlinarith only [hdecrease, hKS]
  have hneg : 12 * d ≤ 3 / (8 * η * K) * S := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 8 * η * K)).mpr
    nlinarith only [hpre]
  have herrsq : (σ + 2 * ρ * B ^ 2) ^ 2 ≤ 9 * e ^ 2 := by
    have hh := pow_le_pow_left₀ (show 0 ≤ σ + 2 * ρ * B ^ 2 by positivity) herror 2
    nlinarith only [hh]
  have hn1 := mul_le_mul_of_nonneg_left herrsq (show 0 ≤ 2 * η * K * m by positivity)
  have hn2 := mul_le_mul_of_nonneg_left hmK (show 0 ≤ 18 * η * K * e ^ 2 by positivity)
  have hn : 2 * η * K * m * (σ + 2 * ρ * B ^ 2) ^ 2 ≤ d := by
    nlinarith only [hn1, hn2, hnoise, hd]
  have hr : (3 * B + η * σ) ^ 3 ≤ (7 * B / 2) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hr' := mul_le_mul_of_nonneg_left hr hρ
  have hrem : ρ * (3 * B + η * σ) ^ 3 / 6 ≤ 8 * d := by
    nlinarith only [hr', hdrop, hd]
  nlinarith only [hneg, hn, hrem, hd]

end LongTails.Proofs.BilevelEpochDescent
