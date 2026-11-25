import LongTails.Proofs.AdaptiveGeneralizedSmoothLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.RhoSmoothHardLocalization

open AdaptivePolynomialLocalization AdaptiveGeneralizedSmoothLocalization

lemma young_split (L₀ L₁ ρ G K p b : ℝ) (hL₀ : 0 < L₀) (hρ : 1 ≤ ρ) (hG : 0 < G)
    (hGL : G ^ ρ * L₁ = L₀) (hK : 0 ≤ K) (hp : 0 ≤ p) (hb : 16 * K * G ≤ L₀ * b) :
    K * p ≤ L₀ / 4 + L₁ / 4 * (p * b) ^ ρ := by
  by_cases h : K * p ≤ L₀ / 4
  · have : 0 ≤ L₁ / 4 * (p * b) ^ ρ := by
      have hL₁ : 0 ≤ L₁ := by
        have hGρ : 0 < G ^ ρ := Real.rpow_pos_of_pos hG _
        by_contra hneg
        push Not at hneg
        nlinarith
      have hb0 : 0 ≤ b := by
        have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hK) hG.le
        by_contra hneg
        push Not at hneg
        nlinarith
      positivity
    linarith
  · push Not at h
    have hKp : 0 < K * p := by linarith
    have hpb : 4 * G ≤ p * b := by
      have h1 : 16 * K * G * p ≤ L₀ * b * p := mul_le_mul_of_nonneg_right hb hp
      have h2 : L₀ / 4 * (16 * G) < K * p * (16 * G) := mul_lt_mul_of_pos_right h (by positivity)
      have h3 : L₀ * (4 * G) < L₀ * (p * b) := by nlinarith
      exact (mul_lt_mul_iff_of_pos_left hL₀).mp h3 |>.le
    have hx : 1 ≤ p * b / G := by
      rw [le_div_iff₀ hG]; linarith
    have hxρ : p * b / G ≤ (p * b / G) ^ ρ := by
      have := Real.rpow_le_rpow_of_exponent_le hx hρ
      rwa [Real.rpow_one] at this
    have hpow : (p * b) ^ ρ = G ^ ρ * (p * b / G) ^ ρ := by
      rw [← Real.mul_rpow hG.le (by positivity)]
      congr 1
      field_simp
    have hmain : L₁ / 4 * (p * b) ^ ρ = L₀ / 4 * (p * b / G) ^ ρ := by
      rw [hpow, ← hGL]; ring
    have hlow : 4 * (K * p) ≤ L₀ / 4 * (p * b / G) := by
      have h1 : 16 * K * G * p ≤ L₀ * b * p := mul_le_mul_of_nonneg_right hb hp
      have e : L₀ / 4 * (p * b / G) = L₀ * b * p / (4 * G) := by field_simp
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith
    have hL₀x := mul_le_mul_of_nonneg_left hxρ (show 0 ≤ L₀ / 4 by positivity)
    rw [hmain]
    nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_curvature (s : Seed (E := E)) (n : ℕ) (hn : 2 ≤ n) (a B : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hrB : 2 * s.r ≤ B) (L₀ L₁ ρ G : ℝ) (hL₀ : 0 < L₀)
    (hL₁ : 0 < L₁) (hρ : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hG : 0 < G) (hGL : G ^ ρ * L₁ = L₀)
    (hcurv : ∀ x, ‖fderiv ℝ s.g x‖ ≤ (L₀ + L₁ * ‖s.g x‖ ^ ρ) / 64)
    (hwidth : 1632 * ((n : ℝ) * (n + 1 : ℕ)) * G ≤ L₀ * B)
    (htune : a * B = s.G + L₀ * B / 1000)
    (hleak : 50 * ((n : ℝ) * (n + 1 : ℕ)) * a * (1 / 2 : ℝ) ^ n ≤ L₀ / 4) (x : E) :
    ‖fderiv ℝ (field s.f s.g n a B (a * B ^ 2)) x‖ ≤
      L₀ + L₁ * ‖field s.f s.g n a B (a * B ^ 2) x‖ ^ ρ := by
  have hW : 0 < a * B ^ 2 := by positivity
  have hp := AdaptivePolynomialHinge.mixing_bounds n ((wall a B x - s.f x) / (a * B ^ 2))
  change 0 ≤ mixing s.f n a B (a * B ^ 2) x ∧ mixing s.f n a B (a * B ^ 2) x ≤ 1 at hp
  have hd := field_derivative_norm_bound s.f s.g n hn a B _ ha.le hW x
    (fderiv ℝ s.g x) (s.gradient x) (s.differentiable x).hasFDerivAt
  set C := ‖field s.f s.g n a B (a * B ^ 2) x‖
  have hCρ : 0 ≤ C ^ ρ := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hl : wall a B x ≤ s.f x
  · obtain ⟨h0, h1⟩ := mixing_interior s.f n a B _ hW x hl
    rw [h0, h1] at hd
    have hfi := field_interior s.f s.g n a B _ hW x hl
    have hC : C = ‖s.g x‖ := by simp only [C, hfi]
    have hc := hcurv x
    rw [hC]
    have : 0 ≤ L₁ * ‖s.g x‖ ^ ρ := mul_nonneg hL₁.le (Real.rpow_nonneg (norm_nonneg _) _)
    nlinarith
  have hrad : B ≤ ‖x‖ := by
    have hnon := s.nonnegative x
    have hwall : 0 ≤ a / 2 * (‖x‖ ^ 2 - B ^ 2) := by change 0 ≤ wall a B x; linarith
    have hsq : B ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith
    nlinarith [norm_nonneg x]
  have hGa : s.G ≤ a * B := by
    have hz := mul_nonneg hL₀.le hB.le
    linarith only [htune, hz]
  set P := mixing s.f n a B (a * B ^ 2) x
  set D := (n : ℝ) * (n + 1 : ℕ)
  have hD : 1 ≤ D := by
    have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
    change 1 ≤ (n : ℝ) * ((n + 1 : ℕ) : ℝ)
    push_cast
    nlinarith
  have ht := transition_term s n hn a B ha hB hrB hGa x
  have hweight := weighted_norm s n a B (a * B ^ 2) ha.le x (hrB.trans hrad)
  rw [norm_smul, Real.norm_of_nonneg ha.le] at hweight
  set U := ‖s.g x‖
  have hU0 : 0 ≤ U := norm_nonneg _
  have hC0 : 0 ≤ C := norm_nonneg _
  have hweight' : (1 - P) * U + P * (a * ‖x‖) ≤ 2 * C := hweight
  have ht' : mixingDerivative s.f n a B (a * B ^ 2) x * ‖a • x - s.g x‖ ^ 2 ≤
      50 * D * a * (P + (1 / 2 : ℝ) ^ n) := ht
  have hU : U ≤ s.G := s.bounded x
  have hUC : U ≤ 4 * C := by
    have h1 : P * U ≤ P * (a * ‖x‖) := by
      apply mul_le_mul_of_nonneg_left _ hp.1
      have := mul_le_mul_of_nonneg_left hrad ha.le
      linarith
    linarith [hweight', h1]
  have hUρ : U ^ ρ ≤ 16 * C ^ ρ := by
    have h1 : U ^ ρ ≤ (4 * C) ^ ρ := Real.rpow_le_rpow hU0 hUC (by linarith)
    rw [Real.mul_rpow (by norm_num) hC0] at h1
    have h2 : (4 : ℝ) ^ ρ ≤ 16 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 4 by norm_num) hρ2
      norm_num at this
      linarith
    nlinarith
  have hfirst : (1 - P) * ‖fderiv ℝ s.g x‖ ≤ L₀ / 4 + L₁ / 4 * C ^ ρ := by
    have h1 : (1 - P) * ‖fderiv ℝ s.g x‖ ≤ ‖fderiv ℝ s.g x‖ := by
      nlinarith [norm_nonneg (fderiv ℝ s.g x), hp.1]
    have h2 := hcurv x
    have h3 : L₁ * U ^ ρ ≤ L₁ * (16 * C ^ ρ) := mul_le_mul_of_nonneg_left hUρ hL₁.le
    have : (L₀ + L₁ * U ^ ρ) / 64 ≤ L₀ / 4 + L₁ / 4 * C ^ ρ := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    linarith
  have hb : 16 * ((1 + 50 * D) * a) * G ≤ L₀ * (a * B / 2) := by
    have hDG : G ≤ D * G := le_mul_of_one_le_left hG.le hD
    have h1 : 16 * (1 + 50 * D) * G ≤ L₀ * B / 2 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 ha.le
    have e1 : 16 * ((1 + 50 * D) * a) * G = a * (16 * (1 + 50 * D) * G) := by ring
    have e2 : L₀ * (a * B / 2) = a * (L₀ * B / 2) := by ring
    rw [e1, e2]
    exact h2
  have hyoung := young_split L₀ L₁ ρ G ((1 + 50 * D) * a) P (a * B / 2) hL₀ hρ hG hGL
    (by positivity) hp.1 hb
  have hPb : P * (a * B / 2) ≤ C := by
    have h1 : P * (a * B) ≤ P * (a * ‖x‖) := by
      apply mul_le_mul_of_nonneg_left _ hp.1
      exact mul_le_mul_of_nonneg_left hrad ha.le
    have h2 : 0 ≤ (1 - P) * U := mul_nonneg (by linarith [hp.2]) hU0
    linarith [hweight', h1, h2]
  have hPbρ : (P * (a * B / 2)) ^ ρ ≤ C ^ ρ :=
    Real.rpow_le_rpow (by have := hp.1; positivity) hPb (by linarith)
  have hsecond : (1 + 50 * D) * a * P ≤ L₀ / 4 + L₁ / 4 * C ^ ρ := by
    have := mul_le_mul_of_nonneg_left hPbρ (show 0 ≤ L₁ / 4 by positivity)
    linarith
  have hleak' : 50 * D * a * (1 / 2 : ℝ) ^ n ≤ L₀ / 4 := hleak
  linarith [hd, ht', hfirst, hsecond, hleak', mul_nonneg hL₁.le hCρ]

end LongTails.Proofs.RhoSmoothHardLocalization
