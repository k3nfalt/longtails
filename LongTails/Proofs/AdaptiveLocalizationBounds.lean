import Mathlib.Tactic

namespace LongTails.Proofs.AdaptiveLocalizationBounds

lemma transition_radius (a B r G s v : ℝ) (ha : 0 < a) (hB : 0 < B)
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hrB : 2 * r ≤ B)
    (hGa : G ≤ a * B) (hv : 0 ≤ v) (hupper : v ≤ G * (s + r))
    (hleft : 0 ≤ a / 2 * (s ^ 2 - B ^ 2) - v)
    (hright : a / 2 * (s ^ 2 - B ^ 2) - v ≤ a * B ^ 2) :
    B ≤ s ∧ s ≤ 4 * B := by
  have hquad : B ^ 2 ≤ s ^ 2 := by nlinarith
  have hgs := mul_le_mul_of_nonneg_right hGa (show 0 ≤ s + r by positivity)
  have hbr := mul_le_mul_of_nonneg_left hrB (show 0 ≤ a * B by positivity)
  constructor
  · nlinarith
  · by_contra h
    have hb : 4 * B < s := lt_of_not_ge h
    have hp := mul_pos (show 0 < s - 4 * B by linarith)
      (show 0 < a * (s + 2 * B) by positivity)
    nlinarith

lemma exterior_separation (a B r G s v : ℝ) (ha : 0 < a) (hB : 0 < B)
    (hr : 0 ≤ r) (hrB : 2 * r ≤ B)
    (hGa : G ≤ a * B) (hupper : v ≤ G * (s + r)) (hs : 4 * B ≤ s) :
    a * B ^ 2 ≤ a / 2 * (s ^ 2 - B ^ 2) - v := by
  have hgs := mul_le_mul_of_nonneg_right hGa (show 0 ≤ s + r by linarith)
  have hbr := mul_le_mul_of_nonneg_left hrB (show 0 ≤ a * B by positivity)
  have hp := mul_nonneg (show 0 ≤ s - 4 * B by linarith)
    (mul_nonneg ha.le (by linarith : 0 ≤ s + 2 * B))
  nlinarith

lemma degree_le_geometric (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * (n + 1 : ℕ) ≤ (3 / 2 : ℝ) * 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hd : ((n + 1 : ℕ) : ℝ) * (n + 2 : ℕ) ≤
        2 * ((n : ℝ) * (n + 1 : ℕ)) := by
      have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      nlinarith
    push_cast at hd ⊢
    rw [pow_succ]
    push_cast at ih
    linarith

lemma curvature_absorption (S C U V L₀ L₁ a p D δ : ℝ)
    (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hbase : S ≤ (1 - p) * (L₀ / 3 + L₁ / 3 * U) + p * a + 50 * D * a * (p + δ))
    (hwall : (1 + 50 * D) * a ≤ L₁ / 3 * V)
    (hleak : 50 * D * a * δ ≤ 2 * L₀ / 3)
    (hweighted : (1 - p) * U + p * V ≤ 2 * C) : S ≤ L₀ + L₁ * C := by
  have hw := mul_le_mul_of_nonneg_right hwall hp
  have hc := mul_le_mul_of_nonneg_left hweighted (show 0 ≤ L₁ / 3 by positivity)
  have hz := mul_nonneg hL₀ hp
  have hh := mul_nonneg hL₁ hC
  nlinarith only [hbase, hw, hc, hz, hh, hleak]

lemma wall_curvature_coefficient (D a B L₁ s : ℝ) (hD : 1 ≤ D) (ha : 0 ≤ a)
    (hL₁ : 0 ≤ L₁) (hB : 256 * D ≤ L₁ * B) (hs : B ≤ s) :
    (1 + 50 * D) * a ≤ L₁ / 3 * (a * s) := by
  have hb := mul_le_mul_of_nonneg_left hs hL₁
  have hh := mul_le_mul_of_nonneg_right (show 3 * (1 + 50 * D) ≤ L₁ * s by linarith) ha
  nlinarith only [hh]

lemma leakage_coefficient (D a B G L₀ L₁ δ : ℝ)
    (ha : a * B = G + L₀ * B / 1000) (hB : 0 < B) (hG : 0 ≤ G)
    (hL₀ : 0 ≤ L₀) (hδ : 0 ≤ δ) (hwidth : 256 * D ≤ L₁ * B)
    (hdegree : D * δ ≤ 3 / 2) (hpeak : G * δ * L₁ ≤ L₀) :
    50 * D * a * δ ≤ 2 * L₀ / 3 := by
  have hg := mul_le_mul_of_nonneg_right hwidth (mul_nonneg hG hδ)
  have hp := mul_le_mul_of_nonneg_right hpeak hB.le
  have hd := mul_le_mul_of_nonneg_right hdegree (mul_nonneg hL₀ hB.le)
  have he := congrArg (fun t : ℝ => 50 * D * δ * t) ha
  have hb := mul_nonneg hL₀ hB.le
  have hout : (50 * D * a * δ) * B ≤ (2 * L₀ / 3) * B := by
    nlinarith only [hg, hp, hd, he, hb]
  exact (mul_le_mul_iff_left₀ hB).mp hout

lemma transition_curvature_term (D a B p δ χ H : ℝ) (ha : 0 < a) (hB : 0 < B)
    (hH : 0 ≤ H) (hχ : 0 ≤ χ) (hsize : H ≤ 5 * a * B)
    (hcurvature : χ ≤ 2 * D * (p + δ) / (a * B ^ 2)) :
    χ * H ^ 2 ≤ 50 * D * a * (p + δ) := by
  have hs : H ^ 2 ≤ (5 * a * B) ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hs hχ
  have h2 := mul_le_mul_of_nonneg_right hcurvature (sq_nonneg (5 * a * B))
  have he : 2 * D * (p + δ) / (a * B ^ 2) * (5 * a * B) ^ 2 =
      50 * D * a * (p + δ) := by field_simp; ring
  rw [he] at h2
  exact h1.trans h2

end LongTails.Proofs.AdaptiveLocalizationBounds
