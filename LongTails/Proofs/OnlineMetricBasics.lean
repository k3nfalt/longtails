import LongTails.Proofs.MetricAcceleratedStep
import LongTails.Proofs.LogBandLearner
import LongTails.Proofs.EpochLoss
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.OnlineMetricAccelerated

variable {d : ℕ}

structure Hyp (f : EuclideanSpace ℝ (Fin d) → ℝ) (w : Fin d → ℝ) (μ fstar : ℝ)
    (xstar : EuclideanSpace ℝ (Fin d)) : Prop where
  w_pos : ∀ i, 0 < w i
  μ_pos : 0 < μ
  μ_le : μ ≤ 1
  grad : ∀ x, HasGradientAt f (gradient f x) x
  smooth : ∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫ + (∑ i, w i * (y i - x i) ^ 2) / 2
  sc : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ * (∑ i, w i * (y i - x i) ^ 2) / 2 ≤ f y
  min : IsMinOn f Set.univ xstar
  fmin : f xstar = fstar

namespace Hyp

variable {f : EuclideanSpace ℝ (Fin d) → ℝ} {w : Fin d → ℝ} {μ fstar : ℝ}
  {xstar : EuclideanSpace ℝ (Fin d)}

lemma conv (H : Hyp f w μ fstar xstar) (x y : EuclideanSpace ℝ (Fin d)) :
    f x + ⟪gradient f x, y - x⟫ ≤ f y := by
  have h := H.sc x y
  have : 0 ≤ μ * (∑ i, w i * (y i - x i) ^ 2) / 2 :=
    div_nonneg (mul_nonneg H.μ_pos.le
      (Finset.sum_nonneg fun i _ => mul_nonneg (H.w_pos i).le (sq_nonneg _))) (by norm_num)
  linarith

lemma ge_fstar (H : Hyp f w μ fstar xstar) (x : EuclideanSpace ℝ (Fin d)) : fstar ≤ f x := by
  rw [← H.fmin]; exact H.min (Set.mem_univ x)

lemma grad_star (H : Hyp f w μ fstar xstar) : gradient f xstar = 0 := by
  have hloc : IsLocalMin f xstar := H.min.isLocalMin Filter.univ_mem
  have hf := (H.grad xstar).hasFDerivAt
  have h0 := hloc.hasFDerivAt_eq_zero hf
  have : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))) (gradient f xstar) =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))) 0 := by
    rw [map_zero]; exact h0
  exact (InnerProductSpace.toDual ℝ _).injective this

lemma growth (H : Hyp f w μ fstar xstar) (x : EuclideanSpace ℝ (Fin d)) :
    μ / 2 * ∑ i, w i * (x i - xstar i) ^ 2 ≤ f x - fstar := by
  have h := H.sc xstar x
  rw [H.grad_star, inner_zero_left, H.fmin] at h
  linarith

lemma dist_le (H : Hyp f w μ fstar xstar) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ i, w i * (x i - xstar i) ^ 2 ≤ 2 / μ * (f x - fstar) := by
  have h := H.growth x
  rw [div_mul_eq_mul_div, le_div_iff₀ H.μ_pos]
  linarith

lemma pair_dist (H : Hyp f w μ fstar xstar) (x u : EuclideanSpace ℝ (Fin d)) {Δ : ℝ}
    (hx : f x - fstar ≤ Δ) (hu : f u - fstar ≤ Δ / 4) :
    ∑ i, w i * (x i - u i) ^ 2 ≤ 9 / 2 / μ * Δ := by
  have h1 := H.dist_le x
  have h2 := H.dist_le u
  have hpt : ∀ i, w i * (x i - u i) ^ 2 ≤
      3 / 2 * (w i * (x i - xstar i) ^ 2) + 3 * (w i * (u i - xstar i) ^ 2) := by
    intro i
    have hw := (H.w_pos i).le
    have : (x i - u i) ^ 2 ≤ 3 / 2 * (x i - xstar i) ^ 2 + 3 * (u i - xstar i) ^ 2 := by
      nlinarith [sq_nonneg ((x i - xstar i) + 2 * (u i - xstar i))]
    nlinarith
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hpt i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hμ := H.μ_pos
  have e1 : 3 / 2 * (2 / μ * (f x - fstar)) ≤ 3 / μ * Δ := by
    rw [show 3 / 2 * (2 / μ * (f x - fstar)) = 3 / μ * (f x - fstar) by ring]
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  have e2 : 3 * (2 / μ * (f u - fstar)) ≤ 3 / 2 / μ * Δ := by
    rw [show 3 * (2 / μ * (f u - fstar)) = 6 / μ * (f u - fstar) by ring,
      show 3 / 2 / μ * Δ = 6 / μ * (Δ / 4) by ring]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have e3 : 3 / μ * Δ + 3 / 2 / μ * Δ = 9 / 2 / μ * Δ := by ring
  nlinarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 3 / 2),
    mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 3)]

end Hyp

lemma band_exp {φ : Fin d → ℝ} (hd : 1 ≤ (d : ℝ))
    (hφ : ∀ i, bandLo d ≤ φ i ∧ φ i ≤ bandHi) (i : Fin d) :
    1 / (4 * d) ≤ Real.exp (φ i) ∧ Real.exp (φ i) ≤ 1 / 2 := by
  obtain ⟨h1, h2⟩ := hφ i
  have h4 : (0 : ℝ) < 4 * d := by positivity
  constructor
  · have := Real.exp_le_exp.mpr h1
    rwa [bandLo, Real.exp_neg, Real.exp_log h4, inv_eq_one_div] at this
  · have := Real.exp_le_exp.mpr h2
    rwa [bandHi, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), inv_eq_one_div] at this

lemma bandLo_le_bandHi (hd : 1 ≤ (d : ℝ)) : bandLo d ≤ bandHi := by
  unfold bandLo bandHi
  have : Real.log 2 ≤ Real.log (4 * d) := Real.log_le_log (by norm_num) (by linarith)
  linarith

lemma bandWidth_pos (hd : 1 ≤ (d : ℝ)) : 0 < bandWidth d := by
  unfold bandWidth
  have h1 : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by linarith)
  have h2 : 0 < Real.log (2 * d) := Real.log_pos (by linarith)
  positivity

lemma bandWidth_sq (hd : 1 ≤ (d : ℝ)) : bandWidth d ^ 2 = d * (bandHi - bandLo d) ^ 2 := by
  unfold bandWidth bandHi bandLo
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  have h : Real.log (4 * d) = Real.log 2 + Real.log (2 * d) := by
    rw [show (4 : ℝ) * d = 2 * (2 * d) by ring, Real.log_mul (by norm_num) (by positivity)]
  rw [h]
  ring

lemma fresh_band (hd : 1 ≤ (d : ℝ)) (i : Fin d) :
    bandLo d ≤ (freshLearner d).φ i ∧ (freshLearner d).φ i ≤ bandHi :=
  ⟨bandLo_le_bandHi hd, le_rfl⟩

noncomputable def comparator (w b : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Real.log (max (1 / w i / (2 * b i)) (1 / (4 * d)))

lemma comparator_band {w b : Fin d → ℝ} (hd : 1 ≤ (d : ℝ)) (hw : ∀ i, 0 < w i)
    (hb : ∀ i, 1 / w i ≤ b i) (i : Fin d) :
    bandLo d ≤ comparator w b i ∧ comparator w b i ≤ bandHi := by
  have h4 : (0 : ℝ) < 4 * d := by positivity
  have hbpos : 0 < b i := lt_of_lt_of_le (by have := hw i; positivity) (hb i)
  have hr : 0 < 1 / w i / (2 * b i) := by have := hw i; positivity
  unfold comparator bandLo bandHi
  constructor
  · rw [← Real.log_inv, inv_eq_one_div]
    exact Real.log_le_log (by positivity) (le_max_right _ _)
  · rw [← Real.log_inv, inv_eq_one_div]
    apply Real.log_le_log (lt_max_of_lt_right (by positivity))
    apply max_le
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hb i]
    · rw [div_le_div_iff₀ h4 (by norm_num)]; linarith

lemma comparator_exp {w b : Fin d → ℝ} (hd : 1 ≤ (d : ℝ)) (hw : ∀ i, 0 < w i)
    (hb : ∀ i, 1 / w i ≤ b i) (i : Fin d) :
    1 / w i / (2 * b i) ≤ Real.exp (comparator w b i) ∧
      Real.exp (comparator w b i) ≤ 1 / w i / (2 * b i) + 1 / (4 * d) := by
  have hbpos : 0 < b i := lt_of_lt_of_le (by have := hw i; positivity) (hb i)
  have hr : 0 < 1 / w i / (2 * b i) := by have := hw i; positivity
  unfold comparator
  rw [Real.exp_log (lt_max_of_lt_left hr)]
  refine ⟨le_max_left _ _, max_le ?_ ?_⟩
  · have : (0 : ℝ) < 1 / (4 * d) := by positivity
    linarith
  · linarith

end OracleTemplate.OnlineMetricAccelerated
