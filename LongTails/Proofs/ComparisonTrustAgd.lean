import LongTails.Proofs.GuardedAcceleratedGeometry

namespace LongTails.Proofs.ComparisonTrustAgd

open LongTails.Algorithms.GuardedMetricAcceleration LongTails.Proofs.GuardedAcceleratedGeometry
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Run (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  a : ℝ
  μ : ℝ
  L : ℝ
  xs : ℕ → E
  zs : ℕ → E
  Gs : ℕ → E

def Run.ys (R : Run E) (k : ℕ) : E := extrapolate R.a (R.xs k) (R.zs k)

structure Run.Valid (R : Run E) (n : ℕ) : Prop where
  ha : 0 < R.a
  ha₁ : R.a ≤ 1
  hμ : 0 < R.μ
  hL : 0 < R.L
  htune : R.a ^ 2 * R.L = R.μ
  x0 : R.xs 0 = 0
  z0 : R.zs 0 = 0
  step : ∀ k < n, R.xs (k + 1) = gradientStep R.L (R.ys k) (R.Gs k) ∧
    R.zs (k + 1) = centerStep R.a R.μ (R.ys k) (R.zs k) (R.Gs k)

def phiSeq (F : E → ℝ) (R : Run E) (θ : ℝ) : ℕ → ℝ
  | 0 => F 0
  | k + 1 => minimumUpdate R.a R.μ (phiSeq F R θ k + (if k = 0 then 0 else 2 * θ))
      (F (R.ys k) - θ) (R.ys k) (R.zs k) (R.Gs k)

lemma inexact_claim (F : E → ℝ) (R : Run E) {n : ℕ} (hv : R.Valid n) {θ : ℝ} (hθ : 0 ≤ θ)
    (w : E)
    (hS1 : ∀ k < n, F (R.ys k) + ⟪R.Gs k, R.xs k - R.ys k⟫ + R.μ / 2 * ‖R.xs k - R.ys k‖ ^ 2 ≤
      F (R.xs k) + θ)
    (hS2 : ∀ k < n, F (R.ys k) + ⟪R.Gs k, w - R.ys k⟫ + R.μ / 2 * ‖w - R.ys k‖ ^ 2 ≤ F w + θ)
    (hD : ∀ k < n, F (R.xs (k + 1)) ≤ F (R.ys k) - ‖R.Gs k‖ ^ 2 / (2 * R.L) + θ) :
    ∀ k ≤ n, F (R.xs k) ≤ phiSeq F R θ k + (if k = 0 then 0 else 2 * θ) ∧
      phiSeq F R θ k + R.μ / 2 * ‖w - R.zs k‖ ^ 2 ≤
        (1 - R.a) ^ k * (F 0 + R.μ / 2 * ‖w‖ ^ 2) + (1 - (1 - R.a) ^ k) * F w +
          2 * θ / R.a := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp [phiSeq, hv.x0], ?_⟩
    simp only [phiSeq, hv.z0, sub_zero, pow_zero, one_mul, sub_self, zero_mul, add_zero]
    have : 0 ≤ 2 * θ / R.a := div_nonneg (by linarith) hv.ha.le
    linarith
  | succ k ih =>
    intro hk
    obtain ⟨h₁, h₂⟩ := ih (by omega)
    have hk' : k < n := by omega
    obtain ⟨hx, hz⟩ := hv.step k hk'
    set A := (if k = 0 then (0 : ℝ) else 2 * θ) with hA
    have hA0 : 0 ≤ A := by rw [hA]; split_ifs <;> linarith
    have hA2 : A ≤ 2 * θ := by rw [hA]; split_ifs <;> linarith
    set y := R.ys k
    set G := R.Gs k
    have hy : y = extrapolate R.a (R.xs k) (R.zs k) := rfl
    constructor
    · have hh := minimum_step (Fnext := F (R.xs (k + 1)) - 2 * θ) (x := R.xs k)
        (Fy := F y - θ) (φ := phiSeq F R θ k + A) (Fx := F (R.xs k))
        (z := R.zs k) (g := G) hv.ha.le hv.ha₁ hv.hμ hv.hL hv.htune h₁
        (by rw [← hy]; linarith [hS1 k hk']) (by linarith [hD k hk'])
      have hne : k + 1 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      have : phiSeq F R θ (k + 1) =
          minimumUpdate R.a R.μ (phiSeq F R θ k + A) (F y - θ) y (R.zs k) G := rfl
      rw [this]
      rw [← hy] at hh
      linarith
    · have hid := estimate_quadratic_identity (a := R.a) (μ := R.μ) (φ := phiSeq F R θ k + A)
        (Fy := F y - θ) hv.hμ.ne' w y (R.zs k) G
      have hrec : phiSeq F R θ (k + 1) + R.μ / 2 * ‖w - R.zs (k + 1)‖ ^ 2 =
          (1 - R.a) * (phiSeq F R θ k + A + R.μ / 2 * ‖w - R.zs k‖ ^ 2) +
            R.a * (F y - θ + ⟪G, w - y⟫ + R.μ / 2 * ‖w - y‖ ^ 2) := by
        rw [hid, hz]
        rfl
      rw [hrec]
      have hw₁ : 0 ≤ 1 - R.a := sub_nonneg.mpr hv.ha₁
      have e1 := mul_le_mul_of_nonneg_left (add_le_add_right h₂ A) hw₁
      have e2 := mul_le_mul_of_nonneg_left
        (show F y - θ + ⟪G, w - y⟫ + R.μ / 2 * ‖w - y‖ ^ 2 ≤ F w by linarith [hS2 k hk'])
        hv.ha.le
      have hθa : (1 - R.a) * (2 * θ / R.a + A) ≤ 2 * θ / R.a := by
        have ha0 : R.a ≠ 0 := hv.ha.ne'
        have : (1 - R.a) * (2 * θ / R.a + 2 * θ) = 2 * θ / R.a - 2 * θ * R.a := by
          field_simp
          ring
        have hmono : (1 - R.a) * (2 * θ / R.a + A) ≤ (1 - R.a) * (2 * θ / R.a + 2 * θ) :=
          mul_le_mul_of_nonneg_left (by linarith) hw₁
        nlinarith [mul_nonneg hθ hv.ha.le]
      have hring : (1 - R.a) * ((1 - R.a) ^ k * (F 0 + R.μ / 2 * ‖w‖ ^ 2) +
          (1 - (1 - R.a) ^ k) * F w + 2 * θ / R.a + A) + R.a * F w =
          (1 - R.a) ^ (k + 1) * (F 0 + R.μ / 2 * ‖w‖ ^ 2) +
            (1 - (1 - R.a) ^ (k + 1)) * F w + (1 - R.a) * (2 * θ / R.a + A) := by ring
      have : (1 - R.a) * (phiSeq F R θ k + A + R.μ / 2 * ‖w - R.zs k‖ ^ 2) ≤
          (1 - R.a) * ((1 - R.a) ^ k * (F 0 + R.μ / 2 * ‖w‖ ^ 2) +
            (1 - (1 - R.a) ^ k) * F w + 2 * θ / R.a + A) := by
        have := e1
        linarith
      linarith

lemma inexact_value (F : E → ℝ) (R : Run E) {n : ℕ} (hv : R.Valid n) {θ : ℝ} (hθ : 0 ≤ θ)
    (w : E)
    (hS1 : ∀ k < n, F (R.ys k) + ⟪R.Gs k, R.xs k - R.ys k⟫ + R.μ / 2 * ‖R.xs k - R.ys k‖ ^ 2 ≤
      F (R.xs k) + θ)
    (hS2 : ∀ k < n, F (R.ys k) + ⟪R.Gs k, w - R.ys k⟫ + R.μ / 2 * ‖w - R.ys k‖ ^ 2 ≤ F w + θ)
    (hD : ∀ k < n, F (R.xs (k + 1)) ≤ F (R.ys k) - ‖R.Gs k‖ ^ 2 / (2 * R.L) + θ) :
    F (R.xs n) - F w ≤ (1 - R.a) ^ n * (F 0 - F w + R.μ / 2 * ‖w‖ ^ 2) + 4 * θ / R.a ∧
      R.μ / 2 * ‖w - R.zs n‖ ^ 2 ≤ (1 - R.a) ^ n * (F 0 - F w + R.μ / 2 * ‖w‖ ^ 2) +
        F w - F (R.xs n) + 4 * θ / R.a := by
  obtain ⟨h₁, h₂⟩ := inexact_claim F R hv hθ w hS1 hS2 hD n le_rfl
  have hA : (if n = 0 then (0 : ℝ) else 2 * θ) ≤ 2 * θ / R.a := by
    split_ifs
    · exact div_nonneg (by linarith) hv.ha.le
    · rw [le_div_iff₀ hv.ha]
      nlinarith [hv.ha₁, hθ]
  have hz : 0 ≤ R.μ / 2 * ‖w - R.zs n‖ ^ 2 := by have := hv.hμ; positivity
  generalize (if n = 0 then (0 : ℝ) else 2 * θ) = A at h₁ hA
  generalize (1 - R.a) ^ n = P at h₂ ⊢
  generalize phiSeq F R θ n = φ at h₁ h₂
  have e1 : P * (F 0 - F w + R.μ / 2 * ‖w‖ ^ 2) = P * (F 0 + R.μ / 2 * ‖w‖ ^ 2) - P * F w := by
    ring
  have e2 : (1 - P) * F w = F w - P * F w := by ring
  have e3 : 4 * θ / R.a = 2 * θ / R.a + 2 * θ / R.a := by ring
  rw [e1, e3]
  rw [e2] at h₂
  constructor
  · linarith
  · linarith

end

end LongTails.Proofs.ComparisonTrustAgd
