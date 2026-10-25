import LongTails.Algorithms.GradientOnlyGuarded
import LongTails.Proofs.GuardedAcceleratedGeometry
import LongTails.Proofs.GdConvex

namespace LongTails.Proofs.GradientOnlyAgd

open scoped RealInnerProductSpace
open LongTails.Algorithms.GradientOnlyGuarded LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Proofs.GuardedAcceleratedGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def regValue (f : E → ℝ) (α : ℝ) (c x : E) : ℝ := f x + α * ‖x - c‖ ^ 2

def supports (f : E → ℝ) (t : Tuning) (c u y G : E) : Prop :=
  regValue f t.α c y + ⟪G, u - y⟫ + t.μ / 2 * ‖u - y‖ ^ 2 ≤ regValue f t.α c u

lemma reg_descent [CompleteSpace E] {f : E → ℝ} {g : E → E} {L₁ α L : ℝ} (_hα : 0 ≤ α) (hL : 0 < L)
    (hLL : L₁ + 2 * α ≤ L)
    (hg : ∀ x, HasGradientAt f (g x) x) (hlip : ∀ x y, ‖g x - g y‖ ≤ L₁ * ‖x - y‖) (c y : E) :
    regValue f α c (gradientStep L y (regGrad α c y (g y))) ≤
      regValue f α c y - ‖regGrad α c y (g y)‖ ^ 2 / (2 * L) := by
  set G := regGrad α c y (g y)
  set d := gradientStep L y G - y
  have hd : d = -(L⁻¹ • G) := by simp only [d, gradientStep]; abel
  have hs := OracleTemplate.Gradient.smooth_upper_bound hg hlip y (gradientStep L y G)
  have hq : ‖gradientStep L y G - c‖ ^ 2 = ‖y - c‖ ^ 2 + 2 * ⟪y - c, d⟫ + ‖d‖ ^ 2 := by
    have : gradientStep L y G - c = (y - c) + d := by simp only [d]; abel
    rw [this, norm_add_sq_real]
  have hGd : ⟪G, d⟫ = ⟪g y, d⟫ + 2 * α * ⟪y - c, d⟫ := by
    simp only [G, regGrad, inner_add_left, real_inner_smul_left]
  have hdG : ⟪G, d⟫ = -(L⁻¹ * ‖G‖ ^ 2) := by
    rw [hd, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hdn : ‖d‖ ^ 2 = L⁻¹ ^ 2 * ‖G‖ ^ 2 := by
    rw [hd, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), mul_pow]
  unfold regValue
  rw [hq]
  have hL' : L ≠ 0 := hL.ne'
  have hkey : -(L⁻¹ * ‖G‖ ^ 2) + (L₁ / 2 + α) * (L⁻¹ ^ 2 * ‖G‖ ^ 2) ≤ -(‖G‖ ^ 2 / (2 * L)) := by
    have hG : 0 ≤ ‖G‖ ^ 2 := sq_nonneg _
    have h1 : (L₁ / 2 + α) * (L⁻¹ ^ 2 * ‖G‖ ^ 2) ≤ (L / 2) * (L⁻¹ ^ 2 * ‖G‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (L / 2) * (L⁻¹ ^ 2 * ‖G‖ ^ 2) = ‖G‖ ^ 2 / (2 * L) := by field_simp
    have h3 : L⁻¹ * ‖G‖ ^ 2 = 2 * (‖G‖ ^ 2 / (2 * L)) := by field_simp
    linarith
  have hlin : f (gradientStep L y G) ≤ f y + ⟪g y, d⟫ + L₁ / 2 * ‖d‖ ^ 2 := by simpa [d] using hs
  nlinarith [hlin, hGd, hdG, hdn, hkey]

lemma agd_succ (t : Tuning) (g : E → E) (c : E) (k : ℕ) (hk : k < t.N) :
    xs t g c (k + 1) = gradientStep t.L (ys t g c k) (regGrad t.α c (ys t g c k) (g (ys t g c k))) ∧
    zs t g c (k + 1) = centerStep t.a t.μ (ys t g c k) (zs t g c k)
      (regGrad t.α c (ys t g c k) (g (ys t g c k))) := by
  have h : agd t g c (k + 1) = advance t g c (agd t g c k) := by
    simp only [agd, min_eq_left (show k + 1 ≤ t.N by omega), min_eq_left (show k ≤ t.N by omega),
      Function.iterate_succ_apply']
  constructor <;> simp only [xs, zs, ys, h, advance]

lemma agd_zero (t : Tuning) (g : E → E) (c : E) : xs t g c 0 = c ∧ zs t g c 0 = c := by
  simp [xs, zs, agd]

noncomputable def phi (f : E → ℝ) (t : Tuning) (g : E → E) (c : E) : ℕ → ℝ
  | 0 => regValue f t.α c c
  | k + 1 => minimumUpdate t.a t.μ (phi f t g c k) (regValue f t.α c (ys t g c k))
      (ys t g c k) (zs t g c k) (regGrad t.α c (ys t g c k) (g (ys t g c k)))

lemma prop_one [CompleteSpace E] {f : E → ℝ} {g : E → E} {L₁ : ℝ} (t : Tuning)
    (hg : ∀ x, HasGradientAt f (g x) x) (hlip : ∀ x y, ‖g x - g y‖ ≤ L₁ * ‖x - y‖)
    (hα : 0 ≤ t.α) (hL : 0 < t.L) (hLL : L₁ + 2 * t.α ≤ t.L) (hμ : 0 < t.μ)
    (ha : 0 ≤ t.a) (ha₁ : t.a ≤ 1) (htune : t.a ^ 2 * t.L = t.μ)
    (c w : E) (n : ℕ) (hn : n ≤ t.N)
    (hacc : ∀ k < n, supports f t c (xs t g c k) (ys t g c k)
      (regGrad t.α c (ys t g c k) (g (ys t g c k))))
    (hcmp : ∀ k < n, supports f t c w (ys t g c k)
      (regGrad t.α c (ys t g c k) (g (ys t g c k)))) :
    regValue f t.α c (xs t g c n) - regValue f t.α c w ≤
      (1 - t.a) ^ n * (regValue f t.α c c - regValue f t.α c w + t.μ / 2 * ‖w - c‖ ^ 2) := by
  have claim : ∀ k ≤ n, regValue f t.α c (xs t g c k) ≤ phi f t g c k ∧
      phi f t g c k + t.μ / 2 * ‖w - zs t g c k‖ ^ 2 ≤
        (1 - t.a) ^ k * (regValue f t.α c c + t.μ / 2 * ‖w - c‖ ^ 2) +
          (1 - (1 - t.a) ^ k) * regValue f t.α c w := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [phi, xs, zs, agd]
    | succ k ih =>
      intro hk
      obtain ⟨h₁, h₂⟩ := ih (by omega)
      have hk' : k < n := by omega
      set y := ys t g c k
      set G := regGrad t.α c y (g y)
      obtain ⟨hx, hz⟩ := agd_succ t g c k (by omega)
      have hsup := hacc k hk'
      have hcm := hcmp k hk'
      unfold supports at hsup hcm
      constructor
      · rw [hx]
        have hdesc := reg_descent hα hL hLL hg hlip c y
        have hy : y = extrapolate t.a (xs t g c k) (zs t g c k) := rfl
        have hh := minimum_step (Fnext := regValue f t.α c (gradientStep t.L y G)) (x := xs t g c k)
          (Fy := regValue f t.α c y) (φ := phi f t g c k) (Fx := regValue f t.α c (xs t g c k))
          (z := zs t g c k) (g := G) ha ha₁ hμ hL htune h₁
          (by rw [← hy]; linarith [hsup]) (by simpa [G] using hdesc)
        simpa [phi, y, G, hy] using hh
      · rw [hz]
        have hid := estimate_quadratic_identity (a := t.a) (μ := t.μ) (φ := phi f t g c k)
          (Fy := regValue f t.α c y) hμ.ne' w y (zs t g c k) G
        have hrec : phi f t g c (k + 1) + t.μ / 2 * ‖w - centerStep t.a t.μ y (zs t g c k) G‖ ^ 2 =
            (1 - t.a) * (phi f t g c k + t.μ / 2 * ‖w - zs t g c k‖ ^ 2) +
              t.a * (regValue f t.α c y + ⟪G, w - y⟫ + t.μ / 2 * ‖w - y‖ ^ 2) := by
          rw [hid]
          simp [phi, minimumUpdate, y, G]
        rw [hrec]
        have hw₁ : 0 ≤ 1 - t.a := sub_nonneg.mpr ha₁
        have e1 := mul_le_mul_of_nonneg_left h₂ hw₁
        have e2 := mul_le_mul_of_nonneg_left hcm ha
        have hring : (1 - t.a) * ((1 - t.a) ^ k * (regValue f t.α c c + t.μ / 2 * ‖w - c‖ ^ 2) +
            (1 - (1 - t.a) ^ k) * regValue f t.α c w) + t.a * regValue f t.α c w =
            (1 - t.a) ^ (k + 1) * (regValue f t.α c c + t.μ / 2 * ‖w - c‖ ^ 2) +
              (1 - (1 - t.a) ^ (k + 1)) * regValue f t.α c w := by ring
        linarith [e1, e2, hring]
  obtain ⟨h₁, h₂⟩ := claim n le_rfl
  have hq : 0 ≤ t.μ / 2 * ‖w - zs t g c n‖ ^ 2 := by positivity
  nlinarith [h₁, h₂, hq]

end LongTails.Proofs.GradientOnlyAgd
