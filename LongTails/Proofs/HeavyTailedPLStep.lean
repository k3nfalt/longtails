import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace

namespace OracleTemplate.HeavyTailedPL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gradient_sq_le {f : E → ℝ} {L m : ℝ} (hL : 0 < L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hm : ∀ x, m ≤ f x) (x : E) : ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - m) := by
  have hd := Gradient.descent hL hg hlip x
  have hl := hm (x - (1 / L) • gradient f x)
  have h2 : ‖gradient f x‖ ^ 2 / (2 * L) ≤ f x - m := by linarith
  rw [div_le_iff₀ (by positivity)] at h2
  linarith

lemma noisy_step {f : E → ℝ} {L η : ℝ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hL0 : 0 ≤ L) (hη : 0 ≤ η) (hLη : L * η ≤ 1 / 2) (x v : E) :
    f (x - η • v) ≤ f x - η / 2 * ‖gradient f x‖ ^ 2 -
      η * ⟪gradient f x, v - gradient f x⟫ + L * η ^ 2 * ‖v - gradient f x‖ ^ 2 := by
  have hu := Gradient.smooth_upper_bound hg hlip x (x - η • v)
  have he : x - η • v - x = -(η • v) := by abel
  rw [he, inner_neg_right, norm_neg, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hη] at hu
  set u := gradient f x
  set e := v - u
  have hv : v = u + e := by simp [e]
  have hin : ⟪u, v⟫ = ‖u‖ ^ 2 + ⟪u, e⟫ := by
    rw [hv, inner_add_right, real_inner_self_eq_norm_sq]
  have hsq : ‖v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖e‖ ^ 2 := by
    rw [hv]
    have h1 := norm_add_le u e
    nlinarith [norm_nonneg u, norm_nonneg e, norm_nonneg (u + e), sq_nonneg (‖u‖ - ‖e‖)]
  have hq : L / 2 * (η * ‖v‖) ^ 2 ≤ L * η ^ 2 * ‖u‖ ^ 2 + L * η ^ 2 * ‖e‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq (show 0 ≤ L / 2 * η ^ 2 by positivity)
    nlinarith
  have hLη2 : L * η ^ 2 * ‖u‖ ^ 2 ≤ η / 2 * ‖u‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hLη (show 0 ≤ η * ‖u‖ ^ 2 by positivity)
    nlinarith
  nlinarith

lemma weighted_step {r r' G2 ip ipc cc Y μ L n : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L) (hn : 3 ≤ n)
    (hstep : r' ≤ r - 4 / (μ * n) / 2 * G2 - 4 / (μ * n) * (ip + ipc) +
      L * (4 / (μ * n)) ^ 2 * Y)
    (hpl : 2 * μ * r ≤ G2) (hipc : -ipc ≤ G2 / 8 + 2 * cc) (hY : 0 ≤ Y) :
    n * (n - 1) * r' ≤ (n - 1) * (n - 2) * r +
      (-(4 * (n - 1) / μ) * ip - 4 * (n - 1) / μ / 8 * G2) +
      8 * (n - 1) * cc / μ + 16 * L / μ ^ 2 * Y := by
  have hn0 : 0 < n := by linarith
  have hw : 0 ≤ n * (n - 1) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hstep hw
  have e1 : n * (n - 1) * (4 / (μ * n) / 2 * G2) = 2 * (n - 1) / μ * G2 := by
    field_simp; ring
  have e2 : n * (n - 1) * (4 / (μ * n) * (ip + ipc)) = 4 * (n - 1) / μ * (ip + ipc) := by
    field_simp
  have e3 : n * (n - 1) * (L * (4 / (μ * n)) ^ 2 * Y) = 16 * L * (n - 1) / (μ ^ 2 * n) * Y := by
    field_simp; ring
  have hY' : 16 * L * (n - 1) / (μ ^ 2 * n) * Y ≤ 16 * L / μ ^ 2 * Y := by
    apply mul_le_mul_of_nonneg_right _ hY
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hL (sq_nonneg μ)]
  have hpl' : 2 * (n - 1) / μ * (2 * μ * r) ≤ 2 * (n - 1) / μ * G2 :=
    mul_le_mul_of_nonneg_left hpl (by have : 0 ≤ n - 1 := by linarith
                                      positivity)
  have e4 : 2 * (n - 1) / μ * (2 * μ * r) = 4 * (n - 1) * r := by field_simp; ring
  have hc : 4 * (n - 1) / μ * (-ipc) ≤ 4 * (n - 1) / μ * (G2 / 8 + 2 * cc) :=
    mul_le_mul_of_nonneg_left hipc (by have : 0 ≤ n - 1 := by linarith
                                       positivity)
  have e5 : 4 * (n - 1) / μ * (G2 / 8 + 2 * cc) = 4 * (n - 1) / μ / 8 * G2 + 8 * (n - 1) * cc / μ := by
    ring
  have key : n * (n - 1) * r' ≤ n * (n - 1) * r - 2 * (n - 1) / μ * G2 -
      4 * (n - 1) / μ * (ip + ipc) + 16 * L * (n - 1) / (μ ^ 2 * n) * Y := by
    calc n * (n - 1) * r' ≤ n * (n - 1) * (r - 4 / (μ * n) / 2 * G2 - 4 / (μ * n) * (ip + ipc) +
          L * (4 / (μ * n)) ^ 2 * Y) := hm
      _ = _ := by rw [mul_add, mul_sub, mul_sub, e1, e2, e3]
  have e6 : 4 * (n - 1) / μ * (ip + ipc) = 4 * (n - 1) / μ * ip + 4 * (n - 1) / μ * ipc := by
    ring
  have e7 : n * (n - 1) * r - 4 * (n - 1) * r / 2 = (n - 1) * (n - 2) * r := by ring
  have e8 : 2 * (n - 1) / μ * G2 = 4 * (n - 1) / μ / 8 * G2 + 3 / 2 * ((n - 1) / μ * G2) := by
    ring
  have e9 : 2 * (n - 1) / μ * G2 = 2 * ((n - 1) / μ * G2) := by ring
  have e10 : 4 * (n - 1) / μ / 8 * G2 = (1 / 2) * ((n - 1) / μ * G2) := by ring
  have e11 : 4 * (n - 1) / μ * -ipc = -(4 * (n - 1) / μ * ipc) := by ring
  rw [e9] at hpl'
  linarith

end OracleTemplate.HeavyTailedPL
