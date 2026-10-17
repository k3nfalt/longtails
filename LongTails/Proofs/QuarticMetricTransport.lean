import LongTails.Proofs.ThirdOrderObjectiveGeometry
import LongTails.Proofs.HessianSnapshotGeometry

namespace LongTails.Proofs.QuarticMetricTransport

open scoped RealInnerProductSpace

lemma scaled_cubic_bound {p n N L β R : ℝ} (hN : 0 ≤ N) (hβ : 0 < β) (hR : 0 < R) (he : β ^ 2 = L * R ^ 2)
    (hm : β * n ^ 2 ≤ N ^ 2) (hp : p ^ 2 ≤ 72 * L * n ^ 4 * N ^ 2) :
    |p| ≤ 9 / R * N ^ 3 := by
  have hs : β ^ 2 * n ^ 4 ≤ N ^ 4 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ β * n ^ 2) hm 2
    nlinarith only [hh]
  have hs' := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ 72 * N ^ 2)
  have hp' := mul_le_mul_of_nonneg_right hp (sq_nonneg R)
  have hc : (R * |p|) ^ 2 ≤ (9 * N ^ 3) ^ 2 := by
    rw [he] at hs'
    nlinarith [sq_abs p]
  have ha : R * |p| ≤ 9 * N ^ 3 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hc
  have hh := (le_div_iff₀ hR).mpr (show |p| * R ≤ 9 * N ^ 3 by nlinarith only [ha])
  convert hh using 1
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma diagonal_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ R : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hR : 0 < R)
    (hΔ : Δ = L * σ ^ 2) (hRΔ : R ^ 2 = Δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x : E) (hgap : ∀ y, f x - f y ≤ Δ) (S : E ≃L[ℝ] E)
    (hS : ∀ v, ‖S v‖ ^ 2 = ⟪fderiv ℝ (gradient f) x v, v⟫ + 8 * L * σ * ‖v‖ ^ 2)
    (v : E) :
    |⟪fderiv ℝ (fderiv ℝ (gradient f)) x v v, v⟫| ≤ 9 / R * ‖S v‖ ^ 3 := by
  have hl := ThirdOrderObjectiveGeometry.hessian_quadratic_lower hf hL hσ hΔ hT x v hgap
  have hp := ThirdOrderObjectiveGeometry.third_diagonal_bound hf hL hσ hΔ hT x v hgap
  have hs := hS v
  have hm : L * σ * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2 := by
    nlinarith [mul_nonneg (mul_pos hL hσ).le (sq_nonneg ‖v‖)]
  have hc : ⟪fderiv ℝ (fderiv ℝ (gradient f)) x v v, v⟫ ^ 2 ≤
      72 * L * ‖v‖ ^ 4 * ‖S v‖ ^ 2 := by
    apply hp.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [mul_nonneg (mul_pos hL hσ).le (sq_nonneg ‖v‖)]
  exact scaled_cubic_bound (norm_nonneg _) (mul_pos hL hσ) hR
    (by rw [hRΔ, hΔ]; ring) hm hc

lemma mixed_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ R : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hR : 0 < R)
    (hΔ : Δ = L * σ ^ 2) (hRΔ : R ^ 2 = Δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x : E) (hgap : ∀ y, f x - f y ≤ Δ) (S : E ≃L[ℝ] E)
    (hS : ∀ v, ‖S v‖ ^ 2 = ⟪fderiv ℝ (gradient f) x v, v⟫ + 8 * L * σ * ‖v‖ ^ 2)
    (a b : E) :
    |⟪fderiv ℝ (fderiv ℝ (gradient f)) x a b, b⟫| ≤ 27 / R * ‖S a‖ * ‖S b‖ ^ 2 := by
  have hh := ThirdOrderObjectiveGeometry.third_mixed_bound hf x S (by positivity : 0 ≤ 9 / R)
    (diagonal_bound hf hL hσ hR hΔ hRΔ hT x hgap S hS) a b
  convert hh using 1
  ring

lemma hessian_transport {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ R : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hR : 0 < R)
    (hΔ : Δ = L * σ ^ 2) (hRΔ : R ^ 2 = Δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x : E) (hgap : ∀ y, f x - f y ≤ Δ) (S : E ≃L[ℝ] E)
    (hS : ∀ v, ‖S v‖ ^ 2 = ⟪fderiv ℝ (gradient f) x v, v⟫ + 8 * L * σ * ‖v‖ ^ 2)
    (s v : E) :
    |⟪(fderiv ℝ (gradient f) (x + s) - fderiv ℝ (gradient f) x) v, v⟫| ≤
      (27 * (‖S s‖ / R) + (‖S s‖ / R) ^ 2) * ‖S v‖ ^ 2 := by
  let A := fderiv ℝ (gradient f) (x + s) - fderiv ℝ (gradient f) x
  let T := fderiv ℝ (fderiv ℝ (gradient f)) x
  have hr : ‖A - T s‖ ≤ L * ‖s‖ ^ 2 := by
    simpa [A, T] using ThirdOrderObjectiveGeometry.hessian_taylor_remainder hf hL.le hT x (x + s)
  have hm (w : E) : L * σ * ‖w‖ ^ 2 ≤ ‖S w‖ ^ 2 := by
    have hl := ThirdOrderObjectiveGeometry.hessian_quadratic_lower hf hL hσ hΔ hT x w hgap
    have hs := hS w
    nlinarith [mul_nonneg (mul_pos hL hσ).le (sq_nonneg ‖w‖)]
  have hp := mul_le_mul (hm s) (hm v) (by positivity : 0 ≤ L * σ * ‖v‖ ^ 2) (sq_nonneg ‖S s‖)
  have hscale : L * ‖s‖ ^ 2 * ‖v‖ ^ 2 ≤ (‖S s‖ / R) ^ 2 * ‖S v‖ ^ 2 := by
    have he : L * σ ^ 2 = R ^ 2 := hΔ.symm.trans hRΔ.symm
    have hp' : (L * ‖s‖ ^ 2 * ‖v‖ ^ 2) * R ^ 2 ≤ ‖S s‖ ^ 2 * ‖S v‖ ^ 2 := by
      calc
        _ = (L * σ * ‖s‖ ^ 2) * (L * σ * ‖v‖ ^ 2) := by rw [← he]; ring
        _ ≤ _ := hp
    have hh := (le_div_iff₀ (sq_pos_of_pos hR)).mpr hp'
    convert hh using 1
    rw [div_pow]
    ring

  have he : |⟪(A - T s) v, v⟫| ≤ (‖S s‖ / R) ^ 2 * ‖S v‖ ^ 2 := by
    calc
      _ ≤ ‖(A - T s) v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A - T s‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (L * ‖s‖ ^ 2 * ‖v‖) * ‖v‖ := by gcongr
      _ = L * ‖s‖ ^ 2 * ‖v‖ ^ 2 := by ring
      _ ≤ _ := hscale
  have ht := mixed_bound hf hL hσ hR hΔ hRΔ hT x hgap S hS s v
  have hid : ⟪A v, v⟫ = ⟪(A - T s) v, v⟫ + ⟪T s v, v⟫ := by
    simp only [sub_apply, inner_sub_left]
    ring
  rw [hid]
  calc
    _ ≤ |⟪(A - T s) v, v⟫| + |⟪T s v, v⟫| := abs_add_le _ _
    _ ≤ (‖S s‖ / R) ^ 2 * ‖S v‖ ^ 2 + 27 / R * ‖S s‖ * ‖S v‖ ^ 2 := add_le_add he ht
    _ = _ := by ring

lemma guarded_hessian_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ R : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hR : 0 < R)
    (hΔ : Δ = L * σ ^ 2) (hRΔ : R ^ 2 = Δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
    (x : E) (hgap : ∀ y, f x - f y ≤ Δ) (S : E ≃L[ℝ] E)
    (hS : ∀ v, ‖S v‖ ^ 2 = ⟪fderiv ℝ (gradient f) x v, v⟫ + 8 * L * σ * ‖v‖ ^ 2)
    (s v : E) (hs : ‖S s‖ ≤ R / 256) :
    7 / 8 * ‖S v‖ ^ 2 - 8 * L * σ * ‖v‖ ^ 2 ≤
        ⟪fderiv ℝ (gradient f) (x + s) v, v⟫ ∧
      ⟪fderiv ℝ (gradient f) (x + s) v, v⟫ ≤ 9 / 8 * ‖S v‖ ^ 2 := by
  have ht : ‖S s‖ / R ≤ 1 / 256 := by
    apply (div_le_iff₀ hR).mpr
    linarith
  have ht₀ : 0 ≤ ‖S s‖ / R := by positivity
  have hc : 27 * (‖S s‖ / R) + (‖S s‖ / R) ^ 2 ≤ 1 / 8 := by
    have hh := pow_le_pow_left₀ ht₀ ht 2
    nlinarith
  have hh := (hessian_transport hf hL hσ hR hΔ hRΔ hT x hgap S hS s v).trans
    (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  simp only [sub_apply, inner_sub_left] at hl hu
  have hvs := hS v
  constructor
  · linarith
  · nlinarith [mul_nonneg (mul_pos hL hσ).le (sq_nonneg ‖v‖)]

end LongTails.Proofs.QuarticMetricTransport
