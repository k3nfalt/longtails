import LongTails.Proofs.GeneralizedMirrorSmoothness
import LongTails.Proofs.PowerMirrorGeometry

open Set

namespace LongTails.Proofs.GeneralizedMirrorCurvature

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V]

lemma shifted_lipschitz {F : E → V} {L0 L1 G : ℝ}
    (hgl : ∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    (c : V) (hc : ‖c‖ ≤ G) (x y : E) (M : ℝ)
    (hM : ∀ θ ∈ Icc (0 : ℝ) 1, ‖F (x + θ • (y - x)) - c‖ ≤ M) :
    ‖(F x - c) - (F y - c)‖ ≤ (L0 + L1 * G + L1 * M) * ‖x - y‖ := by
  have h := hgl x y (M + G) (by
    intro θ hθ
    have hn := norm_le_insert c (F (x + θ • (y - x)))
    rw [norm_sub_rev c] at hn
    have hh := hM θ hθ
    linarith)
  have he : F x - c - (F y - c) = F x - F y := by abel
  rw [he]
  nlinarith

lemma composite_self_bound {f ψ : E → ℝ} {df : E → E →L[ℝ] ℝ}
    {Q : Set E} {L0 L1 G : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (hG : 0 ≤ G) (hc : ConvexOn ℝ univ f) (hψ : ConvexOn ℝ Q ψ)
    (hd : Continuous df) (hf : ∀ x, HasFDerivAt f (df x) x)
    (hgl : ∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖df (x + θ • (y - x))‖ ≤ M) →
      ‖df x - df y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    {u x : E} (hu : u ∈ Q) (hx : x ∈ Q)
    (hmin : IsMinOn (fun w => f w + ψ w) Q u) (hgrad : ‖df u‖ ≤ G) :
    ‖df x - df u‖ ^ 2 ≤
      32 * (L0 + L1 * G + L1 * ‖df x - df u‖) * (f x + ψ x - (f u + ψ u)) := by
  let H : E → ℝ := fun w => f w - df u w
  let dH : E → E →L[ℝ] ℝ := fun w => df w - df u
  have hDH : ∀ w, HasFDerivAt H (dH w) w :=
    fun w => (hf w).sub (df u).hasFDerivAt
  have hHmin : ∀ w, H u ≤ H w := by
    intro w
    have hs := PowerMirrorGeometry.convex_support hc (mem_univ u) (mem_univ w) (hf u)
    simp only [map_sub] at hs
    dsimp [H]
    linarith
  have hbase : 0 < L0 + L1 * G := by positivity
  have hs := GeneralizedMirrorSmoothness.self_bound hbase hL1
    (show Continuous dH from hd.sub continuous_const) hDH
    (fun w z M hM => shifted_lipschitz hgl (df u) hgrad w z M hM) x u hHmin
  have ho := GeneralizedMirrorGeometry.composite_optimality hψ hu (hf u) hmin hx
  simp only [map_sub] at ho
  have hgap : H x - H u ≤ f x + ψ x - (f u + ψ u) := by dsimp [H]; linarith
  have hcoef : 0 ≤ 32 * (L0 + L1 * G + L1 * ‖df x - df u‖) := by positivity
  exact hs.trans (mul_le_mul_of_nonneg_left hgap hcoef)

lemma solve_self_bound {n B L Δ : ℝ} (hB : 0 ≤ B)
    (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (h : n ^ 2 ≤ 32 * (B + L * n) * Δ) :
    n ≤ 64 * L * Δ + 8 * Real.sqrt (B * Δ) := by
  have hs := Real.sqrt_nonneg (B * Δ)
  have hs2 := Real.sq_sqrt (mul_nonneg hB hΔ)
  have hc : 0 ≤ L * Δ := mul_nonneg hL hΔ
  by_contra hh
  push Not at hh
  have hp : 0 < (n - 64 * L * Δ - 8 * Real.sqrt (B * Δ)) *
      (n + 8 * Real.sqrt (B * Δ)) := mul_pos (by linarith) (by linarith)
  nlinarith [mul_nonneg hc hs, mul_nonneg hB hΔ]

lemma curvature_from_self_bound {n B L Δ : ℝ} (hn : 0 ≤ n) (hB : 0 ≤ B)
    (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (h : n ^ 2 ≤ 32 * (B + L * n) * Δ) :
    B + L * n ≤ 2 * B + 64 * L ^ 2 * Δ := by
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg L)
  have hd : 0 ≤ L ^ 2 * Δ := mul_nonneg (sq_nonneg L) hΔ
  have ht : 0 ≤ L * n := mul_nonneg hL hn
  by_contra hh
  push Not at hh
  have hp : 0 < (L * n - (B + 64 * L ^ 2 * Δ)) * (L * n + B) :=
    mul_pos (by linarith) (by linarith)
  nlinarith [mul_nonneg hB hd, mul_nonneg hd ht]

lemma local_curvature {F : E → V} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hc : Continuous F)
    (hgl : ∀ x y M, (∀ θ ∈ Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    (x y : E) (hd : L1 * ‖x - y‖ ≤ 1 / 2) :
    L0 + L1 * ‖F y‖ ≤ 2 * (L0 + L1 * ‖F x‖) := by
  have h := GeneralizedMirrorSmoothness.local_difference hL0 hL1 hc hgl x y hd
  have hi := norm_le_insert (F x) (F y)
  have hm := mul_le_mul_of_nonneg_left h hL1
  have hn := mul_le_mul_of_nonneg_left hi hL1
  have hb : 0 ≤ L0 + L1 * ‖F x‖ := by positivity
  have ht := mul_le_mul_of_nonneg_left hd hb
  nlinarith

lemma weighted_gradient_bound {n A a B L Δ R : ℝ}
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hΔ : 0 ≤ Δ) (hR : 0 < R)
    (hself : n ^ 2 ≤ 32 * (B + L * n) * Δ)
    (hgap : A * Δ ≤ R ^ 2)
    (hbase : 16384 * B * a ^ 2 ≤ A)
    (hlinear : 1024 * L * R * a ≤ A) : a * n ≤ R / 8 := by
  have hn := solve_self_bound hB hL hΔ hself
  have hn' := mul_le_mul_of_nonneg_left hn ha
  have hl := (mul_le_mul_of_nonneg_right hlinear hΔ).trans hgap
  have hb := (mul_le_mul_of_nonneg_right hbase hΔ).trans hgap
  have hs := Real.sq_sqrt (mul_nonneg hB hΔ)
  have hs0 := Real.sqrt_nonneg (B * Δ)
  have hterm1 : 64 * a * L * Δ ≤ R / 16 := by nlinarith
  have hterm2 : 8 * a * Real.sqrt (B * Δ) ≤ R / 16 := by
    have he : (a * Real.sqrt (B * Δ)) ^ 2 = a ^ 2 * (B * Δ) := by
      rw [mul_pow, hs]
    nlinarith [sq_nonneg (128 * a * Real.sqrt (B * Δ) - R),
      mul_nonneg ha hs0]
  nlinarith

lemma weighted_curvature_bound {A a B L Δ R C : ℝ}
    (hA : 0 < A) (ha : 0 ≤ a) (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) (hR : 0 < R)
    (hcurve : C ≤ 2 * B + 64 * L ^ 2 * Δ)
    (hgap : A * Δ ≤ R ^ 2)
    (hbase : 16384 * B * a ^ 2 ≤ A)
    (hlinear : 1024 * L * R * a ≤ A) : 256 * C * a ^ 2 ≤ A := by
  have hlin2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1024 * L * R * a) hlinear 2
  have hg := mul_le_mul_of_nonneg_left hgap hA.le
  have hterm := mul_le_mul_of_nonneg_right hlin2 hΔ
  have hrr : 0 < R ^ 2 := sq_pos_of_pos hR
  have hl : 1048576 * L ^ 2 * a ^ 2 * Δ ≤ A := by
    nlinarith
  have hc := mul_le_mul_of_nonneg_right hcurve (sq_nonneg a)
  nlinarith

end LongTails.Proofs.GeneralizedMirrorCurvature
