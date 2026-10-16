import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ScalarClippedAcceleration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma projection_step {Q : Set E} (hQ : Convex ℝ Q) {z g u next : E}
    {a h : ℝ} (hh : 0 < h) (hu : u ∈ Q) (hn : next ∈ Q)
    (hp : ‖z - (a / h) • g - next‖ = ⨅ w : Q, ‖z - (a / h) • g - w‖) :
    a * ⟪g, next - u⟫ ≤
      h / 2 * (‖z - u‖ ^ 2 - ‖next - u‖ ^ 2 - ‖next - z‖ ^ 2) := by
  have hi := (norm_eq_iInf_iff_real_inner_le_zero hQ hn).mp hp u hu
  have he : z - (a / h) • g - next = z - next - (a / h) • g := by abel
  rw [he, show u - next = -(next - u) by abel, inner_neg_right,
    inner_sub_left, real_inner_smul_left] at hi
  have hd : a * ⟪g, next - u⟫ / h ≤ ⟪z - next, next - u⟫ := by
    rw [show a * ⟪g, next - u⟫ / h = a / h * ⟪g, next - u⟫ by ring]
    linarith
  have hm := (div_le_iff₀ hh).mp hd
  have hs : ‖z - u‖ ^ 2 =
      ‖z - next‖ ^ 2 + 2 * ⟪z - next, next - u⟫ + ‖next - u‖ ^ 2 := by
    rw [show z - u = (z - next) + (next - u) by abel, norm_add_sq_real]
  rw [hs, norm_sub_rev next z]
  nlinarith only [hm]

lemma error_movement {a h : ℝ} (hh : 0 < h) (e v : E) :
    -(a * ⟪e, v⟫) ≤ a ^ 2 * ‖e‖ ^ 2 / h + h / 4 * ‖v‖ ^ 2 := by
  have hs := sq_nonneg ‖v + (2 * a / h) • e‖
  rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm e v] at hs
  have hm := mul_nonneg (show 0 ≤ h / 4 by positivity) hs
  have he : h / 4 * (‖v‖ ^ 2 + 2 * (2 * a / h * ⟪e, v⟫) +
      (2 * a / h) ^ 2 * ‖e‖ ^ 2) =
      h / 4 * ‖v‖ ^ 2 + a * ⟪e, v⟫ + a ^ 2 * ‖e‖ ^ 2 / h := by
    field_simp
    ring
  rw [he] at hm
  linarith

lemma accelerated_step {f : E → ℝ} {x z u next grad g : E} {A a L h : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hB : 0 < A + a) (hh : 0 < h)
    (hcoef : L * a ^ 2 / (2 * (A + a)) ≤ h / 4)
    (hx : f ((A / (A + a)) • x + (a / (A + a)) • z) +
      ⟪grad, x - ((A / (A + a)) • x + (a / (A + a)) • z)⟫ ≤ f x)
    (hu : f ((A / (A + a)) • x + (a / (A + a)) • z) +
      ⟪grad, u - ((A / (A + a)) • x + (a / (A + a)) • z)⟫ ≤ f u)
    (hsmooth : f ((A / (A + a)) • x + (a / (A + a)) • next) ≤
      f ((A / (A + a)) • x + (a / (A + a)) • z) +
      ⟪grad, (a / (A + a)) • (next - z)⟫ +
        L / 2 * ‖(a / (A + a)) • (next - z)‖ ^ 2)
    (hproj : a * ⟪g, next - u⟫ ≤
      h / 2 * (‖z - u‖ ^ 2 - ‖next - u‖ ^ 2 - ‖next - z‖ ^ 2)) :
    (A + a) * (f ((A / (A + a)) • x + (a / (A + a)) • next) - f u) +
        h / 2 * ‖next - u‖ ^ 2 ≤
      A * (f x - f u) + h / 2 * ‖z - u‖ ^ 2 +
        a ^ 2 * ‖g - grad‖ ^ 2 / h - a * ⟪g - grad, z - u⟫ := by
  let y := (A / (A + a)) • x + (a / (A + a)) • z
  have hid : A • (x - y) + a • (u - y) = a • (u - z) := by
    dsimp [y]
    match_scalars
    all_goals field_simp [hB.ne'] <;> ring
  have hi := congrArg (fun v => ⟪grad, v⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hx' := mul_le_mul_of_nonneg_left hx hA
  have hu' := mul_le_mul_of_nonneg_left hu ha
  have hn : ⟪grad, u - z⟫ = -⟪grad, z - u⟫ := by
    rw [show u - z = -(z - u) by abel, inner_neg_right]
  rw [hn] at hi
  have hw : (A + a) * (f y - f u) ≤ A * (f x - f u) + a * ⟪grad, z - u⟫ := by
    dsimp [y] at *
    nlinarith only [hx', hu', hi]
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsmooth
  have hd := mul_le_mul_of_nonneg_left hsmooth hB.le
  have he : (A + a) * (f y + a / (A + a) * ⟪grad, next - z⟫ +
      L / 2 * ((a / (A + a)) ^ 2 * ‖next - z‖ ^ 2)) =
      (A + a) * f y + a * ⟪grad, next - z⟫ +
        L * a ^ 2 / (2 * (A + a)) * ‖next - z‖ ^ 2 := by
    field_simp
  change (A + a) * _ ≤ (A + a) * (f y + _ + _) at hd
  rw [he] at hd
  have hc := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖next - z‖)
  have hy := error_movement (a := a) hh (g - grad) (next - z)
  have hadd : ⟪g, next - u⟫ = ⟪grad, z - u⟫ + ⟪grad, next - z⟫ +
      ⟪g - grad, z - u⟫ + ⟪g - grad, next - z⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  dsimp [y] at hw hd
  rw [hadd] at hproj
  linarith only [hw, hd, hc, hy, hproj]

lemma potential_telescope (f : E → ℝ) (x z e : ℕ → E) (u : E)
    (A a : ℕ → ℝ) {h : ℝ} (hh : 0 ≤ h) (hA : A 0 = 0)
    (hstep : ∀ t,
      A (t + 1) * (f (x (t + 1)) - f u) + h / 2 * ‖z (t + 1) - u‖ ^ 2 ≤
        A t * (f (x t) - f u) + h / 2 * ‖z t - u‖ ^ 2 +
          (a t) ^ 2 * ‖e t‖ ^ 2 / h - a t * ⟪e t, z t - u⟫) (N : ℕ) :
    A N * (f (x N) - f u) ≤ h / 2 * ‖z 0 - u‖ ^ 2 +
      (∑ t ∈ Finset.range N, (a t) ^ 2 * ‖e t‖ ^ 2) / h -
        ∑ t ∈ Finset.range N, a t * ⟪e t, z t - u⟫ := by
  have hp : ∀ n,
      A n * (f (x n) - f u) + h / 2 * ‖z n - u‖ ^ 2 ≤
        h / 2 * ‖z 0 - u‖ ^ 2 +
          ∑ t ∈ Finset.range n, ((a t) ^ 2 * ‖e t‖ ^ 2 / h - a t * ⟪e t, z t - u⟫) := by
    intro n
    induction n with
    | zero => simp [hA]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith only [ih, hstep n]
  have hn := hp N
  rw [Finset.sum_sub_distrib, ← Finset.sum_div] at hn
  have hz : 0 ≤ h / 2 * ‖z N - u‖ ^ 2 := by positivity
  linarith only [hn, hz]

end LongTails.Proofs.ScalarClippedAcceleration
