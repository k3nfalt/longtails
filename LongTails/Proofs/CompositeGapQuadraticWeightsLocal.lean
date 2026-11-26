import LongTails.Algorithms.CompositeGapQuadraticWeights
import LongTails.Proofs.CompositeGapModel
import LongTails.Proofs.CompositeGeneralizedStep

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CompositeGapQuadraticWeights

open LongTails.Setups.CompositeGapSmooth
open OracleTemplate OracleTemplate.CompositeGapQuadraticWeights
open CompositeGapGeometry CompositeGapModel

variable {p : Params} {I : Instance p} {s c : p.E}

lemma upper_ball (h : Conditions p I s) {x : p.E} {M r d : ℝ}
    (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) (hM : 0 < M) (hr : 0 < r)
    (hd : M * r ^ 2 = d) (hcoef : p.H0 + p.H1 * d ≤ M)
    (hloc : Real.sqrt p.H1 * r ≤ 1) (hx : x ∈ I.Q)
    (hgap : objective I x - objective I s ≤ d) (u : p.E) (hu : ‖u - x‖ ≤ r) :
    smoothShift I s u ≤ 6 * d := by
  have hd' : 0 < d := hd ▸ mul_pos hM (sq_pos_of_pos hr)
  have hg := shifted_gradient_sq h h0 h1 hx hd' hgap hcoef
  have hgn : ‖I.grad x - I.grad s‖ ≤ 4 * M * r := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [← hd] at hg
    nlinarith only [hg]
  have ht := shifted_upper h hx ((mul_le_mul_of_nonneg_left hu (Real.sqrt_nonneg _)).trans hloc)
  have hi := (real_inner_le_norm (I.grad x - I.grad s) (u - x)).trans
    (mul_le_mul hgn hu (norm_nonneg _) (by positivity))
  have hc : p.H0 + p.H1 * (objective I x - objective I s) ≤ M := by
    linarith [mul_le_mul_of_nonneg_left hgap h1]
  have hm := mul_le_mul hc ((sq_le_sq₀ (norm_nonneg _) hr.le).mpr hu)
    (sq_nonneg _) hM.le
  nlinarith only [ht, hi, hm, (smoothShift_le_gap h hx).trans hgap, hd]

lemma probe (h : Conditions p I s) {x y : p.E} {M r d : ℝ}
    (hr : 0 < r) (hd : M * r ^ 2 = d) (hy : ‖y - x‖ ≤ r / 2)
    (hb : ∀ u, ‖u - x‖ ≤ r → smoothShift I s u ≤ 6 * d) (hM : 0 < M) :
    ‖I.grad y - I.grad s‖ ≤ 12 * M * r := by
  let g := I.grad y - I.grad s
  by_cases hg : ‖g‖ = 0
  · change ‖g‖ ≤ _
    rw [hg]
    positivity
  let t := r / (2 * ‖g‖)
  have hgp : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg)
  have ht : 0 < t := by dsimp [t]; positivity
  have he : t * ‖g‖ = r / 2 := by dsimp [t]; field_simp
  have hn : ‖t • g‖ = r / 2 := by rwa [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hball : ‖y + t • g - x‖ ≤ r := by
    rw [show y + t • g - x = (y - x) + t • g by abel]
    linarith [norm_add_le (y - x) (t • g)]
  have hh := shifted_support h (y + t • g) y
  rw [add_sub_cancel_left, inner_smul_right, real_inner_self_eq_norm_sq] at hh
  change smoothShift I s y + t * ‖g‖ ^ 2 ≤ _ at hh
  change ‖g‖ ≤ _
  apply (mul_le_mul_iff_right₀ hr).mp
  nlinarith only [hh, congrArg (· * ‖g‖) he,
    hb _ hball, smoothShift_nonneg h y, hd]

lemma scaled_displacement {a θ M r d D J : ℝ} (ha : 0 ≤ a) (hθ : 0 ≤ θ)
    (hr : 0 < r) (hd : M * r ^ 2 = d) (hD : 0 ≤ D)
    (hsmall : 64 * (θ * a) * M ≤ 1) (hJ : θ * J ≤ 4 * d)
    (hstep : D ^ 2 / 2 ≤ a * (12 * M * r) * D + a * J) : θ * D ≤ r := by
  have hs := mul_le_mul_of_nonneg_left hstep (sq_nonneg θ)
  have hj := mul_le_mul_of_nonneg_left hJ (mul_nonneg hθ ha)
  have hlin := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ r * (θ * D) by positivity)
  have hquad := mul_le_mul_of_nonneg_right hsmall (sq_nonneg r)
  rw [← hd] at hj
  by_contra! hh
  have hp := mul_pos (sub_pos.mpr hh) (show 0 < 32 * (θ * D) + 20 * r by positivity)
  nlinarith only [hs, hj, hlin, hquad, hp, sq_nonneg r]

lemma mass_succ (M : ℝ) (n : ℕ) : mass M (n + 1) = mass M n + increment M n := by
  simp only [mass, increment, Nat.cast_succ]
  ring

lemma fraction_eq {M : ℝ} (hM : 0 < M) (n : ℕ) :
    increment M n / (mass M n + increment M n) = 2 / ((n : ℝ) + 2) := by
  rw [← mass_succ]
  simp only [mass, increment, Nat.cast_succ]
  field_simp
  ring

end LongTails.Proofs.CompositeGapQuadraticWeights
