import LongTails.Algorithms.DashaScaling
import LongTails.Proofs.DashaTracking
import LongTails.Proofs.DashaQuantization
import LongTails.Proofs.SvrgConvex

namespace LongTails.Proofs.DashaScalingDescent

open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling

variable {p : Params}

lemma objective_gradient (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (x : Point p) :
    HasGradientAt (objective p f)
      ((1 / (p.n : ℝ)) • ∑ i, gradient (f i) x) x := by
  have he : objective p f = LongTails.Setups.FiniteSumSmoothAndConvex.objective f := by
    funext y
    simp only [LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex.objective,
      LongTails.Setups.FiniteSumSmoothAndConvex.objective]
  rw [he]
  simpa only [OracleTemplate.FiniteSum.fullGradient, one_div] using
    OracleTemplate.FiniteSum.objective_gradient (f := f)
      (oracle := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2) hg x

lemma objective_gradient_eq (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (x : Point p) :
    gradient (objective p f) x = (1 / (p.n : ℝ)) • ∑ i, gradient (f i) x :=
  (objective_gradient f hg x).gradient

lemma mean_norm (v : Fin p.n → Point p) :
    ‖(1 / (p.n : ℝ)) • ∑ i, v i‖ ≤ (1 / (p.n : ℝ)) * ∑ i, ‖v i‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

lemma mean_norm_sq (v : Fin p.n → Point p) :
    ‖(1 / (p.n : ℝ)) • ∑ i, v i‖ ^ 2 ≤ (1 / (p.n : ℝ)) * ∑ i, ‖v i‖ ^ 2 := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hsum := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖v i‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hsum
  have hm := mean_norm v
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hm
  have hb := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (1 / (p.n : ℝ)) ^ 2 by positivity)
  have he : (1 / (p.n : ℝ)) ^ 2 * ((∑ i, ‖v i‖ ^ 2) * p.n) =
      (1 / (p.n : ℝ)) * ∑ i, ‖v i‖ ^ 2 := by field_simp
  rw [he] at hb
  nlinarith

lemma objective_lipschitz_mean_square (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (hH : 0 ≤ p.Lhat)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (x y : Point p) :
    ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.Lhat * ‖x - y‖ := by
  rw [objective_gradient_eq f hg x, objective_gradient_eq f hg y, ← smul_sub,
    ← Finset.sum_sub_distrib]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) := mean_norm_sq _
    _ ≤ p.Lhat ^ 2 * ‖x - y‖ ^ 2 := hs x y
    _ = _ := by rw [mul_pow]

lemma objective_lipschitz_effective (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (hH : 0 ≤ p.Lhat)
    (hL : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (x y : Point p) :
    ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ min p.L p.Lhat * ‖x - y‖ := by
  rcases le_total p.L p.Lhat with h | h
  · rw [min_eq_left h]
    exact hL x y
  · rw [min_eq_right h]
    exact objective_lipschitz_mean_square f hg hH hs x y

lemma estimate_eq_mean (c : Choice p) (s : Iterate p) :
    estimate p c s = (1 / (p.n : ℝ)) • ∑ i,
      LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i) := by
  unfold estimate
  congr 1
  ext j
  simp [LongTails.Algorithms.DashaQuantization.reconstruct, Finset.mul_sum]

lemma trajectory_gradient (c : Choice p) (f : Functions p) (seed : ℕ → Sample p)
    (k : ℕ) (i : Fin p.n) :
    (trajectory p c f seed k).localGradient i = gradient (f i) (trajectory p c f seed k).point := by
  cases k <;> rfl

lemma trajectory_step (c : Choice p) (f : Functions p) (seed : ℕ → Sample p) (k : ℕ) :
    (trajectory p c f seed (k + 1)).point =
      (trajectory p c f seed k).point - stepSize p c • estimate p c (trajectory p c f seed k) := rfl

lemma reconstruct_add (c : Choice p) (z w : Fin p.d → ℤ) :
    LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (fun j => z j + w j) =
      LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) z +
      LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) w := by
  ext j
  simp [LongTails.Algorithms.DashaQuantization.reconstruct, mul_add]

lemma next_local_code (c : Choice p) (f : Functions p) (s : Iterate p) (seed : Sample p)
    (i : Fin p.n) :
    let xnext := s.point - stepSize p c • estimate p c s
    let g := LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.localCode i)
    let u := gradient (f i) xnext - s.localGradient i - momentum p c • (g - s.localGradient i)
    LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c)
      ((nextIterate p c f s seed).localCode i) =
      g + LongTails.Algorithms.DashaCyclic.compress c.block c.precision (spacing p c) u (seed i) := by
  exact reconstruct_add c _ _

lemma initial_gradient_gap (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2)
    (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x)
    (hgap : objective p f p.x0 - lower ≤ p.Δ) :
    ‖gradient (objective p f) p.x0‖ ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ := by
  let L := min p.L p.Lhat
  let g := gradient (objective p f) p.x0
  have hpos : 0 < L := lt_min hL hH
  have hgrad : ∀ x, HasGradientAt (objective p f) (gradient (objective p f) x) x := by
    intro x
    rw [objective_gradient_eq f hg x]
    exact objective_gradient f hg x
  have hd := DashaTracking.inexact_descent hgrad
    (objective_lipschitz_effective f hg hH.le hlip hs) p.x0 g (1 / L)
  change objective p f (p.x0 - (1 / L) • g) ≤
    objective p f p.x0 - (1 / L) / 2 * ‖g‖ ^ 2 -
      ((1 / L) / 2 - L * (1 / L) ^ 2 / 2) * ‖g‖ ^ 2 +
      (1 / L) / 2 * ‖g - g‖ ^ 2 at hd
  have he : objective p f p.x0 - (1 / L) / 2 * ‖g‖ ^ 2 -
      ((1 / L) / 2 - L * (1 / L) ^ 2 / 2) * ‖g‖ ^ 2 +
      (1 / L) / 2 * ‖g - g‖ ^ 2 = objective p f p.x0 - ‖g‖ ^ 2 / (2 * L) := by
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    field_simp
    ring
  rw [he] at hd
  have hb : ‖g‖ ^ 2 / (2 * L) ≤ p.Δ := by linarith [hlower (p.x0 - (1 / L) • g)]
  have hb' := (div_le_iff₀ (show 0 < 2 * L by positivity)).mp hb
  change ‖g‖ ^ 2 ≤ 2 * L * p.Δ
  nlinarith only [hb']

lemma initial_gradient_norm (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G) :
    ‖gradient (objective p f) p.x0‖ ≤ p.G := by
  rw [objective_gradient_eq f hg]
  calc
    _ ≤ (1 / (p.n : ℝ)) * ∑ i, ‖gradient (f i) p.x0‖ := mean_norm _
    _ ≤ (1 / (p.n : ℝ)) * ∑ _ : Fin p.n, p.G :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hG i)) (by positivity)
    _ = p.G := by simp [ne_of_gt (show (0 : ℝ) < p.n by exact_mod_cast p.n.pos)]

lemma initial_gradient_certificate {f : Functions p}
    (hgap : ‖gradient (objective p f) p.x0‖ ^ 2 ≤ 2 * min p.L p.Lhat * p.Δ)
    (hG : ‖gradient (objective p f) p.x0‖ ≤ p.G)
    (hcert : min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2) :
    ‖gradient (objective p f) p.x0‖ ^ 2 ≤ p.ε ^ 2 := by
  have hG0 : 0 ≤ p.G := (norm_nonneg _).trans hG
  have hsq := (sq_le_sq₀ (norm_nonneg _) hG0).mpr hG
  exact (le_min hgap hsq).trans hcert

lemma sparse_trajectory_gradient (c initializer : Choice p) (f : Functions p) (seed : ℕ → Sample p)
    (k : ℕ) (i : Fin p.n) :
    (sparseTrajectory p c initializer f seed k).localGradient i =
      gradient (f i) (sparseTrajectory p c initializer f seed k).point := by
  cases k <;> rfl

end LongTails.Proofs.DashaScalingDescent
