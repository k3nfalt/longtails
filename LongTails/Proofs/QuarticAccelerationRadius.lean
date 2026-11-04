import LongTails.Proofs.QuarticAccelerationTrace

namespace LongTails.Proofs.QuarticAccelerationRadius

open LongTails.Algorithms.CompositeCubicAcceleration hiding advance damping
open LongTails.Algorithms.QuarticAcceleration
open LongTails.Proofs.QuarticAccelerationEnergy LongTails.Proofs.QuarticAccelerationTrace
open LongTails.Proofs.CompositeCubicAcceleration hiding advance_certificate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma ball_mixture (x y xstar : E) {b c B : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 < b + c)
    (hx : ‖x - xstar‖ ≤ B) (hy : ‖y - xstar‖ ≤ B) :
    ‖(b + c)⁻¹ • (b • x + c • y) - xstar‖ ≤ B := by
  have hw : b / (b + c) + c / (b + c) = 1 := by field_simp
  have hxm : x ∈ Metric.closedBall xstar B := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
  have hym : y ∈ Metric.closedBall xstar B := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
  have hh := (convex_closedBall xstar B) hxm hym (div_nonneg hb hs.le) (div_nonneg hc hs.le) hw
  have he : (b + c)⁻¹ • (b • x + c • y) =
      (b / (b + c)) • x + (c / (b + c)) • y := by
    simp only [smul_add, smul_smul, div_eq_mul_inv, mul_comm]
  rw [he]
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hh

lemma large_parameter_radius {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) {k : ℕ} (hk : k < N)
    (hlarge : t.guess k ≤ lam t γ k) :
    ‖t.point k - location t k‖ ^ 2 ≤ 2 * R ^ 2 := by
  have hcoef := trial_coefficient (hv.guess_pos k hk.le) (weight_nonneg hv k hk.le)
  have hh := dissipation_bound hv hc hγ hx0 hmin hk
  unfold dissipation at hh
  rw [min_eq_left hlarge] at hh
  apply dissipation_radius (rest := 0) (by norm_num) hcoef
  simpa only [zero_add, mul_assoc] using hh

lemma guess_bound {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) (hN : 0 < N) :
    ∀ k ≤ N, t.guess k ≤ 8 * γ * R ^ 2 := by
  intro k hk
  induction k with
  | zero =>
    have hh := large_parameter_radius hv hc hγ hx0 hmin hN (hv.first_guess hN).le
    rw [hv.first_guess hN]
    unfold lam parameter
    have hm := mul_le_mul_of_nonneg_left hh hγ.le
    nlinarith only [hm, mul_nonneg hγ.le (sq_nonneg R)]
  | succ k ih =>
    have hlt : k < N := by omega
    rw [hv.guess_eq k hlt]
    unfold nextGuess
    split_ifs with hd
    · have hp := hv.guess_pos k hlt.le
      linarith [ih hlt.le]
    · have hu : t.guess k < lam t γ k := lt_of_not_ge hd
      have hh := large_parameter_radius hv hc hγ hx0 hmin hlt hu.le
      have hm := mul_le_mul_of_nonneg_left hh hγ.le
      unfold lam parameter at hu
      nlinarith only [hu, hm]

lemma movement_bound {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) {k : ℕ} (hk : k < N) :
    ‖t.point k - location t k‖ ≤ 3 * R := by
  have hR := (norm_nonneg _).trans hx0
  apply movement_radius hR (norm_nonneg _)
  by_cases hlarge : t.guess k ≤ lam t γ k
  · have hh := large_parameter_radius hv hc hγ hx0 hmin hk hlarge
    nlinarith only [hh, sq_nonneg R]
  · have hl := (le_of_not_ge hlarge).trans (guess_bound hv hc hγ hx0 hmin (by omega) k hk.le)
    unfold lam parameter at hl
    apply (mul_le_mul_iff_right₀ hγ).mp
    nlinarith only [hl]

lemma center_ball (s : State E) (xstar : E) {μ B : ℝ} (hμ : 0 < μ) (hA : 0 ≤ s.weight)
    (hx : ‖s.point - xstar‖ ≤ B) (hv : ‖s.momentum - xstar‖ ≤ B) :
    ‖center E μ s - xstar‖ ≤ B := by
  exact ball_mixture s.point s.momentum xstar hA (trialWeight_pos hμ hA).le
    (add_pos_of_nonneg_of_pos hA (trialWeight_pos hμ hA)) hx hv

lemma advance_ball (s : State E) (xstar y g : E) {μ γ B : ℝ} (hμ : 0 < μ) (hA : 0 ≤ s.weight)
    (hlam : 0 < parameter E γ (center E μ s) y)
    (hx : ‖s.point - xstar‖ ≤ B) (hy : ‖y - xstar‖ ≤ B) :
    ‖(advance E μ γ s y g).point - xstar‖ ≤ B := by
  let a := trialWeight μ s.weight
  let β := damping E μ γ s y
  have ha : 0 < a := trialWeight_pos hμ hA
  have hb := damping_properties hμ hlam
  have he : (1 - β) * s.weight + β * (s.weight + a) = s.weight + β * a := by ring
  have hp : 0 < s.weight + β * a := add_pos_of_nonneg_of_pos hA (mul_pos hb.1 ha)
  have hh := ball_mixture s.point y xstar (b := (1 - β) * s.weight) (c := β * (s.weight + a)) (mul_nonneg (sub_nonneg.mpr hb.2.1) hA)
    (mul_nonneg hb.1.le (add_nonneg hA ha.le)) (by rw [he]; exact hp) hx hy
  rw [he] at hh
  exact hh

lemma point_center_radius {t : Trace E} {f : E → ℝ} {γ R : ℝ} {x0 xstar : E} {N : ℕ}
    (hv : Valid t f γ x0 N) (hc : ConvexOn ℝ Set.univ f) (hγ : 0 < γ)
    (hx0 : ‖x0 - xstar‖ ≤ R) (hmin : ∀ x, f xstar ≤ f x) : ∀ k ≤ N,
    ‖(t.state k).point - xstar‖ ≤ (1 + 3 * (k : ℝ)) * R ∧
    ‖location t k - xstar‖ ≤ (1 + 3 * (k : ℝ)) * R := by
  let B := fun k : ℕ => (1 + 3 * (k : ℝ)) * R
  have hR : 0 ≤ R := (norm_nonneg _).trans hx0
  have hB k : R ≤ B k := by
    dsimp [B]
    nlinarith only [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hR]
  have hBs k : B (k + 1) = B k + 3 * R := by dsimp [B]; push_cast; ring
  have hp k (hk : k ≤ N) : ‖(t.state k).point - xstar‖ ≤ B k := by
    induction k with
    | zero => simpa [hv.initial, B] using hx0
    | succ k ih =>
      have hlt : k < N := by omega
      have hpoint := ih hlt.le
      have hcenter := center_ball (t.state k) xstar (hv.guess_pos k hlt.le) (weight_nonneg hv k hlt.le)
        hpoint ((momentum_radius hv hc hγ hx0 hmin hlt.le).trans (hB k))
      have hmove := movement_bound hv hc hγ hx0 hmin hlt
      have hy : ‖t.point k - xstar‖ ≤ B (k + 1) := by
        have hh := norm_sub_le_norm_sub_add_norm_sub (t.point k) (location t k) xstar
        rw [hBs]
        change ‖location t k - xstar‖ ≤ B k at hcenter
        linarith only [hh, hcenter, hmove]
      rw [hv.advance_eq k hlt]
      apply advance_ball (t.state k) xstar (t.point k) (t.gradient k)
        (hv.guess_pos k hlt.le) (weight_nonneg hv k hlt.le) (hv.lam_pos k hlt) _ hy
      rw [hBs]
      linarith only [hpoint, hR]
  intro k hk
  exact ⟨hp k hk, center_ball (t.state k) xstar (hv.guess_pos k hk) (weight_nonneg hv k hk)
    (hp k hk) ((momentum_radius hv hc hγ hx0 hmin hk).trans (hB k))⟩


end LongTails.Proofs.QuarticAccelerationRadius
