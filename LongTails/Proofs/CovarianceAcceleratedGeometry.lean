import LongTails.Proofs.CovarianceAcceleratedMixture

open MeasureTheory ProbabilityTheory Convexity
open scoped RealInnerProductSpace
open LongTails.Algorithms.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedMixture

namespace LongTails.Proofs.CovarianceAcceleratedGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} (z : Fin n → E)

lemma mean_single (i : Fin n) : mean z (StdSimplex.single i) = z i := by
  classical
  simp [mean, StdSimplex.weights_single, Finsupp.single_apply]

lemma mixture_single (i : Fin n) (u : E) :
    mixture z (StdSimplex.single i) u = density (z i) u := by
  classical
  simp [mixture, StdSimplex.weights_single, Finsupp.single_apply]

lemma mean_norm_le (w : StdSimplex ℝ (Fin n)) {M : ℝ} (hz : ∀ i, ‖z i‖ ≤ M) :
    ‖mean z w‖ ≤ M := by
  calc
    ‖mean z w‖ ≤ ∑ i, ‖w.weights i • z i‖ := norm_sum_le _ _
    _ = ∑ i, w.weights i * ‖z i‖ := by
      congr 1; ext i; rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (w.weights_nonneg i)]
    _ ≤ ∑ i, w.weights i * M := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hz i) (w.weights_nonneg i)
    _ = M := by rw [← Finset.sum_mul, w.total_of_fintype, one_mul]

lemma weights_distance_sq_le (w v : StdSimplex ℝ (Fin n)) :
    ∑ i, (w.weights i - v.weights i) ^ 2 ≤ 2 := by
  have h (i : Fin n) : (w.weights i - v.weights i) ^ 2 ≤ w.weights i + v.weights i := by
    have hw := w.weights_nonneg i
    have hv := v.weights_nonneg i
    have hw1 := w.weights_apply_le_one i
    have hv1 := v.weights_apply_le_one i
    nlinarith [mul_nonneg hw hv, mul_nonneg hw (sub_nonneg.mpr hw1),
      mul_nonneg hv (sub_nonneg.mpr hv1)]
  calc
    _ ≤ ∑ i, (w.weights i + v.weights i) := Finset.sum_le_sum fun i _ => h i
    _ = 2 := by rw [Finset.sum_add_distrib, w.total_of_fintype, v.total_of_fintype]; norm_num

lemma couple_radius {A α R : ℝ} {x0 y v : E} (hA : 0 ≤ A) (hα : 0 ≤ α)
    (hB : 0 < A + α) (hy : ‖y - x0‖ ≤ R) (hv : ‖v - x0‖ ≤ R) :
    ‖couple A α y v - x0‖ ≤ R := by
  have ha : 0 ≤ A / (A + α) := div_nonneg hA hB.le
  have hb : 0 ≤ α / (A + α) := div_nonneg hα hB.le
  have hab : A / (A + α) + α / (A + α) = 1 := by
    rw [← add_div, div_self hB.ne']
  have he : couple A α y v - x0 =
      (A / (A + α)) • (y - x0) + (α / (A + α)) • (v - x0) := by
    unfold couple
    rw [smul_sub, smul_sub]
    have hh : (A / (A + α)) • x0 + (α / (A + α)) • x0 = x0 := by
      rw [← add_smul, hab, one_smul]
    conv_lhs => rw [← hh]
    abel
  rw [he]
  calc
    _ ≤ ‖(A / (A + α)) • (y - x0)‖ + ‖(α / (A + α)) • (v - x0)‖ := norm_add_le _ _
    _ = (A / (A + α)) * ‖y - x0‖ + (α / (A + α)) * ‖v - x0‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ (A / (A + α)) * R + (α / (A + α)) * R :=
      add_le_add (mul_le_mul_of_nonneg_left hy ha) (mul_le_mul_of_nonneg_left hv hb)
    _ = R := by rw [← add_mul, hab, one_mul]

lemma couple_sub_left {A α : ℝ} (hB : A + α ≠ 0) (y v : E) :
    couple A α y v - y = (α / (A + α)) • (v - y) := by
  have hab : A / (A + α) = 1 - α / (A + α) := by
    have hh : A / (A + α) + α / (A + α) = 1 := by
      rw [← add_div, div_self hB]
    linarith
  rw [couple, hab, sub_smul, one_smul, smul_sub]
  abel

lemma couple_sub_couple (A α : ℝ) (y v w : E) :
    couple A α y v - couple A α y w = (α / (A + α)) • (v - w) := by
  unfold couple
  rw [smul_sub]
  abel

omit [InnerProductSpace ℝ E] in
lemma ball_pair_distance {x0 v w : E} {R : ℝ}
    (hv : ‖v - x0‖ ≤ R) (hw : ‖w - x0‖ ≤ R) : ‖v - w‖ ≤ 2 * R := by
  have he : v - w = (v - x0) - (w - x0) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

lemma couple_move_le {A α R : ℝ} {x0 y v : E} (hα : 0 ≤ α) (hB : 0 < A + α)
    (hy : ‖y - x0‖ ≤ R) (hv : ‖v - x0‖ ≤ R) :
    ‖couple A α y v - y‖ ≤ α / (A + α) * (2 * R) := by
  rw [couple_sub_left hB.ne', norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hα hB.le)]
  exact mul_le_mul_of_nonneg_left (ball_pair_distance hv hy) (div_nonneg hα hB.le)

lemma couple_pair_move_le {A α R : ℝ} {x0 y v w : E}
    (hα : 0 ≤ α) (hB : 0 < A + α)
    (hv : ‖v - x0‖ ≤ R) (hw : ‖w - x0‖ ≤ R) :
    ‖couple A α y v - couple A α y w‖ ≤ α / (A + α) * (2 * R) := by
  rw [couple_sub_couple, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hα hB.le)]
  exact mul_le_mul_of_nonneg_left (ball_pair_distance hv hw) (div_nonneg hα hB.le)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma divergence_single (i j : Fin n) :
    divergence z (StdSimplex.single i) (StdSimplex.single j) = ‖z i - z j‖ ^ 2 / 2 := by
  simp only [divergence, mixture_single, density]
  exact CovarianceAcceleratedTilt.gaussian_density_kl _ _

lemma potential_nonneg (w v : StdSimplex ℝ (Fin n)) {a β γ M : ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hM : 0 ≤ M) (hz : ∀ i, ‖z i‖ ≤ M) :
    0 ≤ potential z a β γ w v := by
  unfold potential
  exact add_nonneg (add_nonneg (divergence_nonneg z w v hM hz) (by positivity))
    (by positivity)

lemma initial_potential_le (i j : Fin n) {a β γ M : ℝ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hM : 0 ≤ M) (hj : z j = 0)
    (hi : ‖z i‖ ≤ M) :
    potential z a β γ (StdSimplex.single i) (StdSimplex.single j) ≤
      M ^ 2 / 2 + β * a ^ 2 / 2 * M ^ 2 + γ := by
  have hs : ‖z i‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (z i)]
  have hw := weights_distance_sq_le (StdSimplex.single i) (StdSimplex.single j)
  have hc : 0 ≤ β * a ^ 2 / 2 := by positivity
  have hd := mul_le_mul_of_nonneg_left hw (show 0 ≤ γ / 2 by positivity)
  have he := mul_le_mul_of_nonneg_left hs hc
  simp only [potential, divergence_single, mean_single, hj, sub_zero]
  nlinarith

omit [MeasurableSpace E] [BorelSpace E] in
lemma finite_ball_net {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ S : Finset E, 0 ∈ S ∧ (∀ z ∈ S, ‖z‖ ≤ R) ∧
      ∀ x : E, ‖x‖ ≤ R → ∃ z ∈ S, ‖x - z‖ ≤ ε := by
  classical
  obtain ⟨S, hsub, hfin, hcover⟩ := (isCompact_closedBall (0 : E) R).finite_cover_balls hε
  refine ⟨insert 0 hfin.toFinset, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simpa using hR
    · simpa using hsub (hfin.mem_toFinset.mp hz)
  · intro x hx
    have hx' : x ∈ Metric.closedBall (0 : E) R := by simpa using hx
    obtain ⟨z, hz, hd⟩ := Set.mem_iUnion₂.mp (hcover hx')
    have hd' : ‖x - z‖ < ε := by simpa only [Metric.mem_ball, dist_eq_norm] using hd
    exact ⟨z, Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hz), hd'.le⟩

end LongTails.Proofs.CovarianceAcceleratedGeometry
