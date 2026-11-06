import LongTails.Proofs.RecoveryFractalSchedule
import LongTails.Proofs.GdSnapshotDynamics
import LongTails.Proofs.AdaptiveSilverDynamics
import LongTails.Proofs.ScheduleBlockVector

namespace LongTails.Proofs.RecoveryFractalLocal

open OracleTemplate OracleTemplate.ScheduleBlock
open LongTails.Setups.SmoothHessianLipschitzGd
open LongTails.Algorithms.RecoveryFractalGd
open LongTails.Proofs.RecoveryFractalExecution
open LongTails.Proofs.RecoveryFractalSchedule
open LongTails.Proofs.GdSnapshotDynamics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma travel_bound (g : E → E) (a : ℕ → ℝ) (X : ℕ → E) (G : ℝ) (n : ℕ)
    (ha : ∀ i < n, 0 ≤ a i)
    (hstep : ∀ i < n, X (i + 1) = X i - a i • g (X i))
    (hg : ∀ i < n, ‖g (X i)‖ ≤ G) :
    ‖X n - X 0‖ ≤ ssum a n * G := by
  induction n with
  | zero => simp [ssum]
  | succ n ih =>
    have hi := ih (fun i hi => ha i (by omega)) (fun i hi => hstep i (by omega))
      (fun i hi => hg i (by omega))
    rw [hstep n (by omega), ssum_succ]
    have he : X n - a n • g (X n) - X 0 = (X n - X 0) - a n • g (X n) := by abel
    rw [he]
    calc
      _ ≤ ‖X n - X 0‖ + ‖a n • g (X n)‖ := norm_sub_le _ _
      _ ≤ ssum a n * G + a n * G := by
        apply add_le_add hi
        rw [norm_smul, Real.norm_of_nonneg (ha n (by omega))]
        exact mul_le_mul_of_nonneg_left (hg n (by omega)) (ha n (by omega))
      _ = _ := by ring

lemma trial_step_sum (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p)
    (t : ℕ) (ht : t ≤ 2 * epochLength p) :
    ssum (fractalStep p) t ≤ 2 * repetitions p / lowerCurvature p := by
  have hs : ssum (fractalStep p) t ≤ ssum (fractalStep p) (2 * epochLength p) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono ht)
    intro i _ _
    exact (fractalStep_pos p hL hk i).le
  have he : 2 * epochLength p = blockLength p * (2 * repetitions p) := by
    unfold epochLength
    ring
  rw [he, repeated_sum] at hs
  have hb := (actual_base_sum_bounds p hL hk).2
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 2 * repetitions p)
  push_cast at hs
  calc
    _ ≤ (2 * repetitions p) * ssum (fractalStep p) (blockLength p) := hs
    _ ≤ (2 * repetitions p) * (1 / lowerCurvature p) := hh
    _ = _ := by ring

lemma trial_radius (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p) (hG : 0 ≤ threshold p)
    (f : p.E → ℝ) (X : ℕ → p.E) (t : ℕ) (ht : t ≤ 2 * epochLength p)
    (hstep : ∀ i < t, X (i + 1) = X i - fractalStep p i • gradient f (X i))
    (hg : ∀ i < t, ‖gradient f (X i)‖ ≤ 8 * threshold p) :
    ‖X t - X 0‖ ≤ radius p / 2 := by
  have htravel := travel_bound (gradient f) (fractalStep p) X (8 * threshold p) t
    (fun i _ => (fractalStep_pos p hL hk i).le) hstep hg
  have hs := trial_step_sum p hL hk t ht
  calc
    _ ≤ ssum (fractalStep p) t * (8 * threshold p) := htravel
    _ ≤ (2 * repetitions p / lowerCurvature p) * (8 * threshold p) :=
      mul_le_mul_of_nonneg_right hs (by positivity)
    _ = radius p / 2 := by unfold radius; ring

noncomputable def forcing (g : E → E) (H : E →L[ℝ] E) (a : ℕ → ℝ)
    (X : ℕ → E) (i : ℕ) : E :=
  (a i)⁻¹ • (g (X (i + 1)) - (g (X i) - a i • H (g (X i))))

lemma forcing_recurrence (g : E → E) (H : E →L[ℝ] E) (a : ℕ → ℝ)
    (X : ℕ → E) (i : ℕ) (ha : a i ≠ 0) :
    g (X (i + 1)) = g (X i) - a i • H (g (X i)) + a i • forcing g H a X i := by
  simp only [forcing, smul_smul, mul_inv_cancel₀ ha, one_smul]
  abel

lemma forcing_bound {g : E → E} {ρ R G : ℝ} (hρ : 0 ≤ ρ) (hR : 0 ≤ R)
    (hg : Differentiable ℝ g)
    (hH : ∀ x y, ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤ ρ * ‖x - y‖)
    (a : ℕ → ℝ) (X : ℕ → E) (z : E) (i : ℕ) (ha : 0 < a i)
    (hstep : X (i + 1) = X i - a i • g (X i))
    (hx : ‖X i - z‖ ≤ R) (hy : ‖X (i + 1) - z‖ ≤ R) (hG : ‖g (X i)‖ ≤ G) :
    ‖forcing g (fderiv ℝ g z) a X i‖ ≤ ρ * R * G := by
  have hb := gd_gradient_forcing hρ ha.le hg hH z (X i) hx (hstep ▸ hy)
  rw [← hstep] at hb
  unfold forcing
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
  calc
    _ ≤ (a i)⁻¹ * (a i * ρ * R * ‖g (X i)‖) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ha.le)
    _ = ρ * R * ‖g (X i)‖ := by field_simp
    _ ≤ ρ * R * G := mul_le_mul_of_nonneg_left hG (mul_nonneg hρ hR)

open scoped RealInnerProductSpace
open LongTails.Proofs.AdaptiveSilverSplit

lemma positive_forcing_error (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ p.E) (eig : ι → ℝ) (H : p.E →L[ℝ] p.E)
    (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫) (heig : ∀ j, eig j ≤ p.L)
    (u v : ℕ → p.E) (t : ℕ)
    (hu : ∀ i < t, u (i + 1) = u i - fractalStep p i • H (u i) + fractalStep p i • v i)
    (B : ℝ) (hB : 0 ≤ B) (hv : ∀ i < t, ‖v i‖ ≤ B) :
    ‖P b eig (u t) - proj b (fun j => cpos eig j * pr (fractalStep p) (eig j) t) (u 0)‖ ≤
      (t : ℝ) * (4 / lowerCurvature p) * B := by
  let lam := fun j => max (eig j) 0
  let U := fun i j => ⟪b j, P b eig (u i)⟫
  let V := fun i j => ⟪b j, P b eig (v i)⟫
  have hrec (i : ℕ) (hi : i < t) (j : ι) :
      U (i + 1) j = (1 - fractalStep p i * lam j) * U i j + fractalStep p i * V i j := by
    dsimp [U, V, lam]
    simp only [P_coord', hu i hi, inner_add_right, inner_sub_right, inner_smul_right, hc]
    by_cases hj : 0 ≤ eig j
    · simp only [cpos, hj, ite_true, one_mul, max_eq_left hj]
      ring
    · simp [cpos, hj]
  have hw (i : ℕ) (hi : i < t) (j : ι) :
      |fractalStep p i * win (fractalStep p) (lam j) (i + 1) t| ≤ 4 / lowerCurvature p := by
    rw [abs_mul, abs_of_nonneg (fractalStep_pos p hL hk i).le]
    exact all_weighted_window_bound p hL hk (le_max_right _ _)
      (max_le (heig j) hL.le) hi
  have hv' (i : ℕ) (hi : i < t) : ∑ j, V i j ^ 2 ≤ B ^ 2 := by
    change (∑ j, ⟪b j, P b eig (v i)⟫ ^ 2) ≤ B ^ 2
    rw [← norm_sq_coords b]
    exact pow_le_pow_left₀ (norm_nonneg _) ((P_norm_le b eig _).trans (hv i hi)) 2
  have hh := forced_coordinate_square_error (fractalStep p) lam U V t hrec
    (4 / lowerCurvature p) B hw hv'
  have he : ‖P b eig (u t) -
      proj b (fun j => cpos eig j * pr (fractalStep p) (eig j) t) (u 0)‖ ^ 2 =
      ∑ j, (U t j - pr (fractalStep p) (lam j) t * U 0 j) ^ 2 := by
    rw [norm_sq_coords b]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [U, lam]
    simp only [inner_sub_right, P_coord', proj_coord]
    by_cases hj : 0 ≤ eig j
    · simp [cpos, hj]
    · simp [cpos, hj]
  have hmu := lowerCurvature_pos p hL
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (t : ℝ) * (4 / lowerCurvature p) * B)).mp
  rw [he]
  simpa only [mul_pow] using hh

lemma positive_filter_bound (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ p.E) (eig : ι → ℝ) (heig : ∀ j, eig j ≤ p.L)
    (t : ℕ) (u : p.E) :
    ‖proj b (fun j => cpos eig j * pr (fractalStep p) (eig j) t) u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_coords b, norm_sq_coords b]
  apply Finset.sum_le_sum
  intro j _
  rw [proj_coord, mul_pow]
  have hc : |cpos eig j * pr (fractalStep p) (eig j) t| ≤ 1 := by
    by_cases hj : 0 ≤ eig j
    · simpa [cpos, hj] using all_prefix_bound p hL hk hj (heig j) t
    · simp [cpos, hj]
  have hc2 := pow_le_pow_left₀ (abs_nonneg _) hc 2
  simp only [sq_abs, one_pow] at hc2
  nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg ⟪b j, u⟫)]

lemma trial_positive_filter_error (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hk : 2 ≤ level p) (hG : 0 ≤ threshold p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ p.E) (eig : ι → ℝ) (X : ℕ → p.E)
    (hc : ∀ j v, ⟪b j, fderiv ℝ (gradient f) (X 0) v⟫ = eig j * ⟪b j, v⟫)
    (heig : ∀ j, eig j ≤ p.L) (t : ℕ) (ht : t ≤ 2 * epochLength p)
    (hstep : ∀ i < t, X (i + 1) = X i - fractalStep p i • gradient f (X i))
    (hg : ∀ i < t, ‖gradient f (X i)‖ ≤ 8 * threshold p) :
    ‖P b eig (gradient f (X t)) -
      proj b (fun j => cpos eig j * pr (fractalStep p) (eig j) t) (gradient f (X 0))‖ ≤
      (t : ℝ) * (4 / lowerCurvature p) * (p.ρ * radius p * (8 * threshold p)) := by
  have hmu := lowerCurvature_pos p hL
  have hR : 0 ≤ radius p := by unfold radius; positivity
  have hr (i : ℕ) (hi : i ≤ t) : ‖X i - X 0‖ ≤ radius p := by
    have hh := trial_radius p hL hk hG f X i (hi.trans ht)
      (fun j hj => hstep j (hj.trans_le hi)) (fun j hj => hg j (hj.trans_le hi))
    linarith
  let H := fderiv ℝ (gradient f) (X 0)
  let v := forcing (gradient f) H (fractalStep p) X
  have hgd : Differentiable ℝ (gradient f) :=
    (OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hf).differentiable
      (by norm_num)
  have hv (i : ℕ) (hi : i < t) : ‖v i‖ ≤ p.ρ * radius p * (8 * threshold p) := by
    exact forcing_bound hρ hR hgd hH (fractalStep p) X (X 0) i
      (fractalStep_pos p hL hk i) (hstep i hi) (hr i hi.le) (hr (i + 1) (by omega)) (hg i hi)
  have hh := positive_forcing_error p hL hk b eig H hc heig
    (fun i => gradient f (X i)) v t
    (fun i _ => forcing_recurrence (gradient f) H (fractalStep p) X i
      (fractalStep_pos p hL hk i).ne')
    (p.ρ * radius p * (8 * threshold p)) (by positivity) hv
  exact hh

lemma trial_positive_gradient (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hk : 2 ≤ level p) (hG : 0 ≤ threshold p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ p.E) (eig : ι → ℝ) (X : ℕ → p.E)
    (hc : ∀ j v, ⟪b j, fderiv ℝ (gradient f) (X 0) v⟫ = eig j * ⟪b j, v⟫)
    (heig : ∀ j, eig j ≤ p.L) (t : ℕ) (ht : t ≤ 2 * epochLength p)
    (hstep : ∀ i < t, X (i + 1) = X i - fractalStep p i • gradient f (X i))
    (hg : ∀ i < t, ‖gradient f (X i)‖ ≤ 8 * threshold p) :
    ‖P b eig (gradient f (X t))‖ ≤ ‖gradient f (X 0)‖ +
      (t : ℝ) * (4 / lowerCurvature p) * (p.ρ * radius p * (8 * threshold p)) := by
  have hh := trial_positive_filter_error p hL hρ hk hG f hf hH b eig X hc heig t ht hstep hg
  have hp := positive_filter_bound p hL hk b eig heig t (gradient f (X 0))
  have hn := norm_le_norm_sub_add (P b eig (gradient f (X t)))
    (proj b (fun j => cpos eig j * pr (fractalStep p) (eig j) t) (gradient f (X 0)))
  linarith

open LongTails.Proofs.AdaptiveSilverDynamics

lemma positive_energy_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E)
    (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫) (g d e : E) :
    phiPart b eig H g d ≤ phiPart b eig H g e +
      (‖P b eig (g + H d)‖ + ‖P b eig (g + H e)‖) / 2 * ‖P b eig (d - e)‖ := by
  let δ := P b eig (d - e)
  let v := P b eig e
  have hd : P b eig d = v + δ := by dsimp [v, δ]; rw [map_sub]; abel
  have hδ : P b eig δ = δ := P_idem b eig (d - e)
  have hge : P b eig (g + H e) = P b eig g + H v := by
    rw [map_add, ← P_comm b eig H hc]
  have hgd : P b eig (g + H d) = P b eig (g + H e) + H δ := by
    rw [map_add, ← P_comm b eig H hc, hd, map_add, hge]
    abel
  have hlin : ⟪g, δ⟫ + ⟪δ, H v⟫ = ⟪δ, P b eig (g + H e)⟫ := by
    rw [hge, inner_add_right, ← P_symm b eig δ g, hδ, real_inner_comm δ g]
  have hcross : ⟪v, H δ⟫ = ⟪δ, H v⟫ := by
    rw [← hsym v δ]
    exact real_inner_comm _ _
  have heq : phiPart b eig H g d - phiPart b eig H g e =
      ⟪δ, P b eig (g + H d) + P b eig (g + H e)⟫ / 2 := by
    unfold phiPart
    rw [hd]
    change (⟪g, v + δ⟫ + ⟪v + δ, H (v + δ)⟫ / 2) -
      (⟪g, v⟫ + ⟪v, H v⟫ / 2) = _
    rw [hgd, map_add]
    simp only [inner_add_left, inner_add_right]
    rw [hcross]
    linarith [hlin]
  have hn := norm_add_le (P b eig (g + H d)) (P b eig (g + H e))
  have hi := real_inner_le_norm δ (P b eig (g + H d) + P b eig (g + H e))
  have hh := mul_le_mul_of_nonneg_left hn (norm_nonneg δ)
  change phiPart b eig H g d ≤ phiPart b eig H g e +
    (‖P b eig (g + H d)‖ + ‖P b eig (g + H e)‖) / 2 * ‖δ‖
  nlinarith [heq]

noncomputable def idealDisplacement {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (a : ℕ → ℝ) (g : E) (t : ℕ) : E :=
  proj b (fun j => -resp a (eig j) t) g

lemma idealDisplacement_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (a : ℕ → ℝ) (g : E) :
    idealDisplacement b eig a g 0 = 0 := by
  apply eq_of_coords b
  intro j
  simp [idealDisplacement, proj_coord, resp]

lemma idealDisplacement_succ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E)
    (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (a : ℕ → ℝ) (g : E) (t : ℕ) :
    idealDisplacement b eig a g (t + 1) = idealDisplacement b eig a g t -
      a t • (g + H (idealDisplacement b eig a g t)) := by
  apply eq_of_coords b
  intro j
  simp only [idealDisplacement, proj_coord, inner_sub_right, inner_smul_right,
    inner_add_right, hc, resp_succ]
  ring

lemma ideal_positive_gradient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E)
    (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (a : ℕ → ℝ) (g : E) (t : ℕ) :
    P b eig (g + H (idealDisplacement b eig a g t)) =
      proj b (fun j => cpos eig j * pr a (eig j) t) g := by
  apply eq_of_coords b
  intro j
  simp only [P_coord', inner_add_right, hc, idealDisplacement, proj_coord]
  have hh := lam_mul_resp a (eig j) t
  linear_combination -(cpos eig j * ⟪b j, g⟫) * hh

lemma ideal_scalar_energy {a : ℕ → ℝ} {lam : ℝ} (hl : 0 ≤ lam) (t : ℕ)
    (ha : ∀ i < t, 0 ≤ a i) (hp : |pr a lam t| ≤ 1) :
    -resp a lam t + lam * resp a lam t ^ 2 / 2 ≤ 0 := by
  rcases eq_or_lt_of_le hl with he | hl
  · rw [← he, resp_zero]
    have hs : 0 ≤ ssum a t := Finset.sum_nonneg (fun i hi => ha i (Finset.mem_range.mp hi))
    nlinarith
  · have hh := lam_mul_resp a lam t
    have hs := congrArg (fun x : ℝ => x ^ 2) hh
    have hp2 : pr a lam t ^ 2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hp 2
      simpa using h
    have heq : 2 * lam * (-resp a lam t + lam * resp a lam t ^ 2 / 2) = pr a lam t ^ 2 - 1 := by
      nlinarith [hs]
    nlinarith

lemma ideal_positive_energy (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ p.E) (eig : ι → ℝ) (H : p.E →L[ℝ] p.E)
    (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫) (heig : ∀ j, eig j ≤ p.L)
    (g : p.E) (t : ℕ) :
    phiPart b eig H g (idealDisplacement b eig (fractalStep p) g t) ≤ 0 := by
  unfold phiPart
  rw [inner_coords b, inner_coords b, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_nonpos
  intro j _
  simp only [P_coord', hc, idealDisplacement, proj_coord]
  by_cases hj : 0 ≤ eig j
  · simp only [cpos, hj, ite_true, one_mul]
    have hh := ideal_scalar_energy hj t (fun i _ => (fractalStep_pos p hL hk i).le)
      (all_prefix_bound p hL hk hj (heig j) t)
    have h := mul_nonpos_of_nonpos_of_nonneg hh (sq_nonneg ⟪b j, g⟫)
    nlinarith [h]
  · simp [cpos, hj]

lemma trial_residual_bound (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hk : 2 ≤ level p) (hG : 0 ≤ threshold p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (X : ℕ → p.E) (t : ℕ) (ht : t ≤ 2 * epochLength p)
    (hstep : ∀ i < t, X (i + 1) = X i - fractalStep p i • gradient f (X i))
    (hg : ∀ i < t, ‖gradient f (X i)‖ ≤ 8 * threshold p) :
    ‖gradient f (X t) - gradient f (X 0) - fderiv ℝ (gradient f) (X 0) (X t - X 0)‖ ≤
      errorBound p := by
  have hmu := lowerCurvature_pos p hL
  have hR : 0 ≤ radius p := by unfold radius; positivity
  have hr : ‖X t - X 0‖ ≤ radius p := by
    have hh := trial_radius p hL hk hG f X t ht hstep hg
    linarith
  have hgd : Differentiable ℝ (gradient f) :=
    (OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hf).differentiable
      (by norm_num)
  exact (OracleTemplate.NonlinearTemporalDiscrepancy.gradient_linearization_bound
    hρ hgd hH (X 0) (X t)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr 2) hρ)

lemma trial_positive_displacement_error (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hk : 2 ≤ level p) (hG : 0 ≤ threshold p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ p.E) (eig : ι → ℝ) (X : ℕ → p.E)
    (hc : ∀ j v, ⟪b j, fderiv ℝ (gradient f) (X 0) v⟫ = eig j * ⟪b j, v⟫)
    (heig : ∀ j, eig j ≤ p.L) (t : ℕ) (ht : t ≤ 2 * epochLength p)
    (hstep : ∀ i < t, X (i + 1) = X i - fractalStep p i • gradient f (X i))
    (hg : ∀ i < t, ‖gradient f (X i)‖ ≤ 8 * threshold p) :
    ‖P b eig (X t - X 0 - idealDisplacement b eig (fractalStep p) (gradient f (X 0)) t)‖ ≤
      (t : ℝ) * (4 / lowerCurvature p) * errorBound p := by
  let H := fderiv ℝ (gradient f) (X 0)
  let Y := idealDisplacement b eig (fractalStep p) (gradient f (X 0))
  let u := fun i => X i - X 0 - Y i
  let e := fun i => gradient f (X i) - gradient f (X 0) - H (X i - X 0)
  have he (i : ℕ) (hi : i < t) : ‖-e i‖ ≤ errorBound p := by
    rw [norm_neg]
    exact trial_residual_bound p hL hρ hk hG f hf hH X i (hi.le.trans ht)
      (fun j hj => hstep j (hj.trans hi)) (fun j hj => hg j (hj.trans hi))
  have hu (i : ℕ) (hi : i < t) :
      u (i + 1) = u i - fractalStep p i • H (u i) + fractalStep p i • (-e i) := by
    dsimp [u, e, Y]
    rw [hstep i hi, idealDisplacement_succ b eig H hc]
    simp only [map_sub]
    module
  have hB : 0 ≤ errorBound p := by unfold errorBound; positivity
  have hh := positive_forcing_error p hL hk b eig H hc heig u (fun i => -e i) t hu
    (errorBound p) hB he
  have hu0 : u 0 = 0 := by simp [u, Y, idealDisplacement_zero]
  rw [hu0, map_zero, sub_zero] at hh
  exact hh

lemma negative_energy_upper {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ) (H : E →L[ℝ] E)
    (hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫)
    (hsym : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫)
    (a : ℕ → ℝ) (g : E) (d e : ℕ → E) (n : ℕ) (B : ℝ)
    (h0 : d 0 = 0) (ha : ∀ i < n, 0 ≤ a i)
    (hd : ∀ i < n, d (i + 1) = d i - a i • (g + H (d i) + e i))
    (he : ∀ i < n, ‖e i‖ ≤ B) :
    psiPart b eig H g (d n) ≤ ssum a n * B ^ 2 / 2 := by
  induction n with
  | zero => simp [h0, psiPart, ssum]
  | succ n ih =>
    have hi := ih (fun i hi => ha i (by omega)) (fun i hi => hd i (by omega))
      (fun i hi => he i (by omega))
    have hp := psi_step b eig H hc hsym g (d n) (e n) (ha n (by omega))
    have hn := pow_le_pow_left₀ (norm_nonneg _) (he n (by omega)) 2
    have hm := mul_le_mul_of_nonneg_left hn (show 0 ≤ a n / 2 from div_nonneg (ha n (by omega)) (by norm_num))
    rw [hd n (by omega), ssum_succ]
    nlinarith [mul_nonneg (ha n (by omega))
      (sq_nonneg ‖(g + H (d n)) - P b eig (g + H (d n))‖)]

lemma trial_positive_model (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hk : 2 ≤ level p) (hG : 0 ≤ threshold p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ p.E) (eig : ι → ℝ) (X : ℕ → p.E)
    (hc : ∀ j v, ⟪b j, fderiv ℝ (gradient f) (X 0) v⟫ = eig j * ⟪b j, v⟫)
    (heig : ∀ j, eig j ≤ p.L) (t : ℕ) (ht : t ≤ 2 * epochLength p)
    (hstep : ∀ i < t, X (i + 1) = X i - fractalStep p i • gradient f (X i))
    (hg : ∀ i < t, ‖gradient f (X i)‖ ≤ 8 * threshold p)
    (h0 : ‖gradient f (X 0)‖ ≤ threshold p)
    (hsmall : (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
      (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ threshold p) :
    ‖P b eig (gradient f (X 0) + fderiv ℝ (gradient f) (X 0) (X t - X 0))‖ ≤
      2 * threshold p := by
  let H := fderiv ℝ (gradient f) (X 0)
  have hmu := lowerCurvature_pos p hL
  have hR : 0 ≤ radius p := by unfold radius; positivity
  have ht' : (t : ℝ) ≤ 2 * epochLength p := by exact_mod_cast ht
  have herr := trial_residual_bound p hL hρ hk hG f hf hH X t ht hstep hg
  have hgrad := trial_positive_gradient p hL hρ hk hG f hf hH b eig X hc heig t ht hstep hg
  have he : P b eig (gradient f (X 0) + H (X t - X 0)) =
      P b eig (gradient f (X t)) -
        P b eig (gradient f (X t) - gradient f (X 0) - H (X t - X 0)) := by
    simp only [map_add, map_sub]
    abel
  change ‖P b eig (gradient f (X 0) + H (X t - X 0))‖ ≤ _
  rw [he]
  have hn := norm_sub_le (P b eig (gradient f (X t)))
    (P b eig (gradient f (X t) - gradient f (X 0) - H (X t - X 0)))
  have hp := (P_norm_le b eig _).trans herr
  have hd := mul_le_mul_of_nonneg_right ht'
    (show 0 ≤ (4 / lowerCurvature p) * (p.ρ * radius p * (8 * threshold p)) by positivity)
  nlinarith

lemma trial_prefix_increase (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ)
    (hk : 2 ≤ level p) (hG : 0 ≤ threshold p)
    (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (X : ℕ → p.E) (t : ℕ) (ht : t ≤ 2 * epochLength p)
    (hstep : ∀ i < t, X (i + 1) = X i - fractalStep p i • gradient f (X i))
    (hg : ∀ i < t, ‖gradient f (X i)‖ ≤ 8 * threshold p)
    (h0 : ‖gradient f (X 0)‖ ≤ threshold p)
    (hsmall : (2 * epochLength p : ℝ) * (4 / lowerCurvature p) *
      (p.ρ * radius p * (8 * threshold p)) + errorBound p ≤ threshold p) :
    f (X t) - f (X 0) ≤ prefixIncrease p := by
  classical
  let H := fderiv ℝ (gradient f) (X 0)
  have hsym := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf (X 0)
  let b := hsym.eigenvectorBasis rfl
  let eig := hsym.eigenvalues rfl
  have hc : ∀ j v, ⟪b j, H v⟫ = eig j * ⟪b j, v⟫ := by
    intro j v
    simpa only [OrthonormalBasis.repr_apply_apply, RCLike.ofReal_real_eq_id, id_eq,
      ContinuousLinearMap.coe_coe] using
      hsym.eigenvectorBasis_apply_self_apply rfl v j
  have heig : ∀ j, eig j ≤ p.L := fun j => (eig_bounds hL.le hlip (X 0) hsym j).2
  have hsym' : ∀ u v, ⟪H u, v⟫ = ⟪u, H v⟫ := fun u v => hsym u v
  have hmu := lowerCurvature_pos p hL
  have hR : 0 ≤ radius p := by unfold radius; positivity
  have hE : 0 ≤ errorBound p := by unfold errorBound; positivity
  have ht' : (t : ℝ) ≤ 2 * epochLength p := by exact_mod_cast ht
  have hmodel := trial_positive_model p hL hρ hk hG f hf hH b eig X hc heig t ht hstep hg h0 hsmall
  let y := idealDisplacement b eig (fractalStep p) (gradient f (X 0)) t
  have hideal : ‖P b eig (gradient f (X 0) + H y)‖ ≤ threshold p := by
    dsimp [y]
    rw [ideal_positive_gradient b eig H hc]
    exact (positive_filter_bound p hL hk b eig heig t _).trans h0
  have hdiff := trial_positive_displacement_error p hL hρ hk hG f hf hH b eig X hc heig t ht hstep hg
  have hphi := positive_energy_difference b eig H hc hsym' (gradient f (X 0)) (X t - X 0) y
  have hiy := ideal_positive_energy p hL hk b eig H hc heig (gradient f (X 0)) t
  have hpos : phiPart b eig H (gradient f (X 0)) (X t - X 0) ≤
      12 * epochLength p * threshold p * errorBound p / lowerCurvature p := by
    have h1 := mul_le_mul_of_nonneg_right
      (show (‖P b eig (gradient f (X 0) + H (X t - X 0))‖ +
        ‖P b eig (gradient f (X 0) + H y)‖) / 2 ≤ 3 * threshold p / 2 by linarith)
      (norm_nonneg (P b eig (X t - X 0 - y)))
    have h2 := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 3 * threshold p / 2 by positivity)
    have h3 := mul_le_mul_of_nonneg_right ht'
      (show 0 ≤ 6 * threshold p * errorBound p / lowerCurvature p by positivity)
    calc
      _ ≤ phiPart b eig H (gradient f (X 0)) y +
          (‖P b eig (gradient f (X 0) + H (X t - X 0))‖ +
            ‖P b eig (gradient f (X 0) + H y)‖) / 2 * ‖P b eig (X t - X 0 - y)‖ := hphi
      _ ≤ (‖P b eig (gradient f (X 0) + H (X t - X 0))‖ +
            ‖P b eig (gradient f (X 0) + H y)‖) / 2 * ‖P b eig (X t - X 0 - y)‖ := by linarith [hiy]
      _ ≤ 3 * threshold p / 2 * ‖P b eig (X t - X 0 - y)‖ := h1
      _ ≤ 3 * threshold p / 2 * ((t : ℝ) * (4 / lowerCurvature p) * errorBound p) := h2
      _ = (t : ℝ) * (6 * threshold p * errorBound p / lowerCurvature p) := by ring
      _ ≤ (2 * epochLength p) * (6 * threshold p * errorBound p / lowerCurvature p) := h3
      _ = _ := by ring
  let d := fun i => X i - X 0
  let e := fun i => gradient f (X i) - gradient f (X 0) - H (X i - X 0)
  have he (i : ℕ) (hi : i < t) : ‖e i‖ ≤ errorBound p :=
    trial_residual_bound p hL hρ hk hG f hf hH X i (hi.le.trans ht)
      (fun j hj => hstep j (hj.trans hi)) (fun j hj => hg j (hj.trans hi))
  have hd (i : ℕ) (hi : i < t) :
      d (i + 1) = d i - fractalStep p i • (gradient f (X 0) + H (d i) + e i) := by
    dsimp [d, e]
    rw [hstep i hi]
    module
  have hneg := negative_energy_upper b eig H hc hsym' (fractalStep p) (gradient f (X 0)) d e t
    (errorBound p) (by simp [d]) (fun i _ => (fractalStep_pos p hL hk i).le) hd he
  have hs := trial_step_sum p hL hk t ht
  have hn : psiPart b eig H (gradient f (X 0)) (X t - X 0) ≤
      repetitions p * errorBound p ^ 2 / lowerCurvature p := by
    have hh := mul_le_mul_of_nonneg_right hs (sq_nonneg (errorBound p))
    dsimp [d] at hneg
    calc
      _ ≤ ssum (fractalStep p) t * errorBound p ^ 2 / 2 := hneg
      _ ≤ (2 * repetitions p / lowerCurvature p * errorBound p ^ 2) / 2 :=
        div_le_div_of_nonneg_right hh (by norm_num)
      _ = _ := by ring
  have hTaylor := taylor_cubic hf hρ hH (X 0) (X t)
  have hr : ‖X t - X 0‖ ≤ radius p := by
    have hh := trial_radius p hL hk hG f X t ht hstep hg
    linarith
  have hrem := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr 3) hρ
  have hsplit := model_split b eig H hc (gradient f (X 0)) (X t - X 0)
  have hsymmetric := hsym' (X t - X 0) (X t - X 0)
  have hup := (abs_le.mp hTaylor).2
  change f (X t) - f (X 0) - ⟪gradient f (X 0), X t - X 0⟫ -
    ⟪H (X t - X 0), X t - X 0⟫ / 2 ≤ _ at hup
  rw [hsymmetric] at hup
  have htotal : f (X t) - f (X 0) ≤
      12 * epochLength p * threshold p * errorBound p / lowerCurvature p +
        repetitions p * errorBound p ^ 2 / lowerCurvature p + p.ρ * radius p ^ 3 := by
    linarith only [hup, hrem, hsplit, hpos, hn]
  unfold prefixIncrease
  have hterm : 0 ≤ epochLength p * threshold p * errorBound p / lowerCurvature p := by positivity
  have hterm2 : 0 ≤ repetitions p * errorBound p ^ 2 / lowerCurvature p := by positivity
  simp only [div_eq_mul_inv] at hterm hterm2 htotal ⊢
  nlinarith only [hterm, hterm2, htotal]


end LongTails.Proofs.RecoveryFractalLocal
