import LongTails.Proofs.SpectralGradientLinear
import LongTails.Proofs.SpectralGradientModel
import LongTails.Proofs.SpectralGradientExecution

open scoped RealInnerProductSpace

namespace OracleTemplate.SpectralGradient

open LongTails.Setups.MinimizerRegularHessian

lemma fit_fits (p : Params) (history : List p.E) (h : ∃ B, Fits p history B) :
    Fits p history (fit p history) := by
  classical
  simp only [fit, dite_eq_left h]
  exact Classical.choose_spec h

lemma spectralSteps_length (p : Params) (history : List p.E) :
    (spectralSteps p history).length = Module.finrank ℝ p.E := by
  simp [spectralSteps]

lemma fitted_eigenvalues (p : Params) (history : List p.E) (h : ∃ B, Fits p history B)
    (i : Fin (Module.finrank ℝ p.E)) :
    p.μ ≤ (fit p history).symmetric.eigenvalues rfl i ∧
      (fit p history).symmetric.eigenvalues rfl i ≤ p.L := by
  have hb := (fit_fits p history h).1
  exact TemporalDiscrepancy.spectral_eigenvalue_bounds (fit p history).map
    (fit p history).symmetric (fun x => (hb x).1) (fun x => (hb x).2) i

lemma spectralSteps_bounds (p : Params) (hμ : 0 < p.μ) (history : List p.E)
    (h : ∃ B, Fits p history B) (η : ℝ) (hη : η ∈ spectralSteps p history) :
    0 < η ∧ η ≤ 1 / p.μ := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hη
  have he := (fitted_eigenvalues p history h i).1
  exact ⟨one_div_pos.mpr (hμ.trans_le he), one_div_le_one_div_of_le hμ he⟩

lemma probeHistory_getD (p : Params) (g : p.E → p.E) (x : p.E) {n j : ℕ}
    (hj : j < n) : (probeHistory p g x n).getD j 0 = g (probePoint p g x j) := by
  simp [probeHistory, List.getD, hj]

lemma probe_lipschitz (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    {f : p.E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ (gradient f))
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) (x y : p.E) :
    ‖(y - (1 / (2 * p.L)) • gradient f y) - (x - (1 / (2 * p.L)) • gradient f x)‖ ≤
      (1 - p.μ / (2 * p.L)) * ‖y - x‖ := by
  have hL : 0 < p.L := hμ.trans_le hμL
  have hρ : 0 ≤ 1 - p.μ / (2 * p.L) := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).mpr
    linarith
  apply step_lipschitz hρ hg
  intro z v
  exact probe_step_bound _ (hessian_symmetric hf hg z) hμ hμL
    (NonlinearTemporalDiscrepancy.hessian_lower_bound hg hs z)
    (NonlinearTemporalDiscrepancy.hessian_upper_bound hL.le hlip z) v

lemma probe_gradient_rate (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    {f : p.E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ (gradient f))
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) (x : p.E) (n : ℕ) :
    ‖gradient f (probePoint p (gradient f) x n)‖ ≤
      (1 - p.μ / (2 * p.L)) ^ n * ‖gradient f x‖ := by
  have hL : 0 < p.L := hμ.trans_le hμL
  have hρ : 0 ≤ 1 - p.μ / (2 * p.L) := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).mpr
    linarith
  induction n with
  | zero => simp [probePoint]
  | succ n ih =>
    rw [probePoint_succ]
    calc
      _ ≤ (1 - p.μ / (2 * p.L)) * ‖gradient f (probePoint p (gradient f) x n)‖ :=
        step_gradient_contract (by positivity) (probe_lipschitz p hμ hμL hf hg hs hlip) _
      _ ≤ (1 - p.μ / (2 * p.L)) * ((1 - p.μ / (2 * p.L)) ^ n * ‖gradient f x‖) :=
        mul_le_mul_of_nonneg_left ih hρ
      _ = _ := by rw [pow_succ]; ring

lemma probe_gradient_bound (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    {f : p.E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ (gradient f))
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖) (x : p.E) (n : ℕ) :
    ‖gradient f (probePoint p (gradient f) x n)‖ ≤ ‖gradient f x‖ := by
  have hL : 0 < p.L := hμ.trans_le hμL
  have hρ : 0 ≤ 1 - p.μ / (2 * p.L) := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).mpr
    linarith
  have hρ1 : 1 - p.μ / (2 * p.L) ≤ 1 := by
    linarith [div_nonneg hμ.le (by positivity : 0 ≤ 2 * p.L)]
  exact (probe_gradient_rate p hμ hμL hf hg hs hlip x n).trans
    ((mul_le_mul_of_nonneg_right (pow_le_one₀ hρ hρ1) (norm_nonneg _)).trans_eq (one_mul _))

lemma probe_residual (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L) (hM : 0 ≤ p.M)
    {f : p.E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ (gradient f))
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (u : p.E) (hu : gradient f u = 0)
    (hH : ∀ z, ‖fderiv ℝ (gradient f) z - fderiv ℝ (gradient f) u‖ ≤ p.M * ‖z - u‖)
    (x : p.E) (j : ℕ) :
    ‖gradient f (probePoint p (gradient f) x (j + 1)) -
      (gradient f (probePoint p (gradient f) x j) -
        (1 / (2 * p.L)) • fderiv ℝ (gradient f) u (gradient f (probePoint p (gradient f) x j)))‖ ≤
      p.M * ‖gradient f x‖ ^ 2 / (2 * p.μ * p.L) := by
  have hL : 0 < p.L := hμ.trans_le hμL
  have hnorm := probe_gradient_bound p hμ hμL hf hg hs hlip x
  have hd (k : ℕ) : ‖probePoint p (gradient f) x k - u‖ ≤ ‖gradient f x‖ / p.μ :=
    (distance_from_gradient hμ hs u hu _).trans (div_le_div_of_nonneg_right (hnorm k) hμ.le)
  have hh := anchored_linearization hM hg u (probePoint p (gradient f) x j)
    (probePoint p (gradient f) x (j + 1)) hH (hd j) (hd (j + 1))
  have he : probePoint p (gradient f) x (j + 1) - probePoint p (gradient f) x j =
      -(1 / (2 * p.L)) • gradient f (probePoint p (gradient f) x j) := by
    rw [probePoint_succ]
    module
  rw [he, map_smul, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * p.L))] at hh
  have he' : gradient f (probePoint p (gradient f) x (j + 1)) -
      gradient f (probePoint p (gradient f) x j) -
      -(1 / (2 * p.L)) • fderiv ℝ (gradient f) u (gradient f (probePoint p (gradient f) x j)) =
      gradient f (probePoint p (gradient f) x (j + 1)) -
      (gradient f (probePoint p (gradient f) x j) -
      (1 / (2 * p.L)) • fderiv ℝ (gradient f) u (gradient f (probePoint p (gradient f) x j))) := by module
  rw [he'] at hh
  calc
    _ ≤ p.M * (‖gradient f x‖ / p.μ) *
        ((1 / (2 * p.L)) * ‖gradient f (probePoint p (gradient f) x j)‖) := hh
    _ ≤ p.M * (‖gradient f x‖ / p.μ) * ((1 / (2 * p.L)) * ‖gradient f x‖) := by
      gcongr
      exact hnorm j
    _ = _ := by ring

lemma probe_fit_exists (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L) (hM : 0 ≤ p.M)
    {f : p.E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ (gradient f))
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + p.μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (u : p.E) (hu : gradient f u = 0)
    (hH : ∀ z, ‖fderiv ℝ (gradient f) z - fderiv ℝ (gradient f) u‖ ≤ p.M * ‖z - u‖)
    (x : p.E) : ∃ B, Fits p (probeHistory p (gradient f) x (Module.finrank ℝ p.E + 1)) B := by
  let B : Model p.E := ⟨fderiv ℝ (gradient f) u, hessian_symmetric hf hg u⟩
  refine ⟨B, ?_, ?_⟩
  · intro v
    exact ⟨NonlinearTemporalDiscrepancy.hessian_lower_bound hg hs u v,
      NonlinearTemporalDiscrepancy.hessian_upper_bound (hμ.le.trans hμL) hlip u v⟩
  · intro j hj
    rw [probeHistory_getD p (gradient f) x (by omega : j + 1 < Module.finrank ℝ p.E + 1),
      probeHistory_getD p (gradient f) x (by omega : j < Module.finrank ℝ p.E + 1),
      probeHistory_getD p (gradient f) x (by omega : 0 < Module.finrank ℝ p.E + 1), probePoint_zero]
    exact probe_residual p hμ hμL hM hf hg hs hlip u hu hH x j

end OracleTemplate.SpectralGradient
