import LongTails.Proofs.CoupledCubicSelection
import LongTails.Proofs.CoupledCubicConcentration
import LongTails.Proofs.CoupledCubicMoments
import LongTails.Proofs.CoupledCubicPopulation

namespace LongTails.Proofs.CoupledCubicBatch

open LongTails.Setups.StrongGrowthFiniteSumSecondOrder
open LongTails.Algorithms.CoupledCubicTournament
open LongTails.Proofs.CoupledCubicExecution
open LongTails.Proofs.CoupledCubicSelection
open LongTails.Proofs.CoupledCubicConcentration

noncomputable def columns (p : Params) (reference : Model p)
    (href : reference.2.toLinearMap.IsSymmetric) (g : Fin p.n × p.E → Model p)
    (x : p.E) (i : Fin p.n) : Option (Fin (Module.finrank ℝ p.E)) → p.E
  | none => (g (i, x)).1 + (g (i, x)).2 (modelStep p reference)
  | some j => (g (i, x)).2 (href.eigenvectorBasis rfl j)

noncomputable def meanColumns (p : Params) (reference : Model p)
    (href : reference.2.toLinearMap.IsSymmetric) : Option (Fin (Module.finrank ℝ p.E)) → p.E
  | none => reference.1 + reference.2 (modelStep p reference)
  | some j => reference.2 (href.eigenvectorBasis rfl j)

noncomputable def scales (p : Params) (reference : Model p)
    (href : reference.2.toLinearMap.IsSymmetric) : Option (Fin (Module.finrank ℝ p.E)) → ℝ
  | none => p.ρ * ‖modelStep p reference‖ ^ 2
  | some j => |href.eigenvalues rfl j| + p.ρ * ‖modelStep p reference‖

lemma columns_mean (p : Params) (reference : Model p)
    (href : reference.2.toLinearMap.IsSymmetric) (g : Fin p.n × p.E → Model p) (x : p.E)
    (hg : reference.1 = (p.n : ℝ)⁻¹ • ∑ i, (g (i, x)).1)
    (hH : reference.2 = (p.n : ℝ)⁻¹ • ∑ i, (g (i, x)).2)
    (j : Option (Fin (Module.finrank ℝ p.E))) :
    ∑ i, columns p reference href g x i j = (p.n : ℝ) • meanColumns p reference href j := by
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p.n
  cases j with
  | none =>
    change ∑ i, ((g (i, x)).1 + (g (i, x)).2 (modelStep p reference)) =
      (p.n : ℝ) • (reference.1 + reference.2 (modelStep p reference))
    rw [hg, hH]
    simp [Finset.sum_add_distrib, smul_apply, sum_apply, smul_add, smul_smul, hn]
  | some j =>
    change ∑ i, (g (i, x)).2 (href.eigenvectorBasis rfl j) =
      (p.n : ℝ) • reference.2 (href.eigenvectorBasis rfl j)
    have he := congrArg (fun H : p.E →L[ℝ] p.E => H (href.eigenvectorBasis rfl j)) hH
    rw [he]
    simp [smul_apply, sum_apply, smul_smul, hn]

lemma columns_moment_of_raw_bounds (p : Params) (reference : Model p)
    (href : reference.2.toLinearMap.IsSymmetric) (g : Fin p.n × p.E → Model p)
    (x : p.E) (hκ : 0 ≤ p.κ) (hρ : 0 ≤ p.ρ)
    (hres : ∑ i, ‖(g (i, x)).1 + (g (i, x)).2 (modelStep p reference)‖ ^ 2 ≤
      5 / 2 * (p.n : ℝ) * p.κ * p.ρ ^ 2 * ‖modelStep p reference‖ ^ 4)
    (hH : ∀ v : p.E, ∑ i, ‖(g (i, x)).2 v‖ ^ 2 ≤ 64 * (p.n : ℝ) * p.κ *
      (‖reference.2 v‖ ^ 2 + p.ρ ^ 2 * ‖modelStep p reference‖ ^ 2 * ‖v‖ ^ 2))
    (j : Option (Fin (Module.finrank ℝ p.E))) :
    (p.n : ℝ)⁻¹ * ∑ i, ‖columns p reference href g x i j‖ ^ 2 ≤
      (64 * p.κ) * scales p reference href j ^ 2 := by
  have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p.n))
  have hnormalize (X C : ℝ) (h : X ≤ (p.n : ℝ) * C) : (p.n : ℝ)⁻¹ * X ≤ C := by
    calc
      _ ≤ (p.n : ℝ)⁻¹ * ((p.n : ℝ) * C) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = C := by field_simp
  cases j with
  | none =>
    simp only [columns, scales]
    apply hnormalize
    have hp : 0 ≤ (p.n : ℝ) * p.κ * p.ρ ^ 2 * ‖modelStep p reference‖ ^ 4 := by positivity
    nlinarith
  | some j =>
    have he : ‖reference.2 (href.eigenvectorBasis rfl j)‖ ^ 2 = (href.eigenvalues rfl j) ^ 2 := by
      change ‖reference.2.toLinearMap (href.eigenvectorBasis rfl j)‖ ^ 2 = _
      rw [href.apply_eigenvectorBasis]
      simp [norm_smul, OrthonormalBasis.norm_eq_one, Real.norm_eq_abs]
    have hh := hH (href.eigenvectorBasis rfl j)
    rw [he, OrthonormalBasis.norm_eq_one] at hh
    simp only [one_pow, mul_one] at hh
    simp only [columns, scales]
    apply hnormalize
    have hs : (href.eigenvalues rfl j) ^ 2 + p.ρ ^ 2 * ‖modelStep p reference‖ ^ 2 ≤
        (|href.eigenvalues rfl j| + p.ρ * ‖modelStep p reference‖) ^ 2 := by
      nlinarith [abs_nonneg (href.eigenvalues rfl j), sq_abs (href.eigenvalues rfl j),
        mul_nonneg (abs_nonneg (href.eigenvalues rfl j))
          (mul_nonneg hρ (norm_nonneg (modelStep p reference)))]
    have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 64 * (p.n : ℝ) * p.κ)
    nlinarith

lemma score_implies_accuracy (p : Params) (reference : Model p)
    (href : reference.2.toLinearMap.IsSymmetric) (g : Fin p.n × p.E → Model p)
    (x : p.E) (V η : ℝ) (hρ : 0 ≤ p.ρ) (hη : 0 ≤ η)
    (hmean : ∀ j, ∑ i, columns p reference href g x i j =
      (p.n : ℝ) • meanColumns p reference href j)
    (hmoment : ∀ j, (p.n : ℝ)⁻¹ * ∑ i, ‖columns p reference href g x i j‖ ^ 2 ≤
      V * scales p reference href j ^ 2)
    (b : ℕ) (ξ : Fin b → Fin p.n)
    (hscore : ∑ j, (scales p reference href j)⁻¹ ^ 2 *
      ‖(1 / (b : ℝ)) • ∑ k, columns p reference href g x (ξ k) j -
        meanColumns p reference href j‖ ^ 2 ≤ η ^ 2) :
    relativeModelAccurate p reference (sampledModel p b g x ξ) href η := by
  have hm (j) : ∑ i, columns p reference href g x i j =
      (Fintype.card (Fin p.n) : ℝ) • meanColumns p reference href j := by
    simpa using hmean j
  have hv (j) : (Fintype.card (Fin p.n) : ℝ)⁻¹ *
      ∑ i, ‖columns p reference href g x i j‖ ^ 2 ≤ V * scales p reference href j ^ 2 := by
    simpa using hmoment j
  constructor
  · have hh := finite_relative_batch_coordinate (columns p reference href g x)
      (meanColumns p reference href) (scales p reference href) V η hη hm hv b ξ hscore none
    rw [sampledModel_coupled_error]
    simpa [columns, meanColumns, scales, one_div,
      abs_of_nonneg (mul_nonneg hρ (sq_nonneg ‖modelStep p reference‖)), mul_assoc] using hh
  · let D := (sampledModel p b g x ξ).2 - reference.2
    have he (j : Fin (Module.finrank ℝ p.E)) : D (href.eigenvectorBasis rfl j) =
        (1 / (b : ℝ)) • ∑ k, columns p reference href g x (ξ k) (some j) -
          meanColumns p reference href (some j) := by
      simp [D, columns, meanColumns, sampledModel_hessian_apply, one_div]
    have hker (j : Fin (Module.finrank ℝ p.E))
        (hz : |href.eigenvalues rfl j| + p.ρ * ‖modelStep p reference‖ = 0) :
        D (href.eigenvectorBasis rfl j) = 0 := by
      rw [he]
      apply finite_batch_error_zero _ _ (hm (some j)) _ b ξ
      have hh := hv (some j)
      simpa [scales, hz] using hh
    have hcols : ∑ j, (|href.eigenvalues rfl j| + p.ρ * ‖modelStep p reference‖)⁻¹ ^ 2 *
        ‖D (href.eigenvectorBasis rfl j)‖ ^ 2 ≤ η ^ 2 := by
      simp only [Fintype.sum_option] at hscore
      have hn : 0 ≤ (scales p reference href none)⁻¹ ^ 2 *
          ‖(1 / (b : ℝ)) • ∑ k, columns p reference href g x (ξ k) none -
            meanColumns p reference href none‖ ^ 2 := by positivity
      simp_rw [he]
      change (∑ j, (scales p reference href (some j))⁻¹ ^ 2 *
        ‖(1 / (b : ℝ)) • ∑ k, columns p reference href g x (ξ k) (some j) -
          meanColumns p reference href (some j)‖ ^ 2) ≤ η ^ 2
      linarith
    intro v
    exact CoupledCubicGeometry.relative_norm_of_weighted_columns (href.eigenvectorBasis rfl)
      (fun j => |href.eigenvalues rfl j| + p.ρ * ‖modelStep p reference‖)
      D η hη hker hcols v

lemma batch_failure_bound (p : Params) (reference : Model p)
    (href : reference.2.toLinearMap.IsSymmetric) (g : Fin p.n × p.E → Model p)
    (x : p.E) (V η : ℝ) (hρ : 0 ≤ p.ρ) (hV : 0 ≤ V) (hη : 0 < η)
    (hmean : ∀ j, ∑ i, columns p reference href g x i j =
      (p.n : ℝ) • meanColumns p reference href j)
    (hmoment : ∀ j, (p.n : ℝ)⁻¹ * ∑ i, ‖columns p reference href g x i j‖ ^ 2 ≤
      V * scales p reference href j ^ 2)
    (b : ℕ) (hb : 0 < b) :
    (MeasureTheory.Measure.pi (fun _ : Fin b => (PMF.uniformOfFintype (Fin p.n)).toMeasure)).real
      {ξ : Fin b → Fin p.n | ¬relativeModelAccurate p reference (sampledModel p b g x ξ) href η} ≤
      ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ) * V / ((b : ℝ) * η ^ 2) := by
  let : MeasurableSpace p.E := borel p.E
  let : BorelSpace p.E := ⟨rfl⟩
  have hm (j) : ∑ i, columns p reference href g x i j =
      (Fintype.card (Fin p.n) : ℝ) • meanColumns p reference href j := by
    simpa using hmean j
  have hv (j) : (Fintype.card (Fin p.n) : ℝ)⁻¹ *
      ∑ i, ‖columns p reference href g x i j‖ ^ 2 ≤ V * scales p reference href j ^ 2 := by
    simpa using hmoment j
  have ht := finite_uniform_relative_batch_tail (columns p reference href g x)
    (meanColumns p reference href) (scales p reference href) V hV hm hv b hb η hη
  have hsub : {ξ : Fin b → Fin p.n |
      ¬relativeModelAccurate p reference (sampledModel p b g x ξ) href η} ⊆
      {ξ : Fin b → Fin p.n | η ^ 2 < ∑ j, (scales p reference href j)⁻¹ ^ 2 *
        ‖(1 / (b : ℝ)) • ∑ k, columns p reference href g x (ξ k) j -
          meanColumns p reference href j‖ ^ 2} := by
    intro ξ hbad
    exact lt_of_not_ge (fun hs => hbad
      (score_implies_accuracy p reference href g x V η hρ hη.le hmean hmoment b ξ hs))
  apply (MeasureTheory.measureReal_mono hsub).trans
  simpa only [Fintype.card_option, Fintype.card_fin] using ht

lemma objective_raw_moments (p : Params) (f : Fin p.n → p.E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hκ : 1 ≤ p.κ) (hρ : 0 < p.ρ)
    (hSGC : ∀ y, (p.n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) y‖ ^ 2 ≤
      p.κ * ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) y‖ ^ 2)
    (hRMS : ∀ y z, (p.n : ℝ)⁻¹ * ∑ i,
      ‖fderiv ℝ (gradient (f i)) y - fderiv ℝ (gradient (f i)) z‖ ^ 2 ≤
        p.ρ ^ 2 * ‖y - z‖ ^ 2) (x : p.E) :
    let reference : Model p := (gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) x,
      fderiv ℝ (gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f)) x)
    let s := modelStep p reference
    (∑ i, ‖gradient (f i) x + fderiv ℝ (gradient (f i)) x s‖ ^ 2 ≤
      5 / 2 * (p.n : ℝ) * p.κ * p.ρ ^ 2 * ‖s‖ ^ 4) ∧
    (∀ v : p.E, ∑ i, ‖fderiv ℝ (gradient (f i)) x v‖ ^ 2 ≤ 64 * (p.n : ℝ) * p.κ *
      (‖reference.2 v‖ ^ 2 + p.ρ ^ 2 * ‖s‖ ^ 2 * ‖v‖ ^ 2)) := by
  let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let G := fun i => gradient (f i)
  let H := fun i => fderiv ℝ (gradient (f i))
  let Gbar := gradient F
  let Hbar := fderiv ℝ (gradient F)
  let reference : Model p := (Gbar x, Hbar x)
  let s := modelStep p reference
  have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p.n))
  have unnormalize (X C : ℝ) (h : (p.n : ℝ)⁻¹ * X ≤ C) : X ≤ (p.n : ℝ) * C := by
    calc
      X = (p.n : ℝ) * ((p.n : ℝ)⁻¹ * X) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h hn.le
  have hS (y : p.E) : ∑ i, ‖G i y‖ ^ 2 ≤ (Fintype.card (Fin p.n) : ℝ) * p.κ * ‖Gbar y‖ ^ 2 := by
    have hh := unnormalize _ _ (hSGC y)
    simpa only [Fintype.card_fin, mul_assoc] using hh
  have hL (y z : p.E) : ∑ i, ‖H i y - H i z‖ ^ 2 ≤
      (Fintype.card (Fin p.n) : ℝ) * p.ρ ^ 2 * ‖y - z‖ ^ 2 := by
    have hh := unnormalize _ _ (hRMS y z)
    simpa only [Fintype.card_fin, mul_assoc] using hh
  have hd (i : Fin p.n) (y : p.E) : HasFDerivAt (G i) (H i y) y :=
    CoupledCubicPopulation.component_gradient_derivative f hf i y
  have hF : ContDiff ℝ 2 F := CoupledCubicPopulation.objective_contDiff_two f hf
  have hb (y : p.E) : HasFDerivAt Gbar (Hbar y) y :=
    ((OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hF).differentiable
      (by norm_num) y).hasFDerivAt
  have hbL (y z : p.E) : ‖Hbar y - Hbar z‖ ≤ p.ρ * ‖y - z‖ :=
    CoupledCubicPopulation.objective_hessian_lipschitz f hf p.ρ hρ.le hRMS y z
  have hsym : (Hbar x).toLinearMap.IsSymmetric :=
    OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hF x
  have hs : Gbar x + Hbar x s + (p.ρ / 2 * ‖s‖) • s = 0 :=
    modelStep_stationary p hρ reference (fun u v => (hsym u v).symm)
  have hrem : ‖Gbar (x + s) - (Gbar x + Hbar x s)‖ ≤ p.ρ / 2 * ‖s‖ ^ 2 := by
    have hh := CubicRegularization.gradient_taylor hb hbL x s
    simpa only [sub_add_eq_sub_sub, div_mul_eq_mul_div] using hh
  have hnew := CoupledCubicMoments.cubic_stationary_gradient_norm (Hbar x) (Gbar x) s
    (Gbar (x + s)) p.ρ hρ.le hs hrem
  constructor
  · simpa only [Fintype.card_fin] using CoupledCubicMoments.cubic_residual_moment
      G H Gbar p.κ p.ρ p.ρ hκ hρ.le le_rfl hd hL hS x s hnew
  · intro v
    simpa only [Fintype.card_fin] using CoupledCubicMoments.cubic_hessian_moment_all_steps
      G H Gbar Hbar p.κ p.ρ p.ρ hκ hρ.le le_rfl hd hb hL hbL hS x s hs v

lemma objective_batch_failure (p : Params) (f : Fin p.n → p.E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (hκ : 1 ≤ p.κ) (hρ : 0 < p.ρ)
    (hSGC : ∀ y, (p.n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) y‖ ^ 2 ≤
      p.κ * ‖gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) y‖ ^ 2)
    (hRMS : ∀ y z, (p.n : ℝ)⁻¹ * ∑ i,
      ‖fderiv ℝ (gradient (f i)) y - fderiv ℝ (gradient (f i)) z‖ ^ 2 ≤
        p.ρ ^ 2 * ‖y - z‖ ^ 2) (x : p.E)
    (href : (fderiv ℝ (gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f)) x).toLinearMap.IsSymmetric)
    (η : ℝ) (hη : 0 < η) (b : ℕ) (hb : 0 < b) :
    let reference : Model p := (gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) x,
      fderiv ℝ (gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f)) x)
    let replies : Fin p.n × p.E → Model p := fun ix =>
      (gradient (f ix.1) ix.2, fderiv ℝ (gradient (f ix.1)) ix.2)
    (MeasureTheory.Measure.pi (fun _ : Fin b => (PMF.uniformOfFintype (Fin p.n)).toMeasure)).real
      {ξ : Fin b → Fin p.n | ¬relativeModelAccurate p reference (sampledModel p b replies x ξ) href η} ≤
      ((Module.finrank ℝ p.E + 1 : ℕ) : ℝ) * (64 * p.κ) / ((b : ℝ) * η ^ 2) := by
  let reference : Model p := (gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) x,
    fderiv ℝ (gradient (LongTails.Setups.FiniteSumSmoothAndConvex.objective f)) x)
  let replies : Fin p.n × p.E → Model p := fun ix =>
    (gradient (f ix.1) ix.2, fderiv ℝ (gradient (f ix.1)) ix.2)
  have hk0 : 0 ≤ p.κ := by linarith
  have hraw := objective_raw_moments p f hf hκ hρ hSGC hRMS x
  apply batch_failure_bound p reference href replies x (64 * p.κ) η hρ.le (by positivity) hη
  · exact columns_mean p reference href replies x
      (CoupledCubicPopulation.objective_gradient f hf x)
      (CoupledCubicPopulation.objective_hessian f hf x)
  · exact columns_moment_of_raw_bounds p reference href replies x hk0 hρ.le hraw.1 hraw.2
  · exact hb

end LongTails.Proofs.CoupledCubicBatch
