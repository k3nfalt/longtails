import LongTails.Setups.QuadraticTemporalDiscrepancy
import LongTails.Proofs.TemporalAcceleratedEnergy
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.Seminorm.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

open scoped RealInnerProductSpace

namespace OracleTemplate.TemporalDiscrepancy

open LongTails.Setups.QuadraticTemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma factorized_quadratic_gradient (A : E →L[ℝ] E) (u x : E) :
    HasGradientAt (fun y => ‖A (y - u)‖ ^ 2 / 2) (A.adjoint (A (x - u))) x := by
  have ha : HasFDerivAt (fun y => A (y - u)) A x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using
      A.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const u)
  have h := ha.norm_sq.const_smul (1 / 2 : ℝ)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  · funext y
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  · ext v
    simp [ContinuousLinearMap.adjoint_inner_left]

lemma objective_minimizer {p : Public} (I : Instance p) :
    IsMinOn (objective I) Set.univ I.xstar := by
  intro x _
  change objective I I.xstar ≤ objective I x
  simp only [objective, sub_self, map_zero, norm_zero, zero_pow (by omega : 2 ≠ 0), zero_div]
  positivity

def queryMap (θ : ℝ) : (E × E) →L[ℝ] E :=
  (1 / (1 + θ)) • (ContinuousLinearMap.fst ℝ E E + θ • ContinuousLinearMap.snd ℝ E E)

def transition (A : E →L[ℝ] E) (μ θ : ℝ) : (E × E) →L[ℝ] (E × E) :=
  let Q := queryMap θ
  let G := (A.adjoint.comp A).comp Q
  (Q - (θ ^ 2 / μ) • G).prod
    ((1 - θ) • ContinuousLinearMap.snd ℝ E E + θ • Q - (θ / μ) • G)

def injection (μ θ : ℝ) : E →L[ℝ] (E × E) :=
  (-(θ ^ 2 / μ) • ContinuousLinearMap.id ℝ E).prod
    (-(θ / μ) • ContinuousLinearMap.id ℝ E)

lemma transition_apply (A : E →L[ℝ] E) (μ θ : ℝ) (s : E × E) :
    transition A μ θ s = acceleratedUpdate θ μ s (A.adjoint (A (acceleratedQuery θ s))) := rfl

lemma forced_transition (A : E →L[ℝ] E) (μ θ : ℝ) (s : E × E) (e : E) :
    acceleratedUpdate θ μ s (A.adjoint (A (acceleratedQuery θ s)) + e) =
      transition A μ θ s + injection μ θ e := by
  rw [transition_apply]
  ext <;> simp [acceleratedUpdate, injection] <;> module

def energyMap (A : E →L[ℝ] E) (μ : ℝ) : (E × E) →ₗ[ℝ] WithLp 2 (E × E) :=
  (WithLp.linearEquiv 2 ℝ (E × E)).symm.toLinearMap.comp
    (A.toLinearMap.prodMap (Real.sqrt μ • LinearMap.id))

def energySeminorm (A : E →L[ℝ] E) (μ : ℝ) : Seminorm ℝ (E × E) :=
  (normSeminorm ℝ (WithLp 2 (E × E))).comp (energyMap A μ)

omit [CompleteSpace E] in
lemma energySeminorm_sq (A : E →L[ℝ] E) {μ : ℝ} (hμ : 0 ≤ μ) (s : E × E) :
    energySeminorm A μ s ^ 2 = ‖A s.1‖ ^ 2 + μ * ‖s.2‖ ^ 2 := by
  change ‖energyMap A μ s‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [energyMap, norm_smul, mul_pow, Real.sq_sqrt hμ]

lemma quadratic_model (A : E →L[ℝ] E) (x y : E) :
    ‖A x‖ ^ 2 / 2 + ⟪A.adjoint (A x), y - x⟫ + ‖A (y - x)‖ ^ 2 / 2 =
      ‖A y‖ ^ 2 / 2 := by
  rw [ContinuousLinearMap.adjoint_inner_left, map_sub, inner_sub_right,
    real_inner_self_eq_norm_sq, norm_sub_sq_real]
  rw [real_inner_comm (A x) (A y)]
  ring

lemma quadratic_descent (A : E →L[ℝ] E) {μ θ L : ℝ}
    (hμ : 0 < μ) (hstep : θ ^ 2 * L ≤ μ)
    (hupper : ∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2) (y : E) :
    ‖A (y - (θ ^ 2 / μ) • A.adjoint (A y))‖ ^ 2 / 2 ≤
      ‖A y‖ ^ 2 / 2 - θ ^ 2 / (2 * μ) * ‖A.adjoint (A y)‖ ^ 2 := by
  let g := A.adjoint (A y)
  have hm := quadratic_model A y (y - (θ ^ 2 / μ) • g)
  have hv : y - (θ ^ 2 / μ) • g - y = -(θ ^ 2 / μ) • g := by module
  rw [hv, inner_smul_right, real_inner_self_eq_norm_sq, map_smul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hm
  have hu := mul_le_mul_of_nonneg_left (hupper g) (sq_nonneg (-(θ ^ 2 / μ)))
  have ht : θ ^ 2 * L / μ ≤ 1 := (div_le_one hμ).mpr hstep
  have hh : (θ ^ 2 / μ) ^ 2 * L * ‖g‖ ^ 2 / 2 ≤
      θ ^ 2 / (2 * μ) * ‖g‖ ^ 2 := by
    calc
      _ = (θ ^ 2 * L / μ) * (θ ^ 2 / (2 * μ) * ‖g‖ ^ 2) := by ring
      _ ≤ 1 * (θ ^ 2 / (2 * μ) * ‖g‖ ^ 2) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
      _ = _ := one_mul _
  change ‖A (y - (θ ^ 2 / μ) • g)‖ ^ 2 / 2 ≤ ‖A y‖ ^ 2 / 2 -
    θ ^ 2 / (2 * μ) * ‖g‖ ^ 2
  have hi : (θ ^ 2 / μ) * ‖g‖ ^ 2 = 2 * (θ ^ 2 / (2 * μ) * ‖g‖ ^ 2) := by ring
  change ‖A y‖ ^ 2 / 2 + -(θ ^ 2 / μ) * ‖g‖ ^ 2 +
    (-(θ ^ 2 / μ)) ^ 2 * ‖A g‖ ^ 2 / 2 = _ at hm
  nlinarith

lemma quadratic_energy_contraction (A : E →L[ℝ] E) {μ θ L : ℝ}
    (hμ : 0 < μ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hstep : θ ^ 2 * L ≤ μ)
    (hlower : ∀ x, μ * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hupper : ∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2) (s : E × E) :
    energySeminorm A μ
        (acceleratedUpdate θ μ s (A.adjoint (A (acceleratedQuery θ s)))) ^ 2 ≤
      (1 - θ) * energySeminorm A μ s ^ 2 := by
  let f := fun x => ‖A x‖ ^ 2 / 2
  let y := acceleratedQuery θ s
  have hs (x : E) : f y + ⟪A.adjoint (A y), x - y⟫ + μ / 2 * ‖x - y‖ ^ 2 ≤ f x := by
    have hm := quadratic_model A y x
    have hl := hlower (x - y)
    dsimp [f]
    linarith
  have h := accelerated_energy_step hμ hθ hθ1 s.1 s.2 0 (A.adjoint (A y))
    (hs s.1) (hs 0) (quadratic_descent A hμ hstep hupper y)
  simp only [f, map_zero, norm_zero, zero_pow (by omega : 2 ≠ 0), zero_div,
    sub_zero] at h
  rw [energySeminorm_sq A hμ.le, energySeminorm_sq A hμ.le]
  change ‖A (acceleratedUpdate θ μ s (A.adjoint (A y))).1‖ ^ 2 / 2 +
    μ / 2 * ‖(acceleratedUpdate θ μ s (A.adjoint (A y))).2‖ ^ 2 ≤ _ at h
  nlinarith

lemma transition_contracts (A : E →L[ℝ] E) {μ θ L : ℝ}
    (hμ : 0 < μ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hstep : θ ^ 2 * L ≤ μ)
    (hlower : ∀ x, μ * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hupper : ∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2) (s : E × E) :
    energySeminorm A μ (transition A μ θ s) ≤
      Real.sqrt (1 - θ) * energySeminorm A μ s := by
  have h := quadratic_energy_contraction A hμ hθ hθ1 hstep hlower hupper s
  rw [← transition_apply] at h
  have hs := Real.sq_sqrt (sub_nonneg.mpr hθ1)
  have hn := apply_nonneg (energySeminorm A μ) s
  have hp := apply_nonneg (energySeminorm A μ) (transition A μ θ s)
  have hr := Real.sqrt_nonneg (1 - θ)
  apply (sq_le_sq₀ hp (mul_nonneg hr hn)).mp
  rwa [mul_pow, hs]

omit [CompleteSpace E] in
lemma injection_bound (A : E →L[ℝ] E) {μ θ L : ℝ}
    (hμ : 0 < μ) (hθ : 0 ≤ θ) (hstep : θ ^ 2 * L ≤ μ)
    (hupper : ∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2) (e : E) :
    energySeminorm A μ (injection μ θ e) ≤ θ * Real.sqrt (2 / μ) * ‖e‖ := by
  have he := energySeminorm_sq A hμ.le (injection μ θ e)
  change energySeminorm A μ (injection μ θ e) ^ 2 =
    ‖A (-(θ ^ 2 / μ) • e)‖ ^ 2 + μ * ‖-(θ / μ) • e‖ ^ 2 at he
  simp only [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at he
  have hu := mul_le_mul_of_nonneg_left (hupper e) (sq_nonneg (θ ^ 2 / μ))
  have ht := mul_le_mul_of_nonneg_right hstep
    (show 0 ≤ θ ^ 2 / μ ^ 2 * ‖e‖ ^ 2 by positivity)
  have hi : μ * (θ ^ 2 / μ ^ 2 * ‖e‖ ^ 2) = θ ^ 2 / μ * ‖e‖ ^ 2 := by
    field_simp
  have hi' : μ * ((θ / μ) ^ 2 * ‖e‖ ^ 2) = θ ^ 2 / μ * ‖e‖ ^ 2 := by
    field_simp
  rw [hi] at ht
  have ht' : (θ ^ 2 / μ) ^ 2 * (L * ‖e‖ ^ 2) ≤ θ ^ 2 / μ * ‖e‖ ^ 2 := by
    convert ht using 1
    field_simp
  have hs := Real.sq_sqrt (show 0 ≤ 2 / μ by positivity)
  have hn := apply_nonneg (energySeminorm A μ) (injection μ θ e)
  have hr : 0 ≤ θ * Real.sqrt (2 / μ) * ‖e‖ := by positivity
  have hid : (θ * Real.sqrt (2 / μ) * ‖e‖) ^ 2 = 2 * θ ^ 2 / μ * ‖e‖ ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    ring
  have hp : energySeminorm A μ (injection μ θ e) ^ 2 ≤
      (θ * Real.sqrt (2 / μ) * ‖e‖) ^ 2 := by
    rw [he, hi', hid]
    calc
      _ ≤ θ ^ 2 / μ * ‖e‖ ^ 2 + θ ^ 2 / μ * ‖e‖ ^ 2 :=
        add_le_add (hu.trans ht') (le_refl _)
      _ = _ := by ring
  exact (sq_le_sq₀ hn hr).mp hp

end OracleTemplate.TemporalDiscrepancy
