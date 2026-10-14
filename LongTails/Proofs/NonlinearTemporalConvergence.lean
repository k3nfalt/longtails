import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.TemporalSpectralResponse
import LongTails.Proofs.TemporalNonlinearStability
import LongTails.Proofs.TemporalAcceleratedExecution
import LongTails.Proofs.NonlinearTemporalParameters
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.NonlinearTemporalDiscrepancy

open LongTails.Setups.HessianLipschitzTemporalDiscrepancy

open TemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma minimizer_gradient_zero {f : E → ℝ} {u : E} (hm : IsMinOn f Set.univ u) :
    gradient f u = 0 := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient, map_zero]
  exact (hm.isLocalMin Filter.univ_mem).fderiv_eq_zero

lemma factorized_hessian_model {f : E → ℝ} {μ L : ℝ} (hμ : 0 < μ) (hL : 0 ≤ L)
    (hf : ContDiff ℝ 2 f)
    (hs : ∀ x y, f x + ⟪gradient f x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (u : E) :
    ∃ A : E →L[ℝ] E, A.adjoint.comp A = fderiv ℝ (gradient f) u ∧
      (∀ x, μ * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2) ∧ (∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2) := by
  have hg := (gradient_contDiff_one hf).differentiable (by norm_num)
  have hlo := hessian_lower_bound hg hs u
  obtain ⟨A, hA⟩ := spectral_factorization (fderiv ℝ (gradient f) u) (hessian_symmetric hf u)
    (fun x => (mul_nonneg hμ.le (sq_nonneg ‖x‖)).trans (hlo x))
  have hn (x : E) : ‖A x‖ ^ 2 = ⟪fderiv ℝ (gradient f) u x, x⟫ := by
    rw [← hA]
    change ‖A x‖ ^ 2 = ⟪A.adjoint (A x), x⟫
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  refine ⟨A, hA, ?_, ?_⟩
  · intro x
    rw [hn]
    exact hlo x
  · intro x
    rw [hn]
    exact hessian_upper_bound hL hlip u x

omit [FiniteDimensional ℝ E] in
lemma centered_forcing_step (A : E →L[ℝ] E) {θ μ : ℝ} (hθ : 1 + θ ≠ 0)
    (G R : E → E) (u : E) (hG : ∀ x, G x = A.adjoint (A (x - u)) + R (x - u))
    (s : E × E) (e : E) :
    let next := acceleratedUpdate θ μ s (G (acceleratedQuery θ s) + e)
    (next.1 - u, next.2 - u) = transition A μ θ (s.1 - u, s.2 - u) +
      injection μ θ (e + R (acceleratedQuery θ (s.1 - u, s.2 - u))) := by
  dsimp only
  change acceleratedUpdate θ μ s (G (acceleratedQuery θ s) + e) - (u, u) = _
  rw [← update_sub_const θ μ hθ, hG, ← query_sub_const θ hθ s u]
  change acceleratedUpdate θ μ (s.1 - u, s.2 - u)
    (A.adjoint (A (acceleratedQuery θ (s.1 - u, s.2 - u))) +
      R (acceleratedQuery θ (s.1 - u, s.2 - u)) + e) = _
  rw [show A.adjoint (A (acceleratedQuery θ (s.1 - u, s.2 - u))) +
      R (acceleratedQuery θ (s.1 - u, s.2 - u)) + e =
      A.adjoint (A (acceleratedQuery θ (s.1 - u, s.2 - u))) +
        (e + R (acceleratedQuery θ (s.1 - u, s.2 - u))) by abel]
  exact forced_transition A μ θ _ _

lemma hessian_remainder_bound {f : E → ℝ} {M : ℝ}
    (hf : ContDiff ℝ 2 f) (hM : 0 ≤ M)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (u : E) (hu : gradient f u = 0) (A : E →L[ℝ] E)
    (hA : A.adjoint.comp A = fderiv ℝ (gradient f) u) (x : E) :
    ‖gradient f (u + x) - A.adjoint (A x)‖ ≤ M * ‖x‖ ^ 2 := by
  have hh := gradient_linearization_bound hM
    ((gradient_contDiff_one hf).differentiable (by norm_num)) hH u (u + x)
  simpa only [hu, sub_zero, add_sub_cancel_left, ← hA, ContinuousLinearMap.comp_apply] using hh

lemma local_centered_bounds (A : E →L[ℝ] E) {μ L θ D M : ℝ}
    (hμ : 0 < μ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hstep : θ ^ 2 * L ≤ μ)
    (hlower : ∀ x, μ * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hupper : ∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2)
    (v : ℕ → E × E) (e r : ℕ → E)
    (hv : ∀ k, v (k + 1) = transition A μ θ (v k) + injection μ θ (e k + r k))
    (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ D)
    (hr : ∀ k, ‖r k‖ ≤ M * ‖acceleratedQuery θ (v k)‖ ^ 2)
    (hsmall : (θ * Real.sqrt (2 / μ) * M / Real.sqrt μ) *
      (energySeminorm A μ (v 0) / Real.sqrt μ + 2 * (33 * θ * D / μ)) ≤
        (1 - Real.sqrt (1 - θ)) / 2) :
    let p := energySeminorm A μ
    let ρ := Real.sqrt (1 - θ)
    let q := (1 + ρ) / 2
    let β := θ * Real.sqrt (2 / μ)
    let a := p (v 0) / Real.sqrt μ
    let b := 33 * θ * D / μ
    (∀ n, ‖(v n).1‖ ≤ a * q ^ n + 2 * b) ∧
    (∀ start count, 0 < count → p (tailAverage v start count) ≤
      (p (v 0) + 2 * β * M * a ^ 2 / (q - ρ)) * q ^ start +
        8 * β * M * b ^ 2 / (1 - ρ) + 2 * β * D / ((1 - ρ) * count)) := by
  let H := A.adjoint.comp A
  have hsym : H.toLinearMap.IsSymmetric := by
    intro x y
    change ⟪A.adjoint (A x), y⟫ = ⟪x, A.adjoint (A y)⟫
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  let basis := hsym.eigenvectorBasis rfl
  let eig := hsym.eigenvalues rfl
  have heig (i : Fin (Module.finrank ℝ E)) : μ ≤ eig i ∧ eig i ≤ L := by
    apply spectral_eigenvalue_bounds H hsym
    · intro x
      simpa only [H, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq] using hlower x
    · intro x
      simpa only [H, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq] using hupper x
  have hdiag (i : Fin (Module.finrank ℝ E)) (x : E) :
      basis.repr (A.adjoint (A x)) i = eig i * basis.repr x i :=
    hsym.eigenvectorBasis_apply_self_apply rfl x i
  let noise := linearOrbit (transition A μ θ) (injection μ θ) 0 e
  have hn0 : noise 0 = 0 := rfl
  have hn (k : ℕ) : noise (k + 1) = transition A μ θ (noise k) + injection μ θ (e k) := rfl
  have hnoise (k : ℕ) : ‖queryMap θ (noise k)‖ ≤ 33 * θ * D / μ :=
    balanced_state_query A basis eig hμ hθ hθ1 hstep hD heig hdiag noise e hn0 hn he k
  have hχ : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hρ0 : 0 ≤ Real.sqrt (1 - θ) := Real.sqrt_nonneg _
  have hρ1 : Real.sqrt (1 - θ) < 1 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by nlinarith)
  have hβ : 0 ≤ θ * Real.sqrt (2 / μ) := by positivity
  have hb : 0 ≤ 33 * θ * D / μ := by positivity
  have hT := transition_contracts A hμ hθ.le hθ1 hstep hlower hupper
  have hB := injection_bound A hμ hθ.le hstep hupper
  have hQ := energy_controls_query A hμ hθ.le hlower
  constructor
  · intro n
    have hxnoise : ‖(noise n).1‖ ≤ 33 * θ * D / μ := by
      have hh := balanced_state_position A basis eig hμ hθ hθ1 hstep hD heig hdiag noise e hn0 hn he n
      exact hh.trans (div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hθ.le hD]) hμ.le)
    have hx := projection_split_bound (ContinuousLinearMap.fst ℝ E E) (energySeminorm A μ) hχ
      (fun s => (energy_controls_coordinates A hμ hlower s).1) (v n) (noise n) hxnoise
    exact hx.trans (nonlinear_split_envelope (transition A μ θ) (injection μ θ) (queryMap θ)
      (energySeminorm A μ) v noise e r hρ0 hρ1 hβ hχ hb hM hT hB hQ hv hn hn0 hnoise hr hsmall n)
  · intro start count hc
    exact split_tail_bound (transition A μ θ) (injection μ θ) (queryMap θ) (energySeminorm A μ)
      v noise e r hρ0 hρ1 hβ hχ hb hD hM hT hB hQ hv hn hn0 hnoise he hr hsmall start count hc

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma average_accuracy_of_local_energy {f : E → ℝ} {μ M R ε : ℝ}
    (hμ : 0 < μ) (hM : 0 ≤ M) (hε : 0 ≤ ε) (A : E →L[ℝ] E) (u : E)
    (hlower : ∀ x, μ * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hrem : ∀ x, |f (u + x) - f u - ‖A x‖ ^ 2 / 2| ≤ M * ‖x‖ ^ 3)
    (v : ℕ → E × E) (hpos : ∀ n, ‖(v n).1‖ ≤ R) (hlocal : 2 * M * R ≤ μ)
    (start count : ℕ) (hc : 0 < count)
    (henergy : energySeminorm A μ (tailAverage v start count) ≤ Real.sqrt ε) :
    f (u + (tailAverage v start count).1) - f u ≤ ε := by
  let px : Seminorm ℝ (E × E) :=
    (normSeminorm ℝ E).comp (ContinuousLinearMap.fst ℝ E E).toLinearMap
  have hpx : ∀ k, px (v k) ≤ (0 : ℝ) * (1 : ℝ) ^ k + R := by
    intro k
    change ‖(v k).1‖ ≤ _
    simpa only [zero_mul, zero_add] using hpos k
  have hb := seminorm_tail_envelope px v (by norm_num : (0 : ℝ) ≤ 1) (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 0) hpx start count hc
  have hnorm : ‖(tailAverage v start count).1‖ ≤ R := by
    change ‖(tailAverage v start count).1‖ ≤ 0 * 1 ^ start + R at hb
    simpa only [zero_mul, zero_add] using hb
  have hl : 2 * M * ‖(tailAverage v start count).1‖ ≤ μ :=
    (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans hlocal
  have ho := local_objective_upper A u (u + (tailAverage v start count).1)
    (by simpa only [add_sub_cancel_left] using hlower (tailAverage v start count).1)
    (by simpa only [add_sub_cancel_left] using hrem (tailAverage v start count).1)
    (by simpa only [add_sub_cancel_left] using hl)
  simp only [add_sub_cancel_left] at ho
  have hp := energySeminorm_sq A hμ.le (tailAverage v start count)
  have he := pow_le_pow_left₀ (apply_nonneg (energySeminorm A μ) _) henergy 2
  rw [Real.sq_sqrt hε] at he
  have hz : 0 ≤ μ * ‖(tailAverage v start count).2‖ ^ 2 := by positivity
  linarith

lemma local_tail_accuracy {f : E → ℝ} (A : E →L[ℝ] E) (u : E)
    {μ L θ D M ε : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hε : 0 ≤ ε) (hstep : θ ^ 2 * L ≤ μ)
    (hlower : ∀ x, μ * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hupper : ∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2)
    (hrem : ∀ x, |f (u + x) - f u - ‖A x‖ ^ 2 / 2| ≤ M * ‖x‖ ^ 3)
    (v : ℕ → E × E) (e r : ℕ → E)
    (hv : ∀ k, v (k + 1) = transition A μ θ (v k) + injection μ θ (e k + r k))
    (he : ∀ n, ‖∑ i ∈ Finset.range n, e i‖ ≤ D)
    (hr : ∀ k, ‖r k‖ ≤ M * ‖acceleratedQuery θ (v k)‖ ^ 2)
    (haM : M * (energySeminorm A μ (v 0) / Real.sqrt μ) ≤ μ / 16)
    (hbM : M * (33 * θ * D / μ) ≤ μ / 32)
    (hbε : Real.sqrt μ * (33 * θ * D / μ) ≤ Real.sqrt ε / 8)
    (n : ℕ) (hn : 0 < n)
    (htrans : energySeminorm A μ (v 0) * ((1 + Real.sqrt (1 - θ)) / 2) ^ n ≤
      Real.sqrt ε / 8)
    (hnoise : 2 * (θ * Real.sqrt (2 / μ)) * D /
      ((1 - Real.sqrt (1 - θ)) * n) ≤ Real.sqrt ε / 8) :
    f (u + (tailAverage v n n).1) - f u ≤ ε := by
  let χ := Real.sqrt μ
  let ρ := Real.sqrt (1 - θ)
  let q := (1 + ρ) / 2
  let a := energySeminorm A μ (v 0) / χ
  let b := 33 * θ * D / μ
  have hχ : 0 < χ := Real.sqrt_pos.mpr hμ
  have hχ2 : χ ^ 2 = μ := Real.sq_sqrt hμ.le
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ < 1 := (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
  have hθρ : θ = 1 - ρ ^ 2 := by dsimp [ρ]; rw [Real.sq_sqrt (by linarith)]; ring
  have ha : 0 ≤ a := div_nonneg (apply_nonneg _ _) hχ.le
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hβ : θ * Real.sqrt 2 / χ = θ * Real.sqrt (2 / μ) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]; dsimp [χ]; ring
  have hpa : χ * a = energySeminorm A μ (v 0) := by dsimp [a]; field_simp
  obtain ⟨hs, ht, hf⟩ := local_response_constants hχ hχ2 hθ hρ0 hρ1 hθρ ha hb hM haM hbM
  rw [hβ] at hs ht hf
  rw [hpa] at ht
  obtain ⟨hpos, htail⟩ := local_centered_bounds A hμ hθ hθ1 hD hM hstep
    hlower hupper v e r hv he hr hs
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hball (k : ℕ) : ‖(v k).1‖ ≤ a + 2 * b := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_one₀ (n := k) hq0 hq1) ha
    exact (hpos k).trans (by nlinarith)
  have hlocal : 2 * M * (a + 2 * b) ≤ μ := by nlinarith
  apply average_accuracy_of_local_energy hμ hM hε A u hlower hrem v hball hlocal n n hn
  have ht' := mul_le_mul_of_nonneg_right ht (pow_nonneg hq0 n)
  have hh := htail n n hn
  change energySeminorm A μ (tailAverage v n n) ≤ _ at hh
  have hε0 := Real.sqrt_nonneg ε
  calc
    _ ≤ 2 * (energySeminorm A μ (v 0) * q ^ n) + χ * b +
        2 * (θ * Real.sqrt (2 / μ)) * D / ((1 - ρ) * n) := by
      nlinarith
    _ ≤ Real.sqrt ε := by dsimp only [q, ρ, χ, b] at *; linarith

end OracleTemplate.NonlinearTemporalDiscrepancy
