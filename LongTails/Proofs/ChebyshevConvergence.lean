import LongTails.Proofs.ChebyshevStochastic
import LongTails.Proofs.ChebyshevEnergy
import LongTails.Proofs.ChebyshevAccuracy
import LongTails.Proofs.QuadraticObjective
import LongTails.Setups.StochasticConvexQuadratic

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.BatchedChebyshev

lemma tuned_allowed (q : LongTails.Setups.StochasticConvexQuadratic.Params) (hL : 0 < q.L) :
    LongTails.Setups.StochasticConvexQuadratic.spec.allowedAlgorithm q (tuned q.L q.R q.σ q.ε q.x0) := by
  let T := if q.L * q.R ^ 2 / 2 ≤ q.ε then 0 else ⌈Real.sqrt (q.L * q.R ^ 2 / q.ε)⌉₊
  refine ⟨(fun i => if i ≤ T then 1 / (q.L * root T i) else 0),
    batch T ⌈65536 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊, ?_, batch_pos _ _, rfl⟩
  · intro i
    change 0 ≤ if i ≤ T then 1 / (q.L * root T i) else 0
    split_ifs
    · exact one_div_nonneg.mpr (mul_nonneg hL.le (root_nonneg _ i))
    · exact le_refl _

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] [MeasurableSpace Ω]

lemma expected_rate {p : Measure Ω} [IsProbabilityMeasure p] {g : E → Ω → E}
    {f : E → ℝ} (A : E →L[ℝ] E) (xstar x0 : E) {L σ R : ℝ}
    (hL : 0 < L) (hR : 0 ≤ R) (hdist : ‖x0 - xstar‖ ≤ R)
    (hf : ∀ x, f x = f xstar + ‖A (x - xstar)‖ ^ 2 / 2)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient E Ω p f g σ) (T M : ℕ) :
    Integrable (fun ξ => f (run L T M g T 1 x0 ξ) - f xstar)
      (Measure.infinitePi fun _ : ℕ => p) ∧
    (∫ ξ, f (run L T M g T 1 x0 ξ) - f xstar
      ∂Measure.infinitePi (fun _ : ℕ => p)) ≤
      L * R ^ 2 / (2 * (2 * (T : ℝ) + 1) ^ 2) +
        (σ ^ 2 / (2 * L)) * (∑ i ∈ Finset.range T,
          weight T (i + 1) ^ 2 / (batch T M (i + 1) : ℝ)) := by
  let H := A.adjoint.comp A
  let hs := factor_symmetric A
  let μ := hs.eigenvalues (n := Module.finrank ℝ E) rfl
  let b := hs.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  have hdiag (x : E) (j : Fin (Module.finrank ℝ E)) :
      b.repr (A.adjoint (A x)) j = μ j * b.repr x j :=
    hs.eigenvectorBasis_apply_self_apply rfl x j
  have heigen (j : Fin (Module.finrank ℝ E)) : A.adjoint (A (b j)) = μ j • b j :=
    hs.apply_eigenvectorBasis rfl j
  have hupper := quadratic_factor_upper A xstar (f xstar) L hf hlip
  have hμ := factor_eigenvalue_bounds A b μ heigen hupper
  have hgrad (x : E) : gradient f x = H (x - xstar) := quadratic_gradient A xstar (f xstar) hf x
  have he := run_energy_bound ho.measurable H A xstar L T M
    (fun i => weight T i ^ 2 / L)
    ho.integrable
    (fun x => by simpa only [hgrad] using ho.variance_integrable x)
    (fun x => by simpa only [hgrad] using ho.unbiased x)
    (fun x => by simpa only [hgrad] using ho.variance x)
    (fun i => by positivity)
    (fun i hi hiT e => noise_energy_bound A hL hi hiT b μ hdiag hμ e)
    T 1 (by omega) (by omega) x0
  have hdet := full_energy_bound A hL T b μ hdiag hμ (x0 - xstar)
  have hdist2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr hdist
  have hdetR : ‖A (propagator H (fun k => 1 / (L * root T k)) T 1 (x0 - xstar))‖ ^ 2 ≤
      L / (2 * (T : ℝ) + 1) ^ 2 * R ^ 2 :=
    hdet.trans (mul_le_mul_of_nonneg_left hdist2 (by positivity))
  have hsum : (∑ j ∈ Finset.Ico 1 (T + 1), (weight T j ^ 2 / L) * σ ^ 2 / batch T M j) =
      (σ ^ 2 / L) * (∑ i ∈ Finset.range T, weight T (i + 1) ^ 2 / (batch T M (i + 1) : ℝ)) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm 1 i]
    ring
  have hpoint (ξ : ℕ → Ω) : f (run L T M g T 1 x0 ξ) - f xstar =
      ‖A (run L T M g T 1 x0 ξ - xstar)‖ ^ 2 / 2 := by rw [hf]; ring
  simp_rw [hpoint]
  refine ⟨he.1.div_const 2, ?_⟩
  rw [integral_div]
  have hh := he.2.trans (add_le_add hdetR (le_refl _))
  rw [hsum] at hh
  have hd := div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2)
  convert hd using 1; field_simp

lemma tuned_expected_accuracy {p : Measure Ω} [IsProbabilityMeasure p] {g : E → Ω → E}
    {f : E → ℝ} (A : E →L[ℝ] E) (xstar x0 : E) {L σ R ε : ℝ}
    (hL : 0 < L) (hR : 0 ≤ R) (hε : 0 < ε) (hdist : ‖x0 - xstar‖ ≤ R)
    (hf : ∀ x, f x = f xstar + ‖A (x - xstar)‖ ^ 2 / 2)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient E Ω p f g σ) :
    let T := if L * R ^ 2 / 2 ≤ ε then 0 else ⌈Real.sqrt (L * R ^ 2 / ε)⌉₊
    let M := ⌈65536 * σ ^ 2 * R ^ 2 / ε ^ 2⌉₊
    Integrable (fun ξ => f (run L T M g T 1 x0 ξ) - f xstar)
      (Measure.infinitePi fun _ : ℕ => p) ∧
    (∫ ξ, f (run L T M g T 1 x0 ξ) - f xstar
      ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ ε := by
  dsimp only
  split_ifs with hcoarse
  · have h := expected_rate A xstar x0 hL hR hdist hf hlip ho 0
      ⌈65536 * σ ^ 2 * R ^ 2 / ε ^ 2⌉₊
    refine ⟨h.1, h.2.trans ?_⟩
    simpa using hcoarse
  · have h := expected_rate A xstar x0 hL hR hdist hf hlip ho
      ⌈Real.sqrt (L * R ^ 2 / ε)⌉₊ ⌈65536 * σ ^ 2 * R ^ 2 / ε ^ 2⌉₊
    exact ⟨h.1, h.2.trans (tuned_error_le hL hε (lt_of_not_ge hcoarse))⟩

end OracleTemplate.BatchedChebyshev
