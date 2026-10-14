import LongTails.Proofs.QuadraticNoiseMoments
import LongTails.Proofs.QuadraticSpectralBounds
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.ChebyshevBatching

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.BatchedChebyshev

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma batchUpdate_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L : ℝ) (T M i : ℕ) :
    Measurable (Function.uncurry (batchUpdate L T M i g)) := by
  unfold batchUpdate Function.uncurry
  fun_prop

omit [CompleteSpace E] in
lemma run_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L : ℝ) (T M n i : ℕ) :
    Measurable (Function.uncurry (run L T M g n i)) := by
  induction n generalizing i with
  | zero => exact measurable_fst
  | succ n ih =>
    have hb := batchUpdate_measurable hg L T M i
    have hr := ih (i + 1)
    exact hr.comp ((hb.comp (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop))

lemma batch_update_energy {p : Measure Ω} [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (H B : E →L[ℝ] E) (u x : E) (L : ℝ) (T M i : ℕ) {σ C : ℝ}
    (hgi : Integrable (g x) p)
    (hg2 : Integrable (fun ω => ‖g x ω - H (x - u)‖ ^ 2) p)
    (hmean : (∫ ω, g x ω ∂p) = H (x - u))
    (hvar : (∫ ω, ‖g x ω - H (x - u)‖ ^ 2 ∂p) ≤ σ ^ 2)
    (hC : 0 ≤ C)
    (hB : ∀ e, ‖(-(1 / (L * root T i))) • B e‖ ^ 2 ≤ C * ‖e‖ ^ 2) :
    Integrable (fun ξ => ‖B (batchUpdate L T M i g x ξ - u)‖ ^ 2)
      (Measure.pi fun _ : Fin (batch T M i) => p) ∧
    (∫ ξ, ‖B (batchUpdate L T M i g x ξ - u)‖ ^ 2
      ∂Measure.pi (fun _ : Fin (batch T M i) => p)) ≤
      ‖B (x - u - (1 / (L * root T i)) • H (x - u))‖ ^ 2 + C * σ ^ 2 / batch T M i := by
  let m := batch T M i
  let X := fun ξ : Fin m → Ω => (1 / (m : ℝ)) • ∑ j, g x (ξ j) - H (x - u)
  have hm : 0 < m := batch_pos T M i
  have hx : Measurable (g x) := hg.comp measurable_prodMk_left
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hmeanb := LightTail.finite_mean_integral hgi m hm
  have hX2 := RobustGradient.finite_mean_variance hx hgi (H (x - u)) hg2 hmean m hm
  have hXi : Integrable X (Measure.pi fun _ : Fin m => p) :=
    hmeanb.1.sub (integrable_const _)
  have hXzero : (∫ ξ, X ξ ∂Measure.pi (fun _ : Fin m => p)) = 0 := by
    dsimp [X]
    rw [integral_sub hmeanb.1 (integrable_const _), hmeanb.2, hmean]
    simp
  let D : E →L[ℝ] E := (-(1 / (L * root T i))) • B
  let y := B (x - u - (1 / (L * root T i)) • H (x - u))
  have ha := StochasticConvexQuadratic.centered_affine_second_moment
    hX hXi hX2.1 hXzero D y
  have hv : (∫ ξ, ‖X ξ‖ ^ 2 ∂Measure.pi (fun _ : Fin m => p)) ≤ σ ^ 2 / m := by
    rw [hX2.2]
    exact div_le_div_of_nonneg_right hvar (Nat.cast_nonneg _)
  have hb := StochasticConvexQuadratic.transformed_noise_squared_bound
    hX hX2.1 D hC hB hv
  have he (ξ : Fin m → Ω) : B (batchUpdate L T M i g x ξ - u) = y + D (X ξ) := by
    have hid : 1 / (L * root T i * (m : ℝ)) = (1 / (L * root T i)) * (1 / (m : ℝ)) := by
      simp only [one_div, mul_inv_rev]
      ring
    simp only [batchUpdate, ← show m = batch T M i from rfl, hid, mul_smul,
      y, D, X, smul_apply, map_sub, map_smul]
    module
  simp_rw [he]
  refine ⟨ha.1, ha.2.le.trans ?_⟩
  dsimp [y]
  calc
    _ ≤ ‖B (x - u - (1 / (L * root T i)) • H (x - u))‖ ^ 2 + C * (σ ^ 2 / m) :=
      add_le_add (le_refl _) hb.2
    _ = _ := by ring

lemma run_energy_bound {p : Measure Ω} [IsProbabilityMeasure p]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (H A : E →L[ℝ] E) (u : E) (L : ℝ) (T M : ℕ) {σ : ℝ} (C : ℕ → ℝ)
    (hgi : ∀ x, Integrable (g x) p)
    (hg2 : ∀ x, Integrable (fun ω => ‖g x ω - H (x - u)‖ ^ 2) p)
    (hmean : ∀ x, (∫ ω, g x ω ∂p) = H (x - u))
    (hvar : ∀ x, (∫ ω, ‖g x ω - H (x - u)‖ ^ 2 ∂p) ≤ σ ^ 2)
    (hC : ∀ i, 0 ≤ C i)
    (hnoise : ∀ i, 0 < i → i ≤ T → ∀ e,
      ‖(-(1 / (L * root T i))) •
        A (propagator H (fun j => 1 / (L * root T j)) (T - i) (i + 1) e)‖ ^ 2 ≤
          C i * ‖e‖ ^ 2)
    (n i : ℕ) (hi : 0 < i) (horizon : i + n = T + 1) (x : E) :
    Integrable (fun ξ => ‖A (run L T M g n i x ξ - u)‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) ∧
    (∫ ξ, ‖A (run L T M g n i x ξ - u)‖ ^ 2
      ∂Measure.infinitePi (fun _ : ℕ => p)) ≤
      ‖A (propagator H (fun j => 1 / (L * root T j)) n i (x - u))‖ ^ 2 +
        ∑ j ∈ Finset.Ico i (T + 1), C j * σ ^ 2 / batch T M j := by
  induction n generalizing i x with
  | zero =>
    have he : i = T + 1 := by omega
    subst i
    simp [run, propagator]
  | succ n ih =>
    have hiT : i ≤ T := by omega
    have hn : n = T - i := by omega
    let m := batch T M i
    let Q := Measure.infinitePi fun _ : ℕ => p
    let B := A.comp (propagator H (fun j => 1 / (L * root T j)) n (i + 1))
    let S := ∑ j ∈ Finset.Ico (i + 1) (T + 1), C j * σ ^ 2 / batch T M j
    let F : (Fin m → Ω) × (ℕ → Ω) → ℝ := fun z =>
      ‖A (run L T M g n (i + 1) (batchUpdate L T M i g x z.1) z.2 - u)‖ ^ 2
    let G := fun b : Fin m → Ω => ‖B (batchUpdate L T M i g x b - u)‖ ^ 2 + S
    have hnext : Measurable (fun b : Fin m → Ω => batchUpdate L T M i g x b) :=
      (batchUpdate_measurable hg L T M i).comp measurable_prodMk_left
    have hF : Measurable F := by
      have hr := (run_measurable hg L T M n (i + 1)).comp
        ((hnext.comp measurable_fst).prodMk measurable_snd)
      exact (A.continuous.measurable.comp (hr.sub measurable_const)).norm.pow_const 2
    have hstep := batch_update_energy hg H B u x L T M i
      (hgi x) (hg2 x) (hmean x) (hvar x) (hC i) (by
        intro e
        simpa only [B, ContinuousLinearMap.comp_apply, hn] using hnoise i hi hiT e)
    have hG : Integrable G (Measure.pi fun _ : Fin m => p) := hstep.1.add (integrable_const S)
    have hfiber (b : Fin m → Ω) := ih (i + 1) (by omega) (by omega) (batchUpdate L T M i g x b)
    have hprod := StochasticConvexQuadratic.nonnegative_product_control hF
      (fun z => sq_nonneg _) (fun b => (hfiber b).1) hG (fun b => (hfiber b).2)
    have hsplit := StochasticGeneralized.splitStream_preserving p m
    have he : (fun ξ => ‖A (run L T M g (n + 1) i x ξ - u)‖ ^ 2) =
        F ∘ StochasticGeneralized.splitStream m := rfl
    rw [he]
    refine ⟨hsplit.integrable_comp_of_integrable hprod.1, ?_⟩
    simp only [Function.comp_def]
    rw [hsplit.integral_comp' F]
    calc
      _ ≤ ∫ b, G b ∂Measure.pi (fun _ : Fin m => p) := hprod.2
      _ = (∫ b, ‖B (batchUpdate L T M i g x b - u)‖ ^ 2
          ∂Measure.pi (fun _ : Fin m => p)) + S := by
        rw [show G = fun b => ‖B (batchUpdate L T M i g x b - u)‖ ^ 2 + S from rfl,
          integral_add hstep.1 (integrable_const S)]
        simp [m]
      _ ≤ (‖B (x - u - (1 / (L * root T i)) • H (x - u))‖ ^ 2 +
          C i * σ ^ 2 / batch T M i) + S := add_le_add hstep.2 (le_refl S)
      _ = _ := by
        rw [Finset.sum_eq_sum_Ico_succ_bot (show i < T + 1 by omega)]
        simp only [propagator, ContinuousLinearMap.comp_apply, sub_apply,
          ContinuousLinearMap.id_apply, smul_apply, B, S]
        ring

end OracleTemplate.BatchedChebyshev
