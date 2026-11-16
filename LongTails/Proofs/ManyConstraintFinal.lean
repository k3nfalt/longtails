import LongTails.Proofs.ManyConstraintSuccess
import LongTails.Proofs.MixedNoiseSelectors

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintFinal

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintStochastic
  LongTails.Proofs.ManyConstraintStep LongTails.Proofs.ManyConstraintBall
  LongTails.Proofs.ManyConstraintRun LongTails.Proofs.ManyConstraintInner
  LongTails.Proofs.ManyConstraintEpochEnergy LongTails.Proofs.ManyConstraintMulti
  LongTails.Proofs.ManyConstraintTuning LongTails.Proofs.ManyConstraintLower
  LongTails.Proofs.ManyConstraintAccuracy LongTails.Proofs.ManyConstraintCleanup
  LongTails.Proofs.ManyConstraintSuccess

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

omit [InnerProductSpace ℝ E] in
lemma cleanup_continuous {P : Fin m → E → E} (hP : ∀ j, Continuous (P j)) :
    ∀ (Q : ℕ) (js : Fin Q → Fin m), Continuous (fun p => cleanup P Q p js) := by
  intro Q
  induction Q with
  | zero => intro js; exact continuous_id
  | succ Q ih => intro js; exact (ih _).comp (hP (js 0))

lemma cleanup_budget {κ R δ : ℝ} (hκ : 1 ≤ κ) (hR : 0 < R) (hδ : 0 < δ) :
    (1 - 1 / κ) ^ QT κ R δ * (2 * R) ^ 2 ≤ δ ^ 2 := by
  have hκ0 : 0 < κ := by linarith
  set Q := QT κ R δ
  have h0 : 0 ≤ 1 - 1 / κ := by
    have : 1 / κ ≤ 1 := by rw [div_le_one hκ0]; exact hκ
    linarith
  have h1 : 1 - 1 / κ ≤ Real.exp (-(1 / κ)) := by
    have := Real.add_one_le_exp (-(1 / κ)); linarith
  have h2 : (1 - 1 / κ) ^ Q ≤ Real.exp (-(Q / κ)) := by
    calc (1 - 1 / κ) ^ Q ≤ Real.exp (-(1 / κ)) ^ Q := pow_le_pow_left₀ h0 h1 Q
      _ = Real.exp (-(Q / κ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hX : 0 < 4 * R ^ 2 / δ ^ 2 := by positivity
  have hQ : κ * Real.log (4 * R ^ 2 / δ ^ 2) ≤ Q := Nat.le_ceil _
  have h3 : Real.log (4 * R ^ 2 / δ ^ 2) ≤ Q / κ := by rw [le_div_iff₀ hκ0]; linarith
  have h4 : Real.exp (-(Q / κ)) ≤ δ ^ 2 / (4 * R ^ 2) := by
    calc Real.exp (-(Q / κ)) ≤ Real.exp (-Real.log (4 * R ^ 2 / δ ^ 2)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = δ ^ 2 / (4 * R ^ 2) := by
          rw [Real.exp_neg, Real.exp_log hX, inv_div]
  have h5 : (1 - 1 / κ) ^ Q ≤ δ ^ 2 / (4 * R ^ 2) := h2.trans h4
  have : (2 * R) ^ 2 = 4 * R ^ 2 := by ring
  rw [this]
  calc (1 - 1 / κ) ^ Q * (4 * R ^ 2) ≤ δ ^ 2 / (4 * R ^ 2) * (4 * R ^ 2) :=
        mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = δ ^ 2 := by field_simp

lemma expect_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    (𝔼 x, f x) = 𝔼 a, 𝔼 b, f (a, b) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

lemma integral_uniform_prod {A W : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace W] {ν : Measure W} [IsProbabilityMeasure ν]
    (F : A × W → ℝ) (hF : Integrable F ((PMF.uniformOfFintype A).toMeasure.prod ν)) :
    (∫ x, F x ∂(PMF.uniformOfFintype A).toMeasure.prod ν) = 𝔼 a, ∫ w, F (a, w) ∂ν := by
  rw [integral_prod F hF, OracleTemplate.MixedNoise.integral_uniform_finite,
    Finset.expect_eq_sum_div_card, Finset.card_univ]
  ring

section Main

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable [NeZero m]
variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}
  {K : Fin m → Set E} {P : Fin m → E → E} {κ R ε δ : ℝ} {x0 : E}

abbrev Sd (m S Q : ℕ) := (Fin S → Fin (2 * m) → Fin m) × (Fin Q → Fin m)

noncomputable def out (grad : Ξ → E → E) (P : Fin m → E → E) (k : Knobs E) (S Q : ℕ)
    (seed : (Fin S → Fin k.M → Fin m) × (Fin Q → Fin m)) (ξ : ℕ → Ξ) : E :=
  cleanup P Q (run grad P k S ⟨k.x0, k.x0, k.x0⟩ seed.1 ξ).s seed.2

omit [NeZero m] in
lemma run_s_measurable {k : Knobs E} (H : Hyp law loss grad L σ xs K P κ R k) (S : ℕ)
    (jss : Fin S → Fin k.M → Fin m) :
    Measurable (fun ξ : ℕ → Ξ => (run grad P k S ⟨k.x0, k.x0, k.x0⟩ jss ξ).s) := by
  have hcm : Measurable (fun ξ : ℕ → Ξ => (tri (⟨k.x0, k.x0, k.x0⟩ : St E), ξ)) :=
    measurable_const.prodMk measurable_id
  exact measurable_fst.comp ((run_measurable_joint H S jss).comp hcm)

omit [NeZero m] in
lemma out_measurable {k : Knobs E} (H : Hyp law loss grad L σ xs K P κ R k) (S Q : ℕ)
    (seed : (Fin S → Fin k.M → Fin m) × (Fin Q → Fin m)) :
    Measurable (out grad P k S Q seed) :=
  (cleanup_continuous (fun j => proj_continuous (H.proj j)) Q seed.2).measurable.comp
    (run_s_measurable H S seed.1)

omit [BorelSpace E] [SecondCountableTopology E] [NeZero m] in
lemma run_s_mem {k : Knobs E} (H : Hyp law loss grad L σ xs K P κ R k) (S : ℕ)
    (jss : Fin S → Fin k.M → Fin m) (ξ : ℕ → Ξ) :
    (run grad P k S ⟨k.x0, k.x0, k.x0⟩ jss ξ).s ∈ closedBall k.x0 k.ρ := by
  have hx0 : k.x0 ∈ closedBall k.x0 k.ρ := mem_closedBall_self H.ρ_nonneg
  exact (run_mem H S _ jss ξ hx0 hx0 hx0).1

omit [BorelSpace E] [SecondCountableTopology E] [NeZero m] in
lemma s_near {k : Knobs E} (H : Hyp law loss grad L σ xs K P κ R k) (hρ : k.ρ = R) (S : ℕ)
    (a : Fin S → Fin k.M → Fin m) (ξ : ℕ → Ξ) :
    ‖(run grad P k S ⟨k.x0, k.x0, k.x0⟩ a ξ).s - xs‖ ≤ 2 * R := by
  have hs := run_s_mem H S a ξ
  rw [mem_closedBall, dist_eq_norm, hρ] at hs
  have h0 : ‖k.x0 - xs‖ ≤ R := H.radius
  calc _ = ‖((run grad P k S ⟨k.x0, k.x0, k.x0⟩ a ξ).s - k.x0) + (k.x0 - xs)‖ := by
        congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ 2 * R := by linarith

omit [BorelSpace E] [SecondCountableTopology E] [NeZero m] in
lemma out_near {k : Knobs E} (H : Hyp law loss grad L σ xs K P κ R k) (hρ : k.ρ = R) (S Q : ℕ)
    (seed : (Fin S → Fin k.M → Fin m) × (Fin Q → Fin m)) (ξ : ℕ → Ξ) :
    ‖out grad P k S Q seed ξ - xs‖ ≤ 2 * R ∧
      ‖(run grad P k S ⟨k.x0, k.x0, k.x0⟩ seed.1 ξ).s - xs‖ ≤ 2 * R := by
  have hs := run_s_mem H S seed.1 ξ
  rw [mem_closedBall, dist_eq_norm, hρ] at hs
  have h0 : ‖k.x0 - xs‖ ≤ R := H.radius
  have h2 : ‖(run grad P k S ⟨k.x0, k.x0, k.x0⟩ seed.1 ξ).s - xs‖ ≤ 2 * R := by
    calc _ = ‖((run grad P k S ⟨k.x0, k.x0, k.x0⟩ seed.1 ξ).s - k.x0) + (k.x0 - xs)‖ := by
          congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ 2 * R := by linarith
  exact ⟨(cleanup_fejer H.proj H.feasible Q _ seed.2).trans h2, h2⟩

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [NeZero m] in
lemma infDist_le_of_near {y : E} {r : ℝ} (hxs : xs ∈ ⋂ j, K j) (hy : ‖y - xs‖ ≤ r) :
    Metric.infDist y (⋂ j, K j) ^ 2 ≤ r ^ 2 := by
  have h : Metric.infDist y (⋂ j, K j) ≤ ‖y - xs‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hxs
  exact pow_le_pow_left₀ Metric.infDist_nonneg (h.trans hy) 2

variable [IsProbabilityMeasure law]

set_option maxHeartbeats 1000000 in
lemma final_bounds (H : Hyp law loss grad L σ xs K P κ R (knobs m κ σ ε L R x0)) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hR : 0 < R) (hδ : 0 < δ) :
    let k := knobs m κ σ ε L R x0
    let S := ST m κ σ ε L R
    let Q := QT κ R δ
    let μS := (PMF.uniformOfFintype (Sd m S Q)).toMeasure.prod
      (Measure.infinitePi fun _ : ℕ => law)
    let F := fun w : Sd m S Q × (ℕ → Ξ) => out grad P k S Q w.1 w.2
    Measurable F ∧
    Integrable (fun w => max (objective law loss (F w) - objective law loss xs) 0) μS ∧
    (∫ w, max (objective law loss (F w) - objective law loss xs) 0 ∂μS) ≤ ε ∧
    Integrable (fun w => Metric.infDist (F w) (⋂ j, K j) ^ 2) μS ∧
    (∫ w, Metric.infDist (F w) (⋂ j, K j) ^ 2 ∂μS) ≤ δ ^ 2 := by
  intro k S Q μS F
  set inf := Measure.infinitePi fun _ : ℕ => law
  have hρ : k.ρ = R := rfl
  have hL := H.L_pos
  have hσ := H.σ_nonneg
  set fstar := objective law loss xs
  set C := ⋂ j, K j
  set sF := fun (a : Fin S → Fin (2 * m) → Fin m) (ξ : ℕ → Ξ) =>
    (run grad P k S ⟨k.x0, k.x0, k.x0⟩ a ξ).s
  have hF : Measurable F := measurable_from_prod_countable_right fun seed =>
    out_measurable H S Q seed
  have hobjc := H.reg.objective_continuous hL
  have hdc : Continuous (fun y : E => Metric.infDist y C ^ 2) :=
    (Metric.continuous_infDist_pt C).pow 2
  set B1 := σ * (2 * R) + L / 2 * (2 * R) ^ 2
  have hb1 : ∀ w, ‖max (objective law loss (F w) - fstar) 0‖ ≤ B1 := by
    intro w
    have h := obj_abs_le H (out_near H hρ S Q w.1 w.2).1
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans h) (by positivity)
  have hb2 : ∀ w, ‖Metric.infDist (F w) C ^ 2‖ ≤ (2 * R) ^ 2 := by
    intro w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact infDist_le_of_near H.feasible (out_near H hρ S Q w.1 w.2).1
  have hI1 : Integrable (fun w => max (objective law loss (F w) - fstar) 0) μS :=
    Integrable.of_bound (((hobjc.measurable.comp hF).sub_const _).max measurable_const
      ).aestronglyMeasurable B1 (Filter.Eventually.of_forall hb1)
  have hI2 : Integrable (fun w => Metric.infDist (F w) C ^ 2) μS :=
    Integrable.of_bound (hdc.measurable.comp hF).aestronglyMeasurable _
      (Filter.Eventually.of_forall hb2)
  refine ⟨hF, hI1, ?_, hI2, ?_⟩
  ·
    rw [integral_uniform_prod _ hI1, expect_prod]
    set D := Dgap law loss P σ κ R k xs
    have hDi : ∀ a, Integrable (fun ξ => D (sF a ξ)) inf := by
      intro a
      refine Integrable.of_bound (((Dgap_measurable H).comp (run_s_measurable H S a)
        ).aestronglyMeasurable) (Dbound law loss grad P L σ κ R k xs)
        (Filter.Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs]; exact Dgap_abs_le H (run_s_mem H S a ξ)
    have hpt : ∀ a b, (∫ ξ, max (objective law loss (F ((a, b), ξ)) - fstar) 0 ∂inf) ≤
        11 / 5 * (∫ ξ, D (sF a ξ) ∂inf) + ε / 7 := by
      intro a b
      have hi : Integrable (fun ξ => max (objective law loss (F ((a, b), ξ)) - fstar) 0) inf :=
        Integrable.of_bound (((hobjc.measurable.comp (out_measurable H S Q (a, b))).sub_const _
          ).max measurable_const).aestronglyMeasurable B1
          (Filter.Eventually.of_forall fun ξ => hb1 ((a, b), ξ))
      have hj : Integrable (fun ξ => 11 / 5 * D (sF a ξ) + ε / 7) inf :=
        ((hDi a).const_mul _).add (integrable_const _)
      calc _ ≤ ∫ ξ, (11 / 5 * D (sF a ξ) + ε / 7) ∂inf := by
            refine integral_mono hi hj fun ξ => ?_
            exact obj_point H hκ hε hR (cleanup_move H.proj ⟨xs, H.feasible⟩ Q _ b)
        _ = _ := by
            rw [integral_add ((hDi a).const_mul _) (integrable_const _), integral_const_mul,
              integral_const]
            simp
    have hED := ED_bound H hκ hε hR
    calc (𝔼 a, 𝔼 b, ∫ ξ, max (objective law loss (F ((a, b), ξ)) - fstar) 0 ∂inf)
        ≤ 𝔼 a, 𝔼 _b : Fin Q → Fin m, (11 / 5 * (∫ ξ, D (sF a ξ) ∂inf) + ε / 7) :=
          Finset.expect_le_expect fun a _ => Finset.expect_le_expect fun b _ => hpt a b
      _ = 11 / 5 * (𝔼 a, ∫ ξ, D (sF a ξ) ∂inf) + ε / 7 := by
          simp only [Fintype.expect_const]
          rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
      _ ≤ 11 / 5 * (ε / 16) + ε / 7 := by gcongr; exact hED
      _ ≤ ε := by linarith
  ·
    rw [integral_uniform_prod _ hI2, expect_prod]
    have hne : C.Nonempty := ⟨xs, H.feasible⟩
    have hcf := cleanup_feasibility H.proj hne H.κ_pos hκ H.regular Q
    have hq : 0 ≤ (1 - 1 / κ) ^ Q := by
      have : 1 / κ ≤ 1 := by rw [div_le_one H.κ_pos]; exact hκ
      exact pow_nonneg (by linarith) Q
    have hint : ∀ a b, Integrable (fun ξ => Metric.infDist (F ((a, b), ξ)) C ^ 2) inf :=
      fun a b => Integrable.of_bound ((hdc.measurable.comp (out_measurable H S Q (a, b))
        ).aestronglyMeasurable) _ (Filter.Eventually.of_forall fun ξ => hb2 ((a, b), ξ))
    have hpt : ∀ a, (𝔼 b, ∫ ξ, Metric.infDist (F ((a, b), ξ)) C ^ 2 ∂inf) ≤
        (1 - 1 / κ) ^ Q * (2 * R) ^ 2 := by
      intro a
      rw [expect_integral_comm _ (hint a)]
      have hi2 : Integrable (fun ξ => 𝔼 b, Metric.infDist (F ((a, b), ξ)) C ^ 2) inf := by
        simp only [Finset.expect_eq_sum_div_card]
        exact (integrable_finsetSum _ fun b _ => hint a b).div_const _
      calc _ ≤ ∫ _ξ, (1 - 1 / κ) ^ Q * (2 * R) ^ 2 ∂inf := by
            refine integral_mono hi2 (integrable_const _) fun ξ => ?_
            refine (hcf (sF a ξ)).trans ?_
            exact mul_le_mul_of_nonneg_left
              (infDist_le_of_near H.feasible (s_near H hρ S a ξ)) hq
        _ = _ := by simp
    calc (𝔼 a, 𝔼 b, ∫ ξ, Metric.infDist (F ((a, b), ξ)) C ^ 2 ∂inf)
        ≤ 𝔼 _a : Fin S → Fin (2 * m) → Fin m, (1 - 1 / κ) ^ Q * (2 * R) ^ 2 :=
          Finset.expect_le_expect fun a _ => hpt a
      _ = (1 - 1 / κ) ^ Q * (2 * R) ^ 2 := Fintype.expect_const _
      _ ≤ δ ^ 2 := cleanup_budget hκ hR hδ

end Main

end LongTails.Proofs.ManyConstraintFinal
