import LongTails.Proofs.HeavyTailedSpectralMoments
import LongTails.Proofs.HeavyTailedProbeGeometry
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.WeakGradientConvolution

open MeasureTheory

namespace LongTails.Proofs.HeavyTailedProductProcess

variable {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω]

def trajectory (step : E → Ω → E) : ℕ → E → (ℕ → Ω) → E
  | 0, v, _ => v
  | n + 1, v, ξ => trajectory step n (step v (ξ 0)) (fun k => ξ (k + 1))

omit [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma trajectory_succ_last (step : E → Ω → E) (n : ℕ) (v : E) (ξ : ℕ → Ω) :
    trajectory step (n + 1) v ξ = step (trajectory step n v ξ) (ξ n) := by
  induction n generalizing v ξ with
  | zero => rfl
  | succ n ih =>
      rw [trajectory, ih]
      rfl

omit [MeasurableSpace Ω] in
lemma trajectory_linearProduct {d : ℕ}
    (B : Ω → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (n : ℕ) (v : EuclideanSpace ℝ (Fin d)) (ξ : ℕ → Ω) :
    trajectory (fun v ω => B ω v) n v ξ =
      HeavyTailedProbeGeometry.linearProduct (fun k => B (ξ k)) n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [trajectory_succ_last, ih]
      rfl

omit [NormedAddCommGroup E] [BorelSpace E] in
lemma trajectory_measurable {step : E → Ω → E}
    (hs : Measurable (Function.uncurry step)) (n : ℕ) :
    Measurable (Function.uncurry (trajectory step n)) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      exact ih.comp ((hs.comp (measurable_fst.prodMk
        ((measurable_pi_apply 0).comp measurable_snd))).prodMk (by fun_prop))

lemma head_tail_preserving (P : Measure Ω) [IsProbabilityMeasure P] :
    MeasurePreserving (fun ξ : ℕ → Ω => (ξ 0, fun k => ξ (k + 1)))
      (Measure.infinitePi fun _ : ℕ => P) (P.prod (Measure.infinitePi fun _ : ℕ => P)) := by
  have h := ((measurePreserving_piUnique (fun _ : Fin 1 => P)).prod
    (MeasurePreserving.id (Measure.infinitePi fun _ : ℕ => P))).comp
      (OracleTemplate.StochasticGeneralized.splitStream_preserving P 1)
  simpa only [Function.comp_def, OracleTemplate.StochasticGeneralized.splitStream,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, MeasurableEquiv.piUnique,
    Equiv.piUnique_apply, Prod.map_apply, id_eq, Fin.default_eq_zero, Fin.val_zero, Nat.add_comm] using h

lemma trajectory_moment_control (P : Measure Ω) [IsProbabilityMeasure P]
    {step : E → Ω → E} (hs : Measurable (Function.uncurry step)) {p c : ℝ}
    (hc : 0 ≤ c)
    (hi : ∀ v, Integrable (fun ω => ‖step v ω‖ ^ p) P)
    (hb : ∀ v, (∫ ω, ‖step v ω‖ ^ p ∂P) ≤ c * ‖v‖ ^ p) (n : ℕ) (v : E) :
    Integrable (fun ξ => ‖trajectory step n v ξ‖ ^ p) (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, ‖trajectory step n v ξ‖ ^ p ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
        c ^ n * ‖v‖ ^ p := by
  induction n generalizing v with
  | zero => simp [trajectory]
  | succ n ih =>
      let F : Ω × (ℕ → Ω) → ℝ := fun z => ‖trajectory step n (step v z.1) z.2‖ ^ p
      have hF : Measurable F := by
        exact ((trajectory_measurable hs n).comp
          (((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk measurable_snd)).norm.pow_const _
      have hcontrol := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
        hF.stronglyMeasurable (fun z => Real.rpow_nonneg (norm_nonneg _) _)
        (Filter.Eventually.of_forall (fun ω => (ih (step v ω)).1))
        ((hi v).const_mul (c ^ n))
        (Filter.Eventually.of_forall (fun ω => (ih (step v ω)).2))
      have hsplit := head_tail_preserving P
      have heq : (fun ξ => ‖trajectory step (n + 1) v ξ‖ ^ p) =
          F ∘ (fun ξ : ℕ → Ω => (ξ 0, fun k => ξ (k + 1))) := rfl
      rw [heq]
      refine ⟨hsplit.integrable_comp_of_integrable hcontrol.1, ?_⟩
      have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P) hsplit.measurable.aemeasurable hF.aestronglyMeasurable
      rw [hsplit.map_eq] at heint
      change (∫ ξ, F (ξ 0, fun k => ξ (k + 1)) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
      rw [← heint]
      have hlast := mul_le_mul_of_nonneg_left (hb v) (pow_nonneg hc n)
      rw [integral_const_mul] at hcontrol
      calc
        _ ≤ c ^ n * (c * ‖v‖ ^ p) := hcontrol.2.trans hlast
        _ = c ^ (n + 1) * ‖v‖ ^ p := by rw [pow_succ]; ring

section VectorMean

variable [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma trajectory_integrable (P : Measure Ω) [IsProbabilityMeasure P]
    {step : E → Ω → E} (hs : Measurable (Function.uncurry step)) {p c : ℝ}
    (hp : 1 ≤ p) (hc : 0 ≤ c)
    (hi : ∀ v, Integrable (fun ω => ‖step v ω‖ ^ p) P)
    (hb : ∀ v, (∫ ω, ‖step v ω‖ ^ p ∂P) ≤ c * ‖v‖ ^ p) (n : ℕ) (v : E) :
    Integrable (trajectory step n v) (Measure.infinitePi fun _ : ℕ => P) := by
  have hm : AEStronglyMeasurable (trajectory step n v) (Measure.infinitePi fun _ : ℕ => P) :=
    ((trajectory_measurable hs n).comp measurable_prodMk_left).aestronglyMeasurable
  apply (integrable_norm_iff hm).mp
  have hpow := integrable_norm_rpow_of_le hm (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 0 ≤ p) hp (trajectory_moment_control P hs hc hi hb n v).1
  simpa using hpow

lemma trajectory_mean (P : Measure Ω) [IsProbabilityMeasure P]
    {step : E → Ω → E} (hs : Measurable (Function.uncurry step)) (M : E →L[ℝ] E)
    (hi : ∀ v, Integrable (step v) P) (hm : ∀ v, (∫ ω, step v ω ∂P) = M v)
    (htraj : ∀ n v, Integrable (trajectory step n v) (Measure.infinitePi fun _ : ℕ => P))
    (n : ℕ) (v : E) :
    (∫ ξ, trajectory step n v ξ ∂Measure.infinitePi (fun _ : ℕ => P)) = (M ^ n) v := by
  induction n generalizing v with
  | zero => simp [trajectory]
  | succ n ih =>
      let F : Ω × (ℕ → Ω) → E := fun z => trajectory step n (step v z.1) z.2
      have hF : Measurable F := (trajectory_measurable hs n).comp
        (((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk measurable_snd)
      have hsplit := head_tail_preserving P
      have hFi : Integrable F (P.prod (Measure.infinitePi fun _ : ℕ => P)) :=
        (hsplit.integrable_comp hF.aestronglyMeasurable).mp (htraj (n + 1) v)
      have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
        hsplit.measurable.aemeasurable hF.aestronglyMeasurable
      rw [hsplit.map_eq] at heint
      change (∫ ξ, F (ξ 0, fun k => ξ (k + 1)) ∂Measure.infinitePi (fun _ : ℕ => P)) = _
      rw [← heint, integral_prod F hFi]
      simp only [F, ih]
      rw [(M ^ n).integral_comp_comm (hi v), hm v, pow_succ]
      rfl

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] in
lemma power_apply_eigenvector (M : E →L[ℝ] E) {u : E} {a : ℝ}
    (hu : M u = a • u) (n : ℕ) : (M ^ n) u = a ^ n • u := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp, hu, map_smul, ih, smul_smul, pow_succ]
      congr 1
      ring

lemma trajectory_norm_mean_lower (P : Measure Ω) [IsProbabilityMeasure P]
    {step : E → Ω → E} (hs : Measurable (Function.uncurry step)) (M : E →L[ℝ] E)
    (hi : ∀ v, Integrable (step v) P) (hm : ∀ v, (∫ ω, step v ω ∂P) = M v)
    (htraj : ∀ n v, Integrable (trajectory step n v) (Measure.infinitePi fun _ : ℕ => P))
    {u : E} {a : ℝ} (hu : M u = a • u) (hunit : ‖u‖ = 1) (ha : 0 ≤ a) (n : ℕ) :
    a ^ n ≤ ∫ ξ, ‖trajectory step n u ξ‖ ∂Measure.infinitePi (fun _ : ℕ => P) := by
  have hb := norm_integral_le_integral_norm (μ := Measure.infinitePi fun _ : ℕ => P) (trajectory step n u)
  rw [trajectory_mean P hs M hi hm htraj, power_apply_eigenvector M hu, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha n), hunit, mul_one] at hb
  exact hb

lemma trajectory_growth_probability (P : Measure Ω) [IsProbabilityMeasure P]
    {step : E → Ω → E} (hs : Measurable (Function.uncurry step)) (M : E →L[ℝ] E)
    (hi : ∀ v, Integrable (step v) P) (hm : ∀ v, (∫ ω, step v ω ∂P) = M v)
    {p q c a : ℝ} (hpq : p.HolderConjugate q) (hc : 0 ≤ c) (ha : 0 < a)
    (hpi : ∀ v, Integrable (fun ω => ‖step v ω‖ ^ p) P)
    (hpb : ∀ v, (∫ ω, ‖step v ω‖ ^ p ∂P) ≤ c * ‖v‖ ^ p)
    {u : E} (hu : M u = a • u) (hunit : ‖u‖ = 1) (n : ℕ)
    (hsmall : c ^ n ≤ (2 * a ^ n) ^ p) :
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | a ^ n / 2 ≤ ‖trajectory step n u ξ‖} ≥ (1 / 4 : ℝ) ^ q := by
  let Q := Measure.infinitePi fun _ : ℕ => P
  let X : (ℕ → Ω) → ℝ := fun ξ => ‖trajectory step n u ξ‖
  have hX : Measurable X := ((trajectory_measurable hs n).comp measurable_prodMk_left).norm
  have htraj := trajectory_integrable P hs hpq.lt.le hc hpi hpb
  have hXi : Integrable X Q := (htraj n u).norm
  have hcontrol := trajectory_moment_control P hs hc hpi hpb n u
  have hXp : Integrable (fun ξ => ‖X ξ‖ ^ p) Q := by
    simpa only [X, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hcontrol.1
  have hLp : MemLp X (ENNReal.ofReal p) Q := by
    apply (integrable_norm_rpow_iff hX.aestronglyMeasurable (by simp [hpq.pos]) (by simp)).mp
    simpa only [ENNReal.toReal_ofReal hpq.nonneg] using hXp
  have hmean := trajectory_norm_mean_lower P hs M hi hm htraj hu hunit ha.le n
  have hmoment : (∫ ξ, X ξ ^ p ∂Q) ≤ (2 * a ^ n) ^ p := by
    have hh := hcontrol.2
    rw [hunit, Real.one_rpow, mul_one] at hh
    exact hh.trans hsmall
  have hroot : (∫ ξ, X ξ ^ p ∂Q) ^ (1 / p) ≤ 2 * a ^ n := by
    have hh := Real.rpow_le_rpow (integral_nonneg (fun ξ => Real.rpow_nonneg (norm_nonneg _) p))
      hmoment (one_div_nonneg.mpr hpq.nonneg)
    rw [← Real.rpow_mul (by positivity : 0 ≤ 2 * a ^ n),
      mul_one_div_cancel hpq.pos.ne', Real.rpow_one] at hh
    exact hh
  exact HeavyTailedMomentBounds.positive_tail_of_moments hpq hLp hXi
    (fun ξ => norm_nonneg _) (pow_pos ha n)
    (measurableSet_le measurable_const hX) (fun ξ hξ => le_of_not_ge hξ) hmean hroot

end VectorMean

end LongTails.Proofs.HeavyTailedProductProcess
