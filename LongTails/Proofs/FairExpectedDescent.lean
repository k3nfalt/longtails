import LongTails.Proofs.FairReachableBounds
import LongTails.Proofs.MixedNoiseSelectors

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory

variable {E Ω Ξ : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] [MeasurableSpace Ξ]

lemma trajectory_expected_descent (cfg : Config) (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hη : 0 ≤ cfg.η) {f : E → ℝ} {F : E → E} {L Δ e : ℝ}
    (hL : 0 < L) (hΔ : 0 ≤ Δ) (hF : ∀ x, HasGradientAt f (F x) x)
    (hFm : Measurable F) (hLip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E)
    (hgap : ∀ x, f x0 - f x ≤ Δ)
    (hG : Real.sqrt (2 * L * Δ) + L * cfg.T * cfg.η ≤ cfg.G)
    (P : Measure (ℕ → Fin cfg.m → Ω)) [IsProbabilityMeasure P]
    (herr : ∀ t < cfg.T,
      Integrable (fun ξ => ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖) P ∧
        (∫ ξ, ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖ ∂P) ≤ e) :
    (∀ t < cfg.T, Integrable (fun ξ => ‖F (trajectory cfg g x0 ξ t).1‖) P) ∧
    cfg.η * (∑ t ∈ Finset.range cfg.T, ∫ ξ, ‖F (trajectory cfg g x0 ξ t).1‖ ∂P) ≤
      Δ + 2 * cfg.η * cfg.T * e + cfg.T * L * cfg.η ^ 2 / 2 := by
  have hi : ∀ t < cfg.T, Integrable (fun ξ => ‖F (trajectory cfg g x0 ξ t).1‖) P := by
    intro t ht
    apply Integrable.of_bound (hFm.comp (measurable_trajectory cfg hm hR hg x0 t).fst).norm.aestronglyMeasurable cfg.G
    filter_upwards [] with ξ
    simpa only [Real.norm_eq_abs, abs_norm, Function.comp_apply] using
      trajectory_gradient_bound cfg hη hL hΔ hF hLip g x0 hgap hG ξ ht.le
  refine ⟨hi, ?_⟩
  have hgSum : Integrable (fun ξ => ∑ t ∈ Finset.range cfg.T, ‖F (trajectory cfg g x0 ξ t).1‖) P :=
    integrable_finsetSum _ (fun t ht => hi t (Finset.mem_range.mp ht))
  have heSum : Integrable (fun ξ => ∑ t ∈ Finset.range cfg.T,
      ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖) P :=
    integrable_finsetSum _ (fun t ht => (herr t (Finset.mem_range.mp ht)).1)
  have hpw : ∀ ξ, cfg.η * (∑ t ∈ Finset.range cfg.T, ‖F (trajectory cfg g x0 ξ t).1‖) ≤
      Δ + 2 * cfg.η * (∑ t ∈ Finset.range cfg.T,
        ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖) +
          cfg.T * L * cfg.η ^ 2 / 2 := by
    intro ξ
    have hd := path_descent_sum hL.le hη hF hLip
      (fun t => (trajectory cfg g x0 ξ t).1) (direction cfg g x0 ξ)
      (T := cfg.T) (fun t _ => trajectory_step cfg g x0 ξ t) cfg.T le_rfl
    have hh := hgap (trajectory cfg g x0 ξ cfg.T).1
    simp only [trajectory] at hd
    linarith
  have he := integral_mono (hgSum.const_mul cfg.η)
    (((integrable_const Δ).add (heSum.const_mul (2 * cfg.η))).add
      (integrable_const ((cfg.T : ℝ) * L * cfg.η ^ 2 / 2))) hpw
  simp only [Pi.add_apply] at he
  rw [integral_add (f := fun ξ => Δ + 2 * cfg.η * (∑ t ∈ Finset.range cfg.T,
      ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖))
      (g := fun _ => (cfg.T : ℝ) * L * cfg.η ^ 2 / 2)
      ((integrable_const Δ).add (heSum.const_mul (2 * cfg.η))) (integrable_const _),
    integral_add (f := fun _ => Δ) (g := fun ξ => 2 * cfg.η *
      (∑ t ∈ Finset.range cfg.T, ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖))
      (integrable_const Δ) (heSum.const_mul (2 * cfg.η))] at he
  simp only [integral_const, integral_const_mul, probReal_univ, one_smul] at he
  rw [integral_finsetSum _ (fun t ht => hi t (Finset.mem_range.mp ht)),
    integral_finsetSum _ (fun t ht => (herr t (Finset.mem_range.mp ht)).1)] at he
  have hb : (∑ t ∈ Finset.range cfg.T,
      ∫ ξ, ‖direction cfg g x0 ξ t - F (trajectory cfg g x0 ξ t).1‖ ∂P) ≤ cfg.T * e := by
    calc
      _ ≤ ∑ _t ∈ Finset.range cfg.T, e := Finset.sum_le_sum fun t ht => (herr t (Finset.mem_range.mp ht)).2
      _ = _ := by simp
  nlinarith

lemma uniform_trajectory_bound (cfg : Config) [Nonempty (Fin (max 1 cfg.T))] (hm : 0 < cfg.m) (hR : 0 < cfg.R)
    (hT : 0 < cfg.T) {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    {F : E → E} (hF : Measurable F) (x0 : E)
    (P : Measure (ℕ → Fin cfg.m → Ω)) [IsProbabilityMeasure P] {ε : ℝ}
    (hbound : ∀ ξ t, t < cfg.T → ‖F (trajectory cfg g x0 ξ t).1‖ ≤ cfg.G)
    (hsum : (∑ t ∈ Finset.range cfg.T, ∫ ξ, ‖F (trajectory cfg g x0 ξ t).1‖ ∂P) ≤ cfg.T * ε) :
    Measurable (fun ω : Fin (max 1 cfg.T) × (ℕ → Fin cfg.m → Ω) =>
      (trajectory cfg g x0 ω.2 ω.1.val).1) ∧
    Integrable (fun ω : Fin (max 1 cfg.T) × (ℕ → Fin cfg.m → Ω) =>
      ‖F (trajectory cfg g x0 ω.2 ω.1.val).1‖) ((PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure.prod P) ∧
    (∫ ω : Fin (max 1 cfg.T) × (ℕ → Fin cfg.m → Ω),
      ‖F (trajectory cfg g x0 ω.2 ω.1.val).1‖ ∂((PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure.prod P)) ≤ ε := by
  have hmax : max 1 cfg.T = cfg.T := max_eq_right hT
  have hτ : ∀ τ : Fin (max 1 cfg.T), τ.val < cfg.T := fun τ => by have := τ.isLt; omega
  have hmout : Measurable (fun ω : Fin (max 1 cfg.T) × (ℕ → Fin cfg.m → Ω) =>
      (trajectory cfg g x0 ω.2 ω.1.val).1) :=
    measurable_from_prod_countable_right fun τ => (measurable_trajectory cfg hm hR hg x0 τ.val).fst
  have hi : Integrable (fun ω : Fin (max 1 cfg.T) × (ℕ → Fin cfg.m → Ω) =>
      ‖F (trajectory cfg g x0 ω.2 ω.1.val).1‖) ((PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure.prod P) := by
    apply Integrable.of_bound (hF.comp hmout).norm.aestronglyMeasurable cfg.G
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_norm, Function.comp_apply] using hbound ω.2 ω.1.val (hτ ω.1)
  refine ⟨hmout, hi, ?_⟩
  rw [integral_prod _ hi]
  change (∫ τ : Fin (max 1 cfg.T), (∫ ξ, ‖F (trajectory cfg g x0 ξ τ.val).1‖ ∂P)
    ∂(PMF.uniformOfFintype (Fin (max 1 cfg.T))).toMeasure) ≤ ε
  rw [MixedNoise.integral_uniform_finite, Fintype.card_fin, Fin.sum_univ_eq_sum_range (fun t => ∫ ξ, ‖F (trajectory cfg g x0 ξ t).1‖ ∂P), hmax]
  have hTreal : 0 < (cfg.T : ℝ) := by exact_mod_cast hT
  have he := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hTreal.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hTreal.ne', one_mul] using he

end OracleTemplate.FairVarianceReduction
