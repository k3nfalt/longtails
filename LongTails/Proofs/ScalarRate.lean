import LongTails.Proofs.ScalarLastIterate

open MeasureTheory

namespace OracleTemplate.BoundedScalarConvex

open LongTails.Setups.BoundedScalarConvex

lemma interval_distance {l u x y : ℝ} (hx : x ∈ Set.Icc l u) (hy : y ∈ Set.Icc l u) :
    |x-y| ≤ u-l := by
  apply abs_le.mpr
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

lemma projected_square_step {l u x y η H g : ℝ}
    (hy : y ∈ Set.Icc l u) (hg : |g| ≤ H) :
    (project l u (x-η*g)-y)^2 ≤ (x-y)^2-2*η*((x-y)*g)+η^2*H^2 := by
  have hd := project_distance hy (x-η*g)
  have hsq : (project l u (x-η*g)-y)^2 ≤ (x-η*g-y)^2 := by
    nlinarith [sq_abs (project l u (x-η*g)-y), sq_abs (x-η*g-y),
      abs_nonneg (project l u (x-η*g)-y), abs_nonneg (x-η*g-y)]
  have hg2 : g^2 ≤ H^2 := by nlinarith [sq_abs g, abs_nonneg g]
  have hm := mul_le_mul_of_nonneg_left hg2 (sq_nonneg η)
  nlinarith

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integral_predictable_product {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {C Y : Ω → ℝ} (hC : Measurable[m] C) (hY : Integrable Y μ)
    {B : ℝ} (hB : ∀ᵐ ω ∂μ, ‖C ω‖ ≤ B) :
    (∫ ω, C ω*Y ω ∂μ) = ∫ ω, C ω*μ[Y | m] ω ∂μ := by
  have hCY : Integrable (C*Y) μ := hY.bdd_mul
    (hC.stronglyMeasurable.mono hm).aestronglyMeasurable hB
  have he := condExp_mul_of_stronglyMeasurable_left hC.stronglyMeasurable hCY hY
  have hi := integral_congr_ae he
  rw [integral_condExp hm] at hi
  exact hi

lemma integrable_distance_sq {X : Ω → ℝ} (hX : Measurable X) {l u y : ℝ}
    (hXm : ∀ ω, X ω ∈ Set.Icc l u) (hy : y ∈ Set.Icc l u) :
    Integrable (fun ω => (X ω-y)^2) μ := by
  apply Integrable.of_bound ((hX.sub_const y).pow_const 2).aestronglyMeasurable ((u-l)^2)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hd := interval_distance (hXm ω) hy
  nlinarith [sq_abs (X ω-y), abs_nonneg (X ω-y)]

lemma integral_regret_step {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {F : ℝ → ℝ} {l u η H xstar : ℝ} (hη : 0 ≤ η) (hxstar : xstar ∈ Set.Icc l u)
    (X X' Y : Ω → ℝ) (hX : Measurable[m] X) (hX' : @Measurable Ω ℝ mΩ _ X')
    (hXm : ∀ ω, X ω ∈ Set.Icc l u) (hX'm : ∀ ω, X' ω ∈ Set.Icc l u)
    (hYi : Integrable Y μ) (hY : ∀ᵐ ω ∂μ, |Y ω| ≤ H)
    (hstep : ∀ᵐ ω ∂μ, X' ω = project l u (X ω-η*Y ω))
    (hFi : Integrable (fun ω => F (X ω)-F xstar) μ)
    (hsub : ∀ᵐ ω ∂μ, F (X ω)+μ[Y | m] ω*(xstar-X ω) ≤ F xstar) :
    2*η*(∫ ω, F (X ω)-F xstar ∂μ) ≤
      (∫ ω, (X ω-xstar)^2 ∂μ)-(∫ ω, (X' ω-xstar)^2 ∂μ)+η^2*H^2 := by
  let C := fun ω => X ω-xstar
  have hCm : Measurable[m] C := hX.sub_const xstar
  have hCB : ∀ᵐ ω ∂μ, ‖C ω‖ ≤ u-l := by
    filter_upwards [] with ω
    exact interval_distance (hXm ω) hxstar
  have hCYi : Integrable (C*Y) μ := hYi.bdd_mul
    (hCm.stronglyMeasurable.mono hm).aestronglyMeasurable hCB
  have hCGi : Integrable (C*μ[Y | m]) μ := integrable_condExp.bdd_mul
    (hCm.stronglyMeasurable.mono hm).aestronglyMeasurable hCB
  have hDi := integrable_distance_sq (mΩ := mΩ) (μ := μ) (hX.mono hm le_rfl) hXm hxstar
  have hD'i := integrable_distance_sq (mΩ := mΩ) (μ := μ) hX' hX'm hxstar
  have hs : (∫ ω, F (X ω)-F xstar ∂μ) ≤ ∫ ω, C ω*μ[Y | m] ω ∂μ := by
    apply integral_mono_ae hFi hCGi
    filter_upwards [hsub] with ω hω
    dsimp [C]
    nlinarith
  have he := integral_predictable_product (mΩ := mΩ) (μ := μ) hm hCm hYi hCB
  rw [← he] at hs
  have hp : (∫ ω, (X' ω-xstar)^2 ∂μ) ≤
      ∫ ω, (X ω-xstar)^2-2*η*(C ω*Y ω)+η^2*H^2 ∂μ := by
    apply integral_mono_ae hD'i ((hDi.sub (hCYi.const_mul (2*η))).add (integrable_const _))
    filter_upwards [hY, hstep] with ω hYω hstepω
    rw [hstepω]
    exact projected_square_step hxstar hYω
  have hterm : Integrable (fun ω => 2*η*(C ω*Y ω)) μ := hCYi.const_mul (2*η)
  have hrhs : Integrable (fun ω => (X ω-xstar)^2-2*η*(C ω*Y ω)) μ := hDi.sub hterm
  rw [integral_add hrhs (integrable_const _),
    integral_sub hDi hterm, integral_const_mul] at hp
  simp only [integral_const, probReal_univ, one_smul] at hp
  have hmul := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*η)
  linarith

lemma integral_last_iterate_rate (m : ℕ → MeasurableSpace Ω) (hm : Monotone m)
    (hambient : ∀ n, m n ≤ mΩ) {F : ℝ → ℝ}
    (hF : ConvexOn ℝ Set.univ F) (hFc : Continuous F)
    {l u η H R xstar : ℝ} (hlu : l ≤ u) (hη : 0 < η) (hH : 0 < H)
    (hL : ∀ x y, |F x-F y| ≤ H*|x-y|) (hxstar : xstar ∈ Set.Icc l u)
    (hR : 0 ≤ R) (X Y : ℕ → Ω → ℝ) (hX : ∀ n, Measurable[m n] (X n))
    (hXm : ∀ n ω, X n ω ∈ Set.Icc l u) (hX0 : ∀ ω, |X 0 ω-xstar| ≤ R)
    (hYi : ∀ n, Integrable (Y n) μ) (hY : ∀ n, ∀ᵐ ω ∂μ, |Y n ω| ≤ H)
    (hstep : ∀ n, ∀ᵐ ω ∂μ, X (n+1) ω = project l u (X n ω-η*Y n ω))
    (hsub : ∀ n, ∀ᵐ ω ∂μ, ∀ y, F (X n ω)+μ[Y n | m n] ω*(y-X n ω) ≤ F y)
    (T : ℕ) (hT : 0 < T) :
    (∫ ω, F (X T ω)-F xstar ∂μ) ≤ R^2/(2*η*T)+(25/2)*η*H^2 := by
  let E := fun n => ∫ ω, F (X n ω)-F xstar ∂μ
  let D := fun n => ∫ ω, (X n ω-xstar)^2 ∂μ
  have hXm' : ∀ n, Measurable (X n) := fun n => (hX n).mono (hambient n) le_rfl
  have hFi : ∀ n, Integrable (fun ω => F (X n ω)-F xstar) μ := fun n =>
    (integrable_objective_interval hFc hH.le hL (hXm' n) (hXm n)).sub (integrable_const _)
  have hDi : ∀ n, Integrable (fun ω => (X n ω-xstar)^2) μ := fun n =>
    integrable_distance_sq (hXm' n) (hXm n) hxstar
  have hreg : ∀ n, 2*η*E n ≤ D n-D (n+1)+η^2*H^2 := by
    intro n
    apply integral_regret_step (hambient n) hη.le hxstar (X n) (X (n+1)) (Y n)
      (hX n) (hXm' (n+1)) (hXm n) (hXm (n+1)) (hYi n) (hY n) (hstep n) (hFi n)
    filter_upwards [hsub n] with ω hω
    exact hω xstar
  have hregsum : ∀ n, 2*η*(∑ j ∈ Finset.range n, E j) ≤ D 0-D n+n*η^2*H^2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      have hn := hreg n
      nlinarith
  have hD0 : D 0 ≤ R^2 := by
    have hi := integral_mono_ae (hDi 0) (integrable_const (R^2))
      (Filter.Eventually.of_forall (fun ω => show (X 0 ω-xstar)^2 ≤ R^2 by
        nlinarith [hX0 ω, sq_abs (X 0 ω-xstar), abs_nonneg (X 0 ω-xstar)]))
    simpa using hi
  have hDN : 0 ≤ D T := integral_nonneg (fun ω => sq_nonneg _)
  have hrestart : ∀ s ≤ T, E T ≤ E s+12*η*H^2 := by
    intro s hs
    have hexc := integral_excursion_bound (mΩ := mΩ) (μ := μ)
      (fun n => m (s+n)) (fun a b hab => hm (Nat.add_le_add_left hab s))
      (fun n => hambient (s+n)) hF hFc hlu hη hH hL
      (fun n => X (s+n)) (fun n => Y (s+n))
      (fun n => hX (s+n)) (fun n => hXm (s+n))
      (fun n => hYi (s+n)) (fun n => hY (s+n))
      (fun n => by simpa [Nat.add_assoc] using hstep (s+n))
      (fun n => hsub (s+n)) (T-s)
    simp only [Nat.add_zero, Nat.add_sub_of_le hs] at hexc
    have he : (∫ ω, F (X T ω)-F (X s ω) ∂μ) = E T-E s := by
      dsimp [E]
      rw [← integral_sub (hFi T) (hFi s)]
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    rw [he] at hexc
    linarith
  have havg : (T : ℝ)*E T ≤ (∑ j ∈ Finset.range T, E j)+T*(12*η*H^2) := by
    have hs := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range T) =>
      hrestart j (le_of_lt (Finset.mem_range.mp hj)))
    simpa [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] using hs
  have hsum := hregsum T
  have hmavg := mul_le_mul_of_nonneg_left havg (show 0 ≤ 2*η by positivity)
  have hmult : 2*η*T*E T ≤ R^2+25*η^2*H^2*T := by nlinarith
  have hden : 0 < 2*η*(T : ℝ) := by positivity
  have hdiv : E T ≤ (R^2+25*η^2*H^2*T)/(2*η*T) := (le_div_iff₀ hden).mpr (by nlinarith)
  have he : (R^2+25*η^2*H^2*T)/(2*η*T) = R^2/(2*η*T)+(25/2)*η*H^2 := by
    field_simp
  exact hdiv.trans_eq he

end OracleTemplate.BoundedScalarConvex
