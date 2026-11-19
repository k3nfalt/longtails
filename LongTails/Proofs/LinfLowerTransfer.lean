import LongTails.Proofs.LinfEmbedding
import LongTails.Proofs.Execution
import LongTails.Setups.HighDimensionalSeparableNoiseLinfSmooth
import LongTails.Setups.HighDimensionalAbcNoiseNonconvex
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.NumberTheory.Bertrand
import LongTails.Theorems.AbcNoiseLowerBound

open MeasureTheory Finset OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.LinfLowerTransfer

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace

open LongTails.Proofs.KhintchineSignFamily LongTails.Proofs.LinfEmbedding

abbrev Sp (n : ℕ) := EuclideanSpace ℝ (Fin n)

section Lift

variable {p D d : ℕ} [Fact p.Prime] (κ : Coeff p ↪ Fin d) (x0 : Sp d)

noncomputable def lift (h : Sp D → ℝ) : Sp d → ℝ := fun x => h (down κ (x - x0))

noncomputable def liftOracle {Ω : Type} (g : Sp D → Ω → Sp D) : Sp d → Ω → Sp d :=
  fun x ω => up κ (g (down κ (x - x0)) ω)

lemma lift_hasGradientAt {h : Sp D → ℝ} {v : Sp D} {x : Sp d}
    (hg : HasGradientAt h v (down κ (x - x0))) :
    HasGradientAt (lift κ x0 h) (up κ v) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hg ⊢
  have hlin : HasFDerivAt (fun y : Sp d => down (D := D) κ (y - x0)) (down κ) x := by
    have := (down (D := D) κ).hasFDerivAt (x := x - x0)
    exact this.comp x ((hasFDerivAt_id x).sub_const x0) |>.congr_fderiv (by ext; simp)
  have hc := hg.comp x hlin
  have hf : lift κ x0 h = h ∘ fun y => down (D := D) κ (y - x0) := rfl
  rw [hf]
  convert hc using 1
  ext y
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply]
  exact inner_up κ v y

lemma lift_gradient {h : Sp D → ℝ} (hg : ∀ u, HasGradientAt h (gradient h u) u) (x : Sp d) :
    gradient (lift κ x0 h) x = up κ (gradient h (down κ (x - x0))) :=
  (lift_hasGradientAt κ x0 (hg _)).gradient

end Lift

section Simulation

noncomputable def pointOracle {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (G : Sp n → Ω → Sp n) : Oracle (Sp n) (Sp n) where
  Seed := fun _ => Ω
  law := P
  answer := fun _ (_, x) ω => G x ω

variable {p D d : ℕ} [Fact p.Prime] (κ : Coeff p ↪ Fin d) (x0 : Sp d)

noncomputable def simulate (A : Algorithm (Sp d) (Sp d) (Sp d)) : Algorithm (Sp D) (Sp D) (Sp D) where
  Seed := A.Seed
  seedSpace := A.seedSpace
  law := A.law
  State := A.State
  initial := A.initial
  query s := ((A.query s).1, down κ ((A.query s).2 - x0))
  update s r := A.update s (up κ r)
  output s := down κ (A.output s - x0)

lemma execute_simulate (A : Algorithm (Sp d) (Sp d) (Sp d)) (g : Sp D → ℝ → Sp D)
    (P : ProbabilityMeasure (ℕ → ℝ)) (K : ℕ) (seed : A.Seed) (ξ : ℕ → ℝ) :
    execute (pointOracle P g) (simulate κ x0 A) (fun _ => K) seed ξ =
      down κ (execute (pointOracle P (liftOracle κ x0 g)) A (fun _ => K) seed ξ - x0) := by
  have h1 := execute_indexed_of_answer (pointOracle P g) (simulate (D := D) κ x0 A) K seed ξ
    (fun t query => g query.2 (ξ t)) (fun _ query => by cases query; rfl)
  have h2 := execute_indexed_of_answer (pointOracle P (liftOracle κ x0 g)) A K seed ξ
    (fun t query => liftOracle κ x0 g query.2 (ξ t)) (fun _ query => by cases query; rfl)
  rw [h1, h2]
  rfl

end Simulation

section Noise

variable {p D d : ℕ} [Fact p.Prime] (κ : Coeff p ↪ Fin d) (hDp : D + 4 ≤ p) (hp2 : p ≠ 2)
include hDp hp2

omit [Fact (Nat.Prime p)] hDp hp2 in
lemma sum_sqrt_le_sqrt_card {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, Real.sqrt (a i) ≤ Real.sqrt (Fintype.card ι * ∑ i, a i) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ => (1 : ℝ))
    (fun i => Real.sqrt (a i))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Real.sq_sqrt (ha _)] at hcs
  have hS : 0 ≤ ∑ i, Real.sqrt (a i) := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  rw [← Real.sqrt_sq hS]
  exact Real.sqrt_le_sqrt hcs

lemma noise_sum_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (ξ : Ω → Sp D) (hξ : Measurable ξ) (hint : Integrable (fun ω => ‖ξ ω‖ ^ 2) μ) :
    ∑ r, Real.sqrt (∫ ω, (up κ (ξ ω) r) ^ 2 ∂μ) ≤ Real.sqrt (∫ ω, ‖ξ ω‖ ^ 2 ∂μ) := by
  have hp4 : (0 : ℝ) < (p : ℝ) ^ 4 := by have := (Fact.out : p.Prime).pos; positivity
  have hzero : ∀ r : Fin d, (∀ c, κ c ≠ r) →
      Real.sqrt (∫ ω, (up κ (ξ ω) r) ^ 2 ∂μ) = 0 := by
    intro r hr
    simp [up_apply_of_not_mem κ _ r hr]
  rw [sum_over_kappa κ _ hzero]
  have hcoord : ∀ c : Coeff p, Real.sqrt (∫ ω, (up κ (ξ ω) (κ c)) ^ 2 ∂μ) =
      (1 / (p : ℝ) ^ 4) * Real.sqrt (∫ ω, proj c (fun i => ξ ω i) ^ 2 ∂μ) := by
    intro c
    simp only [up_apply_kappa, mul_pow]
    rw [integral_const_mul, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  simp only [hcoord, ← Finset.mul_sum]
  have hmeasc : ∀ c : Coeff p, Measurable (fun ω => proj c (fun i => ξ ω i)) := by
    intro c
    unfold proj
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp ((PiLp.continuous_ofLp 2 _).measurable.comp hξ)).mul_const _
  have hintc : ∀ c : Coeff p, Integrable (fun ω => proj c (fun i => ξ ω i) ^ 2) μ := by
    intro c
    refine (hint.const_mul (A1 p)).mono' ((hmeasc c).pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact proj_sq_le hDp hp2 (ξ ω) c
  have hsum : ∑ c : Coeff p, ∫ ω, proj c (fun i => ξ ω i) ^ 2 ∂μ =
      A1 p * ∫ ω, ‖ξ ω‖ ^ 2 ∂μ := by
    rw [← integral_finsetSum _ (fun c _ => hintc c), ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
      second_moment_euclid hDp hp2 (ξ ω))
  have hcs := sum_sqrt_le_sqrt_card (fun c : Coeff p => ∫ ω, proj c (fun i => ξ ω i) ^ 2 ∂μ)
    (fun c => integral_nonneg fun ω => sq_nonneg _)
  rw [hsum, card_coeff (p := p)] at hcs
  have hE : 0 ≤ ∫ ω, ‖ξ ω‖ ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hA := A1_le_pow (p := p) (Fact.out : p.Prime).one_lt.le
  have hA0 : 0 ≤ A1 p := by
    unfold A1
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
    have : (0 : ℝ) ≤ (p : ℝ) ^ 3 := by positivity
    nlinarith
  have hbound : Real.sqrt ((p : ℝ) ^ 4 * (A1 p * ∫ ω, ‖ξ ω‖ ^ 2 ∂μ)) ≤
      (p : ℝ) ^ 4 * Real.sqrt (∫ ω, ‖ξ ω‖ ^ 2 ∂μ) := by
    have hle : A1 p * ∫ ω, ‖ξ ω‖ ^ 2 ∂μ ≤ (p : ℝ) ^ 4 * ∫ ω, ‖ξ ω‖ ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_right hA hE
    calc Real.sqrt ((p : ℝ) ^ 4 * (A1 p * ∫ ω, ‖ξ ω‖ ^ 2 ∂μ))
        ≤ Real.sqrt ((p : ℝ) ^ 4 * ((p : ℝ) ^ 4 * ∫ ω, ‖ξ ω‖ ^ 2 ∂μ)) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle hp4.le)
      _ = (p : ℝ) ^ 4 * Real.sqrt (∫ ω, ‖ξ ω‖ ^ 2 ∂μ) := by
          rw [← mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_mul_self hp4.le]
  calc (1 / (p : ℝ) ^ 4) * ∑ c : Coeff p, Real.sqrt (∫ ω, proj c (fun i => ξ ω i) ^ 2 ∂μ)
      ≤ (1 / (p : ℝ) ^ 4) * ((p : ℝ) ^ 4 * Real.sqrt (∫ ω, ‖ξ ω‖ ^ 2 ∂μ)) := by
        gcongr
        exact hcs.trans hbound
    _ = _ := by rw [← mul_assoc, one_div_mul_cancel hp4.ne', one_mul]

end Noise

section Admissible

open LongTails.Setups

variable {p D : ℕ} [Fact p.Prime] (hDp : D + 4 ≤ p) (hp2 : p ≠ 2)
include hDp hp2

theorem lift_admissible (q : SeparableNoiseLinfSmooth.Params)
    (κ : Coeff p ↪ Fin q.d) (h : Sp D → ℝ) (g : Sp D → q.Ω → Sp D)
    (pm : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)) (fstar : ℝ)
    (hiid : StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → q.Ω) => ξ k)
      (pm : Measure q.Ω) (P : Measure (ℕ → q.Ω)))
    (hgrad : ∀ u, HasGradientAt h (gradient h u) u)
    (hlip : ∀ u v, ‖gradient h u - gradient h v‖ ≤ q.L * ‖u - v‖)
    (hlow : ∀ u, fstar ≤ h u) (hinf : ∀ η, 0 < η → ∃ u, h u < fstar + η)
    (hgap : h 0 - fstar ≤ q.Δ) (hmeas : Measurable (Function.uncurry g))
    (hint : ∀ u, Integrable (g u) pm) (hmean : ∀ u, ∫ ω, g u ω ∂pm = gradient h u)
    (hvarint : ∀ u, Integrable (fun ω => ‖g u ω - gradient h u‖ ^ 2) pm)
    (hvar : ∀ u, ∫ ω, ‖g u ω - gradient h u‖ ^ 2 ∂pm ≤ q.S ^ 2) (hS : 0 ≤ q.S)
    (hL : 0 ≤ q.L) :
    SeparableNoiseLinfSmooth.spec.admissible q (lift κ q.x0 h)
      (pointOracle P (liftOracle κ q.x0 g)) := by
  have hG := lift_gradient κ q.x0 hgrad
  refine ⟨liftOracle κ q.x0 g, pm, P, fstar, hiid, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [hG]
    exact lift_hasGradientAt κ q.x0 (hgrad _)
  · intro x y r hxy
    simp only [hG]
    have hsub : ∀ i, up κ (gradient h (down κ (x - q.x0))) i - up κ (gradient h (down κ (y - q.x0))) i
        = up κ (gradient h (down κ (x - q.x0)) - gradient h (down κ (y - q.x0))) i := by
      intro i; simp [map_sub]
    simp only [hsub]
    refine (l1_up_le κ hDp hp2 _).trans ?_
    refine (hlip _ _).trans ?_
    have hd : down (D := D) κ (x - q.x0) - down κ (y - q.x0) = down κ (x - y) := by
      rw [← map_sub]; congr 1; abel
    rw [hd]
    exact mul_le_mul_of_nonneg_left (down_norm_le κ hDp hp2 _ r (fun i => by
      have := hxy i; simpa using this)) hL
  · intro x; exact hlow _
  · intro η hη
    obtain ⟨u, hu⟩ := hinf η hη
    have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    have hA : 0 < A1 p := by
      unfold A1
      have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
      have : 0 < (p : ℝ) - 1 := by linarith
      positivity
    refine ⟨q.x0 + ((p : ℝ) ^ 8 / A1 p) • up κ u, ?_⟩
    have : down κ (q.x0 + ((p : ℝ) ^ 8 / A1 p) • up κ u - q.x0) = u := by
      rw [add_sub_cancel_left, map_smul, down_up κ hDp hp2, smul_smul]
      rw [show (p : ℝ) ^ 8 / A1 p * (A1 p / (p : ℝ) ^ 8) = 1 by field_simp, one_smul]
    simp only [lift, this]
    exact hu
  · simp only [lift, sub_self, map_zero]
    exact hgap
  · have hc : Measurable (fun z : Sp q.d × q.Ω => down (D := D) κ (z.1 - q.x0)) :=
      (down (D := D) κ).continuous.measurable.comp (measurable_fst.sub_const q.x0)
    exact (up κ).continuous.measurable.comp (hmeas.comp (hc.prodMk measurable_snd))
  · intro x
    exact (up κ).integrable_comp (hint _)
  · intro x
    simp only [hG]
    simp only [liftOracle]
    rw [(up κ).integral_comp_comm (hint _), hmean]
  · intro x i
    simp only [hG]
    have hm : Measurable (g (down κ (x - q.x0))) := hmeas.comp (measurable_const.prodMk measurable_id)
    refine (hvarint (down κ (x - q.x0))).mono' ?_ ?_
    · have hci : Continuous (fun z : Sp q.d => z i) := (EuclideanSpace.proj i).continuous
      exact (((hci.measurable.comp ((up κ).continuous.measurable.comp hm)).sub_const _).pow_const
        2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      simp only [liftOracle]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have e : up κ (g (down κ (x - q.x0)) ω) i - up κ (gradient h (down κ (x - q.x0))) i =
          up κ (g (down κ (x - q.x0)) ω - gradient h (down κ (x - q.x0))) i := by
        simp [map_sub]
      rw [e, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (up_coord_abs_le κ hDp hp2 _ i) 2
  · intro x
    simp only [hG]
    set u := down (D := D) κ (x - q.x0)
    have hm : Measurable (g u) := hmeas.comp (measurable_const.prodMk measurable_id)
    have e : ∀ (i : Fin q.d) (ω : q.Ω), liftOracle κ q.x0 g x ω i - up κ (gradient h u) i =
        up κ (g u ω - gradient h u) i := by
      intro i ω; simp [liftOracle, u, map_sub]
    simp only [e]
    refine (noise_sum_le κ hDp hp2 (pm : Measure q.Ω) (fun ω => g u ω - gradient h u)
      (hm.sub_const _) (hvarint u)).trans ?_
    calc Real.sqrt (∫ ω, ‖g u ω - gradient h u‖ ^ 2 ∂(pm : Measure q.Ω))
        ≤ Real.sqrt (q.S ^ 2) := Real.sqrt_le_sqrt (hvar u)
      _ = q.S := Real.sqrt_sq hS

end Admissible

section Assembly

open LongTails.Setups

noncomputable def ratio (q : HighDimensionalSeparableNoiseLinfSmooth.Params) : ℝ :=
  q.L * q.Δ * (1 + q.S ^ 2 / q.ε ^ 2) / q.ε ^ 2

noncomputable def dim (q : HighDimensionalSeparableNoiseLinfSmooth.Params) : ℕ :=
  ⌈2 ^ 40 * (1 + ratio q) ^ 4⌉₊

noncomputable def euclidParams (q : HighDimensionalSeparableNoiseLinfSmooth.Params) :
    HighDimensionalAbcNoiseNonconvex.Params where
  d := dim q
  L := q.L
  A := 0
  B := 0
  C := q.S ^ 2
  Δ := q.Δ
  ε := 3 * q.ε
  x0 := 0

noncomputable def lowerBudget (q : HighDimensionalSeparableNoiseLinfSmooth.Params) : ℕ :=
  ⌊q.L * q.Δ * (1 + q.S ^ 2 / q.ε ^ 2) / (2 ^ 60 * q.ε ^ 2)⌋₊

variable (q : HighDimensionalSeparableNoiseLinfSmooth.Params)
  (hv : HighDimensionalSeparableNoiseLinfSmooth.spec.valid q)
include hv

lemma ratio_nonneg : 0 ≤ ratio q := by
  obtain ⟨hL, hS, hε, hreg, -⟩ := hv
  have hLΔ : 0 ≤ q.L * q.Δ := le_trans (by positivity) hreg
  unfold ratio; positivity

lemma euclid_ratio_le : q.L * q.Δ * (1 + 0 + 0 * q.Δ / (3 * q.ε) ^ 2 + q.S ^ 2 / (3 * q.ε) ^ 2) /
    (3 * q.ε) ^ 2 ≤ ratio q := by
  obtain ⟨hL, hS, hε, hreg, -⟩ := hv
  have hLΔ : 0 ≤ q.L * q.Δ := le_trans (by positivity) hreg
  unfold ratio
  have he : (0 : ℝ) < q.ε ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) he]
  have h1 : q.S ^ 2 / (3 * q.ε) ^ 2 ≤ q.S ^ 2 / q.ε ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) he (by nlinarith)
  have h2 : 1 + 0 + 0 * q.Δ / (3 * q.ε) ^ 2 + q.S ^ 2 / (3 * q.ε) ^ 2 ≤ 1 + q.S ^ 2 / q.ε ^ 2 := by
    simp only [zero_mul, zero_div, add_zero]; linarith
  have h3 : 0 ≤ 1 + q.S ^ 2 / q.ε ^ 2 := by positivity
  have h4 : q.L * q.Δ * (1 + 0 + 0 * q.Δ / (3 * q.ε) ^ 2 + q.S ^ 2 / (3 * q.ε) ^ 2) ≤
      q.L * q.Δ * (1 + q.S ^ 2 / q.ε ^ 2) := mul_le_mul_of_nonneg_left h2 hLΔ
  have h5 : q.ε ^ 2 ≤ (3 * q.ε) ^ 2 := by nlinarith
  calc q.L * q.Δ * (1 + 0 + 0 * q.Δ / (3 * q.ε) ^ 2 + q.S ^ 2 / (3 * q.ε) ^ 2) * q.ε ^ 2
      ≤ q.L * q.Δ * (1 + q.S ^ 2 / q.ε ^ 2) * q.ε ^ 2 := mul_le_mul_of_nonneg_right h4 he.le
    _ ≤ q.L * q.Δ * (1 + q.S ^ 2 / q.ε ^ 2) * (3 * q.ε) ^ 2 :=
        mul_le_mul_of_nonneg_left h5 (mul_nonneg hLΔ h3)

lemma euclid_valid : HighDimensionalAbcNoiseNonconvex.spec.valid (euclidParams q) := by
  have hr := euclid_ratio_le q hv
  have hr0 := ratio_nonneg q hv
  obtain ⟨hL, hS, hε, hreg, -⟩ := hv
  refine ⟨hL, le_rfl, le_rfl, sq_nonneg _, by simp [euclidParams]; positivity, ?_, ?_⟩
  · simp only [euclidParams]; nlinarith
  · simp only [euclidParams, dim]
    refine le_trans ?_ (Nat.le_ceil _)
    have hLΔ : 0 ≤ q.L * q.Δ := le_trans (by positivity) hreg
    have h0 : 0 ≤ 1 + 0 + 0 * q.Δ / (3 * q.ε) ^ 2 + q.S ^ 2 / (3 * q.ε) ^ 2 := by
      simp only [zero_mul, zero_div, add_zero]; positivity
    have h1 : 0 ≤ 1 + q.L * q.Δ * (1 + 0 + 0 * q.Δ / (3 * q.ε) ^ 2 + q.S ^ 2 / (3 * q.ε) ^ 2) /
        (3 * q.ε) ^ 2 :=
      add_nonneg zero_le_one (div_nonneg (mul_nonneg hLΔ h0) (sq_nonneg _))
    gcongr

lemma budget_le_euclid (b : ℕ) (hb : b ≤ lowerBudget q) :
    b ≤ LongTails.Theorems.AbcNoiseLowerBound.budget (euclidParams q) 0 := by
  refine hb.trans (Nat.floor_mono ?_)
  obtain ⟨hL, hS, hε, hreg, -⟩ := hv
  have hLΔ : 0 ≤ q.L * q.Δ := le_trans (by positivity) hreg
  simp only [euclidParams]
  have he : (0 : ℝ) < q.ε ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hS2 : 0 ≤ q.S ^ 2 / q.ε ^ 2 := by positivity
  have e : q.S ^ 2 / (3 * q.ε) ^ 2 = q.S ^ 2 / q.ε ^ 2 / 9 := by field_simp; ring
  simp only [zero_mul, zero_div, add_zero, e]
  have hk : 0 ≤ q.L * q.Δ * q.ε ^ 2 := by positivity
  nlinarith [mul_nonneg hk hS2]

lemma exists_prime : ∃ p, p.Prime ∧ dim q + 4 ≤ p ∧ p ≠ 2 ∧ 5 ≤ p ∧ p ^ 4 ≤ q.d := by
  have hr0 := ratio_nonneg q hv
  obtain ⟨-, -, -, -, hd⟩ := hv
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (dim q + 3) (by omega)
  have hdim1 : (1 : ℝ) ≤ dim q := by
    unfold dim
    have : (1 : ℝ) ≤ 2 ^ 40 * (1 + ratio q) ^ 4 := by
      have : (1 : ℝ) ≤ (1 + ratio q) ^ 4 := one_le_pow₀ (by linarith)
      nlinarith
    exact this.trans (Nat.le_ceil _)
  have hdim1' : 1 ≤ dim q := by exact_mod_cast hdim1
  refine ⟨p, hp, by omega, by omega, by omega, ?_⟩
  have hdimle : (dim q : ℝ) ≤ 2 ^ 40 * (1 + ratio q) ^ 4 + 1 := by
    unfold dim
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hpR : (p : ℝ) ≤ 2 ^ 42 * (1 + ratio q) ^ 4 := by
    have : (p : ℝ) ≤ 2 * ((dim q : ℝ) + 3) := by exact_mod_cast hle
    have h1 : (1 : ℝ) ≤ (1 + ratio q) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  have hp4 : ((p ^ 4 : ℕ) : ℝ) ≤ 2 ^ 168 * (1 + ratio q) ^ 16 := by
    push_cast
    calc (p : ℝ) ^ 4 ≤ (2 ^ 42 * (1 + ratio q) ^ 4) ^ 4 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hpR 4
      _ = 2 ^ 168 * (1 + ratio q) ^ 16 := by ring
  have : ((p ^ 4 : ℕ) : ℝ) ≤ (q.d : ℝ) := hp4.trans (by unfold ratio at *; exact hd)
  exact_mod_cast this

end Assembly

section Failure

open LongTails.Setups

lemma gradient_continuous_of_lip {n : ℕ} {f : Sp n → ℝ} {L : ℝ}
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) : Continuous (gradient f) := by
  apply LipschitzWith.continuous (K := ⟨max L 0, le_max_right _ _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  exact (hlip x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

theorem exists_failure (q : HighDimensionalSeparableNoiseLinfSmooth.Params)
    (hv : HighDimensionalSeparableNoiseLinfSmooth.spec.valid q)
    (A : Algorithm (Sp q.d) (Sp q.d) (Sp q.d)) (b : Fin 1 → ℕ) (hb : ∀ i, b i ≤ lowerBudget q) :
    ∃ (I : Sp q.d → ℝ) (O : Oracle (Sp q.d) (Sp q.d)),
      HighDimensionalSeparableNoiseLinfSmooth.spec.admissible q I O ∧
        ¬ HighDimensionalSeparableNoiseLinfSmooth.spec.successful q I
          (fun seed : A.Seed × ((k : ℕ) → O.Seed k) => execute O A b seed.1 seed.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨p, hpp, hDp, hp2, h5, hcard⟩ := exists_prime q hv
  have : Fact p.Prime := ⟨hpp⟩
  have hc : Fintype.card (Coeff p) ≤ Fintype.card (Fin q.d) := by
    simp only [Fintype.card_fin, Fintype.card_pi, Finset.prod_const, ZMod.card, Finset.card_univ,
      Fintype.card_fin]
    exact hcard
  obtain ⟨κ⟩ := Function.Embedding.nonempty_of_card_le hc
  have hbe : ∀ i, b i ≤ LongTails.Theorems.AbcNoiseLowerBound.budget (euclidParams q) i := by
    intro i
    have := budget_le_euclid q hv (b i) (hb i)
    simpa [LongTails.Theorems.AbcNoiseLowerBound.budget] using this
  have hbeq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  obtain ⟨h, O, hadm, hfail⟩ := LongTails.Theorems.AbcNoiseLowerBound.result (euclidParams q)
    (euclid_valid q hv) (simulate (D := dim q) κ q.x0 A) trivial b hbe
  obtain ⟨g, pm, P, fstar, hiid, hO, hgrad, hlip, hlow, hinf, hgap, hmeas, hint, hmean, hvarint,
    hvar⟩ := hadm
  subst hO
  obtain ⟨hL, hS, hε, -, -⟩ := hv
  let P' : ProbabilityMeasure (ℕ → ℝ) := P
  let pm' : ProbabilityMeasure ℝ := pm
  refine ⟨lift κ q.x0 h, pointOracle P' (liftOracle κ q.x0 g),
    lift_admissible hDp hp2 (HighDimensionalSeparableNoiseLinfSmooth.toGeneral q) κ h g pm' P'
      fstar hiid hgrad hlip hlow hinf
      hgap hmeas hint hmean hvarint
      (fun u => (hvar u).trans (le_of_eq (by
        simp [euclidParams, HighDimensionalAbcNoiseNonconvex.toGeneral,
          HighDimensionalSeparableNoiseLinfSmooth.toGeneral])))
      hS hL.le, ?_⟩
  rintro ⟨hmo, hio, hlo⟩
  apply hfail
  have hexec : ∀ seed : A.Seed × (ℕ → ℝ),
      execute (pointOracle P' g) (simulate (D := dim q) κ q.x0 A) b seed.1 seed.2 =
      down κ (execute (pointOracle P' (liftOracle κ q.x0 g)) A b seed.1 seed.2 - q.x0) := by
    intro seed
    rw [hbeq]
    exact execute_simulate κ q.x0 A g P' (b 0) seed.1 seed.2
  set rf := fun seed : A.Seed × (ℕ → ℝ) =>
    execute (pointOracle P' (liftOracle κ q.x0 g)) A b seed.1 seed.2 with hrf
  have hG := lift_gradient κ q.x0 hgrad
  have hgc := gradient_continuous_of_lip hlip
  have hdc : Continuous (fun x : Sp q.d => down (D := dim q) κ (x - q.x0)) := by fun_prop
  have hptw : ∀ seed, ‖gradient h (down κ (rf seed - q.x0))‖ ≤
      3 * ∑ r, |gradient (lift κ q.x0 h) (rf seed) r| := by
    intro seed
    rw [hG]
    exact l1_up_ge κ hDp hp2 h5 _
  have hmeasf : Measurable (fun seed => ‖gradient h (down κ (rf seed - q.x0))‖) :=
    (hgc.comp hdc).norm.measurable.comp hmo
  have hint3 : Integrable (fun seed => 3 * ∑ r, |gradient (lift κ q.x0 h) (rf seed) r|)
      ((A.law : Measure _).prod (P' : Measure (ℕ → ℝ))) := by
    exact hio.const_mul 3
  have hintf : Integrable (fun seed => ‖gradient h (down κ (rf seed - q.x0))‖)
      ((A.law : Measure _).prod (P' : Measure (ℕ → ℝ))) := by
    refine hint3.mono' hmeasf.aestronglyMeasurable (Filter.Eventually.of_forall fun seed => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hptw seed
  have hfinal : ∫ seed, ‖gradient h (down κ (rf seed - q.x0))‖
      ∂((A.law : Measure _).prod (P' : Measure (ℕ → ℝ))) ≤ 3 * q.ε := by
    calc ∫ seed, ‖gradient h (down κ (rf seed - q.x0))‖
          ∂((A.law : Measure _).prod (P' : Measure (ℕ → ℝ)))
        ≤ ∫ seed, 3 * ∑ r, |gradient (lift κ q.x0 h) (rf seed) r|
            ∂((A.law : Measure _).prod (P' : Measure (ℕ → ℝ))) := integral_mono hintf hint3 hptw
      _ = 3 * ∫ seed, ∑ r, |gradient (lift κ q.x0 h) (rf seed) r|
            ∂((A.law : Measure _).prod (P' : Measure (ℕ → ℝ))) := integral_const_mul _ _
      _ ≤ 3 * q.ε := by
          have hlo' : ∫ seed, ∑ r, |gradient (lift κ q.x0 h) (rf seed) r|
              ∂((A.law : Measure _).prod (P' : Measure (ℕ → ℝ))) ≤ q.ε := hlo
          linarith
  have hfun : (fun seed : A.Seed × (ℕ → ℝ) =>
      execute (pointOracle P' g) (simulate (D := dim q) κ q.x0 A) b seed.1 seed.2) =
      fun seed => down κ (rf seed - q.x0) := funext hexec
  have hm : Measurable (fun seed : A.Seed × (ℕ → ℝ) =>
      execute (pointOracle P' g) (simulate (D := dim q) κ q.x0 A) b seed.1 seed.2) := by
    rw [hfun]
    exact hdc.measurable.comp hmo
  have e2 : (fun seed : A.Seed × (ℕ → ℝ) => ‖gradient h (down κ (rf seed - q.x0))‖) =
      fun seed : A.Seed × (ℕ → ℝ) => ‖gradient h
        (execute (pointOracle P' g) (simulate (D := dim q) κ q.x0 A) b seed.1 seed.2)‖ :=
    funext fun seed => congrArg (fun u => ‖gradient h u‖) (hexec seed).symm
  have hi : Integrable (fun seed : A.Seed × (ℕ → ℝ) => ‖gradient h
      (execute (pointOracle P' g) (simulate (D := dim q) κ q.x0 A) b seed.1 seed.2)‖)
      ((A.law : Measure _).prod (P' : Measure (ℕ → ℝ))) := by
    rw [← e2]
    exact hintf
  have hle : ∫ seed : A.Seed × (ℕ → ℝ), ‖gradient h
      (execute (pointOracle P' g) (simulate (D := dim q) κ q.x0 A) b seed.1 seed.2)‖
      ∂((A.law : Measure _).prod (P' : Measure (ℕ → ℝ))) ≤ 3 * q.ε := by
    rw [← e2]
    exact hfinal
  exact ⟨hm, hi, hle⟩

end Failure

end LongTails.Proofs.LinfLowerTransfer
