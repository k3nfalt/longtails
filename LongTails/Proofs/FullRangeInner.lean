import LongTails.Algorithms.FullRangeMlmc
import LongTails.Proofs.FullRangeResolvent
import LongTails.Proofs.SmoothBanachNoise
import LongTails.Proofs.SmoothBanachSampling
import LongTails.Setups.StochasticGeneralizedMonotone

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.FullRangeInner

open OracleTemplate.StochasticCohypomonotone
open LongTails.Algorithms.FullRangeMlmc
open LongTails.Setups.StochasticGeneralizedMonotone (IsStochasticOperator)
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ η : ℝ}

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma inner_smooth_sq (x y : E) :
    ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * (innerSL ℝ x) y + 1 * ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, innerSL_apply_apply]
  linarith

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma innerStep_fixed (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) (x : E) {γ : ℝ}
    (hγ : 0 < γ) :
    innerStep J η γ x (resH H hη hηL x) (F (resH H hη hηL x)) = resH H hη hηL x := by
  set z := resH H hη hηL x
  have hm : η⁻¹ • (x - z) - F z ∈ G z := H.resH_mem hη hηL x
  have hγη : 0 < γ * η := by positivity
  refine H.res_unique hγη ?_
  have e : (γ * η)⁻¹ • (z - γ • (z - x + η • F z) - z) = η⁻¹ • (x - z) - F z := by
    have h1 : z - γ • (z - x + η • F z) - z = γ • ((x - z) - η • F z) := by
      rw [smul_sub, smul_add, smul_sub, smul_sub]
      abel
    rw [h1, smul_smul, inv_mul_eq_div]
    have h2 : γ * η ≠ 0 := hγη.ne'
    have h3 : γ / (γ * η) = η⁻¹ := by field_simp
    rw [h3, smul_sub, smul_smul, inv_mul_cancel₀ hη.ne', one_smul]
  rwa [e]

lemma innerStep_moment (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) (x z : E) {γ σ : ℝ}
    (hγ : 0 < γ) (hγs : γ * (1 + η * L) ^ 2 ≤ 1 - η * L)
    (p : Measure Ω) [IsProbabilityMeasure p] (g : E → Ω → E)
    (hg : IsStochasticOperator p F g σ) :
    Integrable (fun ω => ‖innerStep J η γ x z (g z ω) - resH H hη hηL x‖ ^ 2) p ∧
    (∫ ω, ‖innerStep J η γ x z (g z ω) - resH H hη hηL x‖ ^ 2 ∂p) ≤
      (1 - γ * (1 - η * L)) * ‖z - resH H hη hηL x‖ ^ 2 + γ ^ 2 * η ^ 2 * σ ^ 2 := by
  set u := resH H hη hηL x
  have hL := H.L_pos
  have hγη : 0 < γ * η := by positivity
  set μ := 1 - η * L with hμ
  have hμpos : 0 < μ := by rw [hμ]; linarith
  set d := z - u
  let y : E := (z - γ • (z - x + η • F z)) - (u - γ • (u - x + η • F u))
  let X : Ω → E := fun ω => (-(γ * η)) • (g z ω - F z)
  have hgm : Measurable (g z) := hg.measurable.comp measurable_prodMk_left
  have hXm : Measurable X := by dsimp [X]; fun_prop
  have hXi : Integrable X p := ((hg.integrable z).sub (integrable_const _)).smul _
  have hsq (ω : Ω) : ‖X ω‖ ^ 2 = (γ * η) ^ 2 * ‖g z ω - F z‖ ^ 2 := by
    simp only [X, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_neg]
  have hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) p := by
    simp_rw [hsq]
    exact (hg.variance_integrable z).const_mul _
  have hzero : (∫ ω, X ω ∂p) = 0 := by
    dsimp [X]
    rw [integral_smul, integral_sub (hg.integrable z) (integrable_const _), hg.unbiased]
    simp
  have hn := LongTails.Proofs.SmoothBanachNoise.centered_second_moment 1 (innerSL ℝ)
    inner_smooth_sq hXm hXi hX2 hzero y
  have hstepEq (ω : Ω) : ‖innerStep J η γ x z (g z ω) - u‖ ≤ ‖y + X ω‖ := by
    have hfix := innerStep_fixed H hη hηL x hγ
    rw [show resH H hη hηL x = u from rfl] at hfix
    conv_lhs => rw [← hfix]
    refine (H.res_nonexp hγη _ _).trans (le_of_eq ?_)
    congr 1
    dsimp only [y, X]
    module
  have hmeas : Measurable (fun ω => innerStep J η γ x z (g z ω)) := by
    have hc : Continuous (J (γ * η)) := (LipschitzWith.of_dist_le_mul (K := 1) (by
      intro a b
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using H.res_nonexp hγη a b)).continuous
    unfold innerStep
    exact hc.measurable.comp (by fun_prop)
  have hle (ω : Ω) : ‖innerStep J η γ x z (g z ω) - u‖ ^ 2 ≤ ‖y + X ω‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hstepEq ω)
  have hi : Integrable (fun ω => ‖innerStep J η γ x z (g z ω) - u‖ ^ 2) p :=
    hn.1.mono' ((hmeas.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hle ω)
  refine ⟨hi, (integral_mono hi hn.1 hle).trans (hn.2.trans ?_)⟩
  have hvarX : (∫ ω, ‖X ω‖ ^ 2 ∂p) ≤ (γ * η) ^ 2 * σ ^ 2 := by
    simp_rw [hsq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hg.variance z) (sq_nonneg _)
  have hy : y = d - γ • (d + η • (F z - F u)) := by
    dsimp only [y, d]
    module
  have hFn : ‖F z - F u‖ ≤ L * ‖d‖ := H.lip z u
  have hin : -(L * ‖d‖ ^ 2) ≤ ⟪d, F z - F u⟫ := by
    have := real_inner_le_norm d (-(F z - F u))
    rw [inner_neg_right, norm_neg] at this
    nlinarith [norm_nonneg d]
  set w := d + η • (F z - F u) with hw
  have hwn : ‖w‖ ≤ (1 + η * L) * ‖d‖ := by
    have h1 := norm_add_le d (η • (F z - F u))
    rw [norm_smul, Real.norm_of_nonneg hη.le] at h1
    nlinarith [mul_le_mul_of_nonneg_left hFn hη.le]
  have hdw : μ * ‖d‖ ^ 2 ≤ ⟪d, w⟫ := by
    rw [hw, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hμ]
    nlinarith [mul_le_mul_of_nonneg_left hin hη.le]
  have hyy : ‖y‖ ^ 2 ≤ (1 - γ * μ) * ‖d‖ ^ 2 := by
    rw [hy, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg hγ.le]
    have hw2 : ‖w‖ ^ 2 ≤ (1 + η * L) ^ 2 * ‖d‖ ^ 2 := by
      have := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hwn
      rwa [mul_pow] at this
    have h1 : γ ^ 2 * ‖w‖ ^ 2 ≤ γ * μ * ‖d‖ ^ 2 := by
      have h2 := mul_le_mul_of_nonneg_left hw2 (sq_nonneg γ)
      have h3 : γ ^ 2 * ((1 + η * L) ^ 2 * ‖d‖ ^ 2) =
          γ * (γ * (1 + η * L) ^ 2) * ‖d‖ ^ 2 := by ring
      have h4 := mul_le_mul_of_nonneg_left hγs (mul_nonneg hγ.le (sq_nonneg ‖d‖))
      nlinarith
    have h5 := mul_le_mul_of_nonneg_left hdw hγ.le
    nlinarith
  have hfin : ‖y‖ ^ 2 + 1 * ∫ ω, ‖X ω‖ ^ 2 ∂p ≤
      (1 - γ * μ) * ‖d‖ ^ 2 + γ ^ 2 * η ^ 2 * σ ^ 2 := by
    have : (γ * η) ^ 2 * σ ^ 2 = γ ^ 2 * η ^ 2 * σ ^ 2 := by ring
    linarith
  exact hfin


lemma epochOf_of_lt (n0 k : ℕ) (h0 : 0 < n0) (h : k < n0) : epochOf n0 k = 0 := by
  have : (k + n0) / n0 = 1 := by
    rw [Nat.div_eq_iff (by omega)]
    constructor <;> omega
  simp [epochOf, this]

lemma epochOf_of_range (n0 l k : ℕ) (h0 : 0 < n0) (h1 : n0 * 2 ^ l ≤ k)
    (h2 : k < n0 * 2 ^ (l + 1)) : epochOf n0 k = l + 1 := by
  unfold epochOf
  have hle : (k + n0) / n0 ≤ 2 ^ (l + 1) := by
    apply Nat.le_of_lt_succ
    rw [Nat.div_lt_iff_lt_mul h0]
    have : (2 ^ (l + 1)).succ * n0 = n0 * 2 ^ (l + 1) + n0 := by
      rw [Nat.succ_mul, Nat.mul_comm]
    omega
  have hgt : 2 ^ l < (k + n0) / n0 := by
    have : 2 ^ l + 1 ≤ (k + n0) / n0 := by
      rw [Nat.le_div_iff_mul_le h0]
      have e : (2 ^ l + 1) * n0 = n0 * 2 ^ l + n0 := by ring
      omega
    omega
  apply le_antisymm (Nat.clog_le_of_le_pow hle)
  exact Nat.succ_le_of_lt ((Nat.lt_clog_iff_pow_lt (by norm_num)).mpr hgt)

lemma geometric_recursion {u : ℕ → ℝ} {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (s m : ℕ)
    (h : ∀ i < m, u (s + i + 1) ≤ (1 - a) * u (s + i) + b) :
    u (s + m) ≤ (1 - a) ^ m * u s + b / a := by
  induction m with
  | zero =>
      simp only [add_zero, pow_zero, one_mul]
      have : 0 ≤ b / a := by positivity
      linarith
  | succ m ih =>
      have h1 := ih (fun i hi => h i (by omega))
      have h2 := h m (by omega)
      have h3 : u (s + (m + 1)) = u (s + m + 1) := rfl
      rw [h3]
      have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 1 - a by linarith)
      have h5 : (1 - a) * ((1 - a) ^ m * u s + b / a) + b = (1 - a) ^ (m + 1) * u s + b / a := by
        field_simp
        ring
      linarith

lemma pow_le_exp_mul {a : ℝ} (ha1 : a ≤ 1) (m : ℕ) : (1 - a) ^ m ≤ Real.exp (-(a * m)) := by
  have h1 : (1 - a) ^ m ≤ Real.exp (-a) ^ m :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-a)]) m
  have h2 : Real.exp (-a) ^ m = Real.exp (-(a * m)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  linarith

section Path

variable (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) {σ γ0 : ℝ} {n0 : ℕ}
  (p : ProbabilityMeasure Ω) (g : E → Ω → E) (x : E)

include H in
omit [CompleteSpace E] in
lemma innerStep_measurable (hη : 0 < η) {γ0 : ℝ} (hγ0 : 0 < γ0) {n0 : ℕ}
    (hg : Measurable (Function.uncurry g)) :
    Measurable (Function.uncurry (innerAdvance J g η γ0 n0 x)) := by
  have hslice (k : ℕ) : Measurable (fun w : E × Ω => innerStep J η (stepAt γ0 n0 k) x w.1 (g w.1 w.2)) := by
    have hγ : 0 < stepAt γ0 n0 k * η := by unfold stepAt; positivity
    have hc : Continuous (J (stepAt γ0 n0 k * η)) := (LipschitzWith.of_dist_le_mul (K := 1) (by
      intro a b
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using H.res_nonexp hγ a b)).continuous
    unfold innerStep
    exact hc.measurable.comp (by
      have : Measurable (fun w : E × Ω => g w.1 w.2) := hg
      fun_prop)
  have hall : Measurable (fun w : ℕ × (E × Ω) => (w.1 + 1,
      innerStep J η (stepAt γ0 n0 w.1) x w.2.1 (g w.2.1 w.2.2))) :=
    (measurable_fst.add_const 1).prodMk (measurable_from_prod_countable_right hslice)
  exact hall.comp (show Measurable (fun w : (ℕ × E) × Ω => (w.1.1, (w.1.2, w.2))) from by fun_prop)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma innerState_fst (k : ℕ) (s : ℕ × E) (ξ : Fin k → Ω) :
    (iterateSamples (innerAdvance J g η γ0 n0 x) k s ξ).1 = s.1 + k := by
  induction k generalizing s with
  | zero => simp [iterateSamples]
  | succ k ih =>
      simp only [iterateSamples]
      rw [ih]
      simp only [innerAdvance]
      omega

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma innerPath_succ (k : ℕ) (ξ : ℕ → Ω) :
    innerPath J g η γ0 n0 x (k + 1) ξ =
      innerStep J η (stepAt γ0 n0 k) x (innerPath J g η γ0 n0 x k ξ)
        (g (innerPath J g η γ0 n0 x k ξ) (ξ k)) := by
  unfold innerPath
  rw [OracleTemplate.GapStrongGrowth.iterateSamples_succ_last]
  simp only [innerAdvance]
  have hf2 := innerState_fst (J := J) (g := g) (η := η) (γ0 := γ0) (n0 := n0) (x := x) k (0, x)
    (fun i : Fin k => ξ i.castSucc)
  rw [hf2]
  simp only [zero_add, Fin.val_last, Fin.val_castSucc]

include H hη hηL in
lemma path_succ_bound (hγ0 : 0 < γ0) (hγ0s : γ0 * (1 + η * L) ^ 2 ≤ 1 - η * L)
    (hg : IsStochasticOperator (p : Measure Ω) F g σ) (k : ℕ)
    (hk : Integrable (fun ξ => ‖innerPath J g η γ0 n0 x k ξ - resH H hη hηL x‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (p : Measure Ω))) :
    Integrable (fun ξ => ‖innerPath J g η γ0 n0 x (k + 1) ξ - resH H hη hηL x‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) ∧
    (∫ ξ, ‖innerPath J g η γ0 n0 x (k + 1) ξ - resH H hη hηL x‖ ^ 2
      ∂Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) ≤
      (1 - stepAt γ0 n0 k * (1 - η * L)) *
        (∫ ξ, ‖innerPath J g η γ0 n0 x k ξ - resH H hη hηL x‖ ^ 2
          ∂Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) +
        stepAt γ0 n0 k ^ 2 * η ^ 2 * σ ^ 2 := by
  set u := resH H hη hηL x
  let Q := Measure.infinitePi fun _ : ℕ => (p : Measure Ω)
  let Pf := Measure.pi fun _ : Fin k => (p : Measure Ω)
  have hadv := innerStep_measurable H g x hη hγ0 (n0 := n0) hg.measurable
  set γ := stepAt γ0 n0 k with hγd
  have hγk : 0 < γ := by rw [hγd]; unfold stepAt; positivity
  have hγkle : γ ≤ γ0 := by
    rw [hγd]
    unfold stepAt
    exact div_le_self hγ0.le (one_le_pow₀ (by norm_num))
  have hγs : γ * (1 + η * L) ^ 2 ≤ 1 - η * L :=
    (mul_le_mul_of_nonneg_right hγkle (sq_nonneg _)).trans hγ0s
  let Z : (Fin k → Ω) → E := fun w =>
    (iterateSamples (innerAdvance J g η γ0 n0 x) k (0, x) w).2
  have hZ : Measurable Z := (OracleTemplate.GapStrongGrowth.iterateSamples_measurable hadv k).snd.comp
    measurable_prodMk_left
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving (p : Measure Ω) k
  have hnext := LongTails.Proofs.SmoothBanachSampling.prefix_next_preserving (p : Measure Ω) k
  let f : (Fin k → Ω) × Ω → ℝ := fun w =>
    ‖innerStep J η γ x (Z w.1) (g (Z w.1) w.2) - u‖ ^ 2
  have hγη : 0 < γ * η := by positivity
  have hfm : Measurable f := by
    have hc : Continuous (J (γ * η)) := (LipschitzWith.of_dist_le_mul (K := 1) (by
      intro a b
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using H.res_nonexp hγη a b)).continuous
    have hgg : Measurable (fun w : (Fin k → Ω) × Ω => g (Z w.1) w.2) :=
      hg.measurable.comp ((hZ.comp measurable_fst).prodMk measurable_snd)
    have hZf : Measurable (fun w : (Fin k → Ω) × Ω => Z w.1) := hZ.comp measurable_fst
    have hin : Measurable (fun w : (Fin k → Ω) × Ω =>
        Z w.1 - γ • (Z w.1 - x + η • g (Z w.1) w.2)) :=
      hZf.sub (((hZf.sub measurable_const).add (hgg.const_smul η)).const_smul γ)
    exact ((hc.measurable.comp hin).sub measurable_const).norm.pow_const 2
  have hfib (w : Fin k → Ω) := innerStep_moment H hη hηL x (Z w) hγk hγs (p : Measure Ω) g hg
  let Gf : (Fin k → Ω) → ℝ := fun w =>
    (1 - γ * (1 - η * L)) * ‖Z w - u‖ ^ 2 + γ ^ 2 * η ^ 2 * σ ^ 2
  have hZsq : Measurable (fun w => ‖Z w - u‖ ^ 2) := (hZ.sub measurable_const).norm.pow_const 2
  have hkPf : Integrable (fun w => ‖Z w - u‖ ^ 2) Pf :=
    (hpre.integrable_comp hZsq.aestronglyMeasurable).mp hk
  have hG : Integrable Gf Pf := (hkPf.const_mul _).add (integrable_const _)
  have hprod := OracleTemplate.StochasticConvexQuadratic.nonnegative_product_control hfm
    (fun w => sq_nonneg _) (fun w => (hfib w).1) hG (fun w => (hfib w).2)
  have hcomp (ξ : ℕ → Ω) : ‖innerPath J g η γ0 n0 x (k + 1) ξ - u‖ ^ 2 =
      f ((fun i : Fin k => ξ i), ξ k) := by
    rw [innerPath_succ]
    rfl
  simp_rw [hcomp]
  refine ⟨hnext.integrable_comp_of_integrable hprod.1, ?_⟩
  have he : (∫ ξ, f ((fun i : Fin k => ξ i), ξ k) ∂Q) = ∫ w, f w ∂Pf.prod (p : Measure Ω) := by
    have := integral_map (μ := Q) hnext.measurable.aemeasurable hfm.aestronglyMeasurable
    rw [hnext.map_eq] at this
    exact this.symm
  rw [he]
  refine hprod.2.trans (le_of_eq ?_)
  dsimp only [Gf]
  rw [integral_add (hkPf.const_mul _) (integrable_const _), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  have he2 : (∫ w, ‖Z w - u‖ ^ 2 ∂Pf) = ∫ ξ, ‖innerPath J g η γ0 n0 x k ξ - u‖ ^ 2 ∂Q := by
    have := integral_map (μ := Q) hpre.measurable.aemeasurable hZsq.aestronglyMeasurable
    rw [hpre.map_eq] at this
    exact this
  rw [he2]

include H hη hηL in
lemma path_integrable (hγ0 : 0 < γ0) (hγ0s : γ0 * (1 + η * L) ^ 2 ≤ 1 - η * L)
    (hg : IsStochasticOperator (p : Measure Ω) F g σ) (k : ℕ) :
    Integrable (fun ξ => ‖innerPath J g η γ0 n0 x k ξ - resH H hη hηL x‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) := by
  induction k with
  | zero =>
      have : (fun ξ : ℕ → Ω => ‖innerPath J g η γ0 n0 x 0 ξ - resH H hη hηL x‖ ^ 2) =
          fun _ => ‖x - resH H hη hηL x‖ ^ 2 := by
        funext ξ
        simp [innerPath, iterateSamples]
      rw [this]
      exact integrable_const _
  | succ k ih => exact (path_succ_bound H hη hηL p g x hγ0 hγ0s hg k ih).1

end Path

end LongTails.Proofs.FullRangeInner
