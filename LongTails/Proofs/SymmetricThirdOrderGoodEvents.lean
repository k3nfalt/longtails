import LongTails.Proofs.SymmetricThirdOrderSampling
import LongTails.Proofs.SymmetricThirdOrderRound

namespace LongTails.Proofs.SymmetricThirdOrderGoodEvents

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.SymmetricThirdOrder
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex
open scoped ENNReal

abbrev Stage (J : ℕ) := Unit ⊕ ((Fin (J + 1) × Bool) ⊕ Bool)

lemma card_stage (J : ℕ) : Fintype.card (Stage J) = 2 * J + 5 := by
  simp only [Stage, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_unit]
  omega

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def endpoint (cfg : Config E) (oracle : E → Ω → Reply E)
    (ξ : ℕ → Ω) (t j : ℕ) (b : Bool) : E :=
  if b then sampledCenter cfg oracle ξ t - (sampledInner cfg oracle ξ t j - sampledCenter cfg oracle ξ t)
  else sampledInner cfg oracle ξ t j

def gradientStart (cfg : Config E) (t j : ℕ) (b : Bool) : ℕ :=
  roundCalls cfg * t + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * j +
    (if b then cfg.batch * cfg.groups else 0)

def hessianStart (cfg : Config E) (t : ℕ) (b : Bool) : ℕ :=
  roundCalls cfg * t + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds +
    (cfg.batch * cfg.groups + cfg.batch * cfg.groups) + (if b then cfg.groups else 0)

noncomputable def badStage (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) : Stage cfg.innerRounds → Set (ℕ → Ω)
  | .inl _ => {ξ | 9 * cfg.σh < ‖QueryPlan.sampledEval oracle ξ
      (hessianPlan cfg (sampledCenter cfg oracle ξ t)) (roundCalls cfg * t) - H (sampledCenter cfg oracle ξ t)‖}
  | .inr (.inl (j, b)) => {ξ | cfg.tolerance < ‖QueryPlan.sampledEval oracle ξ
      (gradientPlan cfg (endpoint cfg oracle ξ t j b)) (gradientStart cfg t j b) - g (endpoint cfg oracle ξ t j b)‖}
  | .inr (.inr b) => {ξ | 9 * cfg.σh < ‖QueryPlan.sampledEval oracle ξ
      (hessianPlan cfg (endpoint cfg oracle ξ t cfg.innerRounds b)) (hessianStart cfg t b) -
        H (endpoint cfg oracle ξ t cfg.innerRounds b)‖}

noncomputable def goodRound (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) : Set (ℕ → Ω) :=
  (⋃ i, badStage cfg oracle g H t i)ᶜ

lemma failure_union_bound [MeasurableSpace Ω] (P : Measure (ℕ → Ω))
    (cfg : Config E) (oracle : E → Ω → Reply E) (g : E → E) (H : E → E →L[ℝ] E)
    (T : ℕ) (q : ℝ≥0∞)
    (hb : ∀ t < T, ∀ i, P (badStage cfg oracle g H t i) ≤ q) :
    P (⋃ t : Fin T, (goodRound cfg oracle g H t)ᶜ) ≤
      (T * (2 * cfg.innerRounds + 5) : ℕ) * q := by
  calc
    _ ≤ ∑ t : Fin T, P ((goodRound cfg oracle g H t)ᶜ) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _t : Fin T, (2 * cfg.innerRounds + 5 : ℕ) * q := by
      apply Finset.sum_le_sum
      intro t _
      simp only [goodRound, compl_compl]
      calc
        _ ≤ ∑ i, P (badStage cfg oracle g H t i) := measure_iUnion_fintype_le _ _
        _ ≤ ∑ _i : Stage cfg.innerRounds, q := Finset.sum_le_sum (fun i _ => hb t t.isLt i)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, card_stage, nsmul_eq_mul]
    _ = _ := by simp [nsmul_eq_mul, Nat.cast_mul, mul_assoc]

lemma badStage_probability [FiniteDimensional ℝ E] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E]
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (ha : 0 < cfg.tolerance) (hσ : 0 ≤ cfg.σh)
    (g : E → E) (hg : Measurable g) (H : E → E →L[ℝ] E) (hH : Measurable H)
    (hsym : ∀ z a b : E, inner ℝ a (H z b) = inner ℝ (H z a) b)
    {σ : ℝ} (hmpos : 0 < cfg.batch) (hsize : 144 * σ ^ 2 ≤ (cfg.batch : ℝ) * cfg.tolerance ^ 2)
    (hgi : ∀ z, Integrable (fun ω => (oracle z ω).1) p)
    (hmean : ∀ z, (∫ ω, (oracle z ω).1 ∂p) = g z)
    (hgv : ∀ z, Integrable (fun ω => ‖(oracle z ω).1 - g z‖ ^ 2) p)
    (hgm : ∀ z, (∫ ω, ‖(oracle z ω).1 - g z‖ ^ 2 ∂p) ≤ σ ^ 2)
    (hhi : ∀ z, Integrable (fun ω => ‖(oracle z ω).2 - H z‖ ^ 2) p)
    (hhm : ∀ z, (∫ ω, ‖(oracle z ω).2 - H z‖ ^ 2 ∂p) ≤ cfg.σh ^ 2)
    (t : ℕ) (i : Stage cfg.innerRounds) :
    P (badStage cfg oracle g H t i) ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ cfg.groups) := by
  rcases i with u | (⟨j, b⟩ | b)
  · exact SymmetricThirdOrderSampling.sampled_center_hessian_failure h cfg oracle ho hC hne hconv hL hδ hσ H hH hsym hhi hhm t
  · have hb := SymmetricThirdOrderSampling.sampled_endpoint_gradient_failure h cfg oracle ho hC hne hconv hL hδ ha
      g hg hmpos hsize hgi hmean hgv hgm t j b
    exact hb.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by norm_num) (by norm_num) _))
  · exact SymmetricThirdOrderSampling.sampled_cleanup_hessian_failure h cfg oracle ho hC hne hconv hL hδ hσ H hH hsym hhi hhm t b

lemma measurableSet_badStage [FiniteDimensional ℝ E] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E]
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ)
    (g : E → E) (hg : Measurable g) (H : E → E →L[ℝ] E) (hH : Measurable H)
    (t : ℕ) (i : Stage cfg.innerRounds) : MeasurableSet (badStage cfg oracle g H t i) := by
  have hc := SymmetricThirdOrderHistory.measurable_sampledCenter cfg oracle ho hC hne hconv hL hδ t
  have hx (j : ℕ) (b : Bool) : Measurable (fun ξ => endpoint cfg oracle ξ t j b) :=
    SymmetricThirdOrderHistory.measurable_sampledEndpoint cfg oracle ho hC hne hconv hL hδ t j b
  rcases i with u | (⟨j, b⟩ | b)
  · have he := SymmetricThirdOrderMeasurability.measurable_hessianPlan oracle ho id
      (fun k => measurable_pi_apply k) cfg _ hc (roundCalls cfg * t)
    exact measurableSet_lt measurable_const ((he.sub (hH.comp hc)).norm)
  · have he := SymmetricThirdOrderMeasurability.measurable_gradientPlan oracle ho id
      (fun k => measurable_pi_apply k) cfg _ (hx j b) (gradientStart cfg t j b)
    exact measurableSet_lt measurable_const ((he.sub (hg.comp (hx j b))).norm)
  · have he := SymmetricThirdOrderMeasurability.measurable_hessianPlan oracle ho id
      (fun k => measurable_pi_apply k) cfg _ (hx cfg.innerRounds b) (hessianStart cfg t b)
    exact measurableSet_lt measurable_const ((he.sub (hH.comp (hx cfg.innerRounds b))).norm)

omit [CompleteSpace E] in
lemma gradient_end_le (cfg : Config E) (t j : ℕ) (b : Bool) (hj : j ≤ cfg.innerRounds) :
    gradientStart cfg t j b + cfg.batch * cfg.groups ≤ roundCalls cfg * (t + 1) - cfg.batch := by
  rw [← SymmetricThirdOrderHistory.correction_start]
  have hh := Nat.mul_le_mul_left (cfg.batch * cfg.groups + cfg.batch * cfg.groups) hj
  cases b <;> simp only [gradientStart, Bool.false_eq_true, ite_false, ite_true] <;> omega

omit [CompleteSpace E] in
lemma hessian_end_le (cfg : Config E) (t : ℕ) (b : Bool) :
    hessianStart cfg t b + cfg.groups ≤ roundCalls cfg * (t + 1) - cfg.batch := by
  rw [← SymmetricThirdOrderHistory.correction_start]
  cases b <;> simp only [hessianStart, Bool.false_eq_true, ite_false, ite_true] <;> omega

lemma badStage_prefix (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) (i : Stage cfg.innerRounds)
    (ξ η : ℕ → Ω) (heq : ∀ j < roundCalls cfg * (t + 1) - cfg.batch, ξ j = η j) :
    (ξ ∈ badStage cfg oracle g H t i) ↔ (η ∈ badStage cfg oracle g H t i) := by
  have hcend : roundCalls cfg * t + cfg.groups ≤ roundCalls cfg * (t + 1) - cfg.batch := by
    rw [← SymmetricThirdOrderHistory.correction_start]
    omega
  have hc := SymmetricThirdOrderHistory.sampledCenter_prefix cfg oracle t ξ η
    (fun j hj => heq j (by omega))
  rcases i with u | (⟨j, b⟩ | b)
  · have hv := SymmetricThirdOrderExecution.sampledEval_adaptive_prefix oracle
      (fun ζ => hessianPlan cfg (sampledCenter cfg oracle ζ t))
      (fun ζ θ hζ => congrArg (hessianPlan cfg)
        (SymmetricThirdOrderHistory.sampledCenter_prefix cfg oracle t ζ θ hζ)) ξ η
      (fun j hj => heq j (lt_of_lt_of_le hj hcend))
    change 9 * cfg.σh < ‖_ - H _‖ ↔ 9 * cfg.σh < ‖_ - H _‖
    rw [hv, hc]
  · have hj : (j : ℕ) ≤ cfg.innerRounds := by omega
    have hend := gradient_end_le cfg t j b hj
    have hstart : roundCalls cfg * t + cfg.groups +
        (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * j ≤ gradientStart cfg t j b := Nat.le_add_right _ _
    have hp := SymmetricThirdOrderHistory.sampledEndpoint_prefix cfg oracle t j
      (gradientStart cfg t j b) b hstart
    have hx : endpoint cfg oracle ξ t j b = endpoint cfg oracle η t j b :=
      hp ξ η (fun l hl => heq l (by omega))
    have hv := SymmetricThirdOrderExecution.sampledEval_adaptive_prefix oracle
      (fun ζ => gradientPlan cfg (endpoint cfg oracle ζ t j b))
      (fun ζ θ hζ => congrArg (gradientPlan cfg) (hp ζ θ hζ)) ξ η
      (fun l hl => heq l (lt_of_lt_of_le hl hend))
    change cfg.tolerance < ‖_ - g _‖ ↔ cfg.tolerance < ‖_ - g _‖
    rw [hv, hx]
  · have hend := hessian_end_le cfg t b
    have hstart : roundCalls cfg * t + cfg.groups +
        (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds ≤ hessianStart cfg t b := by
      unfold hessianStart
      omega
    have hp := SymmetricThirdOrderHistory.sampledEndpoint_prefix cfg oracle t cfg.innerRounds
      (hessianStart cfg t b) b hstart
    have hx : endpoint cfg oracle ξ t cfg.innerRounds b = endpoint cfg oracle η t cfg.innerRounds b :=
      hp ξ η (fun l hl => heq l (by omega))
    have hv := SymmetricThirdOrderExecution.sampledEval_adaptive_prefix oracle
      (fun ζ => hessianPlan cfg (endpoint cfg oracle ζ t cfg.innerRounds b))
      (fun ζ θ hζ => congrArg (hessianPlan cfg) (hp ζ θ hζ)) ξ η
      (fun l hl => heq l (lt_of_lt_of_le hl hend))
    change 9 * cfg.σh < ‖_ - H _‖ ↔ 9 * cfg.σh < ‖_ - H _‖
    rw [hv, hx]

lemma all_rounds_failure_probability [FiniteDimensional ℝ E] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E]
    {p : Measure Ω} {P : Measure (ℕ → Ω)} [IsProbabilityMeasure p] [IsProbabilityMeasure P]
    (h : IID (fun k (ξ : ℕ → Ω) => ξ k) p P)
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ) (ha : 0 < cfg.tolerance) (hσ : 0 ≤ cfg.σh)
    (g : E → E) (hg : Measurable g) (H : E → E →L[ℝ] E) (hH : Measurable H)
    (hsym : ∀ z a b : E, inner ℝ a (H z b) = inner ℝ (H z a) b)
    {σ : ℝ} (hmpos : 0 < cfg.batch) (hsize : 144 * σ ^ 2 ≤ (cfg.batch : ℝ) * cfg.tolerance ^ 2)
    (hgi : ∀ z, Integrable (fun ω => (oracle z ω).1) p)
    (hmean : ∀ z, (∫ ω, (oracle z ω).1 ∂p) = g z)
    (hgv : ∀ z, Integrable (fun ω => ‖(oracle z ω).1 - g z‖ ^ 2) p)
    (hgm : ∀ z, (∫ ω, ‖(oracle z ω).1 - g z‖ ^ 2 ∂p) ≤ σ ^ 2)
    (hhi : ∀ z, Integrable (fun ω => ‖(oracle z ω).2 - H z‖ ^ 2) p)
    (hhm : ∀ z, (∫ ω, ‖(oracle z ω).2 - H z‖ ^ 2 ∂p) ≤ cfg.σh ^ 2)
    (T : ℕ) :
    P (⋃ t : Fin T, (goodRound cfg oracle g H t)ᶜ) ≤
      ENNReal.ofReal ((T : ℝ) * (2 * cfg.innerRounds + 5) * (2 / 3 : ℝ) ^ cfg.groups) := by
  have hb := failure_union_bound P cfg oracle g H T (ENNReal.ofReal ((2 / 3 : ℝ) ^ cfg.groups))
    (fun t _ i => badStage_probability h cfg oracle ho hC hne hconv hL hδ ha hσ g hg H hH hsym
      hmpos hsize hgi hmean hgv hgm hhi hhm t i)
  have he : (T : ℝ) * (2 * cfg.innerRounds + 5) = ((T * (2 * cfg.innerRounds + 5) : ℕ) : ℝ) := by
    push_cast
    ring
  rw [he, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  exact hb

lemma goodRound_prefix (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) (ξ η : ℕ → Ω)
    (heq : ∀ j < roundCalls cfg * (t + 1) - cfg.batch, ξ j = η j) :
    (ξ ∈ goodRound cfg oracle g H t) ↔ (η ∈ goodRound cfg oracle g H t) := by
  simp only [goodRound, Set.mem_compl_iff, Set.mem_iUnion]
  exact not_congr (exists_congr (fun i => badStage_prefix cfg oracle g H t i ξ η heq))

lemma measurableSet_goodRound [FiniteDimensional ℝ E] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E]
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ)
    (g : E → E) (hg : Measurable g) (H : E → E →L[ℝ] E) (hH : Measurable H) (t : ℕ) :
    MeasurableSet (goodRound cfg oracle g H t) :=
  (MeasurableSet.iUnion (measurableSet_badStage cfg oracle ho hC hne hconv hL hδ g hg H hH t)).compl

lemma goodRound_not_bad (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) (ξ : ℕ → Ω)
    (hg : ξ ∈ goodRound cfg oracle g H t) (i : Stage cfg.innerRounds) :
    ξ ∉ badStage cfg oracle g H t i := by
  exact fun hi => hg (Set.mem_iUnion.mpr ⟨i, hi⟩)

lemma goodRound_center (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) (ξ : ℕ → Ω)
    (hg : ξ ∈ goodRound cfg oracle g H t) :
    ‖QueryPlan.sampledEval oracle ξ (hessianPlan cfg (sampledCenter cfg oracle ξ t))
      (roundCalls cfg * t) - H (sampledCenter cfg oracle ξ t)‖ ≤ 9 * cfg.σh :=
  not_lt.mp (goodRound_not_bad cfg oracle g H t ξ hg (.inl ()))

lemma goodRound_gradient (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t j : ℕ) (b : Bool) (ξ : ℕ → Ω)
    (hg : ξ ∈ goodRound cfg oracle g H t) (hj : j ≤ cfg.innerRounds) :
    ‖QueryPlan.sampledEval oracle ξ (gradientPlan cfg (endpoint cfg oracle ξ t j b))
      (gradientStart cfg t j b) - g (endpoint cfg oracle ξ t j b)‖ ≤ cfg.tolerance :=
  not_lt.mp (goodRound_not_bad cfg oracle g H t ξ hg (.inr (.inl (⟨j, by omega⟩, b))))

lemma goodRound_hessian (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) (b : Bool) (ξ : ℕ → Ω)
    (hg : ξ ∈ goodRound cfg oracle g H t) :
    ‖QueryPlan.sampledEval oracle ξ (hessianPlan cfg (endpoint cfg oracle ξ t cfg.innerRounds b))
      (hessianStart cfg t b) - H (endpoint cfg oracle ξ t cfg.innerRounds b)‖ ≤ 9 * cfg.σh :=
  not_lt.mp (goodRound_not_bad cfg oracle g H t ξ hg (.inr (.inr b)))

lemma goodRound_modelGradient (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t j : ℕ) (ξ : ℕ → Ω)
    (hg : ξ ∈ goodRound cfg oracle g H t) (hj : j ≤ cfg.innerRounds) :
    ‖QueryPlan.sampledEval oracle ξ
      (modelGradientPlan cfg (sampledCenter cfg oracle ξ t) (sampledInner cfg oracle ξ t j)
        (sampledMatrix cfg oracle ξ t)) (gradientStart cfg t j false) -
      modelGradient g (sampledCenter cfg oracle ξ t) (sampledMatrix cfg oracle ξ t) cfg.L cfg.δ
        (sampledInner cfg oracle ξ t j - sampledCenter cfg oracle ξ t)‖ ≤ cfg.tolerance := by
  rw [SymmetricThirdOrderExecution.modelGradientPlan_eval]
  apply SymmetricThirdOrderRound.paired_gradient_error
  · simpa only [endpoint, gradientStart, Bool.false_eq_true, ite_false, Nat.add_zero] using
      goodRound_gradient cfg oracle g H t j false ξ hg hj
  · simpa only [endpoint, gradientStart, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] using
      goodRound_gradient cfg oracle g H t j true ξ hg hj

open scoped RealInnerProductSpace

lemma goodRound_accuracy [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 3 f) (hc : ConvexOn ℝ Set.univ f)
    (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) (t : ℕ)
    (hL : 0 < cfg.L) (hδ : 0 < cfg.δ) (hσ : 0 ≤ cfg.σh) (ha : 0 < cfg.tolerance)
    (hδσ : 288 * cfg.σh ≤ cfg.δ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ cfg.L * ‖x - y‖)
    (hC : IsCompact cfg.C) (hconv : Convex ℝ cfg.C) (hx : cfg.x0 ∈ cfg.C)
    (xstar : E) (Δ R : ℝ) (hmin : ∀ x, f xstar ≤ f x) (hgap : f cfg.x0 - f xstar ≤ Δ)
    (hdist : ‖cfg.x0 - sampledCenter cfg oracle ξ t‖ ≤ R)
    (k : ℕ) (hJ : cfg.innerRounds = k + 1)
    (htune : (6 / 7 : ℝ) ^ k * (8 * (Δ + 3 * cfg.L * R ^ 4 + cfg.δ * R ^ 2)) ≤
      cfg.tolerance ^ 2 / cfg.δ)
    (hcleanup : 262144 * cfg.L * cfg.tolerance ^ 2 ≤ cfg.δ ^ 3)
    (hgood : ξ ∈ goodRound cfg oracle (gradient f) (fderiv ℝ (gradient f)) t) :
    let c := sampledCenter cfg oracle ξ t
    let z := (sampledCleanup cfg oracle ξ t).1
    let n := (sampledCleanup cfg oracle ξ t).2
    ‖gradient f z + n + (cfg.δ + 8 * cfg.L * ‖z - c‖ ^ 2) • (z - c)‖ ≤
      (3 / 16 : ℝ) * (cfg.δ + 8 * cfg.L * ‖z - c‖ ^ 2) * ‖z - c‖ + 35 * cfg.tolerance ∧
      ∀ v ∈ cfg.C, ⟪n, v - z⟫ ≤ 0 := by
  let c := sampledCenter cfg oracle ξ t
  let A := QueryPlan.sampledEval oracle ξ (hessianPlan cfg c) (roundCalls cfg * t)
  let B := sampledMatrix cfg oracle ξ t
  let G := fun j y => QueryPlan.sampledEval oracle ξ (modelGradientPlan cfg c y B)
    (roundCalls cfg * t + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * j)
  let y := sampledInner cfg oracle ξ t cfg.innerRounds
  let qg := QueryPlan.sampledEval oracle ξ (modelGradientPlan cfg c y B)
    (gradientStart cfg t cfg.innerRounds false)
  let Hp := QueryPlan.sampledEval oracle ξ (hessianPlan cfg y) (hessianStart cfg t false)
  let Hm := QueryPlan.sampledEval oracle ξ (hessianPlan cfg (c - (y - c))) (hessianStart cfg t true)
  have hsym (w : E) (call : ℕ) (u v : E) :
      ⟪u, QueryPlan.sampledEval oracle ξ (hessianPlan cfg w) call v⟫ =
        ⟪QueryPlan.sampledEval oracle ξ (hessianPlan cfg w) call u, v⟫ := by
    rw [SymmetricThirdOrderExecution.hessianPlan_eval]
    exact SymmetricThirdOrderHessian.symmetricHessian_symmetric _ u v
  have hiter (j : ℕ) : sampledInner cfg oracle ξ t j =
      innerIterate cfg.C cfg.x0 c B cfg.L cfg.δ G j :=
    SymmetricThirdOrderExecution.innerPlan_eval_iterate oracle ξ cfg c B j _
  have hG : ∀ j < k + 1, ‖G j (innerIterate cfg.C cfg.x0 c B cfg.L cfg.δ G j) -
      modelGradient (gradient f) c B cfg.L cfg.δ (innerIterate cfg.C cfg.x0 c B cfg.L cfg.δ G j - c)‖ ≤
        cfg.tolerance := by
    intro j hj
    rw [← hiter]
    simpa only [G, gradientStart, Bool.false_eq_true, ite_false, Nat.add_zero] using
      goodRound_modelGradient cfg oracle (gradient f) (fderiv ℝ (gradient f)) t j ξ hgood (by omega)
  have hy : y = innerIterate cfg.C cfg.x0 c B cfg.L cfg.δ G (k + 1) := by
    simpa only [y, hJ] using hiter cfg.innerRounds
  have hg : ‖qg - modelGradient (gradient f) c B cfg.L cfg.δ (y - c)‖ ≤ cfg.tolerance :=
    goodRound_modelGradient cfg oracle (gradient f) (fderiv ℝ (gradient f)) t cfg.innerRounds ξ hgood le_rfl
  have hp : ‖Hp - fderiv ℝ (gradient f) y‖ ≤ 9 * cfg.σh := by
    simpa only [Hp, y, endpoint, Bool.false_eq_true, ite_false] using
      goodRound_hessian cfg oracle (gradient f) (fderiv ℝ (gradient f)) t false ξ hgood
  have hm : ‖Hm - fderiv ℝ (gradient f) (c - (y - c))‖ ≤ 9 * cfg.σh := by
    simpa only [Hm, y, c, endpoint, ite_true] using
      goodRound_hessian cfg oracle (gradient f) (fderiv ℝ (gradient f)) t true ξ hgood
  have hh := SymmetricThirdOrderRound.estimated_round_accuracy hf hc hL hδ hσ ha hδσ hT
    cfg.C cfg.x0 xstar c A B G hC hconv hx (hsym c _) (goodRound_center cfg oracle
      (gradient f) (fderiv ℝ (gradient f)) t ξ hgood) rfl hmin hgap hdist k htune hG y hy
      qg Hp Hm hg (hsym y _) (hsym (c - (y - c)) _) hp hm hcleanup
  simpa only [sampledCleanup, SymmetricThirdOrderExecution.cleanupPlan_eval, qg, Hp, Hm,
    c, B, y, gradientStart, hessianStart, Bool.false_eq_true, ite_false, ite_true, Nat.add_zero] using hh

noncomputable def survived (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) : Set (ℕ → Ω) :=
  {ξ | ∀ u < t, ξ ∈ goodRound cfg oracle g H u}

lemma survived_zero (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) : survived cfg oracle g H 0 = Set.univ := by
  ext ξ
  simp [survived]

lemma survived_succ (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) :
    survived cfg oracle g H (t + 1) = survived cfg oracle g H t ∩ goodRound cfg oracle g H t := by
  ext ξ
  change (∀ u < t + 1, ξ ∈ goodRound cfg oracle g H u) ↔
    (∀ u < t, ξ ∈ goodRound cfg oracle g H u) ∧ ξ ∈ goodRound cfg oracle g H t
  constructor
  · intro hh
    exact ⟨fun u hu => hh u (by omega), hh t (by omega)⟩
  · rintro ⟨hh, ht⟩ u hu
    by_cases hut : u < t
    · exact hh u hut
    · have he : u = t := by omega
      simpa only [he] using ht

lemma survived_prefix (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) (ξ η : ℕ → Ω)
    (heq : ∀ j < roundCalls cfg * t, ξ j = η j) :
    (ξ ∈ survived cfg oracle g H t) ↔ (η ∈ survived cfg oracle g H t) := by
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  exact goodRound_prefix cfg oracle g H u ξ η (fun j hj => heq j
    (hj.trans_le ((Nat.sub_le _ _).trans (Nat.mul_le_mul_left _ hu))))

lemma survived_succ_prefix (cfg : Config E) (oracle : E → Ω → Reply E)
    (g : E → E) (H : E → E →L[ℝ] E) (t : ℕ) (ξ η : ℕ → Ω)
    (heq : ∀ j < roundCalls cfg * (t + 1) - cfg.batch, ξ j = η j) :
    (ξ ∈ survived cfg oracle g H (t + 1)) ↔ (η ∈ survived cfg oracle g H (t + 1)) := by
  apply forall_congr'
  intro u
  apply forall_congr'
  intro hu
  exact goodRound_prefix cfg oracle g H u ξ η (fun j hj => heq j
    (hj.trans_le (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ hu) _)))

lemma measurableSet_survived [FiniteDimensional ℝ E] [MeasurableSpace Ω]
    [MeasurableSpace E] [BorelSpace E]
    (cfg : Config E) (oracle : E → Ω → Reply E) (ho : Measurable (Function.uncurry oracle))
    (hC : IsCompact cfg.C) (hne : cfg.C.Nonempty) (hconv : Convex ℝ cfg.C)
    (hL : 0 ≤ cfg.L) (hδ : 0 < cfg.δ)
    (g : E → E) (hg : Measurable g) (H : E → E →L[ℝ] E) (hH : Measurable H) (t : ℕ) :
    MeasurableSet (survived cfg oracle g H t) := by
  simp only [survived, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun u => MeasurableSet.iInter (fun _ =>
    measurableSet_goodRound cfg oracle ho hC hne hconv hL hδ g hg H hH u))

end LongTails.Proofs.SymmetricThirdOrderGoodEvents
