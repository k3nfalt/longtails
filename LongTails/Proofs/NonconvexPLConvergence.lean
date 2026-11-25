import LongTails.Proofs.Execution
import LongTails.Proofs.NonconvexPLMoreau
import LongTails.Proofs.NonconvexPLProcess
import LongTails.Proofs.TwoSidedPLConvergence
import LongTails.Algorithms.NonconvexPLSmoothedAgda

open MeasureTheory Finset
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticTwoSidedPL
open LongTails.Setups.StochasticNonconvexPL

namespace OracleTemplate.NonconvexPL

open StochasticGradient
open OracleTemplate.TwoSidedPL (advance_add)

section Execution

variable {E F : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace Ω]

noncomputable def jointOracle (Gx : E × F → Ω → E) (Gy : E × F → Ω → F) (p : ProbabilityMeasure Ω) :
    Oracle (E × F) (E × F) :=
  { Seed := fun _ => Ω
    law := ⟨Measure.infinitePi (fun _ : ℕ => (p : Measure Ω)), inferInstance⟩
    answer := fun _ w ω => (Gx w.2 ω, Gy w.2 ω) }

lemma advance_joint (Gx : E × F → Ω → E) (Gy : E × F → Ω → F) (p : ProbabilityMeasure Ω)
    (L μy τ : ℝ) (n : ℕ) (x0 : E) (y0 : F) (j : Fin (n + 1)) (ξ : ℕ → Ω) :
    ∀ t, advance (fun k s =>
        (nonconvexPLSmoothedAgda (2 * L) τ (τ / 32) (τ * μy / 6144) n x0 y0).update s
        ((jointOracle Gx Gy p).answer []
          ((nonconvexPLSmoothedAgda (2 * L) τ (τ / 32) (τ * μy / 6144) n x0 y0).query s) (ξ k)))
        (2 * t) 0 ((nonconvexPLSmoothedAgda (2 * L) τ (τ / 32) (τ * μy / 6144) n x0 y0).initial j) =
      (j, 2 * t, (path Gx Gy L μy τ x0 y0 ξ t).1, (path Gx Gy L μy τ x0 y0 ξ t).2.1,
        (path Gx Gy L μy τ x0 y0 ξ t).2.2,
        if (j : ℕ) ≤ t then (path Gx Gy L μy τ x0 y0 ξ j).2.2 else x0) := by
  intro t
  induction t with
  | zero =>
    simp only [Nat.mul_zero, advance]
    by_cases h : (j : ℕ) ≤ 0
    · have hj : (j : ℕ) = 0 := by omega
      simp only [hj, le_refl, ite_true]
      rfl
    · simp only [h, ite_false]
      rfl
  | succ t ih =>
    rw [show 2 * (t + 1) = 2 * t + 2 by ring, advance_add, ih, Nat.zero_add]
    have h0 : (2 * t) % 2 = 0 := by omega
    have h1 : ¬ (2 * t + 1) % 2 = 0 := by omega
    have h2 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
    simp only [advance, nonconvexPLSmoothedAgda, jointOracle, h0, h1, h2, ite_true, ite_false]
    refine Prod.ext rfl (Prod.ext (show 2 * t + 1 + 1 = 2 * t + 2 by omega)
      (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))))
    by_cases hj : t + 1 = (j : ℕ)
    · have h3 : (j : ℕ) ≤ t + 1 := le_of_eq hj.symm
      have h4 : ¬ (j : ℕ) ≤ t := by omega
      simp only [hj, ite_true, h4, ite_false, le_refl]
      rw [← hj]
      rfl
    · simp only [hj, ite_false]
      by_cases h4 : (j : ℕ) ≤ t
      · have h5 : (j : ℕ) ≤ t + 1 := by omega
        simp only [h4, h5, ite_true]
      · have h5 : ¬ (j : ℕ) ≤ t + 1 := by omega
        simp only [h4, h5, ite_false]

lemma execute_joint (Gx : E × F → Ω → E) (Gy : E × F → Ω → F) (p : ProbabilityMeasure Ω)
    (L μy τ : ℝ) (n : ℕ) (x0 : E) (y0 : F) (j : Fin (n + 1)) (ξ : ℕ → Ω) :
    execute (jointOracle Gx Gy p) (nonconvexPLSmoothedAgda (2 * L) τ (τ / 32) (τ * μy / 6144) n x0 y0)
        (fun _ => 2 * n) j ξ = (path Gx Gy L μy τ x0 y0 ξ j).2.2 := by
  erw [execute_advance_of_answer _ _ _ _ _
    (fun k query => (jointOracle Gx Gy p).answer [] query (ξ k)) (fun _ _ => rfl)]
  have h := advance_joint Gx Gy p L μy τ n x0 y0 j ξ n
  have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.isLt
  simp only [hj, ite_true] at h
  rw [h]
  rfl

end Execution

section Expectation

variable {E F Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [ProperSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μy σ : ℝ}
  {Gx : E × F → Ω → E} {Gy : E × F → Ω → F} {p : Measure Ω} [IsProbabilityMeasure p]

omit [IsProbabilityMeasure p] in
lemma measurable_residual (H : Hyp f gx gy L μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) (τ : ℝ) (x0 : E) (y0 : F)
    (t : ℕ) :
    Measurable fun ξ : ℕ → Ω => moreauResidual f L (path Gx Gy L μy τ x0 y0 ξ t).2.2 :=
  H.continuous_moreauResidual.measurable.comp
    (measurable_path ox.measurable oy.measurable L μy τ x0 y0 t).snd.snd

lemma memLp_residual (H : Hyp f gx gy L μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) (τ : ℝ) (x0 : E) (y0 : F)
    (t : ℕ) :
    MemLp (fun ξ : ℕ → Ω => moreauResidual f L (path Gx Gy L μy τ x0 y0 ξ t).2.2) 2
      (Measure.infinitePi fun _ : ℕ => p) := by
  have hz := (memLp_path H ox oy τ x0 y0 t).2.2
  refine memLp_of_bound (measurable_residual H ox oy τ x0 y0 t).aestronglyMeasurable
    (c0 := 2 * L * ‖xbar f L 0‖) [fun ξ => 10 * L * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.2‖] ?_ ?_
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rw [hv]
    exact hz.norm.const_mul _
  · intro ξ
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [Real.norm_eq_abs, abs_of_nonneg (H.moreauResidual_nonneg _)]
    exact H.moreauResidual_le _

lemma integral_split {X : Type*} [MeasurableSpace X] {P : Measure X} (hP : P.real Set.univ = 1)
    (c C : ℝ) (T : ℕ) (a b : ℕ → X → ℝ) (ha : ∀ t, Integrable (a t) P)
    (hb : ∀ t, Integrable (b t) P) :
    ∫ ξ, (c * (C + ∑ t ∈ range T, a t ξ) + ∑ t ∈ range T, b t ξ) ∂P =
      c * (C + ∑ t ∈ range T, ∫ ξ, a t ξ ∂P) + ∑ t ∈ range T, ∫ ξ, b t ξ ∂P := by
  have hfin : IsFiniteMeasure P := by
    refine ⟨?_⟩
    by_contra h
    have htop : P Set.univ = ⊤ := not_lt_top_iff.mp h
    have : P.real Set.univ = 0 := by rw [Measure.real, htop, ENNReal.toReal_top]
    rw [this] at hP
    exact zero_ne_one hP
  have h1 : Integrable (fun ξ => ∑ t ∈ range T, a t ξ) P := integrable_finsetSum _ fun t _ => ha t
  have h2 : Integrable (fun ξ => ∑ t ∈ range T, b t ξ) P := integrable_finsetSum _ fun t _ => hb t
  have h3 : Integrable (fun ξ => C + ∑ t ∈ range T, a t ξ) P := (integrable_const C).add h1
  have h4 : Integrable (fun ξ => c * (C + ∑ t ∈ range T, a t ξ)) P := h3.const_mul c
  have e1 : ∫ ξ, (c * (C + ∑ t ∈ range T, a t ξ) + ∑ t ∈ range T, b t ξ) ∂P =
      ∫ ξ, c * (C + ∑ t ∈ range T, a t ξ) ∂P + ∫ ξ, ∑ t ∈ range T, b t ξ ∂P := integral_add h4 h2
  have e2 : ∫ ξ, c * (C + ∑ t ∈ range T, a t ξ) ∂P = c * ∫ ξ, (C + ∑ t ∈ range T, a t ξ) ∂P :=
    integral_const_mul c _
  have e3 : ∫ ξ, (C + ∑ t ∈ range T, a t ξ) ∂P = ∫ _ : X, C ∂P + ∫ ξ, ∑ t ∈ range T, a t ξ ∂P :=
    integral_add (integrable_const C) h1
  have e4 : ∫ ξ, ∑ t ∈ range T, a t ξ ∂P = ∑ t ∈ range T, ∫ ξ, a t ξ ∂P :=
    integral_finsetSum _ fun t _ => ha t
  have e5 : ∫ ξ, ∑ t ∈ range T, b t ξ ∂P = ∑ t ∈ range T, ∫ ξ, b t ξ ∂P :=
    integral_finsetSum _ fun t _ => hb t
  have e6 : ∫ _ : X, C ∂P = C := by rw [integral_const, hP, one_smul]
  rw [e1, e2, e3, e4, e5, e6]

lemma expected_moreau (H : Hyp f gx gy L μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) {τ : ℝ} (hτ : 0 < τ)
    (hs : 3 * L * τ ≤ 1) (x0 : E) (y0 : F) (T : ℕ) :
    ∫ ξ, ∑ t ∈ range T, μy * τ * moreauResidual f L (path Gx Gy L μy τ x0 y0 ξ t).2.2 ^ 2
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      2 ^ 19 * L * ((statePotential f L (x0, y0, x0) - minimaxValue f) +
        T * (4 * L * τ ^ 2 * σ ^ 2)) + T * (24 * L ^ 2 * τ ^ 3 * μy * σ ^ 2) := by
  have hL := H.hL
  have hμ := H.hμy
  set P := Measure.infinitePi fun _ : ℕ => p with hP
  have hres : ∀ t, Integrable (fun ξ : ℕ → Ω =>
      μy * τ * moreauResidual f L (path Gx Gy L μy τ x0 y0 ξ t).2.2 ^ 2) P := fun t =>
    ((memLp_residual H ox oy τ x0 y0 t).integrable_sq).const_mul _
  have hn1 : ∀ t, Integrable (fun ξ => ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) P :=
    fun t => (noise1_sq H ox oy μy τ x0 y0 t).1
  have hn2 : ∀ t, Integrable (fun ξ => ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) P :=
    fun t => (noise2_sq H ox oy μy τ x0 y0 t).1
  have hmi : ∀ t, Integrable (fun ξ => martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
      (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
      (noise2 gy Gx Gy L μy τ x0 y0 ξ t)) P := fun t => (martingale_props H ox oy τ x0 y0 t).1
  have hterm : ∀ t, Integrable (fun ξ => 2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
      ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) -
      martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
        (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
        (noise2 gy Gx Gy L μy τ x0 y0 ξ t)) P := fun t =>
    (((hn1 t).add (hn2 t)).const_mul _).sub (hmi t)
  have hterm2 : ∀ t, Integrable (fun ξ => 24 * L ^ 2 * τ ^ 3 * μy *
      ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) P := fun t => (hn1 t).const_mul _
  have hpath : ∀ ξ : ℕ → Ω, ∑ t ∈ range T,
      μy * τ * moreauResidual f L (path Gx Gy L μy τ x0 y0 ξ t).2.2 ^ 2 ≤
      2 ^ 19 * L * ((statePotential f L (x0, y0, x0) - minimaxValue f) +
        ∑ t ∈ range T, (2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
          ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) -
          martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
            (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
            (noise2 gy Gx Gy L μy τ x0 y0 ξ t))) +
      ∑ t ∈ range T, 24 * L ^ 2 * τ ^ 3 * μy * ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 := by
    intro ξ
    exact H.moreau_sum hτ hs (fun t => path Gx Gy L μy τ x0 y0 ξ t)
      (fun t => noise1 gx Gx Gy L μy τ x0 y0 ξ t) (fun t => noise2 gy Gx Gy L μy τ x0 y0 ξ t)
      (fun t => path_rec gx gy Gx Gy L μy τ x0 y0 ξ t) T
  have hlhs : Integrable (fun ξ : ℕ → Ω => ∑ t ∈ range T,
      μy * τ * moreauResidual f L (path Gx Gy L μy τ x0 y0 ξ t).2.2 ^ 2) P :=
    integrable_finsetSum _ fun t _ => hres t
  have hrhs : Integrable (fun ξ : ℕ → Ω =>
      2 ^ 19 * L * ((statePotential f L (x0, y0, x0) - minimaxValue f) +
        ∑ t ∈ range T, (2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
          ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) -
          martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
            (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
            (noise2 gy Gx Gy L μy τ x0 y0 ξ t))) +
      ∑ t ∈ range T, 24 * L ^ 2 * τ ^ 3 * μy * ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) P :=
    (((integrable_const _).add (integrable_finsetSum _ fun t _ => hterm t)).const_mul _).add
      (integrable_finsetSum _ fun t _ => hterm2 t)
  refine (integral_mono hlhs hrhs hpath).trans ?_
  have hprob : P.real Set.univ = 1 := by
    rw [hP]
    simp
  refine (integral_split (P := P) hprob (2 ^ 19 * L)
    (statePotential f L (x0, y0, x0) - minimaxValue f) T
    (fun t ξ => 2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
          ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) -
          martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
            (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
            (noise2 gy Gx Gy L μy τ x0 y0 ξ t))
    (fun t ξ => 24 * L ^ 2 * τ ^ 3 * μy * ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2)
    hterm hterm2).le.trans ?_
  have hA : ∀ t ∈ range T, ∫ ξ, (2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
      ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) -
      martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
        (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
        (noise2 gy Gx Gy L μy τ x0 y0 ξ t)) ∂P ≤ 4 * L * τ ^ 2 * σ ^ 2 := by
    intro t _
    have hsum : Integrable (fun ξ : ℕ → Ω => ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
        ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) P := (hn1 t).add (hn2 t)
    have hmul : Integrable (fun ξ : ℕ → Ω => 2 * L * τ ^ 2 *
        (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 + ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2)) P :=
      hsum.const_mul _
    have e1 : ∫ ξ, (2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
        ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) -
        martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
          (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
          (noise2 gy Gx Gy L μy τ x0 y0 ξ t)) ∂P =
        ∫ ξ, 2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
          ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) ∂P -
        ∫ ξ, martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
          (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
          (noise2 gy Gx Gy L μy τ x0 y0 ξ t) ∂P := integral_sub hmul (hmi t)
    have e2 : ∫ ξ, 2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
        ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) ∂P =
        2 * L * τ ^ 2 * ∫ ξ, (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
          ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) ∂P := integral_const_mul _ _
    have e3 : ∫ ξ, (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
        ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) ∂P =
        ∫ ξ, ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 ∂P +
          ∫ ξ, ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 ∂P := integral_add (hn1 t) (hn2 t)
    rw [e1, e2, e3, (martingale_props H ox oy τ x0 y0 t).2, sub_zero]
    have h1 := (noise1_sq H ox oy μy τ x0 y0 t).2
    have h2 := (noise2_sq H ox oy μy τ x0 y0 t).2
    have h0 : 0 ≤ 2 * L * τ ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) h0]
  have hB : ∀ t ∈ range T, ∫ ξ, 24 * L ^ 2 * τ ^ 3 * μy *
      ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 ∂P ≤ 24 * L ^ 2 * τ ^ 3 * μy * σ ^ 2 := by
    intro t _
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (noise1_sq H ox oy μy τ x0 y0 t).2 (by positivity)
  have hsA := sum_le_sum hA
  have hsB := sum_le_sum hB
  rw [sum_const, card_range, nsmul_eq_mul] at hsA hsB
  have h19 : (0 : ℝ) ≤ 2 ^ 19 * L := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsA h19]

end Expectation

end OracleTemplate.NonconvexPL
