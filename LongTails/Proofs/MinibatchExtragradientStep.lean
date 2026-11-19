import LongTails.Algorithms.MinibatchExtragradient
import LongTails.Proofs.RegularizedProxEgAssembly
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace LongTails.Proofs.MinibatchExtragradientStep

open OracleTemplate OracleTemplate.QueryPlan
open OracleTemplate.StochasticCohypomonotone (evalP evalP_bind evalP_map evalP_ask lintegral_split
  lintegral_tuple batch_integrable batch_lintegral_sq)
open LongTails.Algorithms.MinibatchExtragradient
open LongTails.Setups.StochasticGeneralizedMonotone (IsStochasticOperator)

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma evalP_batchSum (g : E → Ω → E) (x : E) :
    ∀ (b : ℕ) (ξ : ℕ → Ω), evalP g (batchSum x b) ξ = ∑ i : Fin b, g x (ξ i)
  | 0, ξ => by simp [evalP, batchSum, sampledEval]
  | b + 1, ξ => by
      rw [batchSum, evalP_ask, evalP_map, evalP_batchSum g x b, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.add_comm]

noncomputable def xbar (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E) (ξ : ℕ → Ω) : E :=
  x - γ • ((1 / (b : ℝ)) • ∑ i : Fin b, g x (ξ i))

noncomputable def xnext (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E) (ξ : ℕ → Ω) : E :=
  x - γ • ((1 / (b : ℝ)) • ∑ i : Fin b, g (xbar g γ b x ξ) (ξ (b + i)))

lemma evalP_extrapolate (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E) (ξ : ℕ → Ω) :
    evalP g (extrapolate γ b x) ξ = xbar g γ b x ξ := by
  rw [extrapolate, evalP_map, evalP_batchSum]
  rfl

lemma evalP_egStep (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E) (ξ : ℕ → Ω) :
    evalP g (egStep γ b x) ξ = xnext g γ b x ξ := by
  rw [egStep, evalP_bind, evalP_extrapolate, evalP_map, evalP_batchSum]
  rfl

lemma evalP_stopped_zero (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E) (ξ : ℕ → Ω) :
    evalP g (stoppedPlan γ b 0 x) ξ = xbar g γ b x ξ :=
  evalP_extrapolate g γ b x ξ

lemma evalP_stopped_succ (g : E → Ω → E) (γ : ℝ) (b n : ℕ) (x : E) (ξ : ℕ → Ω) :
    evalP g (stoppedPlan γ b (n + 1) x) ξ =
      evalP g (stoppedPlan γ b n (xnext g γ b x ξ)) (fun i => ξ (b + b + i)) := by
  have h := evalP_bind g (egStep γ b x) (fun y => stoppedPlan γ b n y) ξ
  rw [evalP_egStep] at h
  exact h

lemma stopLen_eq (b n : ℕ) : stopLen b n = b + (b + b) * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stopLen, ih]; ring

lemma scalar_key (a p s D f : ℝ) (hD0 : 0 ≤ D)
    (hf0 : 0 ≤ f) (hD : D ≤ a / 2 + p + s) (hf : f ≤ 3 / 2 * a + p) :
    D ^ 2 - a ^ 2 + 16 / 55 * f ^ 2 ≤ 26 * (p ^ 2 + s ^ 2) := by
  have h1 : D ^ 2 ≤ (a / 2 + p + s) ^ 2 := pow_le_pow_left₀ hD0 hD 2
  have h2 : f ^ 2 ≤ (3 / 2 * a + p) ^ 2 := pow_le_pow_left₀ hf0 hf 2
  nlinarith [sq_nonneg (a - 20 * p), sq_nonneg (a - 20 * s), sq_nonneg (p - s)]

lemma pathwise {F : E → E} {L ρ γ : ℝ} (hγ : L * γ = 1 / 2) (hγ0 : 0 < γ)
    (hρ : ρ ≤ γ / 10) (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (xs : E)
    (hmin : ∀ x, -ρ * ‖F x‖ ^ 2 ≤ ⟪F x, x - xs⟫) (x e1 e2 : E) :
    ‖x - γ • (F (x - γ • (F x + e1)) + e2) - xs‖ ^ 2 +
        γ ^ 2 / 11 * ‖F (x - γ • (F x + e1))‖ ^ 2 ≤
      ‖x - xs‖ ^ 2 + 26 * γ ^ 2 * (‖e1‖ ^ 2 + ‖e2‖ ^ 2) -
        2 * γ * ⟪x - γ • (F x + e1) - xs, e2⟫ := by
  set G1 := F x + e1 with hG1
  set xb := x - γ • G1 with hxb
  set G2 := F xb + e2 with hG2
  have hexp : ‖x - γ • G2 - xs‖ ^ 2 = ‖x - xs‖ ^ 2 - 2 * γ * ⟪G2, x - xs⟫ + γ ^ 2 * ‖G2‖ ^ 2 := by
    rw [show x - γ • G2 - xs = (x - xs) - γ • G2 by abel, norm_sub_sq_real, inner_smul_right,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm]
    ring
  have hsplit : ⟪G2, x - xs⟫ = ⟪F xb, xb - xs⟫ + ⟪xb - xs, e2⟫ + γ * ⟪G2, G1⟫ := by
    have e : x - xs = (xb - xs) + γ • G1 := by rw [hxb]; abel
    rw [e, inner_add_right, inner_smul_right]
    simp only [hG2, inner_add_left]
    rw [real_inner_comm (xb - xs) e2]
  have hpol : ‖G2‖ ^ 2 - 2 * ⟪G2, G1⟫ = ‖G2 - G1‖ ^ 2 - ‖G1‖ ^ 2 := by
    rw [norm_sub_sq_real]
    ring
  have hxbx : ‖xb - x‖ = γ * ‖G1‖ := by
    rw [hxb, show x - γ • G1 - x = -(γ • G1) by abel, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hγ0]
  have hLx : ‖F xb - F x‖ ≤ ‖G1‖ / 2 := by
    have h := hlip xb x
    rw [hxbx] at h
    have e : L * (γ * ‖G1‖) = ‖G1‖ / 2 := by rw [← mul_assoc, hγ]; ring
    linarith
  have hD : ‖G2 - G1‖ ≤ ‖G1‖ / 2 + ‖e1‖ + ‖e2‖ := by
    have e : G2 - G1 = (F xb - F x) + (e2 - e1) := by rw [hG2, hG1]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le e2 e1
    linarith
  have hf : ‖F xb‖ ≤ 3 / 2 * ‖G1‖ + ‖e1‖ := by
    have e : F xb = (F xb - F x) + (G1 - e1) := by rw [hG1]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le G1 e1
    linarith
  have hkey := scalar_key ‖G1‖ ‖e1‖ ‖e2‖ ‖G2 - G1‖ ‖F xb‖ (norm_nonneg _) (norm_nonneg _) hD hf
  have hm := hmin xb
  have hρf : 2 * γ * ρ * ‖F xb‖ ^ 2 ≤ γ ^ 2 / 5 * ‖F xb‖ ^ 2 := by
    have : 2 * γ * ρ ≤ γ ^ 2 / 5 := by nlinarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
  rw [hexp, hsplit]
  have hm2 : -(2 * γ) * ⟪F xb, xb - xs⟫ ≤ 2 * γ * ρ * ‖F xb‖ ^ 2 := by nlinarith
  have hkey2 := mul_le_mul_of_nonneg_left hkey hγ2
  have e3 : γ ^ 2 * ‖G2‖ ^ 2 - 2 * γ * (γ * ⟪G2, G1⟫) = γ ^ 2 * (‖G2 - G1‖ ^ 2 - ‖G1‖ ^ 2) := by
    rw [← hpol]
    ring
  nlinarith

section Expectation

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma batch_lintegral_affine {F : E → E} {g : E → Ω → E} {σ : ℝ}
    (hg : IsStochasticOperator μ F g σ) (z y : E) (C α β : ℝ) (hα : 0 ≤ α) {b : ℕ} (hb : 0 < b)
    (hnn : ∀ v : Fin b → Ω, 0 ≤ C + α * ‖(1 / (b : ℝ)) • ∑ i, g z (v i) - F z‖ ^ 2 -
      β * ⟪y, (1 / (b : ℝ)) • ∑ i, g z (v i) - F z⟫) :
    ∫⁻ v, ENNReal.ofReal (C + α * ‖(1 / (b : ℝ)) • ∑ i, g z (v i) - F z‖ ^ 2 -
        β * ⟪y, (1 / (b : ℝ)) • ∑ i, g z (v i) - F z⟫) ∂(Measure.pi fun _ : Fin b => μ) ≤
      ENNReal.ofReal (C + α * (σ ^ 2 / b)) := by
  obtain ⟨h0, h1, h2, h3⟩ := batch_integrable hg z hb
  set N : (Fin b → Ω) → E := fun v => (1 / (b : ℝ)) • ∑ i, g z (v i) - F z
  have hi1 : Integrable (fun v => β * ⟪y, N v⟫) (Measure.pi fun _ : Fin b => μ) :=
    (h0.const_inner y).const_mul _
  have hi2 : Integrable (fun v => α * ‖N v‖ ^ 2) (Measure.pi fun _ : Fin b => μ) :=
    h2.const_mul _
  have hi12 : Integrable (fun v => C + α * ‖N v‖ ^ 2) (Measure.pi fun _ : Fin b => μ) :=
    (integrable_const C).add hi2
  have hiall : Integrable (fun v => C + α * ‖N v‖ ^ 2 - β * ⟪y, N v⟫)
      (Measure.pi fun _ : Fin b => μ) := hi12.sub hi1
  rw [← ofReal_integral_eq_lintegral_ofReal hiall (Filter.Eventually.of_forall hnn)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_sub hi12 hi1, integral_add (integrable_const C) hi2,
    integral_const_mul, integral_const_mul, integral_inner h0, h1, inner_zero_right]
  simp only [integral_const, smul_eq_mul, mul_zero, sub_zero, probReal_univ, one_mul]
  have := mul_le_mul_of_nonneg_left h3 hα
  linarith

omit [CompleteSpace E] in
lemma xbar_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (γ : ℝ) (b : ℕ) :
    Measurable (fun z : E × (ℕ → Ω) => xbar g γ b z.1 z.2) := by
  have hS : Measurable (fun z : E × (ℕ → Ω) => ∑ i : Fin b, g z.1 (z.2 i)) :=
    Finset.measurable_sum _ fun i _ =>
      hg.comp (measurable_fst.prodMk ((measurable_pi_apply (i : ℕ)).comp measurable_snd))
  unfold xbar
  exact measurable_fst.sub ((hS.const_smul _).const_smul _)

omit [CompleteSpace E] in
lemma xnext_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (γ : ℝ) (b : ℕ) :
    Measurable (fun z : E × (ℕ → Ω) => xnext g γ b z.1 z.2) := by
  have hx := xbar_measurable hg γ b (Ω := Ω)
  have hS : Measurable (fun z : E × (ℕ → Ω) => ∑ i : Fin b, g (xbar g γ b z.1 z.2) (z.2 (b + i))) :=
    Finset.measurable_sum _ fun i _ =>
      hg.comp (hx.prodMk ((measurable_pi_apply (b + (i : ℕ))).comp measurable_snd))
  unfold xnext
  exact measurable_fst.sub ((hS.const_smul _).const_smul _)

omit [CompleteSpace E] in
lemma stopped_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (γ : ℝ)
    (b : ℕ) : ∀ n, Measurable (fun z : E × (ℕ → Ω) => evalP g (stoppedPlan γ b n z.1) z.2)
  | 0 => by
      simp_rw [evalP_stopped_zero]
      exact xbar_measurable hg γ b
  | n + 1 => by
      have ih := stopped_measurable hg γ b n
      simp_rw [evalP_stopped_succ]
      exact ih.comp ((xnext_measurable hg γ b).prodMk
        ((by fun_prop : Measurable (fun ξ : ℕ → Ω => fun i => ξ (b + b + i))).comp measurable_snd))

noncomputable def err1 (F : E → E) (g : E → Ω → E) (b : ℕ) (x : E) (u : Fin b → Ω) : E :=
  (1 / (b : ℝ)) • ∑ i, g x (u i) - F x

noncomputable def xbU (F : E → E) (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E) (u : Fin b → Ω) : E :=
  x - γ • (F x + err1 F g b x u)

noncomputable def err2 (F : E → E) (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E)
    (u v : Fin b → Ω) : E :=
  (1 / (b : ℝ)) • ∑ i, g (xbU F g γ b x u) (v i) - F (xbU F g γ b x u)

noncomputable def bound (F : E → E) (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x xs : E)
    (u v : Fin b → Ω) : ℝ :=
  (‖x - xs‖ ^ 2 + 26 * γ ^ 2 * ‖err1 F g b x u‖ ^ 2) +
    26 * γ ^ 2 * ‖(1 / (b : ℝ)) • ∑ i, g (xbU F g γ b x u) (v i) - F (xbU F g γ b x u)‖ ^ 2 -
    2 * γ * ⟪xbU F g γ b x u - xs,
      (1 / (b : ℝ)) • ∑ i, g (xbU F g γ b x u) (v i) - F (xbU F g γ b x u)⟫

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [MeasurableSpace Ω] in
lemma xbar_eq (F : E → E) (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E) (ξ : ℕ → Ω) :
    xbar g γ b x ξ = xbU F g γ b x (fun i => ξ i) := by
  unfold xbar xbU err1
  congr 2
  abel

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [MeasurableSpace Ω] in
lemma xnext_eq (F : E → E) (g : E → Ω → E) (γ : ℝ) (b : ℕ) (x : E) (ξ : ℕ → Ω) :
    xnext g γ b x ξ = x - γ • (F (xbU F g γ b x (fun i => ξ i)) +
      err2 F g γ b x (fun i => ξ i) (fun i => ξ (b + i))) := by
  unfold xnext err2
  rw [xbar_eq F]
  congr 2
  abel

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [MeasurableSpace Ω] in
lemma path_bound {F : E → E} {g : E → Ω → E} {L ρ γ : ℝ} (hγ : L * γ = 1 / 2) (hγ0 : 0 < γ)
    (hρ : ρ ≤ γ / 10) (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (xs : E)
    (hmin : ∀ x, -ρ * ‖F x‖ ^ 2 ≤ ⟪F x, x - xs⟫) {b : ℕ} (x : E) (u v : Fin b → Ω) :
    ‖x - γ • (F (xbU F g γ b x u) + err2 F g γ b x u v) - xs‖ ^ 2 +
        γ ^ 2 / 11 * ‖F (xbU F g γ b x u)‖ ^ 2 ≤ bound F g γ b x xs u v := by
  have h := pathwise hγ hγ0 hρ hlip xs hmin x (err1 F g b x u) (err2 F g γ b x u v)
  have e : x - γ • (F x + err1 F g b x u) = xbU F g γ b x u := rfl
  rw [e] at h
  unfold bound
  unfold err2 at h ⊢
  linarith

omit [CompleteSpace E] in
lemma bound_measurable {F : E → E} {g : E → Ω → E} (hF : Continuous F)
    (hg : Measurable (Function.uncurry g)) (γ : ℝ) (b : ℕ) (x xs : E) {α : Type*}
    [MeasurableSpace α] {U V : α → Fin b → Ω} (hU : Measurable U) (hV : Measurable V) :
    Measurable (fun a => bound F g γ b x xs (U a) (V a)) := by
  have hS1 : Measurable (fun a => ∑ i, g x (U a i)) :=
    Finset.measurable_sum _ fun i _ =>
      hg.comp (measurable_const.prodMk ((measurable_pi_apply i).comp hU))
  have he1 : Measurable (fun a => err1 F g b x (U a)) :=
    (hS1.const_smul _).sub measurable_const
  have hxb : Measurable (fun a => xbU F g γ b x (U a)) :=
    measurable_const.sub ((measurable_const.add he1).const_smul _)
  have hS2 : Measurable (fun a => ∑ i, g (xbU F g γ b x (U a)) (V a i)) :=
    Finset.measurable_sum _ fun i _ =>
      hg.comp (hxb.prodMk ((measurable_pi_apply i).comp hV))
  have he2 : Measurable (fun a =>
      (1 / (b : ℝ)) • ∑ i, g (xbU F g γ b x (U a)) (V a i) - F (xbU F g γ b x (U a))) :=
    (hS2.const_smul _).sub (hF.measurable.comp hxb)
  unfold bound
  exact ((measurable_const.add ((he1.norm.pow_const 2).const_mul _)).add
    ((he2.norm.pow_const 2).const_mul _)).sub (((hxb.sub measurable_const).inner he2).const_mul _)

lemma inner_bound {F : E → E} {g : E → Ω → E} {σ γ : ℝ} (hg : IsStochasticOperator μ F g σ)
    (hF : Continuous F) {b : ℕ} (hb : 0 < b) (x xs : E) (u : Fin b → Ω)
    (hnn : ∀ v, 0 ≤ bound F g γ b x xs u v) :
    ∫⁻ t, ENNReal.ofReal (bound F g γ b x xs u (fun i : Fin b => t i))
        ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ENNReal.ofReal ((‖x - xs‖ ^ 2 + 26 * γ ^ 2 * ‖err1 F g b x u‖ ^ 2) +
        26 * γ ^ 2 * (σ ^ 2 / b)) := by
  have hv : Measurable (fun v : Fin b → Ω => ENNReal.ofReal (bound F g γ b x xs u v)) :=
    (bound_measurable hF hg.measurable γ b x xs (U := fun _ : Fin b → Ω => u) (V := id)
      measurable_const measurable_id).ennreal_ofReal
  rw [lintegral_tuple μ (fun i : Fin b => (i : ℕ)) (fun i j h => Fin.ext h)
    (fun v => ENNReal.ofReal (bound F g γ b x xs u v)) hv]
  unfold bound at hnn ⊢
  exact batch_lintegral_affine hg (xbU F g γ b x u) (xbU F g γ b x u - xs)
    (‖x - xs‖ ^ 2 + 26 * γ ^ 2 * ‖err1 F g b x u‖ ^ 2) (26 * γ ^ 2) (2 * γ) (by positivity) hb hnn

lemma step_expect {F : E → E} {g : E → Ω → E} {L ρ γ σ : ℝ}
    (hg : IsStochasticOperator μ F g σ) (hγ : L * γ = 1 / 2) (hγ0 : 0 < γ)
    (hρ : ρ ≤ γ / 10) (hlip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖) (xs : E)
    (hmin : ∀ x, -ρ * ‖F x‖ ^ 2 ≤ ⟪F x, x - xs⟫) {b : ℕ} (hb : 0 < b) (x : E) :
    ∫⁻ ξ, (ENNReal.ofReal (‖xnext g γ b x ξ - xs‖ ^ 2) +
        ENNReal.ofReal (γ ^ 2 / 11) * ENNReal.ofReal (‖F (xbar g γ b x ξ)‖ ^ 2))
        ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ENNReal.ofReal (‖x - xs‖ ^ 2) + ENNReal.ofReal (52 * γ ^ 2 * (σ ^ 2 / b)) := by
  have hL0 : 0 < L := by
    by_contra h
    push Not at h
    nlinarith
  have hF : Continuous F := (LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0.le]; exact hlip a b).continuous
  have hc : (0 : ℝ) ≤ γ ^ 2 / 11 := by positivity
  have hpt : ∀ ξ : ℕ → Ω, ENNReal.ofReal (‖xnext g γ b x ξ - xs‖ ^ 2) +
      ENNReal.ofReal (γ ^ 2 / 11) * ENNReal.ofReal (‖F (xbar g γ b x ξ)‖ ^ 2) ≤
      ENNReal.ofReal (bound F g γ b x xs (fun i => ξ i) (fun i => ξ (b + i))) := by
    intro ξ
    rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hc (sq_nonneg _)),
      xnext_eq F, xbar_eq F]
    exact ENNReal.ofReal_le_ofReal (path_bound hγ hγ0 hρ hlip xs hmin x _ _)
  refine (lintegral_mono hpt).trans ?_
  have hbm : Measurable (fun q : (Fin b → Ω) × (ℕ → Ω) =>
      bound F g γ b x xs q.1 (fun i : Fin b => q.2 i)) :=
    bound_measurable hF hg.measurable γ b x xs (U := fun q : (Fin b → Ω) × (ℕ → Ω) => q.1)
      (V := fun q : (Fin b → Ω) × (ℕ → Ω) => fun i : Fin b => q.2 i) measurable_fst
      ((by fun_prop : Measurable (fun t : ℕ → Ω => fun i : Fin b => t i)).comp measurable_snd)
  have hsplit := lintegral_split μ b
    (fun u t => ENNReal.ofReal (bound F g γ b x xs u (fun i : Fin b => t i))) hbm.ennreal_ofReal
  beta_reduce at hsplit
  rw [hsplit]
  have hinner : ∀ u, ∫⁻ t, ENNReal.ofReal (bound F g γ b x xs u (fun i : Fin b => t i))
      ∂(Measure.infinitePi fun _ : ℕ => μ) ≤
      ENNReal.ofReal (‖x - xs‖ ^ 2 + 26 * γ ^ 2 * (σ ^ 2 / b)) +
        ENNReal.ofReal (26 * γ ^ 2) * ENNReal.ofReal (‖err1 F g b x u‖ ^ 2) := by
    intro u
    refine (inner_bound hg hF hb x xs u (fun v => le_trans (by positivity)
      (path_bound hγ hγ0 hρ hlip xs hmin x u v))).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 26 * γ ^ 2 by positivity),
      ← ENNReal.ofReal_add (show (0 : ℝ) ≤ ‖x - xs‖ ^ 2 + 26 * γ ^ 2 * (σ ^ 2 / b) by positivity)
        (mul_nonneg (show (0 : ℝ) ≤ 26 * γ ^ 2 by positivity) (sq_nonneg _))]
    congr 1
    ring
  refine (lintegral_mono hinner).trans ?_
  have hSx : Measurable (fun u : Fin b → Ω => ∑ i, g x (u i)) :=
    Finset.measurable_sum _ fun i _ =>
      hg.measurable.comp (measurable_const.prodMk (measurable_pi_apply i))
  have hm1 : Measurable (fun u : Fin b → Ω => ENNReal.ofReal (‖err1 F g b x u‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((((hSx.const_smul _).sub measurable_const).norm).pow_const 2)
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul _ hm1]
  have hv : ∫⁻ u, ENNReal.ofReal (‖err1 F g b x u‖ ^ 2) ∂(Measure.pi fun _ : Fin b => μ) ≤
      ENNReal.ofReal (σ ^ 2 / b) := batch_lintegral_sq hg x hb
  have hA : (0 : ℝ) ≤ ‖x - xs‖ ^ 2 + 26 * γ ^ 2 * (σ ^ 2 / b) := by positivity
  have hB : (0 : ℝ) ≤ 26 * γ ^ 2 * (σ ^ 2 / b) := by positivity
  have hC : (0 : ℝ) ≤ 52 * γ ^ 2 * (σ ^ 2 / b) := by positivity
  calc ENNReal.ofReal (‖x - xs‖ ^ 2 + 26 * γ ^ 2 * (σ ^ 2 / b)) +
        ENNReal.ofReal (26 * γ ^ 2) * ∫⁻ u, ENNReal.ofReal (‖err1 F g b x u‖ ^ 2)
          ∂(Measure.pi fun _ : Fin b => μ)
      ≤ ENNReal.ofReal (‖x - xs‖ ^ 2 + 26 * γ ^ 2 * (σ ^ 2 / b)) +
          ENNReal.ofReal (26 * γ ^ 2) * ENNReal.ofReal (σ ^ 2 / b) := by gcongr
    _ = ENNReal.ofReal (‖x - xs‖ ^ 2) + ENNReal.ofReal (52 * γ ^ 2 * (σ ^ 2 / b)) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 26 * γ ^ 2 by positivity),
          ← ENNReal.ofReal_add hA hB, ← ENNReal.ofReal_add (sq_nonneg _) hC]
        congr 1
        ring

end Expectation

end LongTails.Proofs.MinibatchExtragradientStep
