import LongTails.Proofs.GaussianVariationalExpectation

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GaussianVariational

open LongTails.Setups.GaussianVariationalInference

variable {d : ℕ}

lemma quad_zero {a b t0 : ℝ} (ht0 : 0 < t0) (h : ∀ t, |t| ≤ t0 → 0 ≤ t * a + t ^ 2 * b) :
    a = 0 := by
  by_contra ha
  have hb1 : 0 < |b| + 1 := by positivity
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · set s := min t0 (-a / (2 * (|b| + 1))) with hs
    have hs0 : 0 < s := lt_min ht0 (div_pos (by linarith) (by positivity))
    have hst : |s| ≤ t0 := by rw [abs_of_pos hs0]; exact min_le_left _ _
    have hsa : s ≤ -a / (2 * (|b| + 1)) := min_le_right _ _
    have hsa' : s * (2 * (|b| + 1)) ≤ -a := (le_div_iff₀ (by positivity)).mp hsa
    have h1 := h s hst
    have h2 : s ^ 2 * b ≤ s ^ 2 * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) (sq_nonneg s)
    nlinarith [abs_nonneg b]
  · set s := min t0 (a / (2 * (|b| + 1))) with hs
    have hs0 : 0 < s := lt_min ht0 (div_pos hpos (by positivity))
    have hst : |-s| ≤ t0 := by rw [abs_neg, abs_of_pos hs0]; exact min_le_left _ _
    have hsa : s ≤ a / (2 * (|b| + 1)) := min_le_right _ _
    have hsa' : s * (2 * (|b| + 1)) ≤ a := (le_div_iff₀ (by positivity)).mp hsa
    have h1 := h (-s) hst
    have h2 : (-s) ^ 2 * b ≤ (-s) ^ 2 * |b| :=
      mul_le_mul_of_nonneg_left (le_abs_self b) (sq_nonneg _)
    nlinarith [abs_nonneg b]

lemma neg_log_one_add_le {x : ℝ} (hx : -1 / 2 ≤ x) : -Real.log (1 + x) ≤ -x + 2 * x ^ 2 := by
  have hpos : 0 < 1 + x := by linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hl
  have hfrac : x / (1 + x) ≥ x - 2 * x ^ 2 := by
    rw [ge_iff_le, le_div_iff₀ hpos]
    nlinarith [sq_nonneg x]
  have hinv : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by field_simp; ring1
  linarith

lemma pinner_smul_right (m : Location d) (C : Scale d) (t : ℝ) (u : Location d) (U : Scale d) :
    pinner m C (t • u) (t • U) = t * pinner m C u U := by
  rw [pinner_comm, pinner_smul_left, pinner_comm]

lemma sqDist_smul (m u : Location d) (C U : Scale d) (t : ℝ) :
    sqDist (m + t • u) m (C + t • U) C = t ^ 2 * ((∑ i, u i ^ 2) + ∑ i, ∑ j, U i j ^ 2) := by
  unfold sqDist
  simp only [Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    add_sub_cancel_left, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma isLower_smul {U : Scale d} (hU : IsLower U) (t : ℝ) : IsLower (t • U) := by
  intro i j h
  simp [Pi.smul_apply, hU i j h]

lemma isLower_add {U W : Scale d} (hU : IsLower U) (hW : IsLower W) : IsLower (U + W) := by
  intro i j h
  simp [Pi.add_apply, hU i j h, hW i j h]

section Optimality

variable {L μ : ℝ} {V : Point d → ℝ}

def IsOptimal (V : Point d → ℝ) (ms : Location d) (Cs : Scale d) : Prop :=
  IsCholesky Cs ∧ ∀ m C, IsCholesky C → objective V ms Cs ≤ objective V m C

lemma objective_eq (V : Point d → ℝ) (m : Location d) (C : Scale d) :
    objective V m C = energy V m C - ∑ i, Real.log (C i i) := rfl

lemma opt_pinner (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsOptimal V ms Cs) (u : Location d) {U : Scale d} (hU : IsLower U) :
    pinner (meanLoc V ms Cs) (meanScale V ms Cs) u U = ∑ i, U i i / Cs i i := by
  set A := pinner (meanLoc V ms Cs) (meanScale V ms Cs) u U
  set B := (∑ i, u i ^ 2) + ∑ i, ∑ j, U i j ^ 2
  set s : Fin d → ℝ := fun i => U i i / Cs i i
  set M := ∑ i, |s i|
  have hCs := hopt.1
  have hpos : ∀ i, 0 < Cs i i := hCs.2
  have ht0 : 0 < 1 / (2 * (M + 1)) := by
    have : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
    positivity
  suffices hq : A - ∑ i, s i = 0 by
    have : A = ∑ i, s i := by linarith
    simpa [s] using this
  refine quad_zero (b := L / 2 * B + 2 * ∑ i, s i ^ 2) ht0 fun t ht => ?_
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hts : ∀ i, |t * s i| ≤ 1 / 2 := by
    intro i
    have hsi : |s i| ≤ M := Finset.single_le_sum (f := fun i => |s i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ i)
    rw [abs_mul]
    have h1 : |t| * |s i| ≤ 1 / (2 * (M + 1)) * M :=
      mul_le_mul ht hsi (abs_nonneg _) (le_of_lt ht0)
    have h2 : 1 / (2 * (M + 1)) * M ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
      linarith
    linarith
  have hdiag : ∀ i, (Cs + t • U) i i = Cs i i * (1 + t * s i) := by
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, s]
    rw [mul_add, mul_one, mul_left_comm, mul_div_cancel₀ _ (hpos i).ne']
  have hchol : IsCholesky (Cs + t • U) := by
    refine ⟨isLower_add hCs.1 (isLower_smul hU t), fun i => ?_⟩
    rw [hdiag i]
    have := neg_abs_le (t * s i)
    have := hts i
    have : 0 < 1 + t * s i := by linarith
    exact mul_pos (hpos i) this
  have hmin := hopt.2 (ms + t • u) (Cs + t • U) hchol
  have hlow : IsLower ((Cs + t • U) - Cs) := by
    rw [add_sub_cancel_left]
    exact isLower_smul hU t
  have heu := energy_upper h ms (ms + t • u) hlow
  rw [add_sub_cancel_left, add_sub_cancel_left, pinner_smul_right, sqDist_smul] at heu
  have hlog : ∀ i, -Real.log ((Cs + t • U) i i) ≤
      -Real.log (Cs i i) + (-(t * s i) + 2 * (t * s i) ^ 2) := by
    intro i
    rw [hdiag i, Real.log_mul (hpos i).ne' (by have := hts i; have := neg_abs_le (t * s i); linarith)]
    have := neg_log_one_add_le (show -1 / 2 ≤ t * s i by
      have := hts i; have := neg_abs_le (t * s i); linarith)
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hlog i
  rw [objective_eq, objective_eq] at hmin
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
  have he1 : ∑ i, (t * s i) ^ 2 = t ^ 2 * ∑ i, s i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he1] at hsum
  nlinarith

noncomputable def optScale (Cs : Scale d) : Scale d := fun i j => if i = j then 1 / Cs i i else 0

lemma pinner_optScale (Cs : Scale d) (u : Location d) (U : Scale d) :
    pinner 0 (optScale Cs) u U = ∑ i, U i i / Cs i i := by
  unfold pinner optScale
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [↓reduceIte]
    ring
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

lemma opt_pinner' (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsOptimal V ms Cs) (u : Location d) {U : Scale d} (hU : IsLower U) :
    pinner (meanLoc V ms Cs) (meanScale V ms Cs) u U = pinner 0 (optScale Cs) u U := by
  rw [opt_pinner h hopt u hU, pinner_optScale]

noncomputable def bregman (V : Point d → ℝ) (ms : Location d) (Cs : Scale d)
    (m : Location d) (C : Scale d) (ξ : Fin d → ℝ) : ℝ :=
  V (sample m C ξ) - V (sample ms Cs ξ) -
    ⟪gradient V (sample ms Cs ξ), sample m C ξ - sample ms Cs ξ⟫

noncomputable def bregmanMean (V : Point d → ℝ) (ms : Location d) (Cs : Scale d)
    (m : Location d) (C : Scale d) : ℝ :=
  ∫ ξ, bregman V ms Cs m C ξ ∂noiseLaw d

lemma integrable_bregman (h : Potential L μ V) (ms : Location d) {Cs C : Scale d}
    (m : Location d) (hC : IsLower (C - Cs)) :
    Integrable (bregman V ms Cs m C) (noiseLaw d) := by
  have hi := (integral_inner_grad h ms Cs (m - ms) hC).1
  unfold bregman
  simp_rw [sample_sub]
  exact ((integrable_V_sample h m C).subL (integrable_V_sample h ms Cs)).subL hi

lemma bregmanMean_eq (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsOptimal V ms Cs) (m : Location d) {C : Scale d} (hC : IsLower (C - Cs)) :
    bregmanMean V ms Cs m C = energy V m C - energy V ms Cs - ∑ i, (C - Cs) i i / Cs i i := by
  have hi := integral_inner_grad h ms Cs (m - ms) hC
  unfold bregmanMean bregman
  simp_rw [sample_sub]
  rw [integral_sub ((integrable_V_sample h m C).subL (integrable_V_sample h ms Cs)) hi.1,
    integral_sub (integrable_V_sample h m C) (integrable_V_sample h ms Cs), hi.2,
    opt_pinner h hopt (m - ms) hC]
  rfl

lemma bregmanMean_le_objective (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsOptimal V ms Cs) (m : Location d) {C : Scale d} (hC : IsCholesky C) :
    bregmanMean V ms Cs m C ≤ objective V m C - objective V ms Cs := by
  rw [bregmanMean_eq h hopt m (isLower_sub hC.1 hopt.1.1), objective_eq, objective_eq]
  have hterm : ∀ i, (C - Cs) i i / Cs i i ≥ Real.log (C i i) - Real.log (Cs i i) := by
    intro i
    have hc := hC.2 i
    have hs := hopt.1.2 i
    rw [← Real.log_div hc.ne' hs.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hc hs)
    simp only [Pi.sub_apply]
    have he : (C i i - Cs i i) / Cs i i = C i i / Cs i i - 1 := by field_simp
    linarith
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [Finset.sum_sub_distrib] at hs
  linarith

lemma bregmanMean_upper (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (m : Location d) {C : Scale d} (hC : IsLower (C - Cs)) :
    bregmanMean V ms Cs m C ≤ L / 2 * sqDist m ms C Cs := by
  have hpt : ∀ ξ, bregman V ms Cs m C ξ ≤ L / 2 * ‖sample m C ξ - sample ms Cs ξ‖ ^ 2 := by
    intro ξ
    have := h.upper (sample ms Cs ξ) (sample m C ξ)
    unfold bregman
    linarith
  have hn := isotropy_sub m ms C Cs
  have hm := integral_mono (integrable_bregman h ms m hC) (hn.1.const_mul (L / 2)) hpt
  rw [integral_const_mul, hn.2] at hm
  exact hm

lemma bregmanMean_lower (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (m : Location d) {C : Scale d} (hC : IsLower (C - Cs)) :
    μ / 2 * sqDist m ms C Cs ≤ bregmanMean V ms Cs m C := by
  have hpt : ∀ ξ, μ / 2 * ‖sample m C ξ - sample ms Cs ξ‖ ^ 2 ≤ bregman V ms Cs m C ξ := by
    intro ξ
    have := h.support (sample ms Cs ξ) (sample m C ξ)
    unfold bregman
    linarith
  have hn := isotropy_sub m ms C Cs
  have hm := integral_mono (hn.1.const_mul (μ / 2)) (integrable_bregman h ms m hC) hpt
  rw [integral_const_mul, hn.2] at hm
  exact hm

lemma tau_nonneg (d : ℕ) {κ : ℝ} (hκ : 1 ≤ κ) : 0 ≤ tau d κ := by
  unfold tau
  have : 0 ≤ Real.log (48 * κ) := Real.log_nonneg (by linarith)
  positivity

noncomputable def tailFn (d : ℕ) (τ : ℝ) (ξ : Fin d → ℝ) : ℝ :=
  64 / rexp 1 * rexp (sqNorm ξ / 4 - τ / 8)

lemma tail_mass (h : Potential L μ V) :
    Integrable (tailFn d (tau d (L / μ))) (noiseLaw d) ∧
      2 * (L / μ) * ∫ ξ, tailFn d (tau d (L / μ)) ξ ∂noiseLaw d ≤ 1 := by
  have hκ : 1 ≤ L / μ := (one_le_div h.pos).mpr h.le
  have ht := tail_integral d (tau d (L / μ))
  refine ⟨ht.1, ?_⟩
  unfold tailFn
  rw [ht.2]
  exact tail_budget hκ

lemma gradDiff_pinner (g g' : Point d) (ξ : Fin d → ℝ) :
    pinner (gradLoc g - gradLoc g') (gradScale g ξ - gradScale g' ξ)
      (gradLoc g - gradLoc g') (gradScale g ξ - gradScale g' ξ) ≤
      (1 + sqNorm ξ) * ‖g - g'‖ ^ 2 := by
  rw [← gradLoc_sub, ← gradScale_sub]
  exact pinner_grad_self_le (g - g') ξ

lemma expected_smoothness (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (m : Location d) {C : Scale d} (hC : IsLower (C - Cs)) :
    Integrable (fun ξ => pinner
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ)
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ))
      (noiseLaw d) ∧
    ∫ ξ, pinner
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ)
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ)
      ∂noiseLaw d ≤ 2 * (L * (2 + tau d (L / μ))) * bregmanMean V ms Cs m C := by
  set r := sqDist m ms C Cs
  set τ := tau d (L / μ)
  have hL := h.L_pos
  have hr : 0 ≤ r := sqDist_nonneg _ _ _ _
  have hκ : 1 ≤ L / μ := (one_le_div h.pos).mpr h.le
  have hτ : 0 ≤ τ := tau_nonneg d hκ
  have hΔ1 : ∀ ξ, ‖(gradient V (sample m C ξ) - gradient V (sample ms Cs ξ))‖ ^ 2 ≤ 2 * L * bregman V ms Cs m C ξ := fun ξ =>
    h.cocoercive (sample m C ξ) (sample ms Cs ξ)
  have hΔ2 : ∀ ξ, ‖(gradient V (sample m C ξ) - gradient V (sample ms Cs ξ))‖ ^ 2 ≤ 2 * L ^ 2 * r * (1 + sqNorm ξ) := by
    intro ξ
    have h1 := h.lip (sample m C ξ) (sample ms Cs ξ)
    have h2 := norm_sample_sub_sq_le m ms C Cs ξ
    have h3 : ‖(gradient V (sample m C ξ) - gradient V (sample ms Cs ξ))‖ ^ 2 ≤ L ^ 2 * ‖sample m C ξ - sample ms Cs ξ‖ ^ 2 := by
      have := norm_nonneg ((gradient V (sample m C ξ) - gradient V (sample ms Cs ξ)))
      rw [← mul_pow]
      exact pow_le_pow_left₀ this h1 2
    nlinarith [sq_nonneg L]
  have hpt : ∀ ξ, pinner
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ)
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ) ≤
      (1 + τ) * (2 * L * bregman V ms Cs m C ξ) + 2 * L ^ 2 * r * tailFn d τ ξ := by
    intro ξ
    have h1 := gradDiff_pinner (gradient V (sample m C ξ)) (gradient V (sample ms Cs ξ)) ξ
    have hS := sqNorm_nonneg ξ
    have h2 := tail_split (τ := τ) hS (sq_nonneg ‖(gradient V (sample m C ξ) - gradient V (sample ms Cs ξ))‖) (by positivity : 0 ≤ 2 * L ^ 2 * r)
      (by have := hΔ2 ξ; linarith)
    have h3 : (1 + τ) * ‖(gradient V (sample m C ξ) - gradient V (sample ms Cs ξ))‖ ^ 2 ≤ (1 + τ) * (2 * L * bregman V ms Cs m C ξ) :=
      mul_le_mul_of_nonneg_left (hΔ1 ξ) (by linarith)
    unfold tailFn
    linarith
  have hT := tail_mass h
  have hB := integrable_bregman h ms m hC
  have hR : Integrable (fun ξ => (1 + τ) * (2 * L * bregman V ms Cs m C ξ) +
      2 * L ^ 2 * r * tailFn d τ ξ) (noiseLaw d) :=
    ((hB.const_mul _).const_mul _).addL (hT.1.const_mul _)
  have hmeas : AEStronglyMeasurable (fun ξ => pinner
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ)
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ))
      (noiseLaw d) := by
    have hg1 := measurable_grad_sample h m C
    have hg2 := measurable_grad_sample h ms Cs
    unfold pinner gradLoc gradScale
    refine Measurable.aestronglyMeasurable ?_
    refine (Finset.measurable_sum _ fun i _ => ?_).add
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    · exact (((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg1).sub
        ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg2)).mul
        (((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg1).sub
        ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg2))
    · have hm1 : Measurable (fun ξ : Fin d → ℝ =>
          (if j ≤ i then gradient V (sample m C ξ) i * ξ j else 0) -
          (if j ≤ i then gradient V (sample ms Cs ξ) i * ξ j else 0)) := by
        split_ifs
        · exact (((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg1).mul
            (measurable_pi_apply j)).sub
            (((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg2).mul (measurable_pi_apply j))
        · exact measurable_const
      exact hm1.mul hm1
  have hint : Integrable (fun ξ => pinner
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ)
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ))
      (noiseLaw d) := by
    refine integrable_poly hmeas (2 * L ^ 2 * r) fun ξ => ?_
    have h1 := gradDiff_pinner (gradient V (sample m C ξ)) (gradient V (sample ms Cs ξ)) ξ
    have h0 := pinner_self_nonneg
      (gradLoc (gradient V (sample m C ξ)) - gradLoc (gradient V (sample ms Cs ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ - gradScale (gradient V (sample ms Cs ξ)) ξ)
    have hS := sqNorm_nonneg ξ
    rw [abs_of_nonneg h0]
    have h2 := mul_le_mul_of_nonneg_left (hΔ2 ξ) (by linarith : (0 : ℝ) ≤ 1 + sqNorm ξ)
    nlinarith
  refine ⟨hint, ?_⟩
  have hm := integral_mono hint hR hpt
  rw [integral_add ((hB.const_mul _).const_mul _) (hT.1.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul] at hm
  have hlow := bregmanMean_lower h (ms := ms) (Cs := Cs) m hC
  have htail : 2 * L ^ 2 * r * ∫ ξ, tailFn d τ ξ ∂noiseLaw d ≤ 2 * L * bregmanMean V ms Cs m C := by
    have h1 := hT.2
    have hμ := h.pos
    have h2 : 2 * L ^ 2 * r * ∫ ξ, tailFn d τ ξ ∂noiseLaw d =
        L * μ * r * (2 * (L / μ) * ∫ ξ, tailFn d τ ξ ∂noiseLaw d) := by
      field_simp
    rw [h2]
    have h3 : L * μ * r * (2 * (L / μ) * ∫ ξ, tailFn d τ ξ ∂noiseLaw d) ≤ L * μ * r * 1 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  unfold bregmanMean at htail hlow ⊢
  nlinarith

end Optimality

end OracleTemplate.GaussianVariational
