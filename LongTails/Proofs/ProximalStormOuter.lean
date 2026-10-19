import LongTails.Proofs.ProximalStormTuning
import LongTails.Algorithms.ProximalStorm

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.ProximalStorm

lemma aNext_sq {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) :
    aNext lam A ^ 2 = lam * (A + aNext lam A) := by
  have hs : Real.sqrt (lam ^ 2 + 4 * lam * A) ^ 2 = lam ^ 2 + 4 * lam * A :=
    Real.sq_sqrt (by positivity)
  unfold aNext
  nlinarith [hs]

lemma aNext_pos {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) : 0 < aNext lam A := by
  unfold aNext; positivity

lemma sqrt_growth {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A) :
    Real.sqrt A + Real.sqrt lam / 2 ≤ Real.sqrt (A + aNext lam A) := by
  have hs : Real.sqrt (lam * A) ≤ Real.sqrt (lam ^ 2 + 4 * lam * A) / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith
  have hge : (Real.sqrt A + Real.sqrt lam / 2) ^ 2 ≤ A + aNext lam A := by
    have h1 : (Real.sqrt A + Real.sqrt lam / 2) ^ 2 =
        A + Real.sqrt (lam * A) + lam / 4 := by
      rw [add_sq, Real.sq_sqrt hA, Real.sqrt_mul hlam.le]
      have := Real.sq_sqrt hlam.le
      nlinarith
    rw [h1]; unfold aNext; linarith
  calc Real.sqrt A + Real.sqrt lam / 2 = Real.sqrt ((Real.sqrt A + Real.sqrt lam / 2) ^ 2) := by
        rw [Real.sqrt_sq (by positivity)]
    _ ≤ _ := Real.sqrt_le_sqrt hge

noncomputable def accA (lam : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => accA lam k + aNext lam (accA lam k)

lemma accA_nonneg {lam : ℝ} (hlam : 0 < lam) : ∀ k, 0 ≤ accA lam k
  | 0 => le_rfl
  | k + 1 => by
      have := accA_nonneg hlam k
      have := aNext_pos hlam this
      simp only [accA]; linarith

lemma accA_ge {lam : ℝ} (hlam : 0 < lam) (k : ℕ) : lam * (k : ℝ) ^ 2 / 4 ≤ accA lam k := by
  have hs : ∀ k : ℕ, (k : ℝ) * Real.sqrt lam / 2 ≤ Real.sqrt (accA lam k) := by
    intro k
    induction k with
    | zero => simp [accA]
    | succ k ih =>
        have := sqrt_growth hlam (accA_nonneg hlam k)
        simp only [accA]; push_cast; linarith
  have h := hs k
  have h0 : 0 ≤ (k : ℝ) * Real.sqrt lam / 2 := by positivity
  have h2 := pow_le_pow_left₀ h0 h 2
  rw [Real.sq_sqrt (accA_nonneg hlam k), div_pow, mul_pow, Real.sq_sqrt hlam.le] at h2
  linarith

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] {Ω : Type} [MeasurableSpace Ω]

section HPE

variable {p : Measure Ω} {f : E → ℝ} {g : E → Ω → E} {Lbar Γ : ℝ} {xstar : E}

lemma Hyp.hpe_step (H : Hyp p f g Lbar Γ xstar) {lam A : ℝ} (hlam : 0 < lam) (hA : 0 ≤ A)
    (y z y' : E) :
    (A + aNext lam A) * (f y' - f xstar) +
        1 / 2 * ‖z - aNext lam A • gradient f y' - xstar‖ ^ 2 +
        (A + aNext lam A) / (2 * lam) * ‖y' - mixPt lam A y z‖ ^ 2 ≤
      A * (f y - f xstar) + 1 / 2 * ‖z - xstar‖ ^ 2 +
        (A + aNext lam A) / (2 * lam) *
          ‖lam • phiGrad f lam (mixPt lam A y z) y'‖ ^ 2 := by
  set aN := aNext lam A
  set A' := A + aN
  set v := gradient f y'
  set xt := mixPt lam A y z
  have haN := aNext_pos hlam hA
  have hA' : 0 < A' := by simp only [A']; linarith
  have hsq : aN ^ 2 = lam * A' := aNext_sq hlam hA
  have c1 := Gradient.convex_support H.convex H.grad y' xstar
  have c2 := Gradient.convex_support H.convex H.grad y' y
  have hmix : A' • xt = A • y + aN • z := by
    have e1 : A' * (A / (A + aNext lam A)) = A := by simp only [A', aN]; field_simp
    have e2 : A' * (aNext lam A / (A + aNext lam A)) = aN := by simp only [A', aN]; field_simp
    simp only [xt, mixPt, smul_add, smul_smul, e1, e2]
  have hφ : lam • phiGrad f lam xt y' = lam • v + (y' - xt) := by
    simp only [phiGrad, smul_add, smul_smul]
    rw [mul_one_div_cancel hlam.ne', one_smul]
  have hnorm : ‖lam • v + (y' - xt)‖ ^ 2 =
      lam ^ 2 * ‖v‖ ^ 2 + 2 * lam * ⟪v, y' - xt⟫ + ‖y' - xt‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp; ring
  have hz : ‖z - aN • v - xstar‖ ^ 2 =
      ‖z - xstar‖ ^ 2 - 2 * aN * ⟪v, z - xstar⟫ + aN ^ 2 * ‖v‖ ^ 2 := by
    rw [show z - aN • v - xstar = (z - xstar) - aN • v by abel, norm_sub_sq_real,
      inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm]
    ring
  have hinner : A * ⟪v, y - y'⟫ + aN * ⟪v, xstar - y'⟫ + aN * ⟪v, z - xstar⟫ =
      A' * ⟪v, xt - y'⟫ := by
    have : A' * ⟪v, xt - y'⟫ = ⟪v, A' • xt⟫ - A' * ⟪v, y'⟫ := by
      rw [inner_sub_right, real_inner_smul_right]; ring
    rw [this, hmix]
    simp only [inner_sub_right, inner_add_right, real_inner_smul_right, A']
    ring
  rw [hφ, hnorm, hz]
  have hfin : (A' / (2 * lam)) * (lam ^ 2 * ‖v‖ ^ 2) = aN ^ 2 / 2 * ‖v‖ ^ 2 := by
    rw [hsq]; field_simp
  have hfin2 : (A' / (2 * lam)) * (2 * lam * ⟪v, y' - xt⟫) = -(A' * ⟪v, xt - y'⟫) := by
    rw [show y' - xt = -(xt - y') by abel, inner_neg_right]; field_simp
  have hexp : A' / (2 * lam) * (lam ^ 2 * ‖v‖ ^ 2 + 2 * lam * ⟪v, y' - xt⟫ + ‖y' - xt‖ ^ 2) =
      aN ^ 2 / 2 * ‖v‖ ^ 2 - A' * ⟪v, xt - y'⟫ + A' / (2 * lam) * ‖y' - xt‖ ^ 2 := by
    rw [mul_add, mul_add, hfin, hfin2]; ring
  rw [hexp]
  simp only [A'] at hinner ⊢
  nlinarith [mul_le_mul_of_nonneg_left c1 haN.le, mul_le_mul_of_nonneg_left c2 hA]

end HPE

end OracleTemplate.ProximalStorm

namespace OracleTemplate.ProximalStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]

noncomputable def batchSum (g : E → Ω → E) (y : E) (ξ : ℕ → Ω) (n1 m : ℕ) : E :=
  ∑ i ∈ Finset.range m, g y (ξ (n1 + i))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma measurable_batchSum {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    {Y : (ℕ → Ω) → E} (hY : Measurable Y) (n1 m : ℕ) :
    Measurable fun ξ => batchSum g (Y ξ) ξ n1 m := by
  unfold batchSum
  exact Finset.measurable_sum _ fun i _ => hg.comp (hY.prodMk (measurable_pi_apply (n1 + i)))

section Batch

variable {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
  {Lbar Γ : ℝ} {xstar : E}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

lemma Hyp.batch_tower (H : Hyp p f g Lbar Γ xstar) {n1 : ℕ} (Wt : (ℕ → Ω) → ℝ)
    (hWt : Measurable Wt) (hWt0 : ∀ ξ, 0 ≤ Wt ξ) (U Y : (ℕ → Ω) → E) (hU : Measurable U)
    (hY : Measurable Y)
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n1 → ξ i = ξ' i) →
      Wt ξ = Wt ξ' ∧ U ξ = U ξ' ∧ Y ξ = Y ξ') (c : ℝ) :
    ∀ m : ℕ, ∫⁻ ξ, ENNReal.ofReal (Wt ξ * ‖U ξ - c • (batchSum g (Y ξ) ξ n1 m -
        (m : ℝ) • gradient f (Y ξ))‖ ^ 2) ∂P ≤
      ∫⁻ ξ, ENNReal.ofReal (Wt ξ * ‖U ξ‖ ^ 2) ∂P +
        m * ∫⁻ ξ, ENNReal.ofReal (Wt ξ * (c ^ 2 * (Γ ^ 2 * ‖gradient f (Y ξ)‖ ^ 2))) ∂P
  | 0 => by simp [batchSum]
  | m + 1 => by
      have ih := H.batch_tower Wt hWt hWt0 U Y hU hY hdep c m
      set V : (ℕ → Ω) → E := fun ξ => U ξ - c • (batchSum g (Y ξ) ξ n1 m -
        (m : ℝ) • gradient f (Y ξ))
      have hVm : Measurable V :=
        hU.sub (((measurable_batchSum H.meas hY n1 m).sub
          ((H.grad_continuous.measurable.comp hY).const_smul _)).const_smul _)
      set S : (ℕ → Ω) → ℝ × E × E := fun ξ => (Wt ξ, V ξ, Y ξ)
      have hS : Measurable S := hWt.prodMk (hVm.prodMk hY)
      have hSdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n1 + m → ξ i = ξ' i) → S ξ = S ξ' := by
        intro ξ ξ' h
        obtain ⟨h1, h2, h3⟩ := hdep ξ ξ' fun i hi => h i (by omega)
        have hb : batchSum g (Y ξ) ξ n1 m = batchSum g (Y ξ') ξ' n1 m := by
          unfold batchSum
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [h3, h (n1 + i) (by simp at hi; omega)]
        simp only [S, V, Prod.mk.injEq]
        exact ⟨h1, by rw [h2, hb, h3], h3⟩
      set h : ℝ × E × E → Ω → ℝ := fun s ω =>
        max s.1 0 * ‖s.2.1 - c • (g s.2.2 ω - gradient f s.2.2)‖ ^ 2
      have hh : Measurable (Function.uncurry h) := by
        have h1 : Measurable fun z : (ℝ × E × E) × Ω => max z.1.1 0 := by fun_prop
        have h2 : Measurable fun z : (ℝ × E × E) × Ω => z.1.2.1 := by fun_prop
        have h3 : Measurable fun z : (ℝ × E × E) × Ω => g z.1.2.2 z.2 :=
          H.meas.comp ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
            measurable_snd)
        have h4 : Measurable fun z : (ℝ × E × E) × Ω => gradient f z.1.2.2 :=
          H.grad_continuous.measurable.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
        exact h1.mul ((h2.sub ((h3.sub h4).const_smul _)).norm.pow_const 2)
      have hpt : ∀ s : ℝ × E × E, Integrable (h s) p ∧
          ∫ ω, h s ω ∂p ≤ max s.1 0 * (‖s.2.1‖ ^ 2 + c ^ 2 * (Γ ^ 2 * ‖gradient f s.2.2‖ ^ 2)) := by
        intro s
        have hZ := H.zeta_int s.2.2
        have hW : Integrable (fun ω => -(c • (g s.2.2 ω - gradient f s.2.2))) p :=
          (hZ.smul c).neg
        have hW2 : Integrable (fun ω => ‖-(c • (g s.2.2 ω - gradient f s.2.2))‖ ^ 2) p := by
          simp_rw [norm_neg, norm_smul, mul_pow]
          exact (H.var_int s.2.2).const_mul _
        have hW0 : ∫ ω, -(c • (g s.2.2 ω - gradient f s.2.2)) ∂p = 0 := by
          rw [integral_neg, integral_smul, H.zeta_mean, smul_zero, neg_zero]
        obtain ⟨hi, he⟩ := sq_norm_add_mean_zero s.2.1 hW hW2 hW0
        have hrw : ∀ ω, s.2.1 + -(c • (g s.2.2 ω - gradient f s.2.2)) =
            s.2.1 - c • (g s.2.2 ω - gradient f s.2.2) := fun ω => by abel
        simp_rw [hrw] at hi he
        refine ⟨hi.const_mul _, ?_⟩
        rw [integral_const_mul, he]
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        simp_rw [norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
        rw [integral_const_mul]
        have := H.sgc s.2.2
        nlinarith [sq_nonneg c]
      have hmax : ∀ ξ, max (Wt ξ) 0 = Wt ξ := fun ξ => max_eq_left (hWt0 ξ)
      have hrun : ∀ ξ, ENNReal.ofReal (Wt ξ * ‖U ξ - c • (batchSum g (Y ξ) ξ n1 (m + 1) -
          ((m + 1 : ℕ) : ℝ) • gradient f (Y ξ))‖ ^ 2) = ENNReal.ofReal (h (S ξ) (ξ (n1 + m))) := by
        intro ξ
        have hv : U ξ - c • (batchSum g (Y ξ) ξ n1 (m + 1) - ((m + 1 : ℕ) : ℝ) • gradient f (Y ξ)) =
            V ξ - c • (g (Y ξ) (ξ (n1 + m)) - gradient f (Y ξ)) := by
          simp only [V, batchSum, Finset.sum_range_succ]
          push_cast
          module
        simp only [h, S, hmax, hv]
      simp_rw [hrun]
      have hGm : Measurable fun ξ => ENNReal.ofReal (Wt ξ * (c ^ 2 * (Γ ^ 2 *
          ‖gradient f (Y ξ)‖ ^ 2))) :=
        ENNReal.measurable_ofReal.comp (hWt.mul ((((H.grad_continuous.measurable.comp
          hY).norm.pow_const 2).const_mul _).const_mul _))
      have htw := tower_le p (n1 + m) S hS hSdep h hh
        (fun s ω => mul_nonneg (le_max_right _ _) (sq_nonneg _)) (fun s => (hpt s).1)
        (fun s => ENNReal.ofReal (max s.1 0 * ‖s.2.1‖ ^ 2) + ENNReal.ofReal (max s.1 0 *
          (c ^ 2 * (Γ ^ 2 * ‖gradient f s.2.2‖ ^ 2)))) (fun s => by
            rw [← ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) (sq_nonneg _))
              (mul_nonneg (le_max_right _ _) (by positivity))]
            apply ENNReal.ofReal_le_ofReal
            have := (hpt s).2
            linarith)
      simp only [S, hmax] at htw
      refine htw.trans ?_
      rw [lintegral_add_right _ hGm]
      calc ∫⁻ ξ, ENNReal.ofReal (Wt ξ * ‖V ξ‖ ^ 2) ∂P +
            ∫⁻ ξ, ENNReal.ofReal (Wt ξ * (c ^ 2 * (Γ ^ 2 * ‖gradient f (Y ξ)‖ ^ 2))) ∂P
          ≤ (∫⁻ ξ, ENNReal.ofReal (Wt ξ * ‖U ξ‖ ^ 2) ∂P +
              m * ∫⁻ ξ, ENNReal.ofReal (Wt ξ * (c ^ 2 * (Γ ^ 2 * ‖gradient f (Y ξ)‖ ^ 2))) ∂P) +
            ∫⁻ ξ, ENNReal.ofReal (Wt ξ * (c ^ 2 * (Γ ^ 2 * ‖gradient f (Y ξ)‖ ^ 2))) ∂P := by
            gcongr
        _ = _ := by push_cast; ring

end Batch

noncomputable def blockStep (g : E → Ω → E) (lam eta a : ℝ) (T0 W B j n : ℕ) (o : ℝ × E × E)
    (ξ : ℕ → Ω) : ℝ × E × E :=
  (o.1 + aNext lam o.1,
    (innerRun g lam eta a (mixPt lam o.1 o.2.1 o.2.2) ξ n (T0 + j)).1,
    o.2.2 - (aNext lam o.1 / B) • batchSum g
      (innerRun g lam eta a (mixPt lam o.1 o.2.1 o.2.2) ξ n (T0 + j)).1 ξ (n + T0 + W) B)

noncomputable def outerPot (f : E → ℝ) (xstar : E) (o : ℝ × E × E) : ℝ :=
  o.1 * (f o.2.1 - f xstar) + 1 / 2 * ‖o.2.2 - xstar‖ ^ 2

noncomputable def wTrunc (f : E → ℝ) (lam M : ℝ) (x : E) : ℝ :=
  if ‖x - prox f lam x‖ ^ 2 ≤ M then 1 else 0

section Block

variable {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
  {Lbar Γ : ℝ} {xstar : E}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

omit [SecondCountableTopology E] in
lemma Hyp.measurable_wTrunc (H : Hyp p f g Lbar Γ xstar) {lam : ℝ} (hlam : 0 < lam) (M : ℝ) :
    Measurable (wTrunc f lam M) := by
  unfold wTrunc
  exact Measurable.ite (measurableSet_le (H.dist2_continuous hlam).measurable measurable_const)
    measurable_const measurable_const

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma Hyp.outerPot_nonneg (H : Hyp p f g Lbar Γ xstar) (o : ℝ × E × E) (h : 0 ≤ o.1) :
    0 ≤ outerPot f xstar o := by
  unfold outerPot
  have := H.min (mem_univ o.2.1)
  simp only [mem_ofPred_eq] at this
  have : 0 ≤ f o.2.1 - f xstar := by linarith
  positivity

end Block

end OracleTemplate.ProximalStorm
