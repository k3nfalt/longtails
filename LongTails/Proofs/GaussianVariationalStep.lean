import LongTails.Proofs.GaussianVariationalVariance

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GaussianVariational

open LongTails.Setups.GaussianVariationalInference

variable {d : ℕ}

section Prox

lemma proxLog_sqrt_ge {η : ℝ} (hη : 0 < η) (y : ℝ) : |y| < Real.sqrt (y ^ 2 + 4 * η) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg y) (by linarith)

lemma proxLog_pos {η : ℝ} (hη : 0 < η) (y : ℝ) : 0 < proxLog η y := by
  unfold proxLog
  have := proxLog_sqrt_ge hη y
  have := neg_abs_le y
  linarith

lemma proxLog_root {η : ℝ} (hη : 0 < η) (y : ℝ) :
    proxLog η y * (proxLog η y - y) = η := by
  unfold proxLog
  have hs := Real.sq_sqrt (show 0 ≤ y ^ 2 + 4 * η by positivity)
  nlinarith

lemma proxLog_fixed {η c : ℝ} (hη : 0 < η) (hc : 0 < c) : proxLog η (c - η / c) = c := by
  unfold proxLog
  have he : (c - η / c) ^ 2 + 4 * η = (c + η / c) ^ 2 := by
    field_simp; ring1
  rw [he, Real.sqrt_sq (by positivity)]
  ring

lemma proxLog_sq_lip {η : ℝ} (hη : 0 < η) (y y' : ℝ) :
    (proxLog η y - proxLog η y') ^ 2 ≤ (y - y') ^ 2 := by
  unfold proxLog
  set s := Real.sqrt (y ^ 2 + 4 * η)
  set s' := Real.sqrt (y' ^ 2 + 4 * η)
  have hs := Real.sq_sqrt (show 0 ≤ y ^ 2 + 4 * η by positivity)
  have hs' := Real.sq_sqrt (show 0 ≤ y' ^ 2 + 4 * η by positivity)
  have ha := proxLog_sqrt_ge hη y
  have ha' := proxLog_sqrt_ge hη y'
  have hT : 0 < s + s' := by
    have := abs_nonneg y
    have := abs_nonneg y'
    linarith
  have hkey : ((y - y') + (s - s')) * (s + s') = (y - y') * ((s + s') + (y + y')) := by
    nlinarith
  have hb1 : -(s + s') ≤ y + y' := by
    have := neg_abs_le y
    have := neg_abs_le y'
    linarith
  have hb2 : y + y' ≤ s + s' := by
    have := le_abs_self y
    have := le_abs_self y'
    linarith
  have hfac : ((s + s') + (y + y')) ^ 2 ≤ (2 * (s + s')) ^ 2 := by nlinarith
  have hsq : ((y - y') + (s - s')) ^ 2 * (s + s') ^ 2 ≤ (2 * (y - y')) ^ 2 * (s + s') ^ 2 := by
    have : ((y - y') + (s - s')) ^ 2 * (s + s') ^ 2 = (y - y') ^ 2 * ((s + s') + (y + y')) ^ 2 := by
      rw [← mul_pow, hkey, mul_pow]
    rw [this]
    have h0 := sq_nonneg (y - y')
    calc (y - y') ^ 2 * ((s + s') + (y + y')) ^ 2 ≤ (y - y') ^ 2 * (2 * (s + s')) ^ 2 :=
          mul_le_mul_of_nonneg_left hfac h0
      _ = (2 * (y - y')) ^ 2 * (s + s') ^ 2 := by ring
  have hT2 : 0 < (s + s') ^ 2 := by positivity
  have h4 : ((y - y') + (s - s')) ^ 2 ≤ (2 * (y - y')) ^ 2 := le_of_mul_le_mul_right hsq hT2
  have he : (y + s) / 2 - (y' + s') / 2 = ((y - y') + (s - s')) / 2 := by ring
  rw [he, div_pow]
  nlinarith

lemma neg_log_proxLog_le {η y z : ℝ} (hη : 0 < η) (hz : 0 < z) :
    -Real.log (proxLog η y) ≤ -Real.log z - (y - proxLog η y) * (z - proxLog η y) / η := by
  have hp := proxLog_pos hη y
  have hl := Real.log_le_sub_one_of_pos (div_pos hz hp)
  rw [Real.log_div hz.ne' hp.ne'] at hl
  have hr := proxLog_root hη y
  have he : (z / proxLog η y - 1) = -(y - proxLog η y) * (z - proxLog η y) / η := by
    field_simp
    nlinarith
  rw [he] at hl
  have : -(y - proxLog η y) * (z - proxLog η y) / η = -((y - proxLog η y) * (z - proxLog η y) / η) := by
    ring
  linarith

end Prox

section Pairs

def pin (z w : Location d × Scale d) : ℝ := pinner z.1 z.2 w.1 w.2

def sqd (z w : Location d × Scale d) : ℝ := sqDist z.1 w.1 z.2 w.2

lemma sqd_eq_pin (z w : Location d × Scale d) : sqd z w = pin (z - w) (z - w) := by
  unfold sqd pin
  rw [sqDist_eq_pinner]
  rfl

lemma pin_self_nonneg (z : Location d × Scale d) : 0 ≤ pin z z := pinner_self_nonneg _ _

lemma pin_sub_left (z z' w : Location d × Scale d) : pin (z - z') w = pin z w - pin z' w :=
  pinner_sub_left _ _ _ _ _ _

lemma pin_sub_right (z w w' : Location d × Scale d) : pin z (w - w') = pin z w - pin z w' :=
  pinner_sub_right _ _ _ _ _ _

lemma pin_comm (z w : Location d × Scale d) : pin z w = pin w z := pinner_comm _ _ _ _

lemma pin_smul_left (c : ℝ) (z w : Location d × Scale d) : pin (c • z) w = c * pin z w :=
  pinner_smul_left _ _ _ _ _

lemma pin_young (a b : Location d × Scale d) {η : ℝ} (hη : 0 < η) :
    pin a b ≤ η / 2 * pin a a + 1 / (2 * η) * pin b b := pinner_young _ _ _ _ hη

noncomputable def proxPair (η : ℝ) (z : Location d × Scale d) : Location d × Scale d :=
  (z.1, proxScale η z.2)

noncomputable def gradPair (g : Point d) (ξ : Fin d → ℝ) : Location d × Scale d :=
  (gradLoc g, gradScale g ξ)

lemma proxStep_eq (η : ℝ) (z : Location d × Scale d) (g : Point d) (ξ : Fin d → ℝ) :
    proxStep η z g ξ = proxPair η (z - η • gradPair g ξ) := rfl

lemma proxPair_sq_lip {η : ℝ} (hη : 0 < η) (z w : Location d × Scale d) :
    sqd (proxPair η z) (proxPair η w) ≤ sqd z w := by
  unfold sqd sqDist proxPair proxScale
  simp only
  refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
  split_ifs with hij
  · subst hij
    exact proxLog_sq_lip hη _ _
  · exact le_rfl

noncomputable def optPair (Cs : Scale d) : Location d × Scale d := (0, optScale Cs)

lemma proxPair_fixed {η : ℝ} (hη : 0 < η) {ms : Location d} {Cs : Scale d} (hCs : IsCholesky Cs) :
    proxPair η ((ms, Cs) - η • optPair Cs) = (ms, Cs) := by
  refine Prod.ext ?_ ?_
  · change ms - η • (0 : Location d) = ms
    rw [smul_zero, sub_zero]
  · funext i j
    change proxScale η (Cs - η • optScale Cs) i j = Cs i j
    unfold proxScale optScale
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [show η * (1 / Cs i i) = η / Cs i i by ring]
      exact proxLog_fixed hη (hCs.2 i)
    · simp [hij]

lemma isLower_proxScale {η : ℝ} {Y : Scale d} (hY : IsLower Y) : IsLower (proxScale η Y) := by
  intro i j h
  unfold proxScale
  simp [ne_of_lt h, hY i j h]

lemma isLower_gradScale (g : Point d) (ξ : Fin d → ℝ) : IsLower (gradScale g ξ) := by
  intro i j h
  unfold gradScale
  simp [not_le.mpr h]

lemma proxStep_cholesky {η : ℝ} (hη : 0 < η) {z : Location d × Scale d} (hz : IsCholesky z.2)
    (g : Point d) (ξ : Fin d → ℝ) : IsCholesky (proxStep η z g ξ).2 := by
  refine ⟨isLower_proxScale (isLower_sub hz.1 (isLower_smul (isLower_gradScale g ξ) η)), fun i => ?_⟩
  unfold proxStep proxScale
  simp only [↓reduceIte]
  exact proxLog_pos hη _

lemma prox_log_ineq {η : ℝ} (hη : 0 < η) (y : Location d × Scale d)
    {zC : Scale d} (hz : ∀ i, 0 < zC i i) (zm : Location d) :
    -∑ i, Real.log ((proxPair η y).2 i i) ≤
      -∑ i, Real.log (zC i i) - 1 / η * pin (y - proxPair η y) ((zm, zC) - proxPair η y) := by
  have hp : ∀ i, (proxPair η y).2 i i = proxLog η (y.2 i i) := fun i => by
    simp [proxPair, proxScale]
  have hkey : pin (y - proxPair η y) ((zm, zC) - proxPair η y) =
      ∑ i, (y.2 i i - proxLog η (y.2 i i)) * (zC i i - proxLog η (y.2 i i)) := by
    unfold pin pinner
    have h1 : ∀ i, (y - proxPair η y).1 i = 0 := fun i => by simp [proxPair]
    have h2 : ∀ i j, (y - proxPair η y).2 i j =
        if i = j then y.2 i i - proxLog η (y.2 i i) else 0 := by
      intro i j
      by_cases hij : i = j
      · subst hij
        simp [proxPair, proxScale]
      · simp [proxPair, proxScale, hij]
    simp only [h1, h2, zero_mul, Finset.sum_const_zero, zero_add, ite_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [proxPair, proxScale]
  rw [hkey]
  simp only [hp]
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    neg_log_proxLog_le (y := y.2 i i) hη (hz i)
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_neg_distrib,
    ← Finset.sum_div] at hs
  have he : 1 / η * ∑ i, (y.2 i i - proxLog η (y.2 i i)) * (zC i i - proxLog η (y.2 i i)) =
      (∑ i, (y.2 i i - proxLog η (y.2 i i)) * (zC i i - proxLog η (y.2 i i))) / η := by ring
  linarith

end Pairs

section Step

variable {L μ : ℝ} {V : Point d → ℝ}

noncomputable def objectivePair (V : Point d → ℝ) (z : Location d × Scale d) : ℝ :=
  objective V z.1 z.2

noncomputable def meanPair (V : Point d → ℝ) (z : Location d × Scale d) : Location d × Scale d :=
  (meanLoc V z.1 z.2, meanScale V z.1 z.2)

noncomputable def sampleGrad (V : Point d → ℝ) (z : Location d × Scale d) (ξ : Fin d → ℝ) :
    Location d × Scale d :=
  gradPair (gradient V (sample z.1 z.2 ξ)) ξ


lemma pin_add_self (x y : Location d × Scale d) :
    pin (x + y) (x + y) = pin x x + 2 * pin x y + pin y y := by
  unfold pin pinner
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.add_apply]
  have h1 : ∀ a b : ℝ, (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := fun a b => by ring
  simp_rw [h1]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

lemma pin_three (a b c : Location d × Scale d) :
    2 * pin (a - b) (b - c) = sqd a c - sqd b c - sqd a b := by
  have h := pin_add_self (a - b) (b - c)
  have he : a - b + (b - c) = a - c := by abel
  rw [he] at h
  rw [sqd_eq_pin, sqd_eq_pin, sqd_eq_pin]
  linarith

lemma sqd_comm (z w : Location d × Scale d) : sqd z w = sqd w z := sqDist_comm _ _ _ _

lemma sqd_nonneg (z w : Location d × Scale d) : 0 ≤ sqd z w := sqDist_nonneg _ _ _ _

lemma step_deterministic (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsOptimal V ms Cs) {z : Location d × Scale d} (hz : IsCholesky z.2)
    {η : ℝ} (hη : 0 < η) (hηL : η * L ≤ 1) (ξ : Fin d → ℝ) :
    objectivePair V (proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ) - objective V ms Cs ≤
      1 / (2 * η) * ((1 - η * μ) * sqd z (ms, Cs) -
        sqd (proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ) (ms, Cs)) +
      pin (meanPair V z - sampleGrad V z ξ)
        (proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ - (ms, Cs)) := by
  set ghat := sampleGrad V z ξ with hghat
  set gbar := meanPair V z with hgbar
  set y := z - η • ghat with hy
  set p := proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ with hpdef
  set w : Location d × Scale d := (ms, Cs) with hw
  have hp : p = proxPair η y := rfl
  have hpC : IsCholesky p.2 := proxStep_cholesky hη hz _ ξ
  have hlow1 : IsLower (p.2 - z.2) := isLower_sub hpC.1 hz.1
  have hlow2 : IsLower (Cs - z.2) := isLower_sub hopt.1.1 hz.1
  have hEu : energy V p.1 p.2 ≤ energy V z.1 z.2 + pin gbar (p - z) + L / 2 * sqd p z :=
    energy_upper h z.1 p.1 hlow1
  have hEl : energy V z.1 z.2 + pin gbar (w - z) + μ / 2 * sqd w z ≤ energy V ms Cs :=
    energy_lower h z.1 ms hlow2
  have hlog := prox_log_ineq hη y hopt.1.2 ms
  rw [← hp] at hlog
  have hobj : objectivePair V p - objective V ms Cs =
      energy V p.1 p.2 - energy V ms Cs + (-∑ i, Real.log (p.2 i i) - -∑ i, Real.log (Cs i i)) := by
    unfold objectivePair
    rw [objective_eq, objective_eq]
    ring
  have e1 : pin gbar (p - z) - pin gbar (w - z) = pin gbar (p - w) := by
    rw [pin_sub_right, pin_sub_right, pin_sub_right]
    ring
  have hyp : y - p = (z - p) - η • ghat := by
    rw [hy]
    abel
  have e2 : pin (y - p) (w - p) = pin (z - p) (w - p) - η * pin ghat (w - p) := by
    rw [hyp, pin_sub_left, pin_smul_left]
  have e3 : pin (z - p) (w - p) = -pin (z - p) (p - w) := by
    rw [pin_sub_right, pin_sub_right]
    ring
  have e4 : pin ghat (w - p) = -pin ghat (p - w) := by
    rw [pin_sub_right, pin_sub_right]
    ring
  have e5 : pin (gbar - ghat) (p - w) = pin gbar (p - w) - pin ghat (p - w) := pin_sub_left _ _ _
  have e6 := pin_three z p w
  have e7 : sqd p z = sqd z p := sqd_comm _ _
  have e8 : sqd w z = sqd z w := sqd_comm _ _
  have hs := sqd_nonneg z p
  have hL : L ≤ 1 / η := by rw [le_div_iff₀ hη]; linarith
  have hLs : L / 2 * sqd z p ≤ 1 / (2 * η) * sqd z p := by
    have : L / 2 ≤ 1 / (2 * η) := by
      rw [show 1 / (2 * η) = (1 / η) / 2 by ring]
      linarith
    exact mul_le_mul_of_nonneg_right this hs
  have hinv : 1 / η * (pin (z - p) (w - p) - η * pin ghat (w - p)) =
      1 / η * pin (z - p) (w - p) - pin ghat (w - p) := by
    field_simp
  have hA : 1 / η * pin (z - p) (p - w) = 1 / (2 * η) * (sqd z w - sqd p w - sqd z p) := by
    rw [← e6]
    field_simp
  rw [e2, hinv, e3, e4] at hlog
  rw [hobj, e5]
  have hfin : 1 / (2 * η) * ((1 - η * μ) * sqd z w - sqd p w) =
      1 / (2 * η) * (sqd z w - sqd p w) - μ / 2 * sqd z w := by
    field_simp; ring1
  rw [hfin]
  have hsplit : 1 / (2 * η) * (sqd z w - sqd p w - sqd z p) =
      1 / (2 * η) * (sqd z w - sqd p w) - 1 / (2 * η) * sqd z p := by ring
  rw [e7] at hEu
  rw [e8] at hEl
  linarith [hA, hsplit]

lemma continuous_proxLog (η : ℝ) : Continuous (proxLog η) := by
  unfold proxLog
  fun_prop

lemma continuous_step (h : Potential L μ V) (η : ℝ) :
    Continuous (fun w : (Location d × Scale d) × (Fin d → ℝ) =>
      proxStep η w.1 (gradient V (sample w.1.1 w.1.2 w.2)) w.2) := by
  have hG : Continuous (fun w : (Location d × Scale d) × (Fin d → ℝ) =>
      gradient V (sample w.1.1 w.1.2 w.2)) := h.continuous_grad.comp continuous_sample
  have hGi : ∀ i, Continuous (fun w : (Location d × Scale d) × (Fin d → ℝ) =>
      gradient V (sample w.1.1 w.1.2 w.2) i) := fun i => (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).comp hG
  unfold proxStep proxScale gradLoc gradScale
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun i => ?_
    dsimp only
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact ((continuous_apply i).comp (continuous_fst.comp continuous_fst)).sub
      (continuous_const.mul (hGi i))
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    dsimp only
    have hC : Continuous (fun w : (Location d × Scale d) × (Fin d → ℝ) => w.1.2 i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
    have hCii : Continuous (fun w : (Location d × Scale d) × (Fin d → ℝ) => w.1.2 i i) :=
      (continuous_apply i).comp ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
    have hxi : ∀ k, Continuous (fun w : (Location d × Scale d) × (Fin d → ℝ) => w.2 k) :=
      fun k => (continuous_apply k).comp continuous_snd
    have hgs : ∀ k l, Continuous (fun w : (Location d × Scale d) × (Fin d → ℝ) =>
        if l ≤ k then gradient V (sample w.1.1 w.1.2 w.2) k * w.2 l else 0) := by
      intro k l
      by_cases hlk : l ≤ k
      · simp only [hlk, ↓reduceIte]
        exact (hGi k).mul (hxi l)
      · simp only [hlk, ↓reduceIte]
        exact continuous_const
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact (continuous_proxLog η).comp (hCii.sub (continuous_const.mul (hgs i i)))
    · simp only [hij, ↓reduceIte, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact hC.sub (continuous_const.mul (hgs i j))

lemma measurable_step (h : Potential L μ V) (η : ℝ) :
    Measurable (fun w : (Location d × Scale d) × (Fin d → ℝ) =>
      proxStep η w.1 (gradient V (sample w.1.1 w.1.2 w.2)) w.2) :=
  (continuous_step h η).measurable

lemma measurable_step_fixed (h : Potential L μ V) (η : ℝ) (z : Location d × Scale d) :
    Measurable (fun ξ : Fin d → ℝ => proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ) :=
  (measurable_step h η).comp (measurable_const.prodMk measurable_id)

lemma measurable_objectivePair (h : Potential L μ V) :
    Measurable (objectivePair V (d := d)) := by
  have hE : Measurable (fun z : Location d × Scale d => energy V z.1 z.2) := by
    have hf : StronglyMeasurable (fun w : (Location d × Scale d) × (Fin d → ℝ) =>
        V (sample w.1.1 w.1.2 w.2)) :=
      (h.continuous_fn.comp continuous_sample).measurable.stronglyMeasurable
    exact (hf.integral_prod_right' (ν := noiseLaw d)).measurable
  unfold objectivePair objective
  refine hE.sub (Finset.measurable_sum _ fun i _ => ?_)
  exact Real.measurable_log.comp ((measurable_pi_apply i).comp ((measurable_pi_apply i).comp
    measurable_snd))

lemma measurable_sqd (w : Location d × Scale d) : Measurable (fun z : Location d × Scale d => sqd z w) := by
  unfold sqd sqDist
  refine (Finset.measurable_sum _ fun i _ => ?_).add
    (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  · exact (((measurable_pi_apply i).comp measurable_fst).sub_const _).pow_const 2
  · exact ((((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd))).sub_const
      _).pow_const 2

lemma measurable_sampleGrad (h : Potential L μ V) (z : Location d × Scale d) :
    Measurable (sampleGrad V z) := by
  have hg := measurable_grad_sample h z.1 z.2
  unfold sampleGrad gradPair gradLoc gradScale
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_iff.mpr fun i =>
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp hg
  · refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    by_cases hji : j ≤ i
    · simp only [hji, ↓reduceIte]
      exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp
        hg).mul (measurable_pi_apply j)
    · simp only [hji, ↓reduceIte]
      exact measurable_const

lemma integral_pin_sampleGrad (h : Potential L μ V) (z w : Location d × Scale d) :
    Integrable (fun ξ => pin (sampleGrad V z ξ) w) (noiseLaw d) ∧
      ∫ ξ, pin (sampleGrad V z ξ) w ∂noiseLaw d = pin (meanPair V z) w :=
  integral_pinner_grad h z.1 z.2 w.1 w.2

lemma integrable_pin_sampleGrad_self (h : Potential L μ V) (z : Location d × Scale d) :
    Integrable (fun ξ => pin (sampleGrad V z ξ) (sampleGrad V z ξ)) (noiseLaw d) := by
  have hm := measurable_sampleGrad h z
  have hmeas : Measurable (fun ξ => pin (sampleGrad V z ξ) (sampleGrad V z ξ)) := by
    unfold pin pinner
    refine (Finset.measurable_sum _ fun i _ => ?_).add
      (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
    · exact ((measurable_pi_apply i).comp (measurable_fst.comp hm)).mul
        ((measurable_pi_apply i).comp (measurable_fst.comp hm))
    · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_snd.comp hm))).mul
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_snd.comp hm)))
  refine integrable_poly hmeas.aestronglyMeasurable
    (2 * ‖gradient V 0‖ ^ 2 + 4 * L ^ 2 * sqDist z.1 0 z.2 0) fun ξ => ?_
  have h1 := pinner_grad_self_le (gradient V (sample z.1 z.2 ξ)) ξ
  have h2 := grad_sample_sq_le h z.1 z.2 ξ
  have h0 := pin_self_nonneg (sampleGrad V z ξ)
  have hS := sqNorm_nonneg ξ
  rw [abs_of_nonneg h0]
  have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 1 + sqNorm ξ)
  have he : pin (sampleGrad V z ξ) (sampleGrad V z ξ) =
      pinner (gradLoc (gradient V (sample z.1 z.2 ξ))) (gradScale (gradient V (sample z.1 z.2 ξ)) ξ)
        (gradLoc (gradient V (sample z.1 z.2 ξ))) (gradScale (gradient V (sample z.1 z.2 ξ)) ξ) := rfl
  rw [he]
  nlinarith

lemma pin_sub_self_expand (a c : Location d × Scale d) :
    pin (a - c) (a - c) = pin a a - 2 * pin a c + pin c c := by
  unfold pin pinner
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, Pi.sub_apply]
  have h1 : ∀ x y : ℝ, (x - y) * (x - y) = x * x - 2 * (x * y) + y * y := fun x y => by ring
  simp_rw [h1]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma integrable_pin_sampleGrad_sub (h : Potential L μ V) (z c : Location d × Scale d) :
    Integrable (fun ξ => pin (sampleGrad V z ξ - c) (sampleGrad V z ξ - c)) (noiseLaw d) := by
  simp_rw [pin_sub_self_expand]
  exact ((integrable_pin_sampleGrad_self h z).subL
    ((integral_pin_sampleGrad h z c).1.const_mul 2)).addL (integrable_const _)

lemma bias_variance (h : Potential L μ V) (z c : Location d × Scale d) :
    ∫ ξ, pin (sampleGrad V z ξ - meanPair V z) (sampleGrad V z ξ - meanPair V z) ∂noiseLaw d ≤
      ∫ ξ, pin (sampleGrad V z ξ - c) (sampleGrad V z ξ - c) ∂noiseLaw d := by
  have hexp : ∀ ξ, pin (sampleGrad V z ξ - c) (sampleGrad V z ξ - c) =
      pin (sampleGrad V z ξ - meanPair V z) (sampleGrad V z ξ - meanPair V z) +
        2 * (pin (sampleGrad V z ξ) (meanPair V z - c) - pin (meanPair V z) (meanPair V z - c)) +
        pin (meanPair V z - c) (meanPair V z - c) := by
    intro ξ
    have h1 := pin_add_self (sampleGrad V z ξ - meanPair V z) (meanPair V z - c)
    have he : sampleGrad V z ξ - meanPair V z + (meanPair V z - c) = sampleGrad V z ξ - c := by abel
    rw [he] at h1
    have h2 : pin (sampleGrad V z ξ - meanPair V z) (meanPair V z - c) =
        pin (sampleGrad V z ξ) (meanPair V z - c) - pin (meanPair V z) (meanPair V z - c) :=
      pin_sub_left _ _ _
    linarith
  simp_rw [hexp]
  have h1 := integrable_pin_sampleGrad_sub h z (meanPair V z)
  have h2 := (integral_pin_sampleGrad h z (meanPair V z - c))
  have h3 : Integrable (fun ξ => 2 * (pin (sampleGrad V z ξ) (meanPair V z - c) -
      pin (meanPair V z) (meanPair V z - c))) (noiseLaw d) :=
    (h2.1.subL (integrable_const _)).const_mul 2
  rw [integral_add (h1.addL h3) (integrable_const _), integral_add h1 h3, integral_const_mul,
    integral_sub h2.1 (integrable_const _), h2.2]
  simp only [integral_const, probReal_univ, one_smul, sub_self, mul_zero, add_zero]
  linarith [pin_self_nonneg (meanPair V z - c)]

lemma pin_add_le (x y : Location d × Scale d) :
    pin (x + y) (x + y) ≤ 2 * pin x x + 2 * pin y y := by
  have h1 := pin_add_self x y
  have h2 := pin_sub_self_expand x y
  have h3 := pin_self_nonneg (x - y)
  linarith

lemma pin_swap_self (a b : Location d × Scale d) : pin (a - b) (a - b) = pin (b - a) (b - a) := by
  rw [pin_sub_self_expand, pin_sub_self_expand, pin_comm b a]
  ring

lemma pin_smul_self (c : ℝ) (x : Location d × Scale d) : pin (c • x) (c • x) = c ^ 2 * pin x x := by
  rw [pin_smul_left, pin_comm, pin_smul_left, pin_comm]
  ring

lemma step_expectation (h : Potential L μ V) {ms : Location d} {Cs : Scale d}
    (hopt : IsOptimal V ms Cs) {z : Location d × Scale d} (hz : IsCholesky z.2)
    {η : ℝ} (hη : 0 < η) (hηL : η * L ≤ 1) :
    Integrable (fun ξ => objectivePair V (proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ) -
      objective V ms Cs) (noiseLaw d) ∧
    Integrable (fun ξ => sqd (proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ) (ms, Cs))
      (noiseLaw d) ∧
    ∫ ξ, (objectivePair V (proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ) -
      objective V ms Cs) ∂noiseLaw d ≤
      1 / (2 * η) * ((1 - η * μ) * sqd z (ms, Cs) -
        ∫ ξ, sqd (proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ) (ms, Cs) ∂noiseLaw d) +
      η * (4 * (L * (2 + tau d (L / μ))) * bregmanMean V ms Cs z.1 z.2 +
        2 * ((2 + tau d (L / μ)) * L * d)) := by
  set w : Location d × Scale d := (ms, Cs) with hw
  set gbar := meanPair V z
  set G := optPair Cs
  set q := proxPair η (z - η • gbar)
  set p := fun ξ => proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ
  set Q := fun ξ => pin (sampleGrad V z ξ - gbar) (sampleGrad V z ξ - gbar)
  set N := fun ξ => pin (gbar - sampleGrad V z ξ) (q - w)
  set r := sqd z w
  have hQi : Integrable Q (noiseLaw d) := integrable_pin_sampleGrad_sub h z gbar
  have hNi : Integrable N (noiseLaw d) := by
    have := (integral_pin_sampleGrad h z (q - w)).1
    have he : N = fun ξ => pin gbar (q - w) - pin (sampleGrad V z ξ) (q - w) := by
      funext ξ
      exact pin_sub_left _ _ _
    rw [he]
    exact (integrable_const _).subL this
  have hN0 : ∫ ξ, N ξ ∂noiseLaw d = 0 := by
    have hh := integral_pin_sampleGrad h z (q - w)
    have he : N = fun ξ => pin gbar (q - w) - pin (sampleGrad V z ξ) (q - w) := by
      funext ξ
      exact pin_sub_left _ _ _
    rw [he, integral_sub (integrable_const _) hh.1, hh.2]
    simp only [integral_const, probReal_univ, one_smul]
    exact sub_self _
  have hpq : ∀ ξ, pin (gbar - sampleGrad V z ξ) (p ξ - w) ≤ η * Q ξ + N ξ := by
    intro ξ
    have hsplit : pin (gbar - sampleGrad V z ξ) (p ξ - w) =
        pin (gbar - sampleGrad V z ξ) (p ξ - q) + N ξ := by
      simp only [N]
      rw [pin_sub_right, pin_sub_right, pin_sub_right]
      ring
    have hy := pin_young (gbar - sampleGrad V z ξ) (p ξ - q) hη
    have hlip : pin (p ξ - q) (p ξ - q) ≤ η ^ 2 * Q ξ := by
      have h1 := proxPair_sq_lip hη (z - η • sampleGrad V z ξ) (z - η • gbar)
      rw [sqd_eq_pin, sqd_eq_pin] at h1
      have he : z - η • sampleGrad V z ξ - (z - η • gbar) = η • (gbar - sampleGrad V z ξ) := by
        rw [smul_sub]
        abel
      rw [he, pin_smul_self] at h1
      have hQ' : pin (gbar - sampleGrad V z ξ) (gbar - sampleGrad V z ξ) = Q ξ := pin_swap_self _ _
      rw [hQ'] at h1
      exact h1
    have hQ : pin (gbar - sampleGrad V z ξ) (gbar - sampleGrad V z ξ) = Q ξ := pin_swap_self _ _
    rw [hsplit]
    rw [hQ] at hy
    have : 1 / (2 * η) * pin (p ξ - q) (p ξ - q) ≤ 1 / (2 * η) * (η ^ 2 * Q ξ) :=
      mul_le_mul_of_nonneg_left hlip (by positivity)
    have he2 : 1 / (2 * η) * (η ^ 2 * Q ξ) = η / 2 * Q ξ := by field_simp
    linarith
  have hdet : ∀ ξ, objectivePair V (p ξ) - objective V ms Cs ≤
      1 / (2 * η) * ((1 - η * μ) * r - sqd (p ξ) w) + η * Q ξ + N ξ := by
    intro ξ
    have := step_deterministic h hopt hz hη hηL ξ
    have := hpq ξ
    linarith
  have hfix := proxPair_fixed (ms := ms) hη hopt.1
  have hrbound : ∀ ξ, sqd (p ξ) w ≤ 2 * r + 2 * (η ^ 2 *
      pin (sampleGrad V z ξ - G) (sampleGrad V z ξ - G)) := by
    intro ξ
    have h1 := proxPair_sq_lip hη (z - η • sampleGrad V z ξ) (w - η • G)
    have hfix' : proxPair η (w - η • G) = w := hfix
    rw [hfix'] at h1
    rw [sqd_eq_pin (z - η • sampleGrad V z ξ) (w - η • G)] at h1
    have he : z - η • sampleGrad V z ξ - (w - η • G) = (z - w) + -(η • (sampleGrad V z ξ - G)) := by
      rw [smul_sub]
      abel
    rw [he] at h1
    have h2 := pin_add_le (z - w) (-(η • (sampleGrad V z ξ - G)))
    have h3 : pin (-(η • (sampleGrad V z ξ - G))) (-(η • (sampleGrad V z ξ - G))) =
        η ^ 2 * pin (sampleGrad V z ξ - G) (sampleGrad V z ξ - G) := by
      rw [← neg_smul, pin_smul_self]
      ring
    have h4 : pin (z - w) (z - w) = r := (sqd_eq_pin z w).symm
    have : sqd (p ξ) w = sqd (proxPair η (z - η • sampleGrad V z ξ)) w := rfl
    rw [this]
    linarith
  have hGi := integrable_pin_sampleGrad_sub h z G
  have hri : Integrable (fun ξ => sqd (p ξ) w) (noiseLaw d) := by
    refine Integrable.mono' ((integrable_const (2 * r)).addL ((hGi.const_mul (η ^ 2)).const_mul 2))
      ((measurable_sqd w).comp (measurable_step_fixed h η z)).aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sqd_nonneg _ _)]
    have := hrbound ξ
    linarith
  have hpC : ∀ ξ, IsCholesky (p ξ).2 := fun ξ => proxStep_cholesky hη hz _ ξ
  have hgap0 : ∀ ξ, 0 ≤ objectivePair V (p ξ) - objective V ms Cs := fun ξ =>
    sub_nonneg.mpr (hopt.2 _ _ (hpC ξ))
  have hoi : Integrable (fun ξ => objectivePair V (p ξ) - objective V ms Cs) (noiseLaw d) := by
    have hB : Integrable (fun ξ => 1 / (2 * η) * ((1 - η * μ) * r) + η * Q ξ + N ξ) (noiseLaw d) :=
      ((integrable_const _).addL (hQi.const_mul η)).addL hNi
    refine Integrable.mono' hB (((measurable_objectivePair h).comp
      (measurable_step_fixed h η z)).sub_const _).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hgap0 ξ)]
    have h1 := hdet ξ
    have h2 := sqd_nonneg (p ξ) w
    have h3 : 0 ≤ 1 / (2 * η) * sqd (p ξ) w := by positivity
    have : 1 / (2 * η) * ((1 - η * μ) * r - sqd (p ξ) w) =
        1 / (2 * η) * ((1 - η * μ) * r) - 1 / (2 * η) * sqd (p ξ) w := by ring
    linarith
  refine ⟨hoi, hri, ?_⟩
  have hR : Integrable (fun ξ => 1 / (2 * η) * ((1 - η * μ) * r - sqd (p ξ) w) + η * Q ξ + N ξ)
      (noiseLaw d) :=
    ((((integrable_const _).subL hri).const_mul _).addL (hQi.const_mul η)).addL hNi
  have hm := integral_mono hoi hR hdet
  rw [integral_add (((integrable_const _).subL hri).const_mul _ |>.addL (hQi.const_mul η)) hNi,
    integral_add (((integrable_const _).subL hri).const_mul _) (hQi.const_mul η), hN0,
    integral_const_mul, integral_sub (integrable_const _) hri, integral_const_mul] at hm
  simp only [integral_const, probReal_univ, one_smul, add_zero] at hm
  have hbv := bias_variance h z G
  set gs := fun ξ => sampleGrad V w ξ
  have hpt2 : ∀ ξ, pin (sampleGrad V z ξ - G) (sampleGrad V z ξ - G) ≤
      2 * pin (sampleGrad V z ξ - gs ξ) (sampleGrad V z ξ - gs ξ) + 2 * pin (gs ξ - G) (gs ξ - G) := by
    intro ξ
    have := pin_add_le (sampleGrad V z ξ - gs ξ) (gs ξ - G)
    have he : sampleGrad V z ξ - gs ξ + (gs ξ - G) = sampleGrad V z ξ - G := by abel
    rwa [he] at this
  have hlowz : IsLower (z.2 - Cs) := isLower_sub hz.1 hopt.1.1
  have hES := expected_smoothness h (ms := ms) (Cs := Cs) z.1 hlowz
  have hVO := variance_at_optimum h hopt
  have hgsG : Integrable (fun ξ => pin (gs ξ - G) (gs ξ - G)) (noiseLaw d) :=
    integrable_pin_sampleGrad_sub h w G
  have hgsGval : ∫ ξ, pin (gs ξ - G) (gs ξ - G) ∂noiseLaw d ≤
      ∫ ξ, pin (gs ξ) (gs ξ) ∂noiseLaw d := by
    have hexp : ∀ ξ, pin (gs ξ - G) (gs ξ - G) = pin (gs ξ) (gs ξ) - 2 * pin (gs ξ) G + pin G G :=
      fun ξ => pin_sub_self_expand _ _
    simp_rw [hexp]
    have hi1 := integrable_pin_sampleGrad_self h w
    have hi2 := integral_pin_sampleGrad h w G
    rw [integral_add (hi1.subL (hi2.1.const_mul 2)) (integrable_const _),
      integral_sub hi1 (hi2.1.const_mul 2), integral_const_mul, hi2.2]
    have hopt' : pin (meanPair V w) G = pin G G := by
      have hlowG : IsLower (optScale Cs) := by
        intro i j hij
        unfold optScale
        simp [ne_of_lt hij]
      exact opt_pinner' h hopt 0 hlowG
    rw [hopt']
    simp only [integral_const, probReal_univ, one_smul]
    linarith [pin_self_nonneg G]
  have hES' : ∫ ξ, pin (sampleGrad V z ξ - gs ξ) (sampleGrad V z ξ - gs ξ) ∂noiseLaw d ≤
      2 * (L * (2 + tau d (L / μ))) * bregmanMean V ms Cs z.1 z.2 := hES.2
  have hVO' : ∫ ξ, pin (gs ξ) (gs ξ) ∂noiseLaw d ≤ (2 + tau d (L / μ)) * L * d := hVO.2
  have hint2 := integral_mono hGi ((hES.1.const_mul 2).addL (hgsG.const_mul 2)) hpt2
  rw [integral_add (hES.1.const_mul 2) (hgsG.const_mul 2), integral_const_mul,
    integral_const_mul] at hint2
  have hQbound : ∫ ξ, Q ξ ∂noiseLaw d ≤ 4 * (L * (2 + tau d (L / μ))) * bregmanMean V ms Cs z.1 z.2 +
      2 * ((2 + tau d (L / μ)) * L * d) := by
    have : ∫ ξ, Q ξ ∂noiseLaw d ≤ ∫ ξ, pin (sampleGrad V z ξ - G) (sampleGrad V z ξ - G) ∂noiseLaw d :=
      hbv
    have h5 : ∫ ξ, pin (sampleGrad V z ξ - gs ξ) (sampleGrad V z ξ - gs ξ) ∂noiseLaw d =
        ∫ ξ, pin (sampleGrad V z ξ - gs ξ) (sampleGrad V z ξ - gs ξ) ∂noiseLaw d := rfl
    linarith
  have hfinal : η * ∫ ξ, Q ξ ∂noiseLaw d ≤ η * (4 * (L * (2 + tau d (L / μ))) *
      bregmanMean V ms Cs z.1 z.2 + 2 * ((2 + tau d (L / μ)) * L * d)) :=
    mul_le_mul_of_nonneg_left hQbound hη.le
  change ∫ ξ, (objectivePair V (p ξ) - objective V ms Cs) ∂noiseLaw d ≤
    1 / (2 * η) * ((1 - η * μ) * r - ∫ ξ, sqd (p ξ) w ∂noiseLaw d) +
      η * (4 * (L * (2 + tau d (L / μ))) * bregmanMean V ms Cs z.1 z.2 +
        2 * ((2 + tau d (L / μ)) * L * d))
  have hQint : ∫ ξ, η * Q ξ ∂noiseLaw d = η * ∫ ξ, Q ξ ∂noiseLaw d := integral_const_mul _ _
  rw [hQint] at hm
  linarith only [hm, hfinal]

end Step

end OracleTemplate.GaussianVariational
