import LongTails.Proofs.GaussianVariationalStep
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import LongTails.Proofs.SgdConvex
import LongTails.Proofs.Execution

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GaussianVariational

open LongTails.Setups.GaussianVariationalInference

variable {d : ℕ} {L μ : ℝ} {V : Point d → ℝ}

noncomputable def noiseConst (L μ : ℝ) (d : ℕ) : ℝ := (2 + tau d (L / μ)) * L * d

noncomputable def stepAt (V : Point d → ℝ) (μ a : ℝ) (k : ℕ) (z : Location d × Scale d)
    (ξ : Fin d → ℝ) : Location d × Scale d :=
  proxStep (stepSize μ a k) z (gradient V (sample z.1 z.2 ξ)) ξ

noncomputable def gap (V : Point d → ℝ) (ms : Location d) (Cs : Scale d)
    (z : Location d × Scale d) : ℝ :=
  objectivePair V z - objective V ms Cs

noncomputable def pot (V : Point d → ℝ) (ms : Location d) (Cs : Scale d) (μ a : ℝ) :
    (k0 n : ℕ) → (Location d × Scale d) → (Fin n → Fin d → ℝ) → ℝ
  | _, 0, _, _ => 0
  | k0, n + 1, z, ξ =>
      averageWeight a k0 / 2 * gap V ms Cs (stepAt V μ a k0 z (ξ 0)) +
        pot V ms Cs μ a (k0 + 1) n (stepAt V μ a k0 z (ξ 0)) (fun i => ξ i.succ)

noncomputable def wsum (V : Point d → ℝ) (μ a : ℝ) :
    (k0 n : ℕ) → (Location d × Scale d) → (Fin n → Fin d → ℝ) → Location d × Scale d
  | _, 0, _, _ => 0
  | k0, n + 1, z, ξ =>
      averageWeight a k0 • stepAt V μ a k0 z (ξ 0) +
        wsum V μ a (k0 + 1) n (stepAt V μ a k0 z (ξ 0)) (fun i => ξ i.succ)

noncomputable def wmass (a : ℝ) : (k0 n : ℕ) → ℝ
  | _, 0 => 0
  | k0, n + 1 => averageWeight a k0 + wmass a (k0 + 1) n

lemma stepSize_pos {μ a : ℝ} (hμ : 0 < μ) (ha : 2 ≤ a) (k : ℕ) : 0 < stepSize μ a k := by
  unfold stepSize
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have : 0 < μ * (k + a) := by positivity
  positivity

lemma averageWeight_pos {a : ℝ} (ha : 2 ≤ a) (k : ℕ) : 0 < averageWeight a k := by
  unfold averageWeight
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma stepAt_cholesky (hμ : 0 < μ) {a : ℝ} (ha : 2 ≤ a) (k : ℕ) {z : Location d × Scale d}
    (hz : IsCholesky z.2) (ξ : Fin d → ℝ) : IsCholesky (stepAt V μ a k z ξ).2 :=
  proxStep_cholesky (stepSize_pos hμ ha k) hz _ ξ

lemma wmass_pos {a : ℝ} (ha : 2 ≤ a) (k0 : ℕ) {n : ℕ} (hn : 0 < n) : 0 < wmass a k0 n := by
  induction n generalizing k0 with
  | zero => omega
  | succ n ih =>
    unfold wmass
    have h1 := averageWeight_pos ha k0
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      simp [wmass, h1]
    · have := ih (k0 + 1) h
      linarith

lemma wmass_ge {a : ℝ} (ha : 2 ≤ a) (n : ℕ) : (n : ℝ) ^ 2 / 2 ≤ wmass a 0 n := by
  have key : ∀ k0 : ℕ, ((k0 : ℝ) + a - 1) * n + (n : ℝ) * (n - 1) / 2 ≤ wmass a k0 n := by
    induction n with
    | zero => intro k0; simp [wmass]
    | succ n ih =>
      intro k0
      unfold wmass
      have := ih (k0 + 1)
      unfold averageWeight
      push_cast at this ⊢
      nlinarith
  have := key 0
  push_cast at this
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

lemma measurable_stepAt (h : Potential L μ V) (a : ℝ) (k : ℕ) :
    Measurable (fun w : (Location d × Scale d) × (Fin d → ℝ) => stepAt V μ a k w.1 w.2) :=
  measurable_step h (stepSize μ a k)

lemma measurable_gap (h : Potential L μ V) (ms : Location d) (Cs : Scale d) :
    Measurable (gap V ms Cs) :=
  (measurable_objectivePair h).sub_const _

lemma measurable_pot (h : Potential L μ V) (ms : Location d) (Cs : Scale d) (a : ℝ) (n : ℕ) :
    ∀ k0, Measurable (fun w : (Location d × Scale d) × (Fin n → Fin d → ℝ) =>
      pot V ms Cs μ a k0 n w.1 w.2) := by
  induction n with
  | zero => intro k0; exact measurable_const
  | succ n ih =>
    intro k0
    have ht : Measurable (fun w : (Location d × Scale d) × (Fin (n + 1) → Fin d → ℝ) =>
        (stepAt V μ a k0 w.1 (w.2 0), fun i : Fin n => w.2 i.succ)) := by
      have hs : Measurable (fun w : (Location d × Scale d) × (Fin (n + 1) → Fin d → ℝ) =>
          stepAt V μ a k0 w.1 (w.2 0)) :=
        (measurable_stepAt h a k0).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp
          measurable_snd))
      exact hs.prodMk (by fun_prop)
    exact (((measurable_gap h ms Cs).comp ht.fst).const_mul _).add ((ih (k0 + 1)).comp ht)

lemma pot_nonneg {ms : Location d} {Cs : Scale d} (hopt : IsOptimal V ms Cs) (hμ : 0 < μ)
    {a : ℝ} (ha : 2 ≤ a) (n : ℕ) :
    ∀ k0 z ξ, IsCholesky (z : Location d × Scale d).2 → 0 ≤ pot V ms Cs μ a k0 n z ξ := by
  induction n with
  | zero => intro k0 z ξ _; simp [pot]
  | succ n ih =>
    intro k0 z ξ hz
    unfold pot
    have hc := stepAt_cholesky (V := V) hμ ha k0 hz (ξ 0)
    have h1 : 0 ≤ gap V ms Cs (stepAt V μ a k0 z (ξ 0)) := sub_nonneg.mpr (hopt.2 _ _ hc)
    have h2 := ih (k0 + 1) _ (fun i => ξ i.succ) hc
    have h3 := averageWeight_pos ha k0
    positivity

lemma measurable_bregmanMean (h : Potential L μ V) (ms : Location d) (Cs : Scale d) :
    Measurable (fun z : Location d × Scale d => bregmanMean V ms Cs z.1 z.2) := by
  have hc : Continuous (fun w : (Location d × Scale d) × (Fin d → ℝ) =>
      bregman V ms Cs w.1.1 w.1.2 w.2) := by
    unfold bregman
    have hs := continuous_sample (d := d)
    have hs2 : Continuous (fun w : (Location d × Scale d) × (Fin d → ℝ) => sample ms Cs w.2) :=
      (continuous_sample_fixed ms Cs).comp continuous_snd
    exact ((h.continuous_fn.comp hs).sub (h.continuous_fn.comp hs2)).sub
      (((h.continuous_grad.comp hs2)).inner (hs.sub hs2))
  exact (hc.measurable.stronglyMeasurable.integral_prod_right' (ν := noiseLaw d)).measurable

lemma pot_bound (h : Potential L μ V) {ms : Location d} {Cs : Scale d} (hopt : IsOptimal V ms Cs)
    (n : ℕ) : ∀ k0 (z : Location d × Scale d), IsCholesky z.2 →
      Integrable (pot V ms Cs μ (offset L μ d) k0 n z) (Measure.pi fun _ : Fin n => noiseLaw d) ∧
      ∫ ξ, pot V ms Cs μ (offset L μ d) k0 n z ξ ∂Measure.pi (fun _ : Fin n => noiseLaw d) ≤
        μ / 4 * (((k0 : ℝ) + offset L μ d - 1) * ((k0 : ℝ) + offset L μ d - 2)) * sqd z (ms, Cs) +
          8 * smoothConst L μ d / μ * bregmanMean V ms Cs z.1 z.2 +
          4 * n * noiseConst L μ d / μ := by
  set a := offset L μ d with ha_def
  set 𝓛 := smoothConst L μ d
  set σ2 := noiseConst L μ d
  have hadef : a = 16 * 𝓛 / μ + 2 := rfl
  have h𝓛def : 𝓛 = L * (2 + tau d (L / μ)) := rfl
  have hσdef : σ2 = (2 + tau d (L / μ)) * L * d := rfl
  clear_value a 𝓛 σ2
  have hμ := h.pos
  have hL := h.L_pos
  have hκ : 1 ≤ L / μ := (one_le_div hμ).mpr h.le
  have hτ := tau_nonneg d hκ
  have h𝓛 : 2 * L ≤ 𝓛 := by
    have e : L * (2 + tau d (L / μ)) = 2 * L + L * tau d (L / μ) := by ring
    rw [h𝓛def, e]
    linarith [mul_nonneg hL.le hτ]
  have h𝓛0 : 0 < 𝓛 := by linarith
  have ha : 2 ≤ a := by
    rw [hadef]
    have : 0 ≤ 16 * 𝓛 / μ := div_nonneg (by linarith) hμ.le
    linarith
  have hσ : 0 ≤ σ2 := by
    rw [hσdef]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity
  induction n with
  | zero =>
    intro k0 z hz
    refine ⟨by simp [pot], ?_⟩
    simp only [pot, integral_zero, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    have hk : (0 : ℝ) ≤ k0 := Nat.cast_nonneg k0
    have h1 : 0 ≤ ((k0 : ℝ) + a - 1) * ((k0 : ℝ) + a - 2) := by nlinarith
    have h2 := sqd_nonneg z (ms, Cs)
    have h3 := bregmanMean_lower h (ms := ms) (Cs := Cs) z.1 (isLower_sub hz.1 hopt.1.1)
    have h4 : 0 ≤ μ / 2 * sqDist z.1 ms z.2 Cs := by
      have := sqDist_nonneg z.1 ms z.2 Cs
      positivity
    have h5 : 0 ≤ 8 * 𝓛 / μ * bregmanMean V ms Cs z.1 z.2 := by
      have : 0 ≤ 8 * 𝓛 / μ := by positivity
      exact mul_nonneg this (by linarith)
    have h6 : 0 ≤ μ / 4 * (((k0 : ℝ) + a - 1) * ((k0 : ℝ) + a - 2)) * sqd z (ms, Cs) := by
      have : 0 ≤ μ / 4 := by positivity
      exact mul_nonneg (mul_nonneg this h1) h2
    linarith
  | succ n ih =>
    intro k0 z hz
    set η := stepSize μ a k0
    have hη : 0 < η := stepSize_pos hμ ha k0
    have hk : (0 : ℝ) ≤ k0 := Nat.cast_nonneg k0
    have hηa : η * (μ * ((k0 : ℝ) + a)) = 2 := by
      simp only [η, stepSize]
      field_simp
    have hηL : η * L ≤ 1 := by
      have h1 : 16 * 𝓛 / μ ≤ (k0 : ℝ) + a := by rw [hadef]; linarith
      have h2 : 16 * 𝓛 ≤ μ * ((k0 : ℝ) + a) := by
        rw [div_le_iff₀ hμ] at h1
        linarith
      nlinarith
    have hstep := step_expectation h hopt hz hη hηL
    set p := fun ξ : Fin d → ℝ => stepAt V μ a k0 z ξ
    have hpC : ∀ ξ, IsCholesky (p ξ).2 := fun ξ => stepAt_cholesky hμ ha k0 hz ξ
    let q := Measure.pi (fun _ : Fin n => noiseLaw d)
    let F := fun w : (Fin d → ℝ) × (Fin n → Fin d → ℝ) =>
      averageWeight a k0 / 2 * gap V ms Cs (p w.1) + pot V ms Cs μ a (k0 + 1) n (p w.1) w.2
    have hFm : Measurable F := by
      have hp : Measurable (fun w : (Fin d → ℝ) × (Fin n → Fin d → ℝ) => p w.1) :=
        (measurable_stepAt h a k0).comp (measurable_const.prodMk measurable_fst)
      exact (((measurable_gap h ms Cs).comp hp).const_mul _).add
        ((measurable_pot h ms Cs a n (k0 + 1)).comp (hp.prodMk measurable_snd))
    have hFnn : ∀ w, 0 ≤ F w := by
      intro w
      have h1 : 0 ≤ gap V ms Cs (p w.1) := sub_nonneg.mpr (hopt.2 _ _ (hpC w.1))
      have h2 := pot_nonneg (V := V) hopt hμ ha n (k0 + 1) (p w.1) w.2 (hpC w.1)
      have h3 := averageWeight_pos ha k0
      positivity
    let B := fun ω : Fin d → ℝ => averageWeight a k0 / 2 * gap V ms Cs (p ω) +
      (μ / 4 * (((k0 + 1 : ℕ) : ℝ) + a - 1) * ((((k0 + 1 : ℕ) : ℝ) + a - 2)) * sqd (p ω) (ms, Cs) +
        8 * 𝓛 / μ * bregmanMean V ms Cs (p ω).1 (p ω).2 + 4 * n * σ2 / μ)
    have hsec : ∀ ω, Integrable (fun ξ => F (ω, ξ)) q := by
      intro ω
      simp only [F]
      exact (integrable_const _).addL (ih (k0 + 1) (p ω) (hpC ω)).1
    have hsecb : ∀ ω, ∫ ξ, F (ω, ξ) ∂q ≤ B ω := by
      intro ω
      simp only [F, B]
      rw [integral_add (integrable_const _) (ih (k0 + 1) (p ω) (hpC ω)).1]
      simp only [integral_const, probReal_univ, one_smul]
      have := (ih (k0 + 1) (p ω) (hpC ω)).2
      push_cast at this ⊢
      linarith
    have hgapi : Integrable (fun ω => gap V ms Cs (p ω)) (noiseLaw d) := hstep.1
    have hri : Integrable (fun ω => sqd (p ω) (ms, Cs)) (noiseLaw d) := hstep.2.1
    have hDle : ∀ ω, bregmanMean V ms Cs (p ω).1 (p ω).2 ≤ gap V ms Cs (p ω) := fun ω =>
      bregmanMean_le_objective h hopt (p ω).1 (hpC ω)
    have hD0 : ∀ ω, 0 ≤ bregmanMean V ms Cs (p ω).1 (p ω).2 := by
      intro ω
      have := bregmanMean_lower h (ms := ms) (Cs := Cs) (p ω).1 (isLower_sub (hpC ω).1 hopt.1.1)
      have := sqDist_nonneg (p ω).1 ms (p ω).2 Cs
      nlinarith
    have hDi : Integrable (fun ω => bregmanMean V ms Cs (p ω).1 (p ω).2) (noiseLaw d) := by
      refine Integrable.mono' hgapi (((measurable_bregmanMean h ms Cs).comp
        (measurable_step_fixed h η z)).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hD0 ω)]
      exact hDle ω
    have hBi : Integrable B (noiseLaw d) :=
      (hgapi.const_mul _).addL (((hri.const_mul _).addL (hDi.const_mul _)).addL (integrable_const _))
    have hint : Integrable (fun ω => ∫ ξ, ‖F (ω, ξ)‖ ∂q) (noiseLaw d) := by
      refine hBi.mono' hFm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
        (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun ξ => norm_nonneg _)]
      simp only [Real.norm_eq_abs, abs_of_nonneg (hFnn _)]
      exact hsecb ω
    have hFi : Integrable F ((noiseLaw d).prod q) :=
      (integrable_prod_iff hFm.aestronglyMeasurable).mpr
        ⟨Filter.Eventually.of_forall hsec, hint⟩
    have hmp : Measurable (pot V ms Cs μ a k0 (n + 1) z) :=
      (measurable_pot h ms Cs a (n + 1) k0).of_uncurry_left
    have heq : (fun w : (Fin d → ℝ) × (Fin n → Fin d → ℝ) =>
        pot V ms Cs μ a k0 (n + 1) z (Fin.cons w.1 w.2)) = F := by
      funext w
      simp only [pot, Fin.cons_zero, Fin.cons_succ, F, p]
    have hcons := StochasticGradient.cons_measurePreserving (noiseLaw d) n
    have hpi : Integrable (pot V ms Cs μ a k0 (n + 1) z) (Measure.pi fun _ : Fin (n + 1) => noiseLaw d) :=
      (hcons.integrable_comp hmp.aestronglyMeasurable).mp (by
        simpa only [Function.comp_def, heq] using hFi)
    refine ⟨hpi, ?_⟩
    have hcalc : ∫ ξ, pot V ms Cs μ a k0 (n + 1) z ξ ∂Measure.pi (fun _ : Fin (n + 1) => noiseLaw d) ≤
        ∫ ω, B ω ∂noiseLaw d := by
      calc _ = ∫ w, F w ∂(noiseLaw d).prod q := by
            rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hmp.aestronglyMeasurable,
              heq]
        _ = ∫ ω, ∫ ξ, F (ω, ξ) ∂q ∂noiseLaw d := integral_prod F hFi
        _ ≤ ∫ ω, B ω ∂noiseLaw d := integral_mono hFi.integral_prod_left hBi hsecb
    have hBval : ∫ ω, B ω ∂noiseLaw d ≤
        (((k0 : ℝ) + a - 1) * ∫ ω, gap V ms Cs (p ω) ∂noiseLaw d) +
          μ / 4 * (((k0 : ℝ) + a) * ((k0 : ℝ) + a - 1)) * ∫ ω, sqd (p ω) (ms, Cs) ∂noiseLaw d +
          4 * n * σ2 / μ := by
      have hpt : ∀ ω, B ω ≤ ((k0 : ℝ) + a - 1) * gap V ms Cs (p ω) +
          μ / 4 * (((k0 : ℝ) + a) * ((k0 : ℝ) + a - 1)) * sqd (p ω) (ms, Cs) + 4 * n * σ2 / μ := by
        intro ω
        simp only [B, averageWeight]
        push_cast
        have h1 : 8 * 𝓛 / μ ≤ ((k0 : ℝ) + a - 1) / 2 := by
          rw [hadef]
          have e : 16 * 𝓛 / μ = 2 * (8 * 𝓛 / μ) := by ring
          rw [e]
          have : 0 ≤ (k0 : ℝ) := hk
          linarith
        have h2 := mul_le_mul_of_nonneg_right h1 (hD0 ω)
        have h3 := mul_le_mul_of_nonneg_left (hDle ω) (by linarith : (0 : ℝ) ≤ ((k0 : ℝ) + a - 1) / 2)
        have he : (k0 : ℝ) + 1 + a - 1 = (k0 : ℝ) + a := by ring
        have he2 : (k0 : ℝ) + 1 + a - 2 = (k0 : ℝ) + a - 1 := by ring
        rw [he, he2]
        nlinarith
      have hRi : Integrable (fun ω => ((k0 : ℝ) + a - 1) * gap V ms Cs (p ω) +
          μ / 4 * (((k0 : ℝ) + a) * ((k0 : ℝ) + a - 1)) * sqd (p ω) (ms, Cs) + 4 * n * σ2 / μ)
          (noiseLaw d) := ((hgapi.const_mul _).addL (hri.const_mul _)).addL (integrable_const _)
      have := integral_mono hBi hRi hpt
      rw [integral_add ((hgapi.const_mul _).addL (hri.const_mul _)) (integrable_const _),
        integral_add (hgapi.const_mul _) (hri.const_mul _), integral_const_mul,
        integral_const_mul] at this
      simpa only [integral_const, probReal_univ, one_smul] using this
    have hstep2 := hstep.2.2
    have hgap_eq : ∫ ω, gap V ms Cs (p ω) ∂noiseLaw d =
        ∫ ξ, (objectivePair V (proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ) -
          objective V ms Cs) ∂noiseLaw d := rfl
    have hr_eq : ∫ ω, sqd (p ω) (ms, Cs) ∂noiseLaw d =
        ∫ ξ, sqd (proxStep η z (gradient V (sample z.1 z.2 ξ)) ξ) (ms, Cs) ∂noiseLaw d := rfl
    rw [← hgap_eq, ← hr_eq] at hstep2
    have hpos : 0 < (k0 : ℝ) + a := by linarith
    have hημ : η * μ * ((k0 : ℝ) + a) = 2 := by rw [← hηa]; ring
    have hinv : 1 / (2 * η) = μ * ((k0 : ℝ) + a) / 4 := by
      rw [div_eq_div_iff (by positivity) (by norm_num)]
      have e : μ * ((k0 : ℝ) + a) * (2 * η) = 2 * (η * μ * ((k0 : ℝ) + a)) := by ring
      rw [e, hημ]
      norm_num
    have hone : 1 - η * μ = ((k0 : ℝ) + a - 2) / ((k0 : ℝ) + a) := by
      rw [eq_div_iff hpos.ne']
      have e : (1 - η * μ) * ((k0 : ℝ) + a) = ((k0 : ℝ) + a) - η * μ * ((k0 : ℝ) + a) := by ring
      rw [e, hημ]
    have hwη : ((k0 : ℝ) + a - 1) * η ≤ 2 / μ := by
      rw [le_div_iff₀ hμ]
      have e : ((k0 : ℝ) + a - 1) * η * μ = η * μ * ((k0 : ℝ) + a) - η * μ := by ring
      rw [e, hημ]
      have : 0 ≤ η * μ := by positivity
      linarith
    rw [hinv, hone] at hstep2
    have hscale := mul_le_mul_of_nonneg_left hstep2 (by linarith : (0 : ℝ) ≤ (k0 : ℝ) + a - 1)
    have hA : ((k0 : ℝ) + a - 1) * (μ * ((k0 : ℝ) + a) / 4 *
        (((k0 : ℝ) + a - 2) / ((k0 : ℝ) + a) * sqd z (ms, Cs) -
          ∫ ω, sqd (p ω) (ms, Cs) ∂noiseLaw d)) =
        μ / 4 * (((k0 : ℝ) + a - 1) * ((k0 : ℝ) + a - 2)) * sqd z (ms, Cs) -
          μ / 4 * (((k0 : ℝ) + a) * ((k0 : ℝ) + a - 1)) * ∫ ω, sqd (p ω) (ms, Cs) ∂noiseLaw d := by
      field_simp
    have hDz0 : 0 ≤ bregmanMean V ms Cs z.1 z.2 := by
      have := bregmanMean_lower h (ms := ms) (Cs := Cs) z.1 (isLower_sub hz.1 hopt.1.1)
      have := sqDist_nonneg z.1 ms z.2 Cs
      nlinarith
    rw [mul_add ((k0 : ℝ) + a - 1), hA] at hscale
    have hnoise : ((k0 : ℝ) + a - 1) * (η * (4 * (L * (2 + tau d (L / μ))) *
        bregmanMean V ms Cs z.1 z.2 + 2 * ((2 + tau d (L / μ)) * L * d))) ≤
        8 * 𝓛 / μ * bregmanMean V ms Cs z.1 z.2 + 4 * σ2 / μ := by
      rw [← h𝓛def, ← hσdef]
      have hX : 0 ≤ 4 * 𝓛 * bregmanMean V ms Cs z.1 z.2 + 2 * σ2 :=
        add_nonneg (mul_nonneg (by linarith) hDz0) (by linarith)
      have := mul_le_mul_of_nonneg_right hwη hX
      calc ((k0 : ℝ) + a - 1) * (η * (4 * 𝓛 * bregmanMean V ms Cs z.1 z.2 + 2 * σ2)) =
            ((k0 : ℝ) + a - 1) * η * (4 * 𝓛 * bregmanMean V ms Cs z.1 z.2 + 2 * σ2) := by ring
        _ ≤ 2 / μ * (4 * 𝓛 * bregmanMean V ms Cs z.1 z.2 + 2 * σ2) := this
        _ = 8 * 𝓛 / μ * bregmanMean V ms Cs z.1 z.2 + 4 * σ2 / μ := by ring
    have hsplitn : 4 * ((n : ℝ) + 1) * σ2 / μ = 4 * n * σ2 / μ + 4 * σ2 / μ := by ring
    push_cast
    linarith only [hcalc, hBval, hscale, hnoise, hsplitn]

lemma sample_combo (θ : ℝ) (z z' : Location d × Scale d) (ξ : Fin d → ℝ) :
    sample (θ • z + (1 - θ) • z').1 (θ • z + (1 - θ) • z').2 ξ =
      θ • sample z.1 z.2 ξ + (1 - θ) • sample z'.1 z'.2 ξ := by
  unfold sample
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add,
    mulVec_smul]
  rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add]
  congr 1
  simp only [smul_add]
  abel

lemma isCholesky_combo {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {z z' : Location d × Scale d}
    (hz : IsCholesky z.2) (hz' : IsCholesky z'.2) : IsCholesky (θ • z + (1 - θ) • z').2 := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, hz.1 i j hij,
      hz'.1 i j hij]
  · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hz.2 i
    have h2 := hz'.2 i
    rcases eq_or_lt_of_le hθ0 with h | h
    · subst h
      simpa using h2
    · nlinarith

lemma gap_combo (h : Potential L μ V) (ms : Location d) (Cs : Scale d) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) {z z' : Location d × Scale d} (hz : IsCholesky z.2) (hz' : IsCholesky z'.2) :
    gap V ms Cs (θ • z + (1 - θ) • z') ≤ θ * gap V ms Cs z + (1 - θ) * gap V ms Cs z' := by
  have hE : energy V (θ • z + (1 - θ) • z').1 (θ • z + (1 - θ) • z').2 ≤
      θ * energy V z.1 z.2 + (1 - θ) * energy V z'.1 z'.2 := by
    unfold energy
    simp_rw [sample_combo]
    have hpt : ∀ ξ, V (θ • sample z.1 z.2 ξ + (1 - θ) • sample z'.1 z'.2 ξ) ≤
        θ * V (sample z.1 z.2 ξ) + (1 - θ) * V (sample z'.1 z'.2 ξ) := by
      intro ξ
      have hb : (0 : ℝ) ≤ 1 - θ := by linarith
      have hab : θ + (1 - θ) = 1 := by ring
      have := h.convex.2 (mem_univ (sample z.1 z.2 ξ)) (mem_univ (sample z'.1 z'.2 ξ)) hθ0 hb hab
      simpa only [smul_eq_mul] using this
    have hi1 := integrable_V_sample h z.1 z.2
    have hi2 := integrable_V_sample h z'.1 z'.2
    have hl : Integrable (fun ξ => V (θ • sample z.1 z.2 ξ + (1 - θ) • sample z'.1 z'.2 ξ))
        (noiseLaw d) := by
      have := integrable_V_sample h (θ • z + (1 - θ) • z').1 (θ • z + (1 - θ) • z').2
      simp_rw [sample_combo] at this
      exact this
    have := integral_mono hl ((hi1.const_mul θ).addL (hi2.const_mul (1 - θ))) hpt
    rwa [integral_add (hi1.const_mul θ) (hi2.const_mul (1 - θ)), integral_const_mul,
      integral_const_mul] at this
  have hlog : ∀ i, θ * Real.log (z.2 i i) + (1 - θ) * Real.log (z'.2 i i) ≤
      Real.log ((θ • z + (1 - θ) • z').2 i i) := by
    intro i
    have hb : (0 : ℝ) ≤ 1 - θ := by linarith
    have hab : θ + (1 - θ) = 1 := by ring
    have := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.mpr (hz.2 i))
      (Set.mem_Ioi.mpr (hz'.2 i)) hθ0 hb hab
    simpa only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      using this
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hlog i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  unfold gap objectivePair
  simp only [objective_eq]
  nlinarith

lemma avg_bound (h : Potential L μ V) (ms : Location d) (Cs : Scale d)
    {a : ℝ} (ha : 2 ≤ a) (n : ℕ) (hn : 0 < n) :
    ∀ k0 (z : Location d × Scale d) ξ, IsCholesky z.2 →
      IsCholesky ((wmass a k0 n)⁻¹ • wsum V μ a k0 n z ξ).2 ∧
      gap V ms Cs ((wmass a k0 n)⁻¹ • wsum V μ a k0 n z ξ) ≤
        2 * pot V ms Cs μ a k0 n z ξ / wmass a k0 n := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro k0 z ξ hz
    have hμ := h.pos
    set z1 := stepAt V μ a k0 z (ξ 0)
    have hz1 : IsCholesky z1.2 := stepAt_cholesky hμ ha k0 hz (ξ 0)
    have hw := averageWeight_pos ha k0
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have hm : wmass a k0 1 = averageWeight a k0 := by simp [wmass]
      have hs : wsum V μ a k0 1 z ξ = averageWeight a k0 • z1 := by simp [wsum, z1]
      have hp : pot V ms Cs μ a k0 1 z ξ = averageWeight a k0 / 2 * gap V ms Cs z1 := by
        simp [pot, z1]
      rw [hm, hs, hp, smul_smul, inv_mul_cancel₀ hw.ne', one_smul]
      refine ⟨hz1, le_of_eq ?_⟩
      field_simp
    · obtain ⟨hA, hgap⟩ := ih hnpos (k0 + 1) z1 (fun i => ξ i.succ) hz1
      set M' := wmass a (k0 + 1) n
      set S' := wsum V μ a (k0 + 1) n z1 (fun i => ξ i.succ)
      set P' := pot V ms Cs μ a (k0 + 1) n z1 (fun i => ξ i.succ)
      have hM' : 0 < M' := wmass_pos ha (k0 + 1) hnpos
      have hm : wmass a k0 (n + 1) = averageWeight a k0 + M' := rfl
      have hs : wsum V μ a k0 (n + 1) z ξ = averageWeight a k0 • z1 + S' := rfl
      have hp : pot V ms Cs μ a k0 (n + 1) z ξ = averageWeight a k0 / 2 * gap V ms Cs z1 + P' := rfl
      set w0 := averageWeight a k0 with hw0
      have hsum : 0 < w0 + M' := by linarith
      have hsumne : w0 + M' ≠ 0 := hsum.ne'
      have hM'ne : M' ≠ 0 := hM'.ne'
      set θ := w0 / (w0 + M') with hθ
      have hθ0 : 0 ≤ θ := by positivity
      have hθ1 : θ ≤ 1 := by
        rw [hθ, div_le_one hsum]
        linarith
      have h1θ : 1 - θ = M' / (w0 + M') := by
        rw [hθ]
        field_simp; ring1
      have hcomb : (w0 + M')⁻¹ • (w0 • z1 + S') = θ • z1 + (1 - θ) • (M'⁻¹ • S') := by
        rw [h1θ, smul_add, smul_smul, smul_smul]
        congr 2
        · rw [hθ]
          ring
        · field_simp
      rw [hm, hs, hp, hcomb]
      refine ⟨isCholesky_combo hθ0 hθ1 hz1 hA, ?_⟩
      have hc := gap_combo h ms Cs hθ0 hθ1 hz1 hA
      have h1 : (1 - θ) * gap V ms Cs (M'⁻¹ • S') ≤ (1 - θ) * (2 * P' / M') :=
        mul_le_mul_of_nonneg_left hgap (by linarith)
      have hfin : θ * gap V ms Cs z1 + (1 - θ) * (2 * P' / M') =
          2 * (w0 / 2 * gap V ms Cs z1 + P') / (w0 + M') := by
        rw [h1θ, hθ]
        field_simp
      linarith

noncomputable def lastIter (V : Point d → ℝ) (μ a : ℝ) :
    (k0 n : ℕ) → (Location d × Scale d) → (Fin n → Fin d → ℝ) → Location d × Scale d
  | _, 0, z, _ => z
  | k0, n + 1, z, ξ => lastIter V μ a (k0 + 1) n (stepAt V μ a k0 z (ξ 0)) (fun i => ξ i.succ)

noncomputable def sgdStep (V : Point d → ℝ) (μ a : ℝ) (s : SgdState d) : SgdState d :=
  ⟨s.seeds, s.count + 1, stepAt V μ a s.count s.current (s.seeds s.count),
    s.total + averageWeight a s.count • stepAt V μ a s.count s.current (s.seeds s.count),
    s.mass + averageWeight a s.count⟩

lemma sgdStep_trace (V : Point d → ℝ) (μ a : ℝ) (n : ℕ) :
    ∀ (ω : ℕ → Fin d → ℝ) k0 z T M,
      (sgdStep V μ a)^[n] (⟨ω, k0, z, T, M⟩ : SgdState d) =
      ⟨ω, k0 + n, lastIter V μ a k0 n z (fun i => ω (k0 + i)),
        T + wsum V μ a k0 n z (fun i => ω (k0 + i)), M + wmass a k0 n⟩ := by
  induction n with
  | zero =>
    intro ω k0 z T M
    simp only [Function.iterate_zero, id_eq, lastIter, wsum, wmass, add_zero]
  | succ n ih =>
    intro ω k0 z T M
    rw [Function.iterate_succ_apply]
    have hstep : sgdStep V μ a ⟨ω, k0, z, T, M⟩ =
        ⟨ω, k0 + 1, stepAt V μ a k0 z (ω k0), T + averageWeight a k0 • stepAt V μ a k0 z (ω k0),
          M + averageWeight a k0⟩ := rfl
    rw [hstep, ih]
    have hseq : (fun i : Fin n => ω (k0 + 1 + i)) = fun i : Fin n => ω (k0 + (i.succ : ℕ)) := by
      funext i
      congr 1
      simp only [Fin.val_succ]
      omega
    have h0 : ω (k0 + ((0 : Fin (n + 1)) : ℕ)) = ω k0 := by simp
    simp only [lastIter, wsum, wmass, h0, hseq]
    congr 1
    all_goals first | omega | abel

lemma sgd_trace (V : Point d → ℝ) (μ a : ℝ) (m0 : Location d) (C0 : Scale d) (n : ℕ)
    (ω : ℕ → Fin d → ℝ) (k0 : ℕ) (z T : Location d × Scale d) (M : ℝ) :
      (fun s => (reparameterizedProxSgd μ a m0 C0).update s
        (gradient V ((reparameterizedProxSgd μ a m0 C0).query s).2))^[n]
        (⟨ω, k0, z, T, M⟩ : SgdState d) =
      ⟨ω, k0 + n, lastIter V μ a k0 n z (fun i => ω (k0 + i)),
        T + wsum V μ a k0 n z (fun i => ω (k0 + i)), M + wmass a k0 n⟩ :=
  sgdStep_trace V μ a n ω k0 z T M

lemma measurable_wsum (h : Potential L μ V) (a : ℝ) (n : ℕ) :
    ∀ k0, Measurable (fun w : (Location d × Scale d) × (Fin n → Fin d → ℝ) =>
      wsum V μ a k0 n w.1 w.2) := by
  induction n with
  | zero => intro k0; exact measurable_const
  | succ n ih =>
    intro k0
    have ht : Measurable (fun w : (Location d × Scale d) × (Fin (n + 1) → Fin d → ℝ) =>
        (stepAt V μ a k0 w.1 (w.2 0), fun i : Fin n => w.2 i.succ)) := by
      have hs : Measurable (fun w : (Location d × Scale d) × (Fin (n + 1) → Fin d → ℝ) =>
          stepAt V μ a k0 w.1 (w.2 0)) :=
        (measurable_stepAt h a k0).comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp
          measurable_snd))
      exact hs.prodMk (by fun_prop)
    have h1 := ht.fst
    have h2 := (ih (k0 + 1)).comp ht
    exact ((h1.fst.const_smul (averageWeight a k0)).add h2.fst).prodMk
      ((h1.snd.const_smul (averageWeight a k0)).add h2.snd)

end OracleTemplate.GaussianVariational
