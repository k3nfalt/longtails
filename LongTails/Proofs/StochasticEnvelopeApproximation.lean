import LongTails.Proofs.StochasticEnvelopeLocalization

open MeasureTheory

namespace LongTails.Proofs.StochasticEnvelopeApproximation

open LongTails.Algorithms.StochasticEnvelopeLocalization
open LongTails.Algorithms.StochasticEnvelopePilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma approximate_movement {Ω : Type*} (g : E → Ω → E) (L p a n β : ℝ)
    {μ s : ℝ} (hμ : 0 < μ) (hs : 0 ≤ s) (center : E)
    (b pilotReplicas innerReplicas pilotSteps K J : ℕ)
    (rough : Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω)
    (pilot : ℕ → Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω)
    (inner : ℕ → Fin (innerReplicas + 1) → ℕ → Ω) :
    ‖approximate g L μ p s a n β center b pilotReplicas innerReplicas pilotSteps K J
      rough pilot inner - center‖ ≤
      2 * localizedRadius g L μ s β center rough pilot pilotSteps := by
  exact StochasticEnvelopeLocalization.refineRun_movement g L μ p s a n
    (StochasticEnvelopePilot.localizedRadius_bounds g L β hμ hs center rough pilot pilotSteps).1
    center center K innerReplicas inner J

lemma localized_scale_bound {a r t U : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (hU : U ≤ 192 * (r + t)) :
    t + a * U ≤ 193 * (t + a * r) ∧ r + 2 * U ≤ 385 * (r + t) := by
  have hmul := mul_le_mul_of_nonneg_left hU ha
  have hat : a * t ≤ t := by nlinarith
  have har : 0 ≤ a * r := mul_nonneg ha hr
  constructor <;> nlinarith

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_approximate {Ω : Type} [MeasurableSpace Ω] {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (L μ p s a n β : ℝ) (center : E)
    (b pilotReplicas innerReplicas pilotSteps K J : ℕ) :
    Measurable (fun w : ((Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω) ×
      (ℕ → Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω)) ×
      (ℕ → Fin (innerReplicas + 1) → ℕ → Ω) =>
      approximate g L μ p s a n β center b pilotReplicas innerReplicas pilotSteps K J
        w.1.1 w.1.2 w.2) := by
  have hU : Measurable (fun w : ((Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω) ×
      (ℕ → Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω)) ×
      (ℕ → Fin (innerReplicas + 1) → ℕ → Ω) =>
      localizedRadius g L μ s β center w.1.1 w.1.2 pilotSteps) :=
    (StochasticEnvelopePilot.measurable_localizedRadius hg L μ s β center
      b pilotReplicas pilotSteps).comp measurable_fst
  exact StochasticEnvelopeLocalization.measurable_refineRun hg L μ p s a n center hU
    measurable_const K innerReplicas measurable_snd J

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma localized_moment_bound {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (P : Measure S) (Q : Measure T) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {U : S → ℝ} {Y : S × T → E} (hU : Measurable U) (hY : Measurable Y) (target : E)
    {p a r t z M η₀ η₁ : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 0 ≤ r) (ht : 0 ≤ t) (hz : 0 ≤ z)
    (hη₀ : 0 ≤ η₀) (hη₁ : 0 ≤ η₁)
    (hi : Integrable (fun w => ‖Y w - target‖ ^ 4) (P.prod Q))
    (hm : (∫ w, ‖Y w - target‖ ^ 4 ∂P.prod Q) ≤ M)
    (hmove : ∀ w, ‖Y w - target‖ ≤ r + 2 * U w.1)
    (hpilot : P {u | U u < r + t ∨ 192 * (r + t) < U u} ≤ ENNReal.ofReal η₀)
    (hinner : ∀ u, r + t ≤ U u → U u ≤ 192 * (r + t) →
      Q {v | (t + a * U u) * z < ‖Y (u, v) - target‖} ≤ ENNReal.ofReal η₁) :
    (∫ w, ‖Y w - target‖ ^ p ∂P.prod Q) ≤
      (193 * (t + a * r) * z) ^ p + (385 * (r + t)) ^ p * η₁ +
        M ^ (p / 4) * η₀ ^ (1 / 2 : ℝ) := by
  let B₀ := {u | U u < r + t ∨ 192 * (r + t) < U u}
  let bad₀ : Set (S × T) := Prod.fst ⁻¹' B₀
  let bad₁ : Set (S × T) := {w | w ∉ bad₀ ∧ (t + a * U w.1) * z < ‖Y w - target‖}
  have hB₀ : MeasurableSet B₀ :=
    (measurableSet_lt hU measurable_const).union (measurableSet_lt measurable_const hU)
  have hbad₀ : MeasurableSet bad₀ := measurable_fst hB₀
  have hthreshold : Measurable (fun w : S × T => (t + a * U w.1) * z) := by fun_prop
  have hbad₁ : MeasurableSet bad₁ := hbad₀.compl.inter
    (measurableSet_lt hthreshold ((hY.sub_const target).norm))
  have hgood (w : S × T) (hw : w ∉ bad₀) : r + t ≤ U w.1 ∧ U w.1 ≤ 192 * (r + t) := by
    exact ⟨le_of_not_gt (fun hlt => hw (Or.inl hlt)), le_of_not_gt (fun hlt => hw (Or.inr hlt))⟩
  have hprob₀ : (P.prod Q) bad₀ ≤ ENNReal.ofReal η₀ := by
    have hf : MeasurePreserving Prod.fst (P.prod Q) P := measurePreserving_fst
    rw [show (P.prod Q) bad₀ = P B₀ from hf.measure_preimage hB₀.nullMeasurableSet]
    exact hpilot
  have hprob₁ : (P.prod Q) bad₁ ≤ ENNReal.ofReal η₁ := by
    have hh := StochasticEnvelopeFreshness.product_failure_probability P Q hbad₁
      (B := ∅) MeasurableSet.empty (ε₀ := 0) (by simp) (ε₁ := ENNReal.ofReal η₁) ?_
    · simpa only [zero_add] using hh
    · intro u _
      by_cases hu : u ∈ B₀
      · have he : {v : T | (u, v) ∈ bad₁} = ∅ := by ext v; simp [bad₁, bad₀, hu]
        rw [he, measure_empty]
        exact bot_le
      · have hu' : r + t ≤ U u ∧ U u ≤ 192 * (r + t) :=
          ⟨le_of_not_gt (fun hlt => hu (Or.inl hlt)), le_of_not_gt (fun hlt => hu (Or.inr hlt))⟩
        exact (measure_mono (fun v hv => hv.2)).trans (hinner u hu'.1 hu'.2)
  have hreal₀ : (P.prod Q).real bad₀ ≤ η₀ := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal hη₀] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob₀
  have hreal₁ : (P.prod Q).real bad₁ ≤ η₁ := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal hη₁] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob₁
  have hM : 0 ≤ M := (integral_nonneg (fun _ => by positivity)).trans hm
  have hb := StochasticEnvelopeSampling.two_event_moment (hY.sub_const target) hp hp2
    (by positivity : 0 ≤ (193 * (t + a * r) * z) ^ p)
    (by positivity : 0 ≤ (385 * (r + t)) ^ p) hbad₀ hbad₁ hi ?_ ?_
  · apply hb.trans
    have h₁ := mul_le_mul_of_nonneg_left hreal₁
      (by positivity : 0 ≤ (385 * (r + t)) ^ p)
    have h₂ := Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity)) hm
      (by positivity : 0 ≤ p / 4)
    have h₃ := Real.rpow_le_rpow (measureReal_nonneg) hreal₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h₄ := mul_le_mul h₂ h₃ (by positivity) (by positivity)
    linarith
  · intro w hw _
    have hs := (localized_scale_bound ha ha1 hr ht (hgood w hw).2).2
    exact Real.rpow_le_rpow (norm_nonneg _) ((hmove w).trans hs) hp.le
  · intro w hw hwi
    have he : ‖Y w - target‖ ≤ (t + a * U w.1) * z :=
      le_of_not_gt (fun hh => hwi ⟨hw, hh⟩)
    have hs := mul_le_mul_of_nonneg_right
      (localized_scale_bound ha ha1 hr ht (hgood w hw).2).1 hz
    exact Real.rpow_le_rpow (norm_nonneg _) (he.trans hs) hp.le

variable [CompleteSpace E]

open RecursiveEnvelopeGeometry in
lemma approximate_fourth_moment {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E}
    {f : E → ℝ} {L μ p s a : ℝ} (h : Model L f field)
    (hg : Measurable (Function.uncurry g)) (hμ : 0 < μ)
    (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (n β : ℝ) (center : E) (pilotReplicas innerReplicas pilotSteps K J : ℕ)
    (hrep : 8 ≤ pilotReplicas + 1) :
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let Q := Measure.pi fun _ : Fin (pilotReplicas + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
    let R := (Q.prod (Measure.infinitePi fun _ : ℕ => Q)).prod
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerReplicas + 1) =>
        Measure.infinitePi fun _ : ℕ => P)
    let X := fun w => approximate g L μ p s a n β center b pilotReplicas innerReplicas
      pilotSteps K J w.1.1 w.1.2 w.2
    Integrable (fun w => ‖X w - prox field μ center‖ ^ 4) R ∧
      (∫ w, ‖X w - prox field μ center‖ ^ 4 ∂R) ≤
        2 ^ 56 * ((L + μ) / μ) ^ 6 * (‖center - prox field μ center‖ + s / μ) ^ 4 := by
  let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
  let Q := Measure.pi fun _ : Fin (pilotReplicas + 1) =>
    Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
  let R₀ := Q.prod (Measure.infinitePi fun _ : ℕ => Q)
  let R := R₀.prod (Measure.infinitePi fun _ : ℕ =>
    Measure.pi fun _ : Fin (innerReplicas + 1) => Measure.infinitePi fun _ : ℕ => P)
  let U := fun w : (Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω) ×
      (ℕ → Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω) =>
    localizedRadius g L μ s β center w.1 w.2 pilotSteps
  obtain ⟨hUi, hUm⟩ := StochasticEnvelopePilot.localizedRadius_fourth_moment P h hg hμ hp hp2
    hs ha ha1 hi hmean hpi hm β center pilotReplicas pilotSteps hrep
  have hf : MeasurePreserving Prod.fst R R₀ := measurePreserving_fst
  have hlift : Integrable (fun w => U w.1 ^ 4) R := hf.integrable_comp_of_integrable hUi
  have he : (∫ w, U w.1 ^ 4 ∂R) = ∫ w, U w ^ 4 ∂R₀ := by
    calc
      _ = ∫ w, U w ^ 4 ∂Measure.map Prod.fst R :=
        (integral_map hf.measurable.aemeasurable (by
          simpa only [hf.map_eq] using hUi.aestronglyMeasurable)).symm
      _ = _ := by rw [hf.map_eq]
  apply StochasticEnvelopeSampling.final_fourth_moment
    (measurable_approximate hg L μ p s a n β center b pilotReplicas innerReplicas pilotSteps K J)
    (prox field μ center)
    (fun w => (StochasticEnvelopePilot.localizedRadius_bounds g L β hμ hs center
      w.1.1 w.1.2 pilotSteps).1)
    ((le_div_iff₀ hμ).mpr (by linarith [h.pos])) (norm_nonneg _) (by positivity) hlift
    (by rw [he]; exact hUm)
  intro w
  have hm := approximate_movement g L p a n β hμ hs center b pilotReplicas innerReplicas
    pilotSteps K J w.1.1 w.1.2 w.2
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (approximate g L μ p s a n β center b pilotReplicas innerReplicas pilotSteps K J
      w.1.1 w.1.2 w.2) center (prox field μ center)
  linarith

open RecursiveEnvelopeGeometry in
lemma approximate_tuned_moment {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E}
    {f : E → ℝ} {L μ p s a n η₀ η₁ : ℝ} (h : Model L f field)
    (hμ : 0 < μ) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 < a) (hn : 1 ≤ n)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hη₀ : 0 < η₀) (hη₁ : 0 < η₁) (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) :
    let κ := (L + μ) / μ
    let β := 1 / (1024 * κ)
    let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
    let pilotReplicas := 7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η₀)⌉₊
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let J := ⌈2 * Real.log (1 + n / a)⌉₊
    let innerReplicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η₁)⌉₊
    let K := ⌈(268435456 : ℝ) ^ (p / (p - 1)) * (Real.sqrt κ + n + 1)⌉₊
    let Q := Measure.pi fun _ : Fin (pilotReplicas + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
    let R := (Q.prod (Measure.infinitePi fun _ : ℕ => Q)).prod
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerReplicas + 1) =>
        Measure.infinitePi fun _ : ℕ => P)
    let X := fun w => approximate g L μ p s a n β center b pilotReplicas innerReplicas N K J
      w.1.1 w.1.2 w.2
    let r := ‖center - prox field μ center‖
    let t := s / μ
    Integrable (fun w => ‖X w - prox field μ center‖ ^ p) R ∧
      (∫ w, ‖X w - prox field μ center‖ ^ p ∂R) ≤
        (193 * (t + a * r) * n ^ (-(p - 1) / p)) ^ p + (385 * (r + t)) ^ p * η₁ +
          (2 ^ 56 * κ ^ 6 * (r + t) ^ 4) ^ (p / 4) * η₀ ^ (1 / 2 : ℝ) := by
  let κ := (L + μ) / μ
  let β := 1 / (1024 * κ)
  let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
  let pilotReplicas := 7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η₀)⌉₊
  let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
  let J := ⌈2 * Real.log (1 + n / a)⌉₊
  let innerReplicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η₁)⌉₊
  let K := ⌈(268435456 : ℝ) ^ (p / (p - 1)) * (Real.sqrt κ + n + 1)⌉₊
  let Q := Measure.pi fun _ : Fin (pilotReplicas + 1) =>
    Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
  let R₀ := Q.prod (Measure.infinitePi fun _ : ℕ => Q)
  let R₁ := Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerReplicas + 1) =>
    Measure.infinitePi fun _ : ℕ => P
  let U := fun w : (Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω) ×
      (ℕ → Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω) =>
    localizedRadius g L μ s β center w.1 w.2 N
  let X := fun w :
      ((Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω) ×
        (ℕ → Fin (pilotReplicas + 1) → Fin 8 → Fin (b + 1) → Ω)) ×
        (ℕ → Fin (innerReplicas + 1) → ℕ → Ω) => approximate g L μ p s a n β center b pilotReplicas innerReplicas N K J
    w.1.1 w.1.2 w.2
  have hκ0 : 0 < κ := by change 2 ≤ κ at hκ; linarith
  have hak : a ≤ κ⁻¹ ^ 2 := by
    change a ≤ κ ^ (-2 : ℝ) at haκ
    simpa only [Real.rpow_neg hκ0.le, Real.rpow_two, inv_pow] using haκ
  have htune := StochasticEnvelopePilot.pilot_relative_tuning hκ hak
  have ha1 : a ≤ 1 := by linarith [htune.2.1, htune.2.2.1]
  have hrep : 8 ≤ pilotReplicas + 1 := (StochasticEnvelopeSampling.confidence_allocation N hη₀).1
  obtain ⟨hXi4, hXm4⟩ := approximate_fourth_moment P h hg hμ hp hp2 hs ha.le ha1
    hi hmean hpi hm n β center pilotReplicas innerReplicas N K J hrep
  have hX : Measurable X := measurable_approximate hg L μ p s a n β center b pilotReplicas innerReplicas N K J
  have hU : Measurable U := StochasticEnvelopePilot.measurable_localizedRadius hg L μ s β center b pilotReplicas N
  refine ⟨(StochasticEnvelopeSampling.lower_power_from_fourth (hX.sub_const (prox field μ center))
    (by linarith : 0 ≤ p) (by linarith : p ≤ 4) hXi4).1, ?_⟩
  apply localized_moment_bound R₀ R₁ hU hX (prox field μ center)
    (by linarith : 0 < p) hp2 ha.le ha1 (norm_nonneg _) (by positivity) (by positivity)
    hη₀.le hη₁.le hXi4 hXm4
  · intro w
    have hm := approximate_movement g L p a n β hμ hs center b pilotReplicas innerReplicas
      N K J w.1.1 w.1.2 w.2
    have hh := norm_sub_le_norm_sub_add_norm_sub (X w) center (prox field μ center)
    dsimp only [X] at hh
    linarith
  · exact StochasticEnvelopePilot.localizedRadius_tuned_failure P h hμ hp hp2 hs ha.le hη₀
      hκ haκ hg hi hmean hpi hm center
  · intro u hu _
    have hrU : ‖center - prox field μ center‖ ≤ U u := by
      have hsμ : 0 ≤ s / μ := by positivity
      linarith
    exact StochasticEnvelopeLocalization.refineRun_stopped_failure
      (⟨P, inferInstance⟩ : ProbabilityMeasure Ω) h hμ hp hp2 hs ha hn hκ haκ hg hi hmean hpi hm
      center center hrU hrU hη₁


open RecursiveEnvelopeGeometry in
lemma approximate_moment {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E}
    {f : E → ℝ} {L μ p s a n : ℝ} (h : Model L f field)
    (hμ : 0 < μ) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 < a) (hn : 1 ≤ n)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) :
    let κ := (L + μ) / μ
    let η₀ := (2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) * n ^ (-2 * (p - 1))
    let η₁ := (2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))
    let β := 1 / (1024 * κ)
    let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
    let pilotReplicas := 7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η₀)⌉₊
    let b := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    let J := ⌈2 * Real.log (1 + n / a)⌉₊
    let innerReplicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η₁)⌉₊
    let K := ⌈(268435456 : ℝ) ^ (p / (p - 1)) * (Real.sqrt κ + n + 1)⌉₊
    let Q := Measure.pi fun _ : Fin (pilotReplicas + 1) =>
      Measure.pi fun _ : Fin 8 => Measure.pi fun _ : Fin (b + 1) => P
    let R := (Q.prod (Measure.infinitePi fun _ : ℕ => Q)).prod
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerReplicas + 1) =>
        Measure.infinitePi fun _ : ℕ => P)
    let X := fun w => approximate g L μ p s a n β center b pilotReplicas innerReplicas N K J
      w.1.1 w.1.2 w.2
    let r := ‖center - prox field μ center‖
    let t := s / μ
    Integrable (fun w => ‖X w - prox field μ center‖ ^ p) R ∧
      (∫ w, ‖X w - prox field μ center‖ ^ p ∂R) ≤
        (2 : ℝ) ^ (18 : ℝ) * (t + a * r) ^ p * n ^ (-(p - 1)) := by
  let κ := (L + μ) / μ
  let η₀ := (2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) * n ^ (-2 * (p - 1))
  let η₁ := (2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))
  have hκ0 : 0 < κ := by change 2 ≤ κ at hκ; linarith
  have hn0 : 0 < n := by linarith
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hη₁ : 0 < η₁ := by dsimp [η₁]; positivity
  have hak : a ≤ κ⁻¹ ^ 2 := by
    change a ≤ κ ^ (-2 : ℝ) at haκ
    simpa only [Real.rpow_neg hκ0.le, Real.rpow_two, inv_pow] using haκ
  have htune := StochasticEnvelopePilot.pilot_relative_tuning hκ hak
  have ha1 : a ≤ 1 := by linarith [htune.2.1, htune.2.2.1]
  obtain ⟨hiX, hmX⟩ := approximate_tuned_moment P h hμ hp hp2 hs ha hn hκ haκ
    hη₀ hη₁ hg hi hmean hpi hm center
  refine ⟨hiX, hmX.trans ?_⟩
  have hc := StochasticEnvelopeSampling.one_level_moment_cancellation hp hp2 hκ ha ha1 hn
    (norm_nonneg (center - prox field μ center)) (div_nonneg hs hμ.le)
  simpa only [η₀, η₁, Real.rpow_ofNat] using hc


end LongTails.Proofs.StochasticEnvelopeApproximation
