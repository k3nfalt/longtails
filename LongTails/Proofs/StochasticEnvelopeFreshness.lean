import LongTails.Proofs.HeavyTailedProductProcess
import Mathlib.Probability.IdentDistrib
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.RobustAdaptiveFailures
import LongTails.Proofs.TwoSidedPLSampling

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.StochasticEnvelopeFreshness

variable {Ω S V : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace V]

lemma measurable_seed_shift {length : S → ℕ} (hlength : Measurable length) :
    Measurable (fun w : S × (ℕ → Ω) => fun j => w.2 (length w.1 + j)) := by
  apply Measurable.of_eval
  intro j
  have hm : Measurable (fun w : (ℕ → Ω) × ℕ => w.1 (w.2 + j)) :=
    measurable_from_prod_countable_left (fun n => measurable_pi_apply (n + j))
  exact hm.comp (measurable_snd.prodMk (hlength.comp measurable_fst))

lemma prefix_tail_lintegral (p : Measure Ω) [IsProbabilityMeasure p]
    (n : ℕ) (X : (ℕ → Ω) → V) (hX : Measurable X)
    (hdep : ∀ ξ ζ, (∀ j, j < n → ξ j = ζ j) → X ξ = X ζ)
    (F : V × (ℕ → Ω) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ξ, F (X ξ, fun j => ξ (n + j)) ∂Measure.infinitePi (fun _ : ℕ => p)) =
      ∫⁻ ξ, ∫⁻ ζ, F (X ξ, ζ) ∂Measure.infinitePi (fun _ : ℕ => p)
        ∂Measure.infinitePi (fun _ : ℕ => p) := by
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  let X' := X ∘ OracleTemplate.TwoSidedPL.extendPrefix ω0 n
  have hX' : Measurable X' := hX.comp (OracleTemplate.TwoSidedPL.measurable_extendPrefix ω0 n)
  have he (ξ : ℕ → Ω) : X ξ = X' (fun i : Fin n => ξ i) :=
    OracleTemplate.TwoSidedPL.factor_prefix ω0 n X hdep ξ
  let G : (Fin n → Ω) × (ℕ → Ω) → ℝ≥0∞ := fun w => F (X' w.1, w.2)
  have hG : Measurable G := hF.comp ((hX'.comp measurable_fst).prodMk measurable_snd)
  simp_rw [he]
  calc
    _ = ∫⁻ w, G w ∂((Measure.pi fun _ : Fin n => p).prod
        (Measure.infinitePi fun _ : ℕ => p)) :=
      (OracleTemplate.StochasticGeneralized.splitStream_preserving p n).lintegral_comp hG
    _ = ∫⁻ b, ∫⁻ ζ, G (b, ζ) ∂Measure.infinitePi (fun _ : ℕ => p)
        ∂Measure.pi (fun _ : Fin n => p) := lintegral_prod G hG.aemeasurable
    _ = _ := ((OracleTemplate.StochasticGeneralized.prefix_preserving p n).lintegral_comp
      hG.lintegral_prod_right').symm

lemma seed_prefix_tail_lintegral (p : Measure Ω) [IsProbabilityMeasure p]
    (Q : Measure S)
    {length : S → ℕ} (hlength : Measurable length)
    (X : S × (ℕ → Ω) → V) (hX : Measurable X)
    (hdep : ∀ s ξ ζ, (∀ j, j < length s → ξ j = ζ j) → X (s, ξ) = X (s, ζ))
    (F : (S × V) × (ℕ → Ω) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F ((w.1, X w), fun j => w.2 (length w.1 + j))
      ∂Q.prod (Measure.infinitePi fun _ : ℕ => p)) =
      ∫⁻ w, ∫⁻ ζ, F ((w.1, X w), ζ) ∂Measure.infinitePi (fun _ : ℕ => p)
        ∂Q.prod (Measure.infinitePi fun _ : ℕ => p) := by
  have hleft : Measurable (fun w : S × (ℕ → Ω) =>
      F ((w.1, X w), fun j => w.2 (length w.1 + j))) :=
    hF.comp ((measurable_fst.prodMk hX).prodMk (measurable_seed_shift hlength))
  have hright : Measurable (fun w : S × (ℕ → Ω) =>
      ∫⁻ ζ, F ((w.1, X w), ζ) ∂Measure.infinitePi (fun _ : ℕ => p)) :=
    hF.lintegral_prod_right'.comp (measurable_fst.prodMk hX)
  rw [lintegral_prod _ hleft.aemeasurable, lintegral_prod _ hright.aemeasurable]
  apply lintegral_congr
  intro s
  exact prefix_tail_lintegral p (length s) (fun ξ => X (s, ξ))
    (hX.comp measurable_prodMk_left) (hdep s)
    (fun w => F ((s, w.1), w.2))
    (hF.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))

lemma seed_prefix_tail_preserving (p : Measure Ω) [IsProbabilityMeasure p]
    (Q : Measure S)
    {length : S → ℕ} (hlength : Measurable length)
    (X : S × (ℕ → Ω) → V) (hX : Measurable X)
    (hdep : ∀ s ξ ζ, (∀ j, j < length s → ξ j = ζ j) → X (s, ξ) = X (s, ζ)) :
    MeasurePreserving
      (fun w : S × (ℕ → Ω) => ((w.1, X w), fun j => w.2 (length w.1 + j)))
      (Q.prod (Measure.infinitePi fun _ : ℕ => p))
      (((Q.prod (Measure.infinitePi fun _ : ℕ => p)).map (fun w => (w.1, X w))).prod
        (Measure.infinitePi fun _ : ℕ => p)) := by
  have hjoint : Measurable (fun w : S × (ℕ → Ω) => (w.1, X w)) :=
    measurable_fst.prodMk hX
  have hsplit := hjoint.prodMk (measurable_seed_shift hlength)
  refine ⟨hsplit, ?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hsplit, seed_prefix_tail_lintegral p Q hlength X hX hdep F hF,
    lintegral_prod F hF.aemeasurable, lintegral_map hF.lintegral_prod_right' hjoint]

lemma adaptive_failure_probability (p : Measure Ω) [IsProbabilityMeasure p]
    {cost : S → ℕ} {next : (n : ℕ) → S → (Fin n → Ω) → S}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (bad : (n : ℕ) → Set (S × (Fin n → Ω))) (hbad : ∀ n, MeasurableSet (bad n))
    {η : ℝ}
    (hprob : ∀ s, (Measure.pi (fun _ : Fin (cost s) => p)).real
      {b | (s, b) ∈ bad (cost s)} ≤ η) (K : ℕ) (initial : S) :
    MeasurableSet {ξ : ℕ → Ω | ∃ j < K,
      let w := OracleTemplate.StochasticGeneralized.blockTrace cost next initial ξ j
      (w.1, fun i : Fin (cost w.1) => w.2 i) ∈ bad (cost w.1)} ∧
    (Measure.infinitePi fun _ : ℕ => p) {ξ : ℕ → Ω | ∃ j < K,
      let w := OracleTemplate.StochasticGeneralized.blockTrace cost next initial ξ j
      (w.1, fun i : Fin (cost w.1) => w.2 i) ∈ bad (cost w.1)} ≤ ENNReal.ofReal (K * η) := by
  classical
  let increment := fun n (s : S) (b : Fin n → Ω) => if (s, b) ∈ bad n then (1 : ℝ) else 0
  have hi (n : ℕ) : Measurable (Function.uncurry (increment n)) :=
    Measurable.ite (hbad n) measurable_const measurable_const
  have hinc (n : ℕ) (s : S) (b : Fin n → Ω) :
      0 ≤ increment n s b ∧ increment n s b ≤ 1 := by
    dsimp [increment]
    split_ifs <;> norm_num
  have hbound (s : S) :
      (∫ b, increment (cost s) s b ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ η := by
    change (∫ b, ({b | (s, b) ∈ bad (cost s)}).indicator (1 : (Fin (cost s) → Ω) → ℝ) b
      ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ η
    have hs : MeasurableSet {b : Fin (cost s) → Ω | (s, b) ∈ bad (cost s)} :=
      (hbad (cost s)).preimage measurable_prodMk_left
    rw [integral_indicator_one hs]
    exact hprob s
  have he : {ξ : ℕ → Ω | ∃ j < K,
      let w := OracleTemplate.StochasticGeneralized.blockTrace cost next initial ξ j
      (w.1, fun i : Fin (cost w.1) => w.2 i) ∈ bad (cost w.1)} =
      {ξ | 1 ≤ OracleTemplate.StochasticGeneralized.accumulated cost next increment K initial ξ} := by
    ext ξ
    constructor
    · rintro ⟨j, hj, hfail⟩
      change 1 ≤ OracleTemplate.StochasticGeneralized.accumulated cost next increment K initial ξ
      rw [OracleTemplate.StochasticGeneralized.accumulated_eq_sum]
      have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.range K) =>
        (hinc (cost (OracleTemplate.StochasticGeneralized.blockTrace cost next initial ξ i).1)
          (OracleTemplate.StochasticGeneralized.blockTrace cost next initial ξ i).1
          (fun k => (OracleTemplate.StochasticGeneralized.blockTrace cost next initial ξ i).2 k)).1)
        (Finset.mem_range.mpr hj)
      simpa only [increment, ite_eq_left hfail] using hh
    · intro hsum
      by_contra hnone
      have hz : OracleTemplate.StochasticGeneralized.accumulated cost next increment K initial ξ = 0 := by
        rw [OracleTemplate.StochasticGeneralized.accumulated_eq_sum]
        apply Finset.sum_eq_zero
        intro j hj
        dsimp [increment]
        rw [ite_eq_right (fun hh => hnone ⟨j, Finset.mem_range.mp hj, hh⟩)]
      change 1 ≤ OracleTemplate.StochasticGeneralized.accumulated cost next increment K initial ξ at hsum
      rw [hz] at hsum
      norm_num at hsum
  rw [he]
  refine ⟨measurableSet_le measurable_const
    ((OracleTemplate.StochasticGeneralized.accumulated_measurable hc hn hi K).comp
      measurable_prodMk_left), ?_⟩
  exact OracleTemplate.RobustGradient.accumulated_failure_probability p hc hn hi hinc hbound K initial

lemma fixed_step_failure_probability (p : Measure Ω) [IsProbabilityMeasure p]
    (T : S → Ω → S) (hT : Measurable (Function.uncurry T))
    (bad : Set (S × Ω)) (hbad : MeasurableSet bad) {η : ℝ}
    (hprob : ∀ s, p.real {ω | (s, ω) ∈ bad} ≤ η) (K : ℕ) (initial : S) :
    MeasurableSet {ξ : ℕ → Ω | ∃ j < K,
      (OracleTemplate.StochasticGradient.advance (fun k s => T s (ξ k)) j 0 initial,
        ξ j) ∈ bad} ∧
    (Measure.infinitePi fun _ : ℕ => p) {ξ : ℕ → Ω | ∃ j < K,
      (OracleTemplate.StochasticGradient.advance (fun k s => T s (ξ k)) j 0 initial,
        ξ j) ∈ bad} ≤ ENNReal.ofReal (K * η) := by
  classical
  let next : (n : ℕ) → S → (Fin n → Ω) → S := fun n s b =>
    if h : 0 < n then T s (b ⟨0, h⟩) else s
  let badBlock : (n : ℕ) → Set (S × (Fin n → Ω)) := fun n =>
    if h : 0 < n then {w | (w.1, w.2 ⟨0, h⟩) ∈ bad} else ∅
  have hn (n : ℕ) : Measurable (Function.uncurry (next n)) := by
    by_cases h : 0 < n
    · simp only [next, h, dite_true, Function.uncurry_def]
      exact hT.comp (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd))
    · simpa only [next, h, dite_false, Function.uncurry_def] using measurable_fst
  have hb (n : ℕ) : MeasurableSet (badBlock n) := by
    by_cases h : 0 < n
    · simp only [badBlock, h, dite_true]
      exact hbad.preimage (measurable_fst.prodMk ((measurable_pi_apply _).comp measurable_snd))
    · simp only [badBlock, h, dite_false]
      exact MeasurableSet.empty
  have hp (s : S) : (Measure.pi (fun _ : Fin 1 => p)).real
      {b | (s, b) ∈ badBlock 1} ≤ η := by
    have hs : MeasurableSet {ω | (s, ω) ∈ bad} :=
      hbad.preimage measurable_prodMk_left
    have he := (measurePreserving_eval (fun _ : Fin 1 => p) (0 : Fin 1)).measure_preimage hs.nullMeasurableSet
    change ((Measure.pi (fun _ : Fin 1 => p)) {b | (s, b 0) ∈ bad}).toReal ≤ η
    change (Measure.pi (fun _ : Fin 1 => p)) {b | (s, b 0) ∈ bad} = _ at he
    rw [he]
    exact hprob s
  have ha (step : ℕ → S → S) (j c : ℕ) (s : S) :
      OracleTemplate.StochasticGradient.advance step (j + 1) c s =
        step (c + j) (OracleTemplate.StochasticGradient.advance step j c s) := by
    induction j generalizing c s with
    | zero => simp [OracleTemplate.StochasticGradient.advance]
    | succ j ih =>
      change OracleTemplate.StochasticGradient.advance step (j + 1) (c + 1) (step c s) =
        step (c + (j + 1)) (OracleTemplate.StochasticGradient.advance step j (c + 1) (step c s))
      rw [ih]
      congr 1
      omega
  have he (ξ : ℕ → Ω) (j : ℕ) :
      OracleTemplate.StochasticGeneralized.blockTrace (fun _ : S => 1) next initial ξ j =
      (OracleTemplate.StochasticGradient.advance (fun k s => T s (ξ k)) j 0 initial,
        fun k => ξ (j + k)) := by
    induction j with
    | zero => simp [OracleTemplate.StochasticGeneralized.blockTrace_zero,
        OracleTemplate.StochasticGradient.advance]
    | succ j ih =>
      rw [OracleTemplate.StochasticGeneralized.blockTrace_succ, ih, ha]
      simp only [OracleTemplate.StochasticGeneralized.blockAdvance, next, Nat.zero_lt_one,
        dite_true, Nat.zero_add, Nat.add_zero]
      congr 1
      funext k
      congr 1
      omega
  have hh := adaptive_failure_probability p (cost := fun _ : S => 1)
    measurable_const hn badBlock hb hp K initial
  simpa [he, badBlock] using hh

lemma product_failure_probability {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure U) (Q : Measure V) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {bad : Set (U × V)} (hbad : MeasurableSet bad) {B : Set U} (hB : MeasurableSet B)
    {ε₀ ε₁ : ℝ≥0∞} (hrough : P B ≤ ε₀)
    (hconditional : ∀ u, u ∉ B → Q {v | (u, v) ∈ bad} ≤ ε₁) :
    (P.prod Q) bad ≤ ε₀ + ε₁ := by
  rw [Measure.prod_apply hbad]
  calc
    _ ≤ ∫⁻ u, B.indicator (1 : U → ℝ≥0∞) u + ε₁ ∂P := by
      apply lintegral_mono
      intro u
      change Q {v | (u, v) ∈ bad} ≤ _
      by_cases hu : u ∈ B
      · simp only [Set.indicator_of_mem hu, Pi.one_apply]
        exact (prob_le_one (μ := Q)).trans (le_add_right le_rfl)
      · simpa only [Set.indicator_of_notMem hu, zero_add] using hconditional u hu
    _ = P B + ε₁ := by
      have hi : Measurable (B.indicator (1 : U → ℝ≥0∞)) :=
        measurable_const.indicator hB
      rw [lintegral_add_left hi, lintegral_indicator_one hB,
        lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by gcongr

section Composition
variable {S Ω V A : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
  [MeasurableSpace V] [MeasurableSpace A]

lemma swap_middle_preserving {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (P : Measure X) (Q : Measure Y) (R : Measure Z)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    MeasurePreserving (fun w : (X × Y) × Z => ((w.1.1, w.2), w.1.2))
      ((P.prod Q).prod R) ((P.prod R).prod Q) := by
  have h := ((measurePreserving_prodAssoc P R Q).symm MeasurableEquiv.prodAssoc).comp
    (((MeasurePreserving.id P).prod (Measure.measurePreserving_swap (μ := Q) (ν := R))).comp
      (measurePreserving_prodAssoc P Q R))
  convert h using 1
  rfl

lemma fresh_step_preserving (Q : Measure S) (p : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure p]
    {cost : S → ℕ} (hc : Measurable cost) (F : S × (ℕ → Ω) → V) (hF : Measurable F)
    (hdep : ∀ s ξ ζ, (∀ j, j < cost s → ξ j = ζ j) → F (s, ξ) = F (s, ζ)) :
    MeasurePreserving (fun w : (ℕ → S) × (ℕ → Ω) =>
      ((w.1 0, F (w.1 0, w.2)), ((fun j => w.1 (j + 1)), fun j => w.2 (cost (w.1 0) + j))))
      ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => p))
      (((Q.prod (Measure.infinitePi fun _ : ℕ => p)).map (fun w => (w.1, F w))).prod
        ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => p))) := by
  let T := Measure.infinitePi fun _ : ℕ => Q
  let R := Measure.infinitePi fun _ : ℕ => p
  let M := (Q.prod R).map (fun w => (w.1, F w))
  have h1 := (HeavyTailedProductProcess.head_tail_preserving Q).prod (MeasurePreserving.id R)
  have h2 := swap_middle_preserving Q T R
  have h3 := (seed_prefix_tail_preserving p Q hc F hF hdep).prod (MeasurePreserving.id T)
  have h4 := swap_middle_preserving M R T
  have h5 := measurePreserving_prodAssoc M T R
  have hall := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  convert hall using 1
  rfl

lemma fresh_step_lintegral (Q : Measure S) (p : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure p]
    {cost : S → ℕ} (hc : Measurable cost) (F : S × (ℕ → Ω) → V) (hF : Measurable F)
    (hdep : ∀ s ξ ζ, (∀ j, j < cost s → ξ j = ζ j) → F (s, ξ) = F (s, ζ))
    (G : V × ((ℕ → S) × (ℕ → Ω)) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ w, G (F (w.1 0, w.2), ((fun j => w.1 (j + 1)), fun j => w.2 (cost (w.1 0) + j)))
      ∂((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => p))) =
      ∫⁻ child, ∫⁻ tails, G (F child, tails)
        ∂((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => p))
        ∂Q.prod (Measure.infinitePi fun _ : ℕ => p) := by
  let G' : (S × V) × ((ℕ → S) × (ℕ → Ω)) → ℝ≥0∞ := fun w => G (w.1.2, w.2)
  have hG' : Measurable G' := hG.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hh := (fresh_step_preserving Q p hc F hF hdep).lintegral_comp hG'
  rw [lintegral_prod G' hG'.aemeasurable,
    lintegral_map hG'.lintegral_prod_right' (measurable_fst.prodMk hF)] at hh
  exact hh

omit [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace A] in
def freshRun (cost : ℕ → S → ℕ) (step : ℕ → A → S × (ℕ → Ω) → A) :
    ℕ → ℕ → A → ((ℕ → S) × (ℕ → Ω)) → A
  | 0, _, state, _ => state
  | N + 1, call, state, w => freshRun cost step N (call + 1) (step call state (w.1 0, w.2))
      ((fun j => w.1 (j + 1)), fun j => w.2 (cost call (w.1 0) + j))

omit [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace A] in
def idealRun (step : ℕ → A → S × (ℕ → Ω) → A) :
    ℕ → ℕ → A → (ℕ → S × (ℕ → Ω)) → A
  | 0, _, state, _ => state
  | N + 1, call, state, ξ => idealRun step N (call + 1) (step call state (ξ 0)) (fun j => ξ (j + 1))

lemma freshRun_measurable {cost : ℕ → S → ℕ} (hc : ∀ k, Measurable (cost k))
    {step : ℕ → A → S × (ℕ → Ω) → A} (hs : ∀ k, Measurable (Function.uncurry (step k)))
    (N call : ℕ) : Measurable (Function.uncurry (freshRun cost step N call)) := by
  induction N generalizing call with
  | zero => exact measurable_fst
  | succ N ih =>
      have hhead : Measurable (fun w : A × ((ℕ → S) × (ℕ → Ω)) =>
          ((w.2.1 0), w.2.2)) := by fun_prop
      have ht : Measurable (fun w : A × ((ℕ → S) × (ℕ → Ω)) =>
          ((fun j => w.2.1 (j + 1)), fun j => w.2.2 (cost call (w.2.1 0) + j))) :=
        (by fun_prop : Measurable (fun w : A × ((ℕ → S) × (ℕ → Ω)) => fun j => w.2.1 (j + 1))).prodMk
          ((measurable_seed_shift (hc call)).comp hhead)
      exact (ih (call + 1)).comp (((hs call).comp (measurable_fst.prodMk hhead)).prodMk ht)

lemma idealRun_measurable {step : ℕ → A → S × (ℕ → Ω) → A}
    (hs : ∀ k, Measurable (Function.uncurry (step k))) (N call : ℕ) :
    Measurable (Function.uncurry (idealRun step N call)) := by
  induction N generalizing call with
  | zero => exact measurable_fst
  | succ N ih => exact (ih (call + 1)).comp (((hs call).comp (measurable_fst.prodMk
      ((measurable_pi_apply 0).comp measurable_snd))).prodMk (by fun_prop))

lemma freshRun_lintegral (Q : Measure S) (p : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure p]
    {cost : ℕ → S → ℕ} (hc : ∀ k, Measurable (cost k))
    {step : ℕ → A → S × (ℕ → Ω) → A} (hs : ∀ k, Measurable (Function.uncurry (step k)))
    (hdep : ∀ call state s ξ ζ, (∀ j, j < cost call s → ξ j = ζ j) →
      step call state (s, ξ) = step call state (s, ζ))
    (G : A → ℝ≥0∞) (hG : Measurable G) (N call : ℕ) (state : A) :
    (∫⁻ w, G (freshRun cost step N call state w)
      ∂((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => p))) =
      ∫⁻ ξ, G (idealRun step N call state ξ)
        ∂Measure.infinitePi (fun _ : ℕ => Q.prod (Measure.infinitePi fun _ : ℕ => p)) := by
  induction N generalizing call state with
  | zero => simp [freshRun, idealRun]
  | succ N ih =>
      let F : A × ((ℕ → S) × (ℕ → Ω)) → ℝ≥0∞ :=
        fun w => G (freshRun cost step N (call + 1) w.1 w.2)
      have hF : Measurable F := hG.comp (freshRun_measurable hc hs N (call + 1))
      have hstep : Measurable (step call state) := (hs call).comp measurable_prodMk_left
      have hh := fresh_step_lintegral Q p (hc call) (step call state) hstep (hdep call state) F hF
      change (∫⁻ (w : (ℕ → S) × (ℕ → Ω)), F (step call state (w.1 0, w.2),
        ((fun j => w.1 (j + 1)), fun j => w.2 (cost call (w.1 0) + j))) ∂_) = _
      rw [hh]
      simp only [F, ih]
      let R := Q.prod (Measure.infinitePi fun _ : ℕ => p)
      let G' : (S × (ℕ → Ω)) × (ℕ → S × (ℕ → Ω)) → ℝ≥0∞ :=
        fun w => G (idealRun step N (call + 1) (step call state w.1) w.2)
      have hG' : Measurable G' := hG.comp
        ((idealRun_measurable hs N (call + 1)).comp
          ((hstep.comp measurable_fst).prodMk measurable_snd))
      have hsplit := (HeavyTailedProductProcess.head_tail_preserving R).lintegral_comp hG'
      rw [lintegral_prod G' hG'.aemeasurable] at hsplit
      exact hsplit.symm

lemma freshRun_map_eq (Q : Measure S) (p : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure p]
    {cost : ℕ → S → ℕ} (hc : ∀ k, Measurable (cost k))
    {step : ℕ → A → S × (ℕ → Ω) → A} (hs : ∀ k, Measurable (Function.uncurry (step k)))
    (hdep : ∀ call state s ξ ζ, (∀ j, j < cost call s → ξ j = ζ j) →
      step call state (s, ξ) = step call state (s, ζ))
    (N call : ℕ) (state : A) :
    ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => p)).map
        (freshRun cost step N call state) =
      (Measure.infinitePi fun _ : ℕ => Q.prod (Measure.infinitePi fun _ : ℕ => p)).map
        (idealRun step N call state) := by
  apply Measure.ext_of_lintegral
  intro G hG
  have hactual : Measurable (freshRun cost step N call state) :=
    (freshRun_measurable hc hs N call).comp measurable_prodMk_left
  have hideal : Measurable (idealRun step N call state) :=
    (idealRun_measurable hs N call).comp measurable_prodMk_left
  rw [lintegral_map hG hactual, lintegral_map hG hideal]
  exact freshRun_lintegral Q p hc hs hdep G hG N call state

lemma freshRun_identDistrib (Q : Measure S) (p : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure p]
    {cost : ℕ → S → ℕ} (hc : ∀ k, Measurable (cost k))
    {step : ℕ → A → S × (ℕ → Ω) → A} (hs : ∀ k, Measurable (Function.uncurry (step k)))
    (hdep : ∀ call state s ξ ζ, (∀ j, j < cost call s → ξ j = ζ j) →
      step call state (s, ξ) = step call state (s, ζ))
    (N call : ℕ) (state : A) :
    ProbabilityTheory.IdentDistrib (freshRun cost step N call state) (idealRun step N call state)
      ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => p))
      (Measure.infinitePi fun _ : ℕ => Q.prod (Measure.infinitePi fun _ : ℕ => p)) :=
  ⟨((freshRun_measurable hc hs N call).comp measurable_prodMk_left).aemeasurable,
    ((idealRun_measurable hs N call).comp measurable_prodMk_left).aemeasurable,
    freshRun_map_eq Q p hc hs hdep N call state⟩


end Composition

end LongTails.Proofs.StochasticEnvelopeFreshness
