import LongTails.Proofs.ClippedExtragradientIteration

open MeasureTheory

namespace LongTails.Proofs.GapNoiseIteration

variable {S Ω : Type*}

noncomputable def accumulatedEnergy (advance : S → Ω → S) (energy loss : S → ℝ) (κ : ℝ) :
    (steps : ℕ) → S → (Fin steps → Ω) → ℝ
  | 0, state, _ => energy state
  | steps + 1, state, ξ => κ * loss state +
      accumulatedEnergy advance energy loss κ steps (advance state (ξ 0)) (fun i => ξ i.succ)

lemma accumulatedEnergy_bounds {advance : S → Ω → S} {energy loss : S → ℝ} {κ M L : ℝ}
    {Inv : S → Prop} (hinv : ∀ s, Inv s → ∀ ω, Inv (advance s ω)) (hκ : 0 ≤ κ)
    (he : ∀ s, Inv s → 0 ≤ energy s ∧ energy s ≤ M)
    (hl : ∀ s, Inv s → 0 ≤ loss s ∧ loss s ≤ L)
    (steps : ℕ) (state : S) (hs : Inv state) (ξ : Fin steps → Ω) :
    0 ≤ accumulatedEnergy advance energy loss κ steps state ξ ∧
      accumulatedEnergy advance energy loss κ steps state ξ ≤ M + steps * κ * L := by
  induction steps generalizing state with
  | zero => simpa only [accumulatedEnergy, Nat.cast_zero, zero_mul, add_zero] using he state hs
  | succ steps ih =>
    have h := ih (advance state (ξ 0)) (hinv state hs (ξ 0)) (fun i => ξ i.succ)
    have hn := mul_nonneg hκ (hl state hs).1
    have hb := mul_le_mul_of_nonneg_left (hl state hs).2 hκ
    simp only [accumulatedEnergy, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith [h.1, h.2]

lemma accumulatedEnergy_decomposition (advance : S → Ω → S) (energy loss : S → ℝ) (κ : ℝ)
    (steps : ℕ) (state : S) (ξ : Fin steps → Ω) :
    accumulatedEnergy advance energy loss κ steps state ξ =
      energy (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance steps state ξ) +
        κ * accumulatedEnergy advance (fun _ => 0) loss 1 steps state ξ := by
  induction steps generalizing state with
  | zero => simp [accumulatedEnergy, OracleTemplate.ContinuizedSimilarQuasar.iterateSamples]
  | succ steps ih =>
    simp only [accumulatedEnergy, OracleTemplate.ContinuizedSimilarQuasar.iterateSamples]
    rw [ih]
    ring

lemma terminal_energy_le_accumulatedEnergy {advance : S → Ω → S} {energy loss : S → ℝ}
    {κ : ℝ} (hκ : 0 ≤ κ) (hl : ∀ s, 0 ≤ loss s) (steps : ℕ) (state : S) (ξ : Fin steps → Ω) :
    energy (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance steps state ξ) ≤
      accumulatedEnergy advance energy loss κ steps state ξ := by
  induction steps generalizing state with
  | zero => exact le_rfl
  | succ steps ih =>
    have h := ih (advance state (ξ 0)) (fun i => ξ i.succ)
    have hn := mul_nonneg hκ (hl state)
    simpa only [accumulatedEnergy, OracleTemplate.ContinuizedSimilarQuasar.iterateSamples] using
      h.trans (le_add_of_nonneg_left hn)

noncomputable def pointTrace {V : Type*} (advance : S → Ω → S) (point : S → V) :
    (steps : ℕ) → S → (Fin steps → Ω) → (Fin steps → V)
  | 0, _, _ => Fin.elim0
  | steps + 1, state, ξ => Fin.cons (point state)
      (pointTrace advance point steps (advance state (ξ 0)) (fun i => ξ i.succ))

lemma pointTrace_mem {V : Type*} {X : Set V} (advance : S → Ω → S) (point : S → V)
    (hp : ∀ state, point state ∈ X) (steps : ℕ) (state : S) (ξ : Fin steps → Ω) :
    ∀ i, pointTrace advance point steps state ξ i ∈ X := by
  induction steps generalizing state with
  | zero => exact fun i => Fin.elim0 i
  | succ steps ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hp state
    · exact ih (advance state (ξ 0)) (fun k => ξ k.succ) j

lemma iterate_eq_of_pointTrace {advance reference : S → Ω → S} {good : S → Ω → Prop}
    (hstep : ∀ s ω, good s ω → reference s ω = advance s ω)
    (steps : ℕ) (state : S) (ξ : Fin steps → Ω)
    (hgood : ∀ i, good (pointTrace reference id steps state ξ i) (ξ i)) :
    OracleTemplate.ContinuizedSimilarQuasar.iterateSamples reference steps state ξ =
      OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance steps state ξ := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih =>
    have hfirst : reference state (ξ 0) = advance state (ξ 0) :=
      hstep state (ξ 0) (by simpa only [pointTrace, Fin.cons_zero, id_eq] using hgood 0)
    have htail : ∀ i, good (pointTrace reference id steps (reference state (ξ 0))
        (fun j => ξ j.succ) i) (ξ i.succ) := by
      intro i
      simpa only [pointTrace, Fin.cons_succ] using hgood i.succ
    simp only [OracleTemplate.ContinuizedSimilarQuasar.iterateSamples]
    rw [ih _ _ htail, hfirst]

lemma iterate_active_input {advance : S → Ω → S} {active : S → Prop}
    (ha : ∀ s ω, active (advance s ω) → active s) (steps : ℕ) (state : S) (ξ : Fin steps → Ω)
    (hfinal : active (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance steps state ξ)) :
    active state := by
  induction steps generalizing state with
  | zero => exact hfinal
  | succ steps ih => exact ha state (ξ 0) (ih _ _ hfinal)

lemma active_total_trace {V : Type*} [AddCommGroup V] {advance : S → Ω → S}
    {point total : S → V} {active : S → Prop}
    (ha : ∀ s ω, active (advance s ω) → active s)
    (ht : ∀ s ω, active (advance s ω) → total (advance s ω) = total s + point s)
    (steps : ℕ) (state : S) (ξ : Fin steps → Ω)
    (hfinal : active (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance steps state ξ)) :
    total (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance steps state ξ) =
      total state + ∑ i, pointTrace advance point steps state ξ i := by
  induction steps generalizing state with
  | zero => simp [OracleTemplate.ContinuizedSimilarQuasar.iterateSamples]
  | succ steps ih =>
    have hnext := iterate_active_input ha steps (advance state (ξ 0)) (fun i => ξ i.succ) hfinal
    change total (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance steps
      (advance state (ξ 0)) (fun i => ξ i.succ)) = _
    rw [ih _ _ hfinal, ht state (ξ 0) hnext]
    simp only [pointTrace, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    abel

lemma active_loss_trace {V : Type*} {advance : S → Ω → S} {point : S → V}
    {loss : S → ℝ} {value : V → ℝ} {active : S → Prop}
    (ha : ∀ s ω, active (advance s ω) → active s)
    (hl : ∀ s ω, active (advance s ω) → loss s = value (point s))
    (steps : ℕ) (state : S) (ξ : Fin steps → Ω)
    (hfinal : active (OracleTemplate.ContinuizedSimilarQuasar.iterateSamples advance steps state ξ)) :
    accumulatedEnergy advance (fun _ => 0) loss 1 steps state ξ =
      ∑ i, value (pointTrace advance point steps state ξ i) := by
  induction steps generalizing state with
  | zero => simp [accumulatedEnergy]
  | succ steps ih =>
    have hnext := iterate_active_input ha steps (advance state (ξ 0)) (fun i => ξ i.succ) hfinal
    simp only [accumulatedEnergy, one_mul, pointTrace, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [hl state (ξ 0) hnext, ih _ _ hfinal]

def GoodSamples (advance : S → Ω → S) (good : S → Ω → Prop) :
    (steps : ℕ) → S → (Fin steps → Ω) → Prop
  | 0, _, _ => True
  | steps + 1, state, ξ => good state (ξ 0) ∧
      GoodSamples advance good steps (advance state (ξ 0)) (fun i => ξ i.succ)

lemma goodSamples_iff (advance : S → Ω → S) (good : S → Ω → Prop)
    (steps : ℕ) (state : S) (ξ : Fin steps → Ω) :
    GoodSamples advance good steps state ξ ↔ ∀ i, good (pointTrace advance id steps state ξ i) (ξ i) := by
  induction steps generalizing state with
  | zero => simp [GoodSamples]
  | succ steps ih => simp only [GoodSamples, ih, Fin.forall_fin_succ, pointTrace, Fin.cons_zero, Fin.cons_succ, id_eq]

variable [MeasurableSpace S] [MeasurableSpace Ω]

lemma measurableSet_goodSamples {advance : S → Ω → S} {good : S → Ω → Prop}
    (ha : Measurable (Function.uncurry advance)) (hg : MeasurableSet {w : S × Ω | good w.1 w.2})
    (steps : ℕ) : MeasurableSet {w : S × (Fin steps → Ω) | GoodSamples advance good steps w.1 w.2} := by
  induction steps with
  | zero => simp [GoodSamples]
  | succ steps ih =>
    have hfirst : Measurable (fun w : S × (Fin (steps + 1) → Ω) => (w.1, w.2 0)) := by fun_prop
    have htail : Measurable (fun w : S × (Fin (steps + 1) → Ω) =>
        (advance w.1 (w.2 0), fun i : Fin steps => w.2 i.succ)) :=
      (ha.comp hfirst).prodMk (by fun_prop)
    exact (hg.preimage hfirst).inter (ih.preimage htail)

lemma goodSamples_failure_probability {advance : S → Ω → S} {good : S → Ω → Prop}
    (ha : Measurable (Function.uncurry advance)) (hg : MeasurableSet {w : S × Ω | good w.1 w.2})
    (P : Measure Ω) [IsProbabilityMeasure P] {Inv : S → Prop} {δ : ENNReal}
    (hinv : ∀ s, Inv s → ∀ ω, Inv (advance s ω))
    (hfailure : ∀ s, Inv s → P {ω | ¬ good s ω} ≤ δ)
    (steps : ℕ) (state : S) (hs : Inv state) :
    (Measure.pi fun _ : Fin steps => P) {ξ | ¬ GoodSamples advance good steps state ξ} ≤ steps * δ := by
  induction steps generalizing state with
  | zero => simp [GoodSamples]
  | succ steps ih =>
    let first : Set (Ω × (Fin steps → Ω)) := {w | ¬ good state w.1}
    let tail : Set (Ω × (Fin steps → Ω)) :=
      {w | ¬ GoodSamples advance good steps (advance state w.1) w.2}
    have hf : MeasurableSet {ω | ¬ good state ω} :=
      (hg.preimage measurable_prodMk_left).compl
    have hm : Measurable (fun w : Ω × (Fin steps → Ω) => (advance state w.1, w.2)) :=
      (ha.comp ((measurable_const (a := state)).prodMk measurable_fst)).prodMk measurable_snd
    have ht : MeasurableSet tail := ((measurableSet_goodSamples ha hg steps).preimage hm).compl
    have hfirst : (P.prod (Measure.pi fun _ : Fin steps => P)) first ≤ δ := by
      rw [show first = Prod.fst ⁻¹' {ω | ¬ good state ω} from rfl,
        measurePreserving_fst.measure_preimage hf.nullMeasurableSet]
      exact hfailure state hs
    have htail : (P.prod (Measure.pi fun _ : Fin steps => P)) tail ≤ steps * δ := by
      rw [Measure.prod_apply ht]
      calc
        _ ≤ ∫⁻ _ : Ω, (steps : ENNReal) * δ ∂P := lintegral_mono fun ω =>
          ih (advance state ω) (hinv state hs ω)
        _ = _ := by simp
    have hsplit := (measurePreserving_piFinSuccAbove (fun _ : Fin (steps + 1) => P) 0).symm
    have hsplit' : MeasurePreserving (fun w : Ω × (Fin steps → Ω) => Fin.cons w.1 w.2)
        (P.prod (Measure.pi fun _ : Fin steps => P)) (Measure.pi fun _ : Fin (steps + 1) => P) := by
      simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using hsplit
    have hbad : MeasurableSet {ξ : Fin (steps + 1) → Ω | ¬ GoodSamples advance good (steps + 1) state ξ} :=
      ((measurableSet_goodSamples ha hg (steps + 1)).preimage measurable_prodMk_left).compl
    rw [← hsplit'.measure_preimage hbad.nullMeasurableSet]
    have he : (fun w : Ω × (Fin steps → Ω) => Fin.cons w.1 w.2) ⁻¹' {ξ : Fin (steps + 1) → Ω | ¬ GoodSamples advance good (steps + 1) state ξ} =
        first ∪ tail := by
      ext w
      simp only [Set.mem_preimage, GoodSamples, Fin.cons_zero, Fin.cons_succ,
        Set.mem_union, first, tail, Set.mem_ofPred_eq, not_and_or]
    rw [he]
    calc
      _ ≤ (P.prod (Measure.pi fun _ : Fin steps => P)) first +
          (P.prod (Measure.pi fun _ : Fin steps => P)) tail := measure_union_le _ _
      _ ≤ δ + steps * δ := add_le_add hfirst htail
      _ = (steps + 1 : ℕ) * δ := by push_cast; ring

lemma initialized_goodSamples_failure_probability {W : Type*} [MeasurableSpace W]
    {advance : S → Ω → S} {good : S → Ω → Prop} {initial : W → S} {initialGood : W → Prop}
    (ha : Measurable (Function.uncurry advance)) (hg : MeasurableSet {w : S × Ω | good w.1 w.2})
    (hi : Measurable initial) (hgi : MeasurableSet {w | initialGood w})
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : Measure W) [IsProbabilityMeasure Q]
    {Inv : S → Prop} {δ δ₀ : ENNReal}
    (hinv : ∀ s, Inv s → ∀ ω, Inv (advance s ω)) (hinit : ∀ w, Inv (initial w))
    (hfailure : ∀ s, Inv s → P {ω | ¬ good s ω} ≤ δ)
    (hinitial : Q {w | ¬ initialGood w} ≤ δ₀) (steps : ℕ) :
    (Q.prod (Measure.pi fun _ : Fin steps => P))
      {w | ¬ (initialGood w.1 ∧ GoodSamples advance good steps (initial w.1) w.2)} ≤ δ₀ + steps * δ := by
  let first : Set (W × (Fin steps → Ω)) := {w | ¬ initialGood w.1}
  let tail : Set (W × (Fin steps → Ω)) := {w | ¬ GoodSamples advance good steps (initial w.1) w.2}
  have hfirst : (Q.prod (Measure.pi fun _ : Fin steps => P)) first ≤ δ₀ := by
    have hf : MeasurableSet {w | ¬ initialGood w} := hgi.compl
    rw [show first = Prod.fst ⁻¹' {w | ¬ initialGood w} from rfl,
      measurePreserving_fst.measure_preimage hf.nullMeasurableSet]
    exact hinitial
  have ht : MeasurableSet tail := ((measurableSet_goodSamples ha hg steps).preimage
    ((hi.comp measurable_fst).prodMk measurable_snd)).compl
  have htail : (Q.prod (Measure.pi fun _ : Fin steps => P)) tail ≤ steps * δ := by
    rw [Measure.prod_apply ht]
    calc
      _ ≤ ∫⁻ _ : W, (steps : ENNReal) * δ ∂Q := lintegral_mono fun w =>
        goodSamples_failure_probability ha hg P hinv hfailure steps (initial w) (hinit w)
      _ = _ := by simp
  have he : {w : W × (Fin steps → Ω) | ¬ (initialGood w.1 ∧
      GoodSamples advance good steps (initial w.1) w.2)} = first ∪ tail := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_union, first, tail, not_and_or]
  rw [he]
  exact (measure_union_le first tail).trans (add_le_add hfirst htail)

lemma measurable_accumulatedEnergy {advance : S → Ω → S} {energy loss : S → ℝ} (κ : ℝ)
    (ha : Measurable (Function.uncurry advance)) (he : Measurable energy) (hl : Measurable loss)
    (steps : ℕ) :
    Measurable (fun w : S × (Fin steps → Ω) => accumulatedEnergy advance energy loss κ steps w.1 w.2) := by
  induction steps with
  | zero => exact he.comp measurable_fst
  | succ steps ih =>
    have ht : Measurable (fun w : S × (Fin (steps + 1) → Ω) => fun i : Fin steps => w.2 i.succ) := by fun_prop
    exact ((hl.comp measurable_fst).const_mul κ).add
      (ih.comp ((ha.comp (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).prodMk ht))

lemma accumulatedEnergy_integral {advance : S → Ω → S} {energy loss : S → ℝ}
    (ha : Measurable (Function.uncurry advance)) (he : Measurable energy) (hl : Measurable loss)
    (P : Measure Ω) [IsProbabilityMeasure P] {κ M L β : ℝ} {Inv : S → Prop}
    (hinv : ∀ s, Inv s → ∀ ω, Inv (advance s ω)) (hκ : 0 ≤ κ)
    (henergy : ∀ s, Inv s → 0 ≤ energy s ∧ energy s ≤ M)
    (hloss : ∀ s, Inv s → 0 ≤ loss s ∧ loss s ≤ L)
    (hstep : ∀ s, Inv s → (∫ ω, energy (advance s ω) ∂P) + κ * loss s ≤ energy s + β)
    (steps : ℕ) (state : S) (hs : Inv state) :
    (∫ ξ : Fin steps → Ω, accumulatedEnergy advance energy loss κ steps state ξ
      ∂Measure.pi (fun _ : Fin steps => P)) ≤ energy state + steps * β := by
  induction steps generalizing state with
  | zero => simp [accumulatedEnergy]
  | succ steps ih =>
    let f : Ω × (Fin steps → Ω) → ℝ := fun w =>
      accumulatedEnergy advance energy loss κ steps (advance state w.1) w.2
    have hm : Measurable f := (measurable_accumulatedEnergy κ ha he hl steps).comp
      ((ha.comp ((measurable_const (a := state)).prodMk measurable_fst)).prodMk measurable_snd)
    have hi : Integrable f (P.prod (Measure.pi fun _ : Fin steps => P)) := by
      apply Integrable.of_bound hm.aestronglyMeasurable (M + steps * κ * L)
      apply Filter.Eventually.of_forall
      intro w
      have hb := accumulatedEnergy_bounds hinv hκ henergy hloss steps
        (advance state w.1) (hinv state hs w.1) w.2
      change ‖accumulatedEnergy advance energy loss κ steps (advance state w.1) w.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2
    have hei : Integrable (fun ω => energy (advance state ω)) P := by
      apply Integrable.of_bound ((he.comp ha).comp measurable_prodMk_left).aestronglyMeasurable M
      apply Filter.Eventually.of_forall
      intro ω
      have hb := henergy (advance state ω) (hinv state hs ω)
      simpa only [Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
    have hcond (ω : Ω) : (∫ ξ : Fin steps → Ω, f (ω, ξ)
        ∂Measure.pi (fun _ : Fin steps => P)) ≤ energy (advance state ω) + steps * β :=
      ih _ (hinv state hs ω)
    have hh := integral_mono hi.integral_prod_left (hei.add (integrable_const _)) hcond
    change (∫ ω, ∫ ξ, f (ω, ξ) ∂Measure.pi (fun _ : Fin steps => P) ∂P) ≤
      (∫ ω, energy (advance state ω) + steps * β ∂P) at hh
    rw [integral_add hei (integrable_const _)] at hh
    simp only [integral_const, probReal_univ, one_smul] at hh
    have hprod : (∫ w, κ * loss state + f w ∂P.prod (Measure.pi fun _ : Fin steps => P)) ≤
        energy state + (steps + 1) * β := by
      rw [integral_add (integrable_const _) hi, integral_prod f hi]
      simp only [integral_const, probReal_univ, one_smul]
      linarith [hstep state hs]
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (steps + 1) => P) 0).symm
    have heq : (∫ ξ : Fin (steps + 1) → Ω,
        accumulatedEnergy advance energy loss κ (steps + 1) state ξ
        ∂Measure.pi (fun _ : Fin (steps + 1) => P)) =
        ∫ w, κ * loss state + f w ∂P.prod (Measure.pi fun _ : Fin steps => P) := by
      rw [← hp.integral_comp']
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, accumulatedEnergy,
        Fin.cons_zero, Fin.cons_succ, cast_eq]
      rfl
    rw [heq]
    simpa only [Nat.cast_add, Nat.cast_one] using hprod

lemma initialized_accumulatedEnergy_integrable {W : Type*} [MeasurableSpace W]
    {advance : S → Ω → S} {energy loss : S → ℝ} {initial : W → S}
    (ha : Measurable (Function.uncurry advance)) (he : Measurable energy) (hl : Measurable loss)
    (hi : Measurable initial) (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure W) [IsProbabilityMeasure Q] {κ M L : ℝ} {Inv : S → Prop}
    (hinv : ∀ s, Inv s → ∀ ω, Inv (advance s ω)) (hκ : 0 ≤ κ)
    (henergy : ∀ s, Inv s → 0 ≤ energy s ∧ energy s ≤ M)
    (hloss : ∀ s, Inv s → 0 ≤ loss s ∧ loss s ≤ L)
    (hinit : ∀ w, Inv (initial w)) (steps : ℕ) :
    Integrable (fun w : W × (Fin steps → Ω) => accumulatedEnergy advance energy loss κ steps (initial w.1) w.2)
      (Q.prod (Measure.pi (fun _ : Fin steps => P))) := by
  have hm := (measurable_accumulatedEnergy κ ha he hl steps).comp
    ((hi.comp measurable_fst).prodMk measurable_snd)
  apply Integrable.of_bound hm.aestronglyMeasurable (M + steps * κ * L)
  apply Filter.Eventually.of_forall
  intro w
  have hb := accumulatedEnergy_bounds hinv hκ henergy hloss steps (initial w.1) (hinit w.1) w.2
  change ‖accumulatedEnergy advance energy loss κ steps (initial w.1) w.2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

lemma initialized_accumulatedEnergy_integral {W : Type*} [MeasurableSpace W]
    {advance : S → Ω → S} {energy loss : S → ℝ} {initial : W → S}
    (ha : Measurable (Function.uncurry advance)) (he : Measurable energy) (hl : Measurable loss)
    (hi : Measurable initial) (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure W) [IsProbabilityMeasure Q] {κ M L β A : ℝ} {Inv : S → Prop}
    (hinv : ∀ s, Inv s → ∀ ω, Inv (advance s ω)) (hκ : 0 ≤ κ)
    (henergy : ∀ s, Inv s → 0 ≤ energy s ∧ energy s ≤ M)
    (hloss : ∀ s, Inv s → 0 ≤ loss s ∧ loss s ≤ L)
    (hstep : ∀ s, Inv s → (∫ ω, energy (advance s ω) ∂P) + κ * loss s ≤ energy s + β)
    (hinit : ∀ w, Inv (initial w)) (hstart : (∫ w, energy (initial w) ∂Q) ≤ A) (steps : ℕ) :
    (∫ w : W × (Fin steps → Ω), accumulatedEnergy advance energy loss κ steps (initial w.1) w.2
      ∂Q.prod (Measure.pi (fun _ : Fin steps => P))) ≤ A + steps * β := by
  let f : W × (Fin steps → Ω) → ℝ := fun w =>
    accumulatedEnergy advance energy loss κ steps (initial w.1) w.2
  have hj : Integrable f (Q.prod (Measure.pi fun _ : Fin steps => P)) :=
    initialized_accumulatedEnergy_integrable ha he hl hi P Q hinv hκ henergy hloss hinit steps
  have hei : Integrable (fun w => energy (initial w)) Q := by
    apply Integrable.of_bound (he.comp hi).aestronglyMeasurable M
    apply Filter.Eventually.of_forall
    intro w
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg (henergy _ (hinit w)).1] using (henergy _ (hinit w)).2
  have hp (w : W) : (∫ ξ, f (w, ξ) ∂Measure.pi (fun _ : Fin steps => P)) ≤
      energy (initial w) + steps * β :=
    accumulatedEnergy_integral ha he hl P hinv hκ henergy hloss hstep steps (initial w) (hinit w)
  have hh := integral_mono hj.integral_prod_left (hei.add (integrable_const _)) hp
  change (∫ w, ∫ ξ, f (w, ξ) ∂Measure.pi (fun _ : Fin steps => P) ∂Q) ≤
    (∫ w, energy (initial w) + steps * β ∂Q) at hh
  rw [integral_add hei (integrable_const _)] at hh
  simp only [integral_const, probReal_univ, one_smul] at hh
  change (∫ w, f w ∂Q.prod (Measure.pi fun _ : Fin steps => P)) ≤ _
  rw [integral_prod _ hj]
  linarith

end LongTails.Proofs.GapNoiseIteration
