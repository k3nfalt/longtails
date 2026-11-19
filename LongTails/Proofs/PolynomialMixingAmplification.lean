import LongTails.Proofs.PolynomialMixingSelectionLaw

open MeasureTheory

namespace LongTails.Proofs.PolynomialMixingAmplification

open LongTails.Setups.PolynomialMixingSubgradient LongTails.Algorithms.PolynomialMixingSelection
open LongTails.Proofs.PolynomialMixingTraining LongTails.Proofs.PolynomialMixingAccuracy
open LongTails.Proofs.PolynomialMixingExecution LongTails.Proofs.PolynomialMixingSelectionLaw
open LongTails.Proofs.PolynomialMixingBlocks OracleTemplate

lemma real_preimage {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} {T : X → Y} (h : MeasurePreserving T μ ν) {B : Set Y} (hB : MeasurableSet B) :
    μ.real (T ⁻¹' B) = ν.real B := congrArg ENNReal.toReal (h.measure_preimage hB.nullMeasurableSet)

lemma real_le_of_enn {X : Type*} [MeasurableSpace X] {μ : Measure X} {B : Set X} {a : ℝ}
    (ha : 0 ≤ a) (h : μ B ≤ ENNReal.ofReal a) : μ.real B ≤ a := by
  simpa only [measureReal_def, ENNReal.toReal_ofReal ha] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

variable {q : Params} {g : Point q → ℝ → Space q} {f : Space q → ℝ}

noncomputable def estimateBad (g : Point q → ℝ → Space q) (f : Space q → ℝ) (c : Schedule) :
    Set (Fin (c.trials+1) → Path) :=
  {w | q.ε / 4 < |(trial g c w).2 - (f (trial g c w).1.val - f 0)|}

lemma measurable_estimateBad (hg : Measurable (Function.uncurry g)) (hf : Measurable fun x : Point q => f x.val)
    (c : Schedule) : MeasurableSet (estimateBad g f c) :=
  measurableSet_lt measurable_const (continuous_abs.measurable.comp ((measurable_trial hg c).snd.sub
    ((hf.comp (measurable_trial hg c).fst).sub_const (f 0))))

lemma section_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (Q : Measure X) (V : Measure Y)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure V] {A : Set (X × Y)} (hA : MeasurableSet A)
    {b : ℝ} (hb : ∀ x, V.real (Prod.mk x ⁻¹' A) ≤ b) : (Q.prod V).real A ≤ b := by
  rw [prod_section_real Q V hA]
  calc
    _ ≤ ∫ _ : X, b ∂Q := integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => measureReal_nonneg)
      (integrable_const b) (Filter.Eventually.of_forall hb)
    _ = b := by simp

lemma conditional_pilot {X Y : Type} [MeasurableSpace Y] (Q : Measure Y) [IsProbabilityMeasure Q]
    (n : ℕ) (train : Y → X) (v : X → Y → ℝ) (m : X → ℝ) (B : ℝ)
    (hm : ∀ x, Measurable (v x))
    (hv : ∀ x, Q.real {w | B/6 < ‖v x w - m x‖} ≤ 1 / 16) :
    let A := {w : Fin (n+1) → Y | B/2 < ‖RobustGradient.pilotCenter B (fun j : Fin n => v (train (w 0)) (w j.succ)) - m (train (w 0))‖}
    MeasurableSet A → (Measure.pi fun _ : Fin (n+1) => Q).real A ≤ (1 / 2 : ℝ)^n := by
  intro A hA
  let V := Measure.pi (fun _ : Fin n => Q)
  let pack := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Y) 0).symm
  have hpack := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => Q) 0).symm
  rw [← real_preimage hpack hA]
  apply section_bound Q V (pack.measurable hA)
  intro w
  have hprob := RobustGradient.pilotCenter_failure_probability (P := Q) (hm (train w))
    (m (train w)) B (hv (train w)) n
  have heq : Prod.mk w ⁻¹' (pack ⁻¹' A) = {z : Fin n → Y | B/2 <
      ‖RobustGradient.pilotCenter B (fun j => v (train w) (z j)) - m (train w)‖} := by
    ext z
    simp [A, pack, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv]
  rw [heq]
  exact real_le_of_enn (by positivity) hprob

lemma estimate_tail (Q : Measure Path) [IsProbabilityMeasure Q] (c : Schedule)
    (hg : Measurable (Function.uncurry g)) (hf : Measurable fun x : Point q => f x.val)
    (hv : ∀ x, Q.real {w | q.ε/12 < |score g x c.samples w - (f x.val - f 0)|} ≤ 1 / 16) :
    (Measure.pi fun _ : Fin (c.trials+1) => Q).real (estimateBad g f c) ≤ (1 / 2 : ℝ)^c.trials := by
  have hV (x : Point q) : Measurable (score g x c.samples) := measurable_score_at (q := q) (g := g) hg c.samples x
  have h := conditional_pilot Q c.trials (average g c.samples) (fun x => score g x c.samples)
    (fun x => f x.val - f 0) (q.ε / 2) hV (fun x => by
      simpa only [div_div, show (2 : ℝ)*6 = 12 by norm_num, Real.norm_eq_abs] using hv x)
  simp only [div_div, show (2 : ℝ)*2 = 4 by norm_num, Real.norm_eq_abs] at h
  exact h (measurable_estimateBad hg hf c)

lemma amplified (Q : Measure Path) [IsProbabilityMeasure Q] (c : Schedule) (u : Point q)
    (hg : Measurable (Function.uncurry g)) (hf : Measurable fun x : Point q => f x.val)
    (hk : 0 < c.trials)
    (ha : Q.real {w | q.ε/2 < f (average g c.samples w).val - f u.val} ≤ 1/16)
    (hv : ∀ x, Q.real {w | q.ε/12 < |score g x c.samples w - (f x.val - f 0)|} ≤ 1 / 16) :
    (Measure.pi fun _ : Fin c.trials => Measure.pi fun _ : Fin (c.trials+1) => Q).real
      {w | q.ε < f (selected g c w).val - f u.val} ≤
      ((c.trials : ℝ) + 1) * (1/2 : ℝ)^c.trials := by
  classical
  let T := Measure.pi (fun _ : Fin (c.trials+1) => Q)
  let P := Measure.pi (fun _ : Fin c.trials => T)
  let A := {w : Path | q.ε/2 < f (average g c.samples w).val - f u.val}
  let bad := (fun w : Fin (c.trials+1) → Path => w 0) ⁻¹' A
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    ((hf.comp (measurable_average hg c.samples)).sub_const _)
  have hbad : T.real bad ≤ 1/16 :=
    (real_preimage (measurePreserving_eval (fun _ : Fin (c.trials+1) => Q) 0) hA).le.trans ha
  let allBad := {w : Fin c.trials → Fin (c.trials+1) → Path | ∀ i, w i ∈ bad}
  have hall : P.real allBad ≤ (1/2 : ℝ)^c.trials := by
    have hM := RobustGradient.majority_failure_probability ((measurable_pi_apply 0) hA) hbad c.trials
    apply (measureReal_mono ?_).trans (real_le_of_enn (by positivity) hM)
    intro w hw
    change c.trials ≤ 2 * (Finset.univ.filter (fun i => w i ∈ bad)).card
    have he : Finset.univ.filter (fun i => w i ∈ bad) = Finset.univ :=
      Finset.filter_true_of_mem (fun i _ => hw i)
    rw [he, Finset.card_univ, Fintype.card_fin]; omega
  let E := fun i : Fin c.trials => (fun w : Fin c.trials → Fin (c.trials+1) → Path => w i) ⁻¹' estimateBad g f c
  have hE (i : Fin c.trials) : P.real (E i) ≤ (1/2 : ℝ)^c.trials :=
    (real_preimage (measurePreserving_eval (fun _ : Fin c.trials => T) i) (measurable_estimateBad hg hf c)).le.trans
      (estimate_tail Q c hg hf hv)
  have hU := (measureReal_iUnion_fintype_le (μ := P) E).trans
    (Finset.sum_le_sum (fun i _ => hE i))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hU
  apply (measureReal_mono (show _ ⊆ allBad ∪ ⋃ i, E i from ?_)).trans
    ((measureReal_union_le _ _).trans (by linarith))
  intro w hw
  by_cases ha' : w ∈ allBad
  · exact Or.inl ha'
  right
  by_contra hn
  obtain ⟨j, hj⟩ := Classical.not_forall.mp ha'
  change ¬ q.ε/2 < f (average g c.samples ((w j) 0)).val - f u.val at hj
  have he (i : Fin c.trials) : |(trial g c (w i)).2 - (f (trial g c (w i)).1.val - f 0)| ≤ q.ε/4 :=
    le_of_not_gt (fun h' => hn (Set.mem_iUnion.mpr ⟨i, h'⟩))
  obtain ⟨i, hi, hmin⟩ := selected_index (origin q) (fun i => trial g c (w i)) hk
  change q.ε < f (selected g c w).val - f u.val at hw
  change selected g c w = (trial g c (w i)).1 at hi
  rw [hi] at hw
  have hja : f (trial g c (w j)).1.val - f u.val ≤ q.ε/2 := le_of_not_gt hj
  linarith [(abs_le.mp (he i)).1, (abs_le.mp (he j)).2, hmin j]

end LongTails.Proofs.PolynomialMixingAmplification
