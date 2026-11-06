import LongTails.Proofs.AffineSoftmaxOuterExecution

namespace LongTails.Proofs.AffineSoftmaxSearchCoupling

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxSearch

def Certificate (d : ℝ → ℝ) (r floor cap answer : ℝ) : Prop :=
  answer ∈ Set.Icc floor cap ∧
    ((answer = floor ∧ d answer < r) ∨ (51 * r / 64 ≤ d answer ∧ d answer ≤ 61 * r / 64))

noncomputable def exactSearch (d : ℝ → ℝ) (r floor cap : ℝ) (H : ℕ) : ℝ :=
  Program.eval (fun _ : Unit => ())
    (searchPlan (fun _ μ => (Program.done (min r (d μ)) : Program Unit Unit ℝ)) r floor cap H)

noncomputable def repair (d : ℝ → ℝ) (r floor cap : ℝ) (H : ℕ) (candidate : ℝ) : ℝ := by
  classical
  exact if Certificate d r floor cap candidate then candidate else exactSearch d r floor cap H

lemma exactSearch_certificate (d : ℝ → ℝ) {r floor cap K : ℝ} (H : ℕ)
    (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap) (hK : 0 ≤ K)
    (hcap : d cap ≤ r / 2) (hend : cap / 2 ^ H ≤ floor)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (hs : K / 2 ^ (H + 7) < r / 64) :
    Certificate d r floor cap (exactSearch d r floor cap H) := by
  apply AffineSoftmaxSearchGeometry.searchPlan_certificate d
    (fun _ μ => (Program.done (min r (d μ)) : Program Unit Unit ℝ)) (fun _ => ()) H
    hr hf hfc hK hcap hend hmod hs
  · intro i _ previous _
    simp only [Program.eval, sub_self, abs_zero]
    positivity
  · intro i _ lower upper _ _
    simp only [Program.eval, sub_self, abs_zero]
    positivity

lemma exactSearch_measurable {Z : Type*} [MeasurableSpace Z] (d : Z → ℝ → ℝ)
    (hd : Measurable (Function.uncurry d)) (r floor cap : ℝ) (H : ℕ) :
    Measurable (fun z => exactSearch (d z) r floor cap H) := by
  let probes : Z → ℕ → ℝ → Program Unit Unit ℝ := fun z _ μ => .done (min r (d z μ))
  have hp (i : ℕ) : Measurable (fun z : Z × ℝ => Program.eval (fun _ : Unit => ()) (probes z.1 i z.2)) :=
    measurable_const.min hd
  exact AffineSoftmaxSearchTrace.searchPlan_measurable probes (fun _ : Unit => ()) r floor cap H hp

lemma certificate_measurable {Z : Type*} [MeasurableSpace Z] (d : Z → ℝ → ℝ)
    (hd : Measurable (Function.uncurry d)) (candidate : Z → ℝ) (hc : Measurable candidate)
    (r floor cap : ℝ) : MeasurableSet {z | Certificate (d z) r floor cap (candidate z)} := by
  have hv : Measurable (fun z => d z (candidate z)) := hd.comp (measurable_id.prodMk hc)
  exact (measurableSet_Icc.preimage hc).inter
    (((measurableSet_eq_fun hc measurable_const).inter (measurableSet_lt hv measurable_const)).union
      ((measurableSet_le measurable_const hv).inter (measurableSet_le hv measurable_const)))

lemma repair_measurable {Z : Type*} [MeasurableSpace Z] (d : Z → ℝ → ℝ)
    (hd : Measurable (Function.uncurry d)) (candidate : Z → ℝ) (hc : Measurable candidate)
    (r floor cap : ℝ) (H : ℕ) : Measurable (fun z => repair (d z) r floor cap H (candidate z)) := by
  classical
  exact Measurable.ite (certificate_measurable d hd candidate hc r floor cap) hc
    (exactSearch_measurable d hd r floor cap H)

lemma repair_eq_candidate (d : ℝ → ℝ) (r floor cap : ℝ) (H : ℕ) (candidate : ℝ)
    (hc : Certificate d r floor cap candidate) : repair d r floor cap H candidate = candidate := by
  simp only [repair, hc, ite_true]

lemma repair_certificate (d : ℝ → ℝ) {r floor cap K : ℝ} (H : ℕ)
    (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap) (hK : 0 ≤ K)
    (hcap : d cap ≤ r / 2) (hend : cap / 2 ^ H ≤ floor)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (hs : K / 2 ^ (H + 7) < r / 64) (candidate : ℝ) :
    Certificate d r floor cap (repair d r floor cap H candidate) := by
  classical
  unfold repair
  split_ifs with h
  · exact h
  · exact exactSearch_certificate d H hr hf hfc hK hcap hend hmod hs

lemma certificate_outer_validity (d : ℝ → ℝ) {r floor cap answer : ℝ}
    (hr : 0 < r) (hf : 0 ≤ floor) (hc : Certificate d r floor cap answer) :
    d answer < r ∧ (answer ≤ 2 * floor ∨ 3 * r / 4 ≤ d answer) := by
  rcases hc.2 with ⟨he, hd⟩ | ⟨hl, hu⟩
  · exact ⟨hd, Or.inl (by rw [he]; linarith)⟩
  · exact ⟨by linarith, Or.inr (by linarith)⟩

lemma exactProx_param_measurable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Z]
    {X : Set E} {f : E → ℝ} (hcompact : IsCompact X) (hne : X.Nonempty)
    (hf : ConvexOn ℝ X f) (hfc : ContinuousOn f X)
    (μ : Z → ℝ) (hμ : Measurable μ) (hpos : ∀ z, 0 < μ z)
    (center : Z → E) (hc : Measurable center) :
    Measurable (fun z => AffineSoftmaxRegularization.exactProx X f (μ z) (center z)) := by
  let T := {t : ℝ // 0 < t} × E
  have hcont : Continuous (fun w : T => AffineSoftmaxRegularization.exactProx X f w.1.val w.2) :=
    AffineSoftmaxRegularization.exactProx_continuous hcompact hne hf hfc
      (fun w : T => w.1.val) (fun w => w.2)
      (continuous_subtype_val.comp continuous_fst) continuous_snd (fun w => w.1.property)
  have hmap : Measurable (fun z : Z => ((⟨μ z, hpos z⟩ : {t : ℝ // 0 < t}), center z)) :=
    (hμ.subtype_mk (h := hpos)).prodMk hc
  have hh := hcont.measurable.comp hmap
  simpa only [Function.comp_def] using hh

lemma predictor_displacement_joint_measurable {E Z : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Z]
    {X : Set E} {f : E → ℝ} (hcompact : IsCompact X) (hne : X.Nonempty)
    (hf : ConvexOn ℝ X f) (hfc : ContinuousOn f X) {floor : ℝ} (hfloor : 0 < floor)
    (state : Z → LongTails.Algorithms.CappedProximal.State E)
    (hA : Measurable (fun z => (state z).weight))
    (hx : Measurable (fun z => (state z).primal)) (hv : Measurable (fun z => (state z).dual)) :
    Measurable (fun w : Z × ℝ =>
      ‖AffineSoftmaxRegularization.exactProx X f (max floor w.2)
          (LongTails.Algorithms.CappedProximal.predictor (max floor w.2) (state w.1)) -
        LongTails.Algorithms.CappedProximal.predictor (max floor w.2) (state w.1)‖) := by
  have hμ : Measurable (fun w : Z × ℝ => max floor w.2) := measurable_const.max measurable_snd
  have hc := AffineSoftmaxPredictor.predictor_param_measurable (fun w : Z × ℝ => state w.1)
    (fun w => max floor w.2) hμ (hA.comp measurable_fst) (hx.comp measurable_fst) (hv.comp measurable_fst)
  exact ((exactProx_param_measurable hcompact hne hf hfc _ hμ
    (fun w => hfloor.trans_le (le_max_left floor w.2)) _ hc).sub hc).norm

def path {S Ω : Type*} (step : S → Ω → S) (initial : S) (seeds : ℕ → Ω) : ℕ → S
  | 0 => initial
  | n + 1 => step (path step initial seeds n) (seeds n)

lemma path_prefix {S Ω : Type*} (step : S → Ω → S) (initial : S)
    (seeds other : ℕ → Ω) (n : ℕ) (h : ∀ i < n, seeds i = other i) :
    path step initial seeds n = path step initial other n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [path, ih (fun i hi => h i (by omega)), h n (by omega)]

lemma path_measurable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (step : S → Ω → S) (hstep : Measurable (Function.uncurry step)) (initial : S) (n : ℕ) :
    Measurable (fun seeds : ℕ → Ω => path step initial seeds n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact hstep.comp (ih.prodMk (measurable_pi_apply n))

lemma paths_equal_of_no_failure {S Ω : Type*} (actual repaired : S → Ω → S)
    (bad : S → Ω → Prop) (heq : ∀ s ω, ¬ bad s ω → actual s ω = repaired s ω)
    (initial : S) (seeds : ℕ → Ω) (n : ℕ)
    (hgood : ∀ i < n, ¬ bad (path repaired initial seeds i) (seeds i)) :
    path actual initial seeds n = path repaired initial seeds n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [path, ih (fun i hi => hgood i (by omega))]
    exact heq _ _ (hgood n (by omega))

lemma coupling_failure_bound {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (actual repaired : S → Ω → S)
    (hm : Measurable (Function.uncurry repaired)) (bad : S → Ω → Prop)
    (hbad : MeasurableSet {z : S × Ω | bad z.1 z.2})
    (heq : ∀ s ω, ¬ bad s ω → actual s ω = repaired s ω)
    {p : ℝ} (hp : 0 ≤ p) (hb : ∀ s, (Q : Measure Ω) {ω | bad s ω} ≤ ENNReal.ofReal p)
    (initial : S) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)))
      {seeds | path actual initial seeds n ≠ path repaired initial seeds n} ≤
      ENNReal.ofReal ((n : ℝ) * p) := by
  have h := AffineSoftmaxSearchProbability.visited_failure_bound Q
    (fun i seeds => path repaired initial seeds i) (path_measurable repaired hm initial)
    (fun i seeds other hprefix => path_prefix repaired initial seeds other i hprefix)
    (fun _ s ω => bad s ω) (fun _ => hbad) hp (fun _ s => hb s) n
  apply le_trans (measure_mono ?_) h
  intro seeds hne
  by_contra hnone
  apply hne
  apply paths_equal_of_no_failure actual repaired bad heq initial seeds n
  intro i hi hbad'
  exact hnone ⟨i, hi, hbad'⟩

end LongTails.Proofs.AffineSoftmaxSearchCoupling
