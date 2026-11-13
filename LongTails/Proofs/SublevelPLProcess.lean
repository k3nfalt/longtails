import LongTails.Proofs.SublevelPLSampling
import LongTails.Proofs.SublevelPLTrajectory

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.SublevelRobustGradient

open RobustGradient

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Ω]


noncomputable def iterFrom {n : ℕ} (L : ℝ) (G : E → (Fin n → Ω) → E)
    (ζ : ℕ → Fin n → Ω) (call : ℕ) (x : E) : ℕ → E
  | 0 => x
  | j + 1 => iterFrom L G ζ call x j - (1 / L) • G (iterFrom L G ζ call x j) (ζ (call + j))

noncomputable def iter {n : ℕ} (L : ℝ) (G : E → (Fin n → Ω) → E) (x0 : E)
    (ζ : ℕ → Fin n → Ω) (j : ℕ) : E :=
  iterFrom L G ζ 0 x0 j

omit [MeasurableSpace Ω] in
lemma iter_succ {n : ℕ} (L : ℝ) (G : E → (Fin n → Ω) → E) (x0 : E) (ζ : ℕ → Fin n → Ω)
    (j : ℕ) : iter L G x0 ζ (j + 1) = iter L G x0 ζ j - (1 / L) • G (iter L G x0 ζ j) (ζ j) := by
  simp [iter, iterFrom]

omit [MeasurableSpace Ω] in
lemma iterFrom_shift {n : ℕ} (L : ℝ) (G : E → (Fin n → Ω) → E) (ζ : ℕ → Fin n → Ω)
    (call : ℕ) (x : E) : ∀ K,
    iterFrom L G ζ call x (K + 1) = iterFrom L G ζ (call + 1) (x - (1 / L) • G x (ζ call)) K
  | 0 => by simp [iterFrom]
  | K + 1 => by
    rw [show iterFrom L G ζ call x (K + 1 + 1) =
      iterFrom L G ζ call x (K + 1) - (1 / L) • G (iterFrom L G ζ call x (K + 1))
        (ζ (call + (K + 1))) from rfl]
    rw [iterFrom_shift L G ζ call x K]
    rw [show call + (K + 1) = call + 1 + K by ring]
    rfl

omit [MeasurableSpace Ω] in
lemma iter_congr {n : ℕ} (L : ℝ) (G : E → (Fin n → Ω) → E) (x0 : E)
    (ζ ζ' : ℕ → Fin n → Ω) : ∀ j, (∀ i, i < j → ζ i = ζ' i) →
    iter L G x0 ζ j = iter L G x0 ζ' j
  | 0, _ => rfl
  | j + 1, h => by
    rw [iter_succ, iter_succ, iter_congr L G x0 ζ ζ' j (fun i hi => h i (by omega)),
      h j (by omega)]

noncomputable def iterFin {n : ℕ} (L : ℝ) (G : E → (Fin n → Ω) → E) (x0 : E) :
    (j : ℕ) → (Fin j → Fin n → Ω) → E
  | 0, _ => x0
  | j + 1, pre => iterFin L G x0 j (Fin.init pre) -
      (1 / L) • G (iterFin L G x0 j (Fin.init pre)) (pre (Fin.last j))

omit [MeasurableSpace Ω] in
lemma iter_eq_iterFin {n : ℕ} (L : ℝ) (G : E → (Fin n → Ω) → E) (x0 : E)
    (ζ : ℕ → Fin n → Ω) : ∀ j, iter L G x0 ζ j = iterFin L G x0 j (fun i : Fin j => ζ i)
  | 0 => rfl
  | j + 1 => by
    rw [iter_succ, iter_eq_iterFin L G x0 ζ j]
    rfl

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
lemma measurable_iterFin {n : ℕ} (L : ℝ) {G : E → (Fin n → Ω) → E}
    (hG : Measurable (Function.uncurry G)) (x0 : E) :
    ∀ j, Measurable (iterFin L G x0 j)
  | 0 => measurable_const
  | j + 1 => by
    have ih := measurable_iterFin L hG x0 j
    have hinit : Measurable (fun pre : Fin (j + 1) → Fin n → Ω => Fin.init pre) :=
      Measurable.of_eval (fun i => measurable_pi_apply _)
    have hlast : Measurable (fun pre : Fin (j + 1) → Fin n → Ω => pre (Fin.last j)) :=
      measurable_pi_apply _
    simp only [iterFin]
    apply Measurable.sub (ih.comp hinit)
    apply Measurable.const_smul
    exact hG.comp ((ih.comp hinit).prodMk hlast)

omit [CompleteSpace E] in
lemma measurable_iter {n : ℕ} (L : ℝ) {G : E → (Fin n → Ω) → E}
    (hG : Measurable (Function.uncurry G)) (x0 : E) (j : ℕ) :
    Measurable (fun ζ : ℕ → Fin n → Ω => iter L G x0 ζ j) := by
  have h : (fun ζ : ℕ → Fin n → Ω => iter L G x0 ζ j) =
      (iterFin L G x0 j) ∘ (fun ζ : ℕ → Fin n → Ω => fun i : Fin j => ζ i) := by
    funext ζ
    simp [Function.comp, iter_eq_iterFin]
  rw [h]
  exact (measurable_iterFin L hG x0 j).comp
    (Measurable.of_eval (fun i => measurable_pi_apply _))

omit [CompleteSpace E] in
lemma block_lintegral_le (p : Measure Ω) [IsProbabilityMeasure p] {n : ℕ}
    {G : E → (Fin n → Ω) → E} (hG : Measurable (Function.uncurry G))
    (L : ℝ) (x0 : E) (F : E × (Fin n → Ω) → ENNReal) (hF : Measurable F) {c : ENNReal}
    (hc : ∀ x, (∫⁻ ξ, F (x, ξ) ∂(Measure.pi fun _ : Fin n => p)) ≤ c) (j : ℕ) :
    (∫⁻ ζ, F (iter L G x0 ζ j, ζ j)
      ∂(Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p)) ≤ c := by
  set B : Measure (Fin n → Ω) := Measure.pi fun _ : Fin n => p with hB
  have : IsProbabilityMeasure B := by rw [hB]; infer_instance
  have hsplit := StochasticGeneralized.splitStream_preserving B j
  let H : (Fin j → Fin n → Ω) × (ℕ → Fin n → Ω) → ENNReal :=
    fun z => F (iterFin L G x0 j z.1, z.2 0)
  have hH : Measurable H :=
    hF.comp (((measurable_iterFin L hG x0 j).comp measurable_fst).prodMk
      ((measurable_pi_apply 0).comp measurable_snd))
  have hcomp : (fun ζ : ℕ → Fin n → Ω => F (iter L G x0 ζ j, ζ j)) =
      fun ζ => H (StochasticGeneralized.splitStream j ζ) := by
    funext ζ
    simp only [H, StochasticGeneralized.splitStream, MeasurableEquiv.coe_mk,
      Equiv.coe_fn_mk, iter_eq_iterFin, add_zero]
  rw [hcomp, hsplit.lintegral_comp hH]
  rw [lintegral_prod _ hH.aemeasurable]
  have hev := measurePreserving_eval_infinitePi (fun _ : ℕ => B) 0
  calc (∫⁻ pre, ∫⁻ tail, H (pre, tail) ∂(Measure.infinitePi fun _ : ℕ => B)
        ∂(Measure.pi fun _ : Fin j => B))
      ≤ ∫⁻ _pre, c ∂(Measure.pi fun _ : Fin j => B) := by
        apply lintegral_mono
        intro pre
        have hm : Measurable (fun ξ : Fin n → Ω => F (iterFin L G x0 j pre, ξ)) :=
          hF.comp (measurable_const.prodMk measurable_id)
        have : (∫⁻ tail, H (pre, tail) ∂(Measure.infinitePi fun _ : ℕ => B)) =
            ∫⁻ ξ, F (iterFin L G x0 j pre, ξ) ∂B := by
          rw [← hev.lintegral_comp hm]
        show (∫⁻ tail, H (pre, tail) ∂(Measure.infinitePi fun _ : ℕ => B)) ≤ c
        rw [this]
        exact hc _
    _ = c := by simp

lemma good_event_measurableSet {n : ℕ} {G : E → (Fin n → Ω) → E}
    (hG : Measurable (Function.uncurry G)) {f : E → ℝ} (hgrad : Measurable (gradient f))
    (L ν : ℝ) (x0 : E) (K : ℕ) :
    MeasurableSet {ζ : ℕ → Fin n → Ω |
      ∀ j, j < K → ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2 ≤ ν} := by
  have : {ζ : ℕ → Fin n → Ω |
      ∀ j, j < K → ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2 ≤ ν} =
      ⋂ j ∈ Finset.range K, {ζ : ℕ → Fin n → Ω |
        ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2 ≤ ν} := by
    ext ζ; simp
  rw [this]
  refine Finset.measurableSet_biInter _ (fun j _ => ?_)
  apply measurableSet_le _ measurable_const
  apply Measurable.pow_const
  apply Measurable.norm
  apply Measurable.sub
  · exact hG.comp ((measurable_iter L hG x0 j).prodMk (measurable_pi_apply j))
  · exact hgrad.comp (measurable_iter L hG x0 j)

lemma failure_probability_le (p : Measure Ω) [IsProbabilityMeasure p] {n : ℕ}
    {G : E → (Fin n → Ω) → E} (hG : Measurable (Function.uncurry G))
    {f : E → ℝ} (hgrad : Measurable (gradient f)) (L ν : ℝ) (x0 : E) (K : ℕ) {q : ENNReal}
    (hq : ∀ x, (Measure.pi fun _ : Fin n => p)
      {ξ | ν < ‖G x ξ - gradient f x‖ ^ 2} ≤ q) :
    (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p)
      {ζ | ∀ j, j < K → ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2 ≤ ν}ᶜ
      ≤ K * q := by
  classical
  let F : E × (Fin n → Ω) → ENNReal := fun w =>
    Set.indicator {w : E × (Fin n → Ω) | ν < ‖G w.1 w.2 - gradient f w.1‖ ^ 2} 1 w
  have hS : MeasurableSet {w : E × (Fin n → Ω) | ν < ‖G w.1 w.2 - gradient f w.1‖ ^ 2} := by
    apply measurableSet_lt measurable_const
    apply Measurable.pow_const
    apply Measurable.norm
    exact hG.sub (hgrad.comp measurable_fst)
  have hF : Measurable F := measurable_one.indicator hS
  have hc : ∀ x, (∫⁻ ξ, F (x, ξ) ∂(Measure.pi fun _ : Fin n => p)) ≤ q := by
    intro x
    have hSx : MeasurableSet {ξ : Fin n → Ω | ν < ‖G x ξ - gradient f x‖ ^ 2} :=
      hS.preimage (measurable_const.prodMk measurable_id)
    have : (fun ξ : Fin n → Ω => F (x, ξ)) =
        Set.indicator {ξ : Fin n → Ω | ν < ‖G x ξ - gradient f x‖ ^ 2} 1 := by
      funext ξ
      simp [F, Set.indicator_apply]
    rw [this, lintegral_indicator_one hSx]
    exact hq x
  have hcompl : {ζ : ℕ → Fin n → Ω |
      ∀ j, j < K → ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2 ≤ ν}ᶜ =
      ⋃ j ∈ Finset.range K, {ζ : ℕ → Fin n → Ω |
        ν < ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2} := by
    ext ζ
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le, Set.mem_iUnion,
      Finset.mem_range, exists_prop]
  rw [hcompl]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hj : ∀ j ∈ Finset.range K, (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p)
      {ζ : ℕ → Fin n → Ω |
        ν < ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2} ≤ q := by
    intro j _
    have hSj : MeasurableSet {ζ : ℕ → Fin n → Ω |
        ν < ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2} :=
      hS.preimage ((measurable_iter L hG x0 j).prodMk (measurable_pi_apply j))
    rw [← lintegral_indicator_one hSj]
    have : Set.indicator {ζ : ℕ → Fin n → Ω |
        ν < ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2} 1 =
        fun ζ => F (iter L G x0 ζ j, ζ j) := by
      funext ζ
      simp [F, Set.indicator_apply]
    rw [this]
    exact block_lintegral_le p hG L x0 F hF hc j
  calc (∑ j ∈ Finset.range K, (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p)
        {ζ : ℕ → Fin n → Ω |
          ν < ‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2})
      ≤ ∑ _j ∈ Finset.range K, q := Finset.sum_le_sum hj
    _ = K * q := by simp

lemma energy_lintegral_le (p : Measure Ω) [IsProbabilityMeasure p] {n : ℕ}
    {G : E → (Fin n → Ω) → E} (hG : Measurable (Function.uncurry G))
    {f : E → ℝ} (hgrad : Measurable (gradient f)) (L : ℝ) (x0 : E) (K : ℕ) {c : ENNReal}
    (hc : ∀ x, (∫⁻ ξ, ENNReal.ofReal (‖G x ξ - gradient f x‖ ^ 2)
      ∂(Measure.pi fun _ : Fin n => p)) ≤ c) :
    (∫⁻ ζ, ∑ j ∈ Finset.range K,
      ENNReal.ofReal (‖G (iter L G x0 ζ j) (ζ j) - gradient f (iter L G x0 ζ j)‖ ^ 2)
      ∂(Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p)) ≤ K * c := by
  let F : E × (Fin n → Ω) → ENNReal := fun w =>
    ENNReal.ofReal (‖G w.1 w.2 - gradient f w.1‖ ^ 2)
  have hF : Measurable F :=
    ENNReal.measurable_ofReal.comp (((hG.sub (hgrad.comp measurable_fst)).norm).pow_const 2)
  have hmj : ∀ j, Measurable (fun ζ : ℕ → Fin n → Ω => F (iter L G x0 ζ j, ζ j)) :=
    fun j => hF.comp ((measurable_iter L hG x0 j).prodMk (measurable_pi_apply j))
  rw [lintegral_finsetSum _ (fun j _ => hmj j)]
  calc (∑ j ∈ Finset.range K, ∫⁻ ζ, F (iter L G x0 ζ j, ζ j)
        ∂(Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p))
      ≤ ∑ _j ∈ Finset.range K, c :=
        Finset.sum_le_sum (fun j _ => block_lintegral_le p hG L x0 F hF hc j)
    _ = K * c := by simp

end OracleTemplate.SublevelRobustGradient
