import LongTails.Proofs.RobustGeneralizedProcess
import LongTails.Proofs.RobustAdaptiveFailures

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.RobustGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate tentativeWeight coupling)
open StochasticGeneralized (proofActive prepare firstHalf secondHalf accumulated blockTrace
  accumulated_eq_sum accumulated_measurable)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

noncomputable def pilotBad (p : Params) (f : p.E → ℝ) (a : ℝ)
    (oracle : p.E → p.Ω → p.E) (x : p.E) {n : ℕ} (ξ : Fin n → p.Ω) : Prop :=
  radius p a/2 < ‖gradient f x-pilotReply p a (sampleReplies oracle x ξ)‖

noncomputable def batchBad (p : Params) (f : p.E → ℝ) (oracle : p.E → p.Ω → p.E)
    (s : Iterate p.E) {m : ℕ} (ξ ζ : Fin m → p.Ω) : Prop :=
  pilotBad p f (tentativeWeight s) oracle (coupling s) ξ ∨
    pilotBad p f (tentativeWeight s) oracle
      (prepare p.L0 p.L1 s (guardedReply p f (tentativeWeight s) oracle (coupling s) ξ)).point ζ

noncomputable def proofFailure (p : Params) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) : ℝ := by
  classical
  exact if proofActive p f u s ∧ batchBad p f oracle s (firstHalf ξ) (secondHalf ξ) then 1 else 0

lemma measurableSet_pilotBad (p : Params) {f : p.E → ℝ}
    (hgrad : Measurable (gradient f)) {oracle : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    MeasurableSet {w : ℝ × p.E × (Fin n → p.Ω) | pilotBad p f w.1 oracle w.2.1 w.2.2} := by
  have hx : Measurable (fun w : ℝ × p.E × (Fin n → p.Ω) => gradient f w.2.1) :=
    hgrad.comp measurable_snd.fst
  have hs : Measurable (fun w : ℝ × p.E × (Fin n → p.Ω) =>
      (w.1, sampleReplies oracle w.2.1 w.2.2)) :=
    measurable_fst.prodMk ((measurable_sampleReplies p hg n).comp measurable_snd)
  exact measurableSet_lt (((measurable_radius p).comp measurable_fst).div_const 2)
    (hx.sub ((measurable_pilotReply p).comp hs)).norm

lemma measurableSet_batchBad (p : Params) {f : p.E → ℝ}
    (hgrad : Measurable (gradient f)) {oracle : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry oracle)) (m : ℕ) :
    MeasurableSet {w : Iterate p.E × (Fin m → p.Ω) × (Fin m → p.Ω) |
      batchBad p f oracle w.1 w.2.1 w.2.2} := by
  have hbad := measurableSet_pilotBad p hgrad hg m
  have hbatch := measurable_guardedReply p hgrad hg m
  unfold batchBad
  apply MeasurableSet.union
  · exact hbad.preimage (show Measurable (fun w : Iterate p.E × (Fin m → p.Ω) × (Fin m → p.Ω) =>
      (tentativeWeight w.1, coupling w.1, w.2.1)) by fun_prop)
  · exact hbad.preimage (show Measurable (fun w : Iterate p.E × (Fin m → p.Ω) × (Fin m → p.Ω) =>
      (tentativeWeight w.1, (prepare p.L0 p.L1 w.1
        (guardedReply p f (tentativeWeight w.1) oracle (coupling w.1) w.2.1)).point, w.2.2)) by fun_prop)

set_option maxHeartbeats 1000000 in
lemma measurable_proofFailure (p : Params) {f : p.E → ℝ}
    (hf : Measurable f) (hgrad : Measurable (gradient f)) (u : p.E)
    {oracle : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (Function.uncurry (proofFailure p f u oracle n)) := by
  have hfirst := StochasticGeneralized.measurable_firstHalf (Ω := p.Ω) n
  have hsecond := StochasticGeneralized.measurable_secondHalf (Ω := p.Ω) n
  have hm : Measurable (fun w : Iterate p.E × (Fin n → p.Ω) =>
      (w.1, firstHalf w.2, secondHalf w.2)) :=
    measurable_fst.prodMk ((hfirst.comp measurable_snd).prodMk (hsecond.comp measurable_snd))
  have hbad := (measurableSet_batchBad p hgrad hg (n/2)).preimage hm
  have hactive := (StochasticGeneralized.measurableSet_proofActive p hf u).preimage
    (measurable_fst : Measurable (Prod.fst : Iterate p.E × (Fin n → p.Ω) → Iterate p.E))
  have hset : MeasurableSet {w : Iterate p.E × (Fin n → p.Ω) |
      proofActive p f u w.1 ∧ batchBad p f oracle w.1 (firstHalf w.2) (secondHalf w.2)} := by
    simpa only [Set.preimage_ofPred_eq, Set.ofPred_and] using hactive.inter hbad
  exact Measurable.ite hset measurable_const measurable_const

lemma proofFailure_bounds (p : Params) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (n : ℕ) (s : Iterate p.E) (ξ : Fin n → p.Ω) :
    0 ≤ proofFailure p f u oracle n s ξ ∧ proofFailure p f u oracle n s ξ ≤ 1 := by
  classical
  unfold proofFailure
  split_ifs <;> norm_num

lemma guardedStep_eq_sampleStep (p : Params) (f : p.E → ℝ)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) {n : ℕ} (ξ : Fin n → p.Ω)
    (h : ¬batchBad p f oracle s (firstHalf ξ) (secondHalf ξ)) :
    guardedStep p f oracle s ξ = sampleStep p oracle s ξ := by
  have h₁ := not_lt.mp (fun h₁ => h (Or.inl h₁))
  have he₁ := guardedReply_eq p f (tentativeWeight s) oracle (coupling s) (firstHalf ξ) h₁
  have h₂ := not_lt.mp (fun h₂ => h (Or.inr h₂))
  have he₂ := guardedReply_eq p f (tentativeWeight s) oracle
    (prepare p.L0 p.L1 s (guardedReply p f (tentativeWeight s) oracle (coupling s) (firstHalf ξ))).point
    (secondHalf ξ) h₂
  unfold guardedStep sampleStep StochasticGeneralized.step
  dsimp only
  rw [he₁] at he₂ ⊢
  rw [he₂]

lemma batchBad_mean (p : Params) {f : p.E → ℝ} (hgrad : Measurable (gradient f))
    {μ : Measure p.Ω} [IsProbabilityMeasure μ] {oracle : p.E → p.Ω → p.E}
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (s : Iterate p.E) (hB : 0 < radius p (tentativeWeight s)) :
    let m := estimatorCost p (tentativeWeight s)
    (∫ w : (Fin m → p.Ω) × (Fin m → p.Ω),
      {w | batchBad p f oracle s w.1 w.2}.indicator (fun _ => (1 : ℝ)) w
      ∂(Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ)) ≤
      2*(1/2 : ℝ)^(pilotGroups p) := by
  classical
  let a := tentativeWeight s
  let m := estimatorCost p a
  let A : Set (Fin m → p.Ω) := {ξ | pilotBad p f a oracle (coupling s) ξ}
  let B : Set ((Fin m → p.Ω) × (Fin m → p.Ω)) :=
    {w | pilotBad p f a oracle
      (prepare p.L0 p.L1 s (guardedReply p f a oracle (coupling s) w.1)).point w.2}
  have hm := measurableSet_pilotBad p hgrad hg.measurable m
  have hbatch := measurable_guardedReply p hgrad hg.measurable m
  have hA : MeasurableSet A := hm.preimage
    (show Measurable (fun ξ : Fin m → p.Ω => (a, coupling s, ξ)) by fun_prop)
  have hBset : MeasurableSet B := hm.preimage
    (show Measurable (fun w : (Fin m → p.Ω) × (Fin m → p.Ω) =>
      (a, (prepare p.L0 p.L1 s (guardedReply p f a oracle (coupling s) w.1)).point, w.2)) by fun_prop)
  have hp (x : p.E) : (Measure.pi fun _ : Fin m => μ).real
      {ξ | pilotBad p f a oracle x ξ} ≤ (1/2 : ℝ)^(pilotGroups p) := by
    have h := pilotReply_failure_probability p μ hg a hB x
    exact (ENNReal.toReal_mono (by finiteness) h).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  exact RobustGradient.adaptive_pair_bad_mean hA hBset (hp (coupling s))
    (fun ξ => hp (prepare p.L0 p.L1 s (guardedReply p f a oracle (coupling s) ξ)).point)

set_option maxHeartbeats 1000000 in
lemma proofFailure_mean (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
     (hgrad : Measurable (gradient f)) (u : p.E)
    {μ : Measure p.Ω} [IsProbabilityMeasure μ] {oracle : p.E → p.Ω → p.E}
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (s : Iterate p.E) :
    (∫ ξ, proofFailure p f u oracle (proofCost p f u s) s ξ
      ∂Measure.pi (fun _ : Fin (proofCost p f u s) => μ)) ≤
      2*(1/2 : ℝ)^(pilotGroups p) := by
  classical
  by_cases hs : proofActive p f u s
  · let n := proofCost p f u s
    let m := n/2
    have hm : m = estimatorCost p (tentativeWeight s) := by
      dsimp [m, n, proofCost]
      rw [ite_eq_left hs]
      omega
    have hB := radius_pos p hp.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2
      (GeneralizedAccelerated.tentativeWeight_pos s hs.2.1)
    let F : (Fin m → p.Ω) × (Fin m → p.Ω) → ℝ :=
      {w | batchBad p f oracle s w.1 w.2}.indicator (fun _ => (1 : ℝ))
    have hset : MeasurableSet {w : (Fin m → p.Ω) × (Fin m → p.Ω) |
        batchBad p f oracle s w.1 w.2} :=
      by
        have hm : Measurable (fun w : (Fin m → p.Ω) × (Fin m → p.Ω) => (s, w)) :=
          measurable_const.prodMk measurable_id
        have hh := (measurableSet_batchBad p hgrad hg.measurable m).preimage hm
        simpa only [Set.preimage_ofPred_eq] using hh
    have hFi : Integrable F ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ)) :=
      (integrable_const 1).indicator hset
    have he : (fun ξ : Fin n → p.Ω => proofFailure p f u oracle n s ξ) =
        F ∘ (fun ξ : Fin n → p.Ω => (firstHalf ξ, secondHalf ξ)) := by
      ext ξ
      simp only [proofFailure, hs, true_and, F, Function.comp_apply, Set.indicator,
        Set.mem_ofPred_eq]
    change (∫ ξ : Fin n → p.Ω, proofFailure p f u oracle n s ξ ∂Measure.pi (fun _ => μ)) ≤ _
    rw [he]
    have hpv := StochasticGeneralized.halves_preserving p μ n
    have hl : HasLaw (fun ξ : Fin n → p.Ω => (firstHalf ξ, secondHalf ξ))
        ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))
        (Measure.pi fun _ : Fin n => μ) := ⟨hpv.measurable.aemeasurable, hpv.map_eq⟩
    rw [hl.integral_comp hFi.aestronglyMeasurable]
    have hb (j : ℕ) (hj : j = estimatorCost p (tentativeWeight s)) :
        (∫ w : (Fin j → p.Ω) × (Fin j → p.Ω),
          {w | batchBad p f oracle s w.1 w.2}.indicator (fun _ => (1 : ℝ)) w
          ∂(Measure.pi fun _ : Fin j => μ).prod (Measure.pi fun _ : Fin j => μ)) ≤
          2*(1/2 : ℝ)^(pilotGroups p) := by
      subst j
      exact batchBad_mean p hgrad hg s hB
    exact hb m hm
  · simp only [proofFailure, hs, false_and, ↓reduceIte, integral_zero]
    positivity

lemma proofFailure_accumulated_measurable (p : Params) {f : p.E → ℝ}
    (hf : Measurable f) (hgrad : Measurable (gradient f)) (u : p.E)
    {oracle : p.E → p.Ω → p.E} (hg : Measurable (Function.uncurry oracle))
    (n : ℕ) (s : Iterate p.E) :
    Measurable (accumulated (proofCost p f u) (proofNext p f u oracle)
      (proofFailure p f u oracle) n s) := by
  exact (accumulated_measurable (measurable_proofCost p hf u)
    (measurable_proofNext p hf hgrad u hg) (measurable_proofFailure p hf hgrad u hg) n).comp
    (measurable_const.prodMk measurable_id)

lemma proofFailure_tail (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hf : Measurable f) (hgrad : Measurable (gradient f)) (u : p.E)
    {μ : Measure p.Ω} [IsProbabilityMeasure μ] {oracle : p.E → p.Ω → p.E}
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (n : ℕ) (s : Iterate p.E) :
    (Measure.infinitePi fun _ : ℕ => μ) {ξ | 1 ≤ accumulated (proofCost p f u)
      (proofNext p f u oracle) (proofFailure p f u oracle) n s ξ} ≤
      ENNReal.ofReal ((n : ℝ)*(2*(1/2 : ℝ)^(pilotGroups p))) := by
  exact RobustGradient.accumulated_failure_probability μ (measurable_proofCost p hf u)
    (measurable_proofNext p hf hgrad u hg.measurable)
    (measurable_proofFailure p hf hgrad u hg.measurable)
    (proofFailure_bounds p f u oracle) (proofFailure_mean p hp hgrad u hg) n s

lemma proofFailure_tail_iid (p : Params) (hp : spec.valid p) {f : p.E → ℝ}
    (hf : Measurable f) (hgrad : Measurable (gradient f)) (u : p.E)
    {μ : Measure p.Ω} [IsProbabilityMeasure μ] {oracle : p.E → p.Ω → p.E}
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ξ}
    {ξ : ℕ → Ξ → p.Ω} (hξ : IID ξ μ P) (n : ℕ) (s : Iterate p.E) :
    P {ω | 1 ≤ accumulated (proofCost p f u) (proofNext p f u oracle)
      (proofFailure p f u oracle) n s (fun k => ξ k ω)} ≤
      ENNReal.ofReal ((n : ℝ)*(2*(1/2 : ℝ)^(pilotGroups p))) := by
  have hm := proofFailure_accumulated_measurable p hf hgrad u hg.measurable n s
  have hl : HasLaw (fun ω k => ξ k ω) (Measure.infinitePi fun _ : ℕ => μ) P :=
    ⟨hξ.stream_law.measurable.aemeasurable, hξ.stream_law.map_eq⟩
  rw [hl.measure_eq (measurableSet_le measurable_const hm)]
  exact proofFailure_tail p hp hf hgrad u hg n s

lemma proofFailure_zero_of_accumulated_lt (p : Params) (f : p.E → ℝ) (u : p.E)
    (oracle : p.E → p.Ω → p.E) (s : Iterate p.E) (ξ : ℕ → p.Ω) (n : ℕ)
    (h : accumulated (proofCost p f u) (proofNext p f u oracle)
      (proofFailure p f u oracle) n s ξ < 1) (i : ℕ) (hi : i < n) :
    let q := blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ i
    proofFailure p f u oracle (proofCost p f u q.1) q.1 (fun j => q.2 j) = 0 := by
  classical
  rw [accumulated_eq_sum] at h
  let q := blockTrace (proofCost p f u) (proofNext p f u oracle) s ξ
  have hm := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.range n) => (proofFailure_bounds p f u oracle
      (proofCost p f u (q j).1) (q j).1 (fun k => (q j).2 k)).1)
    (Finset.mem_range.mpr hi)
  have hh := hm.trans_lt h
  dsimp only [q] at hh
  dsimp only
  unfold proofFailure at hh ⊢
  split_ifs with hb
  · rw [ite_eq_left hb] at hh
    exact False.elim ((lt_irrefl (1 : ℝ)) hh)
  · rfl

end OracleTemplate.RobustGeneralized
