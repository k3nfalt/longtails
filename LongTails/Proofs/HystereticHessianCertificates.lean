import LongTails.Proofs.HystereticHessianExpectation
import LongTails.Proofs.HystereticHessianConcentration
import LongTails.Proofs.HystereticHessianTracking

open MeasureTheory
open scoped LongTails.Proofs.HystereticHessianMeasurable

namespace LongTails.Proofs.HystereticHessianCertificates

open OracleTemplate.StochasticGeneralized

noncomputable def flaggedNext {S Ω : Type*}
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (bad : (n : ℕ) → S → (Fin n → Ω) → Bool)
    (n : ℕ) (s : S × Bool) (w : Fin n → Ω) : S × Bool :=
  (next n s.1 w, s.2 || bad n s.1 w)

def flagValue {S : Type*} (s : S × Bool) : ℝ := if s.2 then 1 else 0

lemma measurable_flaggedNext {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (bad : (n : ℕ) → S → (Fin n → Ω) → Bool)
    (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hb : ∀ n, Measurable (Function.uncurry (bad n))) (n : ℕ) :
    Measurable (Function.uncurry (flaggedNext next bad n)) := by
  have hp : Measurable (fun w : (S × Bool) × (Fin n → Ω) => (w.1.1, w.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  exact ((hn n).comp hp).prodMk
    ((measurable_of_countable (fun b : Bool × Bool => b.1 || b.2)).comp
      ((measurable_snd.comp measurable_fst).prodMk ((hb n).comp hp)))

lemma measurable_flagValue {S : Type*} [MeasurableSpace S] :
    Measurable (flagValue (S := S)) :=
  (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp measurable_snd

lemma flagValue_nonneg {S : Type*} (s : S × Bool) : 0 ≤ flagValue s := by
  unfold flagValue
  split_ifs <;> norm_num

lemma adaptive_flag_probability {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (bad : (n : ℕ) → S → (Fin n → Ω) → Bool)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hb : ∀ n, Measurable (Function.uncurry (bad n))) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprob : ∀ s, (Measure.pi fun _ : Fin (cost s) => P).real {w | bad (cost s) s w = true} ≤ δ)
    (s : S) (K : ℕ) :
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | (blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) (s, false) ξ K).1.2 = true} ≤
        (K : ℝ) * δ := by
  have hsection (t : S) : MeasurableSet {w : Fin (cost t) → Ω | bad (cost t) t w = true} :=
    (measurableSet_singleton true).preimage ((hb (cost t)).comp (measurable_const.prodMk measurable_id))
  have hfalse (t : S) : (fun w => flagValue (flaggedNext next bad (cost t) (t, false) w)) =
      {w | bad (cost t) t w = true}.indicator (fun _ => (1 : ℝ)) := by
    funext w
    simp [flagValue, flaggedNext, Set.indicator_apply]
  have hi (t : S × Bool) : Integrable
      (fun w => flagValue (flaggedNext next bad (cost t.1) t w))
      (Measure.pi fun _ : Fin (cost t.1) => P) := by
    rcases t with ⟨t, b⟩
    cases b with
    | false =>
      dsimp only
      rw [hfalse]
      exact (integrable_const (1 : ℝ)).indicator (hsection t)
    | true => simp [flaggedNext, flagValue]
  have hd (t : S × Bool) :
      (∫ w, flagValue (flaggedNext next bad (cost t.1) t w) ∂Measure.pi (fun _ : Fin (cost t.1) => P)) ≤
        flagValue t + δ := by
    rcases t with ⟨t, b⟩
    cases b with
    | false =>
      dsimp only
      rw [hfalse, integral_indicator_const (1 : ℝ) (hsection t)]
      simpa [flagValue] using hprob t
    | true => simpa [flaggedNext, flagValue] using hδ
  have hh := HystereticHessianMoments.adaptive_potential_drift P (hc.comp measurable_fst)
    (measurable_flaggedNext next bad hn hb) measurable_flagValue flagValue_nonneg hi hd K (s, false)
  have htrace : Measurable (fun ξ : ℕ → Ω =>
      blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) (s, false) ξ K) :=
    (OracleTemplate.ClippedExtragradient.measurable_blockTrace
    (hc.comp measurable_fst) (measurable_flaggedNext next bad hn hb) K).comp
      (measurable_const.prodMk measurable_id)
  have hflag : Measurable (fun ξ =>
      (blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) (s, false) ξ K).1.2) :=
    measurable_snd.comp (measurable_fst.comp htrace)
  have hA : MeasurableSet {ξ | (blockTrace (fun t : S × Bool => cost t.1)
      (flaggedNext next bad) (s, false) ξ K).1.2 = true} :=
    (measurableSet_singleton true).preimage hflag
  have heq : (fun ξ => flagValue
      (blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) (s, false) ξ K).1) =
      {ξ | (blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) (s, false) ξ K).1.2 = true}.indicator
        (fun _ => (1 : ℝ)) := by
    funext ξ
    simp [flagValue, Set.indicator_apply]
  have hresult := hh.2
  change (∫ ξ, flagValue (blockTrace (fun t : S × Bool => cost t.1)
    (flaggedNext next bad) (s, false) ξ K).1 ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      flagValue (s, false) + (K : ℝ) * δ at hresult
  rw [heq, integral_indicator_const (1 : ℝ) hA] at hresult
  simpa [flagValue] using hresult

lemma flagged_trace_projection {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (bad : (n : ℕ) → S → (Fin n → Ω) → Bool)
    (s : S × Bool) (ξ : ℕ → Ω) (K : ℕ) :
    let t := blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) s ξ K
    (t.1.1, t.2) = blockTrace cost next s.1 ξ K := by
  dsimp only
  induction K generalizing s ξ with
  | zero => rfl
  | succ K ih =>
    rw [blockTrace_start_succ, blockTrace_start_succ]
    exact ih (flaggedNext next bad (cost s.1) s (fun i => ξ i)) (fun i => ξ (cost s.1 + i))

noncomputable def blockBad {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (bad : (n : ℕ) → S → (Fin n → Ω) → Bool) (s : S) (ξ : ℕ → Ω) (k : ℕ) : Bool :=
  let t := blockTrace cost next s ξ k
  bad (cost t.1) t.1 (fun i => t.2 i)

lemma flagged_trace_succ {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (bad : (n : ℕ) → S → (Fin n → Ω) → Bool)
    (s : S × Bool) (ξ : ℕ → Ω) (K : ℕ) :
    (blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) s ξ (K + 1)).1.2 =
      ((blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) s ξ K).1.2 ||
        blockBad cost next bad s.1 ξ K) := by
  have hp := flagged_trace_projection cost next bad s ξ K
  have hv := congrArg (fun t : S × (ℕ → Ω) => bad (cost t.1) t.1 (fun i => t.2 i)) hp
  rw [blockTrace_succ]
  exact congrArg (fun b =>
    (blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) s ξ K).1.2 || b) hv

lemma flagged_trace_false_iff {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (bad : (n : ℕ) → S → (Fin n → Ω) → Bool)
    (s : S × Bool) (ξ : ℕ → Ω) (K : ℕ) :
    (blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) s ξ K).1.2 = false ↔
      s.2 = false ∧ ∀ k < K, blockBad cost next bad s.1 ξ k = false := by
  induction K with
  | zero => simp [blockTrace_zero]
  | succ K ih =>
    rw [flagged_trace_succ, Bool.or_eq_false_iff, ih]
    constructor
    · rintro ⟨⟨hs, hprev⟩, hlast⟩
      refine ⟨hs, ?_⟩
      intro k hk
      by_cases he : k = K
      · simpa [he] using hlast
      · exact hprev k (by omega)
    · rintro ⟨hs, hall⟩
      exact ⟨⟨hs, fun k hk => hall k (by omega)⟩, hall K (by omega)⟩

lemma adaptive_block_failure_probability {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (bad : (n : ℕ) → S → (Fin n → Ω) → Bool)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hb : ∀ n, Measurable (Function.uncurry (bad n))) {δ : ℝ} (hδ : 0 ≤ δ)
    (hprob : ∀ s, (Measure.pi fun _ : Fin (cost s) => P).real {w | bad (cost s) s w = true} ≤ δ)
    (s : S) (K : ℕ) :
    (Measure.infinitePi fun _ : ℕ => P).real {ξ | ∃ k < K, blockBad cost next bad s ξ k = true} ≤
      (K : ℝ) * δ := by
  have heq : {ξ | (blockTrace (fun t : S × Bool => cost t.1) (flaggedNext next bad) (s, false) ξ K).1.2 = true} =
      {ξ | ∃ k < K, blockBad cost next bad s ξ k = true} := by
    ext ξ
    have hh := not_congr (flagged_trace_false_iff cost next bad (s, false) ξ K)
    simpa only [Bool.not_eq_false, eq_self, true_and, not_forall, not_imp,
      exists_prop, Set.mem_ofPred_eq] using hh
  rw [← heq]
  exact adaptive_flag_probability P cost next bad hc hn hb hδ hprob s K

noncomputable def finiteMedoid {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Ω → E) (groups B n : ℕ) (w : Fin n → Ω) : E :=
  OracleTemplate.MultiplicativeRobustEstimator.medoid (fun j : Fin (groups + 1) =>
    (B : ℝ)⁻¹ • ∑ k ∈ Finset.range B,
      if h : j.val * B + k < n then X (w ⟨j.val * B + k, h⟩) else 0)

lemma measurable_finiteMedoid {E Ω Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] [MeasurableSpace Y] (X : Y → Ω → E)
    (hX : Measurable (Function.uncurry X)) (groups B n : ℕ) :
    Measurable (fun w : Y × (Fin n → Ω) => finiteMedoid (X w.1) groups B n w.2) := by
  apply OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
  apply Measurable.of_eval
  intro j
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro k _
  by_cases h : j.val * B + k < n
  · simp only [h, dite_true]
    exact hX.comp (measurable_fst.prodMk ((measurable_pi_apply (⟨j.val * B + k, h⟩ : Fin n)).comp measurable_snd))
  · simp only [h, dite_false]
    exact measurable_const

lemma group_index_lt (groups B : ℕ) (j : Fin (groups + 1)) {k : ℕ} (hk : k < B) :
    j.val * B + k < (groups + 1) * B := by
  calc
    j.val * B + k < j.val * B + B := Nat.add_lt_add_left hk _
    _ = (j.val + 1) * B := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ (groups + 1) * B := Nat.mul_le_mul_right _ j.isLt

lemma finiteMedoid_prefix {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Ω → E) (groups B : ℕ) (ξ : ℕ → Ω) :
    finiteMedoid X groups B ((groups + 1) * B) (fun i => ξ i) =
      OracleTemplate.MultiplicativeRobustEstimator.medoid (fun j : Fin (groups + 1) =>
        (B : ℝ)⁻¹ • ∑ k ∈ Finset.range B, X (ξ (j.val * B + k))) := by
  unfold finiteMedoid
  congr 1
  funext j
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [group_index_lt groups B j (Finset.mem_range.mp hk), dite_true]

set_option maxHeartbeats 800000 in
lemma finiteMedoid_failure {E : Type*} {Ω : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → E) (hX : Measurable X) (u : E)
    {q κ r : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (hr : 0 < r)
    (hi : Integrable X P) (hm : (∫ ω, X ω ∂P) = u)
    (hqi : Integrable (fun ω => ‖X ω - u‖ ^ q) P)
    (hqb : (∫ ω, ‖X ω - u‖ ^ q ∂P) ≤ κ)
    (B : ℕ) (hB : 0 < B) (hsize : 6 * κ / (B : ℝ) ^ (q - 1) ≤ (r / 1536) ^ q)
    (groups : ℕ) :
    (Measure.pi fun _ : Fin ((groups + 1) * B) => P).real
      {w | r < ‖finiteMedoid X groups B ((groups + 1) * B) w - u‖} ≤ (1 / 2 : ℝ) ^ (groups + 1) := by
  have hF : Measurable (finiteMedoid X groups B ((groups + 1) * B)) := by
    apply OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
    apply Measurable.of_eval
    intro j
    apply Measurable.const_smul
    apply Finset.measurable_sum
    intro k hk
    have hi := group_index_lt groups B j (Finset.mem_range.mp hk)
    simp only [hi, dite_true]
    exact hX.comp (measurable_pi_apply (⟨j.val * B + k, hi⟩ : Fin ((groups + 1) * B)))
  have hset : MeasurableSet {w : Fin ((groups + 1) * B) → Ω |
      r < ‖finiteMedoid X groups B ((groups + 1) * B) w - u‖} :=
    measurableSet_lt measurable_const ((hF.sub_const u).norm)
  have hpre := prefix_preserving P ((groups + 1) * B)
  have hh := HystereticHessianConcentration.stream_medoid_failure_at_radius
    (Measure.infinitePi fun _ : ℕ => P) (infinitePi_iid P) hX u hq hq2 hr hi hm hqi hqb B hB hsize groups
  have heq : {ξ : ℕ → Ω | r < ‖finiteMedoid X groups B ((groups + 1) * B) (fun i => ξ i) - u‖} =
      {ξ : ℕ → Ω | r < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
        (fun j : Fin (groups + 1) => (B : ℝ)⁻¹ • ∑ k ∈ Finset.range B, X (ξ (j.val * B + k))) - u‖} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, finiteMedoid_prefix X groups B ξ]
  have hp : (Measure.pi fun _ : Fin ((groups + 1) * B) => P)
      {w | r < ‖finiteMedoid X groups B ((groups + 1) * B) w - u‖} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (groups + 1)) := by
    rw [← hpre.measure_preimage hset.nullMeasurableSet]
    simpa only [Set.preimage_ofPred_eq, heq] using hh
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
  simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (groups + 1))] using ht

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianMeasurable HystereticHessianAnchorBlocks HystereticHessianBlocks HystereticHessianMoments

noncomputable def gradientFailure (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (a : ℝ) (n : ℕ) (refresh : Bool) (x : Space p) (w : Fin n → ℝ × Ω) : Bool := by
  classical
  exact if refresh then
    if ‖g x‖ ≤ 4 * c.radius then
      if a < ‖finiteMedoid (fun z : ℝ × Ω => answer (x, none) z.2)
        c.groups (c.resetBatch + 1) n w - g x‖ then true else false
    else false
  else if (c.radius + ‖g x‖) / 256 < ‖finiteMedoid (fun z : ℝ × Ω => answer (x, none) z.2)
    c.groups (c.pilotBatch + 1) n w - g x‖ then true else false

lemma measurable_gradientFailure (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (a : ℝ) (n : ℕ) (refresh : Bool) :
    Measurable (Function.uncurry (gradientFailure p c answer g a n refresh)) := by
  have hX : Measurable (Function.uncurry (fun x (z : ℝ × Ω) => answer (x, none) z.2)) :=
    ha.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd.snd)
  have hmed (B : ℕ) := measurable_finiteMedoid (fun x (z : ℝ × Ω) => answer (x, none) z.2)
    hX c.groups B n
  have hgrad : Measurable (fun w : Space p × (Fin n → ℝ × Ω) => g w.1) := hg.comp measurable_fst
  cases refresh with
  | false =>
    unfold gradientFailure
    simp only [Bool.false_eq_true, ite_false]
    apply Measurable.ite (measurableSet_lt ((measurable_const.add hgrad.norm).div_const 256)
      ((hmed (c.pilotBatch + 1)).sub hgrad).norm) <;> exact measurable_const
  | true =>
    unfold gradientFailure
    simp only [ite_true]
    apply Measurable.ite (measurableSet_le hgrad.norm measurable_const)
    · apply Measurable.ite (measurableSet_lt measurable_const ((hmed (c.resetBatch + 1)).sub hgrad).norm) <;>
        exact measurable_const
    · exact measurable_const

noncomputable def phaseFailure (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (a : ℝ) (n : ℕ) (ph : Phase p c) (x : Space p) (w : Fin n → ℝ × Ω) : Bool :=
  match ph with
  | .gradient refresh _ _ _ _ => gradientFailure p c answer g a n refresh x w
  | _ => false

lemma measurable_phaseFailure (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (a : ℝ) (n : ℕ) :
    Measurable (fun w : Phase p c × (Space p × (Fin n → ℝ × Ω)) =>
      phaseFailure p c answer g a n w.1 w.2.1 w.2.2) := by
  apply measurable_phase_uncurry p c (F := fun ph (w : Space p × (Fin n → ℝ × Ω)) =>
    phaseFailure p c answer g a n ph w.1 w.2)
  · have hm : Measurable (fun w : Bool × (Space p × (Fin n → ℝ × Ω)) =>
        gradientFailure p c answer g a n w.1 w.2.1 w.2.2) :=
      measurable_from_prod_countable_right (fun refresh => measurable_gradientFailure p c answer ha g hg a n refresh)
    exact hm.comp (measurable_fst.fst.prodMk measurable_snd)
  · exact measurable_const
  · exact measurable_const

noncomputable def gradientBlockBad (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (a : ℝ) (n : ℕ) (s : AnchoredTimedState p c) (w : Fin n → ℝ × Ω) : Bool := by
  classical
  exact if n = anchoredTimedCost p c s ∧ s.2 < trialCalls c ∧ s.1.value.active = true then
    phaseFailure p c answer g a n s.1.value.phase s.1.value.point w
  else false

lemma measurable_gradientBlockBad (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (a : ℝ) (n : ℕ) : Measurable (Function.uncurry (gradientBlockBad p c answer g a n)) := by
  unfold gradientBlockBad
  apply Measurable.ite
    ((measurableSet_eq_fun measurable_const ((measurable_anchoredTimedCost p c).comp measurable_fst)).inter
      ((measurableSet_lt measurable_fst.snd measurable_const).inter
        (measurableSet_eq_fun ((measurable_active p c).comp
          ((measurable_value p c).comp measurable_fst.fst)) measurable_const)))
  · apply (measurable_phaseFailure p c answer ha g hg a n).comp
      (f := fun w : AnchoredTimedState p c × (Fin n → ℝ × Ω) =>
        (w.1.1.value.phase, w.1.1.value.point, w.2))
    exact ((measurable_phase p c).comp ((measurable_value p c).comp measurable_fst.fst)).prodMk
      (((measurable_point p c).comp ((measurable_value p c).comp measurable_fst.fst)).prodMk measurable_snd)
  · exact measurable_const

lemma gradientBlockBad_horizon (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (a : ℝ) (n : ℕ) (s : AnchoredTimedState p c) (w : Fin n → ℝ × Ω)
    (ht : trialCalls c ≤ s.2) : gradientBlockBad p c answer g a n s w = false := by
  simp [gradientBlockBad, not_lt.mpr ht]

lemma gradientBlockBad_inactive (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (a : ℝ) (n : ℕ) (s : AnchoredTimedState p c) (w : Fin n → ℝ × Ω)
    (ha : s.1.value.active = false) : gradientBlockBad p c answer g a n s w = false := by
  simp [gradientBlockBad, ha]

lemma gradientBlockBad_offcost (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (a : ℝ) (n : ℕ) (s : AnchoredTimedState p c) (w : Fin n → ℝ × Ω)
    (hn : n ≠ anchoredTimedCost p c s) : gradientBlockBad p c answer g a n s w = false := by
  simp [gradientBlockBad, hn]

lemma gradient_block_failure_probability (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hU : 0 < c.radius) {a : ℝ} (ha0 : 0 < a)
    (hi : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (hm : ∀ x, (∫ z, answer (x, none) z.2 ∂P) = g x)
    (hpi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ z : ℝ × Ω, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hpilot : ∀ x, 6 * (p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p) /
      ((c.pilotBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (((c.radius + ‖g x‖) / 256) / 1536) ^ p.p)
    (hreset : ∀ x, ‖g x‖ ≤ 4 * c.radius →
      6 * (p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p) /
        ((c.resetBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (a / 1536) ^ p.p)
    (M : ℝ) (s : AnchoredTimedState p c) (hs : BlockValid p c g M s) :
    (Measure.pi fun _ : Fin (anchoredTimedCost p c s) => P).real
      {w | gradientBlockBad p c answer g a (anchoredTimedCost p c s) s w = true} ≤
        (1 / 2 : ℝ) ^ (c.groups + 1) := by
  by_cases ht : s.2 < trialCalls c
  · by_cases hactive : s.1.value.active = true
    · cases hphase : s.1.value.phase with
      | padding => simp [gradientBlockBad, ht, hactive, hphase, phaseFailure]
      | transport i sum => simp [gradientBlockBad, ht, hactive, hphase, phaseFailure]
      | gradient refresh j i sum values =>
        have hfr := hs.1.2.2.1 hactive
        have hinit : j.val = 0 ∧ i = 0 ∧ sum = 0 ∧ values = fun _ => 0 := by
          simpa only [forgetAnchor, hphase] using hfr
        have hj : j = 0 := Fin.ext hinit.1
        subst j
        rcases hinit with ⟨_, rfl, rfl, rfl⟩
        have hcost : anchoredTimedCost p c s =
            (c.groups + 1) * ((if refresh then c.resetBatch else c.pilotBatch) + 1) := by
          simp [anchoredTimedCost, timedCost, forgetAnchor, ht, phaseCalls, hactive, hphase,
            HystereticHessianPhases.batchRemaining_initial]
        rw [hcost]
        have hX : Measurable (fun z : ℝ × Ω => answer (s.1.value.point, none) z.2) :=
          ha.comp (measurable_const.prodMk measurable_snd)
        cases refresh with
        | false =>
          simp only [Bool.false_eq_true, ite_false] at hcost
          have hh := finiteMedoid_failure P (fun z : ℝ × Ω => answer (s.1.value.point, none) z.2)
            hX (g s.1.value.point) hp hp2
            (by positivity : 0 < (c.radius + ‖g s.1.value.point‖) / 256)
            (hi _) (hm _) (hpi _) (hb _) (c.pilotBatch + 1) (by omega) (hpilot _) c.groups
          simpa [gradientBlockBad, hcost, ht, hactive, hphase, phaseFailure, gradientFailure] using hh
        | true =>
          simp only [ite_true] at hcost
          by_cases hlocal : ‖g s.1.value.point‖ ≤ 4 * c.radius
          · have hh := finiteMedoid_failure P (fun z : ℝ × Ω => answer (s.1.value.point, none) z.2)
              hX (g s.1.value.point) hp hp2 ha0 (hi _) (hm _) (hpi _) (hb _)
              (c.resetBatch + 1) (by omega) (hreset _ hlocal) c.groups
            simpa [gradientBlockBad, hcost, ht, hactive, hphase, phaseFailure, gradientFailure, hlocal] using hh
          · simp [gradientBlockBad, ht, hactive, hphase, phaseFailure, gradientFailure, hlocal]
    · have hh : s.1.value.active = false := Bool.eq_false_iff.mpr hactive
      simp [gradientBlockBad, hh]
  · simp [gradientBlockBad, ht]

lemma adaptive_gradient_block_probability (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hU : 0 < c.radius) {a : ℝ} (ha0 : 0 < a)
    (hi : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (hm : ∀ x, (∫ z, answer (x, none) z.2 ∂P) = g x)
    (hpi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ z : ℝ × Ω, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hpilot : ∀ x, 6 * (p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p) /
      ((c.pilotBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (((c.radius + ‖g x‖) / 256) / 1536) ^ p.p)
    (hreset : ∀ x, ‖g x‖ ≤ 4 * c.radius →
      6 * (p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p) /
        ((c.resetBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (a / 1536) ^ p.p)
    (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ t : State p c, ‖g (t.point + fineDisplacement p c t)‖ ≤ 2 * max ‖g t.point‖ M)
    (s : BlockState p c g M) (K : ℕ) :
    let cost := fun t : BlockState p c g M => anchoredTimedCost p c t.val
    let next := blockNext p c answer g M hcoarse hfine
    let bad := fun n (t : BlockState p c g M) w => gradientBlockBad p c answer g a n t.val w
    (Measure.infinitePi fun _ : ℕ => P).real {ξ | ∃ k < K, blockBad cost next bad s ξ k = true} ≤
      (K : ℝ) * (1 / 2 : ℝ) ^ (c.groups + 1) := by
  intro cost next bad
  have hc : Measurable cost := (measurable_anchoredTimedCost p c).comp measurable_subtype_coe
  have hn (n : ℕ) : Measurable (Function.uncurry (next n)) :=
    measurable_blockNext p c answer ha g M hcoarse hfine n
  have hbad (n : ℕ) : Measurable (Function.uncurry (bad n)) :=
    (measurable_gradientBlockBad p c answer ha g hg a n).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  apply adaptive_block_failure_probability P cost next bad hc hn hbad (by positivity)
  intro t
  exact gradient_block_failure_probability p c P answer ha g hp hp2 hU ha0 hi hm hpi hb
    hpilot hreset M t.val t.property

lemma gradient_frame (p : Params) (c : Config) (s : State p c)
    (refresh : Bool) {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (j i : ℕ) (hj : j ≤ c.groups)
    (hi : i ≤ if refresh then c.resetBatch else c.pilotBatch) (ha : s.active = true)
    (ht : s.slot + (c.groups + 1) * ((if refresh then c.resetBatch else c.pilotBatch) + 1) <
      macroCalls c) :
    path p c answer { s with phase := .gradient refresh 0 0 0 (fun _ => 0) } ξ
      (j * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + i) =
      { s with
        slot := s.slot + (j * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + i)
        phase := .gradient refresh ⟨j, by omega⟩ i
          (∑ k ∈ Finset.range i, answer (s.point, none)
            (ξ (j * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + k)).2)
          (fun k => if k.val < j then
            (((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
              ∑ l ∈ Finset.range ((if refresh then c.resetBatch else c.pilotBatch) + 1),
                answer (s.point, none)
                  (ξ (k.val * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + l)).2
            else 0) } := by
  let b := if refresh then c.resetBatch else c.pilotBatch
  have hmul : (j + 1) * (b + 1) ≤ (c.groups + 1) * (b + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  change i ≤ b at hi
  change s.slot + (c.groups + 1) * (b + 1) < macroCalls c at ht
  simp only [Nat.add_mul, Nat.one_mul] at hmul ht
  have hbefore : s.slot + j * (b + 1) < macroCalls c := by omega
  have hframe : s.slot + j * (b + 1) + i < macroCalls c := by omega
  rw [path_add, gradient_groups_prefix p c s refresh answer ξ j hj ha hbefore]
  rw [gradient_prefix p c { s with slot := s.slot + j * (b + 1) }
    refresh ⟨j, by omega⟩ _ answer _ i ha hi hframe]
  simp only [b, Nat.add_assoc]

lemma final_group_values {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (groups b : ℕ) (X : ℕ → E) :
    Function.update
      (fun k : Fin (groups + 1) => if k.val < groups then
        ((b + 1 : ℕ) : ℝ)⁻¹ • ∑ l ∈ Finset.range (b + 1), X (k.val * (b + 1) + l)
        else 0)
      (⟨groups, by omega⟩ : Fin (groups + 1))
      (((b + 1 : ℕ) : ℝ)⁻¹ •
        ((∑ l ∈ Finset.range b, X (groups * (b + 1) + l)) + X (groups * (b + 1) + b))) =
    (fun k : Fin (groups + 1) =>
      ((b + 1 : ℕ) : ℝ)⁻¹ • ∑ l ∈ Finset.range (b + 1), X (k.val * (b + 1) + l)) := by
  rw [← Finset.sum_range_succ]
  rw [GuardedHessianExecution.prefix_values_update]
  simp only [Fin.is_lt, ite_true]

lemma gradient_phase_completed_value (p : Params) (c : Config) (s : State p c)
    (refresh : Bool) {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + (c.groups + 1) * ((if refresh then c.resetBatch else c.pilotBatch) + 1) <
      macroCalls c) (n : ℕ)
    (hn : n < (c.groups + 1) * ((if refresh then c.resetBatch else c.pilotBatch) + 1))
    (j : Fin (c.groups + 1)) (i : ℕ) (sum : Space p) (values : Fin (c.groups + 1) → Space p)
    (hphase : (path p c answer { s with phase := .gradient refresh 0 0 0 (fun _ => 0) } ξ n).phase =
      .gradient refresh j i sum values)
    (hi : (if refresh then c.resetBatch else c.pilotBatch) ≤ i) (hj : c.groups ≤ j.val) :
    let t := path p c answer { s with phase := .gradient refresh 0 0 0 (fun _ => 0) } ξ n
    t.point = s.point ∧
    OracleTemplate.MultiplicativeRobustEstimator.medoid
      (Function.update values j
        ((((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
          (sum + answer (query p c t (ξ n).1) (ξ n).2))) =
    OracleTemplate.MultiplicativeRobustEstimator.medoid
      (fun k : Fin (c.groups + 1) =>
        (((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
          ∑ l ∈ Finset.range ((if refresh then c.resetBatch else c.pilotBatch) + 1),
            answer (s.point, none)
              (ξ (k.val * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + l)).2) := by
  let b := if refresh then c.resetBatch else c.pilotBatch
  have hjn : n / (b + 1) ≤ c.groups := by
    have hh : n / (b + 1) < c.groups + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hn
    omega
  have hin : n % (b + 1) ≤ b := Nat.le_of_lt_succ (Nat.mod_lt n (by omega))
  have he : n / (b + 1) * (b + 1) + n % (b + 1) = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n (b + 1)
  have hframe := gradient_frame p c s refresh answer ξ (n / (b + 1)) (n % (b + 1)) hjn hin ha ht
  rw [he] at hframe
  rw [hframe] at hphase ⊢
  simp only [Phase.gradient.injEq] at hphase
  rcases hphase with ⟨_, hj', hi', hsum, hvalues⟩
  have hjlast : n / (b + 1) = c.groups := by
    have hh := congrArg Fin.val hj'
    change n / (b + 1) = j.val at hh
    omega
  have hilast : n % (b + 1) = b := by omega
  subst i
  subst sum
  subst values
  subst j
  constructor
  · rfl
  · simp only [query, ha, ite_true]
    simp only [hjlast, hilast]
    have hlast : n = c.groups * (b + 1) + b := by
      simpa only [hjlast, hilast] using he.symm
    simp only [hlast]
    congr 1
    exact final_group_values c.groups b (fun k => answer (s.point, none) (ξ k).2)

lemma pilot_phase_accuracy (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + (c.groups + 1) * (c.pilotBatch + 1) < macroCalls c)
    (hgood : ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
      (fun k : Fin (c.groups + 1) => ((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ •
        ∑ l ∈ Finset.range (c.pilotBatch + 1),
          answer (s.point, none) (ξ (k.val * (c.pilotBatch + 1) + l)).2) - g s.point‖ ≤
            (c.radius + ‖g s.point‖) / 256)
    (n : ℕ) (hn : n < (c.groups + 1) * (c.pilotBatch + 1)) :
    let t := path p c answer { s with phase := .gradient false 0 0 0 (fun _ => 0) } ξ n
    HystereticHessianTransport.PilotReplyAccurate p c g t
      (answer (query p c t (ξ n).1) (ξ n).2) := by
  intro t _ j i sum values hphase hi hj
  have hh := gradient_phase_completed_value p c s false answer ξ ha ht n hn j i sum values hphase hi hj
  change t.point = s.point ∧ _ at hh
  simp only [Bool.false_eq_true, ite_false] at hh
  have hpoint := hh.1
  dsimp only [t] at hpoint ⊢
  rw [hh.2, hpoint]
  exact hgood

lemma refresh_phase_accuracy (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (a : ℝ) (ξ : ℕ → ℝ × Ω) (ha : s.active = true)
    (ht : s.slot + (c.groups + 1) * (c.resetBatch + 1) < macroCalls c)
    (hgood : ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
      (fun k : Fin (c.groups + 1) => ((c.resetBatch + 1 : ℕ) : ℝ)⁻¹ •
        ∑ l ∈ Finset.range (c.resetBatch + 1),
          answer (s.point, none) (ξ (k.val * (c.resetBatch + 1) + l)).2) - g s.point‖ ≤ a)
    (n : ℕ) (hn : n < (c.groups + 1) * (c.resetBatch + 1)) :
    let t := path p c answer { s with phase := .gradient true 0 0 0 (fun _ => 0) } ξ n
    HystereticHessianTracking.RefreshReplyAccurate p c g a t
      (answer (query p c t (ξ n).1) (ξ n).2) := by
  intro t _ j i sum values hphase hi hj
  have hh := gradient_phase_completed_value p c s true answer ξ ha ht n hn j i sum values hphase hi hj
  change t.point = s.point ∧ _ at hh
  simp only [ite_true] at hh
  have hpoint := hh.1
  dsimp only [t] at hpoint ⊢
  rw [hh.2, hpoint]
  exact hgood

lemma fresh_phase_completed_value (p : Params) (c : Config) (s : State p c)
    {Ω : Type} (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (hc : HystereticHessianPhases.CounterValid p c s)
    (hf : HystereticHessianPhases.PhaseFits p c s) (hfr : Fresh p c s)
    (n : ℕ) (hn : n < phaseCalls p c s)
    (ha : (path p c answer s ξ n).active = true)
    (refresh : Bool) (j : Fin (c.groups + 1)) (i : ℕ) (sum : Space p)
    (values : Fin (c.groups + 1) → Space p)
    (hphase : (path p c answer s ξ n).phase = .gradient refresh j i sum values)
    (hi : (if refresh then c.resetBatch else c.pilotBatch) ≤ i) (hj : c.groups ≤ j.val) :
    s.active = true ∧ s.phase = .gradient refresh 0 0 0 (fun _ => 0) ∧
    (path p c answer s ξ n).point = s.point ∧
    OracleTemplate.MultiplicativeRobustEstimator.medoid
      (Function.update values j
        ((((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
          (sum + answer (query p c (path p c answer s ξ n) (ξ n).1) (ξ n).2))) =
    OracleTemplate.MultiplicativeRobustEstimator.medoid
      (fun k : Fin (c.groups + 1) =>
        (((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
          ∑ l ∈ Finset.range ((if refresh then c.resetBatch else c.pilotBatch) + 1),
            answer (s.point, none)
              (ξ (k.val * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + l)).2) := by
  by_cases hs : s.active = true
  · refine ⟨hs, ?_⟩
    have hstart := hfr hs
    cases hp : s.phase with
    | padding =>
      have ht : s.slot + n < macroCalls c := by
        have hslot := hc.1
        simp only [phaseCalls, hs, hp, ite_true] at hn
        omega
      rw [padding_prefix p c s answer ξ n (Or.inr hp) ht] at hphase
      simp [hp] at hphase
    | transport k v =>
      simp only [hp] at hstart
      rcases hstart with ⟨rfl, rfl⟩
      have hn' : n ≤ c.transportBatch := by simpa [phaseCalls, hs, hp] using hn
      have ht := phaseCalls_strict_fit p c s hc hf hs (by simp [hp])
      have hclock : s.slot + n < macroCalls c := by omega
      have he : s = { s with phase := .transport 0 0 } := by cases s; simp_all
      rw [he, transport_prefix p c s answer ξ n hs hn' hclock] at hphase
      simp at hphase
    | gradient r k l v vs =>
      simp only [hp] at hstart
      rcases hstart with ⟨hk, rfl, rfl, rfl⟩
      have hk' : k = 0 := Fin.ext hk
      subst k
      have hcost : phaseCalls p c s = (c.groups + 1) * ((if r then c.resetBatch else c.pilotBatch) + 1) := by
        simp [phaseCalls, hs, hp, HystereticHessianPhases.batchRemaining_initial]
      have ht := phaseCalls_strict_fit p c s hc hf hs (by simp [hp])
      rw [hcost] at ht hn
      have he : s = { s with phase := .gradient r 0 0 0 (fun _ => 0) } := by cases s; simp_all
      let b := if r then c.resetBatch else c.pilotBatch
      have hjn : n / (b + 1) ≤ c.groups := by
        have hh : n / (b + 1) < c.groups + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hn
        omega
      have hin : n % (b + 1) ≤ b := Nat.le_of_lt_succ (Nat.mod_lt n (by omega))
      have hidx : n / (b + 1) * (b + 1) + n % (b + 1) = n := by
        simpa only [Nat.mul_comm] using Nat.div_add_mod n (b + 1)
      have hframe := gradient_frame p c s r answer ξ (n / (b + 1)) (n % (b + 1)) hjn hin hs ht
      rw [hidx, ← he] at hframe
      have hsame : r = refresh := by rw [hframe] at hphase; exact (Phase.gradient.inj hphase).1
      subst r
      refine ⟨rfl, ?_⟩
      have hh := gradient_phase_completed_value p c s refresh answer ξ hs ht n hn j i sum values
        (by simpa only [← he] using hphase) hi hj
      simpa only [← he] using hh
  · have hs' : s.active = false := Bool.eq_false_iff.mpr hs
    have ht : s.slot + n < macroCalls c := by
      have hslot := hc.1
      simp only [phaseCalls, hs', Bool.false_eq_true, ite_false] at hn
      omega
    rw [padding_prefix p c s answer ξ n (Or.inl hs') ht] at ha
    simp [hs'] at ha

lemma good_gradient_block_value (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (a : ℝ) (s : AnchoredTimedState p c) (ξ : ℕ → ℝ × Ω) (refresh : Bool)
    (ht : s.2 < trialCalls c) (ha : s.1.value.active = true)
    (hphase : s.1.value.phase = .gradient refresh 0 0 0 (fun _ => 0))
    (hlocal : refresh = true → ‖g s.1.value.point‖ ≤ 4 * c.radius)
    (hgood : gradientBlockBad p c answer g a (anchoredTimedCost p c s) s (fun i => ξ i) = false) :
    ‖OracleTemplate.MultiplicativeRobustEstimator.medoid
      (fun k : Fin (c.groups + 1) =>
        (((if refresh then c.resetBatch else c.pilotBatch) + 1 : ℕ) : ℝ)⁻¹ •
          ∑ l ∈ Finset.range ((if refresh then c.resetBatch else c.pilotBatch) + 1),
            answer (s.1.value.point, none)
              (ξ (k.val * ((if refresh then c.resetBatch else c.pilotBatch) + 1) + l)).2) -
        g s.1.value.point‖ ≤ if refresh then a else (c.radius + ‖g s.1.value.point‖) / 256 := by
  have hcost : anchoredTimedCost p c s =
      (c.groups + 1) * ((if refresh then c.resetBatch else c.pilotBatch) + 1) := by
    simp [anchoredTimedCost, timedCost, forgetAnchor, ht, phaseCalls, ha, hphase,
      HystereticHessianPhases.batchRemaining_initial]
  simp only [gradientBlockBad, ht, ha, and_self, ite_true, hphase, phaseFailure] at hgood
  cases refresh with
  | false =>
    simp only [gradientFailure, Bool.false_eq_true, ite_false] at hgood ⊢
    simp only [Bool.false_eq_true, ite_false] at hcost
    rw [hcost] at hgood
    simp only [finiteMedoid_prefix] at hgood
    split_ifs at hgood with hh
    exact le_of_not_gt hh
  | true =>
    have hl := hlocal rfl
    simp only [gradientFailure, ite_true, hl] at hgood ⊢
    simp only [ite_true] at hcost
    rw [hcost] at hgood
    simp only [finiteMedoid_prefix] at hgood
    split_ifs at hgood with hh
    exact le_of_not_gt hh

lemma good_gradient_block_pilot (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (a : ℝ) (s : AnchoredTimedState p c) (ξ : ℕ → ℝ × Ω)
    (hs : TimedValid p c (forgetAnchor p c s))
    (hgood : gradientBlockBad p c answer g a (anchoredTimedCost p c s) s (fun i => ξ i) = false)
    (n : ℕ) (hn : n < anchoredTimedCost p c s) :
    let t := path p c answer s.1.value ξ n
    HystereticHessianTransport.PilotReplyAccurate p c g t
      (answer (query p c t (ξ n).1) (ξ n).2) := by
  have ht : s.2 < trialCalls c := by
    by_contra hh
    simp [anchoredTimedCost, timedCost, forgetAnchor, hh] at hn
  have hcost : anchoredTimedCost p c s = phaseCalls p c s.1.value := by
    simp [anchoredTimedCost, timedCost, forgetAnchor, ht]
  rw [hcost] at hn
  intro t ha j i sum values hphase hi hj
  have hh := fresh_phase_completed_value p c s.1.value answer ξ hs.1 hs.2.1 hs.2.2.1
    n hn ha false j i sum values hphase hi hj
  have hv := good_gradient_block_value p c answer g a s ξ false ht hh.1 hh.2.1 (by simp) hgood
  simp only [Bool.false_eq_true, ite_false] at hh hv
  dsimp only [t]
  rw [hh.2.2.2, hh.2.2.1]
  exact hv

lemma good_gradient_block_refresh (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (a : ℝ) (s : AnchoredTimedState p c) (ξ : ℕ → ℝ × Ω)
    (hs : TimedValid p c (forgetAnchor p c s))
    (hl : HystereticHessianTransport.LocalTransport p c g s.1.value)
    (hgood : gradientBlockBad p c answer g a (anchoredTimedCost p c s) s (fun i => ξ i) = false)
    (n : ℕ) (hn : n < anchoredTimedCost p c s) :
    let t := path p c answer s.1.value ξ n
    HystereticHessianTracking.RefreshReplyAccurate p c g a t
      (answer (query p c t (ξ n).1) (ξ n).2) := by
  have ht : s.2 < trialCalls c := by
    by_contra hh
    simp [anchoredTimedCost, timedCost, forgetAnchor, hh] at hn
  have hcost : anchoredTimedCost p c s = phaseCalls p c s.1.value := by
    simp [anchoredTimedCost, timedCost, forgetAnchor, ht]
  rw [hcost] at hn
  intro t ha j i sum values hphase hi hj
  have hh := fresh_phase_completed_value p c s.1.value answer ξ hs.1 hs.2.1 hs.2.2.1
    n hn ha true j i sum values hphase hi hj
  have hlocal : ‖g s.1.value.point‖ ≤ 4 * c.radius := by
    simpa only [HystereticHessianTransport.LocalTransport, hh.2.1] using hl hh.1
  have hv := good_gradient_block_value p c answer g a s ξ true ht hh.1 hh.2.1 (fun _ => hlocal) hgood
  simp only [ite_true] at hh hv
  dsimp only [t]
  rw [hh.2.2.2, hh.2.2.1]
  exact hv

lemma block_interval_cover {S Ω : Type*} (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S) (s : S) (ξ : ℕ → Ω)
    (K n : ℕ) (hn : n < blockCalls cost next s ξ K) :
    ∃ k < K, ∃ i < cost (blockTrace cost next s ξ k).1,
      n = blockCalls cost next s ξ k + i := by
  induction K with
  | zero => simp [blockCalls] at hn
  | succ K ih =>
    rw [blockCalls_succ] at hn
    by_cases hprev : n < blockCalls cost next s ξ K
    · rcases ih hprev with ⟨k, hk, i, hi, he⟩
      exact ⟨k, by omega, i, hi, he⟩
    · exact ⟨K, by omega, n - blockCalls cost next s ξ K, by omega, by omega⟩

lemma valid_block_calls_projection (p : Params) (c : Config) {Ω : Type} [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ t : State p c,
      ‖g (t.point + fineDisplacement p c t)‖ ≤ 2 * max ‖g t.point‖ M)
    (s : BlockState p c g M) (ξ : ℕ → ℝ × Ω) (k : ℕ) :
    blockCalls (fun t : BlockState p c g M => anchoredTimedCost p c t.val)
      (blockNext p c answer g M hcoarse hfine) s ξ k =
    blockCalls (anchoredTimedCost p c) (finiteRun (anchoredTimedAdvance p c answer)) s.val ξ k := by
  unfold blockCalls
  apply Finset.sum_congr rfl
  intro i _
  have he := congrArg Prod.fst (valid_block_trace_projection p c answer g M hcoarse hfine s ξ i)
  exact congrArg (anchoredTimedCost p c) he

lemma valid_block_calls_horizon (p : Params) (c : Config) {Ω : Type} [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ t : State p c,
      ‖g (t.point + fineDisplacement p c t)‖ ≤ 2 * max ‖g t.point‖ M)
    (ξ : ℕ → ℝ × Ω) :
    blockCalls (fun t : BlockState p c g M => anchoredTimedCost p c t.val)
      (blockNext p c answer g M hcoarse hfine)
      ⟨(⟨initial p c, p.x0⟩, 0), initial_block_valid p c g M⟩ ξ (blockCap c) = trialCalls c := by
  rw [valid_block_calls_projection]
  have hh := anchored_timed_trace_horizon p c answer ξ
  rw [blockTrace_eq_trajectory, anchored_timed_trajectory] at hh
  simpa only [Nat.zero_add] using hh

lemma valid_block_state_path (p : Params) (c : Config) {Ω : Type} [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ t : State p c,
      ‖g (t.point + fineDisplacement p c t)‖ ≤ 2 * max ‖g t.point‖ M)
    (s : BlockState p c g M) (ξ : ℕ → ℝ × Ω) (k : ℕ) :
    let cost := fun t : BlockState p c g M => anchoredTimedCost p c t.val
    let next := blockNext p c answer g M hcoarse hfine
    (blockTrace cost next s ξ k).1.val.1.value =
      path p c answer s.val.1.value ξ (blockCalls cost next s ξ k) := by
  dsimp only
  have he := congrArg (fun t => t.1.1.value)
    (valid_block_trace_projection p c answer g M hcoarse hfine s ξ k)
  rw [blockTrace_eq_trajectory, anchored_timed_trajectory, anchoredPath_projection] at he
  rw [valid_block_calls_projection]
  exact he

lemma valid_block_frame_path (p : Params) (c : Config) {Ω : Type} [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ t : State p c,
      ‖g (t.point + fineDisplacement p c t)‖ ≤ 2 * max ‖g t.point‖ M)
    (s : BlockState p c g M) (ξ : ℕ → ℝ × Ω) (k i : ℕ) :
    let cost := fun t : BlockState p c g M => anchoredTimedCost p c t.val
    let next := blockNext p c answer g M hcoarse hfine
    let t := blockTrace cost next s ξ k
    path p c answer t.1.val.1.value t.2 i =
      path p c answer s.val.1.value ξ (blockCalls cost next s ξ k + i) := by
  dsimp only
  rw [path_add, valid_block_state_path]
  congr 1
  funext j
  exact blockTrace_tail _ _ _ _ _ _

lemma good_blocks_pilot_accuracy (p : Params) (c : Config) {Ω : Type} [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M a : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ t : State p c,
      ‖g (t.point + fineDisplacement p c t)‖ ≤ 2 * max ‖g t.point‖ M)
    (ξ : ℕ → ℝ × Ω) :
    let cost := fun t : BlockState p c g M => anchoredTimedCost p c t.val
    let next := blockNext p c answer g M hcoarse hfine
    let bad := fun n (t : BlockState p c g M) w => gradientBlockBad p c answer g a n t.val w
    let start : BlockState p c g M := ⟨(⟨initial p c, p.x0⟩, 0), initial_block_valid p c g M⟩
    (∀ k < blockCap c, blockBad cost next bad start ξ k = false) →
    ∀ n < trialCalls c, HystereticHessianTransport.PilotReplyAccurate p c g
      (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2) := by
  intro cost next bad start hgood n hn
  have hhorizon : blockCalls cost next start ξ (blockCap c) = trialCalls c :=
    valid_block_calls_horizon p c answer g M hcoarse hfine ξ
  rcases block_interval_cover cost next start ξ (blockCap c) n (by omega) with ⟨k, hk, i, hi, he⟩
  let t := blockTrace cost next start ξ k
  have hbad : gradientBlockBad p c answer g a (anchoredTimedCost p c t.1.val) t.1.val
      (fun j => t.2 j) = false := hgood k hk
  have hh := good_gradient_block_pilot p c answer g a t.1.val t.2 t.1.property.1 hbad i hi
  have hframe := valid_block_frame_path p c answer g M hcoarse hfine start ξ k i
  change path p c answer t.1.val.1.value t.2 i =
    path p c answer (initial p c) ξ (blockCalls cost next start ξ k + i) at hframe
  have hsample : t.2 i = ξ (blockCalls cost next start ξ k + i) := blockTrace_tail _ _ _ _ _ _
  dsimp only at hh
  rw [hframe, hsample, ← he] at hh
  exact hh

lemma good_blocks_refresh_accuracy (p : Params) (c : Config) {Ω : Type} [Nonempty Ω]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M a : ℝ) (hU : 0 ≤ c.radius)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ t : State p c,
      ‖g (t.point + fineDisplacement p c t)‖ ≤ 2 * max ‖g t.point‖ M)
    (ξ : ℕ → ℝ × Ω) :
    let cost := fun t : BlockState p c g M => anchoredTimedCost p c t.val
    let next := blockNext p c answer g M hcoarse hfine
    let bad := fun n (t : BlockState p c g M) w => gradientBlockBad p c answer g a n t.val w
    let start : BlockState p c g M := ⟨(⟨initial p c, p.x0⟩, 0), initial_block_valid p c g M⟩
    (∀ k < blockCap c, blockBad cost next bad start ξ k = false) →
    ∀ n < trialCalls c, HystereticHessianTracking.RefreshReplyAccurate p c g a
      (path p c answer (initial p c) ξ n)
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2) := by
  intro cost next bad start hgood n hn
  have hp := good_blocks_pilot_accuracy p c answer g M a hcoarse hfine ξ hgood
  have hhorizon : blockCalls cost next start ξ (blockCap c) = trialCalls c :=
    valid_block_calls_horizon p c answer g M hcoarse hfine ξ
  rcases block_interval_cover cost next start ξ (blockCap c) n (by omega) with ⟨k, hk, i, hi, he⟩
  let t := blockTrace cost next start ξ k
  have hbad : gradientBlockBad p c answer g a (anchoredTimedCost p c t.1.val) t.1.val
      (fun j => t.2 j) = false := hgood k hk
  have hstate := valid_block_state_path p c answer g M hcoarse hfine start ξ k
  change t.1.val.1.value = path p c answer (initial p c) ξ (blockCalls cost next start ξ k) at hstate
  have hl : HystereticHessianTransport.LocalTransport p c g t.1.val.1.value := by
    rw [hstate]
    apply HystereticHessianTransport.path_local_transport p c answer g hU ξ
    intro j hj
    exact hp j (by omega)
  have hh := good_gradient_block_refresh p c answer g a t.1.val t.2 t.1.property.1 hl hbad i hi
  have hframe := valid_block_frame_path p c answer g M hcoarse hfine start ξ k i
  change path p c answer t.1.val.1.value t.2 i =
    path p c answer (initial p c) ξ (blockCalls cost next start ξ k + i) at hframe
  have hsample : t.2 i = ξ (blockCalls cost next start ξ k + i) := blockTrace_tail _ _ _ _ _ _
  dsimp only at hh
  rw [hframe, hsample, ← he] at hh
  exact hh

lemma macro_noise_prefix_of_good (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (Q : Measure (ℝ × Ω)) (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (a : ℝ) (ξ : ℕ → ℝ × Ω) (j : ℕ)
    (hgood : (path p c answer (initial p c) ξ (j * macroCalls c),
      fun k => ξ (j * macroCalls c + k)) ∉ HystereticHessianConcentration.macroBad p c Q answer g a)
    (n : ℕ) (hn : n ≤ macroCalls c) :
    ‖∑ i ∈ Finset.range n, HystereticHessianTransport.transportNoise p c Q answer g
      (path p c answer (initial p c) ξ (j * macroCalls c + i)) (ξ (j * macroCalls c + i))‖ ≤ a := by
  have hs : (path p c answer (initial p c) ξ (j * macroCalls c)).slot = 0 := by
    rw [path_slot]
    simp
  have hh : ¬ a < ‖∑ i ∈ Finset.range n, HystereticHessianTransport.transportNoise p c Q answer g
      (path p c answer (path p c answer (initial p c) ξ (j * macroCalls c))
        (fun k => ξ (j * macroCalls c + k)) i) (ξ (j * macroCalls c + i))‖ := by
    intro h
    exact hgood ⟨n, by simpa only [hs, Nat.sub_zero] using hn, h⟩
  simp_rw [← path_add] at hh
  exact le_of_not_gt hh

lemma good_blocks_tracked_accuracy (p : Params) (c : Config) {Ω : Type}
    [MeasurableSpace Ω] [Nonempty Ω] (Q : Measure (ℝ × Ω))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M a d : ℝ) (hU : 0 ≤ c.radius) (hstep : 0 ≤ c.fineStep)
    (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hb : ∀ t : State p c, ‖HystereticHessianTracking.transportBias p c Q answer g t‖ ≤ d)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ t : State p c,
      ‖g (t.point + fineDisplacement p c t)‖ ≤ 2 * max ‖g t.point‖ M)
    (ξ : ℕ → ℝ × Ω) :
    let cost := fun t : BlockState p c g M => anchoredTimedCost p c t.val
    let next := blockNext p c answer g M hcoarse hfine
    let bad := fun n (t : BlockState p c g M) w => gradientBlockBad p c answer g a n t.val w
    let start : BlockState p c g M := ⟨(⟨initial p c, p.x0⟩, 0), initial_block_valid p c g M⟩
    (∀ k < blockCap c, blockBad cost next bad start ξ k = false) →
    (∀ j < c.macros + 1, (path p c answer (initial p c) ξ (j * macroCalls c),
      fun k => ξ (j * macroCalls c + k)) ∉ HystereticHessianConcentration.macroBad p c Q answer g a) →
    ∀ n < trialCalls c, ‖HystereticHessianTracking.trackedError p c g
      (path p c answer (initial p c) ξ n)‖ ≤
      3 * a + (((c.epoch + 1) * (c.transportBatch + 1) : ℕ) : ℝ) * d := by
  intro cost next bad start hgood hnoise n hn
  have hp := good_blocks_pilot_accuracy p c answer g M a hcoarse hfine ξ hgood
  have hr := good_blocks_refresh_accuracy p c answer g M a hU hcoarse hfine ξ hgood
  have hMC := macroCalls_pos c
  have hj : n / macroCalls c < c.macros + 1 :=
    (Nat.div_lt_iff_lt_mul hMC).mpr hn
  have hi : n % macroCalls c ≤ macroCalls c := (Nat.mod_lt n hMC).le
  have he : n / macroCalls c * macroCalls c + n % macroCalls c = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n (macroCalls c)
  have hh := HystereticHessianTracking.trial_tracked_error_bound p c Q answer g ξ hU hstep ha hd hb
    (n / macroCalls c) (n % macroCalls c) hi
    (fun k hk => hp k (by omega)) (fun k hk => hr k (by omega))
    (fun k hk => macro_noise_prefix_of_good p c Q answer g a ξ _ (hnoise _ hj) k (by omega))
  simpa only [he] using hh

end LongTails.Proofs.HystereticHessianCertificates
