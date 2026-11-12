import LongTails.Proofs.AffineResidualSearch
import LongTails.Proofs.AffineSoftmaxPredictor

namespace LongTails.Proofs.AffineResidualSearchTrace

open MeasureTheory
open LongTails.Algorithms.AffineResidualSearch
open LongTails.Algorithms.AffineSoftmaxEstimator (smoothValue)
open LongTails.Algorithms.CappedProximal (predictor)
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxSearch (searchPlan bisectPlan gridPlan)
open scoped ENNReal
open AffineSoftmaxSearchTrace
open AffineSoftmaxSearchProbability (Active query query_range)

noncomputable def querySet (floor cap : ℝ) : Set ℝ :=
  Set.range (fun q : ℚ × ℚ => (q.1 : ℝ) * floor + (q.2 : ℝ) * cap)

lemma querySet_countable (floor cap : ℝ) : (querySet floor cap).Countable := Set.countable_range _

lemma floor_mem (floor cap : ℝ) : floor ∈ querySet floor cap := by
  refine ⟨(1, 0), ?_⟩
  norm_num

lemma cap_mem (floor cap : ℝ) : cap ∈ querySet floor cap := by
  refine ⟨(0, 1), ?_⟩
  norm_num

lemma midpoint_mem {floor cap x y : ℝ} (hx : x ∈ querySet floor cap) (hy : y ∈ querySet floor cap) :
    (x + y) / 2 ∈ querySet floor cap := by
  rcases hx with ⟨⟨a, b⟩, rfl⟩
  rcases hy with ⟨⟨c, d⟩, rfl⟩
  refine ⟨((a + c) / 2, (b + d) / 2), ?_⟩
  push_cast
  ring

lemma current_mem (floor cap : ℝ) (i : ℕ) : max floor (cap / 2 ^ i) ∈ querySet floor cap := by
  have hc : cap / 2 ^ i ∈ querySet floor cap := by
    refine ⟨(0, 1 / (2 : ℚ) ^ i), ?_⟩
    push_cast
    ring
  by_cases h : floor ≤ cap / 2 ^ i
  · simpa only [max_eq_right h] using hc
  · simpa only [max_eq_left (le_of_not_ge h)] using floor_mem floor cap

lemma step_mem (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H i : ℕ) (s : State)
    (hl : s.2.1 ∈ querySet floor cap) (hu : s.2.2 ∈ querySet floor cap) :
    (step observe r floor cap H i s).2.1 ∈ querySet floor cap ∧
      (step observe r floor cap H i s).2.2 ∈ querySet floor cap := by
  have hc := current_mem floor cap i
  have hm := midpoint_mem hl hu
  unfold step
  dsimp only
  split_ifs <;> try simp only [scan, bracket, done]
  all_goals first
    | exact ⟨cap_mem floor cap, cap_mem floor cap⟩
    | exact ⟨floor_mem floor cap, floor_mem floor cap⟩
    | exact ⟨hc, hl⟩
    | exact ⟨hc, hc⟩
    | exact ⟨hl, hu⟩
    | exact ⟨hl, hm⟩
    | exact ⟨hm, hu⟩
    | exact ⟨hm, hm⟩

lemma trajectory_mem (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H i : ℕ) :
    (trajectory observe r floor cap H i).2.1 ∈ querySet floor cap ∧
      (trajectory observe r floor cap H i).2.2 ∈ querySet floor cap := by
  induction i with
  | zero => exact ⟨cap_mem floor cap, cap_mem floor cap⟩
  | succ i ih => exact step_mem observe r floor cap H i _ ih.1 ih.2

lemma query_mem (observe : ℕ → ℝ → ℝ) (r floor cap : ℝ) (H i : ℕ) :
    AffineSoftmaxSearchProbability.query floor cap i (trajectory observe r floor cap H i) ∈ querySet floor cap := by
  have hh := trajectory_mem observe r floor cap H i
  unfold AffineSoftmaxSearchProbability.query
  split_ifs
  · exact current_mem floor cap i
  · exact midpoint_mem hh.1 hh.2

noncomputable def patched {Ω : Type*} (S : Set ℝ) (observe : Ω → ℝ → ℝ) (fallback : ℝ → ℝ)
    (ω : Ω) (μ : ℝ) : ℝ := by
  classical
  exact if μ ∈ S then observe ω μ else fallback μ

lemma patched_measurable {Ω : Type*} [MeasurableSpace Ω] {S : Set ℝ} (hS : S.Countable)
    (observe : Ω → ℝ → ℝ) (fallback : ℝ → ℝ)
    (ho : ∀ μ, Measurable (fun ω => observe ω μ)) (hf : Measurable fallback) :
    Measurable (Function.uncurry (patched S observe fallback)) := by
  classical
  let : Countable S := hS.to_subtype
  let A : Set (Ω × ℝ) := {z | z.2 ∈ S}
  have hA : MeasurableSet A := hS.measurableSet.preimage measurable_snd
  have hm : Measurable (fun z : Ω × S => observe z.1 z.2) :=
    measurable_from_prod_countable_left (fun μ => ho μ)
  have hleft : Measurable (fun z : A => observe z.val.1 z.val.2) :=
    hm.comp ((measurable_fst.comp measurable_subtype_coe).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk (h := fun z => z.property)))
  have hright : Measurable (fun z : (Aᶜ : Set (Ω × ℝ)) => fallback z.val.2) :=
    hf.comp (measurable_snd.comp measurable_subtype_coe)
  exact hleft.dite hright hA

lemma step_patched {Ω : Type*} (observe : ℕ → Ω → ℝ → ℝ) (fallback : ℝ → ℝ)
    (ξ : ℕ → Ω) (r floor cap : ℝ) (H i : ℕ) (s : State)
    (hl : s.2.1 ∈ querySet floor cap) (hu : s.2.2 ∈ querySet floor cap) :
    step (fun k => patched (querySet floor cap) (observe k) fallback (ξ k)) r floor cap H i s =
      step (fun k => observe k (ξ k)) r floor cap H i s := by
  have hc := current_mem floor cap i
  have hm := midpoint_mem hl hu
  simp only [step, patched, hc, hm, ite_true]

lemma trajectory_patched {Ω : Type*} (observe : ℕ → Ω → ℝ → ℝ) (fallback : ℝ → ℝ)
    (ξ : ℕ → Ω) (r floor cap : ℝ) (H i : ℕ) :
    trajectory (fun k => patched (querySet floor cap) (observe k) fallback (ξ k)) r floor cap H i =
      trajectory (fun k => observe k (ξ k)) r floor cap H i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [trajectory, ih, trajectory]
      have hm := trajectory_mem (fun k => observe k (ξ k)) r floor cap H i
      exact step_patched observe fallback ξ r floor cap H i _ hm.1 hm.2

lemma seeded_trajectory_measurable {Ω : Type*} [MeasurableSpace Ω]
    (observe : ℕ → Ω → ℝ → ℝ) (ho : ∀ i μ, Measurable (fun ω => observe i ω μ))
    (r floor cap : ℝ) (H i : ℕ) :
    Measurable (fun ξ : ℕ → Ω => trajectory (fun k => observe k (ξ k)) r floor cap H i) := by
  have hm k := patched_measurable (querySet_countable floor cap) (observe k) (fun _ => 0)
    (ho k) measurable_const
  have hh := AffineSoftmaxSearchTrace.seeded_trajectory_measurable
    (fun k => patched (querySet floor cap) (observe k) (fun _ => 0)) hm r floor cap H i
  simpa only [trajectory_patched] using hh

lemma searchPlan_measurable {Ω Q R : Type*} [MeasurableSpace Ω]
    (probe : ℕ → Ω → ℝ → Program Q R ℝ) (reply : Q → R)
    (ho : ∀ i μ, Measurable (fun ω => Program.eval reply (probe i ω μ)))
    (r floor cap : ℝ) (H : ℕ) :
    Measurable (fun ξ : ℕ → Ω => Program.eval reply (searchPlan (fun i => probe i (ξ i)) r floor cap H)) := by
  have hh := (seeded_trajectory_measurable (fun i ω μ => Program.eval reply (probe i ω μ))
    ho r floor cap H (2 * H + 9)).snd.fst
  simpa only [trajectory_search_eq, done] using hh

lemma search_bad_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (observe : ℕ → Ω → ℝ → ℝ)
    (ho : ∀ i μ, Measurable (fun ω => observe i ω μ))
    (d : ℝ → ℝ) (hd : Measurable d) (r floor cap : ℝ) (H : ℕ) (hr : 0 ≤ r)
    {p : ℝ} (hp : 0 ≤ p)
    (hprob : ∀ i μ, μ ∈ Set.Icc floor cap →
      (Q : Measure Ω) {ω | r / 64 < |observe i ω μ - min r (d μ)|} ≤ ENNReal.ofReal p) (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)))
      {ξ | ∃ i < n,
        let state := trajectory (fun k => observe k (ξ k)) r floor cap H i
        Active H i state ∧ query floor cap i state ∈ Set.Icc floor cap ∧
          r / 64 < |observe i (ξ i) (query floor cap i state) - min r (d (query floor cap i state))|} ≤
      ENNReal.ofReal ((n : ℝ) * p) := by
  let obs := fun i => patched (querySet floor cap) (observe i) (fun μ => min r (d μ))
  have hm i : Measurable (Function.uncurry (obs i)) :=
    patched_measurable (querySet_countable floor cap) (observe i) _ (ho i) (measurable_const.min hd)
  have hb i μ (hμ : μ ∈ Set.Icc floor cap) :
      (Q : Measure Ω) {ω | r / 64 < |obs i ω μ - min r (d μ)|} ≤ ENNReal.ofReal p := by
    by_cases hs : μ ∈ querySet floor cap
    · simpa only [obs, patched, hs, ite_true] using hprob i μ hμ
    · have hn : ¬r / 64 < 0 := not_lt_of_ge (by positivity)
      simp only [obs, patched, hs, ite_false, sub_self, abs_zero, hn, Set.ofPred_false, measure_empty]
      exact bot_le
  have hh := AffineSoftmaxSearchProbability.search_bad_event_bound Q obs hm d hd r floor cap H hp hb n
  apply le_trans (measure_mono ?_) hh
  intro ξ hξ
  rcases hξ with ⟨i, hi, hbad⟩
  refine ⟨i, hi, ?_⟩
  dsimp only at hbad ⊢
  have hq := query_mem (fun k => observe k (ξ k)) r floor cap H i
  simpa only [obs, trajectory_patched, patched, hq, ite_true] using hbad

lemma searchPlan_failure_bound {Ω Q R : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (probe : ℕ → Ω → ℝ → Program Q R ℝ) (reply : Q → R)
    (ho : ∀ i μ, Measurable (fun ω => Program.eval reply (probe i ω μ)))
    (d : ℝ → ℝ) (hd : Measurable d) {r floor cap K : ℝ} (H : ℕ)
    (hr : 0 < r) (hf : 0 < floor) (hfc : floor ≤ cap) (hK : 0 ≤ K)
    (hcap : d cap ≤ r / 2) (hend : cap / 2 ^ H ≤ floor)
    (hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ K * |x - y| / min x y)
    (hs : K / 2 ^ (H + 7) < r / 64)
    {p : ℝ} (hp : 0 ≤ p)
    (hprob : ∀ i μ, μ ∈ Set.Icc floor cap →
      (P : Measure Ω) {ω | r / 64 < |Program.eval reply (probe i ω μ) - min r (d μ)|} ≤ ENNReal.ofReal p) :
    (Measure.infinitePi (fun _ : ℕ => (P : Measure Ω)))
      {ξ | let answer := Program.eval reply (searchPlan (fun i => probe i (ξ i)) r floor cap H)
        ¬ (answer ∈ Set.Icc floor cap ∧
          ((answer = floor ∧ d answer < r) ∨ (51 * r / 64 ≤ d answer ∧ d answer ≤ 61 * r / 64)))} ≤
      ENNReal.ofReal (((2 * H + 9 : ℕ) : ℝ) * p) := by
  let observe := fun i ω μ => Program.eval reply (probe i ω μ)
  have hb := search_bad_event_bound P observe ho d hd r floor cap H hr.le hp hprob (2 * H + 9)
  apply le_trans (measure_mono ?_) hb
  intro ξ hfail
  by_contra hgood
  apply hfail
  apply AffineSoftmaxSearchGeometry.searchPlan_certificate d (fun i => probe i (ξ i)) reply H
    hr hf hfc hK hcap hend hmod hs
  · intro i hi previous heq
    apply le_of_not_gt
    intro herror
    apply hgood
    refine ⟨i, hi, ?_⟩
    have hrange := trajectory_range (observe := fun k => observe k (ξ k)) r (hf.le.trans hfc) hfc H i
    have hqr := query_range (hf.le.trans hfc) hfc i _ hrange.1 hrange.2
    change trajectory (fun k => observe k (ξ k)) r floor cap H i = scan previous at heq
    rw [heq] at hqr ⊢
    exact ⟨Or.inl rfl, hqr, by simpa only [query, scan, Prod.fst, ite_true, observe] using herror⟩
  · intro i hi lower upper heq hit
    apply le_of_not_gt
    intro herror
    apply hgood
    refine ⟨i, hi, ?_⟩
    have hrange := trajectory_range (observe := fun k => observe k (ξ k)) r (hf.le.trans hfc) hfc H i
    have hqr := query_range (hf.le.trans hfc) hfc i _ hrange.1 hrange.2
    change trajectory (fun k => observe k (ξ k)) r floor cap H i = bracket lower upper at heq
    rw [heq] at hqr ⊢
    refine ⟨Or.inr ⟨rfl, hit⟩, hqr, ?_⟩
    simpa only [query, bracket, Prod.fst, Prod.snd, show ¬ (1 : ℕ) = 0 by decide, ite_false, observe] using herror

lemma bisectPlan_finite_range {Z Q R : Type*} (probe : Z → ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r : ℝ) (n index : ℕ) (lower upper : ℝ) :
    (Set.range (fun z => Program.eval reply (bisectPlan (probe z) r n index lower upper))).Finite := by
  induction n generalizing index lower upper with
  | zero => simpa only [bisectPlan, Program.eval_bind, Program.eval] using
      (Set.finite_range_const (c := (lower + upper) / 2) (α := Z))
  | succ n ih =>
      simp only [bisectPlan, Program.eval_bind, apply_ite (Program.eval reply), Program.eval]
      apply Set.finite_range_ite (ih (index + 1) lower ((lower + upper) / 2))
      exact Set.finite_range_ite (ih (index + 1) ((lower + upper) / 2) upper) Set.finite_range_const

lemma gridPlan_finite_range {Z Q R : Type*} (probe : Z → ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r floor upper : ℝ) (H n index : ℕ) (previous : ℝ) :
    (Set.range (fun z => Program.eval reply (gridPlan (probe z) r floor upper H n index previous))).Finite := by
  induction n generalizing index previous with
  | zero =>
      simp only [gridPlan, Program.eval_bind, apply_ite (Program.eval reply), Program.eval]
      apply Set.finite_range_ite
      · by_cases hi : index = 0
        · simpa only [hi, ite_true, Program.eval] using (Set.finite_range_const (c := upper) (α := Z))
        · simpa only [hi, ite_false] using bisectPlan_finite_range probe reply r (H + 7) (H + 1)
            (max floor (upper / 2 ^ index)) previous
      · exact Set.finite_range_const
  | succ n ih =>
      simp only [gridPlan, Program.eval_bind, apply_ite (Program.eval reply), Program.eval]
      apply Set.finite_range_ite
      · by_cases hi : index = 0
        · simpa only [hi, ite_true, Program.eval] using (Set.finite_range_const (c := upper) (α := Z))
        · simpa only [hi, ite_false] using bisectPlan_finite_range probe reply r (H + 7) (H + 1)
            (max floor (upper / 2 ^ index)) previous
      · exact ih (index + 1) (max floor (upper / 2 ^ index))

lemma searchPlan_finite_range {Z Q R : Type*} (probe : Z → ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r floor cap : ℝ) (H : ℕ) :
    (Set.range (fun z => Program.eval reply (searchPlan (probe z) r floor cap H))).Finite :=
  gridPlan_finite_range probe reply r floor cap H H 0 cap

lemma regularizationSearchPlan_measurable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (m : ℕ) [NeZero m] (X : Set E) (state : LongTails.Algorithms.CappedProximal.State E)
    (τ L r floor cap : ℝ) (H b : ℕ) (reply : Fin m × E → ℝ × E) :
    Measurable (fun seeds => Program.eval reply
      (regularizationSearchPlan m X state τ L r floor cap H b seeds)) := by
  exact searchPlan_measurable
    (fun _ ω μ => probePlan m (X ∩ Metric.closedBall (predictor (max floor μ) state) r)
      (predictor (max floor μ) state) τ (max floor μ) L r ω b) reply
    (fun _ μ => AffineResidualSearch.probePlan_measurable m _ _ τ (max floor μ) L r b reply)
    r floor cap H

lemma regularizationSearchPlan_failure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (m : ℕ) [NeZero m] {X : Set E}
    (hX : Convex ℝ X) (hcompact : IsCompact X) (f : Fin m → E → ℝ)
    (state : LongTails.Algorithms.CappedProximal.State E) (hA : 0 ≤ state.weight) (hx : state.primal ∈ X) (hv : state.dual ∈ X)
    {τ L G r floor cap D : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap)
    (hdiam : ‖state.dual - state.primal‖ ≤ D)
    (hc : ∀ i, ConvexOn ℝ X (f i))
    (hg : ∀ i x, x ∈ X → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ X → y ∈ X →
      ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖)
    (hbound : ∀ i x, x ∈ X → ‖gradient (f i) x‖ ≤ G)
    (reply : Fin m × E → ℝ × E)
    (hreply : ∀ i x, x ∈ X → reply (i, x) = (f i x, gradient (f i) x))
    (H b : ℕ) (hcap : 2 * G / r ≤ cap) (hend : cap / 2 ^ H ≤ floor)
    (hwidth : (2 * D + G / floor) / 2 ^ (H + 7) < r / 64) :
    let F := fun z => smoothValue τ (fun i => f i z)
    let displacement := fun μ => ‖AffineSoftmaxRegularization.exactProx X F μ (predictor μ state) - predictor μ state‖
    (Measure.infinitePi (fun _ : ℕ => (probeLaw : Measure ProbeSeed)))
      {seeds | let answer := Program.eval reply (regularizationSearchPlan m X state τ L r floor cap H b seeds)
        ¬ (answer ∈ Set.Icc floor cap ∧
          ((answer = floor ∧ displacement answer < r) ∨
            (51 * r / 64 ≤ displacement answer ∧ displacement answer ≤ 61 * r / 64)))} ≤
      ENNReal.ofReal (((2 * H + 9 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ b) := by
  let F := fun z => smoothValue τ (fun i => f i z)
  let d := fun μ => ‖AffineSoftmaxRegularization.exactProx X F (max floor μ)
    (predictor (max floor μ) state) - predictor (max floor μ) state‖
  let probe := fun (_ : ℕ) seed μ => probePlan m (X ∩ Metric.closedBall (predictor (max floor μ) state) r)
    (predictor (max floor μ) state) τ (max floor μ) L r seed b
  have hF : ConvexOn ℝ X F := SmoothFiniteMaximumGeometry.smoothValue_convex f hτ hX hc hg hbound
  have hFg x (hx' : x ∈ X) : HasGradientAt F (gradient F x) x := by
    have hh := SmoothFiniteMaximumGeometry.smoothValue_gradient f (fun i => gradient (f i) x)
      hτ.ne' (fun i => hg i x hx')
    rw [hh.gradient]
    exact hh
  have hFcont : ContinuousOn F X := fun x hx' => (hFg x hx').continuousAt.continuousWithinAt
  have hFb x (hx' : x ∈ X) : ‖gradient F x‖ ≤ G :=
    SmoothFiniteMaximumGeometry.smoothValue_gradient_bound f hτ.ne' (fun i => hg i x hx')
      (fun i => hbound i x hx')
  have hd : Measurable d := (AffineSoftmaxPredictor.proximal_predictor_displacement_continuous
    hcompact ⟨state.primal, hx⟩ hF hFcont state hA (fun μ : ℝ => max floor μ)
    (continuous_const.max continuous_id) (fun μ => hf.trans_le (le_max_left floor μ))).measurable
  have hcapPos : 0 < cap := hf.trans_le hfc
  have hdcap : d cap ≤ r / 2 := by
    dsimp [d]
    rw [max_eq_right hfc]
    apply (AffineSoftmaxPredictor.proximal_predictor_displacement_bound hcompact hF hFcont hFg hG.le hFb
      state hA hx hv hcapPos).trans
    apply (div_le_iff₀ hcapPos).mpr
    have hh := (div_le_iff₀ hr).mp hcap
    nlinarith
  have hmod : ∀ x ∈ Set.Icc floor cap, ∀ y ∈ Set.Icc floor cap,
      |d x - d y| ≤ (2 * D + G / floor) * |x - y| / min x y := by
    intro x hx' y hy'
    dsimp [d]
    rw [max_eq_right hx'.1, max_eq_right hy'.1]
    exact AffineSoftmaxPredictor.proximal_predictor_modulus hcompact hF hFcont hFg hG.le hf hFb
      state hA hx hv hdiam hx' hy'
  have hprob i μ (_hμ : μ ∈ Set.Icc floor cap) :
      (probeLaw : Measure ProbeSeed) {seed | r / 64 < |Program.eval reply (probe i seed μ) - min r (d μ)|} ≤
        ENNReal.ofReal ((1 / 4 : ℝ) ^ b) := by
    have hp := AffineResidualSearch.probePlan_global_failure m hX hcompact f
      (predictor (max floor μ) state) hL hr hτ (hf.trans_le (le_max_left floor μ))
      hc hg hlip hbound (AffineSoftmaxPredictor.predictor_mem hX state
        (hf.trans_le (le_max_left floor μ)) hA hx hv) reply hreply b
    simpa only [probe, d, F, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4), ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hp
  have hD : 0 ≤ D := (norm_nonneg _).trans hdiam
  have hb := searchPlan_failure_bound probeLaw probe reply
    (fun _ μ => AffineResidualSearch.probePlan_measurable m _ _ τ (max floor μ) L r b reply)
    d hd H hr hf hfc (by positivity : 0 ≤ 2 * D + G / floor) hdcap hend hmod hwidth
    (by positivity : 0 ≤ (1 / 4 : ℝ) ^ b) hprob
  apply le_trans (measure_mono ?_) hb
  intro seeds hbad hgood
  apply hbad
  simpa only [d, max_eq_right hgood.1.1, regularizationSearchPlan, probe, F] using hgood

end LongTails.Proofs.AffineResidualSearchTrace
