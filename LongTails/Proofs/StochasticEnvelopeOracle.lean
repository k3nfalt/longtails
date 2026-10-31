import LongTails.Proofs.StochasticEnvelopeMeasurability
import LongTails.Proofs.StochasticEnvelopeDebiasing
open MeasureTheory OracleTemplate
namespace LongTails.Proofs.StochasticEnvelopeOracle
open LongTails.Algorithms.StochasticEnvelopeProgram RecursiveEnvelopeGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω]
lemma tunedApproximationPlan_moment
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E}
    {f : E → ℝ} {L μ p s a n : ℝ} (h : Model L f field)
    (hμ : 0 < μ) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 < a) (hn : 1 ≤ n)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) :
    let R := Measure.infinitePi fun _ : ℕ => P
    let X := fun ξ : ℕ → Ω => RecursiveEnvelopeExecution.evalAt
      (fun k x => g x (ξ k)) (tunedApproximationPlan L μ p s a n center) 0
    Integrable (fun w => ‖X w - prox field μ center‖ ^ p) R ∧
      (∫ w, ‖X w - prox field μ center‖ ^ p ∂R) ≤
        (2 : ℝ) ^ (18 : ℝ) * (s / μ + a * ‖center - prox field μ center‖) ^ p * n ^ (-(p - 1)) := by
  exact StochasticEnvelopeTransport.approximatePlan_moment P h hμ hp hp2 hs ha hn hκ haκ hg hi hmean hpi hm center

omit [CompleteSpace E] in
lemma measurable_tunedApproximationPlan {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (L μ p s a n : ℝ) :
    Measurable (fun w : E × (ℕ → Ω) => RecursiveEnvelopeExecution.evalAt
      (fun k x => g x (w.2 k)) (tunedApproximationPlan L μ p s a n w.1) 0) := by
  exact StochasticEnvelopeMeasurability.measurable_approximatePlan hg L μ p s a n _ _ _ _ _ _ _
lemma tuned_debiased_contract
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E}
    {f : E → ℝ} {L μ p s a m t : ℝ} (h : Model L f field)
    (hμ : 0 < μ) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 < a) (hm1 : 1 ≤ m)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) :
    let R := Measure.infinitePi fun _ : ℕ => P
    let X := fun ell (ξ : ℕ → Ω) => RecursiveEnvelopeExecution.evalAt
      (fun k x => g x (ξ k)) (tunedApproximationPlan L μ p s a (m * (2 : ℝ) ^ ell) center) 0
    let q := p / (p - 1)
    let r := q * (1 + t) / (q * (1 + t) - 1)
    let v := levelProbability t ht.le ht1
    let Q := (ProbabilityTheory.geometricMeasure v).prod (R.prod (R.prod R))
    let Z := fun w : ℕ × ((ℕ → Ω) × (ℕ → Ω) × (ℕ → Ω)) => debiasedValue v w.1
      (X 0 w.2.1) (X (w.1 + 1) w.2.2.1) (X w.1 w.2.2.2)
    Measurable Z ∧ Integrable Z Q ∧ (∫ w, Z w ∂Q) = prox field μ center ∧
      Integrable (fun w => ‖Z w - prox field μ center‖ ^ r) Q ∧
      (∫ w, ‖Z w - prox field μ center‖ ^ r ∂Q) ≤
        (2 : ℝ) ^ (27 : ℝ) * q / t *
          (s / μ + a * ‖center - prox field μ center‖) ^ r * m ^ (-(r / q)) := by
  let R := Measure.infinitePi fun _ : ℕ => P
  let X := fun ell (ξ : ℕ → Ω) => RecursiveEnvelopeExecution.evalAt
    (fun k x => g x (ξ k)) (tunedApproximationPlan L μ p s a (m * (2 : ℝ) ^ ell) center) 0
  have hmeas (ell : ℕ) : Measurable (X ell) :=
    (measurable_tunedApproximationPlan hg L μ p s a (m * (2 : ℝ) ^ ell)).comp
      (measurable_const.prodMk measurable_id)
  have hmoment (ell : ℕ) := tunedApproximationPlan_moment P h hμ hp hp2 hs ha
    (show 1 ≤ m * (2 : ℝ) ^ ell from one_le_mul_of_one_le_of_one_le hm1 (one_le_pow₀ (by norm_num)))
    hκ haκ hg hi hmean hpi hm center
  exact StochasticEnvelopeDebiasing.dyadic_debiased_contract (P := R) X (prox field μ center) hmeas hp hp2 ht ht1
    (by positivity) (lt_of_lt_of_le zero_lt_one hm1) (fun ell => (hmoment ell).1)
    (fun ell => (hmoment ell).2)

noncomputable def independentEnvelopeReply (g : E → Ω → E)
    (L μ p s a m v : ℝ) (center : E)
    (w : ℕ × ((ℕ → Ω) × (ℕ → Ω) × (ℕ → Ω))) : E :=
  let X := fun ell (ξ : ℕ → Ω) => RecursiveEnvelopeExecution.evalAt
    (fun k x => g x (ξ k)) (tunedApproximationPlan L μ p s a (m * (2 : ℝ) ^ ell) center) 0
  μ • (center - debiasedValue v w.1 (X 0 w.2.1) (X (w.1 + 1) w.2.2.1) (X w.1 w.2.2.2))

omit [CompleteSpace E] in
lemma measurable_independentEnvelopeReply {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (L μ p s a m v : ℝ) :
    Measurable (Function.uncurry (independentEnvelopeReply g L μ p s a m v)) := by
  have hfixed : Measurable (fun w : ℕ × (E × ((ℕ → Ω) × (ℕ → Ω) × (ℕ → Ω))) =>
      independentEnvelopeReply g L μ p s a m v w.2.1 (w.1, w.2.2)) := by
    apply measurable_from_prod_countable_right
    intro ell
    have h0 := (measurable_tunedApproximationPlan hg L μ p s a (m * (2 : ℝ) ^ 0)).comp
      (show Measurable (fun w : E × ((ℕ → Ω) × (ℕ → Ω) × (ℕ → Ω)) => (w.1, w.2.1)) by fun_prop)
    have h1 := (measurable_tunedApproximationPlan hg L μ p s a (m * (2 : ℝ) ^ (ell + 1))).comp
      (show Measurable (fun w : E × ((ℕ → Ω) × (ℕ → Ω) × (ℕ → Ω)) => (w.1, w.2.2.1)) by fun_prop)
    have h2 := (measurable_tunedApproximationPlan hg L μ p s a (m * (2 : ℝ) ^ ell)).comp
      (show Measurable (fun w : E × ((ℕ → Ω) × (ℕ → Ω) × (ℕ → Ω)) => (w.1, w.2.2.2)) by fun_prop)
    exact ((measurable_fst.sub (h0.add ((h1.sub h2).const_smul (((1 - v) ^ ell * v)⁻¹)))).const_smul μ)
  exact hfixed.comp (show Measurable (fun w : E × (ℕ × ((ℕ → Ω) × (ℕ → Ω) × (ℕ → Ω))) => (w.2.1, (w.1, w.2.2))) by fun_prop)

lemma independentEnvelopeReply_contract
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E}
    {f : E → ℝ} {L μ p s a m t : ℝ} (h : Model L f field)
    (hμ : 0 < μ) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 < a) (hm1 : 1 ≤ m)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) :
    let q := p / (p - 1)
    let r := q * (1 + t) / (q * (1 + t) - 1)
    let v := levelProbability t ht.le ht1
    let R := Measure.infinitePi fun _ : ℕ => P
    let Q := (ProbabilityTheory.geometricMeasure v).prod (R.prod (R.prod R))
    let Y := independentEnvelopeReply g L μ p s a m v center
    Integrable Y Q ∧ (∫ w, Y w ∂Q) = envelopeField field μ center ∧
      Integrable (fun w => ‖Y w - envelopeField field μ center‖ ^ r) Q ∧
      (∫ w, ‖Y w - envelopeField field μ center‖ ^ r ∂Q) ≤
        ((2 : ℝ) ^ (28 : ℝ) * q / t * m ^ (-(r / q))) *
          (s ^ r + a ^ r * ‖envelopeField field μ center‖ ^ r) := by
  let q := p / (p - 1)
  let r := q * (1 + t) / (q * (1 + t) - 1)
  let C := (2 : ℝ) ^ (27 : ℝ) * q / t * m ^ (-(r / q))
  have hh := tuned_debiased_contract P h hμ hp hp2 hs ha hm1 ht ht1 hκ haκ hg hi hmean hpi hm center
  have he := StochasticEnvelopeDebiasing.envelope_reply_mean hh.2.1 (prox field μ center) center μ hh.2.2.1
  obtain ⟨hq, hr, hrp, hr2⟩ := StochasticEnvelopeDebiasing.transformed_exponent hp hp2 ht ht1
  have hq0 : 0 < q := by change 2 ≤ q at hq; linarith
  have hC : 0 ≤ C := by positivity
  have hbound := StochasticEnvelopeDebiasing.envelope_reply_moment
    (prox field μ center) center hμ hr.le hr2 hC hs ha.le hh.2.2.2.1
    (show _ ≤ C * (s / μ + a * ‖center - prox field μ center‖) ^ r by
      exact hh.2.2.2.2.trans_eq (by dsimp only [C]; ring))
  refine ⟨he.1, he.2, hbound.1, hbound.2.trans_eq ?_⟩
  dsimp only [C, envelopeField]
  norm_num only [Real.rpow_ofNat, Nat.reducePow]
  ring

end LongTails.Proofs.StochasticEnvelopeOracle

open MeasureTheory OracleTemplate
namespace LongTails.Proofs.StochasticEnvelopeOracle
open StochasticEnvelopeTransport
open RecursiveEnvelopeExecution StochasticEnvelopeExecution
open LongTails.Algorithms.StochasticEnvelopeProgram
variable {Ω : Type} [MeasurableSpace Ω]

abbrev TripleIndex := ℕ ⊕ (ℕ ⊕ ℕ)

def tripleUsed (a b c : ℕ) : TripleIndex → Prop
  | .inl j => j < a
  | .inr (.inl j) => j < b
  | .inr (.inr j) => j < c

def tripleFlat (a b : ℕ) : TripleIndex → ℕ
  | .inl j => j
  | .inr (.inl j) => a + j
  | .inr (.inr j) => a + b + j

lemma tripleFlat_bound (a b c : ℕ) (i : TripleIndex) (hi : tripleUsed a b c i) :
    tripleFlat a b i < a + b + c := by
  rcases i with j | (j | j) <;> simp only [tripleUsed, tripleFlat] at * <;> omega

lemma tripleFlat_inj (a b c : ℕ) : Set.InjOn (tripleFlat a b) {i | tripleUsed a b c i} := by
  intro i hi j hj he
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [Set.mem_ofPred_eq, tripleUsed, tripleFlat] at * <;>
    first | omega | (congr <;> omega)

noncomputable def coupledThree (a b c : ℕ) (ξ : ℕ → Ω) :
    (ℕ → Ω) × (ℕ → Ω) × (ℕ → Ω) :=
  let ζ := fun i => ξ (completeIndex (tripleUsed a b c) (tripleFlat a b) (a + b + c) i)
  ((fun j => ζ (.inl j)), (fun j => ζ (.inr (.inl j))), fun j => ζ (.inr (.inr j)))

lemma coupledThree_preserving (p : Measure Ω) [IsProbabilityMeasure p] (a b c : ℕ) :
    MeasurePreserving (coupledThree (Ω := Ω) a b c) (Measure.infinitePi fun _ : ℕ => p)
      ((Measure.infinitePi fun _ : ℕ => p).prod
        ((Measure.infinitePi fun _ : ℕ => p).prod (Measure.infinitePi fun _ : ℕ => p))) := by
  have hsplit := ((MeasurePreserving.id (Measure.infinitePi fun _ : ℕ => p)).prod
    (infinitePi_sum_preserving (A := ℕ) (B := ℕ) p)).comp
    (infinitePi_sum_preserving (A := ℕ) (B := ℕ ⊕ ℕ) p)
  exact hsplit.comp (completeIndex_preserving p (tripleUsed a b c) (tripleFlat a b)
    (a + b + c) (tripleFlat_bound a b c) (tripleFlat_inj a b c))

lemma coupledThree_joint (a b c : ℕ → ℕ) :
    Measurable (fun w : ℕ × (ℕ → Ω) => coupledThree (a w.1) (b w.1) (c w.1) w.2) := by
  apply measurable_from_prod_countable_right
  intro n
  dsimp only [coupledThree]
  exact (Measurable.of_eval (fun _ => measurable_pi_apply _)).prodMk
    ((Measurable.of_eval (fun _ => measurable_pi_apply _)).prodMk
      (Measurable.of_eval (fun _ => measurable_pi_apply _)))

lemma coupledThree_seed_preserving (P : Measure ℕ) [SFinite P]
    (p : Measure Ω) [IsProbabilityMeasure p] (a b c : ℕ → ℕ) :
    MeasurePreserving (fun w : ℕ × (ℕ → Ω) => (w.1, coupledThree (a w.1) (b w.1) (c w.1) w.2))
      (P.prod (Measure.infinitePi fun _ : ℕ => p))
      (P.prod ((Measure.infinitePi fun _ : ℕ => p).prod
        ((Measure.infinitePi fun _ : ℕ => p).prod (Measure.infinitePi fun _ : ℕ => p)))) :=
  (MeasurePreserving.id P).skew_product (coupledThree_joint a b c)
    (Filter.Eventually.of_forall (fun n => (coupledThree_preserving p (a n) (b n) (c n)).map_eq))

omit [MeasurableSpace Ω] in
lemma evalAt_completed_prefix {Q R U I : Type*} [Encodable I]
    (g : Q → Ω → R) (ξ : ℕ → Ω) (used : I → Prop) (flat : I → ℕ) (C : ℕ)
    {k : ℕ} (plan : QueryPlan Q R U k) (embedding : ℕ → I) (offset : ℕ)
    (hu : ∀ j, j < k → used (embedding j)) (hf : ∀ j, j < k → flat (embedding j) = offset + j) :
    evalAt (fun j q => g q (ξ j)) plan offset =
      evalAt (fun j q => g q (ξ (completeIndex used flat C (embedding j)))) plan 0 := by
  have hh := evalAt_shift (fun j q => g q (ξ j)) plan offset 0
  simp only [Nat.add_zero] at hh
  rw [← hh]
  apply evalAt_prefix_congr
  intro j hj q
  simp only [Nat.zero_add, completeIndex_used used flat C (embedding j) (hu j hj), hf j hj]

omit [MeasurableSpace Ω] in
lemma debiasedPlan_coupled {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → Ω → E) (ξ : ℕ → Ω) (v : ℝ) (cost : ℕ → ℕ)
    (plans : (ell : ℕ) → QueryPlan E E E (cost ell)) (n : ℕ) :
    evalAt (fun j x => g x (ξ j)) (debiasedPlan v cost plans n) 0 =
      let w := coupledThree (cost 0) (cost (n + 1)) (cost n) ξ
      debiasedValue v n (evalAt (fun j x => g x (w.1 j)) (plans 0) 0)
        (evalAt (fun j x => g x (w.2.1 j)) (plans (n + 1)) 0)
        (evalAt (fun j x => g x (w.2.2 j)) (plans n) 0) := by
  rw [evalAt_debiasedPlan]
  simp only [Nat.zero_add]
  unfold coupledThree
  congr 1
  · exact evalAt_completed_prefix g ξ _ _ _ (plans 0) (fun j : ℕ => (Sum.inl j : TripleIndex)) 0
      (fun j hj => hj) (fun j _ => by simp [tripleFlat])
  · exact evalAt_completed_prefix g ξ _ _ _ (plans (n + 1)) (fun j : ℕ => (Sum.inr (Sum.inl j) : TripleIndex)) (cost 0)
      (fun j hj => hj) (fun j _ => rfl)
  · exact evalAt_completed_prefix g ξ _ _ _ (plans n) (fun j : ℕ => (Sum.inr (Sum.inr j) : TripleIndex)) (cost 0 + cost (n + 1))
      (fun j hj => hj) (fun j _ => rfl)

section Envelope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open StochasticEnvelopeOracle

omit [MeasurableSpace Ω] in
lemma tunedEnvelopePlan_coupled (g : E → Ω → E) (L μ p s a m v : ℝ) (center : E)
    (n : ℕ) (ξ : ℕ → Ω) :
    evalAt (fun j x => g x (ξ j)) (tunedEnvelopePlan L μ p s a m v center n) 0 =
      independentEnvelopeReply g L μ p s a m v center
        (n, coupledThree (approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ 0)).calls
          (approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ (n + 1))).calls
          (approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ n)).calls ξ) := by
  unfold tunedEnvelopePlan
  rw [evalAt_map, debiasedPlan_coupled]
  rfl

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_tunedEnvelopePlan {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (L μ p s a m v : ℝ) :
    Measurable (fun w : E × (ℕ × (ℕ → Ω)) =>
      evalAt (fun j x => g x (w.2.2 j)) (tunedEnvelopePlan L μ p s a m v w.1 w.2.1) 0) := by
  let cost := fun ell => (approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ ell)).calls
  have hc := coupledThree_joint (Ω := Ω) (fun _ => cost 0) (fun n => cost (n + 1)) cost
  have hh := (measurable_independentEnvelopeReply hg L μ p s a m v).comp
    (measurable_fst.prodMk (measurable_snd.fst.prodMk (hc.comp measurable_snd)))
  convert hh using 1
  funext w
  exact tunedEnvelopePlan_coupled g L μ p s a m v w.1 w.2.1 w.2.2

lemma tunedEnvelopePlan_seed_identDistrib {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (P : Measure ℕ) [SFinite P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (L μ p s a m v : ℝ) (center : E) :
    ProbabilityTheory.IdentDistrib
      (fun w : ℕ × (ℕ → Ω) => (w.1,
        evalAt (fun j x => g x (w.2 j)) (tunedEnvelopePlan L μ p s a m v center w.1) 0))
      (fun w : ℕ × ((ℕ → Ω) × (ℕ → Ω) × (ℕ → Ω)) =>
        (w.1, independentEnvelopeReply g L μ p s a m v center w))
      (P.prod (Measure.infinitePi fun _ : ℕ => Q))
      (P.prod ((Measure.infinitePi fun _ : ℕ => Q).prod
        ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => Q)))) := by
  let cost := fun ell => (approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ ell)).calls
  have hc := coupledThree_seed_preserving P Q (fun _ => cost 0) (fun n => cost (n + 1)) cost
  have hY : Measurable (fun w : ℕ × ((ℕ → Ω) × (ℕ → Ω) × (ℕ → Ω)) =>
      (w.1, independentEnvelopeReply g L μ p s a m v center w)) :=
    measurable_fst.prodMk ((measurable_independentEnvelopeReply hg L μ p s a m v).comp measurable_prodMk_left)
  refine ⟨(measurable_fst.prodMk ((measurable_tunedEnvelopePlan hg L μ p s a m v).comp measurable_prodMk_left)).aemeasurable,
    hY.aemeasurable, ?_⟩
  simp_rw [tunedEnvelopePlan_coupled]
  calc
    _ = ((P.prod (Measure.infinitePi fun _ : ℕ => Q)).map
        (fun w => (w.1, coupledThree (cost 0) (cost (w.1 + 1)) (cost w.1) w.2))).map
        (fun w => (w.1, independentEnvelopeReply g L μ p s a m v center w)) :=
      (Measure.map_map hY hc.measurable).symm
    _ = _ := by rw [hc.map_eq]

lemma tunedEnvelopePlan_identDistrib {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (P : Measure ℕ) [SFinite P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (L μ p s a m v : ℝ) (center : E) :
    ProbabilityTheory.IdentDistrib
      (fun w : ℕ × (ℕ → Ω) =>
        evalAt (fun j x => g x (w.2 j)) (tunedEnvelopePlan L μ p s a m v center w.1) 0)
      (independentEnvelopeReply g L μ p s a m v center)
      (P.prod (Measure.infinitePi fun _ : ℕ => Q))
      (P.prod ((Measure.infinitePi fun _ : ℕ => Q).prod
        ((Measure.infinitePi fun _ : ℕ => Q).prod (Measure.infinitePi fun _ : ℕ => Q)))) :=
  (tunedEnvelopePlan_seed_identDistrib hg P Q L μ p s a m v center).comp measurable_snd

end Envelope

open RecursiveEnvelopeGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma tunedEnvelopePlan_contract
    (P : Measure Ω) [IsProbabilityMeasure P] {g : E → Ω → E} {field : E → E}
    {f : E → ℝ} {L μ p s a m t : ℝ} (h : Model L f field)
    (hμ : 0 < μ) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 ≤ s) (ha : 0 < a) (hm1 : 1 ≤ m)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hκ : 2 ≤ (L + μ) / μ) (haκ : a ≤ ((L + μ) / μ) ^ (-2 : ℝ))
    (hg : Measurable (Function.uncurry g))
    (hi : ∀ x, Integrable (g x) P) (hmean : ∀ x, ∫ ω, g x ω ∂P = field x)
    (hpi : ∀ x, Integrable (fun ω => ‖g x ω - field x‖ ^ p) P)
    (hm : ∀ x, (∫ ω, ‖g x ω - field x‖ ^ p ∂P) ≤ s ^ p + a ^ p * ‖field x‖ ^ p)
    (center : E) :
    let q := p / (p - 1)
    let r := q * (1 + t) / (q * (1 + t) - 1)
    let v := levelProbability t ht.le ht1
    let Q := (ProbabilityTheory.geometricMeasure v).prod (Measure.infinitePi fun _ : ℕ => P)
    let Y := fun w : ℕ × (ℕ → Ω) => evalAt (fun j x => g x (w.2 j))
      (tunedEnvelopePlan L μ p s a m v center w.1) 0
    Integrable Y Q ∧ (∫ w, Y w ∂Q) = envelopeField field μ center ∧
      Integrable (fun w => ‖Y w - envelopeField field μ center‖ ^ r) Q ∧
      (∫ w, ‖Y w - envelopeField field μ center‖ ^ r ∂Q) ≤
        ((2 : ℝ) ^ (28 : ℝ) * q / t * m ^ (-(r / q))) *
          (s ^ r + a ^ r * ‖envelopeField field μ center‖ ^ r) := by
  let q := p / (p - 1)
  let r := q * (1 + t) / (q * (1 + t) - 1)
  let v := levelProbability t ht.le ht1
  have hh := independentEnvelopeReply_contract P h hμ hp hp2 hs ha hm1 ht ht1 hκ haκ
    hg hi hmean hpi hm center
  have hd := tunedEnvelopePlan_identDistrib hg (ProbabilityTheory.geometricMeasure v) P L μ p s a m v center
  have hd' := hd.comp (show Measurable (fun x : E => ‖x - envelopeField field μ center‖ ^ r) by fun_prop)
  exact ⟨hd.integrable_iff.mpr hh.1, hd.integral_eq.trans hh.2.1,
    hd'.integrable_iff.mpr hh.2.2.1, hd'.integral_eq.trans_le hh.2.2.2⟩


end LongTails.Proofs.StochasticEnvelopeOracle
