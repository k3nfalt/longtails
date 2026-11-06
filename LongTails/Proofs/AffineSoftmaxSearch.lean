import LongTails.Algorithms.AffineSoftmaxSearch
import LongTails.Proofs.AffineSoftmaxOuter
import LongTails.Proofs.AffineSoftmaxExecution

namespace LongTails.Proofs.AffineSoftmaxSearch

open scoped ENNReal
open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxSearch

lemma bisectPlan_eval_mem {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r floor cap : ℝ) (fuel index : ℕ) (lower upper : ℝ)
    (hl : lower ∈ Set.Icc floor cap) (hu : upper ∈ Set.Icc floor cap) :
    Program.eval reply (bisectPlan probe r fuel index lower upper) ∈ Set.Icc floor cap := by
  induction fuel generalizing index lower upper with
  | zero =>
    simp only [bisectPlan, Program.eval_bind, Program.eval, Set.mem_Icc]
    constructor <;> linarith [hl.1, hl.2, hu.1, hu.2]
  | succ n ih =>
    have hm : (lower + upper) / 2 ∈ Set.Icc floor cap := by
      constructor <;> linarith [hl.1, hl.2, hu.1, hu.2]
    simp only [bisectPlan, Program.eval_bind]
    split_ifs
    · exact ih _ _ _ hl hm
    · exact ih _ _ _ hm hu
    · exact hm

lemma gridPlan_eval_mem {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r : ℝ) {floor cap : ℝ} (hc : 0 ≤ cap) (hfc : floor ≤ cap)
    (H fuel index : ℕ) (previous : ℝ) (hp : previous ∈ Set.Icc floor cap) :
    Program.eval reply (gridPlan probe r floor cap H fuel index previous) ∈ Set.Icc floor cap := by
  have hcurrent (j : ℕ) : max floor (cap / 2 ^ j) ∈ Set.Icc floor cap := by
    refine ⟨le_max_left _ _, max_le hfc ?_⟩
    exact div_le_self hc (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  induction fuel generalizing index previous with
  | zero =>
    simp only [gridPlan, Program.eval_bind]
    split_ifs
    · exact ⟨hfc, le_rfl⟩
    · exact bisectPlan_eval_mem probe reply r floor cap _ _ _ _ (hcurrent index) hp
    · exact ⟨le_rfl, hfc⟩
  | succ n ih =>
    simp only [gridPlan, Program.eval_bind]
    split_ifs
    · exact ⟨hfc, le_rfl⟩
    · exact bisectPlan_eval_mem probe reply r floor cap _ _ _ _ (hcurrent index) hp
    · exact ih _ _ (hcurrent index)

lemma searchPlan_eval_mem {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r : ℝ) {floor cap : ℝ} (hc : 0 ≤ cap) (hfc : floor ≤ cap)
    (H : ℕ) :
    Program.eval reply (searchPlan probe r floor cap H) ∈ Set.Icc floor cap :=
  gridPlan_eval_mem probe reply r hc hfc H H 0 cap ⟨hfc, le_rfl⟩

lemma bisectPlan_cost_le {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r : ℝ) (fuel index : ℕ) (lower upper : ℝ) (B : ℕ)
    (hcost : ∀ j t, Program.cost reply (probe j t) ≤ B) :
    Program.cost reply (bisectPlan probe r fuel index lower upper) ≤ (fuel + 1) * B := by
  induction fuel generalizing index lower upper with
  | zero => simpa only [bisectPlan, Program.cost_bind, Program.cost, add_zero, zero_add, one_mul]
      using hcost index ((lower + upper) / 2)
  | succ n ih =>
    simp only [bisectPlan, Program.cost_bind]
    split_ifs
    · have hh := ih (index + 1) lower ((lower + upper) / 2)
      have hc := hcost index ((lower + upper) / 2)
      nlinarith
    · have hh := ih (index + 1) ((lower + upper) / 2) upper
      have hc := hcost index ((lower + upper) / 2)
      nlinarith
    · simpa only [Program.cost, add_zero] using
        (hcost index ((lower + upper) / 2)).trans (by nlinarith : B ≤ (n + 1 + 1) * B)

lemma gridPlan_cost_le {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r floor upper : ℝ) (H fuel index : ℕ) (previous : ℝ) (B : ℕ)
    (hcost : ∀ j t, Program.cost reply (probe j t) ≤ B) :
    Program.cost reply (gridPlan probe r floor upper H fuel index previous) ≤
      (fuel + H + 9) * B := by
  induction fuel generalizing index previous with
  | zero =>
    simp only [gridPlan, Program.cost_bind]
    split_ifs
    · simp only [Program.cost, add_zero]
      exact (hcost _ _).trans (by nlinarith)
    · have hb := bisectPlan_cost_le probe reply r (H + 7) (H + 1)
        (max floor (upper / 2 ^ index)) previous B hcost
      have hc := hcost index (max floor (upper / 2 ^ index))
      nlinarith
    · simp only [Program.cost, add_zero]
      exact (hcost _ _).trans (by nlinarith)
  | succ n ih =>
    simp only [gridPlan, Program.cost_bind]
    split_ifs
    · simp only [Program.cost, add_zero]
      exact (hcost _ _).trans (by nlinarith)
    · have hb := bisectPlan_cost_le probe reply r (H + 7) (H + 1)
        (max floor (upper / 2 ^ index)) previous B hcost
      have hc := hcost index (max floor (upper / 2 ^ index))
      nlinarith
    · have hb := ih (index + 1) (max floor (upper / 2 ^ index))
      have hc := hcost index (max floor (upper / 2 ^ index))
      nlinarith

lemma observed_displacement_certificate {r d observed : ℝ} (hr : 0 < r)
    (he : |observed - min r d| ≤ r / 64)
    (hl : 13 * r / 16 ≤ observed) (hu : observed ≤ 15 * r / 16) :
    51 * r / 64 ≤ d ∧ d ≤ 61 * r / 64 := by
  have he1 := (abs_le.mp he).1
  have he2 := (abs_le.mp he).2
  have hd : d ≤ r := by
    by_contra h
    rw [min_eq_left (le_of_lt (lt_of_not_ge h))] at he1
    linarith
  rw [min_eq_right hd] at he1 he2
  constructor <;> linarith

lemma observed_small_certificate {r d observed : ℝ} (hr : 0 < r)
    (he : |observed - min r d| ≤ r / 64) (hu : observed < 7 * r / 8) :
    d < 57 * r / 64 := by
  have he1 := (abs_le.mp he).1
  have hd : d ≤ r := by
    by_contra h
    rw [min_eq_left (le_of_lt (lt_of_not_ge h))] at he1
    linarith
  rw [min_eq_right hd] at he1
  linarith

lemma observation_error {E : Type*} [NormedAddCommGroup E]
    (center prox approximate : E) {e : ℝ} (he : ‖approximate - prox‖ ≤ e) :
    |‖approximate - center‖ - ‖prox - center‖| ≤ e := by
  have hh := abs_norm_sub_norm_le (approximate - center) (prox - center)
  rw [show (approximate - center) - (prox - center) = approximate - prox by abel] at hh
  exact hh.trans he

lemma selectTrialsPlan_cost {Q R E : Type*} (trial : ℕ → Program Q R (E × ℝ))
    (initial : E × ℝ) (reply : Q → R) (n : ℕ) :
    Program.cost reply (selectTrialsPlan trial initial n) =
      ∑ j ∈ Finset.range n, Program.cost reply (trial j) := by
  induction n with
  | zero => simp only [selectTrialsPlan, Program.cost, Finset.range_zero, Finset.sum_empty]
  | succ n ih => simp only [selectTrialsPlan, Program.cost_bind, Program.cost_map, ih,
      Finset.sum_range_succ]

lemma selectTrialsPlan_score_le_initial {Q R E : Type*} (trial : ℕ → Program Q R (E × ℝ))
    (initial : E × ℝ) (reply : Q → R) (n : ℕ) :
    (Program.eval reply (selectTrialsPlan trial initial n)).2 ≤ initial.2 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [selectTrialsPlan, Program.eval_bind, Program.eval_map]
    split_ifs with h
    · exact (le_of_lt h).trans ih
    · exact ih

lemma selectTrialsPlan_score_le_trial {Q R E : Type*} (trial : ℕ → Program Q R (E × ℝ))
    (initial : E × ℝ) (reply : Q → R) (n j : ℕ) (hj : j < n) :
    (Program.eval reply (selectTrialsPlan trial initial n)).2 ≤ (Program.eval reply (trial j)).2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [selectTrialsPlan, Program.eval_bind, Program.eval_map]
    by_cases hjn : j < n
    · split_ifs with h
      · exact (le_of_lt h).trans (ih hjn)
      · exact ih hjn
    · have he : j = n := by omega
      subst j
      split_ifs with h
      · exact le_rfl
      · exact le_of_not_gt h

lemma selectTrialsPlan_eval_property {Q R E : Type*} (trial : ℕ → Program Q R (E × ℝ))
    (initial : E × ℝ) (reply : Q → R) (P : E × ℝ → Prop)
    (hi : P initial) (ht : ∀ j, P (Program.eval reply (trial j))) (n : ℕ) :
    P (Program.eval reply (selectTrialsPlan trial initial n)) := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    simp only [selectTrialsPlan, Program.eval_bind, Program.eval_map]
    split_ifs
    · exact ht n
    · exact ih

lemma regularizedScorePlan_eval {E : Type*} [NormedAddCommGroup E]
    (m : ℕ) (τ μ : ℝ) (center x : E) (reply : Fin m × E → ℝ × E) :
    Program.eval reply (regularizedScorePlan m τ μ center x) =
      LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ (fun i => (reply (i, x)).1) +
        μ / 2 * ‖x - center‖ ^ 2 := by
  simp only [regularizedScorePlan, Program.eval_map, AffineSoftmaxExecution.cachePlan_eval]

lemma regularizedScorePlan_cost {E : Type*} [NormedAddCommGroup E]
    (m : ℕ) (τ μ : ℝ) (center x : E) (reply : Fin m × E → ℝ × E) :
    Program.cost reply (regularizedScorePlan m τ μ center x) = m := by
  simp only [regularizedScorePlan, Program.cost_map, AffineSoftmaxExecution.cachePlan_cost]

lemma predictor_ratio_perturbation {A μ ν q p : ℝ}
    (hA : 0 ≤ A) (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hq : 0 ≤ q) (hp : 0 ≤ p)
    (heq : μ * A * q ^ 2 + q = 1) (hep : ν * A * p ^ 2 + p = 1) :
    μ * |q - p| ≤ |μ - ν| := by
  let c := ν * A * (q + p) + 1
  have hc : 1 ≤ c := by
    have hh := mul_nonneg (mul_nonneg hν hA) (add_nonneg hq hp)
    dsimp [c]
    linarith
  have he : c * (q - p) = (ν - μ) * A * q ^ 2 := by dsimp [c]; nlinarith
  have hab := congrArg abs he
  rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ c), abs_mul, abs_mul,
    abs_of_nonneg hA, abs_of_nonneg (sq_nonneg q), abs_sub_comm ν μ] at hab
  have hm := mul_nonneg (show 0 ≤ μ * |q - p| by positivity) (sub_nonneg.mpr hc)
  have hnoise := mul_nonneg (abs_nonneg (μ - ν)) hq
  have habμ := congrArg (fun t : ℝ => μ * t) hab
  have heqabs := congrArg (fun t : ℝ => |μ - ν| * t) heq
  nlinarith only [habμ, hm, hnoise, heqabs]

lemma predictor_ratio_equation {A a μ : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hweight : μ * a ^ 2 = A + a) :
    μ * A * (a / (A + a)) ^ 2 + a / (A + a) = 1 := by
  have hden : A + a ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hA ha)
  field_simp
  nlinarith [congrArg (fun t : ℝ => A * t) hweight]

lemma predictor_center_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A μ ν q p D : ℝ} (hA : 0 ≤ A) (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hq : 0 ≤ q) (hp : 0 ≤ p)
    (heq : μ * A * q ^ 2 + q = 1) (hep : ν * A * p ^ 2 + p = 1)
    (x v : E) (hdiam : ‖v - x‖ ≤ D) :
    μ * ‖((1 - q) • x + q • v) - ((1 - p) • x + p • v)‖ ≤ D * |μ - ν| := by
  have he : ((1 - q) • x + q • v) - ((1 - p) • x + p • v) = (q - p) • (v - x) := by module
  rw [he, norm_smul, Real.norm_eq_abs]
  have hD : 0 ≤ D := (norm_nonneg _).trans hdiam
  have hr := predictor_ratio_perturbation hA hμ hν hq hp heq hep
  have h1 := mul_le_mul_of_nonneg_left hdiam (mul_nonneg hμ (abs_nonneg (q - p)))
  have h2 := mul_le_mul_of_nonneg_right hr hD
  nlinarith only [h1, h2]

lemma independent_selection_failure {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (score : Ω → ℝ) (hm : Measurable score)
    (out : (ℕ → Ω) → ℝ) (b : ℕ) (threshold : ℝ) (p : ℝ≥0∞)
    (hselect : ∀ seeds j, j < b → out seeds ≤ score (seeds j))
    (hprob : (Q : Measure Ω) {ω | threshold < score ω} ≤ p) :
    (Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)))
      {seeds | threshold < out seeds} ≤ p ^ b := by
  calc
    _ ≤ (Measure.infinitePi (fun _ : ℕ => (Q : Measure Ω)))
        (Set.pi (Finset.range b) (fun _ : ℕ => {ω | threshold < score ω})) := by
      apply measure_mono
      intro seeds h j hj
      exact lt_of_lt_of_le h (hselect seeds j (Finset.mem_range.mp hj))
    _ = ∏ j ∈ Finset.range b, (Q : Measure Ω) {ω | threshold < score ω} :=
      Measure.infinitePi_pi _ (fun _ _ => measurableSet_lt measurable_const hm)
    _ ≤ ∏ _j ∈ Finset.range b, p := Finset.prod_le_prod (fun _ _ => hprob)
    _ = p ^ b := by simp

lemma expected_gap_failure {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (gap : Ω → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hi : Integrable gap (Q : Measure Ω)) (hn : ∀ ω, 0 ≤ gap ω)
    (he : (∫ ω, gap ω ∂(Q : Measure Ω)) ≤ δ) :
    (Q : Measure Ω) {ω | 4 * δ < gap ω} ≤ (1 / 4 : ℝ≥0∞) := by
  have hh := (hi.div_const (4 * δ)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (hn ω) (by positivity)))
    (s := {ω | 4 * δ < gap ω}) (fun ω hω =>
      (one_le_div (by positivity : 0 < 4 * δ)).mpr (le_of_lt hω))
  apply hh.trans
  rw [integral_div]
  calc
    ENNReal.ofReal ((∫ ω, gap ω ∂(Q : Measure Ω)) / (4 * δ)) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (by positivity : 0 < 4 * δ)).mpr
      linarith
    _ = (1 / 4 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
      norm_num

lemma boostedCachedPlan_failure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot (Fin m) E)
    (τ L G r μ : ℝ) {δ : ℝ} (hδ : 0 < δ) (project : E → E)
    (reply : Fin m × E → ℝ × E) (b : ℕ) (F : E → ℝ) (u : E)
    (hanchor : LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ s.value = F s.anchor)
    (hscore : ∀ seed, Program.eval reply (regularizedScorePlan m τ μ s.anchor
      (Program.eval reply (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan
        s τ L G r μ δ project seed))) =
      F (Program.eval reply (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan
        s τ L G r μ δ project seed)))
    (hm : Measurable (fun seed => F (Program.eval reply
      (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ δ project seed)) - F u))
    (hi : Integrable (fun seed => F (Program.eval reply
      (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ δ project seed)) - F u)
      (LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _))
    (hn : ∀ seed, 0 ≤ F (Program.eval reply
      (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ δ project seed)) - F u)
    (he : (∫ seed, F (Program.eval reply
      (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ δ project seed)) - F u
      ∂(LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _)) ≤ δ) :
    (Measure.infinitePi (fun _ : ℕ =>
      (LongTails.Algorithms.AffineSoftmaxProx.proxLaw : Measure _)))
      {seeds | 4 * δ < F (Program.eval reply
        (boostedCachedPlan m s τ L G r μ δ project seeds b)) - F u} ≤ (1 / 4 : ℝ≥0∞) ^ b := by
  let out := fun seed => Program.eval reply
    (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ δ project seed)
  let trial := fun seed =>
    (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ δ project seed).bind fun x =>
      (regularizedScorePlan m τ μ s.anchor x).map fun score => (x, score)
  have htrial (seed) : Program.eval reply (trial seed) = (out seed, F (out seed)) := by
    simp only [trial, Program.eval_bind, Program.eval_map, hscore, out]
  let initial := (s.anchor, LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue τ s.value)
  let best := fun seeds : ℕ → LongTails.Algorithms.AffineSoftmaxProx.ProxSeed => Program.eval reply (selectTrialsPlan (fun j => trial (seeds j)) initial b)
  have hbest (seeds) : (best seeds).2 = F (best seeds).1 := by
    exact selectTrialsPlan_eval_property (fun j => trial (seeds j)) initial reply
      (fun z => z.2 = F z.1) hanchor (fun j => by rw [htrial]) b
  have hout (seeds) : Program.eval reply
      (boostedCachedPlan m s τ L G r μ δ project seeds b) = (best seeds).1 := by
    simp only [boostedCachedPlan, Program.eval_map, best, initial, trial]
  apply independent_selection_failure LongTails.Algorithms.AffineSoftmaxProx.proxLaw
    (fun seed => F (out seed) - F u) hm _ b (4 * δ) (1 / 4)
  · intro seeds j hj
    have hh := selectTrialsPlan_score_le_trial (fun j => trial (seeds j)) initial reply b j hj
    change (best seeds).2 ≤ (Program.eval reply (trial (seeds j))).2 at hh
    rw [hbest, htrial] at hh
    rw [hout]
    exact sub_le_sub_right hh (F u)
  · exact expected_gap_failure LongTails.Algorithms.AffineSoftmaxProx.proxLaw _ hδ hi hn he

lemma boostedCachedPlan_cost {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot (Fin m) E)
    (τ L G r μ δ : ℝ) (project : E → E)
    (seeds : ℕ → LongTails.Algorithms.AffineSoftmaxProx.ProxSeed) (b : ℕ)
    (reply : Fin m × E → ℝ × E) :
    Program.cost reply (boostedCachedPlan m s τ L G r μ δ project seeds b) =
      (∑ j ∈ Finset.range b, Program.cost reply
        (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ δ project (seeds j))) + b * m := by
  simp only [boostedCachedPlan, Program.cost_map, selectTrialsPlan_cost,
    Program.cost_bind, regularizedScorePlan_cost, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]

lemma boostedCachedPlan_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (s : LongTails.Algorithms.AffineSoftmaxEstimator.Snapshot (Fin m) E)
    (τ L G r μ δ : ℝ) (project : E → E)
    (seeds : ℕ → LongTails.Algorithms.AffineSoftmaxProx.ProxSeed) (b : ℕ)
    (reply : Fin m × E → ℝ × E) {C : Set E} (ha : s.anchor ∈ C)
    (ho : ∀ seed, Program.eval reply
      (LongTails.Algorithms.AffineSoftmaxProx.cachedProxPlan s τ L G r μ δ project seed) ∈ C) :
    Program.eval reply (boostedCachedPlan m s τ L G r μ δ project seeds b) ∈ C := by
  simp only [boostedCachedPlan, Program.eval_map]
  apply selectTrialsPlan_eval_property _ _ reply (fun z => z.1 ∈ C) ha
  intro j
  simpa only [Program.eval_bind, Program.eval_map] using ho (seeds j)

lemma selectTrialsPlan_measurable {Q R E Z : Type*} [MeasurableSpace E] [MeasurableSpace Z]
    (trial : Z → ℕ → Program Q R (E × ℝ)) (initial : Z → E × ℝ)
    (reply : Q → R) (hi : Measurable initial)
    (ht : ∀ j, Measurable (fun z => Program.eval reply (trial z j))) (n : ℕ) :
    Measurable (fun z => Program.eval reply (selectTrialsPlan (trial z) (initial z) n)) := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    simp only [selectTrialsPlan, Program.eval_bind, Program.eval_map]
    exact (ht n).ite (measurableSet_lt (ht n).snd ih.snd) ih

lemma regularizedScorePlan_measurable {E Z : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Z]
    (m : ℕ) (τ : ℝ) (μ : Z → ℝ) (hμ : Measurable μ) (center x : Z → E)
    (hc : Measurable center) (hx : Measurable x) (reply : Fin m × E → ℝ × E)
    (hr : Measurable reply) :
    Measurable (fun z => Program.eval reply (regularizedScorePlan m τ (μ z) (center z) (x z))) := by
  simp_rw [regularizedScorePlan_eval]
  unfold LongTails.Algorithms.AffineSoftmaxEstimator.smoothValue
  have hv (i : Fin m) : Measurable (fun z => Real.exp ((reply (i, x z)).1 / τ)) :=
    (((hr.comp (measurable_const.prodMk hx)).fst).div_const τ).exp
  exact ((Finset.measurable_sum _ (fun i _ => hv i)).log.const_mul τ).add
    ((hμ.div_const 2).mul ((hx.sub hc).norm.pow_const 2))

end LongTails.Proofs.AffineSoftmaxSearch
