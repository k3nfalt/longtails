import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.GeneralizedLipschitzPilot
import LongTails.Proofs.StochasticEnvelopePilot
import LongTails.Proofs.RobustPilot

namespace LongTails.Proofs.GeneralizedLipschitzExecution

open OracleTemplate OracleTemplate.StochasticGradient OracleTemplate.FiniteVariance
open LongTails.Algorithms.GeneralizedLipschitzPilot

section Execution

variable {E Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace Ω]

lemma execute_burnin (c : Config) (hc : 0 < c.calls) (center : E) (R G G0 κ : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (oracle : E → Ω → E)
    (ξ : ℕ → Ω) (T : ℕ) :
    burninOutput c hc center R G G0 κ T
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ =
      (advance (fun k (s : E × Bool) => blockUpdate c center R G G0 κ s
        (fun j => if _h : j < c.calls then oracle s.1 (ξ (k * c.calls + j)) else 0))
        T 0 (center, false)).1 := by
  simpa only [burninOutput, burninAlgorithm, blockAlgorithm] using
    execute_batched hc (blockAlgorithm c center R G G0 κ)
      (fun (s : E × Bool) _ => s.1) (fun _ reply => reply) (0 : E) P oracle ξ T ()

lemma raw_index_lt (c : Config) {i : ℕ} (hi : i < c.rawCount) : i < c.calls := by
  unfold Config.calls
  omega

lemma update_index_lt (c : Config) {i : ℕ} (hi : i < c.updateCount) :
    c.rawCount + c.scales * c.scaleCalls + i < c.calls := by
  unfold Config.calls
  omega

lemma moment_index_lt (c : Config) {j leaf i : ℕ}
    (hj : j < c.scales) (hleaf : leaf < 3 ^ c.depth) (hi : i < c.momentCount) :
    c.rawCount + j * c.scaleCalls + leaf * c.momentCount + i < c.calls := by
  have hj' := Nat.mul_le_mul_right c.scaleCalls (Nat.succ_le_of_lt hj)
  have hl' := Nat.mul_le_mul_right c.momentCount (Nat.succ_le_of_lt hleaf)
  unfold Config.calls Config.scaleCalls at *
  nlinarith

lemma mean_index_lt (c : Config) {j k i : ℕ}
    (hj : j < c.scales) (hk : k < c.repetitions) (hi : i < c.meanCount) :
    c.rawCount + j * c.scaleCalls + 3 ^ c.depth * c.momentCount + k * c.meanCount + i < c.calls := by
  have hj' := Nat.mul_le_mul_right c.scaleCalls (Nat.succ_le_of_lt hj)
  have hk' := Nat.mul_le_mul_right c.meanCount (Nat.succ_le_of_lt hk)
  unfold Config.calls Config.scaleCalls at *
  nlinarith

lemma blockMoment_prefix (c : Config) (κ G0 initial : ℝ) (j : ℕ)
    (data tail : ℕ → E) (hdata : ∀ k, data (c.rawCount + k) = tail k) :
    blockMoment c κ G0 initial data j = blockMoment {c with rawCount := 0} κ G0 initial tail j := by
  simp [blockMoment, Config.scaleCalls, Nat.add_assoc, hdata]

lemma blockMean_prefix (c : Config) (κ G0 initial : ℝ) (j : ℕ)
    (data tail : ℕ → E) (hdata : ∀ k, data (c.rawCount + k) = tail k) :
    blockMean c κ G0 initial data j = blockMean {c with rawCount := 0} κ G0 initial tail j := by
  simp [blockMean, Config.scaleCalls, Nat.add_assoc, hdata]


lemma blockValue_congr_range (g h : ℕ → ℝ) (depth start : ℕ)
    (he : ∀ i, start * 3 ^ depth ≤ i → i < (start + 1) * 3 ^ depth → g i = h i) :
    blockValue (fun (_ : Unit) i => g i) depth () start =
      blockValue (fun (_ : Unit) i => h i) depth () start := by
  induction depth generalizing start with
  | zero => exact he start (by simp) (by simp)
  | succ depth ih =>
    have hc (r : ℕ) (hr : r < 3) := ih (start * 3 + r) (by
      intro i hlo hhi
      apply he i
      · rw [pow_succ]
        nlinarith
      · rw [pow_succ]
        have hp : 0 < 3 ^ depth := by positivity
        nlinarith)
    have h0 := hc 0 (by decide)
    simp only [Nat.add_zero] at h0
    simp only [blockValue]
    rw [h0, hc 1 (by decide), hc 2 (by decide)]

lemma moment_index_lt_pilot (c : Config) {j leaf i : ℕ}
    (hj : j < c.scales) (hleaf : leaf < 3 ^ c.depth) (hi : i < c.momentCount) :
    c.rawCount + j * c.scaleCalls + leaf * c.momentCount + i <
      c.rawCount + c.scales * c.scaleCalls := by
  have hj' := Nat.mul_le_mul_right c.scaleCalls (Nat.succ_le_of_lt hj)
  have hl' := Nat.mul_le_mul_right c.momentCount (Nat.succ_le_of_lt hleaf)
  unfold Config.scaleCalls at *
  nlinarith

lemma mean_index_lt_pilot (c : Config) {j k i : ℕ}
    (hj : j < c.scales) (hk : k < c.repetitions) (hi : i < c.meanCount) :
    c.rawCount + j * c.scaleCalls + 3 ^ c.depth * c.momentCount + k * c.meanCount + i <
      c.rawCount + c.scales * c.scaleCalls := by
  have hj' := Nat.mul_le_mul_right c.scaleCalls (Nat.succ_le_of_lt hj)
  have hk' := Nat.mul_le_mul_right c.meanCount (Nat.succ_le_of_lt hk)
  unfold Config.scaleCalls at *
  nlinarith

lemma blockMoment_congr_pilot (c : Config) (κ G0 initial : ℝ) {j : ℕ} (hj : j < c.scales)
    (data data' : ℕ → E) (he : ∀ i, i < c.rawCount + c.scales * c.scaleCalls → data i = data' i) :
    blockMoment c κ G0 initial data j = blockMoment c κ G0 initial data' j := by
  dsimp [blockMoment]
  apply blockValue_congr_range
  intro leaf _ hleaf
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [he _ (moment_index_lt_pilot c hj (by simpa using hleaf) i.isLt)]

lemma blockMean_congr_pilot (c : Config) (κ G0 initial : ℝ) {j : ℕ} (hj : j < c.scales)
    (data data' : ℕ → E) (he : ∀ i, i < c.rawCount + c.scales * c.scaleCalls → data i = data' i) :
    blockMean c κ G0 initial data j = blockMean c κ G0 initial data' j := by
  dsimp [blockMean]
  congr 1
  funext k i
  exact he _ (mean_index_lt_pilot c hj k.isLt i.isLt)
omit [NormedSpace ℝ E] in
lemma select_congr_range (G0 initial κ : ℝ) (moments moments' : ℕ → ℝ) (means means' : ℕ → E)
    (remaining index : ℕ)
    (hq : ∀ j, index ≤ j → j < index + remaining → moments j = moments' j)
    (hm : ∀ j, index ≤ j → j < index + remaining → means j = means' j) :
    select G0 initial κ moments means index remaining = select G0 initial κ moments' means' index remaining := by
  induction remaining generalizing index with
  | zero => rfl
  | succ remaining ih =>
    simp only [select, hq index le_rfl (by omega), hm index le_rfl (by omega)]
    split_ifs
    · rfl
    · rfl
    · exact ih (index + 1) (fun j hlo hhi => hq j (by omega) (by omega))
        (fun j hlo hhi => hm j (by omega) (by omega))

omit [NormedSpace ℝ E] in
lemma rawScale_congr_pilot (c : Config) (G0 : ℝ) (data data' : ℕ → E)
    (he : ∀ i, i < c.rawCount + c.scales * c.scaleCalls → data i = data' i) :
    rawScale G0 (fun i : Fin c.rawCount => data i) = rawScale G0 (fun i : Fin c.rawCount => data' i) := by
  congr 1
  funext i
  exact he i (by have hi := i.isLt; omega)

lemma blockDecision_congr_pilot (c : Config) (κ G0 : ℝ) (data data' : ℕ → E)
    (he : ∀ i, i < c.rawCount + c.scales * c.scaleCalls → data i = data' i) :
    blockDecision c κ G0 data = blockDecision c κ G0 data' := by
  dsimp [blockDecision]
  rw [rawScale_congr_pilot c G0 data data' he]
  apply select_congr_range
  · intro j _ hj
    exact blockMoment_congr_pilot c κ G0 _ (by omega) data data' he
  · intro j _ hj
    exact blockMean_congr_pilot c κ G0 _ (by omega) data data' he

open MeasureTheory

noncomputable def splitFinite {Ω : Type} [MeasurableSpace Ω] (n m : ℕ) :
    (Fin (n + m) → Ω) ≃ᵐ ((Fin n → Ω) × (Fin m → Ω)) where
  toFun ξ := (fun i => ξ ⟨i, by omega⟩, fun i => ξ ⟨n + i, by omega⟩)
  invFun z i := if h : (i : ℕ) < n then z.1 ⟨i, h⟩ else z.2 ⟨i - n, by omega⟩
  left_inv ξ := by
    funext i
    dsimp
    split_ifs with hi
    · rfl
    · congr 1
      apply Fin.ext
      dsimp
      omega
  right_inv z := by
    apply Prod.ext
    · funext i
      simp
    · funext i
      simp
  measurable_toFun := by
    change Measurable (fun ξ : Fin (n + m) → Ω =>
      ((fun i : Fin n => ξ ⟨i, by omega⟩), (fun i : Fin m => ξ ⟨n + i, by omega⟩)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : (Fin n → Ω) × (Fin m → Ω) => fun i : Fin (n + m) =>
      if h : (i : ℕ) < n then z.1 ⟨i, h⟩ else z.2 ⟨i - n, by omega⟩)
    apply Measurable.of_eval
    intro i
    split_ifs <;> fun_prop

lemma splitFinite_preserving {Ω : Type} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (n m : ℕ) :
    MeasurePreserving (splitFinite (Ω := Ω) n m) (Measure.pi fun _ : Fin (n + m) => p)
      ((Measure.pi fun _ : Fin n => p).prod (Measure.pi fun _ : Fin m => p)) := by
  have ht := ((MeasurePreserving.id (Measure.pi fun _ : Fin n => p)).prod
    (OracleTemplate.StochasticGeneralized.prefix_preserving p m)).comp
      (OracleTemplate.StochasticGeneralized.splitStream_preserving p n)
  refine ⟨(splitFinite n m).measurable, ?_⟩
  rw [← (OracleTemplate.StochasticGeneralized.prefix_preserving p (n + m)).map_eq,
    Measure.map_map (splitFinite n m).measurable (by fun_prop)]
  exact ht.map_eq

end Execution

section SplitReplies

variable {Ω F : Type} [MeasurableSpace Ω] [Zero F]
lemma split_reply_prefix (c : Config) (X : Ω → F)
    (a : Fin (c.rawCount + c.scales * c.scaleCalls) → Ω) (b : Fin c.updateCount → Ω)
    (i : ℕ) (hi : i < c.rawCount + c.scales * c.scaleCalls) :
    (if h : i < c.calls then X ((splitFinite (c.rawCount + c.scales * c.scaleCalls) c.updateCount).symm
      (a, b) ⟨i, h⟩) else 0) = X (a ⟨i, hi⟩) := by
  have hlt : i < c.calls := by unfold Config.calls; omega
  simp [hlt, splitFinite, hi]

lemma split_reply_update (c : Config) (X : Ω → F)
    (a : Fin (c.rawCount + c.scales * c.scaleCalls) → Ω) (b : Fin c.updateCount → Ω)
    (i : Fin c.updateCount) :
    (if h : c.rawCount + c.scales * c.scaleCalls + i < c.calls then
      X ((splitFinite (c.rawCount + c.scales * c.scaleCalls) c.updateCount).symm
        (a, b) ⟨c.rawCount + c.scales * c.scaleCalls + i, h⟩) else 0) = X (b i) := by
  have hlt : c.rawCount + c.scales * c.scaleCalls + i < c.calls := by
    unfold Config.calls
    omega
  simp [hlt, splitFinite]

end SplitReplies

section Geometry

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma blockUpdate_mem_ball (c : Config) (center : E) (R G G0 κ : ℝ)
    (hR : 0 ≤ R) (state : E × Bool) (data : ℕ → E)
    (hs : ‖state.1 - center‖ ≤ R) :
    ‖(blockUpdate c center R G G0 κ state data).1 - center‖ ≤ R := by
  classical
  unfold blockUpdate
  split_ifs
  · exact hs
  · split
    · exact hs
    · exact hs
    · simpa only [Prod.fst, add_sub_cancel_left] using OracleTemplate.norm_clip_le hR _

lemma advance_mem_ball (c : Config) (center : E) (R G G0 κ : ℝ)
    (hR : 0 ≤ R) (data : ℕ → (E × Bool) → ℕ → E) (T call : ℕ) (state : E × Bool)
    (hs : ‖state.1 - center‖ ≤ R) :
    ‖(OracleTemplate.StochasticGradient.advance
      (fun k s => blockUpdate c center R G G0 κ s (data k s)) T call state).1 - center‖ ≤ R := by
  induction T generalizing call state with
  | zero => exact hs
  | succ T ih =>
    exact ih (call + 1) _ (blockUpdate_mem_ball c center R G G0 κ hR state _ hs)
lemma burninOutput_mem_ball {Ω : Type} [MeasurableSpace Ω]
    (c : Config) (hc : 0 < c.calls) (center : E) (R G G0 κ : ℝ) (hR : 0 ≤ R)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (oracle : E → Ω → E)
    (ξ : ℕ → Ω) (T : ℕ) :
    ‖burninOutput c hc center R G G0 κ T
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ - center‖ ≤ R := by
  rw [execute_burnin]
  exact advance_mem_ball c center R G G0 κ hR _ T 0 (center, false) (by simpa)

end Geometry

section Drift

open MeasureTheory
open scoped RealInnerProductSpace

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
lemma projected_step_integral (center x xstar : E) {R η : ℝ} (hR : 0 ≤ R)
    (hstar : ‖xstar - center‖ ≤ R) {X : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) :
    Integrable (fun ω => ‖center + OracleTemplate.clip R (x - η • X ω - center) - xstar‖ ^ 2) P ∧
    (∫ ω, ‖center + OracleTemplate.clip R (x - η • X ω - center) - xstar‖ ^ 2 ∂P) ≤
      ‖x - xstar‖ ^ 2 - 2 * η * ⟪x - xstar, ∫ ω, X ω ∂P⟫ +
        η ^ 2 * (∫ ω, ‖X ω‖ ^ 2 ∂P) := by
  have he (ω : Ω) : ‖x - η • X ω - xstar‖ ^ 2 =
      ‖x - xstar‖ ^ 2 - 2 * η * ⟪x - xstar, X ω⟫ + η ^ 2 * ‖X ω‖ ^ 2 := by
    rw [show x - η • X ω - xstar = (x - xstar) - η • X ω by abel,
      norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right]
    ring
  have hi1 : Integrable (fun ω => ‖x - xstar‖ ^ 2 - 2 * η * ⟪x - xstar, X ω⟫) P := (integrable_const (‖x - xstar‖ ^ 2)).sub ((hXi.const_inner (x - xstar)).const_mul (2 * η))
  have hi2 := hX2.const_mul (η ^ 2)
  have hi : Integrable (fun ω => ‖x - η • X ω - xstar‖ ^ 2) P := by
    have hi3 : Integrable (fun ω => ‖x - xstar‖ ^ 2 - 2 * η * ⟪x - xstar, X ω⟫ + η ^ 2 * ‖X ω‖ ^ 2) P := hi1.add hi2
    simpa only [he] using hi3
  have hbound (ω : Ω) : ‖center + OracleTemplate.clip R (x - η • X ω - center) - xstar‖ ^ 2 ≤
      ‖x - η • X ω - xstar‖ ^ 2 := by
    have h := OracleTemplate.norm_clip_sub_le hR hstar (x - η • X ω - center)
    have he1 : center + OracleTemplate.clip R (x - η • X ω - center) - xstar =
        OracleTemplate.clip R (x - η • X ω - center) - (xstar - center) := by abel
    rw [he1]
    have he2 : x - η • X ω - center - (xstar - center) = x - η • X ω - xstar := by abel
    rw [he2] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hp : Integrable (fun ω => ‖center + OracleTemplate.clip R (x - η • X ω - center) - xstar‖ ^ 2) P := by
    apply Integrable.mono' hi
    · apply Measurable.aestronglyMeasurable
      exact ((measurable_const.add ((OracleTemplate.measurable_clip R).comp
        ((measurable_const.sub (hX.const_smul η)).sub measurable_const))).sub measurable_const).norm.pow_const 2
    · filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound ω
  refine ⟨hp, (integral_mono hp hi hbound).trans_eq ?_⟩
  simp_rw [he]
  rw [integral_add hi1 hi2, integral_sub (integrable_const _) ((hXi.const_inner _).const_mul _),
    integral_const_mul, integral_const_mul, integral_inner hXi]
  simp
lemma pilot_step_drift (center x xstar : E) {R G m gap : ℝ} (hR : 0 ≤ R)
    (hG : 0 < G) (hm : 0 < m) (hstar : ‖xstar - center‖ ≤ R) {X : Ω → E}
    (hX : Measurable X) (hXi : Integrable X P) (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    (hsub : gap ≤ ⟪x - xstar, ∫ ω, X ω ∂P⟫)
    (hgap : m / (16 * G) ≤ gap) (hmoment : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ 4 * m ^ 2) :
    (∫ ω, ‖center + OracleTemplate.clip R (x - (1 / (128 * G * m)) • X ω - center) - xstar‖ ^ 2 ∂P)
      ≤ ‖x - xstar‖ ^ 2 - 1 / (2048 * G ^ 2) := by
  have h := (projected_step_integral center x xstar hR hstar (η := 1 / (128 * G * m)) hX hXi hX2).2
  have h1 := mul_le_mul_of_nonneg_left (hgap.trans hsub) (by positivity : 0 ≤ 2 * (1 / (128 * G * m)))
  have h2 := mul_le_mul_of_nonneg_left hmoment (sq_nonneg (1 / (128 * G * m)))
  have he : 2 * (1 / (128 * G * m)) * (m / (16 * G)) -
      (1 / (128 * G * m)) ^ 2 * (4 * m ^ 2) = 3 / (4096 * G ^ 2) := by
    field_simp
    ring
  have hconst : 1 / (2048 * G ^ 2) ≤ 3 / (4096 * G ^ 2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_pos_of_pos hG]
  linarith

end Drift

open MeasureTheory
open scoped BigOperators NNReal

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {A : Type*} [MeasurableSpace A]
omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma continuous_rawMaximum (n : ℕ) : Continuous (rawMaximum (E := E) (n := n)) := by
  unfold rawMaximum
  fun_prop

omit [InnerProductSpace ℝ E] in
lemma measurable_rawScale_family {n : ℕ} {data : A → Fin n → E}
    (hd : ∀ i, Measurable (fun a => data a i)) (G0 : ℝ) :
    Measurable (fun a => rawScale G0 (data a)) := by
  have h := (continuous_rawMaximum n).measurable.comp (Measurable.of_eval hd)
  exact (measurable_const.max h).const_mul 2

lemma measurable_scale_family {initial : A → ℝ} (hi : Measurable initial) (G0 : ℝ) (j : ℕ) :
    Measurable (fun a => scale G0 (initial a) j) :=
  measurable_const.max (hi.div_const _)

lemma measurable_blockValue_family {g : A → ℕ → ℝ}
    (hg : ∀ k, Measurable (fun a => g a k)) (depth k : ℕ) :
    Measurable (fun a => OracleTemplate.FiniteVariance.blockValue (fun (_ : Unit) i => g a i) depth () k) := by
  induction depth generalizing k with
  | zero => exact hg k
  | succ depth ih =>
    exact ((ih (k * 3)).min (ih (k * 3 + 1))).max
      (((ih (k * 3 + 1)).min (ih (k * 3 + 2))).max ((ih (k * 3 + 2)).min (ih (k * 3))))

lemma measurable_blockMoment_family (c : Config) (κ G0 : ℝ)
    {initial : A → ℝ} {data : A → ℕ → E} (hi : Measurable initial)
    (hd : ∀ k, Measurable (fun a => data a k)) (j : ℕ) :
    Measurable (fun a => blockMoment c κ G0 (initial a) (data a) j) := by
  have hB := (measurable_scale_family hi G0 j).const_mul (256 * κ)
  have hleaf (leaf : ℕ) : Measurable (fun a =>
      (∑ i : Fin c.momentCount, ‖OracleTemplate.clip (256 * κ * scale G0 (initial a) j)
        (data a (c.rawCount + j * c.scaleCalls + leaf * c.momentCount + i))‖ ^ 2) / c.momentCount) := by
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    exact ((LongTails.Proofs.StochasticEnvelopePilot.measurable_variable_clip hB (hd _)).norm).pow_const 2
  have h := measurable_blockValue_family hleaf c.depth 0
  exact h

lemma measurable_blockMean_family (c : Config) (κ G0 : ℝ)
    {initial : A → ℝ} {data : A → ℕ → E} (hi : Measurable initial)
    (hd : ∀ k, Measurable (fun a => data a k)) (j : ℕ) :
    Measurable (fun a => blockMean c κ G0 (initial a) (data a) j) := by
  have hm := measurable_scale_family hi G0 j
  have hB := hm.const_mul (256 * κ)
  have hv : Measurable (fun a => fun k : Fin c.repetitions =>
      (1 / (c.meanCount : ℝ)) • ∑ i : Fin c.meanCount,
        OracleTemplate.clip (256 * κ * scale G0 (initial a) j)
          (data a (c.rawCount + j * c.scaleCalls + 3 ^ c.depth * c.momentCount + k * c.meanCount + i))) := by
    apply Measurable.of_eval
    intro k
    apply Measurable.const_smul
    apply Finset.measurable_sum
    intro i _
    exact LongTails.Proofs.StochasticEnvelopePilot.measurable_variable_clip hB (hd _)
  exact (OracleTemplate.RobustGradient.measurable_pilotCenter c.repetitions).comp
    ((hm.div_const 16).prodMk hv)

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma measurable_selectionValue {H : Type*} [MeasurableSpace H]
    (G0 κ : ℝ) {initial : A → ℝ} {moments : A → ℕ → ℝ} {means : A → ℕ → E}
    {terminal exhausted : A → H} {update : A → ℕ → H}
    (hi : Measurable initial) (hq : ∀ j, Measurable (fun a => moments a j))
    (hm : ∀ j, Measurable (fun a => means a j))
    (ht : Measurable terminal) (he : Measurable exhausted)
    (hu : ∀ j, Measurable (fun a => update a j)) (remaining index : ℕ) :
    Measurable (fun a => match select G0 (initial a) κ (moments a) (means a) index remaining with
      | .terminal => terminal a
      | .update j => update a j
      | .exhausted => exhausted a) := by
  induction remaining generalizing index with
  | zero => exact he
  | succ remaining ih =>
    have hs := measurable_scale_family hi G0 index
    have hterminal : MeasurableSet {a | scale G0 (initial a) index ≤ 64 * G0} :=
      measurableSet_le hs measurable_const
    have haccept := (measurableSet_le ((hs.pow_const 2).const_mul κ |>.div_const 32) (hq index)).union
      (measurableSet_le (hs.div_const 4) (hm index).norm)
    have hfun : (fun a => match select G0 (initial a) κ (moments a) (means a) index (remaining + 1) with
        | .terminal => terminal a | .update j => update a j | .exhausted => exhausted a) =
        (fun a => if scale G0 (initial a) index ≤ 64 * G0 then terminal a
          else if κ * (scale G0 (initial a) index) ^ 2 / 32 ≤ moments a index ∨
              scale G0 (initial a) index / 4 ≤ ‖means a index‖ then update a index
          else match select G0 (initial a) κ (moments a) (means a) (index + 1) remaining with
            | .terminal => terminal a | .update j => update a j | .exhausted => exhausted a) := by
      funext a
      simp only [select]
      split_ifs <;> rfl
    rw [hfun]
    exact Measurable.ite hterminal ht (Measurable.ite haccept (hu index) (ih (index + 1)))

lemma measurable_blockUpdate_family (c : Config) (center : E) (R G G0 κ : ℝ)
    {state : A → E × Bool} {data : A → ℕ → E} (hs : Measurable state)
    (hd : ∀ k, Measurable (fun a => data a k)) :
    Measurable (fun a => blockUpdate c center R G G0 κ (state a) (data a)) := by
  classical
  let initial := fun a => rawScale G0 (fun i : Fin c.rawCount => data a i)
  have hi : Measurable initial := measurable_rawScale_family (fun i => hd i) G0
  let avg := fun a => (1 / (c.updateCount : ℝ)) •
    ∑ i : Fin c.updateCount, data a (c.rawCount + c.scales * c.scaleCalls + i)
  have havg : Measurable avg := by
    apply Measurable.const_smul
    exact Finset.measurable_sum _ (fun i _ => hd _)
  have hupdate (j : ℕ) : Measurable (fun a =>
      (center + OracleTemplate.clip R ((state a).1 -
        (1 / (128 * G * scale G0 (initial a) j)) • avg a - center), false)) := by
    have hm := measurable_scale_family hi G0 j
    have hη : Measurable (fun a => 1 / (128 * G * scale G0 (initial a) j)) :=
      measurable_const.div (hm.const_mul (128 * G))
    exact (measurable_const.add ((OracleTemplate.measurable_clip R).comp
      ((hs.fst.sub (hη.smul havg)).sub measurable_const))).prodMk measurable_const
  have hterminal : Measurable (fun a => ((state a).1, true)) := hs.fst.prodMk measurable_const
  have hc := measurable_selectionValue G0 κ hi
    (fun j => measurable_blockMoment_family c κ G0 hi hd j)
    (fun j => measurable_blockMean_family c κ G0 hi hd j)
    hterminal hterminal hupdate c.scales 0
  have hdone : MeasurableSet {a | (state a).2 = true} := measurableSet_eq_fun hs.snd measurable_const
  convert Measurable.ite hdone hs hc using 1
  funext a
  dsimp [blockUpdate, blockDecision, initial, avg]
  split_ifs
  · rfl
  · split <;> simp_all
  all_goals infer_instance

lemma measurable_burnin_advance {Ω : Type} [MeasurableSpace Ω]
    (c : Config) (center : E) (R G G0 κ : ℝ) {oracle : E → Ω → E}
    (ho : Measurable (Function.uncurry oracle)) (T call : ℕ) :
    Measurable (fun w : (E × Bool) × (ℕ → Ω) =>
      OracleTemplate.StochasticGradient.advance
        (fun k s => blockUpdate c center R G G0 κ s
          (fun j => if _h : j < c.calls then oracle s.1 (w.2 (k * c.calls + j)) else 0))
        T call w.1) := by
  induction T generalizing call with
  | zero => exact measurable_fst
  | succ T ih =>
    have hd (j : ℕ) : Measurable (fun w : (E × Bool) × (ℕ → Ω) =>
        if _h : j < c.calls then oracle w.1.1 (w.2 (call * c.calls + j)) else 0) := by
      split_ifs
      · exact ho.comp (measurable_fst.fst.prodMk ((measurable_pi_apply _).comp measurable_snd))
      · exact measurable_const
    have hu := measurable_blockUpdate_family c center R G G0 κ measurable_fst hd
    simpa only [OracleTemplate.StochasticGradient.advance, Function.comp_def] using
      (ih (call + 1)).comp (hu.prodMk measurable_snd)

lemma measurable_burninOutput {Ω : Type} [MeasurableSpace Ω]
    (c : Config) (hc : 0 < c.calls) (center : E) (R G G0 κ : ℝ)
    (P : ProbabilityMeasure (ℕ → Ω)) {oracle : E → Ω → E}
    (ho : Measurable (Function.uncurry oracle)) (T : ℕ) :
    Measurable (fun ξ => burninOutput c hc center R G G0 κ T
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ) := by
  have h := ((measurable_burnin_advance c center R G G0 κ ho T 0).comp
    ((measurable_const (a := (center, false))).prodMk measurable_id)).fst
  convert h using 1
  funext ξ
  exact execute_burnin c hc center R G G0 κ P oracle ξ T

section Moments

variable {D Ξ F : Type*} [MeasurableSpace D] [MeasurableSpace Ξ]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
lemma measurable_clipped_mean (p : Measure Ξ) [SFinite p] {B : D → ℝ} {X : D → Ξ → F}
    (hB : Measurable B) (hX : Measurable (Function.uncurry X)) :
    Measurable (fun a => ∫ ω, OracleTemplate.clip (B a) (X a ω) ∂p) := by
  have h : Measurable (fun z : D × Ξ => OracleTemplate.clip (B z.1) (X z.1 z.2)) :=
    LongTails.Proofs.StochasticEnvelopePilot.measurable_variable_clip (hB.comp measurable_fst) hX
  exact h.stronglyMeasurable.integral_prod_right.measurable

lemma measurable_clipped_secondMoment (p : Measure Ξ) [SFinite p] {B : D → ℝ} {X : D → Ξ → F}
    (hB : Measurable B) (hX : Measurable (Function.uncurry X)) :
    Measurable (fun a => ∫ ω, ‖OracleTemplate.clip (B a) (X a ω)‖ ^ 2 ∂p) := by
  have h : Measurable (fun z : D × Ξ => ‖OracleTemplate.clip (B z.1) (X z.1 z.2)‖ ^ 2) :=
    ((LongTails.Proofs.StochasticEnvelopePilot.measurable_variable_clip (hB.comp measurable_fst) hX).norm).pow_const 2
  exact h.stronglyMeasurable.integral_prod_right.measurable

end Moments

end LongTails.Proofs.GeneralizedLipschitzExecution
