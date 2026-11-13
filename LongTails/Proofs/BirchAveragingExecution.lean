import LongTails.Algorithms.BirchAveraging
import LongTails.Proofs.Execution

namespace LongTails.Setups.BirchNonIID

def workerCalls (workers t : ℕ) (i : Fin workers) : ℕ :=
  ((Finset.range t).filter (fun k => k % workers = i.val)).card

theorem workerCalls_full {workers : ℕ} (hw : 0 < workers) (B : ℕ) (i : Fin workers) :
    workerCalls workers (workers * B) i = B := by
  unfold workerCalls
  conv_rhs => rw [← Finset.card_range B]
  apply Finset.card_bij (fun t _ => t / workers)
  · intro t ht
    have hb := (Finset.mem_filter.mp ht).1
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa [Nat.mul_comm] using Finset.mem_range.mp hb
  · intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hda := Nat.div_add_mod a workers
    have hdb := Nat.div_add_mod b workers
    rw [he, ha'] at hda
    rw [hb'] at hdb
    omega
  · intro b hb
    have hb' := Finset.mem_range.mp hb
    refine ⟨b * workers + i.val, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_range.mpr
        have hm := Nat.mul_le_mul_right workers (Nat.succ_le_of_lt hb')
        nlinarith [i.isLt]
      · simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt i.isLt, Nat.zero_add]

theorem workerCalls_succ {workers : ℕ} (t : ℕ) (i : Fin workers) :
    workerCalls workers (t + 1) i = workerCalls workers t i +
      if t % workers = i.val then 1 else 0 := by
  unfold workerCalls
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

/-- The next scheduled worker always has budget left before the full schedule ends. -/
theorem workerCalls_safe {workers : ℕ} (hw : 0 < workers) (B t : ℕ)
    (ht : t < workers * B) :
    workerCalls workers t (scheduledWorker workers hw t) < B := by
  rw [← workerCalls_full hw B (scheduledWorker workers hw t)]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.filter_subset_filter _ (Finset.range_mono ht.le), ?_⟩
  intro he
  have hmem : t ∈ (Finset.range (workers * B)).filter
      (fun k => k % workers = (scheduledWorker workers hw t).val) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, rfl⟩
  rw [← he] at hmem
  have := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
  omega

def workerRemaining (workers B t : ℕ) (i : Fin workers) : ℕ :=
  B - workerCalls workers t i

theorem workerRemaining_zero (workers B : ℕ) :
    workerRemaining workers B 0 = fun _ => B := by
  funext i
  simp [workerRemaining, workerCalls]

theorem workerRemaining_succ {workers : ℕ} (hw : 0 < workers) (B t : ℕ) :
    workerRemaining workers B (t + 1) =
      Function.update (workerRemaining workers B t) (scheduledWorker workers hw t)
        (workerRemaining workers B t (scheduledWorker workers hw t) - 1) := by
  funext i
  by_cases h : i = scheduledWorker workers hw t
  · subst i
    simp [Function.update, workerRemaining, workerCalls_succ, scheduledWorker, Nat.sub_sub]
  · have hv : t % workers ≠ i.val := by
      intro he
      apply h
      apply Fin.ext
      exact he.symm
    simp [Function.update, h, workerRemaining, workerCalls_succ, hv]

theorem workerRemaining_safe {workers : ℕ} (hw : 0 < workers) (B t : ℕ)
    (ht : t < workers * B) :
    0 < workerRemaining workers B t (scheduledWorker workers hw t) :=
  Nat.sub_pos_of_lt (workerCalls_safe hw B t ht)

end LongTails.Setups.BirchNonIID

open MeasureTheory
open scoped BigOperators

namespace LongTails.Setups.BirchNonIID

open OracleTemplate
open OracleTemplate.Rennala (Point)

noncomputable def executionTape {workers d : ℕ} {Ω : Type} (hw : 0 < workers)
    (x0 : Point d) (η : ℝ) (K : ℕ) (g : Fin workers → Point d → Ω → Point d)
    (ξ : ℕ → Ω) : ℕ → (ℕ → Point d)
  | 0 => fun _ => 0
  | t + 1 => Function.update (executionTape hw x0 η K g ξ t) t
      (g (scheduledWorker workers hw t)
        (averagingQuery hw x0 η K t (executionTape hw x0 η K g ξ t)).2 (ξ t))

noncomputable def executionQuery {workers d : ℕ} {Ω : Type} (hw : 0 < workers)
    (x0 : Point d) (η : ℝ) (K : ℕ) (g : Fin workers → Point d → Ω → Point d)
    (ξ : ℕ → Ω) (t : ℕ) : Point d :=
  (averagingQuery hw x0 η K t (executionTape hw x0 η K g ξ t)).2

theorem correctedAveraging_execute {workers d K R : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (hw : 0 < workers) (hK : 0 < K) (hR : 0 < R) (x0 : Point d) (η : ℝ)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Fin workers → Point d → Ω → Point d)
    (j : Fin (workers * K * R)) (ξ : ℕ → Ω) :
    execute (workerOracle P g) (correctedAveraging workers d K R hw hK hR x0 η)
      (fun _ => K * R) j ξ = executionQuery hw x0 η K g ξ j.val := by
  let state : ℕ → AveragingState d := fun t =>
    ⟨t, executionTape hw x0 η K g ξ t, j.val,
      if j.val < t then executionQuery hw x0 η K g ξ j.val else x0⟩
  apply execute_eq_of_safe_prefix (workerOracle P g)
    (correctedAveraging workers d K R hw hK hR x0 η) (fun _ => K * R) j ξ
    state (workerRemaining workers (K * R)) (workers * K * R)
  · simp [state, executionTape, correctedAveraging]
  · intro history
    change state (history.length + 1) =
      (⟨history.length + 1,
        Function.update (executionTape hw x0 η K g ξ history.length) history.length
          (g (scheduledWorker workers hw history.length)
            (executionQuery hw x0 η K g ξ history.length) (ξ history.length)), j.val,
        if history.length = j.val then executionQuery hw x0 η K g ξ history.length
        else (state history.length).saved⟩ : AveragingState d)
    dsimp [state, executionTape, executionQuery]
    congr 1
    split_ifs <;> simp_all <;> omega
  · exact workerRemaining_zero workers (K * R)
  · intro t
    exact workerRemaining_succ hw (K * R) t
  · intro t ht
    exact workerRemaining_safe hw (K * R) t (by simpa [Nat.mul_assoc] using ht)
  · intro t ht
    have hj : j.val < t := lt_of_lt_of_le j.isLt ht
    change (state t).saved = _
    simp [state, hj]
  · simp [Nat.mul_assoc]

theorem measurable_executionTape {workers d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (hw : 0 < workers) (x0 : Point d) (η : ℝ) (K : ℕ)
    (g : Fin workers → Point d → Ω → Point d)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => executionTape hw x0 η K g ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hq := (measurable_averagingQuery hw x0 η K t).comp ih
    have hr := (hg (scheduledWorker workers hw t)).comp
      (hq.prodMk (measurable_pi_apply t))
    apply Measurable.of_eval
    intro k
    by_cases hk : k = t
    · subst k
      simpa [executionTape, Function.update, Function.comp_def, Function.uncurry] using hr
    · simpa [executionTape, Function.update, hk, Function.comp_def] using (measurable_pi_apply k).comp ih

theorem measurable_executionQuery {workers d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (hw : 0 < workers) (x0 : Point d) (η : ℝ) (K : ℕ)
    (g : Fin workers → Point d → Ω → Point d)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (t : ℕ) :
    Measurable (fun ξ : ℕ → Ω => executionQuery hw x0 η K g ξ t) :=
  (measurable_averagingQuery hw x0 η K t).comp
    (measurable_executionTape hw x0 η K g hg t)

theorem measurable_correctedAveraging_execute {workers d K R : ℕ} {Ω : Type}
    [MeasurableSpace Ω] (hw : 0 < workers) (hK : 0 < K) (hR : 0 < R)
    (x0 : Point d) (η : ℝ) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Fin workers → Point d → Ω → Point d)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) :
    Measurable (fun seed : Fin (workers * K * R) × (ℕ → Ω) =>
      execute (workerOracle P g) (correctedAveraging workers d K R hw hK hR x0 η)
        (fun _ => K * R) seed.1 seed.2) := by
  simp only [correctedAveraging_execute]
  exact measurable_from_prod_countable_right
    (fun j => measurable_executionQuery hw x0 η K g hg j.val)

end LongTails.Setups.BirchNonIID

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

theorem blockIndex_before {workers : ℕ} (i : Fin workers) {b t : ℕ}
    (hb : b < t / workers) : b * workers + i.val < t := by
  have hm := Nat.mul_le_mul_right workers (Nat.succ_le_of_lt hb)
  calc
    b * workers + i.val < b * workers + workers := Nat.add_lt_add_left i.isLt _
    _ = b.succ * workers := by rw [Nat.succ_mul]
    _ ≤ t / workers * workers := hm
    _ ≤ t := Nat.div_mul_le_self t workers

/-- Queries are determined by already received replies, even though replay accepts a full tape. -/
theorem averagingQuery_congr {workers d : ℕ} (hw : 0 < workers) (_hK : 0 < K)
    (x0 : Point d) (η : ℝ) (t : ℕ) {tape tape' : ℕ → Point d}
    (h : ∀ u, u < t → tape u = tape' u) :
    averagingQuery hw x0 η K t tape = averagingQuery hw x0 η K t tape' := by
  have he := Nat.div_add_mod (t / workers) K
  have hs : replayServer x0 η K (replyBlocks (workers := workers) K tape) (t / workers / K) =
      replayServer x0 η K (replyBlocks (workers := workers) K tape') (t / workers / K) := by
    apply replayServer_congr
    intro s hs j hj i
    apply h
    apply blockIndex_before i
    have hm := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hs)
    calc
      s * K + j < s * K + K := Nat.add_lt_add_left hj _
      _ = s.succ * K := by rw [Nat.succ_mul]
      _ ≤ t / workers / K * K := hm
      _ ≤ t / workers := Nat.div_mul_le_self _ _
  unfold averagingQuery
  simp only [hs]
  congr 1
  apply replayLocal_congr
  intro j hj i
  apply h
  apply blockIndex_before i
  nlinarith

/-- A reference tape whose replies match the oracle determines the actual run. -/
theorem executionTape_reference {workers d : ℕ} {Ω : Type} (hw : 0 < workers)
    (hK : 0 < K) (x0 : Point d) (η : ℝ)
    (g : Fin workers → Point d → Ω → Point d) (ξ : ℕ → Ω) (tape : ℕ → Point d)
    (href : ∀ t, g (scheduledWorker workers hw t)
      (averagingQuery hw x0 η K t tape).2 (ξ t) = tape t) :
    ∀ t u, u < t → executionTape hw x0 η K g ξ t u = tape u := by
  intro t
  induction t with
  | zero => intro u hu; omega
  | succ t ih =>
    intro u hu
    have hq := averagingQuery_congr hw hK x0 η t ih
    by_cases hut : u = t
    · subst u
      simpa [executionTape, Function.update, hq] using href t
    · have hu' : u < t := by omega
      simpa [executionTape, Function.update, hut] using ih u hu'

theorem executionQuery_reference {workers d : ℕ} {Ω : Type} (hw : 0 < workers)
    (hK : 0 < K) (x0 : Point d) (η : ℝ)
    (g : Fin workers → Point d → Ω → Point d) (ξ : ℕ → Ω) (tape : ℕ → Point d)
    (href : ∀ t, g (scheduledWorker workers hw t)
      (averagingQuery hw x0 η K t tape).2 (ξ t) = tape t) (t : ℕ) :
    executionQuery hw x0 η K g ξ t = (averagingQuery hw x0 η K t tape).2 := by
  exact congrArg Prod.snd (averagingQuery_congr hw hK x0 η t
    (executionTape_reference hw hK x0 η g ξ tape href t))

end LongTails.Setups.BirchNonIID

open MeasureTheory

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

noncomputable def referencePoint {workers d : ℕ} (hw : 0 < workers)
    (I : Instance workers d) (x0 : Point d) (η : ℝ) (K t : ℕ) : Point d :=
  localPath I (scheduledWorker workers hw t)
    (serverPath I x0 η K (t / workers / K)) η (t / workers % K)

noncomputable def referenceTape {workers d : ℕ} (hw : 0 < workers)
    (I : Instance workers d) (x0 : Point d) (η : ℝ) (K t : ℕ) : Point d :=
  gradient (I.localObjective (scheduledWorker workers hw t)) (referencePoint hw I x0 η K t)

theorem referenceTape_block {workers d : ℕ} (hw : 0 < workers) (hK : 0 < K)
    (I : Instance workers d) (x0 : Point d) (η : ℝ) (r k : ℕ) (hk : k < K) (i : Fin workers) :
    replyBlocks K (referenceTape hw I x0 η K) r k i =
      gradient (I.localObjective i) (localPath I i (serverPath I x0 η K r) η k) := by
  have hdiv : ((r * K + k) * workers + i.val) / workers = r * K + k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  have hr : (r * K + k) / K = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hk, Nat.zero_add]
  have hm : (r * K + k) % K = k := by simp [Nat.add_mod, Nat.mod_eq_of_lt hk]
  have hi : scheduledWorker workers hw ((r * K + k) * workers + i.val) = i := by
    apply Fin.ext
    simp [scheduledWorker, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  simp only [replyBlocks, referenceTape, referencePoint, hdiv, hr, hm, hi]

theorem averagingQuery_reference {workers d : ℕ} (hw : 0 < workers) (hK : 0 < K)
    (I : Instance workers d)
    (hg : ∀ i x, HasGradientAt (I.localObjective i) (gradient (I.localObjective i) x) x)
    (x0 : Point d) (η : ℝ) (t : ℕ) :
    (averagingQuery hw x0 η K t (referenceTape hw I x0 η K)).2 =
      referencePoint hw I x0 η K t := by
  have hs : replayServer x0 η K (replyBlocks (workers := workers) K (referenceTape hw I x0 η K)) (t / workers / K) =
      serverPath I x0 η K (t / workers / K) := by
    calc
      _ = replayServer x0 η K (fun r k i =>
          gradient (I.localObjective i) (localPath I i (serverPath I x0 η K r) η k))
          (t / workers / K) := by
        apply replayServer_congr
        intro r _ k hk i
        exact referenceTape_block hw hK I x0 η r k hk i
      _ = _ := replayServer_exact I hg x0 η K _
  change replayLocal _ η _ _ _ = _
  rw [hs]
  calc
    _ = replayLocal (serverPath I x0 η K (t / workers / K)) η
        (fun k i => gradient (I.localObjective i)
          (localPath I i (serverPath I x0 η K (t / workers / K)) η k))
        (scheduledWorker workers hw t) (t / workers % K) := by
      apply replayLocal_congr
      intro k hk i
      exact referenceTape_block hw hK I x0 η _ k
        (lt_trans hk (Nat.mod_lt _ hK)) i
    _ = _ := replayLocal_exact I hg _ η _ _

/-- Zero variance identifies the entire actual query sequence almost surely. -/
theorem executionQuery_ae_reference {workers d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {P : ProbabilityMeasure (ℕ → Ω)}
    (hw : 0 < workers) (hK : 0 < K) (I : Instance workers d)
    (hf : ∀ i x, HasGradientAt (I.localObjective i) (gradient (I.localObjective i) x) x)
    (g : Fin workers → Point d → Ω → Point d)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point d) Ω (μ : Measure Ω) (I.localObjective i) (g i) 0)
    (x0 : Point d) (η : ℝ) :
    ∀ᵐ ξ ∂(P : Measure (ℕ → Ω)), ∀ t,
      executionQuery hw x0 η K g ξ t = referencePoint hw I x0 η K t := by
  have h := zeroVariance_schedule_exact hiid hg
    (fun t => (scheduledWorker workers hw t, referencePoint hw I x0 η K t))
  filter_upwards [h] with ξ hξ
  intro t
  calc
    _ = (averagingQuery hw x0 η K t (referenceTape hw I x0 η K)).2 := by
      apply executionQuery_reference hw hK
      intro s
      rw [averagingQuery_reference hw hK I hf]
      exact hξ s
    _ = _ := averagingQuery_reference hw hK I hf x0 η t

end LongTails.Setups.BirchNonIID

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

theorem uniform_output_ae_constant {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    [NeZero N] (P : ProbabilityMeasure Ω) (f : Point d → ℝ)
    (x : Fin N → Ω → Point d) (z : Fin N → Point d)
    (hm : ∀ j, Measurable (x j)) (hx : ∀ j, x j =ᵐ[(P : Measure Ω)] fun _ => z j) :
    let Q := (PMF.uniformOfFintype (Fin N)).toMeasure.prod (P : Measure Ω)
    Integrable (fun s : Fin N × Ω => ‖gradient f (x s.1 s.2)‖ ^ 2) Q ∧
    (∫ s : Fin N × Ω, ‖gradient f (x s.1 s.2)‖ ^ 2 ∂Q) =
      (1 / (N : ℝ)) * ∑ j, ‖gradient f (z j)‖ ^ 2 := by
  have he (j : Fin N) : (fun ω => ‖gradient f (x j ω)‖ ^ 2) =ᵐ[(P : Measure Ω)]
      fun _ => ‖gradient f (z j)‖ ^ 2 := by
    filter_upwards [hx j] with ω hω
    rw [hω]
  have hi (j : Fin N) : Integrable (fun ω => ‖gradient f (x j ω)‖ ^ 2) (P : Measure Ω) :=
    (integrable_const _).congr (he j).symm
  have hv (j : Fin N) : (∫ ω, ‖gradient f (x j ω)‖ ^ 2 ∂(P : Measure Ω)) =
      ‖gradient f (z j)‖ ^ 2 := by
    rw [integral_congr_ae (he j)]
    simp
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ N =>
    have h := OracleTemplate.Rennala.uniform_prefix_accuracy P f N x
      ((1 / ((N + 1 : ℕ) : ℝ)) * ∑ j, ‖gradient f (z j)‖ ^ 2) hm hi (by simp only [hv]; rfl)
    exact ⟨h.2.1, h.2.2.1.trans (by simp only [hv])⟩

theorem correctedAveraging_output_moments {workers d K R : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {μ : ProbabilityMeasure Ω} {P : ProbabilityMeasure (ℕ → Ω)}
    (hw : 0 < workers) (hK : 0 < K) (hR : 0 < R) (I : Instance workers d)
    (hf : ∀ i x, HasGradientAt (I.localObjective i) (gradient (I.localObjective i) x) x)
    (g : Fin workers → Point d → Ω → Point d)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (μ : Measure Ω) (P : Measure (ℕ → Ω)))
    (hg : ∀ i, LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point d) Ω (μ : Measure Ω) (I.localObjective i) (g i) 0)
    (x0 : Point d) (η : ℝ) :
    let A := correctedAveraging workers d K R hw hK hR x0 η
    let Q := (A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω))
    Integrable (fun s : Fin (workers * K * R) × (ℕ → Ω) =>
      ‖gradient (objective I) (OracleTemplate.execute (workerOracle P g) A
        (fun _ => K * R) s.1 s.2)‖ ^ 2) Q ∧
    (∫ s : Fin (workers * K * R) × (ℕ → Ω),
      ‖gradient (objective I) (OracleTemplate.execute (workerOracle P g) A
        (fun _ => K * R) s.1 s.2)‖ ^ 2 ∂Q) =
      (1 / ((workers * K * R : ℕ) : ℝ)) *
        ∑ j : Fin (workers * K * R), ‖gradient (objective I) (referencePoint hw I x0 η K j.val)‖ ^ 2 := by
  let : NeZero (workers * K * R) := ⟨Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos hw hK) hR)⟩
  have hae := executionQuery_ae_reference hw hK I hf g hiid hg x0 η
  have hx (j : Fin (workers * K * R)) :
      (fun ξ => executionQuery hw x0 η K g ξ j.val) =ᵐ[(P : Measure (ℕ → Ω))]
        fun _ => referencePoint hw I x0 η K j.val := by
    filter_upwards [hae] with ξ hξ
    exact hξ j.val
  have hu := uniform_output_ae_constant P (objective I)
    (fun j ξ => executionQuery hw x0 η K g ξ j.val)
    (fun j : Fin (workers * K * R) => referencePoint hw I x0 η K j.val)
    (fun j => measurable_executionQuery hw x0 η K g (fun i => (hg i).measurable) j.val) hx
  dsimp only
  simp only [correctedAveraging_execute]
  set_option backward.isDefEq.respectTransparency false in
    exact hu

end LongTails.Setups.BirchNonIID

open scoped BigOperators

namespace LongTails.Setups.BirchNonIID

open OracleTemplate.Rennala (Point)

theorem sum_range_blocks (f : ℕ → ℝ) (B n : ℕ) :
    (∑ t ∈ Finset.range (B * n), f t) =
      ∑ b ∈ Finset.range B, ∑ i ∈ Finset.range n, f (b * n + i) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem referencePoint_block {workers d : ℕ} (hw : 0 < workers) (hK : 0 < K)
    (I : Instance workers d) (x0 : Point d) (η : ℝ) (r k : ℕ) (hk : k < K) (i : Fin workers) :
    referencePoint hw I x0 η K ((r * K + k) * workers + i.val) =
      localPath I i (serverPath I x0 η K r) η k := by
  have hdiv : ((r * K + k) * workers + i.val) / workers = r * K + k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  have hr : (r * K + k) / K = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hk, Nat.zero_add]
  have hm : (r * K + k) % K = k := by simp [Nat.add_mod, Nat.mod_eq_of_lt hk]
  have hi : scheduledWorker workers hw ((r * K + k) * workers + i.val) = i := by
    apply Fin.ext
    simp [scheduledWorker, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  simp only [referencePoint, hdiv, hr, hm, hi]

theorem referencePoint_energy_sum {workers d K : ℕ} (hw : 0 < workers) (hK : 0 < K)
    (I : Instance workers d) (x0 : Point d) (η : ℝ) (R : ℕ) :
    (∑ j : Fin (workers * K * R), ‖gradient (objective I) (referencePoint hw I x0 η K j.val)‖ ^ 2) =
      ∑ r ∈ Finset.range R, roundGradientEnergy I (serverPath I x0 η K r) η K := by
  rw [← Finset.sum_range (n := workers * K * R)
    (fun t => ‖gradient (objective I) (referencePoint hw I x0 η K t)‖ ^ 2)]
  have hsize : workers * K * R = R * (K * workers) := by ring
  rw [hsize, sum_range_blocks]
  apply Finset.sum_congr rfl
  intro r _
  rw [sum_range_blocks]
  unfold roundGradientEnergy
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hidx : r * (K * workers) + (k * workers + i.val) = (r * K + k) * workers + i.val := by ring
  rw [hidx, referencePoint_block hw hK I x0 η r k (Finset.mem_range.mp hk) i]

theorem referencePoint_average_bound {workers d K R : ℕ} {I : Instance workers d}
    {L δ η Δ : ℝ} (hw : 0 < workers) (hK : 0 < K) (hR : 0 < R)
    (hη : 0 < η) (hL : 0 < L) (hδ : 0 < δ)
    (hs : LongTails.Setups.BirchSgd.SmoothObjective (objective I) L)
    (hd : GradientDifferenceSimilarity I δ) (x0 : Point d)
    (hstep : η * L ≤ 1 / 4)
    (hh : η * L * (K : ℝ) ≤ Real.log (1 + L / δ) / 8)
    (hlower : ∀ x, I.lower ≤ objective I x)
    (hgap : objective I x0 - I.lower ≤ Δ) :
    (1 / ((workers * K * R : ℕ) : ℝ)) *
      (∑ j : Fin (workers * K * R), ‖gradient (objective I) (referencePoint hw I x0 η K j.val)‖ ^ 2) ≤
      2 * Δ / (η * (K : ℝ) * (R : ℝ)) := by
  rw [referencePoint_energy_sum hw hK]
  have he := serverPath_gradient_energy hw hη hL hδ hs hd x0 K R hstep hh hlower hgap
  have hw' : (workers : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hw
  have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hR
  calc
    _ ≤ (1 / ((workers * K * R : ℕ) : ℝ)) * (2 * (workers : ℝ) * Δ / η) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by push_cast; field_simp

end LongTails.Setups.BirchNonIID
