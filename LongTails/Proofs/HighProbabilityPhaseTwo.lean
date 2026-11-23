import LongTails.Proofs.HighProbabilityExecution
import LongTails.Proofs.HighProbabilityRoundStep
import LongTails.Proofs.HighProbabilityConstants

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.HighProbabilityPhaseTwo

open OracleTemplate QueryPlan LongTails.Algorithms.HighProbabilityStationarity
open LongTails.Proofs.HighProbabilityAdapted LongTails.Proofs.HighProbabilityExecution
open LongTails.Proofs.HighProbabilityRounds LongTails.Proofs.HighProbabilityRoundStep
open LongTails.Proofs.HighProbabilityTest LongTails.Proofs.HighProbabilityConstants

instance optionFinMeasurable (J : ℕ) : MeasurableSpace (Option (Fin J)) := ⊤

instance optionFinDiscrete (J : ℕ) : DiscreteMeasurableSpace (Option (Fin J)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

section Generic

variable {Q R Ω : Type*} (g : Q → Ω → R) (ξ : ℕ → Ω)

lemma traj_shift {X Z : Type*} (F : X → Z → X) (s : X) (b : ℕ → Z) (n : ℕ) :
    traj F s b (n + 1) = traj F (F s (b 0)) (fun t => b (t + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show F (traj F s b (n + 1)) (b (n + 1)) = _
    rw [ih]
    rfl

lemma stepIter_traj {S : Type*} {c : ℕ} (body : S → QueryPlan Q R S c)
    (F : S → (Fin c → Ω) → S)
    (hF : ∀ s call, sampledEval g ξ (body s) call = F s (fun j => ξ (call + j.val))) (n : ℕ)
    (s : S) (call : ℕ) :
    stepIter g ξ body n s call = traj F s (fun t j => ξ (call + t * c + j.val)) n := by
  induction n generalizing s call with
  | zero => rfl
  | succ n ih =>
    rw [stepIter, ih, hF, traj_shift]
    have e : (fun t (j : Fin c) => ξ (call + (t + 1) * c + j.val)) =
        fun t j => ξ (call + c + t * c + j.val) := by
      funext t j; congr 1; ring
    simp only [zero_mul, add_zero]
    rw [e]

end Generic

lemma calls_eq (Λ k0 r lv : ℕ) (hlv : lv ≤ Λ) :
    2 ^ (Λ - lv) * (k0 * 2 ^ lv * r) = k0 * r * 2 ^ Λ := by
  rw [mul_comm]
  exact round_calls Λ k0 r lv hlv

def blockOf {Ω : Type*} (K b : ℕ) {N : ℕ} (h : K * b = N) (z : Fin N → Ω) : Fin K → Fin b → Ω :=
  fun i l => z (Fin.cast h (finProdFinEquiv (i, l)))

lemma blockOf_preserving {Ω : Type} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p]
    (K b : ℕ) {N : ℕ} (h : K * b = N) :
    MeasurePreserving (blockOf K b h) (Measure.pi fun _ : Fin N => p)
      (Measure.pi fun _ : Fin K => Measure.pi fun _ : Fin b => p) := by
  subst h
  exact OracleTemplate.SublevelRobustGradient.reindex_preserving p K b

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω]

noncomputable def roundMap (g : E → Ω → E) (ε α : ℝ) (Λ k0 r : ℕ) (hk0 : 0 < k0) (x0 : E)
    (Y : Fin (2 ^ Λ) → E) (s : Ladder (2 ^ Λ)) (z : Fin (k0 * r * 2 ^ Λ) → Ω) :
    Ladder (2 ^ Λ) :=
  (s.1 + 1, nextSlots s.2 (fun i : Fin (2 ^ (Λ - min s.1 Λ)) =>
    testPasses α (threshold ε α (min s.1 Λ)) (Nat.mul_pos hk0 (Nat.two_pow_pos (min s.1 Λ)))
      (slots s.2 i) (fun l => g (((slots s.2 i).map Y).getD x0)
        (blockOf _ _ (calls_eq Λ k0 r (min s.1 Λ) (min_le_right _ _)) z i l))))

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma round_eval (g : E → Ω → E) (ξ : ℕ → Ω) (ε α : ℝ) (Λ k0 r : ℕ) (hk0 : 0 < k0) (x0 : E)
    (Y : Fin (2 ^ Λ) → E) (s : Ladder (2 ^ Λ)) (call : ℕ) :
    sampledEval g ξ (roundPlan ε α Λ k0 r hk0 x0 Y s) call =
      roundMap g ε α Λ k0 r hk0 x0 Y s (fun j => ξ (call + j.val)) := by
  unfold roundPlan roundMap
  rw [sampledEval_castPlan, sampledEval_map, sampledEval_collectPlans]
  congr 2
  funext i
  unfold testPlan
  rw [sampledEval_map, sampledEval_samplePlan]
  congr 1
  funext l
  congr 1
  simp only [blockOf, finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_cast]
  congr 1
  ring

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma phaseTwo_eval (g : E → Ω → E) (ξ : ℕ → Ω) (ε α : ℝ) (Λ k0 r : ℕ) (hk0 : 0 < k0) (x0 : E)
    (Y : Fin (2 ^ Λ) → E) (call : ℕ) :
    sampledEval g ξ (phaseTwo ε α Λ k0 r hk0 x0 Y) call =
      (((traj (roundMap g ε α Λ k0 r hk0 x0 Y) (0, fun j => some j)
        (fun t j => ξ (call + t * (k0 * r * 2 ^ Λ) + j.val)) (Λ + 1)).2
          ⟨0, Nat.two_pow_pos Λ⟩).map Y).getD x0 := by
  unfold phaseTwo
  rw [sampledEval_map, sampledEval_stepRepeat,
    stepIter_traj g ξ _ (roundMap g ε α Λ k0 r hk0 x0 Y) (round_eval g ξ ε α Λ k0 r hk0 x0 Y)]

lemma measurable_decide_of {α' : Type*} [MeasurableSpace α'] {P : α' → Prop}
    [DecidablePred P] (hP : MeasurableSet {a | P a}) : Measurable (fun a => decide (P a)) := by
  refine measurable_to_countable' fun b => ?_
  cases b
  · have : (fun a => decide (P a)) ⁻¹' {false} = {a | P a}ᶜ := by
      ext a; simp
    rw [this]; exact hP.compl
  · have : (fun a => decide (P a)) ⁻¹' {true} = {a | P a} := by
      ext a; simp
    rw [this]; exact hP

omit [CompleteSpace E] in
lemma measurable_aggregate_vec {k r : ℕ} (hk : 0 < k) (B : ℝ) :
    Measurable (fun v : Fin (k * r) → E =>
      OracleTemplate.SublevelRobustGradient.aggregate (m := k) (b := r) hk B v) := by
  unfold OracleTemplate.SublevelRobustGradient.aggregate
  refine (OracleTemplate.SublevelRobustGradient.measurable_robustCenter hk B).comp ?_
  refine Measurable.of_eval fun i => ?_
  unfold OracleTemplate.SublevelRobustGradient.blockMean
  exact (Finset.measurable_sum Finset.univ fun l _ =>
    measurable_pi_apply (finProdFinEquiv (i, l))).const_smul _

omit [CompleteSpace E] in
lemma measurable_testPasses {β : Type*} (α τ : ℝ) {k r : ℕ} (hk : 0 < k) (e : Option β) :
    Measurable (testPasses (E := E) α τ hk e : (Fin (k * r) → E) → Bool) := by
  classical
  have hd : Measurable (fun v : Fin (k * r) → E => decide
      (‖OracleTemplate.SublevelRobustGradient.aggregate (m := k) (b := r) hk (2 * α) v‖ ≤ τ)) :=
    measurable_decide_of (measurableSet_le (measurable_aggregate_vec hk (2 * α)).norm
      measurable_const)
  have he : (testPasses (E := E) α τ hk e : (Fin (k * r) → E) → Bool) =
      (fun d => e.isSome && d) ∘ fun v => decide
        (‖OracleTemplate.SublevelRobustGradient.aggregate (m := k) (b := r) hk (2 * α) v‖ ≤ τ) := by
    funext v
    simp only [testPasses, Function.comp]
  rw [he]
  exact (measurable_of_countable _).comp hd

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma measurable_point {J : ℕ} (e : Option (Fin J)) (x0 : E) :
    Measurable (fun Y : Fin J → E => (e.map Y).getD x0) := by
  cases e with
  | none => exact measurable_const
  | some a => exact measurable_pi_apply a

omit [CompleteSpace E] in
lemma measurable_roundMap_slice {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (ε α : ℝ) (Λ k0 r : ℕ) (hk0 : 0 < k0) (x0 : E) (s : Ladder (2 ^ Λ)) :
    Measurable (fun w : (Fin (2 ^ Λ) → E) × (Fin (k0 * r * 2 ^ Λ) → Ω) =>
      roundMap g ε α Λ k0 r hk0 x0 w.1 s w.2) := by
  have hpass : Measurable (fun w : (Fin (2 ^ Λ) → E) × (Fin (k0 * r * 2 ^ Λ) → Ω) =>
      fun i : Fin (2 ^ (Λ - min s.1 Λ)) =>
        testPasses α (threshold ε α (min s.1 Λ)) (Nat.mul_pos hk0 (Nat.two_pow_pos (min s.1 Λ)))
          (slots s.2 i) (fun l => g (((slots s.2 i).map w.1).getD x0)
            (blockOf _ _ (calls_eq Λ k0 r (min s.1 Λ) (min_le_right _ _)) w.2 i l))) := by
    refine Measurable.of_eval fun i => ?_
    refine (measurable_testPasses α _ _ _).comp ?_
    refine Measurable.of_eval fun l => ?_
    exact hg.comp (((measurable_point (slots s.2 i) x0).comp measurable_fst).prodMk
      ((measurable_pi_apply _).comp measurable_snd))
  have he : (fun w : (Fin (2 ^ Λ) → E) × (Fin (k0 * r * 2 ^ Λ) → Ω) =>
      roundMap g ε α Λ k0 r hk0 x0 w.1 s w.2) =
      (fun pass : Fin (2 ^ (Λ - min s.1 Λ)) → Bool => (s.1 + 1, nextSlots s.2 pass)) ∘
        (fun w : (Fin (2 ^ Λ) → E) × (Fin (k0 * r * 2 ^ Λ) → Ω) =>
          fun i : Fin (2 ^ (Λ - min s.1 Λ)) =>
            testPasses α (threshold ε α (min s.1 Λ))
              (Nat.mul_pos hk0 (Nat.two_pow_pos (min s.1 Λ)))
              (slots s.2 i) (fun l => g (((slots s.2 i).map w.1).getD x0)
                (blockOf _ _ (calls_eq Λ k0 r (min s.1 Λ) (min_le_right _ _)) w.2 i l))) := rfl
  rw [he]
  exact (measurable_of_countable _).comp hpass

noncomputable def chainStep (g : E → Ω → E) (ε α : ℝ) (Λ k0 r : ℕ) (hk0 : 0 < k0) (x0 : E)
    (w : (Fin (2 ^ Λ) → E) × Ladder (2 ^ Λ)) (z : Fin (k0 * r * 2 ^ Λ) → Ω) :
    (Fin (2 ^ Λ) → E) × Ladder (2 ^ Λ) :=
  (w.1, roundMap g ε α Λ k0 r hk0 x0 w.1 w.2 z)

omit [CompleteSpace E] in
lemma measurable_chainStep {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (ε α : ℝ) (Λ k0 r : ℕ) (hk0 : 0 < k0) (x0 : E) :
    Measurable (Function.uncurry (chainStep g ε α Λ k0 r hk0 x0)) := by
  have hR : Measurable (fun u : ((Fin (2 ^ Λ) → E) × (Fin (k0 * r * 2 ^ Λ) → Ω)) ×
      Ladder (2 ^ Λ) => roundMap g ε α Λ k0 r hk0 x0 u.1.1 u.2 u.1.2) :=
    measurable_from_prod_countable_left fun s =>
      measurable_roundMap_slice hg ε α Λ k0 r hk0 x0 s
  have hperm : Measurable (fun w : ((Fin (2 ^ Λ) → E) × Ladder (2 ^ Λ)) ×
      (Fin (k0 * r * 2 ^ Λ) → Ω) => ((w.1.1, w.2), w.1.2)) :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  exact (measurable_fst.comp measurable_fst).prodMk (hR.comp hperm)

lemma measurableSet_of_slices {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Countable B]
    [MeasurableSingletonClass B] {S : Set (A × B)} (h : ∀ b, MeasurableSet {a | (a, b) ∈ S}) :
    MeasurableSet S := by
  have he : S = ⋃ b, {a | (a, b) ∈ S} ×ˢ ({b} : Set B) := by
    ext ⟨a, b⟩
    simp
  rw [he]
  exact MeasurableSet.iUnion fun b => (h b).prod (measurableSet_singleton b)

lemma slots_nextSlots {β : Type*} {J K : ℕ} (e : Fin J → Option β) (pass : Fin K → Bool)
    (j : ℕ) (hj : j < J) : slots (nextSlots e pass) j = passers (slots e) pass j := by
  simp [slots, nextSlots, hj]

def width (Λ n : ℕ) : ℕ := 2 ^ (Λ - min n Λ)

lemma width_le (Λ n : ℕ) : width Λ n ≤ 2 ^ Λ :=
  Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)

def healthy (f : E → ℝ) (ε α : ℝ) (Λ n : ℕ) : Set ((Fin (2 ^ Λ) → E) × Ladder (2 ^ Λ)) :=
  {w | n ≤ Λ + 1 → w.2.1 = n ∧ (∀ i < width Λ n, ∃ a, slots w.2.2 i = some a) ∧
    3 * (Finset.univ.filter (fun i : Fin (width Λ n) =>
      ∃ a, slots w.2.2 i = some a ∧ ¬ ‖gradient f (w.1 a)‖ ≤ ε / 2 + 2 * n * α)).card ≤
        width Λ n}

omit [SecondCountableTopology E] in
lemma measurableSet_healthy {f : E → ℝ} (hgm : Measurable (gradient f)) (ε α : ℝ) (Λ n : ℕ) :
    MeasurableSet (healthy f ε α Λ n) := by
  classical
  refine measurableSet_of_slices fun s => ?_
  have hc : Measurable (fun Y : Fin (2 ^ Λ) → E => (Finset.univ.filter (fun i : Fin (width Λ n) =>
      ∃ a, slots s.2 i = some a ∧ ¬ ‖gradient f (Y a)‖ ≤ ε / 2 + 2 * n * α)).card) := by
    simp only [Finset.card_filter]
    refine Finset.measurable_sum _ fun i _ => Measurable.ite ?_ measurable_const measurable_const
    cases h : slots s.2 i with
    | none => simp
    | some a =>
      simp only [Option.some.injEq, exists_eq_left']
      exact (measurableSet_le (hgm.comp (measurable_pi_apply a)).norm measurable_const).compl
  have he : {Y : Fin (2 ^ Λ) → E | (Y, s) ∈ healthy f ε α Λ n} =
      {_Y | ¬ n ≤ Λ + 1} ∪ ({_Y | s.1 = n ∧ ∀ i < width Λ n, ∃ a, slots s.2 i = some a} ∩
        ((fun Y : Fin (2 ^ Λ) → E => (Finset.univ.filter (fun i : Fin (width Λ n) =>
          ∃ a, slots s.2 i = some a ∧ ¬ ‖gradient f (Y a)‖ ≤ ε / 2 + 2 * n * α)).card) ⁻¹'
            {m | 3 * m ≤ width Λ n})) := by
    ext Y
    simp only [healthy, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [he]
  exact (MeasurableSet.const _).union ((MeasurableSet.const _).inter
    (hc (MeasurableSet.of_discrete)))

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma traj_chainStep (g : E → Ω → E) (ε α : ℝ) (Λ k0 r : ℕ) (hk0 : 0 < k0) (x0 : E)
    (Y : Fin (2 ^ Λ) → E) (s : Ladder (2 ^ Λ)) (b : ℕ → Fin (k0 * r * 2 ^ Λ) → Ω) (n : ℕ) :
    traj (chainStep g ε α Λ k0 r hk0 x0) (Y, s) b n =
      (Y, traj (roundMap g ε α Λ k0 r hk0 x0 Y) s b n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [traj, ih]; rfl

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma round_good {g : E → Ω → E} {f : E → ℝ} {ε α : ℝ} {Λ k0 r : ℕ} (hk0 : 0 < k0) (x0 : E)
    {n : ℕ} (hn : n ≤ Λ) (Y : Fin (2 ^ Λ) → E) (e : Fin (2 ^ Λ) → Option (Fin (2 ^ Λ)))
    (hw : (Y, ((n, e) : Ladder (2 ^ Λ))) ∈ healthy f ε α Λ n) (z : Fin (k0 * r * 2 ^ Λ) → Ω)
    (hacc : 6 * (Finset.univ.filter (fun i : Fin (2 ^ (Λ - min n Λ)) =>
      ¬ ‖OracleTemplate.SublevelRobustGradient.aggregate (m := k0 * 2 ^ min n Λ) (b := r)
          (Nat.mul_pos hk0 (Nat.two_pow_pos (min n Λ))) (2 * α)
          (fun l => g (((slots e i).map Y).getD x0)
            (blockOf _ _ (calls_eq Λ k0 r (min n Λ) (min_le_right _ _)) z i l)) -
        gradient f (((slots e i).map Y).getD x0)‖ ≤ α)).card ≤ 2 ^ (Λ - min n Λ)) :
    chainStep g ε α Λ k0 r hk0 x0 (Y, (n, e)) z ∈ healthy f ε α Λ (n + 1) := by
  classical
  obtain ⟨_, hsome, hsolid⟩ := hw (by omega)
  have hmin : min n Λ = n := min_eq_left hn
  have hminr : ((min n Λ : ℕ) : ℝ) = n := by rw [hmin]
  have hthr : (2 * ((min n Λ : ℕ) : ℝ) + 1) * α = (2 * (n : ℝ) + 1) * α := by rw [hminr]
  set pass : Fin (2 ^ (Λ - min n Λ)) → Bool := fun i =>
    testPasses α (threshold ε α (min n Λ)) (Nat.mul_pos hk0 (Nat.two_pow_pos (min n Λ)))
      (slots e i) (fun l => g (((slots e i).map Y).getD x0)
        (blockOf _ _ (calls_eq Λ k0 r (min n Λ) (min_le_right _ _)) z i l)) with hpassdef
  have hstep : chainStep g ε α Λ k0 r hk0 x0 (Y, (n, e)) z = (Y, (n + 1, nextSlots e pass)) := rfl
  rw [hstep]
  have hKK : 2 * width Λ (n + 1) = 2 ^ (Λ - min n Λ) ∨
      (2 ^ (Λ - min n Λ) = 1 ∧ width Λ (n + 1) = 1) := by
    unfold width
    rw [hmin]
    rcases Nat.lt_or_ge n Λ with hlt | hge
    · left
      rw [min_eq_left (by omega : n + 1 ≤ Λ)]
      rw [show Λ - n = (Λ - (n + 1)) + 1 by omega, pow_succ]
      ring
    · right
      have : n = Λ := le_antisymm hn hge
      subst this
      simp
  have hdet := round_deterministic (K := 2 ^ (Λ - min n Λ)) (K' := width Λ (n + 1))
    (slots e) pass
    (fun a => ‖gradient f (Y a)‖ ≤ ε / 2 + 2 * n * α)
    (fun a => ‖gradient f (Y a)‖ ≤ ε / 2 + 2 * ((n + 1 : ℕ) : ℝ) * α)
    (fun i => ‖OracleTemplate.SublevelRobustGradient.aggregate (m := k0 * 2 ^ min n Λ) (b := r)
          (Nat.mul_pos hk0 (Nat.two_pow_pos (min n Λ))) (2 * α)
          (fun l => g (((slots e i).map Y).getD x0)
            (blockOf _ _ (calls_eq Λ k0 r (min n Λ) (min_le_right _ _)) z i l)) -
        gradient f (((slots e i).map Y).getD x0)‖ ≤ α)
    (fun i => hsome i (by unfold width; exact i.isLt))
    (fun i hi => by
      simp only [hpassdef, testPasses, Bool.and_eq_true] at hi
      exact Option.isSome_iff_exists.mp hi.1)
    (fun i a ha hsol hac => by
      simp only [hpassdef, testPasses, ha, Option.isSome_some, Bool.true_and, decide_eq_true_eq,
        Option.map_some, Option.getD_some]
      simp only [ha, Option.map_some, Option.getD_some] at hac
      have htri := norm_le_norm_add_norm_sub' (OracleTemplate.SublevelRobustGradient.aggregate
        (m := k0 * 2 ^ min n Λ) (b := r) (Nat.mul_pos hk0 (Nat.two_pow_pos (min n Λ))) (2 * α)
        (fun l => g (Y a) (blockOf _ _ (calls_eq Λ k0 r (min n Λ) (min_le_right _ _)) z i l)))
        (gradient f (Y a))
      unfold threshold
      linarith)
    (fun i a ha hp hac => by
      simp only [hpassdef, testPasses, ha, Option.isSome_some, Bool.true_and,
        decide_eq_true_eq] at hp
      simp only [ha, Option.map_some, Option.getD_some] at hac hp
      have htri := norm_le_norm_add_norm_sub' (gradient f (Y a))
        (OracleTemplate.SublevelRobustGradient.aggregate
        (m := k0 * 2 ^ min n Λ) (b := r) (Nat.mul_pos hk0 (Nat.two_pow_pos (min n Λ))) (2 * α)
        (fun l => g (Y a) (blockOf _ _ (calls_eq Λ k0 r (min n Λ) (min_le_right _ _)) z i l)))
      rw [norm_sub_rev] at hac
      unfold threshold at hp
      push_cast
      linarith)
    (by unfold width at hsolid; exact hsolid) hacc hKK
  obtain ⟨hall, hbad⟩ := hdet
  intro _
  refine ⟨rfl, fun i hi => ?_, ?_⟩
  · rw [slots_nextSlots e pass i (lt_of_lt_of_le hi (width_le Λ (n + 1)))]
    exact hall i hi
  · have hfil : (Finset.univ.filter (fun i : Fin (width Λ (n + 1)) =>
        ∃ a, slots (nextSlots e pass) i = some a ∧
          ¬ ‖gradient f (Y a)‖ ≤ ε / 2 + 2 * ((n + 1 : ℕ) : ℝ) * α)) =
        Finset.univ.filter (fun j : Fin (width Λ (n + 1)) => ∃ y, passers (slots e) pass j = some y ∧
          ¬ ‖gradient f (Y y)‖ ≤ ε / 2 + 2 * ((n + 1 : ℕ) : ℝ) * α) := by
      refine Finset.filter_congr fun i _ => ?_
      rw [slots_nextSlots e pass i (lt_of_lt_of_le i.isLt (width_le Λ (n + 1)))]
    simp only at hfil ⊢
    rw [hfil]
    exact hbad

section Probability

variable {p : Measure Ω} [IsProbabilityMeasure p]

lemma round_fail {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {f : E → ℝ}
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p) {σ : ℝ}
    (hvar : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p) ≤ σ ^ 2)
    {ε α : ℝ} (hα : 0 < α) {Λ k0 r : ℕ} (hk0 : 0 < k0) (hr : 0 < r)
    (hrα : 144 * σ ^ 2 ≤ r * α ^ 2) (x0 : E) {n : ℕ} (hn : n ≤ Λ)
    (w : (Fin (2 ^ Λ) → E) × Ladder (2 ^ Λ)) (hw : w ∈ healthy f ε α Λ n) :
    (Measure.pi fun _ : Fin (k0 * r * 2 ^ Λ) => p).real
      {z | chainStep g ε α Λ k0 r hk0 x0 w z ∉ healthy f ε α Λ (n + 1)} ≤ roundBound k0 Λ n := by
  classical
  obtain ⟨Y, m, e⟩ := w
  have hm : m = n := (hw (by omega)).1
  subst hm
  have hmin : min m Λ = m := min_eq_left hn
  set k := k0 * 2 ^ min m Λ with hkdef
  have hk : 0 < k := Nat.mul_pos hk0 (Nat.two_pow_pos (min m Λ))
  set K := 2 ^ (Λ - min m Λ) with hKdef
  have hcalls := calls_eq Λ k0 r (min m Λ) (min_le_right _ _)
  let pt : Fin K → E := fun i => ((slots e i).map Y).getD x0
  let A : Fin K → Set (Fin (k * r) → Ω) := fun i =>
    {v | α < ‖OracleTemplate.SublevelRobustGradient.aggregate (m := k) (b := r) hk (2 * α)
      (fun l => g (pt i) (v l)) - gradient f (pt i)‖}
  have hgx (x : E) : Measurable (g x) := hg.comp measurable_prodMk_left
  have hA (i : Fin K) : MeasurableSet (A i) :=
    measurableSet_lt measurable_const (((measurable_aggregate_vec hk (2 * α)).comp
      (Measurable.of_eval fun l => (hgx (pt i)).comp (measurable_pi_apply l))).sub_const
        _).norm
  set θ : ℝ := (1 / 2 : ℝ) ^ k with hθdef
  have hθ : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp (i : Fin K) : (Measure.pi fun _ : Fin (k * r) => p).real (A i) ≤ θ := by
    have h := test_inaccurate (p := p) (hgx (pt i)) (hgi (pt i)) (gradient f (pt i))
      (hvi (pt i)) (hmean (pt i)) (hvar (pt i)) hα hk hr hrα
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  set a := K / 6 + 1 with hadef
  let T : Set (Fin K → Fin (k * r) → Ω) :=
    {ζ | a ≤ (Finset.univ.filter (fun i => ζ i ∈ A i)).card}
  have hT : MeasurableSet T := by
    have hcard : Measurable (fun ζ : Fin K → Fin (k * r) → Ω =>
        (Finset.univ.filter (fun i => ζ i ∈ A i)).card) := by
      simp only [Finset.card_filter]
      exact Finset.measurable_sum _ fun i _ =>
        Measurable.ite ((hA i).preimage (measurable_pi_apply i)) measurable_const measurable_const
    exact hcard (MeasurableSet.of_discrete (s := {c : ℕ | a ≤ c}))
  have hsub : {z | chainStep g ε α Λ k0 r hk0 x0 (Y, (m, e)) z ∉ healthy f ε α Λ (m + 1)} ⊆
      blockOf K (k * r) hcalls ⁻¹' T := by
    intro z hz
    by_contra hc
    apply hz
    refine round_good hk0 x0 hn Y e hw z ?_
    have hfil : (Finset.univ.filter (fun i : Fin K =>
        ¬ ‖OracleTemplate.SublevelRobustGradient.aggregate (m := k) (b := r) hk (2 * α)
          (fun l => g (pt i) (blockOf K (k * r) hcalls z i l)) - gradient f (pt i)‖ ≤ α)) =
        Finset.univ.filter (fun i => blockOf K (k * r) hcalls z i ∈ A i) := by
      refine Finset.filter_congr fun i _ => ?_
      simp only [A, Set.mem_ofPred_eq, not_le]
    simp only [Set.mem_preimage, T, Set.mem_ofPred_eq, not_le] at hc
    change 6 * (Finset.univ.filter (fun i : Fin K =>
        ¬ ‖OracleTemplate.SublevelRobustGradient.aggregate (m := k) (b := r) hk (2 * α)
          (fun l => g (pt i) (blockOf K (k * r) hcalls z i l)) - gradient f (pt i)‖ ≤ α)).card ≤ K
    rw [hfil]
    omega
  have hpres := blockOf_preserving p K (k * r) hcalls
  have hfrac := fraction_failure (P := Measure.pi fun _ : Fin (k * r) => p) hA hθ hθ1 hp a
  calc (Measure.pi fun _ : Fin (k0 * r * 2 ^ Λ) => p).real
        {z | chainStep g ε α Λ k0 r hk0 x0 (Y, (m, e)) z ∉ healthy f ε α Λ (m + 1)} ≤
      (Measure.pi fun _ : Fin (k0 * r * 2 ^ Λ) => p).real (blockOf K (k * r) hcalls ⁻¹' T) :=
        measureReal_mono hsub
    _ = (Measure.pi fun _ : Fin K => Measure.pi fun _ : Fin (k * r) => p).real T := by
        simp only [measureReal_def]
        rw [hpres.measure_preimage hT.nullMeasurableSet]
    _ ≤ (1 + Real.sqrt θ) ^ K * Real.sqrt θ ^ a :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) hfrac
    _ = roundBound k0 Λ m := by
        unfold roundBound
        rw [ite_eq_left hn]
        simp only [hθdef, hkdef, hKdef, hadef, hmin]

lemma phase_two {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) {f : E → ℝ}
    (hgm : Measurable (gradient f))
    (hgi : ∀ x, Integrable (g x) p) (hmean : ∀ x, ∫ ω, g x ω ∂p = gradient f x)
    (hvi : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p) {σ : ℝ}
    (hvar : ∀ x, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p) ≤ σ ^ 2)
    {ε α : ℝ} (hα : 0 < α) {Λ k0 r : ℕ} (hk0 : 0 < k0) (hr : 0 < r)
    (hrα : 144 * σ ^ 2 ≤ r * α ^ 2) (x0 : E) (Y : Fin (2 ^ Λ) → E)
    (hY : 3 * (Finset.univ.filter (fun j : Fin (2 ^ Λ) =>
      ¬ ‖gradient f (Y j)‖ ≤ ε / 2)).card ≤ 2 ^ Λ) :
    (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (k0 * r * 2 ^ Λ) => p).real
      {b | ¬ ‖gradient f ((((traj (roundMap g ε α Λ k0 r hk0 x0 Y) (0, fun j => some j) b
        (Λ + 1)).2 ⟨0, Nat.two_pow_pos Λ⟩).map Y).getD x0)‖ ≤ ε / 2 + 2 * (Λ + 1) * α} ≤
      ∑ n ∈ Finset.range (Λ + 1), roundBound k0 Λ n := by
  classical
  have h0 : (Y, ((0, fun j => some j) : Ladder (2 ^ Λ))) ∈ healthy f ε α Λ 0 := by
    intro _
    refine ⟨rfl, fun i hi => ⟨⟨i, by simpa [width] using hi⟩, by
      simp [slots, show i < 2 ^ Λ by simpa [width] using hi]⟩, ?_⟩
    have hfil : (Finset.univ.filter (fun i : Fin (width Λ 0) =>
        ∃ a, slots (fun j : Fin (2 ^ Λ) => some j) i = some a ∧
          ¬ ‖gradient f (Y a)‖ ≤ ε / 2 + 2 * ((0 : ℕ) : ℝ) * α)).card =
        (Finset.univ.filter (fun j : Fin (2 ^ Λ) => ¬ ‖gradient f (Y j)‖ ≤ ε / 2)).card := by
      have hw : width Λ 0 = 2 ^ Λ := by simp [width]
      refine Finset.card_bij (fun i _ => ⟨i, by rw [← hw]; exact i.isLt⟩) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        obtain ⟨a, ha, hna⟩ := hi
        have hlt : (i : ℕ) < 2 ^ Λ := by rw [← hw]; exact i.isLt
        simp only [slots, dite_eq_left hlt, Option.some.injEq] at ha
        subst ha
        simpa using hna
      · intro i _ j _ hij
        exact Fin.ext (by simpa using congrArg Fin.val hij)
      · intro j hj
        refine ⟨⟨j, by rw [hw]; exact j.isLt⟩, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact ⟨j, by simp [slots], by simpa using hj⟩
    rw [hfil]
    simpa [width] using hY
  have hstep (n : ℕ) (w : (Fin (2 ^ Λ) → E) × Ladder (2 ^ Λ)) (hw : w ∈ healthy f ε α Λ n) :
      (Measure.pi fun _ : Fin (k0 * r * 2 ^ Λ) => p).real
        {z | chainStep g ε α Λ k0 r hk0 x0 w z ∉ healthy f ε α Λ (n + 1)} ≤
          roundBound k0 Λ n := by
    by_cases hn : n ≤ Λ
    · exact round_fail hg hgi hmean hvi hvar hα hk0 hr hrα x0 hn w hw
    · have hemp : {z | chainStep g ε α Λ k0 r hk0 x0 w z ∉ healthy f ε α Λ (n + 1)} = ∅ := by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
        exact fun h => absurd h (by omega)
      rw [hemp]
      simp only [measureReal_empty]
      exact roundBound_nonneg k0 Λ n
  have hchain := chain_health (pw := Measure.pi fun _ : Fin (k0 * r * 2 ^ Λ) => p)
    (measurable_chainStep hg ε α Λ k0 r hk0 x0) _ (healthy f ε α Λ)
    (fun n => measurableSet_healthy hgm ε α Λ n) h0 (roundBound k0 Λ) (roundBound_nonneg k0 Λ)
    hstep (Λ + 1)
  refine (measureReal_mono ?_).trans hchain
  intro b hb
  simp only [Set.mem_ofPred_eq] at hb ⊢
  intro hH
  apply hb
  rw [traj_chainStep] at hH
  obtain ⟨_, hsome, hbad⟩ := hH le_rfl
  have hw1 : width Λ (Λ + 1) = 1 := by simp [width]
  obtain ⟨a, ha⟩ := hsome 0 (by rw [hw1]; norm_num)
  have h0lt : (0 : ℕ) < 2 ^ Λ := Nat.two_pow_pos Λ
  have hslot : (traj (roundMap g ε α Λ k0 r hk0 x0 Y) (0, fun j => some j) b (Λ + 1)).2
      ⟨0, Nat.two_pow_pos Λ⟩ = some a := by
    simpa [slots, h0lt] using ha
  rw [hslot]
  simp only [Option.map_some, Option.getD_some]
  by_contra hna
  have hmem : (⟨0, by rw [hw1]; norm_num⟩ : Fin (width Λ (Λ + 1))) ∈
      Finset.univ.filter (fun i : Fin (width Λ (Λ + 1)) =>
        ∃ a, slots (traj (roundMap g ε α Λ k0 r hk0 x0 Y) (0, fun j => some j) b (Λ + 1)).2 i =
          some a ∧ ¬ ‖gradient f (Y a)‖ ≤ ε / 2 + 2 * ((Λ + 1 : ℕ) : ℝ) * α) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨a, ha, ?_⟩
    push_cast
    exact hna
  have hpos := Finset.card_pos.mpr ⟨_, hmem⟩
  simp only at hbad
  omega

end Probability

end LongTails.Proofs.HighProbabilityPhaseTwo
