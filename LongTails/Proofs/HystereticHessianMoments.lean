import LongTails.Proofs.ClippedExtragradientProcess
import LongTails.Proofs.GuardedGradientMoments
import LongTails.Algorithms.HystereticHessianTransport
import LongTails.Proofs.HeavyTailedTapeExecution
import LongTails.Proofs.GuardedGeneralizedGeometry

open MeasureTheory

namespace LongTails.Proofs.HystereticHessianMoments

open OracleTemplate.StochasticGeneralized

lemma adaptive_potential_drift {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] {cost : S → ℕ}
    {next : (n : ℕ) → S → (Fin n → Ω) → S} {V : S → ℝ} {c : ℝ}
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hV : Measurable V) (hV0 : ∀ s, 0 ≤ V s)
    (hi : ∀ s, Integrable (fun b => V (next (cost s) s b))
      (Measure.pi fun _ : Fin (cost s) => p))
    (hb : ∀ s, (∫ b, V (next (cost s) s b)
      ∂Measure.pi (fun _ : Fin (cost s) => p)) ≤ V s + c) (k : ℕ) (s : S) :
    Integrable (fun ξ => V (blockTrace cost next s ξ k).1) (Measure.infinitePi fun _ : ℕ => p) ∧
      (∫ ξ, V (blockTrace cost next s ξ k).1 ∂Measure.infinitePi (fun _ : ℕ => p)) ≤
        V s + (k : ℝ) * c := by
  induction k generalizing s with
  | zero => simp [blockTrace_zero]
  | succ k ih =>
    let m := cost s
    let F : (Fin m → Ω) × (ℕ → Ω) → ℝ := fun z =>
      V (blockTrace cost next (next m s z.1) z.2 k).1
    have hnext : Measurable (fun b : Fin m → Ω => next m s b) :=
      (hn m).comp measurable_prodMk_left
    have hF : Measurable F := hV.comp
      (measurable_fst.comp ((OracleTemplate.ClippedExtragradient.measurable_blockTrace hc hn k).comp
        ((hnext.comp measurable_fst).prodMk measurable_snd)))
    have hprod := WeakGradientConvolution.nonnegative_fiber_integral_bound
      hF.stronglyMeasurable (fun z => hV0 _)
      (Filter.Eventually.of_forall (fun b => (ih (next m s b)).1))
      ((hi s).add (integrable_const ((k : ℝ) * c)))
      (Filter.Eventually.of_forall (fun b => (ih (next m s b)).2))
    have hsplit := splitStream_preserving p m
    have he : (fun ξ => V (blockTrace cost next s ξ (k + 1)).1) = F ∘ splitStream m := by
      funext ξ
      rw [blockTrace_start_succ]
      rfl
    rw [he]
    refine ⟨hsplit.integrable_comp_of_integrable hprod.1, ?_⟩
    simp only [Function.comp_def]
    rw [hsplit.integral_comp' F]
    apply hprod.2.trans
    simp only [Pi.add_apply]
    rw [integral_add (hi s) (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    have hh := hb s
    push_cast
    linarith

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport

lemma coarse_displacement_bound (p : Params) (c : Config) (v : Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hcap : 0 ≤ c.coarseCap) :
    ‖coarseDisplacement p c v‖ ≤ c.coarseCap := by
  have ht : 0 ≤ min c.coarseCap (‖v‖ / (64 * (p.L0 + p.L1 * ‖v‖))) := by positivity
  rw [coarseDisplacement, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact (mul_le_of_le_one_right ht
    (MatrixPolarCharacterization.normalized_norm_le_one v)).trans (min_le_left _ _)

lemma fine_displacement_bound (p : Params) (c : Config) (s : State p c)
    (hstep : 0 ≤ c.fineStep) : ‖fineDisplacement p c s‖ ≤ c.fineStep := by
  rw [fineDisplacement, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hstep]
  exact mul_le_of_le_one_right hstep
    (MatrixPolarCharacterization.normalized_norm_le_one s.estimate)

lemma coarse_proposal_growth (p : Params) (c : Config) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hcap : 0 ≤ c.coarseCap)
    (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    {M : ℝ} (hsmall : p.L1 * c.coarseCap ≤ 1 / 4)
    (hbase : p.L0 * c.coarseCap ≤ M / 4) (x v : Space p) :
    ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M := by
  apply GuardedGeneralizedGeometry.short_gradient_growth hL0 hL1 hg hH x _ _ hsmall hbase
  simpa only [add_sub_cancel_left] using coarse_displacement_bound p c v hL0 hL1 hcap

lemma fine_proposal_growth (p : Params) (c : Config) (g : Space p → Space p)
    (hL0 : 0 ≤ p.L0) (hL1 : 0 ≤ p.L1) (hstep : 0 ≤ c.fineStep)
    (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 + p.L1 * ‖g x‖)
    {M : ℝ} (hsmall : p.L1 * c.fineStep ≤ 1 / 4)
    (hbase : p.L0 * c.fineStep ≤ M / 4) (s : State p c) :
    ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M := by
  apply GuardedGeneralizedGeometry.short_gradient_growth hL0 hL1 hg hH s.point _ _ hsmall hbase
  simpa only [add_sub_cancel_left] using fine_displacement_bound p c s hstep

def MoveValid (p : Params) (c : Config) (s : State p c) : Prop :=
  match s.phase with
  | .transport _ _ => s.move = fineDisplacement p c s
  | _ => True

lemma beginFineStep_move_valid (p : Params) (c : Config) (s : State p c) :
    MoveValid p c (beginFineStep p c s) := by
  unfold beginFineStep
  split_ifs <;> simp [MoveValid, fineDisplacement]

lemma finishPilot_move_valid (p : Params) (c : Config) (s : State p c) (v : Space p) :
    MoveValid p c (finishPilot p c s v) := by
  unfold finishPilot
  split_ifs
  all_goals first
    | exact beginFineStep_move_valid p c s
    | simp [MoveValid]

lemma raw_update_move_valid (p : Params) (c : Config) (s : State p c)
    (hs : MoveValid p c s) (reply : Space p) : MoveValid p c (rawUpdate p c s reply) := by
  cases hactive : s.active with
  | false => simpa [rawUpdate, hactive] using hs
  | true =>
    cases hphase : s.phase with
    | padding => simpa [rawUpdate, hactive, hphase] using hs
    | transport i sum =>
      have hm : s.move = fineDisplacement p c s := by simpa [MoveValid, hphase] using hs
      simp only [rawUpdate, hactive, hphase, ite_true]
      split_ifs <;> simp_all [MoveValid, fineDisplacement]
    | gradient refresh j i sum values =>
      simp only [rawUpdate, hactive, hphase, ite_true]
      split_ifs
      all_goals first
        | exact beginFineStep_move_valid p c _
        | exact finishPilot_move_valid p c s _
        | simp [MoveValid]

lemma update_move_valid (p : Params) (c : Config) (s : State p c)
    (hs : MoveValid p c s) (u : ℝ) (reply : Space p) : MoveValid p c (update p c s u reply) := by
  have hh := raw_update_move_valid p c s hs reply
  unfold update
  split_ifs
  · exact hh
  · trivial

structure AnchoredState (p : Params) (c : Config) where
  value : State p c
  anchor : Space p

noncomputable def nextAnchor (p : Params) (c : Config) (s : AnchoredState p c)
    (reply : Space p) : Space p :=
  if s.value.active then
    match s.value.phase with
    | .gradient false j i sum values =>
        if i < c.pilotBatch then s.anchor
        else if j.val + 1 < c.groups + 1 then s.anchor
        else
          let values := Function.update values j
            (((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ • (sum + reply))
          let v := OracleTemplate.MultiplicativeRobustEstimator.medoid values
          if c.guardThreshold < ‖v‖ then s.anchor else s.value.point
    | _ => s.anchor
  else s.anchor

noncomputable def anchoredUpdate (p : Params) (c : Config) (s : AnchoredState p c)
    (u : ℝ) (reply : Space p) : AnchoredState p c :=
  ⟨update p c s.value u reply, nextAnchor p c s reply⟩

noncomputable def potential (p : Params) (c : Config) (g : Space p → Space p)
    (s : AnchoredState p c) : ℝ :=
  if s.value.active || s.value.success then ‖g s.anchor‖ ^ 2 else 0

def AnchoredValid (p : Params) (c : Config) (s : AnchoredState p c) : Prop :=
  (s.value.success = true → s.value.active = false ∧ s.value.point = s.anchor) ∧
    (s.value.active = true → match s.value.phase with
      | .gradient true _ _ _ _ => s.value.point = s.anchor
      | .transport _ _ => s.value.point = s.anchor
      | _ => True)

lemma initial_anchored_valid (p : Params) (c : Config) :
    AnchoredValid p c ⟨initial p c, p.x0⟩ := by
  simp [AnchoredValid, initial]

lemma output_energy_bound (p : Params) (c : Config) (g : Space p → Space p)
    (s : AnchoredState p c) (hs : AnchoredValid p c s) :
    ‖g (output p c s.value)‖ ^ 2 ≤ potential p c g s + ‖g p.x0‖ ^ 2 := by
  by_cases hsuccess : s.value.success = true
  · rw [output, ite_eq_left hsuccess, (hs.1 hsuccess).2]
    simp only [potential, hsuccess, Bool.or_true, ite_true]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · have hp : 0 ≤ potential p c g s := by unfold potential; split_ifs <;> positivity
    simpa [output, hsuccess] using (le_add_of_nonneg_left hp :
      ‖g p.x0‖ ^ 2 ≤ potential p c g s + ‖g p.x0‖ ^ 2)

lemma beginFineStep_valid (p : Params) (c : Config) (s : State p c) (anchor : Space p)
    (hpoint : s.point = anchor) (hsuccess : s.success = false) :
    AnchoredValid p c ⟨beginFineStep p c s, anchor⟩ := by
  unfold beginFineStep
  split_ifs <;> simp [AnchoredValid, hpoint, hsuccess]

lemma accepted_finishPilot_valid (p : Params) (c : Config) (s : State p c) (v : Space p)
    (hsuccess : s.success = false) (hguard : ‖v‖ ≤ c.guardThreshold) :
    AnchoredValid p c ⟨finishPilot p c s v, s.point⟩ := by
  unfold finishPilot
  rw [ite_eq_right (not_lt.mpr hguard)]
  split_ifs
  all_goals first
    | exact beginFineStep_valid p c s s.point rfl hsuccess
    | simp [AnchoredValid, hsuccess]

lemma beginFineStep_potential (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (anchor : Space p) (hactive : s.active = true) :
    potential p c g ⟨beginFineStep p c s, anchor⟩ = ‖g anchor‖ ^ 2 := by
  unfold beginFineStep
  split_ifs <;> simp [potential, hactive]

lemma finishPilot_potential (p : Params) (c : Config) (g : Space p → Space p)
    (s : State p c) (anchor v : Space p) (hactive : s.active = true) :
    potential p c g ⟨finishPilot p c s v,
      if c.guardThreshold < ‖v‖ then anchor else s.point⟩ =
      if c.guardThreshold < ‖v‖ then 0 else ‖g s.point‖ ^ 2 := by
  unfold finishPilot
  split_ifs
  all_goals first
    | exact beginFineStep_potential p c g s s.point hactive
    | simp [potential, hactive]

lemma fresh_pilot_potential (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (Q : Measure (ℕ → Ω)) [IsProbabilityMeasure Q]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) P Q)
    (g : Space p → Space p) (s : AnchoredState p c) (X : Ω → Space p)
    (hX : Measurable X) (hactive : s.value.active = true)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    {M : ℝ} (hM : 0 < M) (hthreshold : c.guardThreshold = 3 * M / 2)
    (hi : Integrable X P) (hmean : (∫ ω, X ω ∂P) = g s.value.point)
    (hpi : Integrable (fun ω => ‖X ω - g s.value.point‖ ^ p.p) P)
    (hb : (∫ ω, ‖X ω - g s.value.point‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g s.value.point‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.pilotBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (hgrowth : ‖g s.value.point‖ ≤ 2 * max ‖g s.anchor‖ M) :
    let estimate := fun ξ : ℕ → Ω => OracleTemplate.MultiplicativeRobustEstimator.medoid
      (fun j : Fin (c.groups + 1) => ((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ •
        ∑ k ∈ Finset.range (c.pilotBatch + 1), X (ξ (j.val * (c.pilotBatch + 1) + k)))
    let F := fun ξ => potential p c g ⟨finishPilot p c s.value (estimate ξ),
      if c.guardThreshold < ‖estimate ξ‖ then s.anchor else s.value.point⟩
    Integrable F Q ∧ (∫ ξ, F ξ ∂Q) ≤ potential p c g s / 2 + 4 * M ^ 2 := by
  dsimp only
  simp_rw [finishPilot_potential p c g s.value s.anchor _ hactive]
  have hh := GuardedGradientMoments.stream_guard_second_moment Q hIID hX (g s.value.point)
    hp hp2 hσ hα hM hi hmean hpi hb (c.pilotBatch + 1) (by omega) hsize
    c.groups hgroups (norm_nonneg (g s.anchor)) hgrowth
  simpa only [hthreshold, potential, hactive, Bool.true_or, ite_true,
    ← not_le, ite_not] using hh

lemma raw_anchored_valid (p : Params) (c : Config) (s : AnchoredState p c)
    (hs : AnchoredValid p c s) (reply : Space p) :
    AnchoredValid p c ⟨rawUpdate p c s.value reply, nextAnchor p c s reply⟩ := by
  cases hactive : s.value.active with
  | false => simpa [rawUpdate, nextAnchor, hactive] using hs
  | true =>
    have hsuccess : s.value.success = false := by
      cases hx : s.value.success with
      | false => rfl
      | true => have hh := (hs.1 hx).1; simp [hactive] at hh
    cases hphase : s.value.phase with
    | padding => simpa [rawUpdate, nextAnchor, hactive, hphase] using hs
    | transport i sum =>
      have hpoint : s.value.point = s.anchor := by simpa [hphase] using hs.2 hactive
      simp only [rawUpdate, nextAnchor, hactive, hphase, ite_true]
      split_ifs <;> simp [AnchoredValid, hsuccess, hpoint]
    | gradient refresh j i sum values =>
      cases refresh with
      | true =>
        have hpoint : s.value.point = s.anchor := by simpa [hphase] using hs.2 hactive
        simp only [rawUpdate, nextAnchor, hactive, hphase, ite_true]
        split_ifs
        all_goals first
          | exact beginFineStep_valid p c _ s.anchor hpoint hsuccess
          | simp [AnchoredValid, hsuccess, hpoint]
      | false =>
        simp only [rawUpdate, nextAnchor, hactive, hphase,
          Bool.false_eq_true, ite_true, ite_false]
        split_ifs with hi hj hguard
        · simp [AnchoredValid, hsuccess]
        · simp [AnchoredValid, hsuccess]
        · unfold finishPilot
          rw [ite_eq_left hguard]
          simp [AnchoredValid]
        · exact accepted_finishPilot_valid p c s.value _ hsuccess (le_of_not_gt hguard)

lemma anchored_update_valid (p : Params) (c : Config) (s : AnchoredState p c)
    (hs : AnchoredValid p c s) (u : ℝ) (reply : Space p) :
    AnchoredValid p c (anchoredUpdate p c s u reply) := by
  have hh := raw_anchored_valid p c s hs reply
  unfold anchoredUpdate update
  split_ifs
  · exact hh
  · constructor
    · exact hh.1
    · simp

lemma inactive_anchor (p : Params) (c : Config) (s : AnchoredState p c)
    (hactive : s.value.active = false) (u : ℝ) (reply : Space p) :
    (anchoredUpdate p c s u reply).anchor = s.anchor := by
  simp [anchoredUpdate, nextAnchor, hactive]

def ProposalValid (p : Params) (c : Config) (g : Space p → Space p) (M : ℝ)
    (s : AnchoredState p c) : Prop :=
  s.value.active = true → ‖g s.value.point‖ ≤ 2 * max ‖g s.anchor‖ M

lemma self_proposal_bound (p : Params) (g : Space p → Space p) (M : ℝ) (x : Space p) :
    ‖g x‖ ≤ 2 * max ‖g x‖ M := by
  have hh := le_max_left ‖g x‖ M
  nlinarith [norm_nonneg (g x)]

lemma beginFineStep_proposal_valid (p : Params) (c : Config) (g : Space p → Space p)
    (M : ℝ) (s : AnchoredState p c) (hs : ProposalValid p c g M s) :
    ProposalValid p c g M ⟨beginFineStep p c s.value, s.anchor⟩ := by
  unfold beginFineStep
  split_ifs
  · simp [ProposalValid]
  · exact hs

lemma finishPilot_proposal_valid (p : Params) (c : Config) (g : Space p → Space p)
    (M : ℝ) (s : State p c) (anchor v : Space p)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M) :
    ProposalValid p c g M ⟨finishPilot p c s v,
      if c.guardThreshold < ‖v‖ then anchor else s.point⟩ := by
  unfold finishPilot
  split_ifs
  all_goals first
    | exact beginFineStep_proposal_valid p c g M ⟨s, s.point⟩
        (fun _ => self_proposal_bound p g M s.point)
    | exact fun _ => hcoarse s.point v
    | exact fun _ => self_proposal_bound p g M s.point
    | simp [ProposalValid]

lemma raw_proposal_valid (p : Params) (c : Config) (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    (s : AnchoredState p c) (hs : AnchoredValid p c s) (hm : MoveValid p c s.value)
    (hp : ProposalValid p c g M s) (reply : Space p) :
    ProposalValid p c g M ⟨rawUpdate p c s.value reply, nextAnchor p c s reply⟩ := by
  cases hactive : s.value.active with
  | false => simpa [rawUpdate, nextAnchor, hactive] using hp
  | true =>
    cases hphase : s.value.phase with
    | padding => simpa [rawUpdate, nextAnchor, hactive, hphase] using hp
    | transport i sum =>
      have hpoint : s.value.point = s.anchor := by simpa [hphase] using hs.2 hactive
      have hmove : s.value.move = fineDisplacement p c s.value := by
        simpa [MoveValid, hphase] using hm
      have hgrowth : ‖g (s.value.point + s.value.move)‖ ≤ 2 * max ‖g s.anchor‖ M := by
        rw [hmove]
        simpa only [hpoint] using hfine s.value
      simp only [rawUpdate, nextAnchor, hactive, hphase, ite_true]
      split_ifs
      · exact fun _ => hp hactive
      all_goals exact fun _ => hgrowth
    | gradient refresh j i sum values =>
      cases refresh with
      | true =>
        simp only [rawUpdate, nextAnchor, hactive, hphase, ite_true]
        split_ifs
        · exact fun _ => hp hactive
        · exact fun _ => hp hactive
        · unfold beginFineStep
          split_ifs
          · simp [ProposalValid]
          · exact fun _ => hp hactive
      | false =>
        simp only [rawUpdate, nextAnchor, hactive, hphase, Bool.false_eq_true, ite_true, ite_false]
        split_ifs with hi hj hguard
        · exact fun _ => hp hactive
        · exact fun _ => hp hactive
        · simpa only [ite_eq_left hguard] using
            finishPilot_proposal_valid p c g M s.value s.anchor
              (OracleTemplate.MultiplicativeRobustEstimator.medoid
                (Function.update values j (((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ • (sum + reply)))) hcoarse
        · simpa only [ite_eq_right hguard] using
            finishPilot_proposal_valid p c g M s.value s.anchor
              (OracleTemplate.MultiplicativeRobustEstimator.medoid
                (Function.update values j (((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ • (sum + reply)))) hcoarse

lemma anchored_update_proposal_valid (p : Params) (c : Config) (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    (s : AnchoredState p c) (hs : AnchoredValid p c s) (hm : MoveValid p c s.value)
    (hp : ProposalValid p c g M s) (u : ℝ) (reply : Space p) :
    ProposalValid p c g M (anchoredUpdate p c s u reply) := by
  have hh := raw_proposal_valid p c g M hcoarse hfine s hs hm hp reply
  unfold anchoredUpdate update
  split_ifs <;> exact hh

noncomputable def path (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : State p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) : State p c :=
  HeavyTailedProductProcess.trajectory
    (fun s z => update p c s z.1 (answer (query p c s z.1) z.2)) n s ξ

noncomputable def anchoredPath (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : AnchoredState p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) : AnchoredState p c :=
  HeavyTailedProductProcess.trajectory
    (fun s z => anchoredUpdate p c s z.1 (answer (query p c s.value z.1) z.2)) n s ξ

lemma anchoredPath_projection (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : AnchoredState p c) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    (anchoredPath p c answer s ξ n).value = path p c answer s.value ξ n := by
  induction n generalizing s ξ with
  | zero => rfl
  | succ n ih => exact ih _ _

lemma anchoredPath_valid (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (s : AnchoredState p c) (hs : AnchoredValid p c s) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    AnchoredValid p c (anchoredPath p c answer s ξ n) := by
  induction n generalizing s ξ with
  | zero => exact hs
  | succ n ih => exact ih _ (anchored_update_valid p c s hs _ _) _

lemma anchoredPath_proposal_valid (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (g : Space p → Space p) (M : ℝ)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    (s : AnchoredState p c) (hs : AnchoredValid p c s) (hm : MoveValid p c s.value)
    (hp : ProposalValid p c g M s) (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    ProposalValid p c g M (anchoredPath p c answer s ξ n) := by
  induction n generalizing s ξ with
  | zero => exact hp
  | succ n ih =>
    let u := (ξ 0).1
    let reply := answer (query p c s.value u) (ξ 0).2
    exact ih (anchoredUpdate p c s u reply) (anchored_update_valid p c s hs u reply)
      (update_move_valid p c s.value hm u reply)
      (anchored_update_proposal_valid p c g M hcoarse hfine s hs hm hp u reply)
      (fun k => ξ (k + 1))

lemma path_output_energy_bound (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p) (g : Space p → Space p)
    (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    ‖g (output p c (path p c answer (initial p c) ξ n))‖ ^ 2 ≤
      potential p c g (anchoredPath p c answer ⟨initial p c, p.x0⟩ ξ n) + ‖g p.x0‖ ^ 2 := by
  have hv := anchoredPath_valid p c answer ⟨initial p c, p.x0⟩ (initial_anchored_valid p c) ξ n
  have hh := output_energy_bound p c g _ hv
  rwa [anchoredPath_projection] at hh

lemma macroCalls_pos (c : Config) : 0 < macroCalls c := by
  unfold macroCalls pilotCalls resetCalls
  positivity

lemma update_slot (p : Params) (c : Config) (s : State p c)
    (hs : s.slot < macroCalls c) (u : ℝ) (reply : Space p) :
    (update p c s u reply).slot = (s.slot + 1) % macroCalls c := by
  by_cases hnext : s.slot + 1 < macroCalls c
  · simp [update, hnext, Nat.mod_eq_of_lt hnext]
  · have he : s.slot + 1 = macroCalls c := by omega
    simp [update, he]

lemma path_slot (p : Params) (c : Config) {Ω : Type}
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ξ : ℕ → ℝ × Ω) (n : ℕ) :
    (path p c answer (initial p c) ξ n).slot = n % macroCalls c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [path, HeavyTailedProductProcess.trajectory_succ_last]
    have hs : (path p c answer (initial p c) ξ n).slot < macroCalls c := by
      rw [ih]
      exact Nat.mod_lt _ (macroCalls_pos c)
    change (update p c (path p c answer (initial p c) ξ n) (ξ n).1
      (answer (query p c (path p c answer (initial p c) ξ n) (ξ n).1) (ξ n).2)).slot = _
    rw [update_slot p c _ hs, ih]
    simp only [Nat.add_mod, Nat.mod_mod]

lemma execute_eq_path (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω))
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (seed : Unit × (ℕ → ℝ)) (ξ : ℕ → Ω) (n : ℕ) :
    OracleTemplate.execute
      { Seed := fun _ => Ω, law := P, answer := fun _ q ω => answer q.2 ω }
      (trial p c) (fun _ => n) seed ξ =
      output p c (path p c answer (initial p c) (fun k => (seed.2 k, ξ k)) n) :=
  HeavyTailedTapeExecution.execute_fresh_tape _ _ _ _ _ _ _ _ _ _ _

end LongTails.Proofs.HystereticHessianMoments
