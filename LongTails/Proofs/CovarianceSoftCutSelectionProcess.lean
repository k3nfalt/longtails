import LongTails.Proofs.CovarianceSoftCutTournamentMeasurable
import LongTails.Proofs.CovarianceSoftCutMom
import LongTails.Proofs.IIDBlocks
import LongTails.Proofs.StochasticEnvelopeFreshness
import LongTails.Proofs.RecursiveAnchorKmExecution

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutSelectionProcess

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Proofs.CovarianceSoftCutTournamentMeasurable

abbrev SelectionState (q : Params) := ℕ × (ℕ → Space q)

def selectionStep (q : Params) (a : ℝ) (K n m h : ℕ) (leaves : ℕ → Space q)
    (g : Space q → q.Ω → Space q) (s : SelectionState q) (ζ : Fin (n*m) → q.Ω) : SelectionState q :=
  (s.1+1, writeBlock q (n*m) (s.1*(n*m)) s.2
    (fun i => g (selectionProbe q a K n m h leaves s.2 s.1).1 (ζ i)))

lemma writeBlock_at (q : Params) (B start : ℕ) (replies : ℕ → Space q)
    (values : Fin B → Space q) (i : Fin B) :
    writeBlock q B start replies values (start+i.val) = values i := by
  have h : start ≤ start+i.val ∧ start+i.val < start+B := by have hi := i.isLt; omega
  simp [writeBlock, h]

lemma writeBlock_before (q : Params) (B start : ℕ) (replies : ℕ → Space q)
    (values : Fin B → Space q) (i : ℕ) (hi : i < start) :
    writeBlock q B start replies values i = replies i := by
  have h : ¬ (start ≤ i ∧ i < start+B) := by omega
  simp [writeBlock, h]

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_writeBlock (q : Params) (B start : ℕ) :
    Measurable (fun z : (ℕ → Space q) × (Fin B → Space q) => writeBlock q B start z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : start ≤ i ∧ i < start+B
  · simp only [writeBlock, dite_eq_left hi]
    fun_prop
  · simp only [writeBlock, dite_eq_right hi]
    fun_prop

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_writeBlock_start (q : Params) (B : ℕ) :
    Measurable (fun z : ((ℕ → Space q) × (Fin B → Space q)) × ℕ => writeBlock q B z.2 z.1.1 z.1.2) :=
  measurable_from_prod_countable_left (fun start => measurable_writeBlock q B start)

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_selectionProbe_state (q : Params) (a : ℝ) (K n m h : ℕ) :
    Measurable (fun z : (ℕ → Space q) × SelectionState q => selectionProbe q a K n m h z.1 z.2.2 z.2.1) := by
  have hm : Measurable (fun z : ((ℕ → Space q) × (ℕ → Space q)) × ℕ =>
      selectionProbe q a K n m h z.1.1 z.1.2 z.2) :=
    measurable_from_prod_countable_left (fun t => measurable_selectionProbe q a K n m h t)
  have hp : Measurable (fun z : (ℕ → Space q) × SelectionState q => ((z.1, z.2.2), z.2.1)) := by fun_prop
  simpa only [Function.comp_def] using hm.comp hp

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_selectionStep (q : Params) (a : ℝ) (K n m h : ℕ)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : ((ℕ → Space q) × SelectionState q) × (Fin (n*m) → q.Ω) =>
      selectionStep q a K n m h z.1.1 g z.1.2 z.2) := by
  have hprobe : Measurable (fun z : ((ℕ → Space q) × SelectionState q) × (Fin (n*m) → q.Ω) =>
      selectionProbe q a K n m h z.1.1 z.1.2.2 z.1.2.1) :=
    (measurable_selectionProbe_state q a K n m h).comp measurable_fst
  have hvalues : Measurable (fun z : ((ℕ → Space q) × SelectionState q) × (Fin (n*m) → q.Ω) =>
      fun i : Fin (n*m) => g (selectionProbe q a K n m h z.1.1 z.1.2.2 z.1.2.1).1 (z.2 i)) := by
    apply Measurable.of_eval
    intro i
    exact hg.comp ((measurable_fst.comp hprobe).prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hold : Measurable (fun z : ((ℕ → Space q) × SelectionState q) × (Fin (n*m) → q.Ω) => z.1.2.2) := by fun_prop
  have hstart : Measurable (fun z : ((ℕ → Space q) × SelectionState q) × (Fin (n*m) → q.Ω) => z.1.2.1*(n*m)) := by fun_prop
  have hi := (hold.prodMk hvalues).prodMk hstart
  have hw := (measurable_writeBlock_start q (n*m)).comp hi
  have hc : Measurable (fun z : ((ℕ → Space q) × SelectionState q) × (Fin (n*m) → q.Ω) => z.1.2.1+1) := by fun_prop
  simpa only [Function.comp_def, selectionStep] using hc.prodMk hw

def selectionRun (q : Params) (a : ℝ) (K n m h : ℕ) (leaves : ℕ → Space q)
    (g : Space q → q.Ω → Space q) (blocks : ℕ → Fin (n*m) → q.Ω) (t : ℕ) : SelectionState q :=
  OracleTemplate.StochasticGradient.advance (fun k s => selectionStep q a K n m h leaves g s (blocks k))
    t 0 (0, fun _ => 0)

lemma selectionRun_succ (q : Params) (a : ℝ) (K n m h : ℕ) (leaves : ℕ → Space q)
    (g : Space q → q.Ω → Space q) (blocks : ℕ → Fin (n*m) → q.Ω) (t : ℕ) :
    selectionRun q a K n m h leaves g blocks (t+1) =
      selectionStep q a K n m h leaves g (selectionRun q a K n m h leaves g blocks t) (blocks t) := by
  unfold selectionRun
  rw [OracleTemplate.RecursiveAnchorKm.advance_succ, Nat.zero_add]

lemma selectionRun_count (q : Params) (a : ℝ) (K n m h : ℕ) (leaves : ℕ → Space q)
    (g : Space q → q.Ω → Space q) (blocks : ℕ → Fin (n*m) → q.Ω) (t : ℕ) :
    (selectionRun q a K n m h leaves g blocks t).1 = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [selectionRun_succ]; simpa only [selectionStep] using congrArg Nat.succ ih

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_selectionRun (q : Params) (a : ℝ) (K n m h : ℕ)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (t : ℕ) :
    Measurable (fun z : (ℕ → Space q) × (ℕ → Fin (n*m) → q.Ω) =>
      selectionRun q a K n m h z.1 g z.2 t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hi : Measurable (fun z : (ℕ → Space q) × (ℕ → Fin (n*m) → q.Ω) =>
        ((z.1, selectionRun q a K n m h z.1 g z.2 t), z.2 t)) :=
      (measurable_fst.prodMk ih).prodMk ((measurable_pi_apply t).comp measurable_snd)
    simpa only [Function.comp_def, selectionRun_succ] using
      (measurable_selectionStep q a K n m h g hg).comp hi

def selectionReplies (q : Params) (a : ℝ) (K n m h : ℕ) (leaves : ℕ → Space q)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (i : ℕ) : Space q :=
  let t := i/(n*m)
  let s := selectionRun q a K n m h leaves g (fun k j => ξ (k*(n*m)+j.val)) t
  g (selectionProbe q a K n m h leaves s.2 t).1 (ξ i)

lemma selectionReplies_block (q : Params) (a : ℝ) (K n m h : ℕ) (hB : 0 < n*m)
    (leaves : ℕ → Space q) (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω)
    (t : ℕ) (i : Fin (n*m)) :
    selectionReplies q a K n m h leaves g ξ (t*(n*m)+i.val) =
      g (selectionProbe q a K n m h leaves
        (selectionRun q a K n m h leaves g (fun k j => ξ (k*(n*m)+j.val)) t).2 t).1
        (ξ (t*(n*m)+i.val)) := by
  have hd : (t*(n*m)+i.val)/(n*m) = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  simp only [selectionReplies, hd]

lemma selectionRun_prefix (q : Params) (a : ℝ) (K n m h : ℕ) (hB : 0 < n*m)
    (leaves : ℕ → Space q) (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (t : ℕ) :
    ∀ i, i < t*(n*m) →
      (selectionRun q a K n m h leaves g (fun k j => ξ (k*(n*m)+j.val)) t).2 i =
        selectionReplies q a K n m h leaves g ξ i := by
  induction t with
  | zero => intro i hi; omega
  | succ t ih =>
    intro i hi
    rw [selectionRun_succ]
    simp only [selectionStep, selectionRun_count]
    by_cases hpre : i < t*(n*m)
    · rw [writeBlock_before q _ _ _ _ i hpre]
      exact ih i hpre
    · have hj : i-t*(n*m) < n*m := by rw [Nat.succ_mul] at hi; omega
      let j : Fin (n*m) := ⟨i-t*(n*m), hj⟩
      have hindex : t*(n*m)+j.val = i := by dsimp [j]; omega
      rw [← hindex, writeBlock_at]
      exact (selectionReplies_block q a K n m h hB leaves g ξ t j).symm

lemma selectionProbe_run_eq (q : Params) (a : ℝ) (K n m h : ℕ) (hB : 0 < n*m)
    (leaves : ℕ → Space q) (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (t : ℕ) :
    selectionProbe q a K n m h leaves
      (selectionRun q a K n m h leaves g (fun k j => ξ (k*(n*m)+j.val)) t).2 t =
      selectionProbe q a K n m h leaves (selectionReplies q a K n m h leaves g ξ) t := by
  apply LongTails.Proofs.CovarianceSoftCutTournament.selectionProbe_prefix
  exact selectionRun_prefix q a K n m h hB leaves g ξ t

lemma selectionReplies_consistent (q : Params) (a : ℝ) (K n m h : ℕ) (hB : 0 < n*m)
    (leaves : ℕ → Space q) (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (i : ℕ) :
    selectionReplies q a K n m h leaves g ξ i =
      g (selectionProbe q a K n m h leaves (selectionReplies q a K n m h leaves g ξ)
        (i/(n*m))).1 (ξ i) := by
  change g (selectionProbe q a K n m h leaves
    (selectionRun q a K n m h leaves g (fun k j => ξ (k*(n*m)+j.val)) (i/(n*m))).2
    (i/(n*m))).1 (ξ i) = _
  rw [selectionProbe_run_eq q a K n m h hB]

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_selectionReplies (q : Params) (a : ℝ) (K n m h : ℕ)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : (ℕ → Space q) × (ℕ → q.Ω) =>
      selectionReplies q a K n m h z.1 g z.2) := by
  apply Measurable.of_eval
  intro i
  have hb : Measurable (fun z : (ℕ → Space q) × (ℕ → q.Ω) =>
      (z.1, fun k (j : Fin (n*m)) => z.2 (k*(n*m)+j.val))) := by fun_prop
  have hs := (measurable_selectionRun q a K n m h g hg (i/(n*m))).comp hb
  have hp : Measurable (fun z : (ℕ → Space q) × (ℕ → q.Ω) =>
      selectionProbe q a K n m h z.1
        (selectionRun q a K n m h z.1 g (fun k j => z.2 (k*(n*m)+j.val)) (i/(n*m))).2
        (i/(n*m))) := by
    exact (measurable_selectionProbe q a K n m h (i/(n*m))).comp
      (measurable_fst.prodMk (measurable_snd.comp hs))
  exact hg.comp ((measurable_fst.comp hp).prodMk ((measurable_pi_apply i).comp measurable_snd))

def selectionBad (q : Params) (a : ℝ) (K n m h : ℕ) (leaves : ℕ → Space q)
    (v : Space q → Space q) (g : Space q → q.Ω → Space q) :
    Set (SelectionState q × (Fin (n*m) → q.Ω)) :=
  {z | let probe := selectionProbe q a K n m h leaves z.1.2 z.1.1
       a < |directionalMomBlock q n m probe.2 (fun i => g probe.1 (z.2 i)) - ⟪v probe.1, probe.2⟫|}

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurableSet_selectionBad (q : Params) (a : ℝ) (K n m h : ℕ) (leaves : ℕ → Space q)
    (v : Space q → Space q) (hv : Measurable v)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) :
    MeasurableSet (selectionBad q a K n m h leaves v g) := by
  have hp : Measurable (fun z : SelectionState q × (Fin (n*m) → q.Ω) =>
      selectionProbe q a K n m h leaves z.1.2 z.1.1) :=
    (measurable_selectionProbe_state q a K n m h).comp (measurable_const.prodMk measurable_fst)
  have hr : Measurable (fun z : SelectionState q × (Fin (n*m) → q.Ω) =>
      fun i : Fin (n*m) => g (selectionProbe q a K n m h leaves z.1.2 z.1.1).1 (z.2 i)) := by
    apply Measurable.of_eval
    intro i
    exact hg.comp ((measurable_fst.comp hp).prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hpair := (measurable_snd.comp hp).prodMk hr
  have hM := (LongTails.Proofs.CovarianceSoftCutMom.measurable_directionalMomBlock q n m).comp hpair
  have hvp := hv.comp (measurable_fst.comp hp)
  have hi := hvp.inner (𝕜 := ℝ) (measurable_snd.comp hp)
  exact measurableSet_lt measurable_const (continuous_abs.measurable.comp (hM.sub hi))

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma selectionRun_failure_probability (q : Params) (hd : 0 < q.d)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (a : ℝ) (ha : 0 < a) (K n m h : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hbatch : 8*q.σ^2 ≤ (q.d : ℝ)*n*a^2) (leaves : ℕ → Space q) (C : ℕ) :
    MeasurableSet {ξ : ℕ → Fin (n*m) → q.Ω | ∃ t < C,
      (selectionRun q a K n m h leaves g ξ t, ξ t) ∈ selectionBad q a K n m h leaves v g} ∧
    (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (n*m) => p)
      {ξ : ℕ → Fin (n*m) → q.Ω | ∃ t < C,
        (selectionRun q a K n m h leaves g ξ t, ξ t) ∈ selectionBad q a K n m h leaves v g} ≤
      ENNReal.ofReal (C * Real.exp (-(m : ℝ)/8)) := by
  have hv := LongTails.Proofs.CovarianceSoftCutOracle.measurable_mean_of_oracle q p f v g hg
  have hbad := measurableSet_selectionBad q a K n m h leaves v hv g hg.measurable
  have hstep : Measurable (Function.uncurry (selectionStep q a K n m h leaves g)) := by
    have hi : Measurable (fun z : SelectionState q × (Fin (n*m) → q.Ω) => ((leaves, z.1), z.2)) := by fun_prop
    exact (measurable_selectionStep q a K n m h g hg.measurable).comp hi
  have hprob (s : SelectionState q) : (Measure.pi fun _ : Fin (n*m) => p).real
      {ζ | (s, ζ) ∈ selectionBad q a K n m h leaves v g} ≤ Real.exp (-(m : ℝ)/8) := by
    exact LongTails.Proofs.CovarianceSoftCutMom.directionalMom_block_failure q hd p f v g hg
      (selectionProbe q a K n m h leaves s.2 s.1).1
      (selectionProbe q a K n m h leaves s.2 s.1).2
      (LongTails.Proofs.CovarianceSoftCutTournament.selectionProbe_direction_norm q a K n m h leaves s.2 s.1)
      n m hn hm a ha hbatch
  exact LongTails.Proofs.StochasticEnvelopeFreshness.fixed_step_failure_probability
    (Measure.pi fun _ : Fin (n*m) => p) (selectionStep q a K n m h leaves g) hstep
    (selectionBad q a K n m h leaves v g) hbad hprob C (0, fun _ => 0)

lemma selectionGood_iff_no_bad (q : Params) (a : ℝ) (K n m h : ℕ) (hB : 0 < n*m)
    (leaves : ℕ → Space q) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (ξ : ℕ → q.Ω) :
    LongTails.Proofs.CovarianceSoftCutTournament.SelectionGood q a K n m h leaves
      (selectionReplies q a K n m h leaves g ξ) v ↔
    ¬ ∃ t < selectionBlocks K h,
      (selectionRun q a K n m h leaves g (fun k j => ξ (k*(n*m)+j.val)) t,
        fun i : Fin (n*m) => ξ (t*(n*m)+i.val)) ∈ selectionBad q a K n m h leaves v g := by
  have he (t : ℕ) :
      (selectionRun q a K n m h leaves g (fun k j => ξ (k*(n*m)+j.val)) t,
        fun i : Fin (n*m) => ξ (t*(n*m)+i.val)) ∈ selectionBad q a K n m h leaves v g ↔
      a < |directionalMomBlock q n m
        (selectionProbe q a K n m h leaves (selectionReplies q a K n m h leaves g ξ) t).2
        (fun i => selectionReplies q a K n m h leaves g ξ (t*(n*m)+i.val)) -
        ⟪v (selectionProbe q a K n m h leaves (selectionReplies q a K n m h leaves g ξ) t).1,
        (selectionProbe q a K n m h leaves (selectionReplies q a K n m h leaves g ξ) t).2⟫| := by
    simp only [selectionBad, Set.mem_ofPred_eq, selectionRun_count]
    rw [selectionProbe_run_eq q a K n m h hB]
    have hr : (fun i : Fin (n*m) => selectionReplies q a K n m h leaves g ξ (t*(n*m)+i.val)) =
        (fun i => g (selectionProbe q a K n m h leaves (selectionReplies q a K n m h leaves g ξ) t).1
          (ξ (t*(n*m)+i.val))) := by
      funext i
      rw [selectionReplies_block q a K n m h hB, selectionProbe_run_eq q a K n m h hB]
    rw [hr]
  simp only [he, LongTails.Proofs.CovarianceSoftCutTournament.SelectionGood, not_exists,
    not_and, not_lt]

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma selection_failure_probability (q : Params) (hd : 0 < q.d)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → q.Ω)) [IsProbabilityMeasure P]
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k ξ => ξ k) p P)
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsCovarianceSubgradient q p f v g) (a : ℝ) (ha : 0 < a)
    (K n m h : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hbatch : 8*q.σ^2 ≤ (q.d : ℝ)*n*a^2) (leaves : ℕ → Space q) :
    MeasurableSet {ξ | ¬ LongTails.Proofs.CovarianceSoftCutTournament.SelectionGood q a K n m h
      leaves (selectionReplies q a K n m h leaves g ξ) v} ∧
    P {ξ | ¬ LongTails.Proofs.CovarianceSoftCutTournament.SelectionGood q a K n m h
      leaves (selectionReplies q a K n m h leaves g ξ) v} ≤
      ENNReal.ofReal (selectionBlocks K h * Real.exp (-(m : ℝ)/8)) := by
  have hb := selectionRun_failure_probability q hd p f v g hg a ha K n m h hn hm hbatch
    leaves (selectionBlocks K h)
  have hlaw := OracleTemplate.FiniteVariance.infinite_block_law p P hs.independent hs.marginal (n*m)
  have he : {ξ | ¬ LongTails.Proofs.CovarianceSoftCutTournament.SelectionGood q a K n m h
      leaves (selectionReplies q a K n m h leaves g ξ) v} =
      (fun ξ : ℕ → q.Ω => fun k (j : Fin (n*m)) => ξ (k*(n*m)+j.val)) ⁻¹'
      {ξ : ℕ → Fin (n*m) → q.Ω | ∃ t < selectionBlocks K h,
        (selectionRun q a K n m h leaves g ξ t, ξ t) ∈ selectionBad q a K n m h leaves v g} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage,
      selectionGood_iff_no_bad q a K n m h (Nat.mul_pos hn hm), not_not]
  rw [he]
  exact ⟨hb.1.preimage hlaw.measurable,
    (hlaw.measure_preimage hb.1.nullMeasurableSet).le.trans hb.2⟩

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurableSet_selectionGood (q : Params) (a : ℝ) (K n m h : ℕ)
    (v : Space q → Space q) (hv : Measurable v) :
    MeasurableSet {z : (ℕ → Space q) × (ℕ → Space q) |
      LongTails.Proofs.CovarianceSoftCutTournament.SelectionGood q a K n m h z.1 z.2 v} := by
  simp only [LongTails.Proofs.CovarianceSoftCutTournament.SelectionGood, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro t
  apply MeasurableSet.iInter
  intro ht
  have hp := measurable_selectionProbe q a K n m h t
  have hr : Measurable (fun z : (ℕ → Space q) × (ℕ → Space q) =>
      fun i : Fin (n*m) => z.2 (t*(n*m)+i.val)) := by fun_prop
  have hpair := (measurable_snd.comp hp).prodMk hr
  have hM := (LongTails.Proofs.CovarianceSoftCutMom.measurable_directionalMomBlock q n m).comp hpair
  have hi := (hv.comp (measurable_fst.comp hp)).inner (𝕜 := ℝ) (measurable_snd.comp hp)
  exact measurableSet_le (continuous_abs.measurable.comp (hM.sub hi)) measurable_const

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurableSet_selection_failure_joint (q : Params) (a : ℝ) (K n m h : ℕ)
    (v : Space q → Space q) (hv : Measurable v)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) :
    MeasurableSet {z : (ℕ → Space q) × (ℕ → q.Ω) |
      ¬ LongTails.Proofs.CovarianceSoftCutTournament.SelectionGood q a K n m h z.1
        (selectionReplies q a K n m h z.1 g z.2) v} := by
  exact ((measurableSet_selectionGood q a K n m h v hv).preimage
    (measurable_fst.prodMk (measurable_selectionReplies q a K n m h g hg))).compl

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_selectedOutput (q : Params) (a : ℝ) (K n m h : ℕ)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun z : (ℕ → Space q) × (ℕ → q.Ω) =>
      selectionOutput q a K n m h z.1 (selectionReplies q a K n m h z.1 g z.2)) := by
  exact (measurable_selectionOutput q a K n m h).comp
    (measurable_fst.prodMk (measurable_selectionReplies q a K n m h g hg))

end LongTails.Proofs.CovarianceSoftCutSelectionProcess

