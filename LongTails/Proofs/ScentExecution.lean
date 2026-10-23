import LongTails.Proofs.ScentSystem
import LongTails.Proofs.SgdExecution


set_option backward.isDefEq.respectTransparency false

namespace OracleTemplate.Scent

open MeasureTheory Real
open LongTails.Setups.CompositionalEntropicRisk
open scoped BigOperators

variable {q : Params} (I : Instance q) (projection : q.E → q.E) (η α : ℝ)

noncomputable def subStep (w : q.E) (st : (Fin q.n → ℝ) × q.E) (ω : Seed q) :
    (Fin q.n → ℝ) × q.E :=
  (newDual I α w st.1 ω, st.2 + piece I α w st.1 ω)

noncomputable def subSteps (w : q.E) (ν : Fin q.n → ℝ) (ξ : ℕ → Seed q) (k0 : ℕ) :
    ℕ → (Fin q.n → ℝ) × q.E
  | 0 => (ν, 0)
  | b + 1 => subStep I α w (subSteps w ν ξ k0 b) (ξ (k0 + b))

noncomputable def iter (ξ : ℕ → Seed q) : ℕ → q.E × (Fin q.n → ℝ)
  | 0 => (q.w0, fun _ => q.c1)
  | t + 1 =>
      let p := iter ξ t
      let st := subSteps I α p.1 p.2 ξ (t * (q.B + 1)) q.B
      (projection (p.1 - (η / q.B) • st.2), st.1)

noncomputable def average (ξ : ℕ → Seed q) (T : ℕ) : q.E :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, (iter I projection η α ξ t).1

section Congr

lemma subSteps_congr (w : q.E) (ν : Fin q.n → ℝ) {ξ ξ' : ℕ → Seed q} (k0 : ℕ) :
    ∀ b, (∀ i, i < k0 + b → ξ i = ξ' i) →
      subSteps I α w ν ξ k0 b = subSteps I α w ν ξ' k0 b := by
  intro b
  induction b with
  | zero => intro _; rfl
  | succ b ih =>
    intro hξ
    simp only [subSteps]
    rw [ih (fun i hi => hξ i (by omega)), hξ (k0 + b) (by omega)]

lemma iter_congr {ξ ξ' : ℕ → Seed q} :
    ∀ t, (∀ i, i < t * (q.B + 1) → ξ i = ξ' i) →
      iter I projection η α ξ t = iter I projection η α ξ' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro hξ
    simp only [iter]
    rw [ih (fun i hi => hξ i (by nlinarith))]
    rw [subSteps_congr I α _ _ (t * (q.B + 1)) q.B (fun i hi => hξ i (by nlinarith))]

end Congr

section Measurability

variable {projection : q.E → q.E} {wstar : q.E} (h : SysHyp I projection wstar)

omit h in
lemma meas_eval_fin {X : Type*} [MeasurableSpace X] :
    Measurable (fun p : (Fin q.n → X) × Fin q.n => p.1 p.2) :=
  measurable_from_prod_countable_left (fun i => measurable_pi_apply i)

include h in
lemma meas_score_triple :
    Measurable (fun p : Fin q.n × (q.E × q.Ξ) => I.score p.1 p.2.1 p.2.2) :=
  measurable_from_prod_countable_right (fun i => (h.anchor i).meas_s)

include h in
lemma meas_grad_triple :
    Measurable (fun p : Fin q.n × (q.E × q.Ξ) => I.grad p.1 p.2.1 p.2.2) :=
  measurable_from_prod_countable_right (fun i => (h.anchor i).meas_g)

omit h in
lemma meas_idx (k : ℕ) : Measurable (fun ξ : ℕ → Seed q => (ξ k).1) :=
  measurable_fst.comp (measurable_pi_apply k)

omit h in
lemma meas_dualSample (k : ℕ) : Measurable (fun ξ : ℕ → Seed q => (ξ k).2.1 (ξ k).1) :=
  meas_eval_fin.comp ((measurable_fst.comp (measurable_snd.comp (measurable_pi_apply k))).prodMk
    (meas_idx k))

omit h in
lemma meas_primalSample (k : ℕ) : Measurable (fun ξ : ℕ → Seed q => (ξ k).2.2 (ξ k).1) :=
  meas_eval_fin.comp ((measurable_snd.comp (measurable_snd.comp (measurable_pi_apply k))).prodMk
    (meas_idx k))

include h in
lemma measurable_newDual {w : (ℕ → Seed q) → q.E} {ν : (ℕ → Seed q) → Fin q.n → ℝ}
    (hw : Measurable w) (hν : Measurable ν) (k : ℕ) :
    Measurable (fun ξ : ℕ → Seed q => newDual I α (w ξ) (ν ξ) (ξ k)) := by
  unfold newDual
  rw [measurable_pi_iff]
  intro j
  simp only [Function.update_apply]
  have hs : Measurable (fun ξ : ℕ → Seed q => I.score (ξ k).1 (w ξ) ((ξ k).2.1 (ξ k).1)) :=
    (meas_score_triple I h).comp ((meas_idx k).prodMk (hw.prodMk (meas_dualSample k)))
  have hνk : Measurable (fun ξ : ℕ → Seed q => ν ξ (ξ k).1) :=
    meas_eval_fin.comp (hν.prodMk (meas_idx k))
  have hspmd : Measurable (fun ξ : ℕ → Seed q => spmd α (ν ξ (ξ k).1) (I.score (ξ k).1 (w ξ)
      ((ξ k).2.1 (ξ k).1))) := by
    unfold spmd
    exact ((hνk.add (measurable_log.comp (measurable_const.add (measurable_const.mul
      (measurable_exp.comp hs))))).sub (measurable_log.comp (measurable_const.add
      (measurable_const.mul (measurable_exp.comp hνk)))))
  exact Measurable.ite (measurableSet_eq_fun measurable_const (meas_idx k)) hspmd
    ((measurable_pi_apply j).comp hν)

include h in
lemma measurable_piece {w : (ℕ → Seed q) → q.E} {ν : (ℕ → Seed q) → Fin q.n → ℝ}
    (hw : Measurable w) (hν : Measurable ν) (k : ℕ) :
    Measurable (fun ξ : ℕ → Seed q => piece I α (w ξ) (ν ξ) (ξ k)) := by
  unfold piece
  have hs : Measurable (fun ξ : ℕ → Seed q => I.score (ξ k).1 (w ξ) ((ξ k).2.1 (ξ k).1)) :=
    (meas_score_triple I h).comp ((meas_idx k).prodMk (hw.prodMk (meas_dualSample k)))
  have hs' : Measurable (fun ξ : ℕ → Seed q => I.score (ξ k).1 (w ξ) ((ξ k).2.2 (ξ k).1)) :=
    (meas_score_triple I h).comp ((meas_idx k).prodMk (hw.prodMk (meas_primalSample k)))
  have hg' : Measurable (fun ξ : ℕ → Seed q => I.grad (ξ k).1 (w ξ) ((ξ k).2.2 (ξ k).1)) :=
    (meas_grad_triple I h).comp ((meas_idx k).prodMk (hw.prodMk (meas_primalSample k)))
  have hνk : Measurable (fun ξ : ℕ → Seed q => ν ξ (ξ k).1) :=
    meas_eval_fin.comp (hν.prodMk (meas_idx k))
  have hspmd : Measurable (fun ξ : ℕ → Seed q => spmd α (ν ξ (ξ k).1) (I.score (ξ k).1 (w ξ)
      ((ξ k).2.1 (ξ k).1))) := by
    unfold spmd
    exact ((hνk.add (measurable_log.comp (measurable_const.add (measurable_const.mul
      (measurable_exp.comp hs))))).sub (measurable_log.comp (measurable_const.add
      (measurable_const.mul (measurable_exp.comp hνk)))))
  exact (measurable_exp.comp (hs'.sub hspmd)).smul hg'

include h in
lemma measurable_subSteps {w : (ℕ → Seed q) → q.E} {ν : (ℕ → Seed q) → Fin q.n → ℝ}
    (hw : Measurable w) (hν : Measurable ν) (k0 : ℕ) :
    ∀ b, Measurable (fun ξ : ℕ → Seed q => (subSteps I α (w ξ) (ν ξ) ξ k0 b).1) ∧
      Measurable (fun ξ : ℕ → Seed q => (subSteps I α (w ξ) (ν ξ) ξ k0 b).2) := by
  intro b
  induction b with
  | zero => exact ⟨hν, measurable_const⟩
  | succ b ih =>
    simp only [subSteps, subStep]
    exact ⟨measurable_newDual I α h hw ih.1 (k0 + b), ih.2.add (measurable_piece I α h hw ih.1 (k0 + b))⟩

include h in
lemma measurable_iter : ∀ t, Measurable (fun ξ : ℕ → Seed q => (iter I projection η α ξ t).1) ∧
    Measurable (fun ξ : ℕ → Seed q => (iter I projection η α ξ t).2) := by
  intro t
  induction t with
  | zero => exact ⟨measurable_const, measurable_const⟩
  | succ t ih =>
    simp only [iter]
    obtain ⟨h1, h2⟩ := measurable_subSteps I α h ih.1 ih.2 (t * (q.B + 1)) q.B
    exact ⟨h.proj_meas.comp (ih.1.sub (h2.const_smul _)), h1⟩

include h in
lemma measurable_average (T : ℕ) : Measurable (fun ξ : ℕ → Seed q => average I projection η α ξ T) := by
  unfold average
  exact (Finset.measurable_sum _ fun t _ => (measurable_iter I η α h t).1).const_smul _

end Measurability

section Execute

lemma advance_add {S : Type*} (step : ℕ → S → S) (K J call : ℕ) (s : S) :
    StochasticGradient.advance step (K + J) call s =
      StochasticGradient.advance step J (call + K) (StochasticGradient.advance step K call s) := by
  induction K generalizing call s with
  | zero => simp [StochasticGradient.advance]
  | succ K ih =>
    simp only [Nat.succ_add, StochasticGradient.advance]
    convert ih (call + 1) (step call s) using 1; congr 1; omega

lemma advance_succ_last {S : Type*} (step : ℕ → S → S) (K call : ℕ) (s : S) :
    StochasticGradient.advance step (K + 1) call s =
      step (call + K) (StochasticGradient.advance step K call s) := by
  rw [advance_add]; rfl

noncomputable def midState (ξ : ℕ → Seed q) (t j : ℕ) (w : q.E) (ν : Fin q.n → ℝ) (sum p : q.E) :
    State q :=
  ⟨t, j, w, (subSteps I α w ν ξ (t * (q.B + 1)) j).1, (subSteps I α w ν ξ (t * (q.B + 1)) j).2, sum,
    decide (j = q.B), if j = q.B then w - (η / q.B) • (subSteps I α w ν ξ (t * (q.B + 1)) j).2 else p⟩

lemma advance_subSteps (P : ProbabilityMeasure (ℕ → Seed q)) (ξ : ℕ → Seed q) (T : ℕ)
    (hB : 0 < q.B) (t : ℕ) (w : q.E) (ν : Fin q.n → ℝ) (sum p : q.E) :
    ∀ j, j ≤ q.B → StochasticGradient.advance
      (fun k state => (scent q η α T).update state
        ((sampleOracle I projection P).answer [] ((scent q η α T).query state) (ξ k)))
      j (t * (q.B + 1)) ⟨t, 0, w, ν, 0, sum, false, p⟩ =
      midState I η α ξ t j w ν sum p := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : (0 : ℕ) ≠ q.B := by omega
    simp [StochasticGradient.advance, midState, subSteps, h0]
  | succ j ih =>
    intro hj
    have hjB : j < q.B := by omega
    have hjne : ¬ (j = q.B) := by omega
    erw [advance_succ_last, ih (by omega)]
    simp only [midState, hjne, decide_false, Bool.false_eq_true, ↓reduceIte, scent, sampleOracle,
      sampleUpdate, subSteps, subStep, newDual, piece, Function.update_self]
    by_cases hB1 : j + 1 = q.B
    · simp [hB1]
    · simp [hB1]

lemma advance_iter (P : ProbabilityMeasure (ℕ → Seed q)) (ξ : ℕ → Seed q) (T : ℕ)
    (hB : 0 < q.B) :
    ∀ T', StochasticGradient.advance
      (fun k state => (scent q η α T).update state
        ((sampleOracle I projection P).answer [] ((scent q η α T).query state) (ξ k)))
      (T' * (q.B + 1)) 0 ⟨0, 0, q.w0, fun _ => q.c1, 0, 0, false, q.w0⟩ =
      ⟨T', 0, (iter I projection η α ξ T').1, (iter I projection η α ξ T').2, 0,
        ∑ t ∈ Finset.range T', (iter I projection η α ξ t).1, false,
        (iter I projection η α ξ T').1⟩ := by
  intro T'
  induction T' with
  | zero =>
    simp [StochasticGradient.advance, iter]
  | succ T' ih =>
    rw [show (T' + 1) * (q.B + 1) = T' * (q.B + 1) + (q.B + 1) by ring]
    erw [advance_add, ih, Nat.zero_add, advance_succ_last,
      advance_subSteps I projection η α P ξ T hB T' _ _ _ _ q.B le_rfl]
    simp only [midState, decide_true, ↓reduceIte, scent, sampleOracle, projectionUpdate,
      Finset.sum_range_succ, iter]

lemma execute_scent (P : ProbabilityMeasure (ℕ → Seed q)) (ξ : ℕ → Seed q) (T : ℕ)
    (hB : 0 < q.B) (hT : 0 < T) (seed : (scent q η α T).Seed) :
    execute (sampleOracle I projection P) (scent q η α T) (fun _ => T * (q.B + 1)) seed ξ =
      average I projection η α ξ T := by
  rw [StochasticGradient.execute_advance_of_answer _ _ _ _ _
    (fun k query => (sampleOracle I projection P).answer [] query (ξ k)) (fun _ _ => rfl)]
  erw [advance_iter I projection η α P ξ T hB T]
  simp only [scent, average, hT.ne']
  rfl

end Execute

end OracleTemplate.Scent
