import LongTails.Proofs.ManySampleConvolutionalPerceptronGeometry
import LongTails.Proofs.ManySampleConvolutionalPerceptronTrace
import LongTails.Proofs.ManySampleConvolutionalPerceptronCounting
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronExecution

open LongTails.Setups.ManySampleConvolutionalPerceptron
open LongTails.Algorithms.ManySampleConvolutionalPerceptron
open ManySampleConvolutionalPerceptronDynamics
open ManySampleConvolutionalPerceptronTrajectory
open ManySampleConvolutionalPerceptronGeometry
open ManySampleConvolutionalPerceptronTrace

variable {d n : ℕ} {D : Data d n} {g R μ κ η σ : ℝ}

noncomputable def step (D : Data d n) (η σ : ℝ) (s : ScanState d n) : ScanState d n :=
  scanUpdate η σ s (answer D (s.cursor, s.point))

def cursorEvent : Fin (n + 1) → Option (Fin n) := Fin.cases none some

structure Ready (G : Geometry D g R μ κ) (η σ : ℝ) (Q : ℕ) (s : ScanState d n) where
  trace : Trace (gains G η σ)
  point_eq : s.point = decode (η * μ) trace.endpoint
  centered : ⟪axis d, trace.endpoint.z⟫ = 0
  earlier : ∀ i : Fin (n + 1), i.val < s.cursor.val → 0 < (answer D (i, s.point)).margin
  accounted : Q ≤ n * trace.negatives + trace.length + s.cursor.val

noncomputable def initialReady (G : Geometry D g R μ κ) (η σ : ℝ) :
    Ready G η σ 0 ⟨((Real.sqrt 2, 0), 0), 0⟩ where
  trace := Trace.empty (gains G η σ)
  point_eq := (decode_initial (η * μ)).symm
  centered := by simp [Trace.endpoint, Trace.empty]
  earlier i hi := by simp at hi
  accounted := Nat.zero_le _

lemma wrong_permitted (G : Geometry D g R μ κ) (hd : 0 < d) (hg : 0 < g) (hη : 0 < η)
    {Q : ℕ} {s : ScanState d n} (hs : Ready G η σ Q s)
    (hm : (answer D (s.cursor, s.point)).margin ≤ 0) :
    Permitted (gains G η σ) (cursorEvent s.cursor) hs.trace.endpoint := by
  have hscale : 0 < G.referenceScale := hg.trans_le G.reference_lower
  cases hc : s.cursor using Fin.cases with
  | zero =>
    simp only [cursorEvent, Fin.cases_zero, Permitted]
    have hmargin : (answer D (s.cursor, s.point)).margin =
        G.referenceScale * hs.trace.endpoint.a * hs.trace.endpoint.q := by
      rw [hc, hs.point_eq]
      exact reference_margin G hd hs.centered
    rw [hmargin] at hm
    exact nonpos_of_mul_nonpos_right
      (show G.referenceScale * (hs.trace.endpoint.a * hs.trace.endpoint.q) ≤ 0 by nlinarith) hscale
  | succ i =>
    have hfirst := hs.earlier 0 (by rw [hc]; simp)
    have hmargin : (answer D (0, s.point)).margin =
        G.referenceScale * hs.trace.endpoint.a * hs.trace.endpoint.q := by
      rw [hs.point_eq]
      exact reference_margin G hd hs.centered
    rw [hmargin] at hfirst
    have haq : 0 < hs.trace.endpoint.a * hs.trace.endpoint.q := by
      apply (mul_pos_iff_of_pos_left hscale).mp
      nlinarith
    simp only [cursorEvent, Fin.cases_succ, Permitted]
    refine ⟨haq, ?_⟩
    have hraw : 0 ≤ LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d (D.samples i) s.point := by
      change LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d (signedSample D s.cursor) s.point ≤ 0 at hm
      rw [hc, signedSample, Fin.cases_succ, margin_neg] at hm
      linarith
    have hmul := mul_nonneg hη.le hraw
    rw [hs.point_eq, sample_margin G i hd hs.centered] at hmul
    exact hmul

lemma wrong_point (G : Geometry D g R μ κ) (hd : 0 < d)
    {Q : ℕ} {s : ScanState d n} (hs : Ready G η σ Q s)
    (hm : (answer D (s.cursor, s.point)).margin ≤ 0) :
    (step D η σ s).point = decode (η * μ) (next (gains G η σ) (cursorEvent s.cursor) hs.trace.endpoint) := by
  simp only [step, scanUpdate, ite_eq_left hm]
  rw [hs.point_eq]
  cases hc : s.cursor using Fin.cases with
  | zero =>
    simp only [cursorEvent, Fin.cases_zero, next, gains, answer, signedSample,
      ite_true]
    exact (decode_positive G hd hs.centered).symm
  | succ i =>
    simp only [cursorEvent, Fin.cases_succ, next, gains, answer, signedSample,
      Fin.succ_ne_zero, ite_false, add_zero, direction_neg, smul_neg, ← sub_eq_add_neg]
    exact (decode_negative G i hd hs.centered).symm

lemma step_good (D : Data d n) (η σ : ℝ) {s : ScanState d n} (hs : Separates D s.point) :
    Separates D (step D η σ s).point := by
  have hm : ¬(answer D (s.cursor, s.point)).margin ≤ 0 := not_le.mpr (hs s.cursor)
  simp only [step, scanUpdate, ite_eq_right hm]
  split_ifs <;> exact hs

noncomputable def Ready.wrong (G : Geometry D g R μ κ) (hd : 0 < d) (hg : 0 < g) (hη : 0 < η)
    {Q : ℕ} {s : ScanState d n} (hs : Ready G η σ Q s)
    (hm : (answer D (s.cursor, s.point)).margin ≤ 0) : Ready G η σ (Q + 1) (step D η σ s) where
  trace := hs.trace.append (cursorEvent s.cursor) (wrong_permitted G hd hg hη hs hm)
  point_eq := by
    rw [Trace.append_endpoint]
    exact wrong_point G hd hs hm
  centered := by
    rw [Trace.append_endpoint]
    exact next_centered G hs.centered _
  earlier i hi := by
    simp only [step, scanUpdate, ite_eq_left hm, Fin.val_zero] at hi
    omega
  accounted := by
    change Q + 1 ≤ n * (hs.trace.append (cursorEvent s.cursor)
      (wrong_permitted G hd hg hη hs hm)).negatives + (hs.trace.length + 1) + (step D η σ s).cursor.val
    rw [Trace.append_negatives]
    simp only [step, scanUpdate, ite_eq_left hm, Fin.val_zero, Nat.add_zero]
    have ha := hs.accounted
    have hi := s.cursor.isLt
    cases hc : s.cursor using Fin.cases with
    | zero =>
      simp only [cursorEvent, Fin.cases_zero, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero]
      rw [hc] at ha
      simp only [Fin.val_zero, Nat.add_zero] at ha
      omega
    | succ i =>
      simp only [cursorEvent, Fin.cases_succ, Option.isSome_some, ite_true, Nat.mul_add, Nat.mul_one]
      omega

noncomputable def Ready.correct (G : Geometry D g R μ κ) {Q : ℕ} {s : ScanState d n}
    (hs : Ready G η σ Q s) (hm : ¬(answer D (s.cursor, s.point)).margin ≤ 0)
    (hend : s.cursor.val ≠ n) : Ready G η σ (Q + 1) (step D η σ s) where
  trace := hs.trace
  point_eq := by simpa [step, scanUpdate, hm, hend] using hs.point_eq
  centered := hs.centered
  earlier i hi := by
    have hpoint : (step D η σ s).point = s.point := by simp [step, scanUpdate, hm, hend]
    rw [hpoint]
    simp only [step, scanUpdate, ite_eq_right hm, dite_eq_right hend] at hi
    by_cases hold : i.val < s.cursor.val
    · exact hs.earlier i hold
    · have heq : i = s.cursor := Fin.ext (by omega)
      subst i
      exact lt_of_not_ge hm
  accounted := by
    have ha := hs.accounted
    simp only [step, scanUpdate, ite_eq_right hm, dite_eq_right hend]
    omega

lemma Ready.completed (G : Geometry D g R μ κ) {Q : ℕ} {s : ScanState d n}
    (hs : Ready G η σ Q s) (hm : ¬(answer D (s.cursor, s.point)).margin ≤ 0)
    (hend : s.cursor.val = n) : Separates D (step D η σ s).point := by
  have hpoint : (step D η σ s).point = s.point := by simp [step, scanUpdate, hm, hend]
  rw [hpoint]
  intro i
  change 0 < (answer D (i, s.point)).margin
  by_cases hi : i.val < s.cursor.val
  · exact hs.earlier i hi
  · have heq : i = s.cursor := Fin.ext (by have := i.isLt; omega)
    subst i
    exact lt_of_not_ge hm

lemma ready_or_separates (G : Geometry D g R μ κ) (hd : 0 < d) (hg : 0 < g) (hη : 0 < η) :
    ∀ Q, Nonempty (Ready G η σ Q ((step D η σ)^[Q] ⟨((Real.sqrt 2, 0), 0), 0⟩)) ∨
      Separates D (((step D η σ)^[Q] ⟨((Real.sqrt 2, 0), 0), 0⟩).point) := by
  intro Q
  induction Q with
  | zero => exact Or.inl ⟨initialReady G η σ⟩
  | succ Q ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with hready | hgood
    · obtain ⟨hs⟩ := hready
      by_cases hm : (answer D
        (((step D η σ)^[Q] ⟨((Real.sqrt 2, 0), 0), 0⟩).cursor,
         ((step D η σ)^[Q] ⟨((Real.sqrt 2, 0), 0), 0⟩).point)).margin ≤ 0
      · exact Or.inl ⟨hs.wrong G hd hg hη hm⟩
      · by_cases hend : ((step D η σ)^[Q] ⟨((Real.sqrt 2, 0), 0), 0⟩).cursor.val = n
        · exact Or.inr (hs.completed G hm hend)
        · exact Or.inl ⟨hs.correct G hm hend⟩
    · exact Or.inr (step_good D η σ hgood)

open ManySampleConvolutionalPerceptronParameters
open ManySampleConvolutionalPerceptronTermination
open ManySampleConvolutionalPerceptronCounting

lemma Ready.call_bound (G : Geometry D g R μ κ) (p : Tuning)
    (hδ : (gains G η σ).contrast = p.δ) (hσ : (gains G η σ).kick = p.δ ^ 2)
    (hp : ∀ i, ‖(gains G η σ).plus i‖ ≤ 1)
    (hr : ∀ i, ‖(gains G η σ).minus i‖ ≤ 1)
    (hmargin : ∀ i, p.κ ≤ -⟪(gains G η σ).minus i, G.separator⟫)
    (hc : ∀ j, p.ρ ≤ coefficient (gains G η σ) j)
    (hc1 : ∀ j, coefficient (gains G η σ) j ≤ 1 / 2)
    {Q : ℕ} {s : ScanState d n} (hs : Ready G η σ Q s) :
    Q < (p.negatives + 1) * (n + 1 + p.referenceLength) := by
  have hm := negative_count_bound p hδ hσ hp hr G.separator_unit hmargin hc hc1
    hs.trace.initial hs.trace.length hs.trace.step hs.trace.permitted
  have hl := event_length_bound p hδ hσ hp hr G.separator_unit hmargin hc hc1
    hs.trace.initial hs.trace.step hs.trace.permitted
  have ha := hs.accounted
  change Q ≤ n * negativeCount hs.trace.events hs.trace.length + hs.trace.length + s.cursor.val at ha
  have hi := s.cursor.isLt
  have hmul := Nat.mul_le_mul_left (n + 1 + p.referenceLength) (Nat.succ_le_iff.mpr hm)
  nlinarith

lemma iterate_separates (G : Geometry D g R μ κ) (p : Tuning)
    (hd : 0 < d) (hg : 0 < g) (hη : 0 < η)
    (hδ : (gains G η σ).contrast = p.δ) (hσ : (gains G η σ).kick = p.δ ^ 2)
    (hp : ∀ i, ‖(gains G η σ).plus i‖ ≤ 1)
    (hr : ∀ i, ‖(gains G η σ).minus i‖ ≤ 1)
    (hmargin : ∀ i, p.κ ≤ -⟪(gains G η σ).minus i, G.separator⟫)
    (hc : ∀ j, p.ρ ≤ coefficient (gains G η σ) j)
    (hc1 : ∀ j, coefficient (gains G η σ) j ≤ 1 / 2)
    {Q : ℕ} (hQ : (p.negatives + 1) * (n + 1 + p.referenceLength) ≤ Q) :
    Separates D (((step D η σ)^[Q] ⟨((Real.sqrt 2, 0), 0), 0⟩).point) := by
  rcases ready_or_separates G hd hg hη Q with hready | hgood
  · obtain ⟨hs⟩ := hready
    exact False.elim ((not_lt_of_ge hQ) (hs.call_bound G p hδ hσ hp hr hmargin hc hc1))
  · exact hgood

lemma output_eq_iterate (p : Params) (D : Data p.dimension p.samples)
    (O : OracleTemplate.Oracle (Query p.dimension p.samples) (Reply p.dimension))
    (hlaw : ∀ history query seed, O.answer history query seed = answer D query.2)
    (K : ℕ) (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    output p O K seed ξ =
      (((step D (1 / (4 * p.upper)) ((p.contrast / (4 * p.upper)) ^ 4))^[K]
        ⟨((Real.sqrt 2, 0), 0), 0⟩).point) := by
  unfold output
  rw [OracleTemplate.execute_eq_of_answer_eq O (answer D) (fun h q s => hlaw h (0, q) s),
    OracleTemplate.execute_iterate]
  rfl

end LongTails.Proofs.ManySampleConvolutionalPerceptronExecution
