import LongTails.Algorithms.TwoSidedConvolutionalPerceptron
import LongTails.Proofs.TwoSidedPerceptronGeometry
import LongTails.Proofs.TwoSidedPerceptronTrace
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSidedPerceptronExecution

open LongTails.Setups.TwoSidedConvolutionalPerceptron
open LongTails.Algorithms.TwoSidedConvolutionalPerceptron
open TwoSidedPerceptronDynamics (State)
open TwoSidedPerceptronTrajectory (Control Regime)
open TwoSidedPerceptronGeometry
open TwoSidedPerceptronTrace

variable {d n : ℕ} {D : Data d n} {g R μ κ η : ℝ} {c : Control}

noncomputable def step (D : Data d n) (η : ℝ) (s : ScanState d n) : ScanState d n :=
  scanUpdate η s (answer D (s.cursor, s.point))

noncomputable def initial (d n : ℕ) : ScanState d n := ⟨identityStart d, 0⟩

structure Ready (G : Geometry D g R μ κ) (c : Control) (η : ℝ) (Q : ℕ)
    (s : ScanState d n) where
  trace : Trace c (coeff G η) (plus G) (minus G)
  point_eq : encode s.point = trace.endpoint
  dirty : Bool
  earlier : dirty = false → ∀ i : Fin (n + 1), i.val < s.cursor.val →
    0 < (answer D (i, s.point)).margin
  accounted : Q + (if dirty then n + 1 else 0) ≤ (n + 1) * trace.length + s.cursor.val

noncomputable def initialReady (G : Geometry D g R μ κ) (c : Control) (η : ℝ)
    (hstart : (c.start : State (Features d)) = ⟨1 / Real.sqrt 2, 0, 1 / Real.sqrt 2, 0⟩) :
    Ready G c η 0 (initial d n) where
  trace := Trace.empty c (coeff G η) (plus G) (minus G)
  point_eq := by rw [Trace.empty_endpoint, hstart]; exact encode_initial
  dirty := false
  earlier _ i hi := by simp [initial] at hi
  accounted := by simp [Trace.empty, initial]

lemma rotate_last {i : Fin (n + 1)} (hi : i.val = n) : finRotate (n + 1) i = 0 := by
  rw [finRotate_apply]
  have hl : i = Fin.last n := Fin.ext (by simp [hi])
  rw [hl, Fin.last_add_one]

lemma rotate_not_last {i : Fin (n + 1)} (hi : i.val ≠ n) : (finRotate (n + 1) i).val = i.val + 1 := by
  rw [finRotate_apply, Fin.val_add_one]
  split_ifs with h
  · exfalso; apply hi; rw [h]; simp
  · rfl

lemma step_cursor (D : Data d n) (η : ℝ) (s : ScanState d n) :
    (step D η s).cursor = finRotate (n + 1) s.cursor := rfl

lemma step_wrong_point {s : ScanState d n} (hm : (answer D (s.cursor, s.point)).margin ≤ 0) :
    (step D η s).point = s.point + η • (answer D (s.cursor, s.point)).direction := by
  simp [step, scanUpdate, hm]

lemma step_correct_point {s : ScanState d n} (hm : 0 < (answer D (s.cursor, s.point)).margin) :
    (step D η s).point = s.point := by
  simp [step, scanUpdate, not_le.mpr hm]

lemma step_good {s : ScanState d n} (hs : Separates D s.point) :
    Separates D (step D η s).point := by
  rw [step_correct_point (hs s.cursor)]
  exact hs

lemma wrong_permitted (G : Geometry D g R μ κ) (hd : 0 < d) (hη : 0 < η)
    (hδ : c.δ = η * μ) {Q : ℕ} {s : ScanState d n} (hs : Ready G c η Q s)
    (hm : (answer D (s.cursor, s.point)).margin ≤ 0) :
    TwoSidedPerceptronDynamics.margin (coeff G η s.cursor) c.δ (plus G s.cursor)
      (minus G s.cursor) hs.trace.endpoint ≤ 0 := by
  have hmul := mul_nonpos_of_nonneg_of_nonpos hη.le hm
  change η * LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d
    (D s.cursor) s.point ≤ 0 at hmul
  rw [margin_encode_scaled hd G s.cursor s.point, hs.point_eq] at hmul
  rw [hδ]
  exact hmul

noncomputable def Ready.wrong (G : Geometry D g R μ κ) (hd : 0 < d) (hη : 0 < η)
    (hδ : c.δ = η * μ) {Q : ℕ} {s : ScanState d n} (hs : Ready G c η Q s)
    (hm : (answer D (s.cursor, s.point)).margin ≤ 0) : Ready G c η (Q + 1) (step D η s) where
  trace := hs.trace.append s.cursor (wrong_permitted G hd hη hδ hs hm)
  point_eq := by
    rw [Trace.append_endpoint, step_wrong_point hm, ← hs.point_eq, hδ]
    exact encode_step hd G η s.cursor s.point
  dirty := if s.cursor.val = n then false else true
  earlier := by
    intro hclean i hi
    by_cases hl : s.cursor.val = n
    · rw [step_cursor, rotate_last hl] at hi
      simp at hi
    · simp [hl] at hclean
  accounted := by
    have ha := hs.accounted
    have hc := s.cursor.isLt
    change Q + 1 + (if (if s.cursor.val = n then false else true) then n + 1 else 0) ≤
      (n + 1) * (hs.trace.length + 1) + (step D η s).cursor.val
    rw [step_cursor, Nat.mul_add, Nat.mul_one]
    by_cases hl : s.cursor.val = n
    · rw [rotate_last hl]
      simp only [hl, ite_true, Bool.false_eq_true, ite_false, Fin.val_zero, Nat.add_zero]
      split_ifs at ha <;> omega
    · rw [rotate_not_last hl]
      simp only [hl, ite_false, ite_true]
      split_ifs at ha <;> omega

noncomputable def Ready.correctNext (G : Geometry D g R μ κ)
    {Q : ℕ} {s : ScanState d n} (hs : Ready G c η Q s)
    (hm : 0 < (answer D (s.cursor, s.point)).margin) (hl : s.cursor.val ≠ n) :
    Ready G c η (Q + 1) (step D η s) where
  trace := hs.trace
  point_eq := by rw [step_correct_point hm]; exact hs.point_eq
  dirty := hs.dirty
  earlier := by
    intro hclean i hi
    rw [step_cursor, rotate_not_last hl] at hi
    rw [step_correct_point hm]
    by_cases he : i.val < s.cursor.val
    · exact hs.earlier hclean i he
    · have hie : i = s.cursor := Fin.ext (by omega)
      subst i
      exact hm
  accounted := by
    rw [step_cursor, rotate_not_last hl]
    have ha := hs.accounted
    omega

noncomputable def Ready.correctLast (G : Geometry D g R μ κ)
    {Q : ℕ} {s : ScanState d n} (hs : Ready G c η Q s)
    (hm : 0 < (answer D (s.cursor, s.point)).margin) (hl : s.cursor.val = n)
    (hdirty : hs.dirty = true) : Ready G c η (Q + 1) (step D η s) where
  trace := hs.trace
  point_eq := by rw [step_correct_point hm]; exact hs.point_eq
  dirty := false
  earlier := by
    intro _ i hi
    rw [step_cursor, rotate_last hl] at hi
    simp at hi
  accounted := by
    rw [step_cursor, rotate_last hl]
    have ha := hs.accounted
    simp only [hdirty, ite_true, hl] at ha
    simp only [Bool.false_eq_true, ite_false, Fin.val_zero, Nat.add_zero]
    omega

lemma Ready.certified (G : Geometry D g R μ κ)
    {Q : ℕ} {s : ScanState d n} (hs : Ready G c η Q s)
    (hm : 0 < (answer D (s.cursor, s.point)).margin) (hl : s.cursor.val = n)
    (hclean : hs.dirty = false) : Separates D (step D η s).point := by
  rw [step_correct_point hm]
  intro i
  by_cases hi : i.val < s.cursor.val
  · exact hs.earlier hclean i hi
  · have hie : i = s.cursor := Fin.ext (by have := i.isLt; omega)
    subst i
    exact hm

lemma iterate_ready_or_good (G : Geometry D g R μ κ) (hd : 0 < d) (hη : 0 < η)
    (hδ : c.δ = η * μ)
    (hstart : (c.start : State (Features d)) = ⟨1 / Real.sqrt 2, 0, 1 / Real.sqrt 2, 0⟩) (Q : ℕ) :
    Separates D ((step D η)^[Q] (initial d n)).point ∨
      Nonempty (Ready G c η Q ((step D η)^[Q] (initial d n))) := by
  induction Q with
  | zero => exact Or.inr ⟨initialReady G c η hstart⟩
  | succ Q ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with hg | hs
    · exact Or.inl (step_good hg)
    · let hs := Classical.choice hs
      by_cases hm : (answer D (((step D η)^[Q] (initial d n)).cursor,
          ((step D η)^[Q] (initial d n)).point)).margin ≤ 0
      · exact Or.inr ⟨hs.wrong G hd hη hδ hm⟩
      · have hp := lt_of_not_ge hm
        by_cases hl : ((step D η)^[Q] (initial d n)).cursor.val = n
        · cases he : hs.dirty with
          | false => exact Or.inl (hs.certified G hp hl he)
          | true => exact Or.inr ⟨hs.correctLast G hp hl he⟩
        · exact Or.inr ⟨hs.correctNext G hp hl⟩

lemma iterate_separates (G : Geometry D g R μ κ) (hd : 0 < d) (hη : 0 < η)
    (hδ : c.δ = η * μ)
    (hstart : (c.start : State (Features d)) = ⟨1 / Real.sqrt 2, 0, 1 / Real.sqrt 2, 0⟩)
    (HG : TwoSidedPerceptronTrajectory.Geometry c (coeff G η) (plus G) (minus G) G.separator)
    {K m : ℕ} (hR : Regime c K) (hm0 : 0 < m)
    (hdecay : (1 - c.clo ^ 2 / 8) ^ m * (2 * c.a₀) ≤ c.threshold (2 * m))
    (hK : 2 * m + c.bound m < K) :
    Separates D ((step D η)^[(n + 1) * K] (initial d n)).point := by
  rcases iterate_ready_or_good G hd hη hδ hstart ((n + 1) * K) with hg | hs
  · exact hg
  · let hs := Classical.choice hs
    have hlen := hs.trace.length_lt HG hR hm0 hdecay hK
    have ha := hs.accounted
    have hc := ((step D η)^[(n + 1) * K] (initial d n)).cursor.isLt
    have hm : (n + 1) * (hs.trace.length + 1) ≤ (n + 1) * K := Nat.mul_le_mul_left (n + 1) hlen
    simp only [Nat.mul_succ] at hm
    split_ifs at ha <;> omega

lemma output_eq_iterate (p : Params) (D : Data p.dimension p.samples)
    (O : OracleTemplate.Oracle (Query p.dimension p.samples) (Reply p.dimension))
    (hlaw : ∀ history query seed, O.answer history query seed = answer D query.2)
    (K : ℕ) (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    output p O K seed ξ = ((step D (stepSize p))^[K] (initial p.dimension p.samples)).point := by
  unfold output
  rw [OracleTemplate.execute_eq_of_answer_eq O (answer D) (fun h q s => hlaw h (0, q) s),
    OracleTemplate.execute_iterate]
  rfl

end LongTails.Proofs.TwoSidedPerceptronExecution
