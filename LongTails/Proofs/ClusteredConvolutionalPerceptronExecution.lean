import LongTails.Algorithms.ClusteredConvolutionalPerceptron
import LongTails.Proofs.ClusteredConvolutionalPerceptronGeometry
import LongTails.Proofs.ClusteredConvolutionalPerceptronTrace
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ClusteredConvolutionalPerceptronExecution

open LongTails.Setups.ClusteredConvolutionalPerceptron
open LongTails.Algorithms.ClusteredConvolutionalPerceptron
open ClusteredConvolutionalPerceptronDynamics (Control)
open ClusteredConvolutionalPerceptronGeometry
open ClusteredConvolutionalPerceptronTrace
open ManySampleConvolutionalPerceptronGeometry (decode)

variable {d n : ℕ} {D : Data d n} {g R μ κ η : ℝ} {c : Control}

noncomputable def step (D : Data d n) (η : ℝ) (s : ScanState d n) : ScanState d n :=
  scanUpdate η s (answer D (s.cursor, s.point))

noncomputable def initial (c : Control) (ε : ℝ) : ScanState d n :=
  ⟨decode ε ⟨c.C, 0, 1, 0⟩, 0⟩

structure Ready (G : Geometry D g R μ κ) (c : Control) (η : ℝ) (Q : ℕ)
    (s : ScanState d n) where
  trace : Trace c (fun i => η * G.background i) (plusResidual G) (minusResidual G)
  point_eq : s.point = decode (η * μ) trace.endpoint
  centered : ⟪axis d, trace.endpoint.z⟫ = 0
  dirty : Bool
  earlier : dirty = false → ∀ i : Fin (n + 1), i.val < s.cursor.val →
    0 < (answer D (i, s.point)).margin
  accounted : Q + (if dirty then n + 1 else 0) ≤ (n + 1) * trace.length + s.cursor.val

noncomputable def initialReady (G : Geometry D g R μ κ) (c : Control) (η : ℝ) :
    Ready G c η 0 (initial c (η * μ)) where
  trace := Trace.empty c (fun i => η * G.background i) (plusResidual G) (minusResidual G)
  point_eq := rfl
  centered := by simp [Trace.endpoint, Trace.empty]
  dirty := false
  earlier _ i hi := by simp [initial] at hi
  accounted := by simp [Trace.empty, initial]

lemma advance_last {i : Fin (n + 1)} (hi : i.val = n) : advance i = 0 := by
  apply Fin.ext
  simp [advance, hi]

lemma advance_not_last {i : Fin (n + 1)} (hi : i.val ≠ n) : (advance i).val = i.val + 1 := by
  have hn := i.isLt
  exact Nat.mod_eq_of_lt (by omega)

lemma step_cursor (D : Data d n) (η : ℝ) (s : ScanState d n) :
    (step D η s).cursor = advance s.cursor := rfl

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
    (hδ : c.δ = (η * μ) ^ 2) {Q : ℕ} {s : ScanState d n} (hs : Ready G c η Q s)
    (hm : (answer D (s.cursor, s.point)).margin ≤ 0) :
    (η * G.background s.cursor) * hs.trace.endpoint.a * hs.trace.endpoint.q +
      c.δ * (hs.trace.endpoint.a * ⟪plusResidual G s.cursor, hs.trace.endpoint.z⟫ +
        hs.trace.endpoint.t * ⟪minusResidual G s.cursor, hs.trace.endpoint.z⟫) ≤ 0 := by
  have hmul := mul_nonpos_of_nonneg_of_nonpos hη.le hm
  change η * LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv d
    (D s.cursor) s.point ≤ 0 at hmul
  rw [hs.point_eq, sample_margin G s.cursor hd hs.centered, ← hδ] at hmul
  exact hmul

lemma wrong_point (G : Geometry D g R μ κ) (hd : 0 < d) (hδ : c.δ = (η * μ) ^ 2)
    {Q : ℕ} {s : ScanState d n} (hs : Ready G c η Q s)
    (hm : (answer D (s.cursor, s.point)).margin ≤ 0) :
    (step D η s).point = decode (η * μ)
      (ClusteredConvolutionalPerceptronDynamics.step (η * G.background s.cursor) c.δ
        (plusResidual G s.cursor) (minusResidual G s.cursor) hs.trace.endpoint) := by
  rw [step_wrong_point hm, hs.point_eq, hδ, decode_step G s.cursor hd hs.centered]
  rfl

noncomputable def Ready.wrong (G : Geometry D g R μ κ) (hd : 0 < d) (hη : 0 < η)
    (hδ : c.δ = (η * μ) ^ 2) {Q : ℕ} {s : ScanState d n} (hs : Ready G c η Q s)
    (hm : (answer D (s.cursor, s.point)).margin ≤ 0) : Ready G c η (Q + 1) (step D η s) where
  trace := hs.trace.append s.cursor (wrong_permitted G hd hη hδ hs hm)
  point_eq := by
    rw [Trace.append_endpoint]
    exact wrong_point G hd hδ hs hm
  centered := by
    rw [Trace.append_endpoint, hδ]
    exact next_centered G hs.centered s.cursor
  dirty := if s.cursor.val = n then false else true
  earlier := by
    intro hclean i hi
    by_cases hl : s.cursor.val = n
    · rw [step_cursor, advance_last hl] at hi
      simp at hi
    · simp [hl] at hclean
  accounted := by
    have ha := hs.accounted
    have hc := s.cursor.isLt
    change Q + 1 + (if (if s.cursor.val = n then false else true) then n + 1 else 0) ≤
      (n + 1) * (hs.trace.length + 1) + (step D η s).cursor.val
    rw [step_cursor, Nat.mul_add, Nat.mul_one]
    by_cases hl : s.cursor.val = n
    · rw [advance_last hl]
      simp only [hl, ite_true, Bool.false_eq_true, ite_false, Fin.val_zero, Nat.add_zero]
      split_ifs at ha <;> omega
    · rw [advance_not_last hl]
      simp only [hl, ite_false, ite_true]
      split_ifs at ha <;> omega

noncomputable def Ready.correctNext (G : Geometry D g R μ κ)
    {Q : ℕ} {s : ScanState d n} (hs : Ready G c η Q s)
    (hm : 0 < (answer D (s.cursor, s.point)).margin) (hl : s.cursor.val ≠ n) :
    Ready G c η (Q + 1) (step D η s) where
  trace := hs.trace
  point_eq := by rw [step_correct_point hm]; exact hs.point_eq
  centered := hs.centered
  dirty := hs.dirty
  earlier := by
    intro hclean i hi
    rw [step_cursor, advance_not_last hl] at hi
    rw [step_correct_point hm]
    by_cases he : i.val < s.cursor.val
    · exact hs.earlier hclean i he
    · have hie : i = s.cursor := Fin.ext (by omega)
      subst i
      exact hm
  accounted := by
    rw [step_cursor, advance_not_last hl]
    have ha := hs.accounted
    omega

noncomputable def Ready.correctLast (G : Geometry D g R μ κ)
    {Q : ℕ} {s : ScanState d n} (hs : Ready G c η Q s)
    (hm : 0 < (answer D (s.cursor, s.point)).margin) (hl : s.cursor.val = n)
    (hdirty : hs.dirty = true) : Ready G c η (Q + 1) (step D η s) where
  trace := hs.trace
  point_eq := by rw [step_correct_point hm]; exact hs.point_eq
  centered := hs.centered
  dirty := false
  earlier := by
    intro _ i hi
    rw [step_cursor, advance_last hl] at hi
    simp at hi
  accounted := by
    rw [step_cursor, advance_last hl]
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
    (hδ : c.δ = (η * μ) ^ 2) (Q : ℕ) :
    Separates D ((step D η)^[Q] (initial c (η * μ))).point ∨
      Nonempty (Ready G c η Q ((step D η)^[Q] (initial c (η * μ)))) := by
  induction Q with
  | zero => exact Or.inr ⟨initialReady G c η⟩
  | succ Q ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with hg | hs
    · exact Or.inl (step_good hg)
    · let hs := Classical.choice hs
      by_cases hm : (answer D (((step D η)^[Q] (initial c (η * μ))).cursor,
          ((step D η)^[Q] (initial c (η * μ))).point)).margin ≤ 0
      · exact Or.inr ⟨hs.wrong G hd hη hδ hm⟩
      · have hp := lt_of_not_ge hm
        by_cases hl : ((step D η)^[Q] (initial c (η * μ))).cursor.val = n
        · cases he : hs.dirty with
          | false => exact Or.inl (hs.certified G hp hl he)
          | true => exact Or.inr ⟨hs.correctLast G hp hl he⟩
        · exact Or.inr ⟨hs.correctNext G hp hl⟩

lemma iterate_separates (G : Geometry D g R μ κ) (hd : 0 < d) (hη : 0 < η)
    (hδ : c.δ = (η * μ) ^ 2)
    (HG : ClusteredConvolutionalPerceptronDynamics.Geometry c
      (fun i => η * G.background i) (plusResidual G) (minusResidual G))
    (hδ1 : c.δ ≤ 1) (hinit : 8 * c.C ^ 2 ≤ c.h)
    (hnoise : (12 * (c.C + c.e) / c.ρ ^ 2) ^ 2 * c.L ≤ c.h) :
    Separates D ((step D η)^[(n + 1) * (⌈8 / c.ρ ^ 2 * Real.log (1 / c.δ)⌉₊ + 3)]
      (initial c (η * μ))).point := by
  rcases iterate_ready_or_good G hd hη hδ
      ((n + 1) * (⌈8 / c.ρ ^ 2 * Real.log (1 / c.δ)⌉₊ + 3)) with hg | hs
  · exact hg
  · let hs := Classical.choice hs
    have hlen := hs.trace.length_bound HG hδ1 hinit hnoise
    have hm := Nat.mul_le_mul_left (n + 1) hlen
    have ha := hs.accounted
    have hc := ((step D η)^[(n + 1) * (⌈8 / c.ρ ^ 2 * Real.log (1 / c.δ)⌉₊ + 3)]
      (initial c (η * μ))).cursor.isLt
    simp only [Nat.mul_succ] at ha hm
    split_ifs at ha <;> omega

end LongTails.Proofs.ClusteredConvolutionalPerceptronExecution
