import LongTails.Proofs.LogFreeParameters
import LongTails.Proofs.LogFreeEscape

namespace LongTails.Proofs.LogFreeTransition

open OracleTemplate LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LogFreeProxNewton
open LongTails.Proofs.LogFreeGeometry LongTails.Proofs.LogFreeTail
open scoped RealInnerProductSpace

variable (p : Params) (f : p.E → ℝ)

noncomputable def replies (q : Fin 2 × p.E) : Reply p.E :=
  if q.1 = 0 then .inl (f q.2, gradient f q.2) else .inr (fderiv ℝ (gradient f) q.2)

noncomputable def exact (x : p.E) : Data p.E := ⟨x, f x, gradient f x, fderiv ℝ (gradient f) x⟩

noncomputable def transition (st : State p.E) : State p.E := QueryPlan.eval (replies p f) (step p st)

noncomputable def values (st : State p.E) (H : p.E →L[ℝ] p.E) : Fin 5 → ℝ × p.E :=
  fun i => (f (candidates p st H i), gradient f (candidates p st H i))

lemma reply_value (x : p.E) : readValue (replies p f (0, x)) = (f x, gradient f x) := by
  simp [replies, readValue]

lemma reply_hessian (x : p.E) :
    readHessian (replies p f (1, x)) = fderiv ℝ (gradient f) x := by
  simp [replies, readHessian]

lemma transition_eq (st : State p.E) :
    transition p f st = next p st (f (probe p st), gradient f (probe p st))
      (fderiv ℝ (gradient f) (probe p st)) (values p f st (fderiv ℝ (gradient f) (probe p st)))
      (fderiv ℝ (gradient f) (landing p st (fderiv ℝ (gradient f) (probe p st))
        (values p f st (fderiv ℝ (gradient f) (probe p st))))) := by
  simp only [transition, step, QueryPlan.eval, reply_value, reply_hessian]
  have hv : (![(f (candidates p st (fderiv ℝ (gradient f) (probe p st)) 0),
        gradient f (candidates p st (fderiv ℝ (gradient f) (probe p st)) 0)),
      (f (candidates p st (fderiv ℝ (gradient f) (probe p st)) 1),
        gradient f (candidates p st (fderiv ℝ (gradient f) (probe p st)) 1)),
      (f (candidates p st (fderiv ℝ (gradient f) (probe p st)) 2),
        gradient f (candidates p st (fderiv ℝ (gradient f) (probe p st)) 2)),
      (f (candidates p st (fderiv ℝ (gradient f) (probe p st)) 3),
        gradient f (candidates p st (fderiv ℝ (gradient f) (probe p st)) 3)),
      (f (candidates p st (fderiv ℝ (gradient f) (probe p st)) 4),
        gradient f (candidates p st (fderiv ℝ (gradient f) (probe p st)) 4))] :
      Fin 5 → ℝ × p.E) = values p f st (fderiv ℝ (gradient f) (probe p st)) := by
    funext i
    fin_cases i <;> rfl
  rw [hv]

lemma pick_le_left (k : Fin 5 → ℝ) (a b : Fin 5) : k (pick k a b) ≤ k a := by
  unfold pick; split_ifs with h
  · exact le_rfl
  · exact (lt_of_not_ge h).le

lemma pick_le_right (k : Fin 5 → ℝ) (a b : Fin 5) : k (pick k a b) ≤ k b := by
  unfold pick; split_ifs with h
  · exact h
  · exact le_rfl

lemma choose_le (st : State p.E) (H : p.E →L[ℝ] p.E) (vals : Fin 5 → ℝ × p.E) (i : Fin 5) :
    key p st H (candidates p st H (choose p st H vals)) (vals (choose p st H vals)).1 ≤
      key p st H (candidates p st H i) (vals i).1 := by
  set k := fun i => key p st H (candidates p st H i) (vals i).1 with hk
  change k (choose p st H vals) ≤ k i
  have h4 := pick_le_right k (pick k (pick k (pick k 0 1) 2) 3) 4
  have h3 := pick_le_left k (pick k (pick k (pick k 0 1) 2) 3) 4
  have h3' := pick_le_right k (pick k (pick k 0 1) 2) 3
  have h2 := pick_le_left k (pick k (pick k 0 1) 2) 3
  have h2' := pick_le_right k (pick k 0 1) 2
  have h1 := pick_le_left k (pick k 0 1) 2
  have h1' := pick_le_right k 0 1
  have h0 := pick_le_left k 0 1
  change k (pick k (pick k (pick k (pick k 0 1) 2) 3) 4) ≤ k i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith

end LongTails.Proofs.LogFreeTransition
