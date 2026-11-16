import LongTails.Algorithms.AsgoFixedRadiusOutput
import Mathlib.Tactic

open MeasureTheory OracleTemplate OracleTemplate.Muon
open private OracleTemplate._run from LongTails.Template

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius
open LongTails.Algorithms.AsgoFixedRadiusOutput

lemma execute_correspondence (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (O : Oracle (Mat p.m p.n) (Mat p.m p.n))
    (decode : (j : ℕ) → O.Seed j → I.Sample)
    (hM : 1 ≤ p.M) (hO : Core.OracleExact p I O decode)
    (T : ℕ) (seed : (Core.method p).Seed) (ω : (j : ℕ) → O.Seed j) :
    execute O (Core.method p) (fun _ => p.M * T) seed ω =
      output p I.g (fun j => decode j (ω j)) T := by
  open Matrix MeasureTheory in
  open scoped BigOperators in
  (
    classical
    cases seed
    let samples : ℕ → I.Sample := fun j => decode j (ω j)
    let state : ℕ → Core.MethodState p := Nat.rec
      ⟨0,0,p.W0,0,0,0⟩ (fun j st => Core.methodStep p st (I.g st.point (samples j)))
    have hstate (j : ℕ) : state (j+1)=Core.methodStep p (state j) (I.g (state j).point (samples j)) := rfl
    let answer := fun (history : List ((Fin 1 × Mat p.m p.n) × Mat p.m p.n))
      (query : Fin 1 × Mat p.m p.n) => O.answer history query (ω history.length)
    have hunfold (D : ℕ) (history : List ((Fin 1 × Mat p.m p.n) × Mat p.m p.n))
        (remaining : Fin 1 → ℕ) (st : (Core.method p).State) :
        OracleTemplate._run answer (Core.method p) (D+1) history remaining st =
          if remaining ((Core.method p).query st).1=0 then ((Core.method p).output st,history) else
            OracleTemplate._run answer (Core.method p) D
              (history++[((Core.method p).query st,answer history ((Core.method p).query st))])
              (Function.update remaining ((Core.method p).query st).1
                (remaining ((Core.method p).query st).1-1))
              ((Core.method p).update st (answer history ((Core.method p).query st))) := rfl
    have hrun (D q : ℕ) (history : List ((Fin 1 × Mat p.m p.n) × Mat p.m p.n))
        (hlen : history.length=q) :
        (OracleTemplate._run answer (Core.method p) D history (fun _ => D) (state q)).1=
          (Core.method p).output (state (q+D)) := by
      induction D generalizing q history with
      | zero => rfl
      | succ D ih =>
        erw [hunfold,ite_eq_right (Nat.succ_ne_zero D)]
        have hrem : Function.update (fun _ : Fin 1 => D+1)
            ((Core.method p).query (state q)).1 (D+1-1)=(fun _ => D) := by
          funext i
          have hi : i=((Core.method p).query (state q)).1 := Subsingleton.elim _ _
          subst i
          simp
        rw [hrem]
        have hreply : answer history ((Core.method p).query (state q))=
            I.g (state q).point (samples q) := by
          dsimp only [answer]
          rw [hO]
          change I.g (state q).point (decode history.length (ω history.length))=_
          rw [hlen]
        rw [hreply]
        change (OracleTemplate._run answer (Core.method p) D
          (history++[((Core.method p).query (state q),I.g (state q).point (samples q))])
          (fun _ => D) (Core.methodStep p (state q) (I.g (state q).point (samples q)))).1=_
        rw [← hstate]
        rw [ih (q+1) _ (by simp only [List.length_append,List.length_singleton,hlen])]
        exact congrArg (fun j => (Core.method p).output (state j))
          (show q+1+D=q+(D+1) by omega)
    let C (t j : ℕ) : Core.MethodState p :=
      ⟨t,j,Core.point p I.g samples t,Core.accumulator p I.g samples t,
        ∑ a ∈ Finset.range j, I.g (Core.point p I.g samples t) (samples (t*p.M+a)),
        ∑ a ∈ Finset.range t, Core.point p I.g samples a⟩
    have hmid (t j : ℕ) (hj : j+1<p.M) :
        Core.methodStep p (C t j) (I.g (Core.point p I.g samples t) (samples (t*p.M+j)))=C t (j+1) := by
      delta Core.methodStep
      dsimp only [C]
      rw [ite_eq_left hj]
      simp only [Finset.sum_range_succ]
    have hfinish (t j : ℕ) (hj : j+1=p.M) :
        Core.methodStep p (C t j) (I.g (Core.point p I.g samples t) (samples (t*p.M+j)))=C (t+1) 0 := by
      have hbatch : (∑ a ∈ Finset.range j, I.g (Core.point p I.g samples t) (samples (t*p.M+a)))+
          I.g (Core.point p I.g samples t) (samples (t*p.M+j))=
            ∑ a ∈ Finset.range p.M, I.g (Core.point p I.g samples t) (samples (t*p.M+a)) := by
        rw [← Finset.sum_range_succ,hj]
      have hpoint : Core.point p I.g samples (t+1)=Core.point p I.g samples t-p.R•
          ofMatrix ((Core.matrixRoot (Core.accumulator p I.g samples t+
            Core.gram (Core.batchGradient p I.g samples t (Core.point p I.g samples t)))+p.k•1)⁻¹*
              toMatrix (Core.batchGradient p I.g samples t (Core.point p I.g samples t))) := rfl
      have hacc : Core.accumulator p I.g samples (t+1)=Core.accumulator p I.g samples t+
          Core.gram (Core.batchGradient p I.g samples t (Core.point p I.g samples t)) := rfl
      delta Core.methodStep
      dsimp only [C]
      rw [ite_eq_right (by omega),hbatch,hpoint,hacc,Finset.sum_range_succ]
      rfl
    have hcomplete (t : ℕ) : state (t*p.M)=C t 0 := by
      induction t with
      | zero => rw [Nat.zero_mul]; rfl
      | succ t ih =>
        have hpartial : ∀ j<p.M, state (t*p.M+j)=C t j := by
          intro j hj
          induction j with
          | zero => simpa only [Nat.add_zero] using ih
          | succ j ihj =>
            rw [Nat.add_succ,hstate,ihj (by omega)]
            exact hmid t j hj
        let j := p.M-1
        have hj : j+1=p.M := by dsimp only [j]; omega
        have hjlt : j<p.M := by omega
        have hindex : (t+1)*p.M=t*p.M+j+1 := by rw [Nat.succ_mul]; omega
        rw [hindex,hstate,hpartial j hjlt]
        exact hfinish t j hj
    have hsum : (∑ _i : Fin 1, p.M*T)=p.M*T := by simp
    change (OracleTemplate._run answer (Core.method p) (∑ _i : Fin 1, p.M*T) [] (fun _ => p.M*T)
      (state 0)).1=output p I.g samples T
    rw [hsum,hrun (p.M*T) 0 [] rfl,Nat.zero_add,Nat.mul_comm p.M T,hcomplete]
    change (if T=0 then p.W0 else (1/(T : ℝ))•∑ t ∈ Finset.range T, Core.point p I.g samples t)=
      (if T=0 then p.W0 else (1/(T : ℝ))•∑ t ∈ Finset.range T, Core.point p I.g samples t)
    rfl
  )

lemma trace_cost (p : LongTails.Setups.AsgoFixedRadius.Public) (O : Oracle (Mat p.m p.n) (Mat p.m p.n))
    (T : ℕ) (seed : (Core.method p).Seed) (ω : (j : ℕ) → O.Seed j) (i : Fin 1) :
    ((executeWithTrace O (Core.method p) (fun _ => p.M * T) seed ω).2.countP
      (fun e => e.1.1 == i)) = p.M * T := by
  open Matrix in
  open scoped BigOperators in
  (
    classical
    let A := Core.method p
    let answer := fun (history : List ((Fin 1 × Mat p.m p.n) × Mat p.m p.n))
      (query : Fin 1 × Mat p.m p.n) => O.answer history query (ω history.length)
    have hstep (k : ℕ) (history : List ((Fin 1 × Mat p.m p.n) × Mat p.m p.n))
        (remaining : Fin 1 → ℕ) (st : A.State) :
        OracleTemplate._run answer A (k + 1) history remaining st =
          if remaining (A.query st).1 = 0 then (A.output st, history) else
            OracleTemplate._run answer A k
              (history ++ [(A.query st, answer history (A.query st))])
              (Function.update remaining (A.query st).1 (remaining (A.query st).1 - 1))
              (A.update st (answer history (A.query st))) := rfl
    have hcost (D : ℕ) (history : List ((Fin 1 × Mat p.m p.n) × Mat p.m p.n))
        (st : A.State) :
        ((OracleTemplate._run answer A D history (fun _ => D) st).2.countP
          (fun e => e.1.1 == i)) = history.countP (fun e => e.1.1 == i) + D := by
      induction D generalizing history st with
      | zero =>
          change history.countP (fun e => e.1.1 == i) =
            history.countP (fun e => e.1.1 == i) + 0
          omega
      | succ D ih =>
          rw [hstep, ite_eq_right (Nat.succ_ne_zero D)]
          have hrem :
              Function.update (fun _ : Fin 1 => D + 1) (A.query st).1 (D + 1 - 1) =
                (fun _ => D) := by
            funext j
            have hj : j = (A.query st).1 := Subsingleton.elim _ _
            subst j
            simp
          rw [hrem, ih]
          have hidx : (A.query st).1 = i := Subsingleton.elim _ _
          simp only [List.countP_append, List.countP_singleton, hidx, beq_self_eq_true, ite_true]
          omega
    have hsum : (∑ _j : Fin 1, p.M * T) = p.M * T := by simp
    change ((OracleTemplate._run answer A (∑ _j : Fin 1, p.M * T) [] (fun _ => p.M * T)
      (A.initial seed)).2.countP (fun e => e.1.1 == i)) = p.M * T
    rw [hsum]
    simpa using hcost (p.M * T) [] (A.initial seed)
  )

end OracleTemplate.AsgoFixedRadius
