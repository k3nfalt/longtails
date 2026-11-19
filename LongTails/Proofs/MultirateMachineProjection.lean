import LongTails.Proofs.MultirateMachine

open MeasureTheory

namespace LongTails.Proofs.MultirateMachine

open DistributedTemplate LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateProtocol
open MultirateReservations

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)

lemma map_update {ι α β : Type*} [DecidableEq ι] (f : ι → α → β) (b : ι → α) (i : ι) (v : α) :
    (fun j => f j (Function.update b i v j)) = Function.update (fun j => f j (b j)) i (f i v) := by
  funext j
  by_cases h : j = i <;> simp [h]

lemma cases_update {α : Type*} (u : α) (f : Fin p.n → α) (i : Fin p.n) (v : α) :
    (Fin.cases (motive := fun _ => α) u (Function.update f i v)) = Function.update (Fin.cases (motive := fun _ => α) u f) i.succ v := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  · by_cases h : k = i <;> simp [h]

lemma inbox_update (b : Table p) (i : Fin p.n) (v : Cell p) :
    inbox g s (Function.update b i v) = Function.update (inbox g s b) i (mailbox g s i v) :=
  map_update (mailbox g s) b i v

lemma workers_root (b : Table p) (prog prog' : Program p) :
    workersOf g s b prog' = Function.update (workersOf g s b prog) 0 ⟨prog',inbox g s b,.idle,false⟩ := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [workersOf]

lemma workers_leaf (b : Table p) (prog : Program p) (i : Fin p.n) (v : Cell p)
    (hm : mailbox g s i v = mailbox g s i (b i)) :
    workersOf g s (Function.update b i v) prog = Function.update (workersOf g s b prog) i.succ
      ⟨.done p.x0, fun _ => none, phaseOf g s i v,false⟩ := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    simp only [workersOf,Fin.cases_zero,inbox_update,hm]
    rw [show mailbox g s i (b i) = inbox g s b i from rfl, Function.update_eq_self]
  · by_cases h : k = i <;> simp [workersOf,h]

lemma workers_mail (b : Table p) (prog prog' : Program p) (i : Fin p.n) (v : Cell p)
    (hphase : phaseOf g s i v = phaseOf g s i (b i)) :
    workersOf g s (Function.update b i v) prog' = Function.update (workersOf g s b prog) 0
      ⟨prog',inbox g s (Function.update b i v),.idle,false⟩ := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [workersOf]
  · by_cases h : k = i <;> simp [workersOf,h,hphase]

lemma messages_down (b : Table p) (i : Fin p.n) (v : Cell p) (hu : uplink g s i v = uplink g s i (b i)) :
    messages g s (Function.update b i v) = Function.update (messages g s b) 0
      (Function.update (messages g s b 0) i.succ (downlink v)) := by
  funext a z
  refine Fin.cases ?_ (fun j => ?_) a
  · refine Fin.cases ?_ (fun k => ?_) z
    · simp [messages, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    · by_cases h : k = i <;> simp [messages,h]
  · refine Fin.cases ?_ (fun k => ?_) z
    · by_cases h : j = i <;> simp [messages,h,hu]
    · simp [messages]

lemma messages_up (b : Table p) (i : Fin p.n) (v : Cell p) (hd : downlink v = downlink (b i)) :
    messages g s (Function.update b i v) = Function.update (messages g s b) i.succ
      (Function.update (messages g s b i.succ) 0 (uplink g s i v)) := by
  funext a z
  refine Fin.cases ?_ (fun j => ?_) a
  · refine Fin.cases ?_ (fun k => ?_) z
    · simp [messages, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    · by_cases h : k = i <;> simp [messages,h,hd, Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  · refine Fin.cases ?_ (fun k => ?_) z
    · by_cases h : j = i <;> simp [messages,h]
    · by_cases h : j = i <;> simp [messages,h]

lemma messages_same (b : Table p) (i : Fin p.n) (v : Cell p)
    (hd : downlink v = downlink (b i)) (hu : uplink g s i v = uplink g s i (b i)) :
    messages g s (Function.update b i v) = messages g s b := by
  rw [messages_down g s b i v hu, hd]
  have h : downlink (b i) = messages g s b 0 i.succ := by simp [messages]
  rw [h, Function.update_eq_self, Function.update_eq_self]

lemma computation_update (P : ProbabilityMeasure (Samples p)) (b : Table p) (i : Fin p.n) (v : Cell p) :
    (oracleOf g P s (Function.update b i v)).computation =
      Function.update (oracleOf g P s b).computation i.succ (computationOf s i v) := by
  change Fin.cases (motive := fun _ => Setups.StarNetwork.ComputationState (Point p) (Samples p)) ⟨none,s,0⟩ _ = _
  rw [map_update (computationOf s)]
  exact cases_update _ _ i _

lemma computation_same (P : ProbabilityMeasure (Samples p)) (b : Table p) (i : Fin p.n) (v : Cell p)
    (h : computationOf s i v = computationOf s i (b i)) :
    (oracleOf g P s (Function.update b i v)).computation = (oracleOf g P s b).computation := by
  rw [computation_update, h]
  have he : computationOf s i (b i) = (oracleOf g P s b).computation i.succ := by rfl
  rw [he, Function.update_eq_self]

end LongTails.Proofs.MultirateMachine
