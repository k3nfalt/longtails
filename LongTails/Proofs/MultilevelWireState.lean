import LongTails.Proofs.MultilevelTransportState

namespace LongTails.Proofs.MultilevelWireState

open DistributedTemplate MeasureTheory LongTails.Setups
open DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport
open MultilevelTransportState MultilevelTimetable

variable {p : Params}

noncomputable def Phase.downlink (t : Script p) (out : ℕ → Bits) : Phase → Option (Time × Bits)
  | .down j τ => some (τ, frame (payload t out j))
  | _ => none

def Phase.uplink (out : ℕ → Bits) : Phase → Option (Time × Bits)
  | .up j τ => some (τ, frame (out j))
  | _ => none

noncomputable def Phase.computing (t : Script p) (out : ℕ → Bits) : Phase → Option (Time × Query p)
  | .work j τ => some (τ, t.decode (payload t out j))
  | _ => none

noncomputable def wires (t : Script p) (out : ℕ → Bits) (b : Book p) : StarNetwork.CommunicationState p.n :=
  ⟨Fin.cases (Fin.cases none (fun i => Phase.downlink t out (b.pending i)))
    (fun i => Fin.cases (Phase.uplink out (b.pending i)) (fun _ => none))⟩

noncomputable def unitState (t : Script p) (out : ℕ → Bits) (b : Book p) (xs : Samples p) (i : Fin p.n) :
    StarNetwork.ComputationState (Query p) (Samples p) :=
  ⟨Phase.computing t out (b.pending i), xs, count t i b.issued - (b.pending i).unused⟩

noncomputable def machine (t : Script p) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) (xs : Samples p) (b : Book p) : OracleState (system p g P) :=
  ⟨Fin.cases ⟨none,xs,0⟩ (unitState t (reply t g xs) b xs), wires t (reply t g xs) b⟩

noncomputable def nodes (b : Book p) (seed : Selection p) (out : ℕ → Bits) : Fin (p.n+1) → State p :=
  Fin.cases (root b seed out) (worker b seed)

def Phase.within (p : Params) (t : Script p) (out : ℕ → Bits) (i : Fin p.n) : Phase → Prop
  | .idle => True
  | .down j τ => τ + 2*p.h i + wire p (out j) ≤ t.finish j
  | .work j τ => τ + wire p (out j) ≤ t.finish j
  | .up j τ => τ ≤ t.finish j

lemma phase_idle {u : Phase} (hu : u.job = none) : u = .idle := by cases u <;> simp_all [Phase.job]

lemma update_job {α : Type*} {β : Type*} [DecidableEq α] (f : α → Phase) (g : Phase → β)
    (i : α) (u : Phase) :
    (fun j => g (Function.update f i u j)) = Function.update (fun j => g (f j)) i (g u) := by
  funext j
  by_cases h : j = i <;> simp [h]

lemma dispatch_yes {t : Script p} (b : Book p) (seed : Selection p) (out : ℕ → Bits)
    (τ : Time) (h : ready t (root b seed out)) :
    dispatch t (root b seed out) =
      (.communicate ((t.worker b.issued).succ, payload t out b.issued), root (launch t b τ) seed out) := by
  rw [dispatch, ite_eq_left h]
  simp only [root, launch] at *
  rw [show t.request b.issued (visible t b.issued (fun j => if j ∈ b.done then some (out j) else none)) =
    payload t out b.issued from visible_ready t b seed out h]
  rw [update_job]
  rfl

lemma dispatch_no {t : Script p} (b : Book p) (seed : Selection p) (out : ℕ → Bits)
    (h : ¬ready t (root b seed out)) : dispatch t (root b seed out) = (.advance 0,root b seed out) := by
  simp [dispatch,h]

lemma accepted (b : Book p) (seed : Selection p) (out : ℕ → Bits) (i : Fin p.n) (j : ℕ)
    (h : (b.pending i).job = some j) :
    accept (root b seed out) i (frame (out j)) = root (collect b i j) seed out := by
  simp only [accept,root,collect,h,unframe_frame,update_job]
  congr 1
  funext k
  by_cases hk : k = j <;> simp [hk]

lemma worker_nodes {b : Book p} {seed : Selection p} {out : ℕ → Bits} (i : Fin p.n) :
    nodes b seed out i.succ = worker b seed i := rfl

lemma root_nodes {b : Book p} {seed : Selection p} {out : ℕ → Bits} :
    nodes b seed out 0 = root b seed out := rfl

lemma wires_down (t : Script p) (out : ℕ → Bits) (b : Book p) (i : Fin p.n) :
    (wires t out b).messages 0 i.succ = Phase.downlink t out (b.pending i) := rfl

lemma wires_up (t : Script p) (out : ℕ → Bits) (b : Book p) (i : Fin p.n) :
    (wires t out b).messages i.succ 0 = Phase.uplink out (b.pending i) := rfl

lemma wires_update_down (t : Script p) (out : ℕ → Bits) (b c : Book p) (i : Fin p.n)
    (hs : ∀ a, Phase.uplink out (c.pending a) = Phase.uplink out (b.pending a))
    (ho : ∀ a ≠ i, Phase.downlink t out (c.pending a) = Phase.downlink t out (b.pending a)) :
    wires t out c = ⟨Function.update (wires t out b).messages 0
      (Function.update ((wires t out b).messages 0) i.succ (Phase.downlink t out (c.pending i)))⟩ := by
  have hzi : (0 : Fin (p.n+1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero _)
  apply congrArg StarNetwork.CommunicationState.mk
  funext v w
  induction v using Fin.cases with
  | zero =>
    induction w using Fin.cases with
    | zero => simp [wires,hzi]
    | succ a =>
      by_cases ha : a = i <;> simp [wires, ha, ho]
  | succ a =>
    induction w using Fin.cases with
    | zero => simp [wires,hs]
    | succ d => simp [wires]

lemma wires_update_up (t : Script p) (out : ℕ → Bits) (b c : Book p) (i : Fin p.n)
    (hs : ∀ a, Phase.downlink t out (c.pending a) = Phase.downlink t out (b.pending a))
    (ho : ∀ a ≠ i, Phase.uplink out (c.pending a) = Phase.uplink out (b.pending a)) :
    wires t out c = ⟨Function.update (wires t out b).messages i.succ
      (Function.update ((wires t out b).messages i.succ) 0 (Phase.uplink out (c.pending i)))⟩ := by
  have hzi : (0 : Fin (p.n+1)) ≠ i.succ := Ne.symm (Fin.succ_ne_zero _)
  apply congrArg StarNetwork.CommunicationState.mk
  funext v w
  induction v using Fin.cases with
  | zero =>
    induction w using Fin.cases with
    | zero => simp [wires,hzi]
    | succ a => simp [wires,hs,hzi]
  | succ a =>
    by_cases ha : a = i
    · subst a
      induction w using Fin.cases with
      | zero => simp [wires]
      | succ d => simp [wires]
    · induction w using Fin.cases with
      | zero => simp [wires,ha,ho]
      | succ d => simp [wires,ha]

end LongTails.Proofs.MultilevelWireState
