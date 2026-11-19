import LongTails.Proofs.MultilevelWireState

namespace LongTails.Proofs.MultilevelWireTransitions

open DistributedTemplate MeasureTheory LongTails.Setups
open DistributedMeanSquaredSmooth
open LongTails.Algorithms.MultilevelTransport
open MultilevelTransportState MultilevelTimetable MultilevelWireState

variable {p : Params} {t : Script p} {out : ℕ → Bits} {b : Book p} {i : Fin p.n}

lemma nodes_root_update (c : Book p) (seed : Selection p) (hs : c.memory = b.memory) :
    Function.update (nodes b seed out) 0 (root c seed out) = nodes c seed out := by
  funext v
  induction v using Fin.cases with
  | zero => simp [nodes]
  | succ a => simp [nodes,worker,hs]

lemma nodes_worker_update (c : Book p) (seed : Selection p) (hc : root c seed out = root b seed out)
    (hm : ∀ a ≠ i, c.memory a = b.memory a) :
    Function.update (nodes b seed out) i.succ (worker c seed i) = nodes c seed out := by
  funext v
  induction v using Fin.cases with
  | zero => simp [nodes,Ne.symm (Fin.succ_ne_zero i),hc]
  | succ a => by_cases h : a = i <;> simp [nodes,h,worker,hm]

lemma root_same (c : Book p) (seed : Selection p) (hn : c.issued = b.issued)
    (hd : c.done = b.done) (hp : ∀ i, (c.pending i).job = (b.pending i).job) :
    root c seed out = root b seed out := by simp only [root,hn,hd,hp]

lemma down_launch (τ : Time) (hf : b.pending (t.worker b.issued) = .idle) :
    wires t out (launch t b τ) = ⟨Function.update (wires t out b).messages 0
      (Function.update ((wires t out b).messages 0) (t.worker b.issued).succ
        (some (τ,frame (payload t out b.issued))))⟩ := by
  rw [wires_update_down t out b (launch t b τ) (t.worker b.issued) (by
    intro a
    by_cases ha : a = t.worker b.issued <;> simp [launch,ha,hf,MultilevelWireState.Phase.uplink]) (by
    intro a ha
    simp [launch,ha])]
  simp [launch,MultilevelWireState.Phase.downlink]


lemma units_launch (τ : Time) (xs : Samples p) (hf : b.pending (t.worker b.issued) = .idle) :
    unitState t out (launch t b τ) xs = unitState t out b xs := by
  funext a
  by_cases h : a = t.worker b.issued
  · subst a; simp [unitState,launch,hf,count_succ,Phase.unused,MultilevelWireState.Phase.computing]
  · simp [unitState,launch,h,count_succ,Ne.symm h]

lemma down_work {j : ℕ} {τ : Time} (h : b.pending i = .down j τ) (σ : Time) (bs : Bits) :
    wires t out (startWork b i j σ bs) = ⟨Function.update (wires t out b).messages 0
      (Function.update ((wires t out b).messages 0) i.succ none)⟩ := by
  rw [wires_update_down t out b (startWork b i j σ bs) (i) (by
    intro a
    by_cases ha : a = i <;> simp [startWork,ha,h,MultilevelWireState.Phase.uplink]) (by
    intro a ha
    simp [startWork,ha])]
  simp [startWork,MultilevelWireState.Phase.downlink]


lemma units_work {j : ℕ} {τ : Time} (h : b.pending i = .down j τ) (σ : Time) (bs : Bits) (xs : Samples p) :
    unitState t out (startWork b i j σ bs) xs = Function.update (unitState t out b xs) i
      {unitState t out b xs i with pending := some (σ,t.decode (payload t out j))} := by
  funext a
  by_cases ha : a = i <;> simp [unitState,startWork,ha,h,Phase.unused,MultilevelWireState.Phase.computing]

lemma up_reply {j : ℕ} {τ : Time} (h : b.pending i = .work j τ) (σ : Time) :
    wires t out (startReply b i j σ) = ⟨Function.update (wires t out b).messages i.succ
      (Function.update ((wires t out b).messages i.succ) 0 (some (σ,frame (out j))))⟩ := by
  rw [wires_update_up t out b (startReply b i j σ) (i) (by
    intro a
    by_cases ha : a = i <;> simp [startReply,ha,h,MultilevelWireState.Phase.downlink]) (by
    intro a ha
    simp [startReply,ha])]
  simp [startReply,MultilevelWireState.Phase.uplink]


lemma units_reply {j : ℕ} {τ : Time} (hv : Valid t b) (h : b.pending i = .work j τ)
    (σ : Time) (xs : Samples p) :
    unitState t out (startReply b i j σ) xs = Function.update (unitState t out b xs) i
      {unitState t out b xs i with pending := none, used := (unitState t out b xs i).used + 1} := by
  have hj : (b.pending i).job = some j := by simp [h,Phase.job]
  have hc := (hv.2.2.1 i j hj).2.2.2
  funext a
  by_cases ha : a = i <;> simp [unitState,startReply,ha,h,Phase.unused,MultilevelWireState.Phase.computing,hc]

lemma up_collect {j : ℕ} {τ : Time} (h : b.pending i = .up j τ) :
    wires t out (collect b i j) = ⟨Function.update (wires t out b).messages i.succ
      (Function.update ((wires t out b).messages i.succ) 0 none)⟩ := by
  rw [wires_update_up t out b (collect b i j) (i) (by
    intro a
    by_cases ha : a = i <;> simp [collect,ha,h,MultilevelWireState.Phase.downlink]) (by
    intro a ha
    simp [collect,ha])]
  simp [collect,MultilevelWireState.Phase.uplink]


lemma units_collect {j : ℕ} {τ : Time} (h : b.pending i = .up j τ) (xs : Samples p) :
    unitState t out (collect b i j) xs = unitState t out b xs := by
  funext a
  by_cases ha : a = i <;> simp [unitState,collect,ha,h,Phase.unused,MultilevelWireState.Phase.computing]

lemma succ_update {α : Type} (f g : Fin p.n → α) (v : α) (r : α)
    (h : g = Function.update f i v) :
    Fin.cases (motive := fun _ : Fin (p.n+1) => α) r g = Function.update (Fin.cases r f) i.succ v := by
  funext a
  induction a using Fin.cases with
  | zero => simp [Ne.symm (Fin.succ_ne_zero i)]
  | succ a => by_cases ha : a = i <;> simp [h,ha]

end LongTails.Proofs.MultilevelWireTransitions
