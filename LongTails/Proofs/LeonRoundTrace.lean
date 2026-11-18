import LongTails.Algorithms.LeonAggregate
import LongTails.Proofs.DashaModular
import LongTails.Algorithms.LeonProtocol

namespace LongTails.Proofs.LeonExchange

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonExchange
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.DashaModular (modulus)

lemma index_lt (p : Params) (j : Fin p.d) : j.val / p.n < blockSize p := by
  have hn := p.n.pos
  change j.val / p.n + 1 ≤ (p.d + p.n - 1) / p.n
  rw [Nat.le_div_iff_mul_le hn]
  have h := Nat.div_add_mod' j.val p.n
  have hr := Nat.mod_lt j.val hn
  have hj := j.isLt
  rw [Nat.add_mul, Nat.one_mul]
  omega

lemma round_trip (p : Params) (l : ℕ) (codes : Fin p.n → Fin p.d → ℤ)
    (suffix : Fin p.n → Fin p.n → List Bool) (suffix' : Fin p.n → List Bool) (j : Fin p.d) :
    unpack p l (fun owner => gather p l
      (fun i => scatter p l owner (codes i) ++ suffix i owner) ++ suffix' owner) j =
        (∑ i, codes i j) % modulus (width p l) := by
  simp only [unpack, dite_eq_left (index_lt p j), gather, scatter, DashaModular.decode_encode]
  rw [DashaModular.sum_residue_mod]
  have hi : j.val / p.n * p.n + j.val % p.n = j.val := Nat.div_add_mod' _ _
  simp [part, hi, j.isLt]

lemma scatter_length (p : Params) (l : ℕ) (i : Fin p.n) (codes : Fin p.d → ℤ) :
    (scatter p l i codes).length = blockSize p * width p l :=
  DashaModular.encode_length _ _ _

lemma gather_length (p : Params) (l : ℕ) (messages : Fin p.n → List Bool) :
    (gather p l messages).length = blockSize p * width p l :=
  DashaModular.encode_length _ _ _

end LongTails.Proofs.LeonExchange

namespace LongTails.Proofs.LeonTranscript

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.LeonExchange
open LongTails.Algorithms.LeonProtocol

inductive Op (p : Params)
  | sample (q : ComputeQuery p) (reply : ComputeReply p)
  | send (i : Fin p.n) (bits : List Bool)
  | receive (i : Fin p.n) (bits : List Bool)

inductive Trace {p : Params} : Program p → List (Op p) → Point p → Prop
  | done (x) : Trace (.finish x) [] x
  | sample {q f values ops x} (h : Trace (f values) ops x) :
    Trace (.sample q f) (.sample q values :: ops) x
  | send {i bits next ops x} (h : Trace next ops x) :
    Trace (.send i bits next) (.send i bits :: ops) x
  | receive {i f bits ops x} (h : Trace (f bits) ops x) :
    Trace (.receive i f) (.receive i bits :: ops) x

def wire (bits : List Bool) := bits ++ List.replicate clockBits false

def exchangeOps (p : Params) (outbound inbound : Fin p.n → List Bool) : List (Op p) :=
  (List.finRange p.n).map (fun i => .send i (outbound i)) ++
    (List.finRange p.n).map (fun i => .receive i (inbound i))

lemma post_trace {p : Params} (packets : Fin p.n → List Bool) {next : Program p} {ops x}
    (h : Trace next ops x) (ids : List (Fin p.n)) :
    Trace (post packets next ids) (ids.map (fun i => Op.send i (packets i)) ++ ops) x := by
  induction ids with
  | nil => exact h
  | cons i ids ih => exact Trace.send ih

lemma collect_trace {p : Params} (packets : Fin p.n → List Bool) {next} {ops : List (Op p)} {x}
    (h : Trace (next packets) ops x) (ids : List (Fin p.n)) (data : Fin p.n → List Bool)
    (hd : ∀ i, i ∉ ids → data i = packets i) :
    Trace (collect next ids data) (ids.map (fun i => Op.receive i (packets i)) ++ ops) x := by
  induction ids generalizing data with
  | nil =>
    have he : data = packets := funext fun i => hd i (by simp)
    subst data
    exact h
  | cons i ids ih =>
    apply Trace.receive
    apply ih
    intro j hj
    by_cases he : j = i
    · subst j; simp
    · rw [Function.update_of_ne he]
      exact hd j (by simp [he, hj])

lemma exchange_trace {p : Params} (outbound inbound : Fin p.n → List Bool) {next ops x}
    (h : Trace (next inbound) ops x) :
    Trace (exchange outbound next) (exchangeOps p outbound inbound ++ ops) x := by
  rw [exchangeOps, List.append_assoc]
  exact post_trace outbound (collect_trace inbound h _ _ (by simp)) _

lemma advance_mod (p : Params) (s : Model p) (l : ℕ) (raw got : Fin p.d → ℤ)
    (h : ∀ j, got j = raw j % LongTails.Algorithms.DashaModular.modulus (width p l)) :
    advance p s l got = advance p s l raw := by
  have he : (fun j => LongTails.Algorithms.DashaModular.restore (width p l) (got j)) =
      fun j => LongTails.Algorithms.DashaModular.restore (width p l) (raw j) := by
    funext j
    rw [h, DashaModular.restore_mod]
  simp only [advance, LongTails.Algorithms.LeonAggregate.decode, he]

end LongTails.Proofs.LeonTranscript

namespace LongTails.Proofs.LeonRoundTrace

open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.LeonExchange
open LongTails.Algorithms.LeonProtocol
open LongTails.Algorithms.LeonAggregate
open LeonTranscript

structure Round (p : Params) where
  level : ℕ
  model : Model p
  values : Fin p.n → List (Point p)

noncomputable def code (R : Round p) (i : Fin p.n) : Fin p.d → ℤ :=
  localCodes (spacing p) (R.model.anchors (R.level + 1)) (mean p (R.values i))

noncomputable def partPacket (R : Round p) (i toWorker : Fin p.n) : List Bool :=
  scatter p R.level toWorker (code R i)

noncomputable def sumPacket (R : Round p) (i : Fin p.n) : List Bool :=
  gather p R.level (fun j => wire (partPacket R j i))

noncomputable def operations (R : Round p) (i : Fin p.n) : List (Op p) :=
  .sample (R.model.point, batch p i R.level) (R.values i) ::
    (exchangeOps p (partPacket R i) (fun j => wire (partPacket R j i)) ++
     exchangeOps p (fun _ => sumPacket R i) (fun j => wire (sumPacket R j)))

noncomputable def nextModel (R : Round p) : Model p :=
  advance p R.model R.level (totalCodes p R.model R.level R.values)

lemma unpack_step (R : Round p) :
    advance p R.model R.level (unpack p R.level (fun j => wire (sumPacket R j))) = nextModel R := by
  apply LeonTranscript.advance_mod
  intro j
  exact LeonExchange.round_trip p R.level (code R) (fun _ _ => _) (fun _ => _) j

lemma round_trace (R : Round p) (worker : Fin p.n) (a b : ℕ) (rest : List ℕ)
    (ops : List (Op p)) (x : Point p)
    (h : Trace (schedule p worker a b rest (nextModel R)) ops x) :
    Trace (schedule p worker a b (R.level :: rest) R.model) (operations R worker ++ ops) x := by
  simp only [schedule, operations, List.cons_append, List.append_assoc]
  apply Trace.sample
  apply exchange_trace
  apply exchange_trace
  rw [unpack_step]
  exact h

noncomputable def actualRound (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (ls : List ℕ) (t : ℕ) : Round p :=
  let model := trajectory p g s ls t
  let l := ls[t]?.getD 0
  ⟨l, model, samplesAt p g s (spent p (ls.take t)) l model.point⟩

lemma whole_trace (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (ls : List ℕ) (i : Fin p.n) (a b : ℕ) (t count : ℕ)
    (hend : t + count = ls.length) :
    Trace (schedule p i a b (ls.drop t) (trajectory p g s ls t))
      ((List.range' t count).flatMap (fun k => operations (actualRound p g s ls k) i))
      (output p (trajectory p g s ls ls.length) a b) := by
  induction count generalizing t with
  | zero =>
    have ht : t = ls.length := by omega
    subst t
    simp [schedule, Trace.done]
  | succ count ih =>
    have ht : t < ls.length := by omega
    have hdrop : ls.drop t = ls[t] :: ls.drop (t + 1) := (List.getElem_cons_drop ht).symm
    rw [hdrop, List.range'_succ, List.flatMap_cons]
    have h := round_trace (actualRound p g s ls t) i a b (ls.drop (t + 1)) _ _
      (ih (t + 1) (by omega))
    simpa only [actualRound, List.getElem?_eq_getElem ht, Option.getD_some] using h

end LongTails.Proofs.LeonRoundTrace
