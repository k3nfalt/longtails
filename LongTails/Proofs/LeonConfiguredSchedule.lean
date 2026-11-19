import LongTails.Proofs.LeonReservations
import LongTails.Proofs.LeonTiming
import LongTails.Proofs.LeonScheduledExecution

namespace LongTails.Proofs.LeonScheduleCertificate

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LeonReservations LeonTranscript

structure Suitable (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (pre : List (Frame p)) (c : Frame p) : Prop where
  order : c.start ≤ c.finish
  sample : ∀ i q vals, c.op i = .sample q vals →
    c.start + (q.2 : ℕ) * p.h i ≤ c.finish ∧
      vals = (List.range q.2).map (fun j => g i q.1 (s i (usedCount pre i + j)))
  send : ∀ i j bits, c.op i = .send j bits →
    c.start + p.l + p.b * (wire bits).length ≤ c.delivery ∧ ∀ m ∈ posted pre i j, m.1 ≤ c.start
  receive : ∀ j i bits, c.op j = .receive i bits →
    c.delivery ≤ c.start ∧ consumed pre i j ++ [(c.delivery,bits)] <+: posted pre i j

inductive Checked (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) : List (Frame p) → Time → Prop
  | nil (T) : Checked g s [] T
  | snoc {pre c T} (prior : Checked g s pre c.start) (ok : Suitable g s pre c)
      (finish : c.finish ≤ T) : Checked g s (pre ++ [c]) T

lemma Checked.later {g : Fin p.n → Point p → p.Ω → Point p} {s : Samples p} {rows t u}
    (h : Checked g s rows t) (ht : t ≤ u) : Checked g s rows u := by
  cases h with
  | nil => exact .nil _
  | snoc prior ok hfin => exact .snoc prior ok (hfin.trans ht)

lemma Checked.lookup {g : Fin p.n → Point p → p.Ω → Point p} {s : Samples p} {rows T}
    (h : Checked g s rows T) (pre : List (Frame p)) (c : Frame p) (tail : List (Frame p))
    (he : rows = pre ++ c :: tail) :
    Suitable g s pre c ∧ c.finish ≤ due T tail false ∧ c.finish ≤ T := by
  induction h generalizing pre c tail with
  | nil => simp at he
  | @snoc past last cap prior ok hfin ih =>
    induction tail using List.reverseRecOn with
    | nil =>
      obtain rfl : past = pre := List.append_inj_left' he (by simp)
      have hl := List.append_cancel_left he
      obtain rfl : last = c := List.cons.inj hl |>.1
      exact ⟨ok, hfin, hfin⟩
    | append_singleton tail e _ =>
      have he' : (past ++ [last]) = (pre ++ c :: tail) ++ [e] := by simpa using he
      have heq := List.append_inj_left' he' (by simp)
      have hl := List.append_cancel_left (heq ▸ he')
      obtain rfl : last = e := List.cons.inj hl |>.1
      obtain ⟨hok, hg, hb⟩ := ih pre c tail heq
      refine ⟨hok, ?_, hb.trans (ok.order.trans hfin)⟩
      cases tail <;> simpa [due] using hg

lemma Checked.certificate {g : Fin p.n → Point p → p.Ω → Point p} {s : Samples p} {rows T}
    (h : Checked g s rows T) : Certified g s T rows := by
  refine ⟨fun pre c rest he => ⟨(h.lookup pre c rest he).1.order, (h.lookup pre c rest he).2.1⟩,
    ?_, fun pre c rest he => (h.lookup pre c rest he).1.sample,
    fun pre c rest he => (h.lookup pre c rest he).1.send,
    fun pre c rest he => (h.lookup pre c rest he).1.receive⟩
  intro c hc
  obtain ⟨pre, rest, he⟩ := List.append_of_mem hc
  exact (h.lookup pre c rest he).2.2

end LongTails.Proofs.LeonScheduleCertificate

namespace LongTails.Proofs.LeonExchangeReservations

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LeonReservations LeonScheduleCertificate LeonTranscript

variable {p : Params}

abbrev Packets (p : Params) := Fin p.n → Fin p.n → List Bool

def sendFrame (t d : Time) (B : Packets p) (j : Fin p.n) : Frame p :=
  ⟨fun i => .send j (B i j), t, t, d⟩

def recvFrame (d : Time) (B : Packets p) (i : Fin p.n) : Frame p :=
  ⟨fun j => .receive i (wire (B i j)), d, d, d⟩

def phase (t d : Time) (B : Packets p) : List (Frame p) :=
  (List.finRange p.n).map (sendFrame t d B) ++ (List.finRange p.n).map (recvFrame d B)

lemma sent_list (t d : Time) (B : Packets p) (ids : List (Fin p.n)) (hn : ids.Nodup) (i j : Fin p.n) :
    posted (ids.map (sendFrame t d B)) i j = if j ∈ ids then [(d,wire (B i j))] else [] := by
  induction ids with
  | nil => simp [posted]
  | cons k ks ih =>
    obtain ⟨hnk,hks⟩ := List.nodup_cons.mp hn
    change sends (sendFrame t d B k) i j ++ posted (ks.map (sendFrame t d B)) i j = _
    by_cases he : j = k
    · subst j; simp [sends,sendFrame,ih hks,hnk]
    · simp [sends,sendFrame,Ne.symm he,he,ih hks]

lemma recv_list (d : Time) (B : Packets p) (ids : List (Fin p.n)) (hn : ids.Nodup) (i j : Fin p.n) :
    consumed (ids.map (recvFrame d B)) i j = if i ∈ ids then [(d,wire (B i j))] else [] := by
  induction ids with
  | nil => simp [consumed]
  | cons k ks ih =>
    obtain ⟨hnk,hks⟩ := List.nodup_cons.mp hn
    change receives (recvFrame d B k) i j ++ consumed (ks.map (recvFrame d B)) i j = _
    by_cases he : i = k
    · subst i; simp [receives,recvFrame,ih hks,hnk]
    · simp [receives,recvFrame,Ne.symm he,he,ih hks]

lemma phase_effect (t d : Time) (B : Packets p) (i j : Fin p.n) :
    posted (phase t d B) i j = [(d,wire (B i j))] ∧
    consumed (phase t d B) i j = [(d,wire (B i j))] ∧ usedCount (phase t d B) i = 0 := by
  have hs := sent_list t d B (List.finRange p.n) (List.nodup_finRange _) i j
  have hr := recv_list d B (List.finRange p.n) (List.nodup_finRange _) i j
  simp only [List.mem_finRange,ite_true] at hs hr
  have hsend (ids : List (Fin p.n)) : consumed (ids.map (sendFrame t d B)) i j = [] ∧
      usedCount (ids.map (sendFrame t d B)) i = 0 := by
    induction ids with
    | nil => simp [usedCount,consumed]
    | cons k ks ih =>
      exact ⟨ih.1, by simpa [usedCount,used,sendFrame] using ih.2⟩
  have hrecv (ids : List (Fin p.n)) : posted (ids.map (recvFrame d B)) i j = [] ∧
      usedCount (ids.map (recvFrame d B)) i = 0 := by
    induction ids with
    | nil => simp [usedCount,posted]
    | cons k ks ih =>
      exact ⟨ih.1, by simpa [usedCount,used,recvFrame] using ih.2⟩
  unfold phase
  simp only [posted,consumed,usedCount,List.flatMap_append,List.map_append,List.sum_append] at *
  simp only [hs,hr,(hsend _).1,(hsend _).2,(hrecv _).1,(hrecv _).2, List.append_nil, List.nil_append, add_zero, and_self]

lemma phase_checked {g : Fin p.n → Point p → p.Ω → Point p} {s : Samples p}
    (t d : Time) (B : Packets p) (pre : List (Frame p)) (hp : Checked g s pre t)
    (hs : ∀ i j, t + p.l + p.b * (wire (B i j)).length ≤ d)
    (ht : t ≤ d) (hpay : ∀ i j m, m ∈ posted pre i j → m.1 ≤ t)
    (hmatch : ∀ i j, posted pre i j = consumed pre i j) :
    Checked g s (pre ++ phase t d B) d := by
  have first (ids : List (Fin p.n)) (hids : ids.Nodup) (xs : List (Frame p))
      (hx : Checked g s xs t) (hh : ∀ i j, j ∈ ids → ∀ m ∈ posted xs i j, m.1 ≤ t) :
      Checked g s (xs ++ ids.map (sendFrame t d B)) t := by
    induction ids generalizing xs with
    | nil => simpa using hx
    | cons j js ih =>
      let c := sendFrame t d B j
      have hnd := List.nodup_cons.mp hids
      have hgood : Suitable g s xs c := by
        refine ⟨le_rfl, by simp [c,sendFrame], ?_, by simp [c,sendFrame]⟩
        intro i j' bits h
        obtain ⟨rfl,rfl⟩ := Op.send.inj h
        exact ⟨hs i j, hh i j (by simp)⟩
      have hnext := ih hnd.2 (xs ++ [c]) (.snoc hx hgood le_rfl) (by
        intro i k hk
        have hne : j ≠ k := fun he => hnd.1 (he ▸ hk)
        simpa [posted,c,sends,sendFrame,hne] using hh i k (List.mem_cons_of_mem _ hk))
      simpa [List.append_assoc,c] using hnext
  let mid := pre ++ (List.finRange p.n).map (sendFrame t d B)
  have hm : Checked g s mid d := (first _ (List.nodup_finRange _) _ hp (fun i j _ => hpay i j)).later ht
  have second (ids : List (Fin p.n)) (hids : ids.Nodup) (xs : List (Frame p))
      (hx : Checked g s xs d) (hh : ∀ i ∈ ids, ∀ j, consumed xs i j ++ [(d,wire (B i j))] <+: posted xs i j) :
      Checked g s (xs ++ ids.map (recvFrame d B)) d := by
    induction ids generalizing xs with
    | nil => simpa using hx
    | cons i is ih =>
      let c := recvFrame d B i
      have hnd := List.nodup_cons.mp hids
      have hgood : Suitable g s xs c := by
        refine ⟨le_rfl, by simp [c,recvFrame], by simp [c,recvFrame], ?_⟩
        intro j i' bits h
        obtain ⟨rfl,rfl⟩ := Op.receive.inj h
        exact ⟨le_rfl,hh i (by simp) j⟩
      have hnext := ih hnd.2 (xs ++ [c]) (.snoc hx hgood le_rfl) (by
        intro k hk j
        have hne : i ≠ k := fun he => hnd.1 (he ▸ hk)
        simpa [posted,consumed,c,sends,receives,recvFrame,hne] using hh k (List.mem_cons_of_mem _ hk) j)
      simpa [List.append_assoc,c] using hnext
  have hdone := second (List.finRange p.n) (List.nodup_finRange _) mid hm (by
    intro i _ j
    have hsent := sent_list t d B _ (List.nodup_finRange _) i j
    have hcons (ids : List (Fin p.n)) : consumed (ids.map (sendFrame t d B)) i j = [] := by
      induction ids with
      | nil => rfl
      | cons k ks ih => exact ih
    have he : posted mid i j = consumed mid i j ++ [(d,wire (B i j))] := by
      simp only [mid,posted,consumed,List.flatMap_append]
      change posted pre i j ++ posted ((List.finRange p.n).map (sendFrame t d B)) i j =
        (consumed pre i j ++ consumed ((List.finRange p.n).map (sendFrame t d B)) i j) ++ _
      rw [hsent,hcons,hmatch]
      simp
    rw [he])
  simpa [mid,phase,List.append_assoc] using hdone

end LongTails.Proofs.LeonExchangeReservations

namespace LongTails.Proofs.LeonRoundReservations

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonTrajectory
open LeonReservations LeonScheduleCertificate LeonExchangeReservations LeonTiming LeonRoundTrace LeonTranscript

noncomputable def computeFinish (p : Params) (t : Time) (l : ℕ) := t + 2^l * computeUnit p
noncomputable def transfer (p : Params) (l : ℕ) := (2:Time)^l * linkUnit p

noncomputable def compFrame (t : Time) (R : Round p) : Frame p :=
  ⟨fun i => .sample (R.model.point,batch p i R.level) (R.values i), t, computeFinish p t R.level, 0⟩

noncomputable def frames (t : Time) (R : Round p) : List (Frame p) :=
  let b := computeFinish p t R.level
  let z := transfer p R.level
  compFrame t R :: (phase b (b+z) (partPacket R) ++ phase (b+z) (b+z+z) (fun i _ => sumPacket R i))

lemma finish_eq (p : Params) (t : Time) (j : ℕ) :
    computeFinish p t j + transfer p j + transfer p j = t + roundTime p j := by
  simp only [computeFinish,transfer,roundTime]
  ring

lemma frame_ops (t : Time) (R : Round p) (i : Fin p.n) :
    (frames t R).map (fun c => c.op i) = operations R i := by
  simp [frames,operations,compFrame,phase,sendFrame,recvFrame,exchangeOps,List.append_assoc,
    Function.comp_def]

structure Settled (p : Params) (pre : List (Frame p)) (atTime : Time) : Prop where
  match_link : ∀ i j, posted pre i j = consumed pre i j
  paid : ∀ i j m, m ∈ posted pre i j → m.1 ≤ atTime

lemma settled_phase {pre : List (Frame p)} {t d : Time} (h : Settled p pre t) (ht : t ≤ d)
    (B : Packets p) : Settled p (pre ++ phase t d B) d := by
  constructor
  · intro i j
    simp only [posted,consumed,List.flatMap_append]
    change posted pre i j ++ posted (phase t d B) i j = consumed pre i j ++ consumed (phase t d B) i j
    rw [h.match_link, (phase_effect t d B i j).1,(phase_effect t d B i j).2.1]
  · intro i j m hm
    have hh : m ∈ posted pre i j ++ posted (phase t d B) i j := by simpa [posted] using hm
    rw [(phase_effect t d B i j).1,List.mem_append,List.mem_singleton] at hh
    rcases hh with hmem | rfl
    · exact (h.paid i j m hmem).trans ht
    · rfl

lemma extend (p : Params) (hh : ∀ i, 0 < p.h i) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (R : Round p) (t : Time) (pre : List (Frame p)) (hcheck : Checked g s pre t)
    (hfree : Settled p pre t)
    (hr : ∀ i, R.values i = (List.range (batch p i R.level)).map
      (fun k => g i R.model.point (s i (usedCount pre i + k)))) :
    Checked g s (pre ++ frames t R) (t + roundTime p R.level) ∧
    Settled p (pre ++ frames t R) (t + roundTime p R.level) ∧
    ∀ i, usedCount (pre ++ frames t R) i = usedCount pre i + (batch p i R.level : ℕ) := by
  let l := R.level
  let b := computeFinish p t l
  let z := transfer p l
  have htb : t ≤ b := le_self_add
  have hbg : b ≤ b+z := le_self_add
  have hge : b+z ≤ b+z+z := le_self_add
  let xs := pre ++ [compFrame t R]
  have hgood : Suitable g s pre (compFrame t R) := by
    refine ⟨htb, ?_, by simp [compFrame], by simp [compFrame]⟩
    intro i q vals he
    obtain ⟨rfl,rfl⟩ := Op.sample.inj he
    exact ⟨add_le_add_right (batch_time p hh i l) t,hr i⟩
  have hx : Checked g s xs b := .snoc hcheck hgood le_rfl
  have hfx : Settled p xs b := by
    constructor
    · intro i j; simpa [xs,posted,consumed,sends,receives,compFrame] using hfree.match_link i j
    · intro i j m hm; exact (hfree.paid i j m (by simpa [xs,posted,sends,compFrame] using hm)).trans htb
  have hp (i j : Fin p.n) : (wire (partPacket R i j)).length = 64 + blockSize p * width p l := by
    simp [wire,partPacket,LeonExchange.scatter_length,clockBits,l,Nat.add_comm]
  have hq (i : Fin p.n) : (wire (sumPacket R i)).length = 64 + blockSize p * width p l := by
    simp [wire,sumPacket,LeonExchange.gather_length,clockBits,l,Nat.add_comm]
  have hcap : p.l + p.b * (64 + blockSize p * width p l : ℕ) ≤ z := width_time p l
  have hphase := phase_checked b (b+z) (partPacket R) xs hx (fun i j => by
    rw [hp]; simpa only [add_assoc] using add_le_add_right hcap b) hbg hfx.paid hfx.match_link
  have hm := settled_phase hfx hbg (partPacket R)
  have hlast := phase_checked (b+z) (b+z+z) (fun i _ => sumPacket R i) _ hphase (fun i _ => by
    rw [hq]; simpa only [add_assoc] using add_le_add_right hcap (b+z)) hge hm.paid hm.match_link
  have he := settled_phase hm hge (fun i _ => sumPacket R i)
  have hlist : pre ++ frames t R = (xs ++ phase b (b+z) (partPacket R)) ++
      phase (b+z) (b+z+z) (fun i _ => sumPacket R i) := by simp [xs,frames,b,z,l,List.append_assoc]
  rw [hlist,← finish_eq]
  refine ⟨hlast,he,fun i => ?_⟩
  have hu (xs ys : List (Frame p)) : usedCount (xs++ys) i = usedCount xs i + usedCount ys i := by
    simp [usedCount]
  rw [hu,hu,(phase_effect _ _ _ i i).2.2,(phase_effect _ _ _ i i).2.2]
  simp [xs,usedCount,used,compFrame]

end LongTails.Proofs.LeonRoundReservations

namespace LongTails.Proofs.LeonConfiguredSchedule

open MeasureTheory

open DistributedTemplate
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex
open LongTails.Algorithms.LeonTuning
open LongTails.Algorithms.LeonTrajectory
open LongTails.Algorithms.LeonProtocol (algorithm)
open LongTails.Algorithms.LeonCalendar
open LeonRoundTrace LeonReservations LeonTiming LeonScheduleCertificate LeonRoundReservations

noncomputable def start (p : Params) (ls : List ℕ) (t : ℕ) : Time :=
  ((ls.take t).map (roundTime p)).sum

noncomputable def plan (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (ls : List ℕ) (t : ℕ) : List (Frame p) :=
  (List.range t).flatMap (fun k => frames (start p ls k) (actualRound p g s ls k))

lemma configured (p : Params) (hh : ∀ i, 0 < p.h i)
    (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (ls : List ℕ) (t : ℕ)
    (ht : t ≤ ls.length) :
    let xs := plan p g s ls t
    Checked g s xs (start p ls t) ∧ Settled p xs (start p ls t) ∧
    ∀ i, usedCount xs i = spent p (ls.take t) i := by
  induction t with
  | zero =>
    exact ⟨.nil _,⟨fun _ _ => rfl,by simp [plan,posted]⟩,fun _ => rfl⟩
  | succ t ih =>
    have ht' : t < ls.length := by omega
    obtain ⟨hc, hs, hused⟩ := ih ht'.le
    let R := actualRound p g s ls t
    have hl : R.level = ls[t] := by simp [R,actualRound,List.getElem?_eq_getElem ht']
    have hv (i) : R.values i = (List.range (batch p i R.level)).map
        (fun k => g i R.model.point (s i (usedCount (plan p g s ls t) i + k))) := by
      rw [hused]; rfl
    obtain ⟨hcheck,hsettle,hu⟩ := extend p hh g s R _ _ hc hs hv
    have hnext : plan p g s ls (t+1) = plan p g s ls t ++ frames (start p ls t) R := by
      simp [plan,List.range_succ,R]
    have htime : start p ls (t+1) = start p ls t + roundTime p R.level := by
      unfold start
      rw [List.take_succ_eq_append_getElem ht', hl]
      simp only [List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
    dsimp only
    rw [hnext,htime]
    refine ⟨hcheck,hsettle,fun i => ?_⟩
    rw [hu,hused,hl,List.take_succ_eq_append_getElem ht']
    simp only [spent,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]

lemma execute_output (p : Params) (hh : ∀ i, 0 < p.h i)
    (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (s : Samples p) (T : Time) (ab : (algorithm p T).Seed)
    (ht : ((levels (height p)).map (roundTime p)).sum ≤ T) :
    let ls := levels (height p)
    DistributedTemplate.execute (system p g P) (algorithm p T) T ab s =
      output p (trajectory p g s ls ls.length) ab.1 ab.2 := by
  let ls := levels (height p)
  let rows := plan p g s ls ls.length
  have htime : start p ls ls.length ≤ T := by simpa [start,ls] using ht
  have hh' := ((configured p hh g s ls ls.length le_rfl).1.later htime).certificate
  apply LeonScheduledExecution.execute (rows := rows) hh' ab
  intro i
  have htr := whole_trace p g s ls i ab.1 ab.2 0 ls.length (by simp)
  simpa [rows,plan,List.map_flatMap,frame_ops,List.range_eq_range',algorithm,ls,trajectory] using htr

end LongTails.Proofs.LeonConfiguredSchedule
