import LongTails.Proofs.GraceReservations

namespace LongTails.Proofs.GraceActions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.LeonProtocol
open LeonReservations (Frame Cursor CompOK due usedCount used posted consumed sends receives)
open LeonTranscript (Trace wire)
open GraceReservations

variable {p : Params} {g : Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
  {seed : Samples p} {rows : List (Frame p.base)} {out : Fin p.n → Point p} {limit : Time}
  {ws : Fin p.n → State p.base} {o : OracleState (system p g P)} {cur : Fin p.n → Cursor rows}

lemma computed (hc : Certified g seed limit rows) (h : Consistent g P seed rows out ws o cur)
    (i : Fin p.n) (time : Time) (val : ComputeReply p) (os : LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.ComputeState p.base)
    (hans : (LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.computation p.base (fun _ => g)).answer i (o.computation i) time = some (val,os)) :
    ∃ a : Cursor rows,
      Consistent g P seed rows out (Function.update ws i (update p.base (ws i) (.computed val)))
        {o with computation := Function.update o.computation i os} (Function.update cur i a) ∧
      due limit (cur i).rest (ws i).busy ≤ due limit a.rest (update p.base (ws i) (.computed val)).busy := by
  have hco := h.compute i
  obtain ⟨hseed, hu, hpend⟩ := hco
  cases hb : (ws i).busy with
  | false =>
    have hp : (o.computation i).pending = none := by simpa [hb] using hpend
    simp [LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.computation,hp] at hans
  | true =>
    obtain ⟨c, tail, q, vals, t, hr, ho, hp, hfin⟩ := (show ∃ c tail q vals t, (cur i).rest = c :: tail ∧
      c.op i = .sample q vals ∧ (o.computation i).pending = some (t,q) ∧ t ≤ c.finish from by
        simpa [hb] using hpend)
    have hrow := (cur i).layout.trans (congrArg (List.append (cur i).past) hr)
    obtain ⟨_, hv⟩ := hc.sample _ _ _ hrow i q vals ho
    obtain ⟨next, hpr, ht⟩ := LeonLocalTrace.sample (by simpa [hr, ho] using h.trace i)
    by_cases hav : t ≤ time
    · simp [LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.computation,hp,hav,hu,hseed,← hv] at hans
      obtain ⟨rfl,rfl⟩ := hans
      let a := (cur i).shift hr
      refine ⟨a, ?_, ?_⟩
      · apply GraceReservations.replace h i _ a _ _ _ _ _
        · simpa [update,hpr,a,Cursor.shift] using ht
        · simp [CompOK,update,hpr,a,Cursor.shift,usedCount,used,ho]
        · intro j hj
          simp [Function.update_of_ne hj]
        · intro k j
          by_cases hk : k = i <;> by_cases hj : j = i <;> subst_vars <;>
            simpa [Function.update_of_ne, *, a, Cursor.shift, posted, consumed, sends,
              receives, update] using h.link _ _
      · simpa [due,hr,hb,update,hpr,a,Cursor.shift] using (hc.ordered _ _ _ hrow).2
    · simp [LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.computation,hp,hav] at hans

lemma received (h : Consistent g P seed rows out ws o cur)
    (i j : Fin p.n) (bits : List Bool) (time : Time) (mail : Mail p)
    (hans : (communication p).answer o.communication time = some ((j,i,bits),mail)) :
    Consistent g P seed rows out (Function.update ws j (update p.base (ws j) (.received (i,bits))))
      {o with communication := mail} cur := by
  obtain ⟨finish, rest, hqueue, _, rfl⟩ := LeonNetwork.mail_answer p.base _ _ _ _ _ _ hans
  constructor
  · intro k
    by_cases hkj : k = j
    · subst k; simpa [update] using h.trace j
    · simpa [Function.update_of_ne hkj] using h.trace k
  · intro k
    by_cases hkj : k = j
    · subst k; simpa [CompOK,update] using h.compute j
    · simpa [Function.update_of_ne hkj] using h.compute k
  · intro k l
    by_cases hl : l = j
    · subst l
      by_cases hk : k = i
      · subst k
        have hh := h.link i j
        rw [hqueue] at hh
        simpa [update] using LeonLinkLedger.deliver hh
      · have he : (k,j) ≠ (i,j) := by simp [hk]
        simpa [update, Function.update_of_ne hk, Function.update_of_ne he] using h.link k j
    · have he : (k,l) ≠ (i,j) := by simp [hl]
      simpa [Function.update_of_ne hl, Function.update_of_ne he] using h.link k l

lemma act (cert : Certified g seed limit rows) (h : Consistent g P seed rows out ws o cur)
    (i : Fin p.n) (t : Time) (ht : t ≤ due limit (cur i).rest (ws i).busy) :
    let q := query p.base (ws i)
    ∃ a : Cursor rows, Consistent g P seed rows out (Function.update ws i q.2)
      (GraceExecution.after g P o i t q.1) (Function.update cur i a) ∧
      t ≤ due limit a.rest q.2.busy := by
  let w := ws i
  have htr := h.trace i
  cases hr : (cur i).rest with
  | nil =>
    rw [hr, List.map_nil] at htr
    have hp := LeonLocalTrace.done htr
    simpa [query,hp,GraceExecution.after] using (show ∃ a : Cursor rows,
      Consistent g P seed rows out (Function.update ws i (ws i)) o (Function.update cur i a) ∧
      t ≤ due limit a.rest (ws i).busy from ⟨cur i, by simpa using h,ht⟩)
  | cons c tail =>
    have hrow := (cur i).layout.trans (congrArg (List.append (cur i).past) hr)
    have hord := cert.ordered _ _ _ hrow
    rw [hr,List.map_cons] at htr
    let a := (cur i).shift hr
    cases ho : c.op i with
    | sample q vals =>
      rw [ho] at htr
      obtain ⟨nxt,hp,_⟩ := LeonLocalTrace.sample htr
      cases hb : (ws i).busy with
      | true =>
        refine ⟨cur i, ?_, ?_⟩
        · simpa [query,hp,hb,GraceExecution.after] using h
        · simpa [query,hp,hb] using ht
      | false =>
        have hco := h.compute i
        have hnone : (o.computation i).pending = none := by simpa [hb] using hco.2.2
        have hstart : t ≤ c.start := by simpa [due,hr,hb] using ht
        have htime := (add_le_add_left hstart ((q.2 : ℕ) * p.h i)).trans
          (cert.sample _ _ _ hrow i q vals ho).1
        refine ⟨cur i, ?_, ?_⟩
        · simp only [query,hp,hb,Bool.false_eq_true,ite_false,GraceExecution.after]
          apply GraceReservations.replace h
          · simpa only [hp] using h.trace i
          · simp only [CompOK, Function.update_self, system, LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.computation, hnone, Option.isSome_none,
              Bool.false_eq_true, ite_false, ite_true]
            exact ⟨hco.1,hco.2.1,c,tail,q,vals,_,hr,ho,rfl,htime⟩
          · intro k hk; simp [Function.update_of_ne hk]
          · intro k j
            by_cases hj : j = i
            · subst j; simpa using h.link k i
            · simpa [Function.update_of_ne hj] using h.link k j
        · simpa [query,hp,hb,hr,due] using hstart.trans hord.1
    | send j bits =>
      rw [ho] at htr
      obtain ⟨nxt,hp,hnext⟩ := LeonLocalTrace.send htr
      have hco := h.compute i
      have hb := LeonLocalTrace.nonbusy hco (by
        intro c' tail' q vals he
        rw [hr,List.cons.injEq] at he
        simp [← he.1,ho])
      have ht' : t ≤ c.start := by simpa [hr,hb,due] using ht
      obtain ⟨hedge, hc, hall⟩ := cert.send _ _ _ hrow i j bits ho
      have hf := arrival_bound h i j t c.start c.delivery bits ht' hc hall
      have postEq : (communication p).submit o.communication t i (j, wire bits) =
          Function.update o.communication (i,j) (o.communication (i,j) ++
            [(max t (((o.communication (i,j)).getLast?.map Prod.fst).getD 0) +
              duration p i j bits, wire bits)]) := by
        simp only [communication, ite_eq_left hedge, duration]
      refine ⟨a, ?_, ?_⟩
      · simp only [query,hp,GraceExecution.after]
        apply GraceReservations.replace h
        · exact hnext
        · simpa [CompOK, a, Cursor.shift, hb, usedCount, used, ho] using hco
        · intro _ _; rfl
        · intro k l
          erw [postEq]
          have hkl := h.link k l
          by_cases hk : k = i <;> by_cases hl : l = i <;> by_cases hj : l = j <;> (try have hj' := Ne.symm hj) <;> subst_vars <;>
            first
            | simpa [Function.update_of_ne, *, a, Cursor.shift, posted, consumed, sends, receives,
                wire] using LeonLinkLedger.append hkl _ _ _ hf
            | simpa [Function.update_of_ne, *, a, Cursor.shift, posted, consumed, sends, receives,
                wire] using hkl
      · simpa [query,hp,hb,a,Cursor.shift] using ht'.trans (hord.1.trans hord.2)
    | receive j bits =>
      rw [ho] at htr
      obtain ⟨nxt,hp,hnext⟩ := LeonLocalTrace.receive htr
      have hco := h.compute i
      have hb := LeonLocalTrace.nonbusy hco (by
        intro c' tail' q vals he
        rw [hr,List.cons.injEq] at he
        simp [← he.1,ho])
      have ht' : t ≤ c.start := by simpa [hr,hb,due] using ht
      cases hin : (ws i).inbox j with
      | nil =>
        refine ⟨cur i, ?_, ?_⟩
        · simpa [query,hp,hin,GraceExecution.after] using h
        · simpa [query,hp,hin] using ht
      | cons b bs =>
        have hlink := h.link j i
        rw [hin] at hlink
        obtain ⟨rfl,hlnew⟩ := LeonLocalTrace.head_in_ledger _ _ _ _ hlink
          (cert.receive _ _ _ hrow i j bits ho).2
        refine ⟨a, ?_, ?_⟩
        · simp only [query,hp,hin,GraceExecution.after]
          apply GraceReservations.replace h
          · exact hnext
          · simpa [CompOK,a,Cursor.shift,hb,usedCount,used,ho] using hco
          · intro _ _; rfl
          · intro k l
            have hkl := h.link k l
            by_cases hk : k = i <;> by_cases hl : l = i <;> by_cases hj : k = j <;> (try have hj' := Ne.symm hj) <;> subst_vars <;>
              first
              | simpa [Function.update_of_ne, *, a, Cursor.shift, posted, consumed, sends, receives] using hlnew
              | simpa [Function.update_of_ne, *, a, Cursor.shift, posted, consumed, sends, receives] using hkl
        · simpa [query,hp,hin,hb,a,Cursor.shift] using ht'.trans (hord.1.trans hord.2)

end LongTails.Proofs.GraceActions
