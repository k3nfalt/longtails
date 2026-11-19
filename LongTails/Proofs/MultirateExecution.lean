import LongTails.Proofs.MultirateRank
import LongTails.Proofs.MultirateReplay
import LongTails.Proofs.MultirateSchedule

open MeasureTheory

namespace LongTails.Proofs.MultirateExecution

open DistributedTemplate LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateProtocol LongTails.Algorithms.MultirateTrajectory LongTails.Algorithms.MultirateCalendar
open MultirateReservations MultirateMachine MultirateEvents MultirateInteraction MultirateProgress MultirateRank

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {P : ProbabilityMeasure (Samples p)}
    {s : Samples p} {D u : Time} {x : Config p} {n : ℕ} {out : Point p}

noncomputable abbrev events (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (s : Samples p) (D : Time) (x : Config p) :=
  event (systemOf g P) (algorithm p D) (image g P s D x)

noncomputable def potential (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (s : Samples p) (D : Time) (x : Config p) (n : ℕ) : ℕ := by
  classical
  exact 2 * rank D x n + if x.now < x.deadline ∧ events g P s D x x.now = none then 1 else 0

def Stop (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (D : Time) (out : Point p) (c : ExecutionState (systemOf g P) (algorithm p D)) : Prop :=
  ∃ k, let z := run (systemOf g P) (algorithm p D) k c
       step (systemOf g P) (algorithm p D) z = none ∧ (c.deadline = D → (algorithm p D).output (z.workers 0) = out)

lemma prepend {c d : ExecutionState (systemOf g P) (algorithm p D)} (h : step _ _ c = some d)
    (hs : Stop g P D out d) : Stop g P D out c := by
  obtain ⟨k,hk,ho⟩ := hs
  refine ⟨k+1,?_,?_⟩
  · simpa only [run,h] using hk
  · intro ht
    simpa only [run,h] using ho ((DistributedExecution.step_deadline _ _ c d h).trans ht)

lemma shift (h : Valid g s out D x n u) (hn : x.now < x.deadline) (he : events g P s D x x.now = none) :
    let O := systemOf g P
    let A := algorithm p D
    let t := nextTime (events g P s D x) x.now x.deadline
    let y := {x with now := t}
    step O A (image g P s D x) = some (image g P s D y) ∧ Valid g s out D y n u ∧
      potential g P s D y n < potential g P s D x n := by
  let O := systemOf g P
  let A := algorithm p D
  let t := nextTime (events g P s D x) x.now x.deadline
  let y := {x with now := t}
  have hex := DistributedExecution.star_nextTime_exists (network p) (evalAt g) P A (image g P s D x) h.time
  have hs := (DistributedExecution.nextTime_spec (events g P s D x) x.now x.deadline hex).1
  have h1 : x.now ≤ t := hs.1
  have h2 : t ≤ x.deadline := hs.2.1
  have hsafe (i : Fin p.n) : Safe y i := by
    refine ⟨(h.safe i).1, ?_⟩
    intro z hz
    have hz' := (h.safe i).2 z hz
    exact DistributedExecution.nextTime_le_ready _ _ _ _ hex hz' (leaf_ready h.responsive i hz hz')
  have hnow (j : 0 < n) : t ≤ u := by
    obtain ⟨z,hz,hzu,hr⟩ := timely_event (P := P) h j
    exact (DistributedExecution.nextTime_le_ready _ _ _ _ hex hz hr).trans hzu
  have hyEvent (z) : events g P s D y z = events g P s D x z := rfl
  refine ⟨?_,⟨h.cert,h2,h.deadline,hnow,hsafe,⟨fun hr => (h.responsive.1 hr).trans h1,
    fun i hr => (h.responsive.2 i hr).trans h1⟩⟩,?_⟩
  · change step O A (image g P s D x) = some (image g P s D y)
    have hnone : event O A (image g P s D x) x.now = none := he
    simp only [step, show (image g P s D x).time = x.now from rfl,
      show (image g P s D x).deadline = x.deadline from rfl, ite_eq_right (not_lt.mpr h.time),
      hnone,ite_eq_right hn.ne]
    rfl
  · change potential g P s D y n < potential g P s D x n
    have hf : ¬(y.now < y.deadline ∧ events g P s D y y.now = none) := by
      rintro ⟨hl,hm⟩
      rcases hs.2.2 with hd | hr
      · exact hl.ne hd
      · rw [hyEvent] at hm
        change (events g P s D x y.now).isSome at hr
        simp [hm] at hr
    simp only [potential,ite_eq_right hf,ite_eq_left (And.intro hn he),Nat.add_zero]
    change 2 * rank D x n < 2 * rank D x n + 1
    omega

lemma completion (h : Valid g s out D x n u) : Stop g P D out (image g P s D x) := by
  classical
  induction hv : potential g P s D x n using Nat.strong_induction_on generalizing x n u with
  | h k ih =>
    cases he : events g P s D x x.now with
    | some ev =>
      obtain ⟨⟨v,e⟩,os⟩ := ev
      obtain ⟨y,hm⟩ := choose h (observed g P s D x v e os he)
      obtain ⟨m,t,hy,hr⟩ := preserved hm h
      have hp : potential g P s D y m < potential g P s D x n := by
        simp only [potential]
        split_ifs <;> omega
      exact prepend (MultirateReplay.replay hm h.time h.deadline he) (ih _ (hp.trans_eq hv) hy rfl)
    | none =>
      rcases h.time.eq_or_lt with ht | ht
      · have hterm : step (systemOf g P) (algorithm p D) (image g P s D x) = none :=
          (DistributedExecution.step_terminal_iff _ _ _ h.time).mpr ⟨ht,he⟩
        refine ⟨0,hterm,?_⟩
        intro hD
        change x.deadline = D at hD
        have hz : n = 0 := by
          by_contra! hn
          obtain ⟨t,ht₁,ht₂,het⟩ := timely_event (P := P) h (Nat.pos_of_ne_zero hn)
          have htx : t = x.now := le_antisymm ((ht₂.trans (certified_limit h.cert)).trans_eq (ht.trans hD).symm) ht₁
          rw [htx] at het
          change (events g P s D x x.now).isSome at het
          rw [he] at het
          cases het
        have hc := h.cert
        rw [hz] at hc
        generalize hp : x.program = z at hc
        cases hc
        change (match (workersOf g s x.table x.program 0).program with | .done z => z | _ => p.x0) = out
        change (match x.program with | .done z => z | _ => p.x0) = out
        rw [hp]
      · obtain ⟨hs,hy,hr⟩ := shift h ht he
        exact prepend hs (ih _ (hr.trans_eq hv) hy rfl)

noncomputable def initialConfig (p : Params) (a b : ℕ) (T : Time) : Config p :=
  ⟨0,T,fun _ => .free 0,start p a b,fun _ => 0,0⟩

lemma extend_cert {prog : Program p} {book : Book p} {T : Time} (hc : Certified g s out T n prog book u)
    (h : T ≤ D) : Certified g s out D n prog book u := by
  induction hc with
  | done b t ht => exact .done _ _ (ht.trans h)
  | post hf hb ht _ ih => exact .post hf hb ht ih
  | collect hj hu ht _ ih => exact .collect hj hu ht ih

lemma initial_eq (g : Fin p.n → Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p))
    (D T : Time) (ab : Fin (steps p) × Fin (steps p)) (s : Samples p) :
    DistributedTemplate.initial (systemOf g P) (algorithm p D) T (ab,s) =
      image g P s D (initialConfig p ab.1 ab.2 T) := by
  have hw : (fun v => (algorithm p D).initial v ab) =
      workersOf g s (fun _ => .free 0) (start p ab.1 ab.2) := by
    funext v
    refine Fin.cases ?_ (fun i => ?_) v
    · simp [algorithm,workersOf]; rfl
    · simp [algorithm,workersOf,phaseOf]
  have ho : (systemOf g P).initial s = oracleOf g P s (fun _ => .free 0) := by
    apply MultirateReplay.oracle_ext
    · funext v
      refine Fin.cases rfl (fun i => ?_) v
      change _ = computationOf s i (.free 0)
      simp [computationOf, Oracle.initial,systemOf,Setups.DistributedAggregateSmoothNonconvex.system,
        Setups.StarNetwork.system,Setups.StarNetwork.computation]
    · funext v w
      refine Fin.cases ?_ (fun i => ?_) v <;> refine Fin.cases rfl (fun _ => rfl) w
  unfold DistributedTemplate.initial image initialConfig
  congr 1

lemma terminates (hh : ∀ i, 0 < p.h i) (hL : ∀ i, 0 ≤ p.L i) (hD : finishTime p ≤ D)
    (T : Time) (hT : T ≤ D) (ab : Fin (steps p) × Fin (steps p)) (s : Samples p) :
    Stop g P D (output p (trajectory p g s (steps p)) ab.1 ab.2)
      (DistributedTemplate.initial (systemOf g P) (algorithm p D) T (ab,s)) := by
  rw [initial_eq]
  obtain ⟨n,u,hu,hc⟩ := MultirateSchedule.start_can (g := g) (s := s) hh hL ab.1 ab.2
  apply completion (u := u) (n := n)
  refine ⟨extend_cert hc hD,zero_le,hT,fun _ => hu,?_,⟨fun _ => le_rfl,fun _ _ => le_rfl⟩⟩
  intro i
  exact ⟨trivial,fun _ h => nomatch h⟩

end LongTails.Proofs.MultirateExecution
