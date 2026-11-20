import LongTails.Proofs.MultirateDeliveries
import LongTails.Proofs.MultirateExecution

namespace LongTails.Proofs.MultirateCertificate

open DistributedTemplate
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Algorithms
open MultirateSchedule MultirateCalendar MultirateFrames MultirateLedger MultirateDeliveries
open LeonReservations (Frame posted consumed usedCount sends receives used)
open LocalReservations (Checked Suitable)
open LeonTranscript (Op)
open LeonExchangeReservations (sendFrame)

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)

noncomputable abbrev allRows := fun i => workerRows g s i (K p)

lemma reserved (i : Fin p.n) (u : ℕ) (ht : 0 < tick p) :
    let c := sampleFrame g s i u
    c.start + (batch p i : ℕ) * p.h i + transmission p ≤ c.delivery := by
  cases u with
  | zero =>
    simpa [sampleFrame,stamp,service] using (Finset.le_sup (f := service p) (Finset.mem_univ i))
  | succ u =>
    have hh := MultirateService.period_covers ht i
    change (if u + 1 = 0 then 0 else stamp p (anchor p i (u+1))) + (batch p i : ℕ) * p.h i +
      transmission p ≤ stamp p ((u+1) * (period p i : ℕ))
    simp only [Nat.succ_ne_zero,ite_false,anchor,Nat.add_sub_cancel,stamp,Nat.add_one_mul,Nat.cast_add,add_mul]
    change (batch p i : ℕ) * p.h i + transmission p ≤ _ at hh
    simp only [Nat.cast_zero,zero_mul,zero_add]
    simpa only [add_assoc] using add_le_add_right hh (Finset.univ.sup (service p) + (u * (period p i : ℕ) : ℕ) * tick p)

lemma job_checked (i : Fin p.n) (u : ℕ) (pre : List (Frame (network p))) (ht : 0 < tick p)
    (hc : Checked (allRows g s) i g s pre (sampleFrame g s i u).start)
    (hu : usedCount pre i = u * (batch p i : ℕ))
    (hs : ∀ j, ∀ v ∈ posted pre i j, v.1 ≤ (sampleFrame g s i u).start) :
    Checked (allRows g s) i g s (pre ++ job g s i u) (sampleFrame g s i u).finish := by
  let c := sampleFrame g s i u
  have hr := reserved g s i u ht
  dsimp only at hr
  change c.start + (batch p i : ℕ) * p.h i + transmission p ≤ c.delivery at hr
  have hlc : transmission p ≤ c.delivery := (le_add_of_nonneg_left zero_le).trans hr
  have ht₁ : c.start + (batch p i : ℕ) * p.h i ≤ c.finish :=
    (le_tsub_iff_right hlc).2 hr
  have horder : c.start ≤ c.finish := (le_add_of_nonneg_right zero_le).trans ht₁
  have hwire : c.finish + p.l + p.b * (LeonTranscript.wire (bits g s i u)).length ≤ c.delivery := by
    have hn : (LeonTranscript.wire (bits g s i u)).length = p.d * width p + clockBits := by
      simp [LeonTranscript.wire,bits,packet,DashaModular.encode_length]
    rw [hn,add_assoc]
    exact tsub_add_cancel_of_le hlc |>.le
  have hsample : Suitable (allRows g s) i g s pre c := by
    refine ⟨horder,?_,by simp [c,sampleFrame],by simp [c,sampleFrame]⟩
    intro q vals he
    obtain ⟨rfl,rfl⟩ := Op.sample.inj he
    exact ⟨ht₁,by simp [jobValues,MultirateTrajectory.values,hu]⟩
  have hbase := Checked.snoc hc hsample le_rfl
  have run (ids : List (Fin p.n)) (hn : ids.Nodup) (xs : List (Frame (network p)))
      (hx : Checked (allRows g s) i g s xs c.finish)
      (hprev : ∀ j ∈ ids, ∀ v ∈ posted xs i j, v.1 ≤ c.finish) :
      Checked (allRows g s) i g s (xs ++ posts g s i u ids) c.finish := by
    induction ids generalizing xs with
    | nil => simpa [posts] using hx
    | cons j js ih =>
      let row := sendFrame (p := network p) c.finish c.delivery (fun _ _ => bits g s i u) j
      obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp hn
      have hgood : Suitable (allRows g s) i g s xs row := by
        refine ⟨le_rfl,by simp [row,sendFrame],?_,by simp [row,sendFrame]⟩
        intro l bs he
        obtain ⟨rfl,rfl⟩ := Op.send.inj he
        exact ⟨hwire,hprev j (by simp)⟩
      have hnext := ih hnd (xs ++ [row]) (.snoc hx hgood le_rfl) (by
        intro l hl
        have hne : j ≠ l := by rintro rfl; exact hnot hl
        simpa [posted,row,sends,sendFrame,hne] using hprev l (List.mem_cons_of_mem _ hl))
      simpa [posts,row,c,List.append_assoc] using hnext
  have hrun := run (List.finRange p.n) (List.nodup_finRange _) (pre ++ [c]) hbase (by
    intro j _ v hv
    have hv' : v ∈ posted pre i j := by simpa [posted,sends,c,sampleFrame] using hv
    exact (hs j v hv').trans horder)
  simpa [job,List.append_assoc,c] using hrun

lemma receive_checked (i : Fin p.n) (k : ℕ) (hk : k < K p) (ht : 0 < tick p)
    (ids : List (Fin p.n)) (hn : ids.Nodup) (hd : ∀ j ∈ ids, j ∈ due p k)
    (xs : List (Frame (network p))) (hx : Checked (allRows g s) i g s xs (enter p i (k+1)))
    (hc : ∀ j ∈ ids, consumed xs j i = (List.range (countBefore p j k)).map (record g s j)) :
    Checked (allRows g s) i g s (xs ++ ids.map (recvFrame g s i k)) (enter p i (k+1)) := by
  induction ids generalizing xs with
  | nil => simpa using hx
  | cons j js ih =>
    let row := recvFrame g s i k j
    obtain ⟨hnot,hnd⟩ := List.nodup_cons.mp hn
    have hj : j ∈ j::js := by simp
    have hgood : Suitable (allRows g s) i g s xs row := by
      refine ⟨le_rfl,by simp [row,recvFrame],by simp [row,recvFrame],?_⟩
      intro l bs he
      obtain ⟨rfl,rfl⟩ := Op.receive.inj he
      rw [hc j hj]
      exact received_witness g s i j k hk (by simpa [due] using hd j hj) ht
    have hnext := ih hnd (fun l hl => hd l (List.mem_cons_of_mem _ hl)) (xs ++ [row]) (.snoc hx hgood le_rfl) (by
      intro l hl
      have hne : j ≠ l := by rintro rfl; exact hnot hl
      simpa [consumed,row,receives,recvFrame,hne] using hc l (List.mem_cons_of_mem _ hl))
    simpa [List.append_assoc,row] using hnext


lemma prefix_checked (i : Fin p.n) (ht : 0 < tick p) (k : ℕ) (hk : k ≤ K p) :
    Checked (allRows g s) i g s (workerRows g s i k) (enter p i k) := by
  induction k with
  | zero =>
    have h := job_checked g s i 0 [] ht (.nil _) (by simp [usedCount]) (by simp [posted])
    have he : (sampleFrame g s i 0).finish ≤ enter p i 0 := by
      simp [sampleFrame,enter,countBefore]
    simpa [workerRows] using h.later he
  | succ k ih =>
    let pre := workerRows g s i k
    have hk' : k < K p := by omega
    have prior := ih hk'.le
    have next : Checked (allRows g s) i g s (pre ++ requests g s i k) (enter p i (k+1)) := by
      by_cases hl : k % (period p i : ℕ) = 0 ∧ k + period p i < K p
      · let u := block p i k + 1
        have hd := due_mul (p := p) i k hl.1
        have hj := issued_launch (p := p) i k hl
        have hstart : (sampleFrame g s i u).start = stamp p k := by simp [sampleFrame,u,launch_anchor i k hl.1]
        have he : enter p i k = stamp p k := by simp [enter,before_eq i k,hl.1,hd,Nat.min_eq_right hk'.le]
        have hnext : enter p i (k+1) = stamp p (u * (period p i : ℕ)) := by
          simp only [enter,before_succ, Nat.add_one_mul, hd, Nat.min_eq_right hl.2.le,u]
        have hjob := job_checked g s i u pre ht (hstart.symm ▸ he ▸ prior)
          (by simpa only [pre,hj,u] using (counters g s i i k).1) (by
            intro j v hv
            rw [hstart]
            change v ∈ posted (workerRows g s i k) i j at hv
            rw [(counters g s i j k).2.1,hj] at hv
            obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
            have hw' : w ≤ block p i k := Nat.le_of_lt_succ (List.mem_range.mp hw)
            change stamp p (w * (period p i : ℕ)) ≤ stamp p k
            apply stamp_mono
            exact (Nat.mul_le_mul_right _ hw').trans_eq hd)
        rw [requests,ite_eq_left hl,hnext]
        exact hjob.later tsub_le_self
      · have hle : enter p i k ≤ enter p i (k+1) := by
          apply stamp_mono
          exact min_le_min_left _ (Nat.mul_le_mul_right _ (before_mono i (Nat.le_succ _)))
        simpa [requests,hl,pre] using prior.later hle
    have hreceives := receive_checked g s i k hk' ht (due p k) (due_nodup k)
      (fun _ h => h) _ next (by
        intro j _
        have he : consumed (requests g s i k) j i = [] := by
          unfold requests
          split_ifs
          · exact (job_effect g s i j _).2.2
          · rfl
        change consumed (pre ++ requests g s i k) j i = _
        rw [show consumed (pre ++ requests g s i k) j i =
          consumed pre j i ++ consumed (requests g s i k) j i from List.flatMap_append,he,List.append_nil]
        exact (counters g s i j k).2.2)
    simpa [prefix_succ,cycle,List.append_assoc,pre] using hreceives

lemma execute_positive (P : MeasureTheory.ProbabilityMeasure (Samples p)) (T : Time)
    (hT : stamp p (K p) ≤ T) (ab : Fin (K p) × Fin (K p)) (hL : 0 < smoothness p)
    (ht : 0 < tick p) :
    DistributedTemplate.execute (Setups.BandwidthHeterogeneousSmoothNonconvex.system (network p) g P)
      (algorithm p T) T ab s = output p (MultirateTrajectory.modelAt g s (K p)) ab := by
  apply MultirateExecution.execute (rows := allRows g s)
  · apply LocalReservations.certificate
    intro i
    apply (prefix_checked g s i ht (K p) le_rfl).later
    exact (stamp_mono (min_le_left _ _)).trans hT
  · intro i
    exact full_trace g s i ab hL.ne'

lemma execute_zero (P : MeasureTheory.ProbabilityMeasure (Samples p)) (T : Time)
    (ab : Fin (K p) × Fin (K p)) (hL : smoothness p = 0) :
    DistributedTemplate.execute (Setups.BandwidthHeterogeneousSmoothNonconvex.system (network p) g P)
      (algorithm p T) T ab s = p.x0 := by
  apply MultirateExecution.execute (rows := fun _ => [])
  · exact LocalReservations.certificate (fun _ => Checked.nil T)
  · intro i
    change LeonTranscript.Trace (initialProgram p i ab.1 ab.2) [] p.x0
    rw [initialProgram,ite_eq_left hL]
    exact .done _

end LongTails.Proofs.MultirateCertificate
