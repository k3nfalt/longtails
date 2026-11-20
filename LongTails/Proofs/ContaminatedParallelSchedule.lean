import LongTails.Proofs.ContaminatedParallelExecution
import LongTails.Proofs.ContaminatedParallelTrajectory
import LongTails.Proofs.LeonConfiguredSchedule

namespace LongTails.Proofs.ContaminatedParallelSchedule

open DistributedTemplate MeasureTheory
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms
open LeonReservations LeonScheduleCertificate LeonExchangeReservations LeonTranscript
open LeonRoundReservations (Settled settled_phase)
open ContaminatedParallelTrajectory

noncomputable def computeTime (p : Params) (op : Operation) : Time :=
  Finset.univ.sup (fun i => (batch p (op.precision p) i : ℕ) * p.h i)

noncomputable def linkTime (p : Params) (l : ℕ) : Time :=
  p.l + p.b * (64 + LeonTuning.blockSize (network p) * LeonTuning.width (network p) l : ℕ)

noncomputable def cost (p : Params) (op : Operation) : Time :=
  computeTime p op + 2 * linkTime p op.level

variable {p : Params}

noncomputable def computeFrame (t : Time) (r : Round p) : Frame (network p) :=
  ⟨fun i => .sample (location p r.model r.op, batch p (r.op.precision p) i) (r.values i),
    t, t + computeTime p r.op, 0⟩

noncomputable def frames (t : Time) (r : Round p) : List (Frame (network p)) :=
  let b := t + computeTime p r.op
  let z := linkTime p r.op.level
  computeFrame t r :: (phase b (b+z) (scatter r) ++ phase (b+z) (b+z+z) (fun i _ => gather r i))

lemma frame_actions (t : Time) (r : Round p) (i : Fin p.n) :
    (frames t r).map (fun c => c.op i) = actions r i := by
  simp [frames,actions,computeFrame,phase,sendFrame,recvFrame,exchangeOps,List.append_assoc,
    Function.comp_def]

lemma extend (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (r : Round p)
    (t : Time) (pre : List (Frame (network p))) (hc : Checked g s pre t)
    (hf : Settled (network p) pre t) (hr : ∀ i, r.values i = (List.range (batch p (r.op.precision p) i)).map
      (fun k => g i (location p r.model r.op) (s i (usedCount pre i + k)))) :
    Checked g s (pre ++ frames t r) (t + cost p r.op) ∧
    Settled (network p) (pre ++ frames t r) (t + cost p r.op) ∧
    ∀ i, usedCount (pre ++ frames t r) i = nextOffset p (usedCount pre) r.op i := by
  let b := t + computeTime p r.op
  let z := linkTime p r.op.level
  have htb : t ≤ b := le_self_add
  have hbg : b ≤ b+z := le_self_add
  have hge : b+z ≤ b+z+z := le_self_add
  let xs := pre ++ [computeFrame t r]
  have hgood : Suitable g s pre (computeFrame t r) := by
    refine ⟨htb, ?_, by simp [computeFrame], by simp [computeFrame]⟩
    intro i q vals he
    obtain ⟨rfl,rfl⟩ := Op.sample.inj he
    exact ⟨add_le_add_right (Finset.le_sup (f := fun j => (batch p (r.op.precision p) j : ℕ) * p.h j)
      (Finset.mem_univ i)) t, hr i⟩
  have hx : Checked g s xs b := .snoc hc hgood le_rfl
  have hfx : Settled (network p) xs b := by
    constructor
    · intro i j; simpa [xs,posted,consumed,sends,receives,computeFrame] using hf.match_link i j
    · intro i j m hm; exact (hf.paid i j m (by simpa [xs,posted,sends,computeFrame] using hm)).trans htb
  have hs (i j : Fin p.n) : p.l + p.b * (wire (scatter r i j)).length = z := by
    simp [z,linkTime,wire,scatter,LeonExchange.scatter_length,clockBits,Nat.add_comm]
  have hg (i : Fin p.n) : p.l + p.b * (wire (gather r i)).length = z := by
    simp [z,linkTime,wire,gather,LeonExchange.gather_length,clockBits,Nat.add_comm]
  have hphase := phase_checked b (b+z) (scatter r) xs hx (fun i j => by
    rw [add_assoc]; exact le_of_eq (congrArg (b + ·) (hs i j))) hbg hfx.paid hfx.match_link
  have hm := settled_phase hfx hbg (scatter r)
  have hlast := phase_checked (b+z) (b+z+z) (fun i _ => gather r i) _ hphase (fun i _ => by
    rw [add_assoc]; exact le_of_eq (congrArg ((b+z) + ·) (hg i))) hge hm.paid hm.match_link
  have he := settled_phase hm hge (fun i _ => gather r i)
  have hlist : pre ++ frames t r = (xs ++ phase b (b+z) (scatter r)) ++
      phase (b+z) (b+z+z) (fun i _ => gather r i) := by simp [xs,frames,b,z,List.append_assoc]
  have ht : t + cost p r.op = b+z+z := by dsimp [cost,b,z]; ring
  rw [hlist,ht]
  refine ⟨hlast,he,fun i => ?_⟩
  have hu (as bs : List (Frame (network p))) : usedCount (as++bs) i = usedCount as i + usedCount bs i := by
    simp [usedCount]
  rw [hu,hu,(phase_effect _ _ _ i i).2.2,(phase_effect _ _ _ i i).2.2]
  simp [xs,usedCount,used,computeFrame,nextOffset]

lemma transcript (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (ls : List Operation)
    (m : Model p) (t : Time) (pre : List (Frame (network p))) (hc : Checked g s pre t)
    (hf : Settled (network p) pre t) :
    ∃ rows, Checked g s (pre ++ rows) (t + (ls.map (cost p)).sum) ∧
      ∀ i, Trace (schedule p i ls m) (rows.map (fun c => c.op i))
        (output p (trajectory p g s ls (usedCount pre) m)) := by
  induction ls generalizing m t pre with
  | nil => exact ⟨[], by simpa using hc, fun _ => Trace.done _⟩
  | cons op ls ih =>
    let r := read p g s (usedCount pre) m op
    obtain ⟨h1,h2,hused⟩ := extend g s r t pre hc hf (fun _ => rfl)
    obtain ⟨rows,hc',htr⟩ := ih (advance p m op (decoded r)) _ _ h1 h2
    refine ⟨frames t r ++ rows, ?_, fun i => ?_⟩
    · simpa [List.append_assoc, add_assoc, r, ContaminatedParallelTrajectory.read] using hc'
    · rw [List.map_append, frame_actions]
      apply round_trace r i ls
      have he : usedCount (pre ++ frames t r) = nextOffset p (usedCount pre) op := funext hused
      rw [he] at htr
      exact htr i

lemma execute_output (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (P : ProbabilityMeasure (Samples p)) (T : Time) (seed : (algorithm p T).Seed) (s : Samples p)
    (ht : ((operations p seed).map (cost p)).sum ≤ T) :
    execute (LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex.system (network p) g P)
      (algorithm p T) T seed s = output p (trajectory p g s (operations p seed) (fun _ => 0) (initialModel p)) := by
  obtain ⟨rows,hcheck,htrace⟩ := transcript g s (operations p seed) (initialModel p) 0 []
    (.nil 0) ⟨fun _ _ => rfl,by simp [posted]⟩
  simp only [List.nil_append,zero_add] at hcheck
  exact ContaminatedParallelExecution.execute_certified p g P T s ((hcheck.later ht).certificate) seed htrace

end LongTails.Proofs.ContaminatedParallelSchedule
