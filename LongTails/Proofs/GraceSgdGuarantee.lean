import LongTails.Proofs.GraceConfiguredSchedule

namespace LongTails.Proofs.GraceSgdGuarantee

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory DistributedTemplate
open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms
open GraceRouting GraceSgd GraceBatch
open GraceRoundSchedule (localPoint)
open GraceSampleSchedule (time)
open GraceConfiguredSchedule (X plan)
open GraceSgdTrajectory (familyTuning)
open LeonReservations (usedCount)
open LeonTranscript (Trace)

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n} (A : Routes p S r)
    (hS : S.Nonempty) (hr : r ∈ S) (hh : ∀ i, 0 < p.h i)
    (hs : ∀ i j, p.G.Adj i j → p.b i j = p.b j i)
    (limit : Time) (hlim : (((tuning p S).iterations : ℕ) - 1 : ℕ) * time A ≤ limit)
    (g : Point p → p.Ω → Point p) (P : ProbabilityMeasure (Samples p)) (s : Samples p)
    (j : (algorithm A limit).Seed)

include hS hh hs hlim in
lemma certificate : GraceReservations.Certified g s limit (plan A g s 0 j.val) := by
  have hb := (GraceConfiguredSchedule.certified A hS hh hs g s 0 j.val).toCertified
  have hb' : GraceReservations.Certified g s (j.val * time A) (plan A g s 0 j.val) := by
    have he : GraceScheduleBlocks.shift s (fun i => 0 * batches p S i) = s := by
      funext i k; simp [GraceScheduleBlocks.shift]
    simpa only [he,Nat.zero_add] using hb
  exact GraceScheduledExecution.enlarge hb' ((mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (show j.val ≤ ((tuning p S).iterations : ℕ) - 1 by have h := j.isLt; omega)) zero_le).trans hlim)

include hS hr hh in
lemma initial_trace (i : Fin p.n) : Trace ((algorithm A limit).initial i j).program
    ((plan A g s 0 j.val).map fun c => c.op i) (localPoint S (X S g s j.val) i) := by
  have hn := GraceConfiguredSchedule.trace A hS hr hh g s 0 j.val i
  have h0 : localPoint S (X S g s 0) i = p.x₀ := by simp [localPoint,X,DistributedBatchedSgd.trajectory]
  simpa only [algorithm,h0,Nat.zero_add] using hn

include hS hr hh hs hlim in
lemma actual_output : execute (system p g P) (algorithm A limit) limit j s = X S g s j.val := by
  have h := GraceScheduledExecution.execute (P := P) (certificate A hS hh hs limit hlim g s j) j
    (initial_trace A hS hr hh limit g s j)
  simpa [localPoint,hr] using h

include hS hr hh hs hlim in
lemma family (hL : 0 < p.L) (hε : 0 < p.ε) : IsQuantizedMinibatchSgd p (algorithm A limit) := by
  let cfg := familyTuning hS hh hL hε
  refine ⟨cfg,id,limit,measurable_id,Measure.map_id,?_⟩
  intro g P j s
  let O := system p g P
  let alg := algorithm A limit
  let rows := plan A g s 0 j.val
  let out := fun i => localPoint S (X S g s j.val) i
  have hroot : out r = X S g s j.val := by simp [out,localPoint,hr]
  have hrow := certificate A hS hh hs limit hlim g s j
  have tr := initial_trace A hS hr hh limit g s j
  have it (l : ℕ) : cfg.iterate g s l = X S g s l := GraceSgdTrajectory.family_iterate hS hh hL hε g s l
  constructor
  · intro T k
    let c := run O alg k (initial O alg T (j,s))
    obtain ⟨cur,hv⟩ := GraceScheduledExecution.run_valid (P := P)
      (GraceScheduledExecution.enlarge hrow (le_max_left limit T)) j tr T (le_max_right limit T) k
    constructor
    · have ho : Trace (c.workers r).program ((cur r).rest.map fun f => f.op r) (out r) := hv.trace r
      change (match (c.workers r).program with | .finish y => y | _ => p.x₀) = p.x₀ ∨
        (match (c.workers r).program with | .finish y => y | _ => p.x₀) = cfg.iterate g s j.val
      rw [it]
      cases he : (c.workers r).program with
      | finish y =>
        rw [he] at ho
        have done {z w : Point p} {ops} (h : Trace (.finish z : LeonProtocol.Program p.base) ops w) : z = w := by cases h; rfl
        exact Or.inr ((done ho).trans hroot)
      | sample => exact Or.inl rfl
      | send => exact Or.inl rfl
      | receive => exact Or.inl rfl
    · intro i
      have hc : LeonReservations.CompOK p.base s i (cur i).past (cur i).rest
          (c.workers i) (c.oracle.computation i) := hv.compute i
      obtain ⟨_,hu,hpend⟩ := hc
      have hall := GraceConfiguredSchedule.counts A g s 0 j.val i
      rw [(cur i).layout,GraceScheduleBlocks.used_append] at hall
      refine ⟨hu.le.trans ((Nat.le_add_right _ _).trans_eq hall),?_⟩
      intro entry he
      change entry ∈ (c.oracle.computation i).pending at he
      cases hb : (c.workers i).busy <;> simp only [hb,Bool.false_eq_true,↓reduceIte] at hpend
      · simp [hpend] at he
      · obtain ⟨f,rest,q,vals,t,hf,ho,hp,_⟩ := hpend
        have eq : entry = (t,q) := by simpa [hp,eq_comm] using he
        subst entry
        obtain ⟨l,hl,hused,hx,hb⟩ := GraceConfiguredSchedule.sample_position A hS hh g s 0 j.val
          (cur i).past f rest (by rw [← hf]; exact (cur i).layout) i q vals ho
        refine ⟨l,hl,hu.trans hused,?_,hb⟩
        simpa [it] using hx
  · obtain ⟨k,hk⟩ := GraceExecution.finite A g P limit j s limit le_rfl
    let init := initial O alg limit (j,s)
    let c := run O alg k init
    obtain ⟨cur,hv⟩ := GraceScheduledExecution.run_valid (P := P) hrow j tr limit le_rfl k
    have hall := GraceScheduledExecution.finished hrow c (DistributedExecution.run_deadline O alg init k)
      (DistributedExecution.run_time_le_deadline O alg init k zero_le) cur hv hk
    refine ⟨k,hk,?_,?_⟩
    · have h := hv.trace r
      rw [hall,List.map_nil] at h
      have he : (c.workers r).program = .finish (out r) := LeonLocalTrace.done h
      change (match (c.workers r).program with | .finish y => y | _ => p.x₀) = cfg.iterate g s j.val
      rw [he,hroot,it]
    · intro i
      have he := (cur i).layout
      rw [hall,List.append_nil] at he
      exact (hv.compute i).2.1.trans ((congrArg (fun xs => usedCount xs i) he.symm).trans
        (GraceConfiguredSchedule.counts A g s 0 j.val i))

end LongTails.Proofs.GraceSgdGuarantee
