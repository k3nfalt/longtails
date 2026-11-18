import LongTails.Proofs.DistributedJacobianStrongGrowthWorker
import LongTails.Proofs.DistributedJacobianStrongGrowthProtocol

namespace LongTails.Proofs.DistributedJacobianStrongGrowthFallbackState

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.LocalNonlinearExtragradient

def RootReference (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (s : State p) (used : ℕ) : Prop :=
  (s.phase = .baseline ∧ used ≤ baselineCount p ∧ s.work = some (.warm (baselineCount p - used)
    (warmRun (p.μ / (p.ρ * p.L ^ 2)) (g p.root) p.x0 (fun k => samples (p.n * k + p.root.val)) used))) ∨
  (s.phase = .done ∧ s.work = none ∧ s.busy = false ∧ s.current = baselineOutput p g samples)

def FallbackState (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (v : Fin p.n) (s : State p) (used : ℕ) : Prop :=
  s.queue = [] ∧ s.ready = false ∧ s.sent = false ∧
    (if v = p.root then RootReference p g samples s used
     else s.phase = .done ∧ s.work = none ∧ s.busy = false ∧ s.current = p.x0)

lemma fallbackState_initial (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (v : Fin p.n) (hε : p.ε < p.R)
    (hrich : ¬ 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    FallbackState p g samples v (initialState p v) 0 := by
  by_cases hv : v = p.root
  · subst v
    simp [FallbackState, RootReference, initialState, not_le.mpr hε, hrich, warmRun]
  · simp [FallbackState, initialState, not_le.mpr hε, hrich, hv]

lemma fallbackState_work (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (v : Fin p.n) (s : State p) (used : ℕ)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (h : FallbackState p g samples v s used) (hw : s.work = some work) :
    v = p.root ∧ s.phase = .baseline ∧ used ≤ baselineCount p ∧
      work = .warm (baselineCount p - used)
        (warmRun (p.μ / (p.ρ * p.L ^ 2)) (g p.root) p.x0 (fun k => samples (p.n * k + p.root.val)) used) := by
  by_cases hv : v = p.root
  · have hr : RootReference p g samples s used := by simpa only [ite_eq_left hv] using h.2.2.2
    rcases hr with hr | hr
    · exact ⟨hv, hr.1, hr.2.1, Option.some.inj (hw.symm.trans hr.2.2)⟩
    · rw [hr.2.1] at hw
      cases hw
  · have hh : s.phase = .done ∧ s.work = none ∧ s.busy = false ∧ s.current = p.x0 := by
      simpa only [ite_eq_right hv] using h.2.2.2
    rw [hh.2.1] at hw
    cases hw

lemma fallbackState_busy (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (v : Fin p.n) (s : State p) (used : ℕ)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (h : FallbackState p g samples v s used) (hw : s.work = some work) :
    FallbackState p g samples v { s with busy := true } used := by
  obtain ⟨hv, hs, hu, hwork⟩ := fallbackState_work p g samples v s used work h hw
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rw [ite_eq_left hv]
  exact Or.inl ⟨hs, hu, hw.trans (congrArg some hwork)⟩

lemma fallbackState_finish (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (v : Fin p.n) (s : State p) (used : ℕ)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (h : FallbackState p g samples v s used) (hw : s.work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = none) :
    FallbackState p g samples v
      (finishLocal p s (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work)) used := by
  obtain ⟨hv, hs, hu, hwork⟩ := fallbackState_work p g samples v s used work h hw
  subst work
  have hz := (DistributedJacobianStrongGrowthWorker.query_none_iff p _).mp hq
  simp only [LongTails.Algorithms.DistributedLocalExtragradientWorker.remainingQueries] at hz
  have he : used = baselineCount p := by omega
  subst used
  simp [FallbackState, RootReference, finishLocal, hs, hv, h.1, h.2.2.1,
    LongTails.Algorithms.DistributedLocalExtragradientWorker.point, baselineOutput]

lemma fallbackState_query (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (v : Fin p.n) (s : State p) (used : ℕ)
    (h : FallbackState p g samples v s used) :
    FallbackState p g samples v (query p v s).2 used := by
  cases hw : s.work with
  | none => simpa [query, h.1, hw, h.2.1] using h
  | some work =>
      cases hb : s.busy with
      | true => simpa [query, h.1, hw, hb] using h
      | false =>
          cases hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
          | none => simpa [query, h.1, hw, hb, hq] using fallbackState_finish p g samples v s used work h hw hq
          | some point => simpa [query, h.1, hw, hb, hq] using fallbackState_busy p g samples v s used work h hw

lemma fallbackState_no_send (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (v : Fin p.n) (s : State p) (used : ℕ)
    (h : FallbackState p g samples v s used) (packet : Fin p.n × List Bool) :
    (query p v s).1 ≠ .communicate packet := by
  cases hw : s.work with
  | none => simp [query, h.1, hw, h.2.1]
  | some work =>
      cases hb : s.busy with
      | true => simp [query, h.1, hw, hb]
      | false =>
          cases hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work <;>
            simp [query, h.1, hw, hb, hq]

lemma fallbackState_reply (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) (v : Fin p.n) (s : State p) (used : ℕ)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (point value : Point p) (h : FallbackState p g samples v s used) (hw : s.work = some work)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some point)
    (hvalue : value = g v point (samples (p.n * used + v.val))) :
    FallbackState p g samples v { s with work := some (LongTails.Algorithms.DistributedLocalExtragradientWorker.reply p work value), busy := false } (used + 1) := by
  obtain ⟨hv, hs, hu, hwork⟩ := fallbackState_work p g samples v s used work h hw
  subst v
  subst work
  have hlt : used < baselineCount p := by
    by_contra hn
    have he : used = baselineCount p := by omega
    simp [he, LongTails.Algorithms.DistributedLocalExtragradientWorker.query] at hq
  have hrem : baselineCount p - used = (baselineCount p - (used + 1)) + 1 := by omega
  have hpoint : point = warmRun (p.μ / (p.ρ * p.L ^ 2)) (g p.root) p.x0
      (fun k => samples (p.n * k + p.root.val)) used := by
    simpa only [hrem, LongTails.Algorithms.DistributedLocalExtragradientWorker.query, Option.some.injEq] using hq.symm
  have hreply := DistributedJacobianStrongGrowthWorker.warm_reply_run p (baselineCount p) used hlt
    (g p.root) p.x0 (fun k => samples (p.n * k + p.root.val))
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  rw [ite_eq_left rfl]
  left
  refine ⟨hs, by omega, ?_⟩
  rw [hvalue, hpoint]
  exact congrArg some hreply

end LongTails.Proofs.DistributedJacobianStrongGrowthFallbackState
