import LongTails.Proofs.DistributedJacobianStrongGrowthWorker
import LongTails.Proofs.DistributedJacobianStrongGrowthPayloadAggregation

namespace LongTails.Proofs.DistributedJacobianStrongGrowthWorkerReference

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientWorker
open LongTails.Algorithms.LocalNonlinearExtragradient

noncomputable def extraWork (p : Params) (T : ℕ) (g : Point p → p.Ω → Point p)
    (x : Point p) (samples : ℕ → p.Ω) (used : ℕ) : Work p :=
  let current := run (1 / (4 * p.L)) g x samples (used / 2)
  if used % 2 = 0 then .first (T - used / 2) current
  else .second (T - used / 2) current (current - (1 / (4 * p.L)) • g current (samples (2 * (used / 2))))

lemma extraWork_initial (p : Params) (T : ℕ) (g : Point p → p.Ω → Point p)
    (x : Point p) (samples : ℕ → p.Ω) : extraWork p T g x samples 0 = .first T x := by
  simp [extraWork, run]

lemma extraWork_final (p : Params) (T : ℕ) (g : Point p → p.Ω → Point p)
    (x : Point p) (samples : ℕ → p.Ω) :
    extraWork p T g x samples (2 * T) = .first 0 (run (1 / (4 * p.L)) g x samples T) := by
  simp [extraWork]

lemma extraWork_remaining (p : Params) (T : ℕ) (g : Point p → p.Ω → Point p)
    (x : Point p) (samples : ℕ → p.Ω) (used : ℕ) (hu : used ≤ 2 * T) :
    remainingQueries (extraWork p T g x samples used) = 2 * T - used := by
  unfold extraWork
  split_ifs <;> simp only [remainingQueries] <;> omega

lemma extraWork_query (p : Params) (T : ℕ) (g : Point p → p.Ω → Point p)
    (x : Point p) (samples : ℕ → p.Ω) (used : ℕ) (hu : used < 2 * T) :
    ∃ point, query (extraWork p T g x samples used) = some point := by
  cases hq : query (extraWork p T g x samples used) with
  | some point => exact ⟨point, rfl⟩
  | none =>
      have hh := (DistributedJacobianStrongGrowthWorker.query_none_iff p _).mp hq
      rw [extraWork_remaining p T g x samples used hu.le] at hh
      omega

lemma extraWork_reply (p : Params) (T : ℕ) (g : Point p → p.Ω → Point p)
    (x : Point p) (samples : ℕ → p.Ω) (used : ℕ) (hu : used < 2 * T) (point : Point p)
    (hq : query (extraWork p T g x samples used) = some point) :
    reply p (extraWork p T g x samples used) (g point (samples used)) =
      extraWork p T g x samples (used + 1) := by
  obtain ⟨r, hrem⟩ : ∃ r, T - used / 2 = r + 1 := ⟨T - used / 2 - 1, by omega⟩
  have hnext : T - (used / 2 + 1) = r := by omega
  by_cases he : used % 2 = 0
  · have hdiv : (used + 1) / 2 = used / 2 := by omega
    have hmod : (used + 1) % 2 ≠ 0 := by omega
    have hu' : used = 2 * (used / 2) := by omega
    have hx : point = run (1 / (4 * p.L)) g x samples (used / 2) := by
      simpa [extraWork, he, hrem, query] using hq.symm
    simp [extraWork, he, hdiv, hmod, hrem, reply, hx, ← hu']
  · have hdiv : (used + 1) / 2 = used / 2 + 1 := by omega
    have hmod : (used + 1) % 2 = 0 := by omega
    have hu' : used = 2 * (used / 2) + 1 := by omega
    have hx : point = run (1 / (4 * p.L)) g x samples (used / 2) -
        (1 / (4 * p.L)) • g (run (1 / (4 * p.L)) g x samples (used / 2)) (samples (2 * (used / 2))) := by
      simpa [extraWork, he, hrem, query] using hq.symm
    simp [extraWork, he, hdiv, hmod, hrem, reply, hx, run, step, ← hu', hnext]

end LongTails.Proofs.DistributedJacobianStrongGrowthWorkerReference
