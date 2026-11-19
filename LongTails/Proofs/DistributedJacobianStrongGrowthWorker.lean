import LongTails.Algorithms.DistributedLocalExtragradientWorker
import Mathlib.Tactic

namespace LongTails.Proofs.DistributedJacobianStrongGrowthWorker

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientWorker

lemma query_none_iff (p : Params) (state : Work p) :
    query state = none ↔ remainingQueries state = 0 := by
  cases state with
  | warm k x => cases k <;> simp [query, remainingQueries]
  | first k x => cases k <;> simp [query, remainingQueries]
  | second k x y => cases k <;> simp [query, remainingQueries]; omega

lemma reply_decreases (p : Params) (state : Work p) (value x : Point p)
    (hq : query state = some x) :
    remainingQueries (reply p state value) + 1 = remainingQueries state := by
  cases state with
  | warm k y => cases k <;> simp_all [query, reply, remainingQueries]
  | first k y => cases k <;> simp_all [query, reply, remainingQueries]; omega
  | second k y z => cases k <;> simp_all [query, reply, remainingQueries]; omega

lemma extra_pair (p : Params) (k : ℕ) (g : Point p → p.Ω → Point p)
    (x : Point p) (a b : p.Ω) :
    reply p (reply p (.first (k + 1) x) (g x a))
      (g (x - (1 / (4 * p.L)) • g x a) b) =
      .first k (LongTails.Algorithms.LocalNonlinearExtragradient.step
        (1 / (4 * p.L)) g x a b) := by
  rfl

lemma warm_reply_run (p : Params) (s k : ℕ) (hk : k < s)
    (g : Point p → p.Ω → Point p) (x : Point p) (samples : ℕ → p.Ω) :
    let η := p.μ / (p.ρ * p.L ^ 2)
    let current := LongTails.Algorithms.LocalNonlinearExtragradient.warmRun η g x samples k
    reply p (.warm (s - k) current) (g current (samples k)) =
      .warm (s - (k + 1))
        (LongTails.Algorithms.LocalNonlinearExtragradient.warmRun η g x samples (k + 1)) := by
  have he : s - k = (s - (k + 1)) + 1 := by omega
  dsimp only
  rw [he]
  rfl

lemma extra_reply_run (p : Params) (T k : ℕ) (hk : k < T)
    (g : Point p → p.Ω → Point p) (x : Point p) (samples : ℕ → p.Ω) :
    let η := 1 / (4 * p.L)
    let current := LongTails.Algorithms.LocalNonlinearExtragradient.run η g x samples k
    reply p (reply p (.first (T - k) current) (g current (samples (2 * k))))
      (g (current - η • g current (samples (2 * k))) (samples (2 * k + 1))) =
      .first (T - (k + 1))
        (LongTails.Algorithms.LocalNonlinearExtragradient.run η g x samples (k + 1)) := by
  have he : T - k = (T - (k + 1)) + 1 := by omega
  dsimp only
  rw [he]
  rfl

end LongTails.Proofs.DistributedJacobianStrongGrowthWorker
