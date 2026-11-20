import LongTails.Proofs.DistributedJacobianStrongGrowthAnchorState
import LongTails.Proofs.DistributedJacobianStrongGrowthMedianExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthAnchorNotification

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthMedianAnchor
open DistributedJacobianStrongGrowthAnchorState

lemma anchorState_notification (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) (idle : Time)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (c : ExecutionState (system p g S) (algorithm p idle)) (i : Fin p.n)
    (notification : Event (Point p) (CommReply p)) (next : OracleState (system p g S))
    (h : ∀ v, AnchorState p (medianCenter p codes) (c.workers v))
    (hcontent : MedianContent p codes c.workers c.oracle.communication)
    (hbounds : ∀ v, PhaseBounds p (c.workers v).phase)
    (he : event (system p g S) (algorithm p idle) c c.time = some ((i, notification), next)) :
    ∀ v, AnchorState p (medianCenter p codes)
      (Function.update c.workers i (update p i (c.workers i) notification) v) := by
  classical
  cases notification with
  | wake =>
      intro v
      by_cases hv : v = i
      · subst v
        simpa [Function.update, update] using h i
      · simpa [Function.update, hv] using h v
  | computed value =>
      intro v
      by_cases hv : v = i
      · subst v
        simpa [Function.update] using anchorState_computed p (medianCenter p codes) i (c.workers i) value (h i)
      · simpa [Function.update, hv] using h v
  | received message =>
      obtain ⟨oracle, ha, _⟩ := DistributedExecution.received_event (system p g S) (algorithm p idle)
        c c.time i message next he
      obtain ⟨finish, hstored, _, _⟩ :=
        DistributedJacobianStrongGrowthOracle.communication_received_data p S c.oracle.communication oracle
          c.time message.source i message.bits ha
      intro v
      by_cases hv : v = i
      · subst v
        have hlocal : AnchorState p (medianCenter p codes) (update p i (c.workers i) (.received message)) := by
          apply anchorState_received p (medianCenter p codes) i (c.workers i) message (h i) (hbounds i)
          intro hd hs
          have hf := median_received_anchor p hp codes c.workers c.oracle.communication hcontent i hd.1 hs
            finish message.bits (by simpa only [hd.2] using hstored)
          simpa only [update, ite_eq_left (show i ≠ p.root ∧ True from ⟨hd.1, trivial⟩), relay, medianCenter] using hf
        simpa [Function.update, algorithm] using hlocal
      · simpa [Function.update, hv] using h v

end LongTails.Proofs.DistributedJacobianStrongGrowthAnchorNotification
