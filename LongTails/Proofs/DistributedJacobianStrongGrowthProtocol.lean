import LongTails.Algorithms.DistributedLocalExtragradientProtocol
import LongTails.Proofs.DistributedJacobianStrongGrowthWorker
import LongTails.Proofs.DistributedJacobianStrongGrowthTree
import LongTails.Proofs.LocalExtragradientQuantization

namespace LongTails.Proofs.DistributedJacobianStrongGrowthProtocol

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.LocalExtragradientQuantization

lemma startRefinement_current (p : Params) (epoch : ℕ) (s : State p) :
    (startRefinement p epoch s).current = s.current := by
  unfold startRefinement
  split_ifs <;> rfl

lemma startRefinement_anchor (p : Params) (epoch : ℕ) (s : State p) :
    (startRefinement p epoch s).anchor = s.anchor := by
  unfold startRefinement
  split_ifs <;> rfl

lemma finishLocal_preserves_collector (p : Params) (s : State p) (x : Point p) :
    (finishLocal p s x).collector = s.collector := by
  cases hs : s.phase <;> simp [finishLocal, hs]

lemma finishBroadcast_refinement_current (p : Params) (s : State p) (epoch : ℕ)
    (hs : s.phase = .refinement epoch) (values : Fin p.d → ℕ) :
    (finishBroadcast p s values).current =
      LongTails.Algorithms.DistributedLocalExtragradient.localizedOutput p s.anchor (radius p (localDepth p))
        (s.current + decodeAverage p.n (refinementWidth p (localDepth p))
          (refinementSpacing p (localDepth p)) values) := by
  simp only [finishBroadcast, hs, startRefinement_current]

lemma relay_packet (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ)
    (packet : Fin p.n × List Bool) (hp : packet ∈ (relay p v s values).queue) :
    packet.1 ∈ children p v ∧ packet.2 = naturalMessage (downWidth p s.phase) values := by
  change packet ∈ (children p v).toList.map (fun child =>
    (child, naturalMessage (downWidth p s.phase) values)) at hp
  obtain ⟨child, hc, he⟩ := List.mem_map.mp hp
  subst packet
  exact ⟨Finset.mem_toList.mp hc, rfl⟩

lemma relay_packet_length (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ)
    (packet : Fin p.n × List Bool) (hp : packet ∈ (relay p v s values).queue) :
    (packet.2 ++ List.replicate clockBits false).length = p.d * downWidth p s.phase + 64 := by
  rw [(relay_packet p v s values packet hp).2]
  exact LocalExtragradientQuantization.naturalMessage_packet_length _ _

lemma query_queue (p : Params) (v : Fin p.n) (s : State p)
    (packet : Fin p.n × List Bool) (rest : List (Fin p.n × List Bool))
    (hq : s.queue = packet :: rest) :
    query p v s = (.communicate packet, { s with queue := rest }) := by
  simp only [query, hq]

lemma query_compute (p : Params) (v : Fin p.n) (s : State p)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p) (x : Point p)
    (hqueue : s.queue = []) (hwork : s.work = some work) (hbusy : s.busy = false)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some x) :
    query p v s = (.compute x, { s with busy := true }) := by
  simp [query, hqueue, hwork, hbusy, hq]

lemma update_computed (p : Params) (v : Fin p.n) (s : State p)
    (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p) (value : Point p)
    (hwork : s.work = some work) (hbusy : s.busy = true) :
    update p v s (.computed value) =
      { s with
        work := some (LongTails.Algorithms.DistributedLocalExtragradientWorker.reply p work value)
        busy := false } := by
  simp [update, hwork, hbusy]

lemma refinement_broadcast_reference (p : Params) (s : State p) (epoch N : ℕ)
    (hs : s.phase = .refinement epoch) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : ℕ → p.Ω) :
    let codes := fun i : Fin p.n => LongTails.Algorithms.DistributedQuantization.quantize p.d
      (refinementWidth p (localDepth p)) (refinementSpacing p (localDepth p))
      (OracleTemplate.clip (clipRadius p (localDepth p))
        (LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i) s.current
          (fun k => samples (N + (p.n * k + i.val))) (localDepth p) - s.current))
    (finishBroadcast p s (aggregateCodes codes)).current =
      LongTails.Algorithms.DistributedLocalExtragradient.projectedBlockOutput p (localDepth p) N
        (clipRadius p (localDepth p)) (refinementWidth p (localDepth p))
        (refinementSpacing p (localDepth p)) s.anchor (radius p (localDepth p)) g s.current samples := by
  dsimp only
  rw [finishBroadcast_refinement_current p s epoch hs]
  rfl

lemma median_broadcast_reference (p : Params) (s : State p)
    (hs : s.phase = .median 1) (values : Fin p.d → ℕ)
    (codes : Fin p.n → LongTails.Algorithms.DistributedQuantization.Grid p.d (warmWidth p (localDepth p)))
    (hlower : LongTails.Algorithms.DistributedLocalExtragradientMedianSearch.nextLower 0 s.lower
      (fun j => decide (values j = 1)) =
        fun j => (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes j).val) :
    (finishBroadcast p s values).current =
      LongTails.Algorithms.DistributedLocalExtragradient.projectBall p p.x0 p.R
        (p.x0 + LongTails.Algorithms.DistributedQuantization.reconstruct (warmSpacing p (localDepth p))
          (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes)) := by
  have hpack : packNaturals (warmWidth p (localDepth p))
      (fun j => (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes j).val) =
        LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes := by
    funext j
    apply Fin.ext
    exact Nat.mod_eq_of_lt (LongTails.Algorithms.DistributedLocalExtragradientWarmStart.medianGrid codes j).isLt
  simp [finishBroadcast, hs, hlower, startRefinement_current, hpack]

lemma query_compute_data (p : Params) (v : Fin p.n) (s next : State p) (x : Point p)
    (h : query p v s = (.compute x, next)) :
    ∃ work, s.queue = [] ∧ s.work = some work ∧ s.busy = false ∧
      LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = some x ∧
      next = { s with busy := true } := by
  cases hqueue : s.queue with
  | cons packet rest => simp [query, hqueue] at h
  | nil =>
      cases hwork : s.work with
      | none =>
          simp only [query, hqueue, hwork] at h
          split_ifs at h <;> simp at h
      | some work =>
          cases hbusy : s.busy with
          | true => simp [query, hqueue, hwork, hbusy] at h
          | false =>
              cases hquery : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | none => simp [query, hqueue, hwork, hbusy, hquery] at h
              | some y =>
                  have he : (.compute y, { s with busy := true }) =
                      ((.compute x : Action (Point p) p.n), next) := by
                    simpa [query, hqueue, hwork, hbusy, hquery] using h
                  have hy : y = x := Action.compute.inj (congrArg Prod.fst he)
                  subst y
                  refine ⟨work, rfl, rfl, rfl, hquery, ?_⟩
                  simpa only [hqueue, hwork] using (congrArg Prod.snd he).symm

end LongTails.Proofs.DistributedJacobianStrongGrowthProtocol
