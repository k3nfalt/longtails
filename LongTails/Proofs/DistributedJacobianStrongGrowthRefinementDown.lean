import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementRelay

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementDown

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open LongTails.Algorithms.DistributedLocalExtragradientTree
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthRefinementContent
open DistributedJacobianStrongGrowthRefinementRelay

lemma refinementContent_relay_root (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network) (epoch : ℕ)
    (hs : (workers p.root).phase = .refinement epoch)
    (hb : epoch < refinementCount p (localDepth p))
    (ha : (workers p.root).anchor = warmCenter p (warmCount p (localDepth p))
      (warmWidth p (localDepth p)) (warmSpacing p (localDepth p)) g samples)
    (hw : (workers p.root).work = none)
    (hfull : children p p.root ⊆ (workers p.root).collector.seen) :
    RefinementContent p g samples (Function.update workers p.root (relay p p.root (workers p.root)
      (broadcastValues p (workers p.root).phase
        (fun j => (workers p.root).own j + (workers p.root).collector.total j)))) network := by
  rw [refinementContent_root_total p hp g samples workers network h epoch hs hw hfull]
  simp only [broadcastValues, hs]
  exact refinementContent_relay p hp g samples workers network h p.root epoch hs hb ha
    (fun hn => False.elim (hn rfl))

lemma refinementContent_receive_down (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (h : RefinementContent p g samples workers network)
    (hh : DistributedJacobianStrongGrowthHandshake.Handshake p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (epoch : ℕ)
    (hs : (workers v).phase = .refinement epoch)
    (hb : epoch < refinementCount p (localDepth p))
    (ha : (workers v).anchor = warmCenter p (warmCount p (localDepth p))
      (warmWidth p (localDepth p)) (warmSpacing p (localDepth p)) g samples)
    (finish : DistributedTemplate.Time) (bits : List Bool)
    (hpending : network.messages (p.parent v) v = some (finish, bits)) :
    RefinementContent p g samples (Function.update workers v
      (update p v (workers v) (.received ⟨p.parent v, bits⟩)))
      ⟨Function.update network.messages (p.parent v) (Function.update (network.messages (p.parent v)) v none)⟩ := by
  classical
  have hd := refinementContent_decode_down p g samples workers network h v hv finish bits hpending epoch hs
  have hu : network.messages v (p.parent v) = none := by
    cases hstored : network.messages v (p.parent v) with
    | none => rfl
    | some packet =>
        have hedge := hh v hv
        unfold DistributedJacobianStrongGrowthHandshake.edgeLoad at hedge
        rw [hpending, hstored] at hedge
        cases hsent : (workers v).sent <;>
          simp only [Option.isSome_some, Bool.toNat_true, hsent, Bool.toNat_false] at hedge <;> omega
  let nextNetwork : CommunicationState p :=
    ⟨Function.update network.messages (p.parent v) (Function.update (network.messages (p.parent v)) v none)⟩
  have hn := DistributedJacobianStrongGrowthConservation.parent_ne_self p hp v hv
  have herase := refinementContent_erase p g samples workers network h (p.parent v) v
  have hrelay := refinementContent_relay p hp g samples workers nextNetwork herase v epoch hs hb ha
    (by intro _; simp [nextNetwork, Function.update, Ne.symm hn, hu])
  simp only [update]
  rw [ite_eq_left (show v ≠ p.root ∧ True from ⟨hv, trivial⟩)]
  rw [show downWidth p (workers v).phase = refinementWidth p (localDepth p) + countWidth p.n by
    simp [downWidth, hs], hd]
  exact hrelay

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementDown
