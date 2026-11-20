import LongTails.Proofs.GraceGraphPacking
import LongTails.Proofs.GraceRouting
import LongTails.Proofs.GracePacket

namespace LongTails.Proofs.GraceCommunicationTime

open LongTails.Setups.GraphBandwidthSmoothNonconvex
open LongTails.Algorithms.GraceRouting
open LongTails.Algorithms.GraceGraph
open LongTails.Algorithms.GracePacket

variable {p : Params} {S : Finset (Fin p.n)} {r : Fin p.n}

lemma frame_bound (A : Routes p S r) (m : ℕ+) (q : ℕ)
    (hc : ∀ e : Link p, ((A.linkLanes e.val.1 e.val.2).card : ℝ) ≤
      4 * m / (α p S : ℝ) * capacity p e)
    (hb : ∀ e : Link p, 0 < capacity p e) :
    A.frameTime q ≤ (q + DistributedTemplate.clockBits : ℕ) * (4 * m / α p S) := by
  apply Finset.sup_le
  intro e _
  apply (div_le_iff₀ (hb e)).mpr
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact_mod_cast hc e

lemma two_phase_budget (A : Routes p S r) (m : ℕ+) (B w : ℕ)
    (hm : (m : ℕ) ≤ A.P) (hα : 0 < α p S)
    (hc : ∀ e : Link p, ((A.linkLanes e.val.1 e.val.2).card : ℝ) ≤
      4 * m / (α p S : ℝ) * capacity p e)
    (hb : ∀ e : Link p, 0 < capacity p e) :
    let t := limbWidth B
    let D := p.d * limbCount w t
    2 * A.slots D * A.frameTime (wordWidth t B) ≤
      16 * ((p.d : DistributedTemplate.Time) * (w + t : ℕ) +
        t * (m : DistributedTemplate.Time) * (A.height + 1 : ℕ)) / α p S := by
  intro t D
  have ht : 0 < t := by dsimp [t, limbWidth, DistributedTemplate.clockBits]; omega
  have hq : wordWidth t B + DistributedTemplate.clockBits = 2 * t := by
    dsimp [t, wordWidth, limbWidth]; omega
  have hframe := frame_bound A m (wordWidth t B) hc hb
  rw [hq] at hframe
  have hf : (A.frameTime (wordWidth t B) : ℝ) ≤ (2 * t : ℕ) * (4 * (m : ℝ) / (α p S : ℝ)) := by
    exact_mod_cast hframe
  have halpha : 0 < (α p S : ℝ) := by exact_mod_cast hα
  have htime := GracePacketPipeline.striped_time hm D A.height (t : ℝ) (α p S : ℝ)
    (Nat.cast_nonneg _) halpha
  change ((A.slots D : ℕ) : ℝ) * (2 * m * t / (α p S : ℝ)) ≤ _ at htime
  have hwidth : (D : ℝ) * t ≤ p.d * ((w + t : ℕ) : ℝ) := by
    have hn := Nat.mul_le_mul_left p.d (GracePacket.limb_capacity w t ht).2
    dsimp [D]
    exact_mod_cast (by simpa [Nat.mul_assoc, Nat.mul_comm t (limbCount w t)] using hn :
      p.d * limbCount w t * t ≤ p.d * (w + t))
  apply NNReal.coe_le_coe.mp
  push_cast at hf hwidth htime ⊢
  have hscaled := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2 * ((A.slots D : ℕ) : ℝ))
  calc
    _ ≤ _ := hscaled
    _ = 8 * (((A.slots D : ℕ) : ℝ) * (2 * m * t / (α p S : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left htime (by norm_num)
    _ ≤ _ := by
      field_simp [halpha.ne']
      nlinarith

end LongTails.Proofs.GraceCommunicationTime
