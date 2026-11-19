import LongTails.Proofs.DistributedJacobianStrongGrowthPhaseProgress

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeSchedule

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch

noncomputable def medianTime (p : Params) : Time :=
  p.latency + p.timePerBit * (p.d * countWidth p.n + 64 : ℕ)

noncomputable def refinementTime (p : Params) : Time :=
  p.latency + p.timePerBit * (p.d * (refinementWidth p (localDepth p) + countWidth p.n) + 64 : ℕ)

noncomputable def roundComm (p : Params) (epoch : ℕ) : Time :=
  if epoch < warmWidth p (localDepth p) then medianTime p else refinementTime p

noncomputable def roundCompute (p : Params) (epoch : ℕ) : Time :=
  if epoch < warmWidth p (localDepth p) then 0 else (2 * localDepth p : ℕ) * p.computeTime

noncomputable def roundStart (p : Params) (epoch : ℕ) : Time :=
  (warmCount p (localDepth p) : ℕ) * p.computeTime +
    (min epoch (warmWidth p (localDepth p)) : ℕ) * (2 * p.height * medianTime p) +
    (epoch - warmWidth p (localDepth p) : ℕ) *
      ((2 * localDepth p : ℕ) * p.computeTime + 2 * p.height * refinementTime p)

noncomputable def upDeadline (p : Params) (epoch : ℕ) (v : Fin p.n) : Time :=
  roundStart p epoch + roundCompute p epoch + (p.height - p.depth v : ℕ) * roundComm p epoch

noncomputable def downDeadline (p : Params) (epoch : ℕ) (v : Fin p.n) : Time :=
  roundStart p epoch + roundCompute p epoch + p.height * roundComm p epoch + p.depth v * roundComm p epoch

lemma roundStart_zero (p : Params) : roundStart p 0 = (warmCount p (localDepth p) : ℕ) * p.computeTime := by
  simp [roundStart]

lemma roundStart_succ (p : Params) (epoch : ℕ) :
    roundStart p (epoch + 1) = roundStart p epoch + roundCompute p epoch + 2 * p.height * roundComm p epoch := by
  by_cases he : epoch < warmWidth p (localDepth p)
  · have hle : epoch ≤ warmWidth p (localDepth p) := by omega
    have hs : epoch + 1 ≤ warmWidth p (localDepth p) := by omega
    simp only [roundStart, roundCompute, roundComm, ite_eq_left he, Nat.min_eq_left hle,
      Nat.min_eq_left hs, Nat.sub_eq_zero_of_le hle, Nat.sub_eq_zero_of_le hs, Nat.cast_add,
      Nat.cast_one, Nat.cast_zero, zero_mul, add_zero]
    ring
  · have hle : warmWidth p (localDepth p) ≤ epoch := by omega
    have hs : warmWidth p (localDepth p) ≤ epoch + 1 := by omega
    have hsub : epoch + 1 - warmWidth p (localDepth p) = (epoch - warmWidth p (localDepth p)) + 1 := by omega
    simp only [roundStart, roundCompute, roundComm, ite_eq_right he, Nat.min_eq_right hle,
      Nat.min_eq_right hs, hsub, Nat.cast_add, Nat.cast_one]
    ring

lemma roundStart_mono (p : Params) : Monotone (roundStart p) := by
  apply monotone_nat_of_le_succ
  intro epoch
  rw [roundStart_succ]
  exact (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)

lemma upDeadline_parent (p : Params) (hp : valid p) (epoch : ℕ) (child : Fin p.n) (hc : child ≠ p.root) :
    upDeadline p epoch child + roundComm p epoch = upDeadline p epoch (p.parent child) := by
  have hd := hp.2.2.2.1 child hc
  have hb := hp.2.2.2.2.1 child
  have he : p.height - p.depth (p.parent child) = (p.height - p.depth child) + 1 := by omega
  simp only [upDeadline, he, Nat.cast_add, Nat.cast_one]
  ring

lemma downDeadline_child (p : Params) (hp : valid p) (epoch : ℕ) (child : Fin p.n) (hc : child ≠ p.root) :
    downDeadline p epoch (p.parent child) + roundComm p epoch = downDeadline p epoch child := by
  have hd := hp.2.2.2.1 child hc
  simp only [downDeadline, ← hd, Nat.cast_add, Nat.cast_one]
  ring

lemma downDeadline_le_next (p : Params) (hp : valid p) (epoch : ℕ) (v : Fin p.n) :
    downDeadline p epoch v ≤ roundStart p (epoch + 1) := by
  have hd : (p.depth v : Time) ≤ p.height := by exact_mod_cast hp.2.2.2.2.1 v
  have hm := mul_le_mul_of_nonneg_right hd (show (0 : Time) ≤ roundComm p epoch from zero_le)
  rw [roundStart_succ]
  unfold downDeadline
  calc
    _ ≤ roundStart p epoch + roundCompute p epoch + p.height * roundComm p epoch +
        p.height * roundComm p epoch := add_le_add le_rfl hm
    _ = _ := by ring

lemma upDeadline_le_down (p : Params) (epoch : ℕ) (v : Fin p.n) :
    upDeadline p epoch v ≤ downDeadline p epoch v := by
  have hd : ((p.height - p.depth v : ℕ) : Time) ≤ p.height := by exact_mod_cast Nat.sub_le p.height (p.depth v)
  have hm := mul_le_mul_of_nonneg_right hd (show (0 : Time) ≤ roundComm p epoch from zero_le)
  unfold upDeadline downDeadline
  exact (add_le_add (le_refl (roundStart p epoch + roundCompute p epoch)) hm).trans
    (le_add_of_nonneg_right zero_le)

lemma deadlines_le_finish (p : Params) (hp : valid p) (epoch : ℕ) (v : Fin p.n)
    (he : epoch < warmWidth p (localDepth p) + refinementCount p (localDepth p)) :
    upDeadline p epoch v ≤ roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) ∧
    downDeadline p epoch v ≤ roundStart p (warmWidth p (localDepth p) + refinementCount p (localDepth p)) := by
  have hd := (downDeadline_le_next p hp epoch v).trans ((roundStart_mono p) (by omega :
    epoch + 1 ≤ warmWidth p (localDepth p) + refinementCount p (localDepth p)))
  exact ⟨(upDeadline_le_down p epoch v).trans hd, hd⟩

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeSchedule
