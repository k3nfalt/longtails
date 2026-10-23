import LongTails.Proofs.ManySampleConvolutionalPerceptronTermination

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronCounting

open ManySampleConvolutionalPerceptronDynamics
open ManySampleConvolutionalPerceptronTrajectory
open ManySampleConvolutionalPerceptronBootstrap
open ManySampleConvolutionalPerceptronParameters
open ManySampleConvolutionalPerceptronTermination

variable {n : ℕ}

def referenceRun (e : ℕ → Option (Fin n)) : ℕ → ℕ
  | 0 => 0
  | k + 1 => match e k with
    | none => referenceRun e k + 1
    | some _ => 0

lemma referenceRun_le (e : ℕ → Option (Fin n)) (k : ℕ) : referenceRun e k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases he : e k with
    | none => simpa only [referenceRun, he, Nat.succ_le_succ_iff] using ih
    | some i => simp [referenceRun, he]

lemma trailing_none {e : ℕ → Option (Fin n)} {k j : ℕ}
    (hj : j < k) (hstart : k - referenceRun e k ≤ j) : e j = none := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    cases he : e k with
    | none =>
      simp only [referenceRun, he, Nat.add_sub_add_right] at hstart
      by_cases hjk : j = k
      · simpa only [hjk] using he
      · exact ih (by omega) hstart
    | some i =>
      simp only [referenceRun, he, Nat.sub_zero] at hstart
      omega

lemma length_with_run {e : ℕ → Option (Fin n)} {L K : ℕ}
    (hrun : ∀ j, j ≤ K → referenceRun e j ≤ L) :
    K ≤ (L + 1) * negativeCount e K + referenceRun e K := by
  induction K with
  | zero => simp [negativeCount, referenceRun]
  | succ K ih =>
    have hi := ih (fun j hj => hrun j (by omega))
    have hr := hrun K (by omega)
    cases he : e K with
    | none =>
      simp only [negativeCount, referenceRun, he, Option.isSome_none, Bool.false_eq_true,
        ite_false, Nat.add_zero]
      omega
    | some i =>
      simp only [negativeCount, referenceRun, he, Option.isSome_some, ite_true, Nat.mul_add,
        Nat.mul_one, Nat.add_zero]
      omega

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma reference_run_bound (p : Tuning) {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    {w : E} (hδ : g.contrast = p.δ) (hσ : g.kick = p.δ ^ 2)
    (hp : ∀ i, ‖g.plus i‖ ≤ 1) (hr : ∀ i, ‖g.minus i‖ ≤ 1)
    (hw : ‖w‖ = 1) (hmargin : ∀ i, p.κ ≤ -⟪g.minus i, w⟫)
    (hc : ∀ j, p.ρ ≤ coefficient g j) (hc1 : ∀ j, coefficient g j ≤ 1 / 2)
    (hinit : x 0 = ⟨1, 0, 1, 0⟩) {K : ℕ}
    (hstep : ∀ j, j < K → x (j + 1) = next g (e j) (x j))
    (hpermit : ∀ j, j < K → Permitted g (e j) (x j)) :
    referenceRun e K ≤ p.referenceLength := by
  by_contra hnot
  have hlong : p.referenceLength + 1 ≤ referenceRun e K := by omega
  have hrunK := referenceRun_le e K
  let J := K - (p.referenceLength + 1)
  have hJ : J + p.referenceLength < K := by dsimp only [J]; omega
  have hblock : ∀ j, j ≤ p.referenceLength → e (J + j) = none := by
    intro j hj
    apply trailing_none (k := K) (by omega)
    dsimp only [J]
    omega
  have hcount := negative_count_bound p hδ hσ hp hr hw hmargin hc hc1 hinit K hstep hpermit
  have hb := bounded_prefix p hδ hσ hp hr hc hc1 hinit
    (K := J) (fun j hj => hstep j (by omega)) (fun j hj => hpermit j (by omega))
    ((negativeCount_mono e (by omega : J ≤ K)).trans hcount.le)
  have hexit := reference_escape p (x := fun j => x (J + j)) (hc none) (hc1 none)
    (by simpa using hb.1) (by simpa using hb.2.1) (fun j hj => by
      have hs := hstep (J + j) (by omega)
      rw [hblock j hj.le] at hs
      simpa only [next, hσ, coefficient, Nat.add_assoc] using hs)
  have hlast := hpermit (J + p.referenceLength) hJ
  rw [hblock _ le_rfl] at hlast
  exact (not_le.mpr hexit) hlast

lemma event_length_bound (p : Tuning) {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    {w : E} (hδ : g.contrast = p.δ) (hσ : g.kick = p.δ ^ 2)
    (hp : ∀ i, ‖g.plus i‖ ≤ 1) (hr : ∀ i, ‖g.minus i‖ ≤ 1)
    (hw : ‖w‖ = 1) (hmargin : ∀ i, p.κ ≤ -⟪g.minus i, w⟫)
    (hc : ∀ j, p.ρ ≤ coefficient g j) (hc1 : ∀ j, coefficient g j ≤ 1 / 2)
    (hinit : x 0 = ⟨1, 0, 1, 0⟩) {K : ℕ}
    (hstep : ∀ j, j < K → x (j + 1) = next g (e j) (x j))
    (hpermit : ∀ j, j < K → Permitted g (e j) (x j)) :
    K ≤ (p.referenceLength + 1) * negativeCount e K + p.referenceLength := by
  have hrun : ∀ j, j ≤ K → referenceRun e j ≤ p.referenceLength := by
    intro j hj
    exact reference_run_bound p hδ hσ hp hr hw hmargin hc hc1 hinit
      (fun k hk => hstep k (by omega)) (fun k hk => hpermit k (by omega))
  exact (length_with_run hrun).trans (Nat.add_le_add_left (hrun K le_rfl) _)

end LongTails.Proofs.ManySampleConvolutionalPerceptronCounting
