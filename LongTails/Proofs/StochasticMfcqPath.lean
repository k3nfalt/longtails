import LongTails.Algorithms.StochasticMfcq
import LongTails.Proofs.StochasticMfcqGeometry
import LongTails.Proofs.StochasticMfcqCertificate

namespace LongTails.Proofs.StochasticMfcqPath

open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection
open LongTails.Algorithms.StochasticMfcq

def estimateAccurate (p : Params) (I : Problem p) (x : p.E) (v : Primitive p) : Prop :=
  ‖v.1 - gradient I.f x‖ ≤ precision p ∧
  (∀ i, |v.2.1 i - I.c x i| ≤ precision p) ∧
  ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p

def invariant (p : Params) (I : Problem p) (k : ℕ) (s : State p) : Prop :=
  feasible p I s.1 ∧ feasible p I s.2.1 ∧
  (s.2.2.2.1 = true → accurate p I (s.1, s.2.2.2.2)) ∧
  (s.2.2.2.1 = false → I.f s.1 ≤ I.f p.x0 - k * (precision p ^ 2 / (2 * p.H)))

lemma initial_invariant (p : Params) (I : Problem p) (H : Regularity p I) :
    invariant p I 0 (initial p) := by
  simp [invariant, initial, H.initialFeasible, feasible]

lemma next_invariant (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (k : ℕ) (s : State p)
    (estimates : Fin (replicas p) → JointSpace p)
    (hs : invariant p I k s)
    (he : estimateAccurate p I s.1 (robustEstimate p estimates)) :
    invariant p I (k + 1) (nextState p s estimates) := by
  rcases hs with ⟨hx, hprev, hcert, hdesc⟩
  rcases he with ⟨hg, hc, hJ⟩
  by_cases hstop : s.2.2.2.1 = true
  · simpa [invariant, nextState, hstop] using And.intro hx (And.intro hx (hcert hstop))
  · have hfalse : s.2.2.2.1 = false := Bool.eq_false_iff.mpr hstop
    by_cases hr : ‖residual p (robustEstimate p estimates)‖ ≤ 4 * precision p
    · have ha := StochasticMfcqCertificate.stopping_accurate p I hp H s.1 hx
        (robustEstimate p estimates) hg hc hJ hr
      simpa [invariant, nextState, hstop, hr] using And.intro hx (And.intro hx ha)
    · have hr' := (lt_of_not_ge hr).le
      have hf := StochasticMfcqGeometry.step_feasible p I hp H s.1 hx
        (robustEstimate p estimates) hg hc hJ hr'
      have hd := StochasticMfcqGeometry.objective_decrease p I hp H s.1 hx
        (robustEstimate p estimates) hg hJ hr'
      have hb := hdesc hfalse
      simp only [nextState, hstop, hr, ↓reduceIte]
      change feasible p I _ ∧ feasible p I s.1 ∧
        (false = true → accurate p I _) ∧
        (false = false → I.f _ ≤ I.f p.x0 - (k + 1 : ℕ) * _)
      refine ⟨hf, hx, by simp, ?_⟩
      intro _
      push_cast
      nlinarith


lemma next_previous (p : Params) (s : State p)
    (estimates : Fin (replicas p) → JointSpace p) :
    (nextState p s estimates).2.1 = s.1 := by
  dsimp only [nextState]
  split_ifs <;> rfl

lemma next_displacement (p : Params) (hp : spec.valid p) (s : State p)
    (estimates : Fin (replicas p) → JointSpace p) :
    ‖(nextState p s estimates).1 - s.1‖ ≤ stepSize p := by
  have hη := StochasticMfcqTuning.stepSize_pos p hp
  have hd := StochasticMfcqGeometry.direction_norm_le p (robustEstimate p estimates)
  dsimp only [nextState]
  split_ifs
  · simpa using hη.le
  · simpa using hη.le
  · simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    nlinarith

lemma final_accurate (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (s : State p) (hs : invariant p I (outerSteps p) s) :
    accurate p I (s.1, s.2.2.2.2) := by
  by_cases hstop : s.2.2.2.1 = true
  · exact hs.2.2.1 hstop
  · have hd := hs.2.2.2 (Bool.eq_false_iff.mpr hstop)
    have hg := H.initialGap s.1 hs.1
    have hn := StochasticMfcqTuning.outerSteps_gap p hp
    linarith

lemma trajectory_invariant (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (s : ℕ → State p)
    (estimates : ℕ → Fin (replicas p) → JointSpace p)
    (h0 : s 0 = initial p)
    (hstep : ∀ k < outerSteps p, s (k + 1) = nextState p (s k) (estimates k))
    (he : ∀ k < outerSteps p,
      estimateAccurate p I (s k).1 (robustEstimate p (estimates k))) :
    ∀ k ≤ outerSteps p, invariant p I k (s k) := by
  intro k hk
  induction k with
  | zero => rw [h0]; exact initial_invariant p I H
  | succ k ih =>
    have hk' : k < outerSteps p := by omega
    rw [hstep k hk']
    exact next_invariant p I hp H k (s k) (estimates k) (ih (by omega)) (he k hk')

lemma trajectory_accurate (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (s : ℕ → State p)
    (estimates : ℕ → Fin (replicas p) → JointSpace p)
    (h0 : s 0 = initial p)
    (hstep : ∀ k < outerSteps p, s (k + 1) = nextState p (s k) (estimates k))
    (he : ∀ k < outerSteps p,
      estimateAccurate p I (s k).1 (robustEstimate p (estimates k))) :
    accurate p I ((s (outerSteps p)).1, (s (outerSteps p)).2.2.2.2) :=
  final_accurate p I hp H _
    (trajectory_invariant p I hp H s estimates h0 hstep he _ le_rfl)

lemma trajectory_invariant_of_alive_accuracy (p : Params) (I : Problem p)
    (hp : spec.valid p) (H : Regularity p I) (s : ℕ → State p)
    (estimates : ℕ → Fin (replicas p) → JointSpace p)
    (h0 : s 0 = initial p)
    (hstep : ∀ k < outerSteps p, s (k + 1) = nextState p (s k) (estimates k))
    (he : ∀ k < outerSteps p, (∀ j ≤ k, feasible p I (s j).1) →
      estimateAccurate p I (s k).1 (robustEstimate p (estimates k))) :
    ∀ k ≤ outerSteps p, invariant p I k (s k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    cases k with
    | zero => rw [h0]; exact initial_invariant p I H
    | succ k =>
      have hk' : k < outerSteps p := by omega
      have hprior := ih k (by omega) (by omega)
      have halive : ∀ j ≤ k, feasible p I (s j).1 := by
        intro j hj
        exact (ih j (by omega) (by omega)).1
      rw [hstep k hk']
      exact next_invariant p I hp H k (s k) (estimates k) hprior (he k hk' halive)

lemma trajectory_displacement (p : Params) (hp : spec.valid p)
    (s : ℕ → State p) (estimates : ℕ → Fin (replicas p) → JointSpace p)
    (h0 : s 0 = initial p)
    (hstep : ∀ k < outerSteps p, s (k + 1) = nextState p (s k) (estimates k))
    (k : ℕ) (hk : k ≤ outerSteps p) :
    ‖(s k).1 - (s k).2.1‖ ≤ stepSize p := by
  cases k with
  | zero =>
    rw [h0]
    simpa [initial] using (StochasticMfcqTuning.stepSize_pos p hp).le
  | succ k =>
    rw [hstep k (by omega), next_previous]
    exact next_displacement p hp (s k) (estimates k)

lemma trajectory_safe_accurate (p : Params) (I : Problem p)
    (hp : spec.valid p) (H : Regularity p I) (s : ℕ → State p)
    (estimates : ℕ → Fin (replicas p) → JointSpace p)
    (h0 : s 0 = initial p)
    (hstep : ∀ k < outerSteps p, s (k + 1) = nextState p (s k) (estimates k))
    (he : ∀ k < outerSteps p, (∀ j ≤ k, feasible p I (s j).1) →
      estimateAccurate p I (s k).1 (robustEstimate p (estimates k))) :
    (∀ k ≤ outerSteps p, feasible p I (s k).1 ∧ feasible p I (s k).2.1 ∧
      ‖(s k).1 - (s k).2.1‖ ≤ stepSize p) ∧
    accurate p I ((s (outerSteps p)).1, (s (outerSteps p)).2.2.2.2) := by
  have hi := trajectory_invariant_of_alive_accuracy p I hp H s estimates h0 hstep he
  refine ⟨?_, final_accurate p I hp H _ (hi _ le_rfl)⟩
  intro k hk
  exact ⟨(hi k hk).1, (hi k hk).2.1,
    trajectory_displacement p hp s estimates h0 hstep k hk⟩

end LongTails.Proofs.StochasticMfcqPath
