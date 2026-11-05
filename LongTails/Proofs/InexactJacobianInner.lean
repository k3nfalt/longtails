import LongTails.Proofs.InexactJacobianModel

open scoped RealInnerProductSpace

namespace LongTails.Proofs.InexactJacobianInner

open LongTails.Setups.InexactJacobianMonotone
open LongTails.Algorithms.NestedAnchoredInexactJacobian
open InexactJacobianModel InexactJacobianGeometry InexactJacobianPhase

noncomputable section

variable {p : Params}

structure Regular (F : p.E → p.E) : Prop where
  deriv : ∀ x, HasFDerivAt F (fderiv ℝ F x) x
  mono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫
  lip : ∀ x y, ‖fderiv ℝ F x - fderiv ℝ F y‖ ≤ p.M * ‖x - y‖

def attemptOffset (k j : ℕ) : ℕ := ∑ l ∈ Finset.range j, 2 * innerCount p k l

def tstate (k : ℕ) (z Fz : p.E) (j i : ℕ) (u Gu : p.E) : State p :=
  ⟨.model, k, z, Fz, j, i, u, Gu, u⟩

def withTrial (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E) (n : ℕ)
    (s : State p) : State p :=
  { s with phase := .certificate, pending := s.trial (F s.innerCenter) (J n s.innerCenter) }

def zseq (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j : ℕ) : ℕ → p.E × p.E
  | 0 => (center p k z Fz, 0)
  | i + 1 =>
    let s := tstate k z Fz j i (zseq F J base k z Fz j i).1 (zseq F J base k z Fz j i).2
    let v := withTrial F J (base + attemptOffset (p := p) k j + 2 * i) s
    (v.pending, v.regularizedValue v.pending (F v.pending))

def trialAt (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j i : ℕ) : State p :=
  tstate k z Fz j i (zseq F J base k z Fz j i).1 (zseq F J base k z Fz j i).2

def certificateAt (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j i : ℕ) : State p :=
  withTrial F J (base + attemptOffset (p := p) k j + 2 * i) (trialAt F J base k z Fz j i)

def acc (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j i : ℕ) : Prop :=
  (certificateAt F J base k z Fz j i).accepted (F (certificateAt F J base k z Fz j i).pending)

lemma zseq_succ_fst (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j i : ℕ) :
    (zseq F J base k z Fz j (i + 1)).1 = (certificateAt F J base k z Fz j i).pending := rfl

lemma zseq_succ_snd (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j i : ℕ) :
    (zseq F J base k z Fz j (i + 1)).2 = F (zseq F J base k z Fz j (i + 1)).1 +
      (1 / outerStep p k) • ((zseq F J base k z Fz j (i + 1)).1 - anchor p k z) := rfl

lemma trialAt_innerAnchor (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) (j i : ℕ) :
    (trialAt F J base k z Fz j i).innerAnchor =
      (1 / ((i : ℝ) + 1)) • center p k z Fz +
        ((i : ℝ) / ((i : ℝ) + 1)) • (zseq F J base k z Fz j i).1 := rfl

lemma attempt_invariant (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (base k : ℕ) (z Fz xs : p.E) (j : ℕ)
    (hzero : F xs + (1 / outerStep p k) • (xs - anchor p k z) = 0)
    (hr : ‖center p k z Fz - xs‖ ≤ guess p k j) :
    ∀ i, 0 < i →
      ‖F (zseq F J base k z Fz j i).1 +
        (1 / outerStep p k) • ((zseq F J base k z Fz j i).1 - anchor p k z)‖ ≤
      2 * ‖center p k z Fz - xs‖ / ((i : ℝ) * innerStep p k j) := by
  let μ := 1 / outerStep p k
  let G := fun x => F x + μ • (x - anchor p k z)
  let u := fun i => (zseq F J base k z Fz j i).1
  let g := fun i => (zseq F J base k z Fz j i).2
  let b := fun i => (trialAt F J base k z Fz j i).innerAnchor
  let c := fun i => (trialAt F J base k z Fz j i).innerCenter
  let D := fun i => fderiv ℝ F (c i) + μ • ContinuousLinearMap.id ℝ p.E
  let JJ := fun i => J (base + attemptOffset (p := p) k j + 2 * i) (c i) + μ • ContinuousLinearMap.id ℝ p.E
  have ha := outerStep_pos hR hε k
  have hμ : 0 < μ := one_div_pos.mpr ha
  have hGmono : ∀ x y, 0 ≤ ⟪G x - G y, x - y⟫ := by
    intro x y
    have h := regularized_strong (anchor p k z) μ hreg.mono x y
    exact (mul_nonneg hμ.le (sq_nonneg _)).trans h
  intro n hn
  have hphase := phase_invariant (G := G) (center p k z Fz) xs hδ hM (norm_nonneg _)
    (guess_pos hM hδ hR hε k j) hr (le_refl _) hzero hGmono u g b c D JJ n
    rfl (fun i => zseq_succ_snd F J base k z Fz j i)
    (fun i _ => FrozenJacobianSplitting.jacobian_monotone hGmono
      (regularized_deriv (anchor p k z) (c i) μ (hreg.deriv _)))
    (fun i _ => by
      dsimp only [JJ, D]
      rw [add_sub_add_right_eq_sub]
      exact hJ _ _)
    (fun i _ => rfl) (fun i _ => rfl)
    (fun i _ v => regularized_taylor hM.le hreg.deriv hreg.lip (anchor p k z) (c i) v μ)
    (fun i _ => by
      have h := trial_equation (trialAt F J base k z Fz j i) (F (c i))
        (J (base + attemptOffset (p := p) k j + 2 * i) (c i)) (fderiv ℝ F (c i))
        ha (innerStep_pos hM hδ hR hε k j)
        (FrozenJacobianSplitting.jacobian_monotone hreg.mono (hreg.deriv _)) (hJ _ _)
      have he : JJ i + p.δ • ContinuousLinearMap.id ℝ p.E =
          J (base + attemptOffset (p := p) k j + 2 * i) (c i) +
            (μ + p.δ) • ContinuousLinearMap.id ℝ p.E := by dsimp only [JJ]; module
      rw [he]
      exact h)
  exact (hphase n le_rfl).2.2 hn

lemma attempt_success (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (base k : ℕ) (z Fz xs : p.E) (j : ℕ)
    (hzero : F xs + (1 / outerStep p k) • (xs - anchor p k z) = 0)
    (hr : ‖center p k z Fz - xs‖ ≤ guess p k j) :
    ∃ i < innerCount p k j, acc F J base k z Fz j i := by
  let N := innerCount p k j
  have hN : 0 < N := innerCount_pos k j
  have hn : N - 1 + 1 = N := by omega
  have ha := outerStep_pos hR hε k
  have ht := innerStep_pos hM hδ hR hε k j
  let G := fun x => F x + (1 / outerStep p k) • (x - anchor p k z)
  have hstrong := regularized_strong (anchor p k z) (1 / outerStep p k) hreg.mono
  have hres := attempt_invariant F hreg J hJ hM hδ hR hε base k z Fz xs j hzero hr N hN
  have hcert := phase_certificate (G := G) (one_div_pos.mpr ha)
    (show 0 < (N : ℝ) * innerStep p k j by positivity)
    (innerCount_sufficient hM hδ hR hε k j) hzero hstrong hres
  refine ⟨N - 1, by omega, ?_⟩
  have hy : (certificateAt F J base k z Fz j (N - 1)).pending =
      (zseq F J base k z Fz j N).1 := by rw [← zseq_succ_fst, hn]
  change ‖outerStep p k • G (certificateAt F J base k z Fz j (N - 1)).pending‖ ≤
    ‖(certificateAt F J base k z Fz j (N - 1)).pending - center p k z Fz‖ / 2
  rw [hy, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  simpa only [one_div, div_inv_eq_mul, mul_comm] using hcert

def Succeeds (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) : Prop :=
  ∃ j, ∃ i, i < innerCount p k j ∧ acc F J base k z Fz j i

def firstAttempt (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) : ℕ := by
  classical
  exact if h : Succeeds F J base k z Fz then Nat.find h else 0

def firstIndex (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) : ℕ := by
  classical
  exact if h : ∃ i, i < innerCount p k (firstAttempt F J base k z Fz) ∧
      acc F J base k z Fz (firstAttempt F J base k z Fz) i then Nat.find h else 0

def nextPoint (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) : p.E :=
  (certificateAt F J base k z Fz (firstAttempt F J base k z Fz)
    (firstIndex F J base k z Fz)).pending

def outerTicks (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    (base k : ℕ) (z Fz : p.E) : ℕ :=
  attemptOffset (p := p) k (firstAttempt F J base k z Fz) + 2 * (firstIndex F J base k z Fz + 1)

lemma first_spec (F : p.E → p.E) (J : ℕ → p.E → p.E →L[ℝ] p.E)
    {base k : ℕ} {z Fz : p.E} (h : Succeeds F J base k z Fz) :
    firstIndex F J base k z Fz < innerCount p k (firstAttempt F J base k z Fz) ∧
      acc F J base k z Fz (firstAttempt F J base k z Fz) (firstIndex F J base k z Fz) ∧
      (∀ j < firstAttempt F J base k z Fz, ∀ i < innerCount p k j, ¬ acc F J base k z Fz j i) ∧
      (∀ i < firstIndex F J base k z Fz, ¬ acc F J base k z Fz (firstAttempt F J base k z Fz) i) := by
  classical
  have hj : firstAttempt F J base k z Fz = Nat.find h := by simp only [firstAttempt, h, ↓reduceDIte]
  have hspec := Nat.find_spec h
  rw [← hj] at hspec
  have hi : firstIndex F J base k z Fz = Nat.find hspec := by simp only [firstIndex, hspec, ↓reduceDIte]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hi]; exact (Nat.find_spec hspec).1
  · rw [hi]; exact (Nat.find_spec hspec).2
  · intro j hjlt i hi' hacc
    rw [hj] at hjlt
    exact Nat.find_min h hjlt ⟨i, hi', hacc⟩
  · intro i hilt hacc
    rw [hi] at hilt
    exact Nat.find_min hspec hilt ⟨lt_trans hilt (Nat.find_spec hspec).1, hacc⟩

lemma guess_unbounded (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (k : ℕ) (r : ℝ) : ∃ j, r ≤ guess p k j := by
  have hρ := guess_pos hM hδ hR hε k 0
  obtain ⟨j, hj⟩ := exists_nat_ge (r / guess p k 0)
  have hjpow : (j : ℝ) ≤ (2 : ℝ) ^ j := by
    have h : ∀ n : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ n := by
      intro n
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [pow_succ]
        push_cast
        nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n)]
    exact h j
  refine ⟨j, ?_⟩
  have h := (div_le_iff₀ hρ).1 (hj.trans hjpow)
  have he : guess p k j = 2 ^ j * guess p k 0 := by unfold guess; simp; ring
  rwa [he]

lemma succeeds (F : p.E → p.E) (hreg : Regular F)
    (J : ℕ → p.E → p.E →L[ℝ] p.E) (hJ : ∀ n x, ‖J n x - fderiv ℝ F x‖ ≤ p.δ)
    (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (base k : ℕ) (z Fz : p.E) : Succeeds F J base k z Fz := by
  obtain ⟨xs, hzero⟩ := regularized_root hM.le (outerStep_pos hR hε k)
    hreg.deriv hreg.lip hreg.mono (anchor p k z)
  obtain ⟨j, hj⟩ := guess_unbounded hM hδ hR hε k ‖center p k z Fz - xs‖
  obtain ⟨i, hi, hacc⟩ := attempt_success F hreg J hJ hM hδ hR hε base k z Fz xs j hzero hj
  exact ⟨j, i, hi, hacc⟩

end

end LongTails.Proofs.InexactJacobianInner
