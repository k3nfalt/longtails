import LongTails.Proofs.ManySampleConvolutionalPerceptronTrajectory

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronBootstrap

open ManySampleConvolutionalPerceptronDynamics
open ManySampleConvolutionalPerceptronStability
open ManySampleConvolutionalPerceptronTrajectory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

def Bounded (H : ℝ) (x : State E) : Prop :=
  |x.a| ≤ 2 ∧ |x.q| ≤ 2 ∧ |x.t - 1| ≤ 1 / 2 ∧ ‖x.z‖ ≤ H

omit [InnerProductSpace ℝ E] in
lemma bounded_signal {H : ℝ} {x : State E} (hx : Bounded H x) :
    1 / 2 ≤ x.t ∧ |x.t| ≤ 3 / 2 := by
  have ht := abs_le.mp hx.2.2.1
  constructor
  · linarith
  · apply abs_le.mpr
    constructor <;> linarith

lemma cold_first_mass {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    (hinit : x 0 = ⟨1, 0, 1, 0⟩) (hc : g.reference ≤ 1 / 2)
    (hc0 : 0 ≤ g.reference) (hσ : 0 ≤ g.kick) (hσ1 : g.kick ≤ 1 / 2)
    (hstep : x 1 = next g (e 0) (x 0)) (hpermit : Permitted g (e 0) (x 0)) :
    |(coordinates (x 1)).1| + |(coordinates (x 1)).2| ≤ 3 := by
  cases he : e 0 with
  | none =>
    rw [he, hinit] at hstep
    rw [hstep]
    simp only [next, positive, coordinates, escapeKick, add_zero, mul_zero, mul_one,
      zero_add, show (0 : ℝ) ≤ 1 by norm_num, ite_true]
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 + g.kick + g.reference),
      abs_of_nonneg (by linarith : 0 ≤ 1 + g.kick - g.reference)]
    linarith
  | some i =>
    rw [he, hinit] at hpermit
    have h := hpermit.1
    norm_num at h

lemma bootstrap {g : Gains E n} {x : ℕ → State E} {e : ℕ → Option (Fin n)}
    {ρ H A : ℝ} {B M : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hδ : 0 < g.contrast)
    (hσ : 0 ≤ g.kick) (hσ1 : g.kick ≤ 1 / 2)
    (hH : 0 < H)
    (hp : ∀ i, ‖g.plus i‖ ≤ 1) (hr : ∀ i, ‖g.minus i‖ ≤ 1)
    (hc : ∀ j, ρ ≤ coefficient g j) (hc1 : ∀ j, coefficient g j ≤ 1 / 2)
    (hinit : x 0 = ⟨1, 0, 1, 0⟩)
    (hglobal : 3 + 12 * (g.contrast * H + g.kick) / ρ ^ 2 ≤ 4)
    (hpost : 3 * g.contrast ^ 2 + 12 * (g.contrast * H + g.kick) / ρ ^ 2 ≤ 2 * A)
    (hdecay : ∀ j : ℕ, B ≤ j → (1 - ρ ^ 2 / 2) ^ (j / 2) ≤ g.contrast ^ 2)
    (hnoise : A ^ 2 / g.contrast + (A + 3 / 2) ^ 2 ≤ 4)
    (hdrift : g.contrast * M * H ≤ 1 / 2)
    (hearly : 4 * (B : ℝ) ≤ H)
    (hcap : 16 * (B : ℝ) ^ 2 + 4 * M ≤ H ^ 2) :
    ∀ K, (∀ j, j < K → x (j + 1) = next g (e j) (x j)) →
      (∀ j, j < K → Permitted g (e j) (x j)) → negativeCount e K ≤ M → Bounded H (x K) := by
  intro K
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro hstep hpermit hcount
    have hprev : ∀ j, j < K → Bounded H (x j) := by
      intro j hj
      apply ih j hj
      · intro k hk; exact hstep k (by omega)
      · intro k hk; exact hpermit k (by omega)
      · exact (negativeCount_mono e hj.le).trans hcount
    have hstab := finite_stability hρ hρ1 hδ.le hσ hH.le hp hc
      (fun j => (hc1 j).trans (by norm_num))
      (by norm_num [hinit, coordinates])
      (fun hK => cold_first_mass hinit (hc1 none) (hρ.le.trans (hc none)) hσ hσ1
        (hstep 0 (by omega)) (hpermit 0 (by omega)))
      (fun j hj => (hprev j hj).2.2.2) hstep hpermit
    have hr0 : 0 ≤ 1 - ρ ^ 2 / 2 := by nlinarith
    have hr1 : 1 - ρ ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg ρ]
    have haK : |(x K).a| ≤ 2 ∧ |(x K).q| ≤ 2 := by
      have hs := hstab K le_rfl
      have hpw : (1 - ρ ^ 2 / 2) ^ (K / 2) ≤ 1 := pow_le_one₀ hr0 hr1
      have hcoord := coordinates_control (x K)
      constructor <;> nlinarith
    have htK : |(x K).t - 1| ≤ 1 / 2 := by
      have ht := signal_drift_bound hδ.le hr (fun j hj => (hprev j hj).2.2.2) hstep
      have hcM : (negativeCount e K : ℝ) ≤ M := by exact_mod_cast hcount
      have hh := mul_le_mul_of_nonneg_left hcM (mul_nonneg hδ.le hH.le)
      simp only [hinit] at ht
      nlinarith
    have hpoststates : ∀ j, B ≤ j → j ≤ K → |(x j).a| ≤ A ∧ |(x j).q| ≤ A := by
      intro j hj hjK
      have hs := hstab j hjK
      have hd := hdecay j hj
      have hcoord := coordinates_control (x j)
      constructor <;> nlinarith
    have hzK : ‖(x K).z‖ ≤ H := by
      by_cases hKB : K ≤ B
      · have hz := coarse_residual_bound hp hr (by simp [hinit])
          (fun j hj => (hprev j hj).1)
          (fun j hj => (bounded_signal (hprev j hj)).2) hstep
        have hcK : (negativeCount e K : ℝ) ≤ B := by
          exact_mod_cast (negativeCount_le e K).trans hKB
        linarith
      · have hBK : B ≤ K := by omega
        have hzB := coarse_residual_bound (K := B) hp hr (by simp [hinit])
          (fun j hj => (hprev j (by omega)).1)
          (fun j hj => (bounded_signal (hprev j (by omega))).2)
          (fun j hj => hstep j (by omega))
        have hcB : (negativeCount e B : ℝ) ≤ B := by exact_mod_cast negativeCount_le e B
        have hzB' : ‖(x B).z‖ ^ 2 ≤ 16 * (B : ℝ) ^ 2 := by
          nlinarith [norm_nonneg (x B).z, (Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
        have htel := count_telescope (e := e) (v := fun j => ‖(x j).z‖ ^ 2) (C := 4) hBK
        have hincr : ∀ j, B ≤ j → j < K →
            ‖(x (j + 1)).z‖ ^ 2 ≤ ‖(x j).z‖ ^ 2 +
              4 * ((negativeCount e (j + 1) : ℝ) - negativeCount e j) := by
          intro j hj hjK
          rw [hstep j hjK]
          cases he : e j with
          | none => simp [next, positive, negativeCount, he]
          | some i =>
            have hs := hpoststates j hj hjK.le
            have ht := (bounded_signal (hprev j hjK)).2
            have hper := hpermit j hjK
            rw [he] at hper
            have hn := negative_norm_increment hδ (hc1 (some i)) (hp i) (hr i)
              hs.1 hs.2 ht hper.1.le hper.2
            simp only [coefficient] at hn
            simp only [next, negativeCount, he, Option.isSome_some, ite_true, Nat.cast_add, Nat.cast_one]
            linarith
        have hz := htel hincr
        have hcM : (negativeCount e K : ℝ) ≤ M := by exact_mod_cast hcount
        have hcB0 : (0 : ℝ) ≤ negativeCount e B := Nat.cast_nonneg _
        nlinarith [norm_nonneg (x K).z]
    exact ⟨haK.1, haK.2, htK, hzK⟩

end LongTails.Proofs.ManySampleConvolutionalPerceptronBootstrap
