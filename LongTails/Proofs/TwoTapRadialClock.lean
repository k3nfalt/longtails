import LongTails.Setups.TwoSampleQuadraticPerceptron
import LongTails.Proofs.SoftQuadraticDynamics

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoTapRadialClock

open LongTails.Setups.TwoSampleQuadraticPerceptron

noncomputable def radius {d : ℕ} (θ : Space .conv d) : ℝ :=
  (θ.1.1 ^ 2 + θ.1.2 ^ 2 + ‖θ.2‖ ^ 2) / 2

noncomputable def pairing {d : ℕ} (θ g : Space .conv d) : ℝ :=
  θ.1.1 * g.1.1 + θ.1.2 * g.1.2 + ⟪θ.2, g.2⟫

lemma radius_step {d : ℕ} (θ g : Space .conv d) (η : ℝ) :
    radius (θ + η • g) - radius θ = η * pairing θ g + η ^ 2 * radius g := by
  unfold radius pairing
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    norm_add_sq_real, norm_smul, Real.norm_eq_abs, real_inner_smul_right, mul_pow, sq_abs]
  ring

lemma pairing_direction {d : ℕ} (θ : Space .conv d) (x : Features d) :
    pairing θ (direction .conv d x θ) = 2 * margin .conv d x θ := by
  simp only [pairing, direction, margin, inner_add_right, real_inner_smul_right]
  rw [real_inner_comm θ.2 x, real_inner_comm θ.2 (shift x)]
  ring

lemma pairing_smul {d : ℕ} (θ g : Space .conv d) (a : ℝ) :
    pairing θ (a • g) = a * pairing θ g := by
  simp only [pairing, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, real_inner_smul_right]
  ring

lemma pairing_sum {d : ℕ} {ι : Type*} (θ : Space .conv d) (s : Finset ι)
    (g : ι → Space .conv d) : pairing θ (∑ i ∈ s, g i) = ∑ i ∈ s, pairing θ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairing]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp only [pairing, Prod.fst_add, Prod.snd_add, inner_add_right]
    ring

lemma full_gradient_radius {d n : ℕ} (x : Fin n → Features d) (θ : Space .conv d) (η : ℝ) :
    let q := fun i => SoftQuadraticDynamics.weight (margin .conv d (x i) θ)
    let g := (n : ℝ)⁻¹ • ∑ i, q i • direction .conv d (x i) θ
    radius (θ + η • g) - radius θ =
      2 * η * ((n : ℝ)⁻¹ * ∑ i, q i * margin .conv d (x i) θ) + η ^ 2 * radius g := by
  dsimp only
  rw [radius_step, pairing_smul, pairing_sum]
  have hw : (∑ i, pairing θ (SoftQuadraticDynamics.weight (margin .conv d (x i) θ) •
      direction .conv d (x i) θ)) =
      2 * ∑ i, SoftQuadraticDynamics.weight (margin .conv d (x i) θ) *
        margin .conv d (x i) θ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pairing_smul θ (direction .conv d (x i) θ), pairing_direction]
    ring
  rw [hw]
  ring

lemma radial_growth {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x d : V) (η : ℝ) :
    (‖x + η • d‖ ^ 2 - ‖x‖ ^ 2) / 2 =
      η * ⟪x, d⟫ + η ^ 2 * ‖d‖ ^ 2 / 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end LongTails.Proofs.TwoTapRadialClock
