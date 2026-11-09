import LongTails.Proofs.GaussianVariationalMoments
import LongTails.Algorithms.ReparameterizedProxSgd
import LongTails.Proofs.LinearDecaySgdStep
import LongTails.Proofs.HiddenDecompositionEnergy

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GaussianVariational

open LongTails.Setups.GaussianVariationalInference

variable {d : ℕ}

lemma mulVec_sub (A B : Scale d) (ξ : Fin d → ℝ) :
    Matrix.mulVec (A - B) ξ = Matrix.mulVec A ξ - Matrix.mulVec B ξ := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma mulVec_add (A B : Scale d) (ξ : Fin d → ℝ) :
    Matrix.mulVec (A + B) ξ = Matrix.mulVec A ξ + Matrix.mulVec B ξ := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma mulVec_smul (c : ℝ) (A : Scale d) (ξ : Fin d → ℝ) :
    Matrix.mulVec (c • A) ξ = c • Matrix.mulVec A ξ := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma mulVec_zero_left (ξ : Fin d → ℝ) : Matrix.mulVec (0 : Scale d) ξ = 0 := by
  funext i
  simp [Matrix.mulVec, dotProduct]

def IsLower (U : Scale d) : Prop := ∀ i j, i < j → U i j = 0

def pinner (m : Location d) (C : Scale d) (u : Location d) (U : Scale d) : ℝ :=
  (∑ i, m i * u i) + ∑ i, ∑ j, C i j * U i j

lemma inner_eq_sum (x y : Point d) : ⟪x, y⟫ = ∑ i, x i * y i := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

lemma norm_sq_eq_sum (x : Point d) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq x

lemma isLower_sub {U W : Scale d} (hU : IsLower U) (hW : IsLower W) : IsLower (U - W) := by
  intro i j h
  simp [Pi.sub_apply, hU i j h, hW i j h]

lemma IsCholesky.isLower {C : Scale d} (h : IsCholesky C) : IsLower C := h.1

lemma pinner_comm (m : Location d) (C : Scale d) (u : Location d) (U : Scale d) :
    pinner m C u U = pinner u U m C := by
  unfold pinner
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma pinner_sub_left (m m' : Location d) (C C' : Scale d) (u : Location d) (U : Scale d) :
    pinner (m - m') (C - C') u U = pinner m C u U - pinner m' C' u U := by
  unfold pinner
  simp only [Pi.sub_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

lemma pinner_sub_right (m : Location d) (C : Scale d) (u u' : Location d) (U U' : Scale d) :
    pinner m C (u - u') (U - U') = pinner m C u U - pinner m C u' U' := by
  rw [pinner_comm, pinner_sub_left, pinner_comm u, pinner_comm u']

lemma pinner_smul_left (c : ℝ) (m : Location d) (C : Scale d) (u : Location d) (U : Scale d) :
    pinner (c • m) (c • C) u U = c * pinner m C u U := by
  unfold pinner
  simp only [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma sqDist_eq_pinner (m m' : Location d) (C C' : Scale d) :
    sqDist m m' C C' = pinner (m - m') (C - C') (m - m') (C - C') := by
  unfold sqDist pinner
  simp only [Pi.sub_apply, Pi.sub_apply, sq]

lemma pinner_self_nonneg (m : Location d) (C : Scale d) : 0 ≤ pinner m C m C := by
  unfold pinner
  exact add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _)

lemma sqDist_nonneg (m m' : Location d) (C C' : Scale d) : 0 ≤ sqDist m m' C C' := by
  rw [sqDist_eq_pinner]
  exact pinner_self_nonneg _ _

lemma sqDist_comm (m m' : Location d) (C C' : Scale d) : sqDist m m' C C' = sqDist m' m C' C := by
  unfold sqDist
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma pinner_young (a b : Location d) (A B : Scale d) {η : ℝ} (hη : 0 < η) :
    pinner a A b B ≤ η / 2 * pinner a A a A + 1 / (2 * η) * pinner b B b B := by
  have key : ∀ x y : ℝ, x * y ≤ η / 2 * (x * x) + 1 / (2 * η) * (y * y) := by
    intro x y
    have h := sq_nonneg (η * x - y)
    rw [show η / 2 * (x * x) + 1 / (2 * η) * (y * y) = ((η * x) ^ 2 + y ^ 2) / (2 * η) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  unfold pinner
  have h1 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key (a i) (b i)
  have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key (A i j) (B i j)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h1 h2
  rw [mul_add, mul_add]
  linarith

lemma inner_sample (g : Point d) (v : Fin d → ℝ) :
    ⟪g, (WithLp.toLp 2 v : Point d)⟫ = ∑ i, g i * v i := by
  rw [inner_eq_sum]

lemma pinner_grad (g : Point d) (ξ : Fin d → ℝ) (u : Location d) {U : Scale d}
    (hU : IsLower U) :
    pinner (gradLoc g) (gradScale g ξ) u U = ⟪g, (WithLp.toLp 2 (u + Matrix.mulVec U ξ) : Point d)⟫ := by
  rw [inner_sample]
  unfold pinner gradLoc gradScale
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ≤ i
  · simp only [h, ↓reduceIte]
    ring
  · simp only [h, ↓reduceIte, zero_mul]
    rw [hU i j (lt_of_not_ge h)]
    ring

lemma gradLoc_sub (g g' : Point d) : gradLoc (g - g') = gradLoc g - gradLoc g' := by
  funext i
  simp [gradLoc]

lemma gradScale_sub (g g' : Point d) (ξ : Fin d → ℝ) :
    gradScale (g - g') ξ = gradScale g ξ - gradScale g' ξ := by
  funext i j
  simp only [gradScale, Pi.sub_apply, PiLp.sub_apply]
  split_ifs <;> ring

lemma pinner_grad_self_le (g : Point d) (ξ : Fin d → ℝ) :
    pinner (gradLoc g) (gradScale g ξ) (gradLoc g) (gradScale g ξ) ≤
      (1 + sqNorm ξ) * ‖g‖ ^ 2 := by
  rw [norm_sq_eq_sum]
  unfold pinner gradLoc gradScale sqNorm
  have h : ∀ i, ∑ j, (if j ≤ i then g i * ξ j else 0) * (if j ≤ i then g i * ξ j else 0) ≤
      g i ^ 2 * ∑ j, ξ j ^ 2 := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · nlinarith
    · simp only [mul_zero]
      positivity
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h i
  have he : (1 + ∑ j, ξ j ^ 2) * ∑ i, g i ^ 2 = ∑ i, g i * g i + ∑ i, g i ^ 2 * ∑ j, ξ j ^ 2 := by
    rw [add_mul, one_mul, ← Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · rw [mul_comm]
  rw [he]
  linarith

lemma sample_sub (m m' : Location d) (C C' : Scale d) (ξ : Fin d → ℝ) :
    sample m C ξ - sample m' C' ξ = (WithLp.toLp 2 ((m - m') + Matrix.mulVec (C - C') ξ) : Point d) := by
  unfold sample
  rw [← WithLp.toLp_sub, mulVec_sub]
  congr 1
  abel

lemma sample_add_smul (m u : Location d) (C U : Scale d) (t : ℝ) (ξ : Fin d → ℝ) :
    sample (m + t • u) (C + t • U) ξ =
      sample m C ξ + t • (WithLp.toLp 2 (u + Matrix.mulVec U ξ) : Point d) := by
  unfold sample
  rw [← WithLp.toLp_smul, ← WithLp.toLp_add, mulVec_add, mulVec_smul]
  congr 1
  rw [smul_add]
  abel

lemma norm_toLp_sq_le (u : Location d) (U : Scale d) (ξ : Fin d → ℝ) :
    ‖(WithLp.toLp 2 (u + Matrix.mulVec U ξ) : Point d)‖ ^ 2 ≤
      2 * (∑ i, u i ^ 2) + 2 * (∑ i, ∑ j, U i j ^ 2) * sqNorm ξ := by
  rw [norm_sq_eq_sum]
  simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
  have hrow : ∀ i, (∑ j, U i j * ξ j) ^ 2 ≤ (∑ j, U i j ^ 2) * sqNorm ξ := fun i =>
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h : ∀ i, (u i + ∑ j, U i j * ξ j) ^ 2 ≤ 2 * u i ^ 2 + 2 * ((∑ j, U i j ^ 2) * sqNorm ξ) := by
    intro i
    nlinarith [hrow i, sq_nonneg (u i - ∑ j, U i j * ξ j)]
  calc ∑ i, (u i + ∑ j, U i j * ξ j) ^ 2
      ≤ ∑ i, (2 * u i ^ 2 + 2 * ((∑ j, U i j ^ 2) * sqNorm ξ)) := Finset.sum_le_sum fun i _ => h i
    _ = 2 * (∑ i, u i ^ 2) + 2 * (∑ i, ∑ j, U i j ^ 2) * sqNorm ξ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

lemma sqDist_split (m m' : Location d) (C C' : Scale d) :
    (∑ i, (m - m') i ^ 2) + ∑ i, ∑ j, (C - C') i j ^ 2 = sqDist m m' C C' := by
  simp [sqDist, Pi.sub_apply, Pi.sub_apply]

lemma norm_sample_sub_sq_le (m m' : Location d) (C C' : Scale d) (ξ : Fin d → ℝ) :
    ‖sample m C ξ - sample m' C' ξ‖ ^ 2 ≤ 2 * sqDist m m' C C' * (1 + sqNorm ξ) := by
  rw [sample_sub]
  have h := norm_toLp_sq_le (m - m') (C - C') ξ
  have hS := sqNorm_nonneg ξ
  have h1 : 0 ≤ ∑ i, (m - m') i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i, ∑ j, (C - C') i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← sqDist_split]
  nlinarith

end OracleTemplate.GaussianVariational
